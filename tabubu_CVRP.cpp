#include <bits/stdc++.h>
#include <chrono>
#include <filesystem>
#include <cmath>
#include <algorithm>
#include <random>

#define ll long long
#define pb push_back
#define mp make_pair
#define pii pair<int,int>
#define vi vector<int>
#define vd vector<double>
#define vvi vector<vector<int>>
#define vpi vector<pair<int,int>>
#define all(v) v.begin(),v.end()
#define FOR(i,a,b) for(int i=a;i<b;i++)
#define RFOR(i,a,b) for(int i=a-1;i>=b;i--)

using namespace std;

int n, m; //number of customers and vehicles
int depot = 0; // depot node index (usually 0)
int Q; // capacity of all vehicles
vector<vector<double>> dist; // dist[i][j]: Euclidean distance from i to j
vi demand; // demand[i]: demand of customer i
vpi loc; // loc[i]: location (x, y) of customer i
vvi routes; // routes[k]: sequence of customer indices for vehicle k (start/end with depot)
vi load; // load[k]: current load of vehicle k
vd duration; // duration[k]: current duration of vehicle k
vvi tabu_list_swap, tabu_list_switch, tabu_list_relocate; vector<vector<vector<int>>> tabu_list_2_opt; // for Tabu Search memory
double best_cost; // best total travel time found
vector<pair<double, int>> angle_customer; // (angle, customer index)
vvi closest_neighbors; // closest_neighbors[i]: list of closest neighbors to customer i
vvi freq; // freq[k][i]: how many times customer i inserted into route k for diversification
int optimal_value = -1; // optimal solution value if known, else -1


const int MAX_ITER = 2000; // max iterations for Tabu Search
const int NMAX = 50; // for early stopping if no improvement
const int TABU_TENURE = 10; // tenure for tabu search

const int NUM_NEIGHBORHOODS = 4;
const int MAX_SEGMENT = 50;
const double gamma1 = 1.0;
const double gamma2 = 0.3;
const double gamma3 = 0.0;
const double gamma4 = 0.5;

struct Solution {
    vvi routes; // routes for each vehicle
    vi load;           // load for each vehicle
    vd duration;       // duration for each vehicle
    double total_cost; // total travel time/distance
    vi customer_vehicle; // customer_vehicle[i] = k means customer i is assigned to vehicle k
};

// Compute Euclidean distance between two points
double euclidean(int x1, int y1, int x2, int y2) {
    return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2));
}

// Build distance matrix: dist[i][j] = Euclidean distance from i to j
void build_distance_matrix() {
    dist.assign(n+5, vd(n+5, 0.0));
    for (int i = 0; i <= n; ++i) {
        for (int j = 0; j <= n; ++j) {
            if (i == j) {
                dist[i][j] = 0.0;
            } else {
                dist[i][j] = euclidean(loc[i].first, loc[i].second, loc[j].first, loc[j].second);
            }
        }
    }
}

void calculate_angle_customer() {
    angle_customer.clear();
    int depot_x = loc[0].first, depot_y = loc[0].second;
    for (int i = 1; i <= n; ++i) {
        double dx = loc[i].first - depot_x;
        double dy = loc[i].second - depot_y;
        double angle = atan2(dy, dx);
        angle_customer.push_back({angle, i});
    }
    sort(angle_customer.begin(), angle_customer.end());
}

// Generate an initial feasible solution using a sweep-like heuristic
Solution generate_initial_solution(int start_idx) {
    Solution sol;
    // 1. Sort customers by angle from depot (precomputed in angle_customer)

    // 2. Build sequence
    vi seq;
    for (int i = 0; i < n; ++i)
        seq.push_back(angle_customer[(start_idx + i) % n].second);

    // 3. Construct routes
    routes.assign(m+1, vi());
    load.assign(m+1, 0);
    duration.assign(m+1, 0);
    int k = 1;
    for (int idx : seq) {
        // Try to insert idx into route k at best position
        int best_feas_pos = -1, best_feas_incr = INT_MAX;
        int best_infeas_pos = -1;
        double best_infeas_incr = 1e18;
        if (routes[k].empty()) {
            routes[k].push_back(0);
            routes[k].push_back(0);
        } // start and end at depot
        int new_load = load[k] + demand[idx];
        for (int pos = 1; pos < routes[k].size(); ++pos) {
            if (new_load > Q) break;
            // Try inserting at pos
            int prev = routes[k][pos-1];
            int next = routes[k][pos];
            auto temp = routes[k];
            temp.insert(temp.begin() + pos, idx);
            // Compute new load and incremental duration
            // Remove old segment, add new segments
            double delta = dist[prev][idx] + dist[idx][next] - dist[prev][next];
            double new_dur = duration[k] + delta;
            double incr = delta;
            if (new_load <= Q) {
                if (incr < best_feas_incr) {
                    best_feas_incr = incr;
                    best_feas_pos = pos;
                }
            } else {
                if (incr < best_infeas_incr) {
                    best_infeas_incr = incr;
                    best_infeas_pos = pos;
                }
            }
        }
        // Insert at best feasible position if found
        if (best_feas_pos != -1) {
            routes[k].insert(routes[k].begin() + best_feas_pos, idx);
            load[k] += demand[idx];
            // Recompute duration
            duration[k] = 0;
            for (int p = 1; p < routes[k].size(); ++p)
                duration[k] += dist[routes[k][p-1]][routes[k][p]];
        }
        // If constraints violated, move to next route
        if (best_feas_pos == -1) {
            if (k < m) {
                k++;
                routes[k].clear();
                routes[k].push_back(0);
                routes[k].push_back(idx);
                routes[k].push_back(0);
                load[k] = demand[idx];
                duration[k] = 0;
                for (int p = 1; p < routes[k].size(); ++p)
                    duration[k] += dist[routes[k][p-1]][routes[k][p]];
            } else {
                // Insert idx into route m (k==m) at the best infeasible position found above
                if (best_infeas_pos == -1) best_infeas_pos = 1;
                routes[m].insert(routes[m].begin() + best_infeas_pos, idx);
                load[m] += demand[idx];
                duration[m] = 0;
                for (int p = 1; p < routes[m].size(); ++p) {
                    duration[m] += dist[routes[m][p-1]][routes[m][p]];
                }
            }
        }
    }
    // End each route at depot
    for (int k = 1; k <= m; ++k){
        if (!routes[k].empty() && routes[k].back() != 0)
            routes[k].push_back(0);
    }
    sol.routes = routes;
    sol.load = load;
    sol.duration = duration;

    // Calculate arrival times for each customer in each route
    sol.total_cost = 0;
    for (int k = 1; k <= m; ++k) {
        sol.total_cost += duration[k];
    }

    sol.customer_vehicle.assign(n+1, 0);
    for (int k = 1; k <= m; ++k) {
        for (int cust : routes[k]) {
            if (cust != 0) sol.customer_vehicle[cust] = k;
        }
    }
    return sol;
}

// Did exactly what it says
void print_solution(const Solution& sol) {
    for (int k = 1; k <= m; ++k) {
        cout << "Route " << k << ": ";
        for (int idx : sol.routes[k]) {
            cout << idx << " ";
        }
        cout << endl;
        cout << "Load: " << sol.load[k] << ", Duration: " << sol.duration[k] << endl;
    }
    cout << "Total Cost: " << sol.total_cost << endl;
    cout << endl;
}

Solution find_best_neighbor(Solution sol, int neighbor_id, int current_iter, double best_cost){
    Solution best_neighbor = sol;
    double best_neighbor_cost = sol.total_cost;

    if (neighbor_id == 0){
        int best_i = -1;
        int best_j = -1;
        //SWAP_CUSTOMERS
        for (int i = 1; i < n; i++){
            for (int j = i + 1; j <= n; j++){
                Solution neighbor = sol;
                int route_i = neighbor.customer_vehicle[i];
                int route_j = neighbor.customer_vehicle[j];
                if (route_i == route_j){
                    // SWAP_WITHIN_A_ROUTE
                    int route = sol.customer_vehicle[i];
                    int pos_i = find(neighbor.routes[route].begin(), neighbor.routes[route].end(), i) - neighbor.routes[route].begin();
                    int pos_j = find(neighbor.routes[route].begin(), neighbor.routes[route].end(), j) - neighbor.routes[route].begin();
                    if (pos_i == 0 || pos_j == 0 || pos_i == neighbor.routes[route].size()-1 || pos_j == neighbor.routes[route].size()-1 || pos_i == pos_j - 1 || pos_j == pos_i + 1) continue;

                    swap(neighbor.routes[route][pos_i], neighbor.routes[route][pos_j]);
                    // Recalculate duration for this route from scratch
                    neighbor.duration[route] = 0;
                    for (int p = 1; p < neighbor.routes[route].size(); ++p)
                        neighbor.duration[route] += dist[neighbor.routes[route][p-1]][neighbor.routes[route][p]];
                    // Recalculate total cost from scratch
                    neighbor.total_cost = 0;
                    for (int k = 1; k <= m; ++k) neighbor.total_cost += neighbor.duration[k];
                    
                    //check tabu and aspiration criteria
                    bool is_tabu = (tabu_list_switch[i][j] >= current_iter);
                    if (is_tabu && neighbor.total_cost >= best_cost) continue;
                    if (neighbor.total_cost < best_cost) {
                        best_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                    if (neighbor.total_cost < best_neighbor_cost) {
                        best_i = i;
                        best_j = j;
                        best_neighbor_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                }
            }
        }
        // Update tabu list
        if (best_i != -1 && best_j != -1) {
            tabu_list_switch[best_i][best_j] = current_iter + TABU_TENURE;
            tabu_list_switch[best_j][best_i] = current_iter + TABU_TENURE;
        }
//        cout << "Best switch Move: " << best_i << " " << best_j << endl;
    }
    if (neighbor_id == 1){
        //switch_customers_from_differrent_routes
        int best_i = -1;
        int best_j = -1;
        for (int i = 0; i < n; i++) {
            for (int j = i + 1; j <= n; j++) {
                Solution neighbor = sol;
                int route_i = sol.customer_vehicle[i];
                int route_j = sol.customer_vehicle[j];
                if (sol.customer_vehicle[i] != sol.customer_vehicle[j]) {
                    //SWITCH_CUSTOMER
                    // Check load constraints
                    if (neighbor.load[route_i] + demand[j] - demand[i] <= Q && neighbor.load[route_j] + demand[i] - demand[j] <= Q) {
                    
                        //Find positions
                        int pos_i = find(neighbor.routes[route_i].begin(), neighbor.routes[route_i].end(), i) - neighbor.routes[route_i].begin();
                        int pos_j = find(neighbor.routes[route_j].begin(), neighbor.routes[route_j].end(), j) - neighbor.routes[route_j].begin();

                        // Bounds check: avoid depot at ends
                        if (pos_i == 0 || pos_i == neighbor.routes[route_i].size() - 1 ||
                            pos_j == 0 || pos_j == neighbor.routes[route_j].size() - 1)
                            continue;
                        // Update loads and durations
                        neighbor.load[route_i] += demand[j] - demand[i];
                        neighbor.load[route_j] += demand[i] - demand[j];

                        //update durations: u-i-v ... x-j-y to u-j-v ... x-i-y
                        int u = neighbor.routes[route_i][pos_i-1];
                        int v = neighbor.routes[route_i][pos_i+1];
                        int x = neighbor.routes[route_j][pos_j-1];
                        int y = neighbor.routes[route_j][pos_j+1];

                        swap(neighbor.routes[route_i][pos_i], neighbor.routes[route_j][pos_j]);
                        swap(neighbor.customer_vehicle[i], neighbor.customer_vehicle[j]);
                        // Recalculate duration for both affected routes from scratch
                        neighbor.duration[route_i] = 0;
                        for (int p = 1; p < neighbor.routes[route_i].size(); ++p)
                            neighbor.duration[route_i] += dist[neighbor.routes[route_i][p-1]][neighbor.routes[route_i][p]];
                        neighbor.duration[route_j] = 0;
                        for (int p = 1; p < neighbor.routes[route_j].size(); ++p)
                            neighbor.duration[route_j] += dist[neighbor.routes[route_j][p-1]][neighbor.routes[route_j][p]];
                        // Recalculate total cost from scratch
                        neighbor.total_cost = 0;
                        for (int k = 1; k <= m; ++k)
                            neighbor.total_cost += neighbor.duration[k];

                    }
                    else continue;
                }
                if (load[route_i] > Q || neighbor.load[route_j] > Q) {
                    continue;
                }
                else {
                    //check tabu and aspiration criteria
                    bool is_tabu = (tabu_list_swap[i][j] >= current_iter);
                    if (is_tabu && neighbor.total_cost >= best_cost) continue;
                    if (neighbor.total_cost < best_cost) {
                        best_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                    if (neighbor.total_cost < best_neighbor_cost) {
                        best_neighbor_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                        best_i = i;
                        best_j = j;
                    }
                }
            }
        }
        if (best_i != -1 && best_j != -1) {
            tabu_list_swap[best_i][best_j] = current_iter + TABU_TENURE;
            tabu_list_swap[best_j][best_i] = current_iter + TABU_TENURE;
        }
//        cout << "Best swap Move: " << best_i << " " << best_j << endl;
    }
    if (neighbor_id == 2){
        //2-opt operation
        int best_k = -1;
        int best_i = -1;
        int best_j = -1;
        for (int k = 1; k <= m; k++){
            if (sol.routes[k].size() <= 3) continue;
            for (int i = 1; i < sol.routes[k].size() - 2; i++) {
                for (int j = i + 1; j < sol.routes[k].size() - 1; j++) {
                    Solution neighbor = sol;
                    // Perform 2-opt: reverse segment
                    reverse(neighbor.routes[k].begin() + i, neighbor.routes[k].begin() + j + 1);
                    // Recalculate duration for this route from scratch
                    neighbor.duration[k] = 0;
                    for (int p = 1; p < neighbor.routes[k].size(); ++p)
                        neighbor.duration[k] += dist[neighbor.routes[k][p-1]][neighbor.routes[k][p]];
                    // Recalculate total cost from scratch
                    neighbor.total_cost = 0;
                    for (int kk = 1; kk <= m; ++kk)
                        neighbor.total_cost += neighbor.duration[kk];

                    // Check tabu and aspiration criteria
                    bool is_tabu = (tabu_list_2_opt[k][i][j] >= current_iter);
                    if (is_tabu && neighbor.total_cost >= best_cost) continue;
                    if (neighbor.total_cost < best_neighbor_cost) {
                        best_neighbor_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                        best_k = k;
                        best_i = i;
                        best_j = j;
                    }
                }
            }
        }
        if (best_k != -1 && best_i != -1 && best_j != -1) {
            tabu_list_2_opt[best_k][best_i][best_j] = current_iter + TABU_TENURE * m;
        }
//        cout << "2-opt Move: " << best_i << " " << best_j << " in Route " << best_k << endl;
    }
    if (neighbor_id == 3){
        Solution neighbor = sol;
        int best_i = -1;
        int best_k = -1;
        //RELOCATE CUSTOMER I TO ANOTHER ROUTE K AT OPTIMAL LOCATION
        for (int i = 1; i <= n; i++){
            int route_i = sol.customer_vehicle[i];
            int pos_i = find(sol.routes[route_i].begin(), sol.routes[route_i].end(), i) - sol.routes[route_i].begin();
            int before_i = sol.routes[route_i][pos_i-1];
            int after_i  = sol.routes[route_i][pos_i+1];
            for (int k = 1; k <= m; k++) {
                if (k == route_i) continue;
                if (sol.load[k] + demand[i] > Q) continue;

                Solution neighbor = sol;
                // Find optimal position to insert customer i into route k
                int best_pos = -1;
                double best_insertion_cost = 1e18;
                for (int pos = 1; pos < neighbor.routes[k].size(); pos++) {
                    // Calculate cost of relocating customer i to position pos in route k
                    double delta_j = dist[neighbor.routes[k][pos - 1]][i] + dist[i][neighbor.routes[k][pos]]
                                     - dist[neighbor.routes[k][pos - 1]][neighbor.routes[k][pos]];
                    if (delta_j < best_insertion_cost) {
                        best_insertion_cost = delta_j;
                        best_pos = pos;
                    }
                }
                if (best_pos != -1) {
                    // Perform relocation
                    neighbor.routes[k].insert(neighbor.routes[k].begin() + best_pos, i);
                    neighbor.routes[route_i].erase(neighbor.routes[route_i].begin() + pos_i);
                    neighbor.customer_vehicle[i] = k;
                    neighbor.load[route_i] -= demand[i];
                    neighbor.load[k] += demand[i];
                    // Recalculate duration for both affected routes from scratch
                    neighbor.duration[route_i] = 0;
                    for (int p = 1; p < neighbor.routes[route_i].size(); ++p)
                        neighbor.duration[route_i] += dist[neighbor.routes[route_i][p-1]][neighbor.routes[route_i][p]];
                    neighbor.duration[k] = 0;
                    for (int p = 1; p < neighbor.routes[k].size(); ++p)
                        neighbor.duration[k] += dist[neighbor.routes[k][p-1]][neighbor.routes[k][p]];
                    // Recalculate total cost from scratch
                    neighbor.total_cost = 0;
                    for (int kk = 1; kk <= m; ++kk)
                        neighbor.total_cost += neighbor.duration[kk];

                    // Check tabu and aspiration criteria
                    bool is_tabu = (tabu_list_relocate[k][i] >= current_iter);
                    if (is_tabu && neighbor.total_cost >= best_cost) continue;
                    if (neighbor.total_cost < best_cost) {
                        best_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                    if (neighbor.total_cost < best_neighbor_cost) {
                        best_neighbor_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                        best_i = i;
                        best_k = k;
                    }
                }
            }
        }
        if (best_i != -1 && best_k != -1) {
            tabu_list_relocate[best_k][best_i] = current_iter + TABU_TENURE;
        }
//        cout << "Relocate Customer " << best_i << " to Route " << best_k << endl;
    }
    return best_neighbor;
}

Solution tabu_search(Solution sol, int max_iter, int max_segment, int nmax) {
    Solution best_solution = sol;
    double best_cost = sol.total_cost;
    double score[NUM_NEIGHBORHOODS] = {0.0};
    double weight[NUM_NEIGHBORHOODS] = {1.0/NUM_NEIGHBORHOODS, 1.0/NUM_NEIGHBORHOODS, 1.0/NUM_NEIGHBORHOODS, 1.0/NUM_NEIGHBORHOODS};
    int count[NUM_NEIGHBORHOODS] = {0};

    // Generate a vector of MAX_SEGMENT different random numbers (seeds)
    vector<int> segment_seeds(max_segment);
    iota(segment_seeds.begin(), segment_seeds.end(), 0);
    random_device rd;
    mt19937 g(rd());
    shuffle(segment_seeds.begin(), segment_seeds.end(), g);

    Solution current_sol = sol;
    

    for (int segment = 1; segment <= max_segment; segment++) {
        if (segment_seeds[segment - 1] >= n) segment_seeds[segment - 1] = segment_seeds[segment - 1] % n;
        if (segment_seeds[segment - 1] == 0) segment_seeds[segment - 1] = 1;
        Solution current_sol = generate_initial_solution(segment_seeds[segment - 1]);
//        cout << "Starting segment " << segment << endl;
//        cout << "Initial solution:" << endl;
//        print_solution(current_sol);
        int iter = 1;
        int no_improve = 0;
        double T0 = 100.0; // initial temperature
        double alpha = 0.995; // cooling rate
        tabu_list_swap.resize(n + 5, vector<int>(n + 5, 0));
        tabu_list_switch.resize(n + 5, vector<int>(n + 5, 0));
        tabu_list_2_opt.resize(m + 5, vector<vector<int>>(n + 5, vector<int>(n + 5, 0)));
        tabu_list_relocate.resize(m + 5, vector<int>(n + 5, 0));
        while (iter < max_iter) {
            //write_here
            int current_iter[NUM_NEIGHBORHOODS] = {1, 1, 1, 1};
            double total_weight = 0;
            for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) total_weight += weight[i];
            double r = ((double) rand() / RAND_MAX) * total_weight;
            int neighbor_id = 0;
            double acc = weight[0];
            while (neighbor_id < NUM_NEIGHBORHOODS - 1 && r > acc) {
                neighbor_id++;
                acc += weight[neighbor_id];
            }
            count[neighbor_id]++;
            //Find best neighbor
//            cout << "Iteration " << iter << ", Segment " << segment << endl;
//            cout << "Weight:" << endl;
//            for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) {
//               cout << "Neighborhood " << i << ": " << weight[i] << endl;
//            }
//            cout << "Selected Neighborhood: " << neighbor_id << endl;
            Solution neighbor = find_best_neighbor(current_sol, neighbor_id, current_iter[neighbor_id], best_cost);
//            cout << "Best neighbor found " << endl;
//            print_solution(neighbor);
            //Update score
            if (neighbor.total_cost < best_cost) {
                best_cost = neighbor.total_cost;
                best_solution = neighbor;
                score[neighbor_id] += gamma1;
                no_improve = 0;
            }
            else if (neighbor.total_cost < current_sol.total_cost) {
                score[neighbor_id] += gamma2;
                no_improve = 0;
            }
            else {
                score[neighbor_id] += gamma3;
                no_improve++;
            }

            // Update tabu list
            current_iter[neighbor_id]++;

            // Early stopping: stop if no improvement for nmax iterations
            if (no_improve >= nmax) {
                break;
            }

            if (neighbor.total_cost < current_sol.total_cost) {
                current_sol = neighbor;
            } else {
                // Simulated Annealing: accept worse solution with probability
                double T = T0 * pow(alpha, iter);
                double delta = neighbor.total_cost - current_sol.total_cost;
                if (T > 1e-8 && exp(-delta / T) > ((double) rand() / RAND_MAX)) {
                    current_sol = neighbor;
                }
            }
            iter++;
        }
        // Update weights using scores
        for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) {
            if (count[i] == 0) {
                // If neighborhood not used, keep previous weight
                weight[i] = weight[i];
            } else {
                // (1-gamma4)*weight[i] + gamma4*(score[i]/count[i])
                weight[i] = (1.0 - gamma4) * weight[i] + gamma4 * (score[i] / count[i]);
            }
        }
        // Normalize weights so that their sum is 1
        double sum_weights = 0.0;
        for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) sum_weights += weight[i];
        if (sum_weights > 0) {
            for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) weight[i] /= sum_weights;
        }
        for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) {
            score[i] = 0.0;
            count[i] = 1;
        }
//        cout << "End of segment " << segment << ", best cost so far: " << best_cost << endl;
    }

    return best_solution;
}

void init() {
    build_distance_matrix();
    calculate_angle_customer();
    tabu_list_swap.resize(n + 5, vector<int>(n + 5, 0));
    tabu_list_switch.resize(n + 5, vector<int>(n + 5, 0));
    tabu_list_2_opt.resize(m + 5, vector<vector<int>>(n + 5, vector<int>(n + 5, 0)));
    tabu_list_relocate.resize(m + 5, vector<int>(n + 5, 0));
    best_cost = 1e18;
}

void input(){
    string line;
    int dimension = 0;
    int capacity = 0;
    int optimal = -1;
    vector<pair<int, int>> coords;
    vector<int> demands_tmp;
    int depot_idx = 0;
    while (getline(cin, line)) {
        // Extract optimal value from COMMENT line if present
        if (line.find("Optimal value") != string::npos) {
            size_t pos = line.find("Optimal value:");
            if (pos != string::npos) {
                string val = line.substr(pos + 14);
                val.erase(0, val.find_first_not_of(" \t\r\n"));
                val.erase(val.find_last_not_of(" \t\r\n") + 1);
                try {
                    optimal_value = stoi(val);
                } catch (...) {
                    optimal_value = -1;
                }
            }
        }
        if (line.find("DIMENSION") != string::npos) {
            dimension = stoi(line.substr(line.find(":") + 1));
        } else if (line.find("CAPACITY") != string::npos) {
            capacity = stoi(line.substr(line.find(":") + 1));
        } else if (line.find("NODE_COORD_SECTION") != string::npos) {
            for (int i = 0; i < dimension; ++i) {
                int idx, x, y;
                cin >> idx >> x >> y;
                coords.push_back({x, y});
            }
        } else if (line.find("DEMAND_SECTION") != string::npos) {
            for (int i = 0; i < dimension; ++i) {
                int idx, d;
                cin >> idx >> d;
                demands_tmp.push_back(d);
            }
        } else if (line.find("DEPOT_SECTION") != string::npos) {
            cin >> depot_idx;
            // skip -1 and EOF
            break;
        }
    }
    n = dimension - 1; // customers (excluding depot)
    Q = capacity;
    m = 5; // or set from file/comment if needed
    loc.resize(n + 1);
    demand.resize(n + 1);
    // File uses 1-based indexing, 1 is depot
    for (int i = 0; i <= n; ++i) {
        loc[i] = coords[i];
        demand[i] = demands_tmp[i];
    }
}



void output(){
    cout << "File name: A-n44-k6.vrp" << endl;
    Solution dummy=generate_initial_solution(1);
    Solution best_sol = tabu_search(dummy, MAX_ITER, MAX_SEGMENT, NMAX);
    cout << "Best solution found:" << endl;
    print_solution(best_sol);
    cout << "Optimal value (if known): " << optimal_value << endl;
    double accuracy = (optimal_value > 0) ? ((best_sol.total_cost - optimal_value) / optimal_value) * 100.0 : -1.0;
    if (accuracy >= 0)
        cout << "Accuracy gap: " << accuracy << "%" << endl;
    else
        cout << "Accuracy gap: N/A" << endl;
}

int main(){
    freopen("data/A-n44-k6.vrp", "r", stdin);
    freopen("output.txt", "w", stdout);
    auto start = chrono::high_resolution_clock::now();
    input();
    init();
    output();
    auto end = chrono::high_resolution_clock::now();
    chrono::duration<double> elapsed = end - start;
    cout << "Elapsed time: " << elapsed.count() << " seconds" << endl;
}