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
const int NMAX = 100; // for early stopping if no improvement
const int TABU_TENURE = 10; // tenure for tabu search

const int NUM_NEIGHBORHOODS = 4;
const int MAX_SEGMENT = 100;
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
                // Find the best vehicle (route) for this customer that does not violate constraint
                int best_vehicle = -1, best_pos = -1;
                double best_incr = 1e18;
                for (int v = 1; v <= m; ++v) {
                    if (load[v] + demand[idx] > Q) continue;
                    for (int pos = 1; pos < routes[v].size(); ++pos) {
                        int prev = routes[v][pos-1];
                        int next = routes[v][pos];
                        double delta = dist[prev][idx] + dist[idx][next] - dist[prev][next];
                        if (delta < best_incr) {
                            best_incr = delta;
                            best_vehicle = v;
                            best_pos = pos;
                        }
                    }
                }
                if (best_vehicle != -1 && best_pos != -1) {
                    routes[best_vehicle].insert(routes[best_vehicle].begin() + best_pos, idx);
                    load[best_vehicle] += demand[idx];
                    duration[best_vehicle] = 0;
                    for (int p = 1; p < routes[best_vehicle].size(); ++p)
                        duration[best_vehicle] += dist[routes[best_vehicle][p-1]][routes[best_vehicle][p]];
                } else {
                    // If no feasible vehicle found, insert into route m at best infeasible position
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
                for (int k = 1; k <= m; k++) {
                    if (neighbor.load[k] > Q) {
                        neighbor.total_cost = 1e18; // Infeasible solution
                        break;
                    }
                }
                {
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
            int route_size = (int)sol.routes[k].size();
            if (route_size <= 3) continue;
            for (int i = 1; i < route_size - 2; i++) {
                for (int j = i + 1; j < route_size - 1; j++) {
                    // Bounds check for reverse
                    if (i < 1 || j >= route_size - 1 || i > j) continue;
                    Solution neighbor = sol;
                    // Perform 2-opt: reverse segment
                    reverse(neighbor.routes[k].begin() + i, neighbor.routes[k].begin() + j + 1);
                    // Recalculate duration for this route from scratch
                    neighbor.duration[k] = 0;
                    for (int p = 1; p < (int)neighbor.routes[k].size(); ++p)
                        neighbor.duration[k] += dist[neighbor.routes[k][p-1]][neighbor.routes[k][p]];
                    // Recalculate total cost from scratch
                    neighbor.total_cost = 0;
                    for (int kk = 1; kk <= m; ++kk)
                        neighbor.total_cost += neighbor.duration[kk];

                    // Check tabu and aspiration criteria
                    if (k < (int)tabu_list_2_opt.size() && i < (int)tabu_list_2_opt[k].size() && j < (int)tabu_list_2_opt[k][i].size()) {
                        bool is_tabu = (tabu_list_2_opt[k][i][j] >= current_iter);
                        if (is_tabu && neighbor.total_cost >= best_cost) continue;
                    }
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
        if (best_k != -1 && best_i != -1 && best_j != -1 && best_k < (int)tabu_list_2_opt.size() && best_i < (int)tabu_list_2_opt[best_k].size() && best_j < (int)tabu_list_2_opt[best_k][best_i].size()) {
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
            // Bounds check for pos_i
            if (route_i < 1 || route_i > m) continue;
            if (pos_i < 0 || pos_i >= (int)sol.routes[route_i].size()) continue;
            if ((int)sol.routes[route_i].size() <= 2) continue; // route must have at least depot, i, depot
            for (int k = 1; k <= m; k++) {
                if (k == route_i) continue;
                if (sol.load[k] + demand[i] > Q) continue;

                Solution neighbor = sol;
                // Find optimal position to insert customer i into route k
                int best_pos = -1;
                double best_insertion_cost = 1e18;
                for (int pos = 1; pos < (int)neighbor.routes[k].size(); pos++) {
                    // Calculate cost of relocating customer i to position pos in route k
                    double delta_j = dist[neighbor.routes[k][pos - 1]][i] + dist[i][neighbor.routes[k][pos]]
                                     - dist[neighbor.routes[k][pos - 1]][neighbor.routes[k][pos]];
                    if (delta_j < best_insertion_cost) {
                        best_insertion_cost = delta_j;
                        best_pos = pos;
                    }
                }
                if (best_pos != -1) {
                    // Perform relocation with bounds check
                    if (best_pos >= 0 && best_pos <= (int)neighbor.routes[k].size()) {
                        neighbor.routes[k].insert(neighbor.routes[k].begin() + best_pos, i);
                    } else {
                        continue;
                    }
                    if (pos_i >= 0 && pos_i < (int)neighbor.routes[route_i].size()) {
                        neighbor.routes[route_i].erase(neighbor.routes[route_i].begin() + pos_i);
                    } else {
                        continue;
                    }
                    neighbor.customer_vehicle[i] = k;
                    neighbor.load[route_i] -= demand[i];
                    neighbor.load[k] += demand[i];
                    // Recalculate duration for both affected routes from scratch
                    neighbor.duration[route_i] = 0;
                    for (int p = 1; p < (int)neighbor.routes[route_i].size(); ++p)
                        neighbor.duration[route_i] += dist[neighbor.routes[route_i][p-1]][neighbor.routes[route_i][p]];
                    neighbor.duration[k] = 0;
                    for (int p = 1; p < (int)neighbor.routes[k].size(); ++p)
                        neighbor.duration[k] += dist[neighbor.routes[k][p-1]][neighbor.routes[k][p]];
                    // Recalculate total cost from scratch
                    neighbor.total_cost = 0;
                    for (int kk = 1; kk <= m; ++kk)
                        neighbor.total_cost += neighbor.duration[kk];

                    for (int kk = 1; kk <= m; kk++) {
                        if (neighbor.load[kk] > Q) {
                            neighbor.total_cost = 1e18; // Infeasible solution
                            break;
                        }
                    }

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
    


        // Helper: check if a solution is feasible (all routes feasible, all customers visited once)
        auto is_solution_feasible = [](const Solution& sol) -> bool {
            vector<bool> customer_visited(n+1, false);
            for (int k = 1; k <= m; ++k) {
                int load_k = sol.load[k];
                const vi& route = sol.routes[k];
                if (route.size() < 2) continue;
                if (route.front() != 0 || route.back() != 0) return false;
                if (load_k > Q) return false;
                for (int i = 1; i < (int)route.size() - 1; ++i) {
                    int cust = route[i];
                    if (cust == 0) return false;
                    if (customer_visited[cust]) return false;
                    customer_visited[cust] = true;
                }
            }
            for (int i = 1; i <= n; ++i) if (!customer_visited[i]) return false;
            return true;
        };

        for (int segment = 1; segment <= max_segment; segment++) {
            Solution best_segment_solution = current_sol;
            double best_segment_cost = current_sol.total_cost;
            // Generate initial solution for this segment using the seed
            if (segment_seeds[segment - 1] >= n) segment_seeds[segment - 1] = segment_seeds[segment - 1] % n;
            if (segment_seeds[segment - 1] == 0) segment_seeds[segment - 1] = 1;
            Solution current_sol = generate_initial_solution(segment_seeds[segment - 1]);
            int iter = 1;
            int no_improve = 0;
            double T0 = 100.0; // initial temperature
            double alpha = 0.995; // cooling rate
            tabu_list_swap.resize(n + 5, vector<int>(n + 5, 0));
            tabu_list_switch.resize(n + 5, vector<int>(n + 5, 0));
            tabu_list_2_opt.resize(m + 5, vector<vector<int>>(n + 5, vector<int>(n + 5, 0)));
            tabu_list_relocate.resize(m + 5, vector<int>(n + 5, 0));
            while (iter < max_iter) {
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
                Solution neighbor = find_best_neighbor(current_sol, neighbor_id, current_iter[neighbor_id], best_cost);
                // Update score
                if (neighbor.total_cost < best_segment_cost) {
                    best_segment_cost = neighbor.total_cost;
                    best_segment_solution = neighbor;
                    no_improve = 0;
                }
                if (neighbor.total_cost < best_cost) {
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
                current_iter[neighbor_id]++;
                if (no_improve >= nmax) {
                    break;
                }
                if (neighbor.total_cost < current_sol.total_cost) {
                    current_sol = neighbor;
                } else {
                    double T = T0 * pow(alpha, iter);
                    double delta = neighbor.total_cost - current_sol.total_cost;
                    if (T > 1e-8 && exp(-delta / T) > ((double) rand() / RAND_MAX)) {
                        current_sol = neighbor;
                    }
                }
                iter++;
            }
            // Only update best_solution if segment solution is feasible
            if (is_solution_feasible(best_segment_solution) && best_segment_cost < best_cost) {
                best_cost = best_segment_cost;
                best_solution = best_segment_solution;
            }
            // Update weights using scores
            for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) {
                if (count[i] == 0) {
                    weight[i] = weight[i];
                } else {
                    weight[i] = (1.0 - gamma4) * weight[i] + gamma4 * (score[i] / count[i]);
                }
            }
            double sum_weights = 0.0;
            for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) sum_weights += weight[i];
            if (sum_weights > 0) {
                for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) weight[i] /= sum_weights;
            }
            for (int i = 0; i < NUM_NEIGHBORHOODS; ++i) {
                score[i] = 0.0;
                count[i] = 1;
            }
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
        } else if (line.find("trucks") != string::npos || line.find("vehicles") != string::npos) {
            // Try to read number of vehicles after 'No of trucks' or 'VEHICLE'
            std::istringstream iss(line);
            std::string token;
            int found = 0;
            while (iss >> token) {
                if (isdigit(token[0])) {
                    m = stoi(token);
                    found = 1;
                    break;
                }
            }
            if (!found) {
                // Try to read next line if not found in this line
                std::string nextline;
                if (getline(cin, nextline)) {
                    std::istringstream iss2(nextline);
                    while (iss2 >> token) {
                        if (isdigit(token[0])) {
                            m = stoi(token);
                            break;
                        }
                    }
                }
            }
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
    if (m <= 0) m = 5; // fallback if not found
    loc.resize(n + 1);
    demand.resize(n + 1);
    // File uses 1-based indexing, 1 is depot
    for (int i = 0; i <= n; ++i) {
        loc[i] = coords[i];
        demand[i] = demands_tmp[i];
    }
}



void output(){
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

int main() {
    namespace fs = std::filesystem;
    std::ofstream fout("output.txt");
    for (const auto& entry : fs::directory_iterator("data")) {
        if (!entry.is_regular_file()) continue;
        std::string fname = entry.path().filename().string();
        if (fname.size() < 4 || fname.substr(fname.size() - 4) != ".vrp") continue;
        std::ifstream fin(entry.path());
        if (!fin) continue;
        // Clear all global state before processing a new file
        dist.clear();
        demand.clear();
        loc.clear();
        routes.clear();
        load.clear();
        duration.clear();
        tabu_list_swap.clear();
        tabu_list_switch.clear();
        tabu_list_2_opt.clear();
        tabu_list_relocate.clear();
        angle_customer.clear();
        closest_neighbors.clear();
        freq.clear();
        optimal_value = -1;
        n = 0; m = 0; Q = 0; depot = 0;
        std::cin.rdbuf(fin.rdbuf());
        std::ostringstream buffer;
        std::streambuf* old_cout = std::cout.rdbuf(buffer.rdbuf());
        auto start = chrono::high_resolution_clock::now();
        input();
        init();
        output();
        auto end = chrono::high_resolution_clock::now();
        chrono::duration<double> elapsed = end - start;
        std::cout << "Elapsed time: " << elapsed.count() << " seconds" << std::endl;
        std::cout.rdbuf(old_cout);
        fout << "File: " << fname << std::endl;
        fout << buffer.str() << std::endl;
    }
    return 0;
}