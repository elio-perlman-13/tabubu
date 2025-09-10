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


const int MAX_ITER = 2000; // max iterations for Tabu Search
const int nmax = 50; // for early stopping if no improvement
const int TABU_TENURE = 10; // tenure for tabu search

const int NUM_NEIGHBORHOODS = 4;
const int MAX_SEGMENT = 20;
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

// Generate an initial feasible solution using a sweep-like heuristic
Solution generate_initial_solution() {
    Solution sol;
    // 1. Compute angles
    int depot_x = loc[0].first, depot_y = loc[0].second;
    for (int i = 1; i <= n; ++i) {
        double dx = loc[i].first - depot_x;
        double dy = loc[i].second - depot_y;
        double angle = atan2(dy, dx);
        angle_customer.push_back({angle, i});
    }
    sort(angle_customer.begin(), angle_customer.end());

    // 2. Randomly choose starting customer
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> dis(0, n-1);
    int start_idx = dis(gen);

    // 3. Build sequence
    vi seq;
    for (int i = 0; i < n; ++i)
        seq.push_back(angle_customer[(start_idx + i) % n].second);

    // 4. Construct routes
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

// Precompute closest neighbors for all customers
void compute_closest_neighbors(int p1) {
    closest_neighbors.assign(n+1, vector<int>());
    for (int i = 1; i <= n; ++i) {
        vector<pair<double, int>> neigh;
        for (int j = 1; j <= n; ++j) {
            if (i == j) continue;
            neigh.push_back({dist[i][j], j});
        }
        sort(neigh.begin(), neigh.end());
        for (int t = 0; t < min(p1, (int)neigh.size()); ++t)
            closest_neighbors[i].push_back(neigh[t].second);
    }
}

Solution find_best_neighbor(Solution sol, int neighbor_id, int current_iter, double best_cost){
    Solution best_neighbor = sol;
    double best_neighbor_cost = 1e18;

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
                    //SWAP_WITHIN_A_ROUTE
                    int route = sol.customer_vehicle[i];
                    int pos_i = find(neighbor.routes[route].begin(), neighbor.routes[route].end(), i) - neighbor.routes[route].begin();
                    int pos_j = find(neighbor.routes[route].begin(), neighbor.routes[route].end(), j) - neighbor.routes[route].begin();
                    if (pos_i == 0 || pos_j == 0 || pos_i == neighbor.routes[route].size()-1 || pos_j == neighbor.routes[route].size()-1) continue;

                    int before_i = neighbor.routes[route][pos_i-1];
                    int after_i  = neighbor.routes[route][pos_i+1];
                    int before_j = neighbor.routes[route][pos_j-1];
                    int after_j  = neighbor.routes[route][pos_j+1];

                    double delta;
                    if (pos_j == pos_i + 1) {
                        delta = dist[before_i][j] + dist[j][i] + dist[i][after_j]
                            - dist[before_i][i] - dist[i][j] - dist[j][after_j];
                    } else {
                        delta = dist[before_i][j] + dist[j][after_i]
                            + dist[before_j][i] + dist[i][after_j]
                            - dist[before_i][i] - dist[i][after_i]
                            - dist[before_j][j] - dist[j][after_j];
                    }
                    swap(neighbor.routes[route][pos_i], neighbor.routes[route][pos_j]);
                    neighbor.duration[route] += delta;
                    neighbor.total_cost += delta;
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
            tabu_list_swap[best_i][best_j] = current_iter + TABU_TENURE;
        }
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

                        double delta_i = (dist[u][j] + dist[j][v]) - (dist[u][i] + dist[i][v]);
                        double delta_j = (dist[x][i] + dist[i][y]) - (dist[x][j] + dist[j][y]);
                        swap(neighbor.routes[route_i][pos_i], neighbor.routes[route_j][pos_j]);
                        swap(neighbor.customer_vehicle[i], neighbor.customer_vehicle[j]);
                        neighbor.duration[route_i] += delta_i;
                        neighbor.duration[route_j] += delta_j;
                        neighbor.total_cost += delta_i + delta_j;

                    }
                    else continue;
                }
                if (load[route_i] > Q || neighbor.load[route_j] > Q) {
                    continue;
                }
                else {
                    //check tabu and aspiration criteria
                    bool is_tabu = (tabu_list_switch[i][j] >= current_iter);
                    if (is_tabu && neighbor.total_cost >= best_cost) continue;
                    if (neighbor.total_cost < best_cost) {
                        best_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                    if (neighbor.total_cost < best_neighbor_cost) {
                        best_neighbor_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                }
            }
        }
        if (best_i != -1 && best_j != -1) {
            tabu_list_swap[best_i][best_j] = current_iter + TABU_TENURE;
        }
    }
    if (neighbor_id == 2){
        //2-opt operation
        int best_k = -1;
        int best_i = -1;
        int best_j = -1;
        for (int k = 1; k <= m; k++){
            if (sol.routes[k].size() <= 3) continue;
            Solution neighbor = sol;
            for (int i = 1; i < neighbor.routes[k].size() - 3; i++) {
                for (int j = i + 1; j < neighbor.routes[k].size() - 2; j++) {
                    int prev_i = neighbor.routes[k][i - 1];
                    int next_j = neighbor.routes[k][j + 1];
                    int cus_i = neighbor.routes[k][i];
                    int cus_j = neighbor.routes[k][j];

                    // Update total cost
                    double delta = 0;
                    delta -= (dist[prev_i][cus_i] + dist[cus_j][next_j]);
                    delta += (dist[prev_i][cus_j] + dist[cus_i][next_j]);
                    neighbor.duration[k] += delta;
                    neighbor.total_cost += delta;

                    reverse(neighbor.routes[k].begin() + i, neighbor.routes[k].begin() + j + 1);

                    // Check tabu and aspiration criteria
                    bool is_tabu = (tabu_list_2_opt[k][i][j] >= current_iter);
                    if (is_tabu && neighbor.total_cost >= best_cost) continue;
                    if (neighbor.total_cost < best_cost) {
                        best_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                    if (neighbor.total_cost < best_neighbor_cost) {
                        best_neighbor_cost = neighbor.total_cost;
                        best_neighbor = neighbor;
                    }
                }
            }
        }
        if (best_k != -1 && best_i != -1 && best_j != -1) {
            tabu_list_2_opt[best_k][best_i][best_j] = current_iter + TABU_TENURE * n;
        }
    }
    if (neighbor_id == 3){
        Solution neighbor = sol;
        int best_i = -1;
        int best_k = -1;
        //RELOCATE CUSTOMER I TO ANOTHER ROUTE K AT OPTIMAL LOCATION
        for (int i = 1; i <= n; i++){
            int route_i = neighbor.customer_vehicle[i];
            int pos_i = find(neighbor.routes[route_i].begin(), neighbor.routes[route_i].end(), i) - neighbor.routes[route_i].begin();
            for (int k = 1; k <= m; k++) {
                if (k == route_i) continue;
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
                    double delta_i = dist[neighbor.routes[route_i][pos_i - 1]][i] + dist[i][neighbor.routes[route_i][pos_i]] + best_insertion_cost;
                    neighbor.duration[route_i] += delta_i;
                    neighbor.duration[k] += best_insertion_cost;
                    neighbor.total_cost += delta_i;
                    neighbor.customer_vehicle[i] = k;

                    neighbor.routes[k].insert(neighbor.routes[k].begin() + best_pos, i);
                    neighbor.routes[route_i].erase(neighbor.routes[route_i].begin() + pos_i);

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
    }
    return best_neighbor;
}

Solution tabu_search(Solution sol, int max_iter, int max_segment) {
    Solution best_solution = sol;
    double best_cost = sol.total_cost;
    double score[NUM_NEIGHBORHOODS] = {0.0};
    double weight[NUM_NEIGHBORHOODS] = {1.0/NUM_NEIGHBORHOODS};
    int count[NUM_NEIGHBORHOODS] = {0};

    Solution current_sol = sol;
    for (int segment = 1; segment <= max_segment; segment++) {
        int iter = 0;
        int no_improve = 0;
        tabu_list_swap.resize(n + 5, vector<int>(n + 5, 0));
        tabu_list_switch.resize(n + 5, vector<int>(n + 5, 0));
        tabu_list_2_opt.resize(m + 5, vector<vector<int>>(n + 5, vector<int>(n + 5, 0)));
        tabu_list_relocate.resize(m + 5, vector<int>(n + 5, 0));
        while (iter < max_iter) {
            //write_here
            int current_iter[NUM_NEIGHBORHOODS] = {0};
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
            Solution neighbor = find_best_neighbor(current_sol, neighbor_id, current_iter[neighbor_id], best_cost);
            
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

            current_sol = neighbor;
            iter++;
        }
    }

    return best_solution;
}

void init() {
    build_distance_matrix();
    compute_closest_neighbors(int(0.2 * n)); // p1 = 20% of n
}

void input(){
    cin >> n >> m;
    cin >> Q;
    loc.resize(n + 5);
    demand.resize(n + 5);
    for (int i = 0; i <= n; ++i) {
        cin >> loc[i].first >> loc[i].second >> demand[i];
    }
}



void output(){
    Solution sol = generate_initial_solution();
    print_solution(sol);
    Solution best_sol = tabu_search(sol, MAX_ITER, MAX_SEGMENT);
    cout << "Best solution found:" << endl;
    print_solution(best_sol);
}

int main(){
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    input();
    init();
    output();
}