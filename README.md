# Tabu Search for CVRP

## Overview
This project implements a Tabu Search metaheuristic for solving the Capacitated Vehicle Routing Problem (CVRP). The algorithm is designed to efficiently find high-quality solutions for standard benchmark instances, supporting batch processing of multiple input files and robust feasibility checks.

## Algorithm Outline
- **Input Parsing:** Reads standard CVRP files, extracting node coordinates, demands, vehicle capacity, number of vehicles, and (if available) optimal value.
- **Initial Solution:** Constructs a feasible initial solution using a sweep-like heuristic based on customer angles from the depot.
- **Tabu Search:**
  - Iteratively improves the solution using adaptive neighborhoods:
    - Intra-route swap
    - Inter-route swap
    - 2-opt (route segment reversal)
    - Relocate (move customer between routes)
  - Tabu lists prevent cycling and encourage exploration.
  - Simulated annealing is used for occasional acceptance of worse solutions.
  - Adaptive neighborhood selection based on recent performance.
- **Feasibility Checking:** Only feasible routes (respecting capacity and customer assignment constraints) are counted in the final solution.
- **Batch Processing:** All `.vrp` files in the `data/` directory are processed, with results written to `output.txt`.

## File Structure
```
.
├── data/                # Input CVRP instances (A-n33-k5.vrp, ...)
├── output.txt           # Results for all processed files
├── tabu_CVRP.cpp        # Main C++ implementation
├── README.md            # This file
└── ...                  # Other project files
```

## Result Table
Below is the result table summarizing the performance of the algorithm on each benchmark file. For each file, the table reports the best cost found, the known optimal value (if available), whether the solution is feasible, the accuracy gap, and the elapsed time.

for MAX_SEGMENT = 100, MAX_ITER = 2000, NMAX = 100, TABU_TENURE = 10:
| File Name         | Best Cost | Optimal Value | Feasible | Accuracy Gap (%) | Elapsed Time (s) |
|-------------------|-----------|--------------|----------|------------------|------------------|
| A-n33-k5.vrp      |   674.12  |     661      |   Yes    |      1.98        |      4.61        |
| A-n45-k6.vrp      |  1049.43  |     944      |   Yes    |     11.17        |     46.22        |
| A-n45-k7.vrp      |  1237.35  |    1146      |   Yes    |      7.97        |     11.60        |
| A-n55-k9.vrp      |  1112.13  |    1073      |   Yes    |      3.65        |     22.19        |
| A-n62-k8.vrp      |  1368.70  |    1288      |   Yes    |      6.27        |     24.85        |
| A-n80-k10.vrp     |  1935.81  |    1763      |   Yes    |      9.80        |     59.63        |

- **Best Cost:** The best total route cost found by the algorithm.
- **Optimal Value:** The known optimal value from the input file (if available).
- **Feasible:** "Yes" if all routes in the solution are feasible, otherwise "No".
- **Accuracy Gap (%):** `((Best Cost - Optimal Value) / Optimal Value) * 100` (if optimal value is known).
- **Elapsed Time (s):** Time taken to solve the instance (in seconds).

## How to Run
1. Place all `.vrp` files to be tested in the `data/` directory.
2. Build and run the program:
   ```sh
   g++ -O2 -std=c++17 -o tabu_CVRP tabu_CVRP.cpp
   ./tabu_CVRP
   ```
3. Check `output.txt` for results and the summary table.

## Notes
- The program automatically clears all state between files to avoid memory errors.
- For debugging or performance analysis, run with AddressSanitizer:
  ```sh
  g++ -g -fsanitize=address -o tabu_CVRP tabu_CVRP.cpp
  ./tabu_CVRP
  ```

---

For questions or improvements, please open an issue or pull request.