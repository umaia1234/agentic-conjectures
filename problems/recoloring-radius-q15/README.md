**English** | [한국어](README.ko.md)

# Graph-colouring reconfiguration radius, Question 15

We search for counterexamples to Cambie–Cames van Batenburg–Cranston Q15
by exact BFS.

- `recolor_radius_search.py`: Python check based on the NetworkX graph atlas
- `recolor_radius_exact.cpp`: C++ implementation supporting graph6 input and shard search
- `recolor_radius_exact`: stored Linux x86-64 build artifact

```bash
python3 problems/recoloring-radius-q15/recolor_radius_search.py --help
g++ -O3 -std=c++17 problems/recoloring-radius-q15/recolor_radius_exact.cpp \
  -o /tmp/recolor_radius_exact
```
