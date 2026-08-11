[English](README.md) | **한국어**

# Graph-colouring reconfiguration radius, Question 15

Cambie–Cames van Batenburg–Cranston Q15의 반례를 exact BFS로 탐색합니다.

- `recolor_radius_search.py`: NetworkX graph atlas 기반 Python 검사
- `recolor_radius_exact.cpp`: graph6 입력과 shard 탐색을 지원하는 C++ 구현
- `recolor_radius_exact`: 저장된 Linux x86-64 빌드 산출물

```bash
python3 problems/recoloring-radius-q15/recolor_radius_search.py --help
g++ -O3 -std=c++17 problems/recoloring-radius-q15/recolor_radius_exact.cpp \
  -o /tmp/recolor_radius_exact
```
