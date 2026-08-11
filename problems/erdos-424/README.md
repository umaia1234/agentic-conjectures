# Erdős problem #424

\(n+1=xy\)인 서로 다른 기생성 정수 \(x,y\)로부터 오름차순으로
기생성 집합을 생성하고 잔여류별 누락을 탐색하는 exact 유한 실험입니다.

## FormalConjectures upstream

[로컬 upstream snapshot](upstream/README.md)은 양의 밀도를 묻는 정확한
Lean 명제를 보존한다. Green의 open problem 63은 같은 명제를 가리키는
alias일 뿐이며, 아래 유한 탐색은 양의 밀도를 증명하지 않는다.

```bash
g++ -O3 -std=c++17 problems/erdos-424/erdos424_probe.cpp -o /tmp/erdos424_probe
/tmp/erdos424_probe 1000000 500
```
