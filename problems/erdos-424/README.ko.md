[English](README.md) | **한국어**

# Erdős problem #424: 10^10까지의 정확한 개수와 Lean으로 검증한 구조

Upstream 명제(FormalConjectures docstring, 출처
[erdosproblems.com/424](https://www.erdosproblems.com/424)):

> Let $a_1 = 2$ and $a_2 = 3$ and continue the sequence by appending to
> $a_1, \ldots, a_n$ all possible values of $a_i a_j - 1$ with $i \neq j$.
> Is it true that the set of integers which eventually appear has positive
> density?

이 집합을 $S$(upstream의 `generatedSet`, OEIS
[A005244](https://oeis.org/A005244)에 수열로 등재)라 하고
$A(N)=\#\{n\le N : n\in S\}$라 쓴다. Ben Green의 open problem 63도 같은 질문이다.
**이 문제는 여전히 미해결이며, 여기의 어떤 결과도 이를 해결하지 않는다.** 이
디렉터리에는 Lean으로 검증한 구조적 사실과 $S\cap[0,10^{10}]$의 정확한 계산을
기록한다. 유한한 데이터로는 양의 밀도를 증명할 수도, 반증할 수도 없다.

## 검증된 결과

### Lean: 잉여류 장애물과 다항식 크기의 상하한

[`Erdos424.lean`](../../AgenticConjectures/Erdos424.lean)은 upstream의 세 정의를
글자 그대로 다시 적고, 아래 정리들을 `sorry`, 추가 공리, `native_decide` 없이
증명한다. 사용하는 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐이다.

| 선언 | 내용 |
|---|---|
| `mem_generatedSet_iff` | $n\in S \iff n=2 \lor n=3 \lor \exists\,x\ne y\in S,\ n=xy-1$ |
| `lt_mul_sub_one` | 서로 다른 $x,y\in S$에 대해 $x<xy-1$이고 $y<xy-1$ |
| `two_le_of_mem` | $n\in S\Rightarrow n\ge2$ |
| `mod_three_ne_one` | $n\in S\Rightarrow n\not\equiv1\pmod 3$ |
| `three_mul_countingFn_le` | 모든 $N$에 대해 $3A(N)\le2N$ |
| `le_two_thirds_of_tendsto` | $A(N)/N\to\alpha$이면 $\alpha\le2/3$ |
| `pow_two_add_one_mem`, `generatedSet_infinite` | $k\ge1$이면 $2^k+1\in S$이고, $S$는 무한집합 |
| `le_sixteen_mul_countingFn_sq` | $N\ge5$이면 $N\le16\,A(N)^2$, 즉 $A(N)\ge\sqrt N/4$ |
| `not_mem_of_prime_succ` | $n+1$이 소수이고 $n\ge4$이면 $n\notin S$ |
| `three_mul_prime_sub_one_not_mem` | $p$가 소수이고 $p\equiv1\pmod3$이면 $3p-1\notin S$ |
| `infinite_nonmembers_zero_mod_three`, `infinite_nonmembers_two_mod_three` | 허용 잉여류 $0$과 $2\pmod 3$ 각각에 비원소가 무한히 많음 |

하한 $\sqrt N/4$는 수치적으로 관찰되는 선형 증가와 거리가 멀며, 양의 밀도를
향한 한 걸음도 아니다. 데이터는 상한 $2/3$ 아래에 머물며, $10^{10}$에서의
비율은 $0.5474$이다.

### $N=10^{10}$까지의 정확한 계산

서로 독립적인 두 프로그램이 $S\cap[0,10^{10}]$ 전체의 비트셋(1.25 GB)을
계산한다.

- [`erdos424_ascending.cpp`](erdos424_ascending.cpp) (A)는 $y$를 오름차순으로
  훑으면서 더 작은 모든 원소 $x$에 대해 $xy-1$을 표시한다. 원소의 두 인수가
  모두 그 원소보다 작으므로(`lt_mul_sub_one`) 이 방식은 정당하다.
- [`erdos424_generations.cpp`](erdos424_generations.cpp) (B)는 upstream의 세대
  $A_0=\{2,3\}$, $A_{k+1}=A_k\cup\{xy-1\}$를 정의 그대로 계산한다. 두 개의 비트
  평면 위에서 semi-naive 방식으로 평가하며, 한 세대가 아무것도 추가하지 않으면
  멈춘다.

두 프로그램은 출력하는 모든 값에서 일치한다. 비트셋 전체의 64비트 해시,
모든 체크포인트 $c\cdot10^k$ ($c=1,2,5$)에서의 개수, 36 이하의 법 26개에 대한
잉여류별 개수, 처음 100개의 비원소가 모두 같다. 또한 두 프로그램 모두
$10^5$까지 upstream 재귀를 글자 그대로 옮긴 Python 구현과 비트 단위로
일치한다. 이 값들과 B의 세대별 분포는 모두
[`counts_result.json`](counts_result.json)에 있다.

| $N$ | $A(N)$ | $A(N)/N$ | 허용된 약 $2N/3$개의 $n\not\equiv1\ (3)$ 중 비율 |
|---:|---:|---:|---:|
| $10^2$ | 23 | 0.230000 | 0.348485 |
| $10^3$ | 250 | 0.250000 | 0.375375 |
| $10^4$ | 3,207 | 0.320700 | 0.481098 |
| $10^5$ | 39,843 | 0.398430 | 0.597651 |
| $10^6$ | 457,599 | 0.457599 | 0.686399 |
| $10^7$ | 4,952,270 | 0.495227 | 0.742841 |
| $10^8$ | 51,899,129 | 0.518991 | 0.778487 |
| $10^9$ | 535,276,618 | 0.535277 | 0.802915 |
| $10^{10}$ | 5,473,663,856 | 0.547366 | 0.821050 |

체크포인트 $200$부터는 기록된 모든 체크포인트에서 $A(N)/N$이 증가한다. 마지막
세 자릿수 구간의 증가량은 각각 $0.024$, $0.016$, $0.012$이다. $n\bmod 6$의 각
잉여류도 $10^3$부터 매 자릿수마다 증가한다([상세 문서](DETAILS.ko.md#5-잉여류별-데이터)
참고). $10^{10}$에서 홀수 허용 잉여류는 약 97%가 채워져 있고, $2\pmod 6$은
86%, $0\pmod 6$은 48%만 채워져 있다.

### 여집합의 구조

- $1\pmod 3$ 잉여류 밖에서 가장 작은 비원소: 6, 8, 11, 12, 15, 18, 20, 21, 23,
  24, 29, 30, 32, 35, 36, …
- $m\le 1000$인 모든 법에 대해, $2,3$을 포함하고 $(a,b)\mapsto ab-1$에 대해
  닫힌 가장 작은 잉여류 집합은 정확히 $\not\equiv1\pmod 3$인 잉여류들의
  집합이다(검증 스크립트로 확인, CI는 $m\le300$까지 확인). 따라서 이 닫힘
  논법으로는 다른 잉여류 장애물이 나올 수 없다. $10^{10}$에서 기록된 26개의 법
  각각에 대해 $\not\equiv1\pmod3$인 모든 잉여류에 원소가 있다. 이런 잉여류 중
  가장 희박한 것은 $n\equiv0\pmod 6$에 속하는 잉여류들이다(예: $0\pmod{30}$은
  36%만 채워짐). 거의 다 채워진 잉여류도 있다. $17\pmod{36}$은 99.99%가
  채워져 있다.
- 허용된 $n$에 대해 $n+1$이 $2\le x<y$이고 $x,y\not\equiv1\pmod 3$인
  분해 $xy$를 갖지 않으면 $n$을 *분해 불가능*이라 부르자. `mod_three_ne_one`에
  의해 이런 $n$은 (2, 3을 제외하면) 결코 원소가 아니다. 이들은 정확히
  $n+1$의 소인수분해가 제한된 짝수 $n$이다([상세 문서](DETAILS.ko.md#4-여집합의-산술적-부분)에
  기술). 고전적인 추정에 따르면 이들의 밀도는 0이지만, 감소 속도는
  $1/\sqrt{\log N}$ 정도로 매우 느리다.
  [`erdos424_factorable.cpp`](erdos424_factorable.cpp)는 $S$를 계산하지 않고
  이들의 개수를 센다. 여집합의 나머지는 *동역학적* 누락이다. 허용되는 분해는
  존재하지만, 어떤 분해의 두 인수도 함께 $S$에 속하지 않는 경우이다.

아래 표는 전체 $n\le N$에 대한 비율이다. $E$는 분해 불가능한 허용 비원소,
$D$는 동역학적 누락의 개수이며, $1\pmod 3$ 잉여류가 나머지 3분의 1을
차지한다.

| $N$ | $A(N)/N$ | 산술적 $E(N)/N$ | 동역학적 $D(N)/N$ | 허용 여집합 중 산술적 부분의 비율 |
|---:|---:|---:|---:|---:|
| $10^{2}$ | 0.2300 | 0.1900 | 0.2400 | 0.442 |
| $10^{3}$ | 0.2500 | 0.1560 | 0.2600 | 0.375 |
| $10^{4}$ | 0.3207 | 0.1344 | 0.2115 | 0.389 |
| $10^{5}$ | 0.3984 | 0.1193 | 0.1489 | 0.445 |
| $10^{6}$ | 0.4576 | 0.1087 | 0.1004 | 0.520 |
| $10^{7}$ | 0.4952 | 0.1005 | 0.0709 | 0.586 |
| $10^{8}$ | 0.5190 | 0.0940 | 0.0537 | 0.636 |
| $10^{9}$ | 0.5353 | 0.0886 | 0.0428 | 0.674 |
| $10^{10}$ | 0.5474 | 0.0840 | 0.0353 | 0.704 |

$10^6$부터는 산술적 부분이 허용 여집합의 절반 이상을 차지하며($10^{10}$에서
70%), 천천히 감소한다. 동역학적 부분은 더 빠르게 감소한다. $E$의 밀도가
0이므로, 동역학적 누락의 밀도도 0이라면 $A(N)/N\to2/3$이 따라 나온다. 그러나
그 사실도, 양의 하밀도도 증명되지 않았다.

## 재현

저장소 루트에서 실행한다.

```bash
python3 problems/erdos-424/verify_counts.py                 # N = 10^9 (CI)
python3 problems/erdos-424/verify_counts.py --limit 10000000000
python3 problems/erdos-424/verify_counts.py --part sieves --closure-limit 1000
lake build AgenticConjectures.Erdos424
```

검증 스크립트는 세 C++ 프로그램을 `g++ -O3 -std=c++17`로 컴파일한다. A와
B를 서로 비교하고, 둘을 Python 참조 구현과 비교하며, 분해 가능한 수의
개수를 Python 약수 열거와 비교한 뒤, 모든 값을
[`counts_result.json`](counts_result.json)과 대조한다. 실행 시간은
2026-10-24에 부하 평균이 8에서 87 사이였던 공유 Apple M5 Max에서 측정했으며,
부하가 낮으면 더 짧다.

| 명령 | 실행 시간 | 최대 메모리 |
|---|---:|---:|
| `verify_counts.py --part sieves` ($10^9$, 닫힘 검사 $m\le300$; CI) | 29초 | 0.25 GB |
| `verify_counts.py --part factorable` ($10^9$; CI) | 22초 | 0.13 GB |
| `verify_counts.py --limit 10000000000` | 700초 | 2.5 GB |
| 그중 $10^{10}$에서의 A, B, factorable | 136초, 249초, 313초 | 1.26, 2.51, 1.25 GB |
| 300 대신 `--closure-limit 1000` | 약 11초 추가 | |
| `erdos424_probe 1000000 500` | 1.3초 | |
| `lake build AgenticConjectures.Erdos424` (이 모듈만) | 15초 | |

## 명제의 충실성

`nextGeneration`, `sequenceSet`, `generatedSet`은
[upstream snapshot](upstream/README.md)에서 글자 그대로 옮겼다. 연구 명제
`erdos_424 : answer(sorry) ↔ generatedSet.HasPosDensity`는 다시 적지 않았다.
`Set.HasPosDensity`가 이 저장소에서 쓸 수 없는 `FormalConjecturesForMathlib`에
정의되어 있기 때문이다. 대신 모듈은
`countingFn N = (generatedSet ∩ Set.Iic N).ncard`를 정의하므로 $A(N)$은
$n\le N$을 센다. $n<N$을 세도 $A(N)$은 많아야 1만큼 달라지므로 어떤 극한도
바뀌지 않는다. 모든 원소는 2 이상이므로 서로 다른 원소에 대해
$x\cdot y\ge6$이고, 자연수 뺄셈 $x\cdot y-1$은 절대 잘리지 않는다.
"서로 다름"은 upstream과 같이 값의 부등식 $x\ne y$이다. $S$가 집합이므로 이는
원래 수열의 $i\ne j$와 일치한다. C++ 프로그램도 같은 규약과 잘림 없는 산술을
쓴다. 입력을 $N\le2^{40}$으로 제한하므로 프로그램이 만드는 모든 곱은
$2^{64}$보다 훨씬 작다.

## 주장하지 않는 것

- $S$의 양의 밀도(또는 그 부정). 증가하는 비율은 증거일 뿐 증명이 아니다.
  천천히 감소하는 산술적 부분은 어떤 극한이 있더라도 매우 느리게 접근함을
  보여 준다.
- 모든 법에 대해 $1\pmod 3$ 잉여류가 유일한 잉여류 장애물이라는 것. 닫힘
  검사는 $m\le1000$까지만 다룬다.
- 새로움. mod 3 장애물과 $2^k+1$ 가족은 초등적이며 이미 알려져 있을 가능성이
  높다. 이번 갱신에서는 upstream 참고문헌 외의 문헌 조사를 하지 않았다.

## 이전 탐색 프로그램

[`erdos424_probe.cpp`](erdos424_probe.cpp)는 원래의 정확한 탐색 프로그램이며,
그 결과는 기록된 적이 없었다. 2026-10-24에
`erdos424_probe 1000000 500`은 `count 457599 density 0.457599`, mod 3의 마지막
비원소 `999996`(잉여류 0)과 `999992`(잉여류 2)를 출력했고, 후보 잉여류는
출력하지 않았다. 즉 $10^6$까지 $m\le500$인 모든 법의 모든 잉여류에 $1000$보다
큰 비원소가 여전히 있다. 이 개수는 위의 $A(10^6)$과 일치한다. 실행에는 약
1.3초가 걸렸다.
