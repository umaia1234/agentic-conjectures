[English](README.md) | **한국어**

# Fonollosa 추측 1: 유일 중복집합 합 문제의 최소 법

법 $N$에 대한 서로 다른 잉여 $n$개의 집합 $A=\{a_0,\dots,a_{n-1}\}$에서
다음을 만족하는 $k\in\mathbb Z_{\ge0}^n$이 모두-1 벡터뿐이면 $A$를
**유효**(valid)하다고 한다.

$$\sum_i k_i=n,\qquad \sum_i k_ia_i\equiv\sum_i a_i\pmod N .$$

다시 말해 $A$에서 뽑은 크기 $n$의 중복집합 가운데 합이 법 $N$으로 $\sum A$인
것은 모두-1 중복집합뿐이라는 뜻이다. 유효성은 평행이동과 단원 곱셈(아핀 사상
$x\mapsto ux+v$)으로 변하지 않으며, 유효한 집합의 부분집합도 유효하다.

J. A. R. Fonollosa,
[*Minimum modulus for the unique multiset-sum problem*](https://arxiv.org/abs/2607.08366)
(arXiv:2607.08366v2, 2026년 7월 14일)은 초증가 집합
$\{2^k-1:0\le k\le n-1\}$이 법 $N=2^n-2^{\lfloor\log_2n\rfloor}$에서 유효하고
그보다 작은 법에서는 유효하지 않음을 증명했다. 저자는 이를 Lean으로도
형식화했다. 논문은 어떤 집합도 이보다 나을 수 없다고 추측한다(§1의 추측 1).

$$n\ge2,\quad N<2^n-2^{\lfloor\log_2n\rfloor}\ \Longrightarrow\ \mathbb Z_N\text{의 어떤 }n\text{-부분집합도 유효하지 않다.}$$

$n=2,\dots,13$에서 $2^n-2^{\lfloor\log_2n\rfloor}$의 값은
$2,6,12,28,60,124,248,504,1016,2040,4088,8184$이다. 우리가 복사한
[formal-conjectures 명제](upstream/README.md)(Apache-2.0)는 이를 다음과 같이
적는다.

> For every $n \geq 2$ and every $N < 2^n - 2^{\lfloor \log_2 n\rfloor}$, no
> set of $n$ residues mod $N$ is valid.

추측은 여전히 **미해결**이다. 이 디렉터리는 부분 결과를 기록하며 상태는
`partial`이다.

## 결과

### Lean(커널 검증; `sorry`, 추가 공리, `native_decide` 없음)

[`MinModulusMultisetSum.lean`](../../AgenticConjectures/MinModulusMultisetSum.lean)은
$N>0$이고 $|A|=n$인 모든 유효한 $A\subseteq$ `ZMod N`에 대해 다음을 증명한다.

| 선언 | 명제 | 비고 |
|---|---|---|
| `IsValidMod.two_pow_le` | $2^{n-1}\le N$ | 평행이동한 부분합이 서로 다르다. Inal 정리의 순환군 경우 |
| `IsValidMod.card_mul_card_sub_one_le` | $n(n-1)\le N$ | Sidon형 성질: $x+w=y+z$, $x\ne w$이면 $\{x,w\}=\{y,z\}$ |
| `IsValidMod.two_pow_add_le` | $n\ge2$에서 $2^{n-1}+n-2\le N$ | 두 배 한 차 $2(b-a_0)$는 공집합이 아닌 평행이동 부분합을 피한다 |
| `statement_of_le_four` | $n\le4$에서 추측 1 | 이때 $2^n-2^{\lfloor\log_2n\rfloor}=n(n-1)$ |

증명은 [DETAILS.ko.md](DETAILS.ko.md)에 자세히 적었다. `statement` 자체는
증명하지 않았다.

### $n\le9$ 전수 탐색(서로 독립적인 두 구현)

$3\le n\le9$인 모든 $n$과 $n\le N\le2^n+8$인 모든 법에 대해, 두 프로그램은
법 $N$의 유효한 $n$-집합을 아핀 사상을 무시하고 모두 나열했으며 모든 법에서
결과가 일치했다.

| $n$ | 추측된 최솟값 | 유효한 $n$-집합이 있는 법 $N\le2^n+8$ (아핀 궤도가 둘 이상이면 그 개수) | 실행 시간 `mmsearch` / `mmcheck` |
|---|---|---|---|
| 3 | 6 | 6, 7, 8 (2), 9, 10 (2), 11, 12 (5), 13 (2), 14 (4), 15 (4), 16 (6) | < 0.1초 / < 0.1초 |
| 4 | 12 | 12, 14 (2), 15 (2), 16 (3), 17, 18 (8), 19 (2), 20 (10), 21 (8), 22 (11), 23 (5), 24 (31) | < 0.1초 / < 0.1초 |
| 5 | 28 | 28, 30 (5), 31, 32 (4), 34 (7), 35, 36 (29), 37 (2), 38 (22), 39 (11), 40 (45) | < 0.1초 / < 0.1초 |
| 6 | 60 | 60, 62 (2), 63, 64 (2), 68 (6), 70 (6), 72 (61) | < 0.1초 / < 0.1초 |
| 7 | 124 | 124, 126, 127, 128 | 0.2초 / 0.2초 |
| 8 | 248 | 248, 252, 254 (2), 255, 256 | 18.7초 / 37.6초 |
| 9 | 504 | 504, 508, 510, 511, 512 | 6519초 / 15753초 |

실행 시간은 법별 시간을 모두 더한 값이다. `mmsearch`는 각 법을 벽시계
시간으로, `mmcheck`는 프로세스 CPU 시간으로 잰다.

따라서 모든 $n\le9$에 대해 다음이 성립한다.

- **추측 1이 성립한다.** $N<2^n-2^{\lfloor\log_2n\rfloor}$인 어떤 법에서도
  유효한 $n$-집합은 없다.
- **추측된 최솟값에서 극값 집합은 유일하다.** 법
  $N=2^n-2^{\lfloor\log_2n\rfloor}$의 유효한 $n$-집합은 모두 $\{2^k-1\}$의
  아핀 상이다. 이는 $n\le9$에서 논문의 열린 문제 2에 해당한다.
- **유효한 법의 집합에는 틈이 있다.** 예를 들어 법 13에서는 유효한 4-집합이
  없고, 법 29와 33에서는 유효한 5-집합이 없다. $n=7,8,9$에서는 $2^n+8$
  이하에서 유효한 집합을 갖는 법이 네다섯 개뿐이다. $n=8$, 법 254의 두 번째
  궤도는 $\{0,1,64,96,112,120,124,126\}$이다.

### 출처를 넘어서는 부분과 재현에 해당하는 부분

- 논문은 CP-SAT로 $n\le7$에서 추측 1을 인증했다(법마다 실행 불가능성 인증서
  하나). $n\le13$에 대해서는 솔버와 GPU 탐색이 추측된 최솟값보다 작은 법에서
  유효한 집합을 찾지 못했고, 찾은 최소 해는 모두 초증가 집합으로 환원되었다고
  보고한다. 우리의 $n\le7$ 경우는 인증된 범위를 재현한다. $n=8,9$의 경우와
  $n\le9$에서 최솟값의 유일성은, 논문의 근거가 탐색인 곳에서 전수 탐색으로
  얻은 결과이다.
- $2^{n-1}\le N$은 아래에 소개하는 M. Inal의 하한을 순환군에서 재현한 것이다.
  [DETAILS.ko.md](DETAILS.ko.md)의 보조정리 5는 Inal이 등호 경우에 쓰는
  논증이다. 정리 3($2^{n-1}+n-2$)은 여기에 두 배 한 차의 개수 세기를 더한
  것이다. Sidon형 하한 $n(n-1)$은 초등적이다. 아래 출처에서 이 두 하한을 찾지
  못했지만 새로움을 주장하지는 않는다.
- $n\le4$에서의 추측 1은 CP-SAT 범위 안에 있다. 이 경우들에 새로 더한 것은
  업스트림 정의에 대한 커널 검증 증명이다.

## 알려진 하한과, 하한이 "열려 있어 보인다"는 언급

v2의 열린 문제 1은 모든 집합에 대해 성립하는 지수적 하한
$N_{\min}\ge c^n$조차 열려 있어 보인다고 언급한다. 논문의 정의에서 유효한
$n$-집합은 $N\ge2^{n-1}$을 만족한다. 이 정의는 업스트림 Lean 정의가 그대로
옮긴 것이고 우리도 바꾸지 않고 사용하며, 위의 `IsValidMod.two_pow_le`가 그
커널 검증 증명이다. 평행이동한 차 $a-a_0$들의 부분합은 모두 서로 다르다.
서로소인 $S,T$ 사이의 일치 $\sigma(S)=\sigma(T)$를 경쟁 중복집합으로 바꿀 수
있기 때문이다.

이는 M. Inal,
[*The Exact Minimum Order for Unique Multiset Sums in Finite Abelian Groups*](https://doi.org/10.17605/OSF.IO/C58Q9)
(2026년 7월 21일자 OSF 프리프린트, v2보다 한 주 뒤)의 논증이다. Inal은 모든
유한 아벨 군 $G$에서 $|G|\ge2^{n-1}$이고 등호는 $(\mathbb Z/2)^{n-1}$에서만
성립함을 증명했으며, 이로써 논문의 문제 4가 해결되었다. $G$가 순환군이고
$n\ge3$이면 $N\ge2^{n-1}+1$을 얻는다. v2의 문제 4 자체도 논문의 자매 연구에서
얻은 또 다른 지수적 하한 $\binom{2n}{n}/2^n\sim2^n/\sqrt{\pi n}$을 이미
인용한다. 저자의 저장소 [jarfo/min-modulus](https://github.com/jarfo/min-modulus)는
`MinModulus/AbelianMin.lean`에서 Inal의 정리를 형식화했고(2026년 7월 22일
커밋들), 그 README는 문제 4를 해결된 것으로, 추측 1을 미해결로 적고 있다.

따라서 유효성에 대한 우리의 해석은 논문과 일치하며, 그 언급은 Inal의
프리프린트보다 먼저 쓰였다. 우리가 아는 모든 하한은 추측된
$2^n-2^{\lfloor\log_2n\rfloor}$에 한참 못 미친다.

## 탐색 방법

두 프로그램은 $d<N$인 각 약수 $d$에 대해 정렬된 집합 $\{0<d<a_2<\dots\}$를
열거한다. 이때 $d$는 쌍들에 대한 $\gcd(x-y,N)$의 최솟값이고, 모든 쌍의 차는
$\gcd\ge d$를 만족하며, 어떤 *정규화된 상* $u(A-p)$도 $d$와 $a_2$ 사이에
원소를 갖지 않는다. 여기서 $p,q\in A$, $\gcd(q-p,N)=d$이고 $u$는
$u(q-p)=d$인 단원이다. 유효한 집합의 모든 아핀 궤도가 이 족과
만난다([DETAILS.ko.md](DETAILS.ko.md) §5). 유효성은 유전적이므로 깊이 우선
탐색은 유효한 접두 집합만 확장하고, 접두 집합의 정규화된 상 중 하나가 $a_2$에
대한 조건을 어기면 그 접두 집합을 가지치기한다.

- [`mmsearch.cpp`](mmsearch.cpp)(C++, 스레드)는 원소를 증가하는 순서로
  추가한다. 접두 집합의 $j$겹 중복집합 합집합을 비트셋으로 유지하고, 확장
  $P\cup\{x\}$를 $x+s\notin(k+1)P$와 $1\le g\le k$에 대한
  $s-gx\notin(k-g)P$로 검사한다. 정규화 사상 목록도 함께 유지한다.
- [`mmcheck.c`](mmcheck.c)(C)는 따로 작성했다. 중복집합을 직접
  센다(합마다 크기 $j$인 중복집합의 개수를 일정 값에서 잘라 저장한 표).
  $a_2$ 이후의 원소는 감소하는 순서로 추가하고, 정규성은 모든 노드에서
  처음부터 다시 계산한다.
- [`brute.py`](brute.py)는 축소 없이 $0$을 포함하는 모든 부분집합을
  검사하고, 유효한 것들을 아핀 궤도로 묶는다.
- [`verify_search.py`](verify_search.py)는 $n=3,\dots,9$에 대한 두
  프로그램의 커밋된 로그를 해석한다. 두 프로그램이 모든 법을 다루고 같은
  궤도를 보고하는지 확인한다. 보고된 모든 집합이 유효한지 Python으로 다시
  확인하고, 추측 1과 최솟값에서의 유일성도 확인한다. 기본 실행에서는 두
  프로그램을 다시 컴파일해 $n\le7$을 다시 돌려 로그와 비교하고, $n\le5$에
  대해($N\le16,24,30$) 전수 대입도 실행한다.

$n\le8$의 로그는 커밋된 소스를 `g++ -O3 -std=c++17 -pthread`와
`gcc -O3 -std=c11`로 컴파일해 얻었다. $n=9$ 실행에 쓴 바이너리는 커밋된
소스를 `clang++ -O3 -march=native -std=c++17`과
`clang -O3 -march=native -Wall -Wextra`로 빌드한 것과 바이트 단위로 같다.
`mmsearch`는 2 스레드로 돌았다(벽시계 54분, 노드 $4.1\cdot10^9$개).
`mmcheck`는 연속한 범위 $9..473$, $474..501$, $502..520$을 하나씩 맡은 단일
스레드 프로세스 세 개로 돌았고(벽시계 1시간 53분), 그 출력은
[`logs/mmcheck_n9.txt`](logs/mmcheck_n9.txt)에 이어 붙였다. 첫 프로세스는
$9..504$로 시작했지만 부하를 고르게 나누려고 $N=473$ 다음에 멈췄다. 기계는
다른 작업과 공유한 Apple M5 Max였다.

## 재현

저장소 루트에서 실행한다.

```bash
python3 problems/min-modulus-multiset-sum/verify_search.py
```

CI 검사이다. 모든 로그 확인, 두 프로그램으로 $n\le7$ 재계산, $n\le5$ 전수
대입을 수행한다. 로컬에서 약 4초 걸렸다.

```bash
python3 problems/min-modulus-multiset-sum/verify_search.py --recompute 8 --no-brute
```

두 프로그램으로 $n=8$을 다시 돌린다. 약 1분 걸린다(로컬에서 53초).

```bash
python3 problems/min-modulus-multiset-sum/verify_search.py --recompute 9 --threads 3 --no-brute
```

$n=9$를 다시 돌린다. 단일 스레드 기준으로 `mmsearch`에 약 1.8시간,
`mmcheck`에 약 4.4시간이 들며, 지정한 스레드 수로 나누어 실행된다(3
스레드로 벽시계 약 2시간).

```bash
lake build AgenticConjectures.MinModulusMultisetSum
```

Lean 모듈을 빌드한다. mathlib이 빌드되어 있으면 약 5초 걸린다.

## 명제 충실성

- `IsValidMod`와 `minModulus`는 업스트림 정의를 항 단위로 그대로 옮겼다.
  `statement`는 업스트림 정리 `min_modulus`의 명제를 한 글자도 바꾸지 않고
  옮겼다. `FormalConjecturesUtil` 없이 빌드하기 위한 조정(이름공간, 속성,
  모듈 헤더, sorry가 붙은 정리 대신 `def statement`)은 모듈 docstring에
  적었다.
- `#A = n`인 `A : Finset (ZMod N)`은 논문처럼 서로 다른 잉여 $n$개의
  집합이다. 중복도 함수 `m : ZMod N → ℕ`는 `A` 위의 값만 의미가 있다.
- $n\ge1$에서 `Nat.log 2 n`은 $\lfloor\log_2n\rfloor$이다.
  $2^{\lfloor\log_2n\rfloor}\le n<2^n$이므로 `minModulus`의 자연수 뺄셈은
  정확하다.
- 업스트림과 마찬가지로 `0 < N`은 `ZMod 0 = ℤ`를 배제한다. `ZMod 1`에는
  두 원소 부분집합이 없으므로 $N=1$은 자명하게 성립한다.
- 하한들은 모든 $N>0$과 모든 유효한 `A`에 대해 성립한다. 탐색은 잉여
  $0,\dots,N-1$로 작업하며, 그 정당성은 [DETAILS.ko.md](DETAILS.ko.md) §5의
  논증과 교차 검증에 기댄다. 프로그램 자체는 형식 검증되지 않았고, 탐색
  결과를 Lean으로 가져오지도 않았다.

## 주장하지 않는 것

- $n\ge10$이나 일반적인 경우의 추측 1 증명.
- 새로움이나 우선권. 저자에게 알리거나 formal-conjectures에 제출한 것은
  없다. 외부 제출에는 사람의 승인이 필요하다.

## 확인한 출처(2026-10-24)

- arXiv:2607.08366v2의 §1(추측 1), §7(기계 인증), §8(열린 문제).
- M. Inal, OSF 프리프린트, doi:10.17605/OSF.IO/C58Q9.
- `e7c78dd63955092b5f8d8a5fa826476337c0f4be` 시점의
  [jarfo/min-modulus](https://github.com/jarfo/min-modulus) (README와
  `MinModulus/AbelianMin.lean`).
- 이 문제와 arXiv:2607.08366 인용 문헌에 대한 arXiv API와 OpenAlex 검색.
  인용 문헌도, 이 추측을 다룬 다른 논문도 찾지 못했다.
- `c094b979118b89adb77cf5f8d923ac9dd2e51b1d` 시점의 formal-conjectures.
  여기서 `min_modulus`는 `research open`으로 분류되어 있다.
