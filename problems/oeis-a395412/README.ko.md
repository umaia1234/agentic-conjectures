[English](README.md) | **한국어**

# OEIS A395412: 비영성이 인증된 유한 범위 확장

전체 정의, 보조정리, 유한 증인의 해석은
[문제별 상세 문서](DETAILS.ko.md)를 참고하십시오.

## 상태

이것은 **무한 추측의 해결이 아니라 부분적인 진전**입니다.

[OEIS A395412](https://oeis.org/A395412)는 `a(n)`을

```text
P_n / d + d
```

가 소수가 되는 squarefree 정수 `d < p_n`의 개수로 정의합니다. 여기서
`P_n`은 `n`번째 primorial입니다. OEIS 항목은 84개 항을 공개하고 `a(n)`이
결코 0이 아니라고 추측합니다.

기록된 결과는 다음과 같으며 각각 따로 구분합니다.

1. 공개된 84개 항을 모두 재현합니다(원래 실행, 아래 참조).
2. **모든 `85 <= n <= 478`에 대해 `a(n) > 0`을 증명합니다.** 각 `n`마다
   증인 `d` 하나를 기록하고, 그 후보 `P_n/d + d`에는 PARI/GP
   `primecertisvalid`와 독립적인 Python 검사기가 확인한 ECPP 소수성 인증서가
   있습니다(다음 절).
3. `85 <= n <= 200`에서는 같은 증인들이 원래 실행에서 이미 PARI/GP
   `isprime`으로 증명되어 있었습니다.
4. 원래 실행은 `201 <= n <= 400`을 BPSW로 선별만 했습니다. 이제 이 구간은
   같은 증인으로 2번 항목에 포함되므로 **확률적 소수 선별만 된 구간은 더
   이상 남아 있지 않습니다.** `n > 478`에 대해서는 아무것도 주장하지
   않습니다.

## 85 <= n <= 478의 ECPP 인증서

**명제.** 모든 `85 <= n <= 478`에 대해
[`ecpp_witnesses.json`](ecpp_witnesses.json)의 `n` 행은 `P_n/d + d`가
소수인 squarefree `d < p_n`을 줍니다. 따라서 `a(n) >= 1`입니다. 인증서가
기대는 정리와 독립 검사기의 건전성 논증은
[상세 문서 5절](DETAILS.ko.md)에 있습니다.

**방법.**

- *증인 선택.* `d`는 후보가 PARI의 BPSW 판정 `ispseudoprime`을 통과하는
  가장 작은 squarefree `d < p_n`입니다. BPSW는 `d`를 고르는 데에만 쓰이며
  증명의 일부가 아닙니다. `85 <= n <= 400`에서 이 증인들은 원래 실행의
  `result.json`과 일치합니다(그 실행에서 200까지는 증명, 201..400은 선별).
- *증명.* [`a395412_ecpp.gp`](a395412_ecpp.gp)는 후보에 PARI/GP 2.19.0
  `primecert`를 실행하고, Atkin–Morain 인증서를 한 줄에 한 단계
  `[N, t, s, a, [x, y]]`씩 파일로 쓴 뒤 다시 읽어 `primecertisvalid`가 1을
  돌려줄 때만 받아들입니다. [`ecpp_certify.py`](ecpp_certify.py)는 `n`마다
  단일 스레드 `gp` 프로세스 하나를 실행하고(동시에 네 개) 행을 기록합니다.
- *독립 검사.* [`verify_witnesses.py`](verify_witnesses.py)는 PARI가
  필요 없습니다. 모든 후보를 `(n, d)`에서 다시 만들어 비트 길이와 십진 전개의
  SHA-256을 행과 비교하고, 자체 타원곡선 연산으로 ECPP 인증서를 검사합니다.
  이번 실행의 모든 인증서를 (gmpy2 정수로) 다시 검사했으며, CI에서는 커밋된
  표본 인증서 세 개를 순수 Python으로 검사하고 변조된 인증서가 거부되는지도
  확인합니다.

**데이터.** `ecpp_witnesses.json`에는 `n`마다 한 행이 있습니다: `n`,
`p_n`, `d`, 후보의 비트 길이, 십진 후보의 SHA-256, ECPP 단계 수, 인증서
파일의 SHA-256, `primecert`와 쓰기/읽기/`primecertisvalid` 검사에 든 PARI CPU
초, 실제 경과 초. 인증서는 모두 합쳐 79 MB(`n = 85`의 11 KB부터
`n = 478`의 523 KB까지)이므로 표본 세 개(`n = 85, 201, 300`)만
[`certificates/`](certificates/)에 커밋하고 나머지는 `ecpp_certify.py`로 다시
만듭니다. `nbthreads = 1`에서 PARI 2.19.0은 별도의 실행에서 다시 만들어도
바이트 단위로 같은 인증서를 냈습니다(`n = 201`은 네 번, `n = 337`은 두 번).

**측정한 실행 시간** (Apple M5 Max, PARI/GP 2.19.0, 단일 스레드 `gp`
프로세스 네 개. CPU 시간은 행마다 기록된 PARI `getabstime` 값의 합):

| 실행 | 범위 | CPU 시간 | 경과 시간 |
|---|---|---:|---:|
| `ecpp_certify.py` (`n = 337`에서 한 번 중단 후 재개) | 85..400 | 8980초 | 24.4 + 44.8분 |
| `ecpp_certify.py --budget-minutes 85` (예산으로 중단) | 401..478 | 15457초 | 80.8분 |
| `verify_witnesses.py --cert-dir ... --backend gmpy2 --jobs 4` | 85..478 | 1331초 | 6.9분 |
| `verify_witnesses.py` (CI 모드, 순수 Python) | 행 + 표본 3개 | | 20.4초 |

두 인증 실행은 다른 작업과 기계를 공유했으므로(18코어에서 부하 평균 약
60~100) 시간이 부풀려져 있습니다. 예를 들어 `n = 400`의 `primecert`는 실행
중에는 CPU 시간 106.5초가 걸렸지만, 부하가 적을 때 따로 시험했을 때는
73.0초였습니다. 가장 어려운 단일 증명은 `n = 467`(4654비트 후보, ECPP 168단계,
`primecert` CPU 시간 306초, 경과 시간 325초)이었습니다. CI 모드 검증기는 유휴
상태의 기계에서 실행했고, 전체 독립 검사는 유휴 상태에서 시작했지만 끝나기
전에 다른 작업들이 다시 기계에 부하를 걸었습니다. `n = 337`에서의 중단은
`gp` 프로세스 하나가 출력도 PARI 오류도 없이 끝난 것이었습니다(외부에서
종료되었을 가능성이 가장 큽니다). 이후 `n = 337`만 따로 실행하자 성공했고,
`ecpp_certify.py`는 이제 그런 프로세스를 다시 실행하며, 재개된 실행은
`n = 335`부터 시작했습니다. `ecpp_witnesses.json`의 `runs` 목록에 세 구간이
모두 기록되어 있습니다.

**재현** (이 디렉터리에서):

```bash
# CI에서 실행 가능: 행, 이전 결과와의 일치, 표본 인증서 세 개 (표준 라이브러리만 사용)
python3 verify_witnesses.py

# 로컬 전용 (PARI/GP 2.19 이상): 모든 인증서를 다시 만들고 PARI로 검사
python3 ecpp_certify.py --from 85 --to 478 --jobs 4 --expect ecpp_witnesses.json

# 로컬 전용 (gmpy2): 다시 만든 모든 인증서를 독립적으로 재검사
python3 verify_witnesses.py --cert-dir build/certificates --backend gmpy2 --jobs 4
```

`ecpp_certify.py`는 `build/`(git 무시 대상)에 쓰고, 출력 파일에 이미 행이
있으면 이어서 실행하며, `--budget-minutes`를 주면 다음 `n`이 시간 안에 끝나지
않을 것 같을 때 새 `n`을 시작하지 않습니다.

**주장하지 않는 것.** `n > 478`에 대한 어떤 것도, `n > 84`에서 `a(n)`의
정확한 값도 주장하지 않으며 무한 추측은 여전히 미해결입니다. 이번 실행에서
확률적 소수 후보가 없는 `n`은 발견되지 않았습니다. OEIS 항목 밖에서 이 수열을
계산한 결과가 있는지는 찾아보지 않았으므로 이 범위에 대해 새로움을 주장하지
않습니다.

## 작은 구조적 보조정리

모든 후보는 `p_n` 이하의 소인수를 갖지 않습니다. 실제로 소수 `ell <= p_n`을
잡습니다. `ell`이 squarefree `d`를 나누지 않으면 `ell`은 `P_n/d`를 나누지만
`d`는 나누지 않습니다. `ell`이 `d`를 나누면 squarefree 조건 때문에 `ell`은
`P_n/d`를 나누지 않고 `d`는 나눕니다. 어느 경우든 `P_n/d + d`는 `ell`을
법으로 0이 아닙니다.

이 보조정리만으로 추측을 증명할 수는 없지만, 작은 소수에 의한 시행 나눗셈으로
이 후보들을 판정할 수 없는 이유를 설명합니다.

## 원래 실행: 재현

원래 실행은 공개된 84개 항을 재현하고, `85 <= n <= 200`을 PARI/GP
`isprime`으로 증명했으며, `201 <= n <= 400`을 BPSW로 선별했습니다. 그 출력은
[`result.json`](result.json)입니다.

[PARI 문서](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#isprime)는
`isprime`을 엄밀한 소수성 판정 절차로 설명합니다. 빠른 합성수 선별 뒤에
APRCL/ECPP를 사용합니다. 결과 파일은 `n`, `p_n`, `d`, 비트 길이, 십진 후보의
SHA-256 해시를 저장합니다. 후보 자체는 `P_n // d + d`로 정확히 다시 만듭니다.

요구 사항: Python 3, `gmpy2`, PARI/GP 2.15 이상.

```bash
cd /home/user/projects/agentic-conjectures/problems/oeis-a395412
python3 search_and_certify.py \
  --gp /path/to/gp \
  --prove-through 200 \
  --screen-through 400 \
  --output result.json
```

Ubuntu에서는 `pari-gp` 패키지가 `gp`를 제공합니다. `--prove-through`를 늘려도
되지만, 엄밀한 소수성 증명이 실행 시간을 지배하므로 상당히 느려집니다.

## 해석

앞으로의 실행이 0인 후보를 보고하더라도, 추측을 결정적으로 반박하려면 허용되는
모든 `d`에 대한 합성수 인증서(예: 진약수)가 추가로 필요합니다. 지금까지의 어떤
실행도 그런 후보를 찾지 못했습니다. 따라서 올바른 결론은 완전한 해결이 아니라
인증된 유한 범위 확장입니다.
