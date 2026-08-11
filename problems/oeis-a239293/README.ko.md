[English](README.md) | **한국어**

# OEIS A239293

[OEIS A239293](https://oeis.org/A239293)은

\[
n^c \equiv n \pmod c
\]

를 만족하는 \(n\) 보다 큰 합성수 \(c\) 중 가장 작은 값을
\(a(n)\)으로 정의합니다. 항목에는 다음 추측이 적혀 있습니다.

> Conjecture: a(n) = n+1 if and only if n+1 is an odd composite number.

## 결과

공식 수열 인덱스인 모든 \(n\ge1\)에서 추측이 성립합니다.

\(m=n+1\)이라 놓으면 \(m\)을 법으로 \(n\equiv-1\)입니다. \(m\)이 홀수
합성수이면

\[
n^m\equiv(-1)^m=-1\equiv n\pmod m
\]

이므로 \(m\)은 조건을 만족합니다. 또한 \(n\)과 \(n+1\) 사이에 자연수가
없으므로 \(m\)은 자동으로 최솟값입니다.

거꾸로 \(a(n)=m\)이라고 하자. 이때 \(m\)은 합성수이고 합동식을 만족합니다.
\(m\)이 짝수라면 같은 잉여 계산에서 \(n^m\equiv1\pmod m\)인 반면,
정의에서는 \(n^m\equiv-1\pmod m\)입니다. 따라서 \(m\mid2\)이어야 하는데,
\(1\) 보다 큰 합성수에게는 불가능합니다. 그러므로 \(m\)은 홀수입니다.

## Lean 형식 증명

[`AgenticConjectures/OeisA239293.lean`](../../AgenticConjectures/OeisA239293.lean)은
수열의 최소 후보 정의를 형식화하고 `sorry`, 추가 공리, `native_decide` 없이
다음을 증명합니다.

```text
a_eq_succ_iff_odd_composite :
  ∀ n ≥ 1, a n = n + 1 ↔ Odd (n + 1) ∧ 1 < n + 1 ∧ ¬(n + 1).Prime
```

정의는 조건을 만족하는 자연수의 하한을 사용합니다. 이 하한은 공집합에 대한
기본값이 아니라 실제로 도달되는 최솟값입니다. 보조 정리
`weakPseudoprimeAbove_nonempty`는 mathlib의
`Nat.exists_infinite_pseudoprimes`를 사용해 모든 양의 밑 \(n\)에 대해 임의로
큰 페르마 의사소수가 있음을 보입니다. 이 의사소수는 A239293의 더 약한
합동식도 만족합니다.

## 명제 충실성

- Lean 정리는 OEIS 오프셋과 정확히 같게 \(n=1\)에서 시작합니다.
- “합성수”는 \(1<c\)와 `¬c.Prime`으로 표현합니다.
- \(n^c\equiv n\pmod c\)는 통상적인 합동식과 동치인 `ZMod c`에서의 등식으로
  표현합니다.
- `a n`은 정확히 합동식을 만족하는 \(n\) 보다 큰 합성수 \(c\) 중
  최솟값이며, 모든 \(n\ge1\)에서 후보 집합이 공집합이 아님을 증명합니다.
- 이 항목에는 upstream Lean 스냅샷이 없습니다. 따라서 위 OEIS 원문과 모듈
  docstring에 표준 명제를 보존했습니다.

## 검증과 연구 상태

2026-08-12 기준 실시간 OEIS 항목(개정 27, 오프셋 1)은 이 동치를 여전히
“Conjecture”로 표시하고 Thomas Ordowski(2018)에게 귀속합니다. 같은 항목은
`n`이 짝수이고 `n+1`이 합성수이면 `a(n)=n+1`이라는 충분조건을 이미
기록합니다. OEIS가 연결한
[Numericana 약한 의사소수 페이지](https://numericana.com/answer/pseudo.htm#weak)도
모든 홀수 합성수 `m`이 밑 `m-1`에 대한 약한 의사소수라고 적고 있습니다.
따라서 이 저장소는 그 방향을 발견했다고 주장하지 않습니다.

정확한 문구, A-번호, 공개 GitHub 코드를 검색했지만 전체 동치의 독립된 증명은
찾지 못했습니다. 관련 공개 코드 결과는
[PARI 항 생성기](https://github.com/gfis/OEIS-prog/blob/fb375daf77829667fb7d46a43f3856dbfc5e8702/prog/gp/a239/A239293.gp)였으며
증명은 아니었습니다. 이런 부정적 검색 결과는 신규성을 확정하지 않습니다. Lean
증명은 미검토 상태이고 OEIS 편집자의 확인을 받지 않았으며 외부에 제출하지
않았습니다.

저장소 루트에서 다음 명령으로 증명과 저장소 전체 게이트를 재현할 수 있습니다.

```bash
lake env lean AgenticConjectures/OeisA239293.lean
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
python3 scripts/verify_all.py --ci
python3 scripts/gen_readme.py --check
```

개발 머신에서 모듈 직접 elaboration은 16.88초가 걸렸습니다. 웜 캐시 상태에서
기록한 저장소 전체 6개 게이트는 총 약 277초가 걸렸습니다. import 도달성
0.24초, no-sorry 검사 0.24초, `lake build` 26.45초, 공리 감사 38.45초, 기존 CI 가능
인증서 35개 검사 211.36초, 대시보드 신선도 검사 0.19초입니다. 인증서 검사에는
upstream 커밋 `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`의 `drat-trim`을 `/tmp`에서
빌드해 사용했으며, 해당 바이너리는 저장소에 커밋하지 않았습니다.
