[English](README.md) | **한국어**

# Formal Conjectures 상류 스냅샷

이 디렉터리는 상위 디렉터리의 A072780 반례와 상류 형식 추측을 연결하는
정확한 Lean 소스를 보존한다.

## 출처

- 저장소: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS 원문: [A072780](https://oeis.org/A072780)
- 정확한 commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- 원래 경로: `FormalConjectures/OEIS/Auto/72780_30fabef9.lean`
- 변경 불가능한 상류 파일: [72780_30fabef9.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/72780_30fabef9.lean)
- 로컬 스냅샷: [72780_30fabef9.lean](72780_30fabef9.lean)
- SHA-256: `9c984bee8555b50e7226f77c2ff422f33c2c220c06461073f1bbae31c6a62839`
- 핵심 선언: `a`; `oeis_72780_conjecture`;
  `oeis_72780_twin_prime_conjecture`; `oeis_72780_goldbach_conjecture`

## 이 문제와의 관계

상위 디렉터리는 `(m,r)=(8,7)`에서
`oeis_72780_goldbach_conjecture`를 반박한다. 스냅샷의 다른 두 추측
정리에 대해서는 어떤 반박도 주장하지 않는다.

추측 선언들은 `by sorry`로 끝난다. 이는 기계가 읽을 수 있는 명제이지
형식 증명이 아니다. 복사한 파일은 원래 저작권과 라이선스 헤더를
그대로 유지한다.

## 빌드 상태

이 소스는 상류 프로젝트의 `FormalConjectures.Util.ProblemImports`를
import하며 독립 실행용이 아닌 스냅샷으로 보존된다. 원래 환경을
재현하려면 같은 Formal Conjectures 프로젝트와 Lean/mathlib 의존성이
필요하다.

## 라이선스

Lean 소스는 상류 Apache-2.0 고지를 유지한다. 로컬
[Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt)을
참조하라. OEIS에서 유래한 수학 내용은 위 OEIS 원문 링크로 출처를
표시한다.
