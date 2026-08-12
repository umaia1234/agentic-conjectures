[English](README.md) | **한국어**

# Formal Conjectures 상류 스냅샷

이 디렉터리는 상위 디렉터리의 A112970 결과를 진행 중인 상류 형식화와 비교하는
데 사용한 정확한 Lean 원문을 보존한다.

## 출처

- 저장소: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Pull request: [#4450](https://github.com/google-deepmind/formal-conjectures/pull/4450)
- OEIS 원문: [A112970](https://oeis.org/A112970)
- 정확한 커밋: [`93dc5e41789aadbd85380183779a94e7a59cb80e`](https://github.com/google-deepmind/formal-conjectures/tree/93dc5e41789aadbd85380183779a94e7a59cb80e)
- 원래 경로: `FormalConjectures/OEIS/112970.lean`
- 변경 불가능한 상류 파일: [112970.lean](https://github.com/google-deepmind/formal-conjectures/blob/93dc5e41789aadbd85380183779a94e7a59cb80e/FormalConjectures/OEIS/112970.lean)
- 로컬 스냅샷: [112970_93dc5e41.lean](112970_93dc5e41.lean)
- SHA-256: `acd3d5c737707b44128d5cae814253e0feea8a9cd62889e31fa3191702394185`
- 중심 선언: `OeisA112970.a`; `conjecture1`; `conjecture2`; `conjecture3`

## 이 문제와의 관계

스냅샷은 로컬 모듈과 같은 guard가 있는 자연수 점화식을 정의한다. 세 연구
선언은 $a(2^n)=a(2^{n+1}+1)$과
$a(2^n-1)=a(3\cdot2^n-1)=1$의 두 부분을 형식화하며 고정한 커밋에서 모두
`sorry`로 끝난다. canonical OEIS 조항 $a(2^n)=A033638(n)$은 설명에만 쓰고
형식 명제로 만들지 않았다. 상위 모듈은 세 선언을 모두 증명하고 누락된
사분제곱 정리를 추가한다.

복사한 파일은 원래 저작권 및 Apache-2.0 라이선스 헤더를 유지한다.

## 빌드 상태

원문은 `FormalConjecturesUtil`을 import하고 상류 benchmark attribute를
사용하므로 독립 빌드용이 아닌 출처 스냅샷으로 보존한다. 로컬 정리 모듈을
빌드하거나 고정한 커밋에서 상류 저장소를 복원해야 이 파일을 원래 환경에서
컴파일할 수 있다.

## 라이선스

Lean 원문은 상류 Apache-2.0 고지를 유지한다. 로컬
[Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt)도 참조한다.
OEIS 유래 수학 내용은 canonical 원문 링크로 출처를 남긴다.
