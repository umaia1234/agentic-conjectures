[English](README.md) | **한국어**

# Formal Conjectures 상류 스냅샷

이 디렉터리는 상위 디렉터리의 A108864 반박과 상류 형식 추측을 연결하는
정확한 Lean 소스를 보존한다.

## 출처

- 저장소: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS 원문: [A108864](https://oeis.org/A108864) (perfect deficiency:
  [A109883](https://oeis.org/A109883))
- 정확한 commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- 원래 경로: `FormalConjectures/OEIS/108864.lean`
- 변경 불가능한 상류 파일: [108864.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/108864.lean)
- 로컬 스냅샷: [108864.lean](108864.lean)
- SHA-256: `ef28b630f7c6c2370106c8286daee4ad374efbdcfcb04558368ac7150e68ce10`
- 핵심 선언: `OeisA108864.perfectDeficiency`; `OeisA108864.A`;
  `OeisA108864.a`; `OeisA108864.conjecture`

## 이 문제와의 관계

스냅샷은 OEIS의 질문 "Is 1155 the last odd number in this sequence?"를
`conjecture : ∀ n > 58, Even (a n)`으로 형식화한다. 여기서
`a n = Nat.nth A n`은 0부터 색인하며 `a 58 = 1155`이다. 상위 디렉터리는
바로 이 명제의 부정을 증명한다. 홀수
`815634435 = 3 * 5 * 7 * 11 * 547 * 1291`은 perfect deficiency가 6인 항이고,
그 색인은 58보다 크다. 로컬 모듈 `AgenticConjectures/OeisA108864.lean`은
`perfectDeficiency`, `A`, 그 `DecidablePred` 인스턴스, `a`를 항 단위로
그대로 옮겨 온다.

연구용 선언 `conjecture`는 고정된 commit에서 여전히 `sorry`로 끝난다.
이는 질문을 기계가 읽을 수 있게 적은 명제일 뿐 형식 증명이 아니다.
다섯 개의 `test` 정리 `a_0`–`a_4`는 상류에서 `decide`로 증명되어 있다.
복사한 파일은 원래 저작권과 라이선스 헤더를 그대로 유지한다.

## 빌드 상태

이 소스는 `module`로 시작하고 `FormalConjecturesUtil`을 import하며 상류의
`category`, `AMS` 속성을 사용하므로, 독립적으로 빌드되지 않는 출처
기록용 스냅샷으로 보존된다. 대신 로컬 정리 모듈을 빌드하거나, 이 파일을
원래 환경에서 컴파일하려면 고정된 commit의 상류 저장소를 복원하라.

## 라이선스

Lean 소스는 상류 Apache-2.0 고지를 유지한다. 로컬
[Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt)을
참조하라. OEIS에서 유래한 수학 내용은 위 OEIS 원문 링크로 출처를
표시한다.
