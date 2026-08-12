[English](README.md) | **한국어**

# 공개된 에르되시 #671 해답 출처

이 디렉터리는 에르되시 문제 #671의 완전한 Lean 증명을 재현하는 데 사용한
공개 원문을 그대로 기록합니다.

## 출처

- 원 문제: [에르되시 문제 #671](https://www.erdosproblems.com/671)
- 공개 해답 게시물: 2026-06-22에 게시된 [토론 글](https://www.erdosproblems.com/forum/thread/671#post-7142)
- 공개 증명 원고: [Overleaf 읽기 링크](https://www.overleaf.com/read/gqmfrhsprtqm#59ac11)
- 공개 Lean 원문: 게시물에서 직접 연결한 Lean 웹 편집기 payload
- 취득일: 2026-08-12
- 로컬 원문 payload: [Erdos671.public.lean](Erdos671.public.lean)
- 기계 검증 가능한 manifest: [SHA256SUMS](SHA256SUMS)
- SHA-256: `3854ae85aca322b5ad2c65fb9c7bae5ca19ed939ceca99521365d8690b8d8923`
- 중심 선언: `Erdos671.erdos_671`

토론 글은 논증을 “GPT Pro”, Lean 형식화를 “Codex”의 작업으로
표기합니다. 정확한 모델명과 harness 이름은 제시하지 않았으므로, 이 저장소는
추측하지 않고 해당 필드를 `unspecified`로 기록합니다.

## 재취득 방법

게시물의 Lean 링크는 LZ-String의 Base64 codec을 사용하여 소스 코드를
`#codez=` fragment에 저장합니다. 이 fragment를 추출하고 URL decoding한 뒤
`decompressFromBase64`를 적용하면 원문을 복원할 수 있습니다. 로컬 snapshot은
복호화한 payload를 UTF-8로 encoding한 결과와 byte 단위로 동일합니다.

문제 디렉터리에서 `(cd upstream && sha256sum -c SHA256SUMS)`를 실행하면 이
snapshot을 검증할 수 있습니다.

## 검증되는 모듈과의 관계

검증되는 모듈
[`AgenticConjectures/Erdos671.lean`](../../../AgenticConjectures/Erdos671.lean)은
증명 본문을 보존합니다. 저장소 출처 설명을 추가하고 namespace를
`AgenticConjectures.Erdos671`로 바꾸며, 최종 명제를 `statement`와
`erdos_671 : statement`로 분리했습니다. 이러한 통합 변경은 수학적 구성이나
증명을 바꾸지 않습니다.

## 라이선스와 사용 범위

공개 웹 편집기 payload에는 저작권 또는 라이선스 header가 없었습니다. 이
저장소는 연구 검증과 출처 표시를 위해 원문을 보존합니다. 복사된 증명의 저작성이나
새로움을 주장하지 않으며 어떠한 외부 창구에도 제출하지 않습니다.
