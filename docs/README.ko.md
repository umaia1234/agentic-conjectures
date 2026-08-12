[English](README.md) | **한국어**

# 문서

저장소 진입점은 루트에 두고, 연구 자료는 그 내용을 설명하는 코드·인증서 옆에
둡니다. 이 색인은 저장소 전역 참고 문서와 문제별 수학 상세 문서를
연결합니다.

## 문서 위치

- [`README.ko.md`](../README.ko.md), [`AGENTS.ko.md`](../AGENTS.ko.md),
  [`CONTRIBUTING.ko.md`](../CONTRIBUTING.ko.md)는 GitHub와 에이전트가 쉽게
  찾을 수 있도록 루트에 유지합니다.
- `problems/<id>/`는 하나의 문제에 대한 상태, 설명, 증명, 검증 노트,
  출처 스냅샷, 코드, 인증서를 함께 보관하는 단위입니다.
- [업스트림 출처 스냅샷](upstream/README.ko.md)은 공통 보존·복원·라이선스
  정책을 설명합니다. 계속 바뀌는 저장소 표는
  [`sources.yaml`](upstream/sources.yaml)에서 생성합니다.
- [주간 하이라이트 아카이브](HIGHLIGHTS.ko.md)는 첫 화면 순환 큐레이션의
  지난 주 기록을 보관하며, [`highlights.yaml`](highlights.yaml)에서
  생성합니다.

## 문제별 수학 상세

아래 목록은 각 문제 `status.yaml`에서 `mathematical-details`로 표시한
산출물을 기준으로 생성합니다. 다시 전역 문서에 복사하지 말고 해당
문제 옆의 연결된 문서를 수정하세요.

<!-- DETAILS:BEGIN (scripts/gen_readme.py) -->
| 문제 | 주장 상태 | 수학 상세 |
|---|---|---|
| [에르되시 #671 — 모든 점에서 비유계인 라그랑주 배열 증명](../problems/erdos-671/README.ko.md) | ✅ 증명 | [상세 전개](../problems/erdos-671/DETAILS.ko.md) |
| [OEIS A000224 — R(n)(R(n)-1)이 n^2-1을 나눌 필요충분조건은 n이 홀수 소수인 것이다](../problems/oeis-a000224/README.ko.md) | 🟡 부분 결과 | [상세 전개](../problems/oeis-a000224/DETAILS.ko.md) |
| [OEIS A076141 — n의 이진 표현은 n^2의 이진 표현에서 최대 한 번 등장, 2^40까지 확인](../problems/oeis-a076141/README.md) | 🟡 부분 결과 | [상세 전개](../problems/oeis-a076141/DETAILS.ko.md) |
| [OEIS A245211: a(n)=n인 것은 n=21뿐](../problems/oeis-a245211/README.ko.md) | 🟡 부분 결과 | [상세 전개](../problems/oeis-a245211/DETAILS.ko.md) |
| [OEIS A354747 최초 미해결 항 a(100943)](../problems/oeis-a354747/README.md) | 🔴 반례 | [상세 전개](../problems/oeis-a354747/DETAILS.ko.md) |
| [OEIS A395412 — 비영성이 인증된 유한 범위 확장](../problems/oeis-a395412/README.md) | 🟡 부분 결과 | [상세 전개](../problems/oeis-a395412/DETAILS.ko.md) |
<!-- DETAILS:END -->
