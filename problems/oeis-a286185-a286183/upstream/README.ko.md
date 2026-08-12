[English](README.md) | **한국어**

# 원문 스냅샷

이 디렉터리에서 다루는 세 수열의 OEIS 항목 원문을 그대로 보존했습니다.
2026-08-12에 다음 명령으로 가져왔습니다.

```bash
curl -s "https://oeis.org/search?q=id:A286185&fmt=text" -o A286185.txt
curl -s "https://oeis.org/search?q=id:A286183&fmt=text" -o A286183.txt
curl -s "https://oeis.org/search?q=id:A286182&fmt=text" -o A286182.txt
```

| 파일 | 수열 | 가져올 당시 OEIS 버전 |
|---|---|---|
| `A286182.txt` | 각기둥 그래프, `2n`개 꼭짓점 | #27, 2025-02-16 |
| `A286183.txt` | 엇각기둥 그래프, `2n`개 꼭짓점 | #21, 2025-02-16 |
| `A286185.txt` | 뫼비우스 사다리 그래프, `2n`개 꼭짓점 | #26, 2025-02-16 |

이 파일들은 이 디렉터리의 결과를 대조한 canonical 원문입니다. `%N` 이름
행은 무엇을 세는지 정하고, `%F` 공식 행은
[../PROOF.md](../PROOF.md)가 A286185와 A286183에 대해 해결하는
`(conjectured)` 표시를 담고 있습니다. `%t` Mathematica 행은
[../certificate.py](../certificate.py)가 다시 구현하여 자체 구성과
교차 검증하는 그래프 구성법입니다.

상류 Lean 스냅샷은 **없습니다**. 세 항목 모두
`google-deepmind/formal-conjectures`에 들어 있지 않으므로,
`AgenticConjectures/OeisA286185A286183.lean`의 Lean 명제는 기존
형식화를 옮긴 것이 아니라 위 OEIS 원문을 직접 기준으로 작성했습니다.

OEIS 콘텐츠는 The OEIS Foundation Inc.의 CC BY-NC-SA 4.0 라이선스를
따릅니다. 출처 보존을 위해 이 파일들을 수정하지 않은 채 포함했습니다.
