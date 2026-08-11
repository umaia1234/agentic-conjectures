# OEIS A297707

이전 소수와의 gap을 탐색하는 실험 코드입니다. `gmpy2`와 `sympy`가
필요하며, 출력된 endpoint는 Baillie–PSW probable prime이므로 최종
증명으로 사용하려면 별도의 소수성 인증이 필요합니다.

```bash
python3 problems/oeis-a297707/oeis_a297707_search.py N
```

## 상류 Lean 형식화

FormalConjectures의 [원문 스냅샷과 출처 기록](upstream/README.md)을
[`297707_fd3973db.lean`](upstream/297707_fd3973db.lean)에 보존했다. 반례
인덱스가 `250`보다 크다는 정리는 `by sorry`인 **추측 statement**이지 형식
증명이 아니다. 이 폴더의 탐색 역시 probable-prime 실험이며 그 명제를 인증하지 않는다.
