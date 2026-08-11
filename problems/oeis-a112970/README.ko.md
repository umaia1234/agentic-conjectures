[English](README.md) | **한국어**

# OEIS A112970 — 2의 거듭제곱 첨자 항등식

## 결론

모든 자연수 $n$에 대해 두 추측 사슬을 모두 **증명했다**.

\[
a(2^n)=a(2^{n+1}+1)=\left\lfloor\frac{n^2}{4}\right\rfloor+1
\]

및

\[
a(2^n-1)=a(3\cdot2^n-1)=1.
\]

첫 번째 닫힌식은 OEIS A033638이다. 결과를 Lean 4로 형식화했으며
`sorry`, 추가 공리, `native_decide` 없이 검사한다.

## 원문 명제와 선행 결과

2026-08-12에 확인한 [OEIS A112970](https://oeis.org/A112970)은
$a(0)=a(1)=1$로 두고 음수 첨자에서 $a(m)=0$이라 하며 다음 점화식을
제시한다.

\[
a(2m+1)=a(m),\qquad a(2m)=a(m)+a(m-2).
\]

offset 0에서 위 두 사슬을 추측으로 기록한다. 참조된
[A033638](https://oeis.org/A033638)은 사분제곱 수열
$\lfloor n^2/4\rfloor+1$이다.

점화식 자체에는 출판된 선행 결과가 있다. Northshield의
[“Sums across Pascal's triangle modulo
2”](https://soar.suny.edu/bitstreams/d770f1ab-549e-49a1-8442-f2f266ff36ed/download)
(Congressus Numerantium 200 (2010), 35–52쪽; preprint 14쪽의 정리 4.1)을
$(a,b)=(4,1)$에 특수화하면 정확히 위 홀수·짝수 점화식을 얻는다. 논문은
A112970, A033638, 사분제곱 닫힌식, 특수 첨자 사슬 어느 것도 명시하지 않는다.
홀수 점화식만 쓰는 세 명제는 즉각적인 따름정리지만 사분제곱 조항에는 아래의
추가 논증이 필요하다.

2026-08-12에 정확한 OEIS 번호, 표시된 전체 등식, 사분제곱 식, GitHub
이력과 코드, 공개 AlphaProof Nexus 결과 트리를 검색했지만 닫힌식의 기존
증명을 찾지 못했다. 보존한 커밋에서 [Formal Conjectures PR
#4450](https://github.com/google-deepmind/formal-conjectures/pull/4450)은 아직
열려 있으며, `sorry`로 끝나는 세 명제는 A033638 조항을 아예 생략한다. 이는
문헌 조사가 아닌 음성 검색 결과일 뿐이며 독창성을 주장하지 않는다. 이 증명은
심사를 받지 않았고 외부에 제출하지 않았다.

## 증명

홀수 점화식에서 즉시

\[
a(2^{n+1}+1)=a(2^n)
\]

을 얻는다. 또한 $2^{n+1}-1$은 $2^n-1$로,
$3\cdot2^{n+1}-1$은 $3\cdot2^n-1$로 줄어든다. 각각의 기저 첨자는 0과
2이고 두 값 모두 1이므로 귀납법으로 두 번째 사슬이 성립한다.

빠진 닫힌식을 위해

\[
r_n=a(2^{n+1}-2)
\]

라 두자. $2^{n+3}-2=2(2^{n+2}-1)$로 쓰고 이 첨자에서 짝수 점화식을
적용한 뒤 두 번째 합에 홀수 점화식을 적용하면

\[
r_{n+2}=r_n+1
\]

을 얻는다. 기저 $r_0=r_1=1$에서

\[
r_n=\left\lfloor\frac{n+2}{2}\right\rfloor
\]

이다. 이제 $b_n=a(2^n)$라 두면 $n\ge1$에서 짝수 점화식으로

\[
b_{n+1}=b_n+a(2^n-2)
       =b_n+\left\lfloor\frac{n+1}{2}\right\rfloor
\]

을 얻는다. $b_0=1$에서 시작해

\[
\left\lfloor\frac{(n+1)^2}{4}\right\rfloor
=\left\lfloor\frac{n^2}{4}\right\rfloor
 +\left\lfloor\frac{n+1}{2}\right\rfloor
\]

을 사용하면 $b_n=\lfloor n^2/4\rfloor+1$이다. Lean에서는 $n$을 짝수와
홀수로 나누어 마지막 바닥함수 항등식을 증명한다.

## 명제 충실성

[`AgenticConjectures/OeisA112970.lean`](../../AgenticConjectures/OeisA112970.lean)은
namespace, 주석, benchmark attribute를 제외하면 고정한 Formal Conjectures
원문의 재귀 정의를 그대로 사용한다. 자연수 모델의 guard는 짝수 점화식이
$k<2$에서 $a(k-2)$를 요구할 때 0을 반환한다. 이는 음수 $m$에서
$a(m)=0$이라는 OEIS 관례를 정확히 구현하며 $a(-1)$ 경계에서 실제로 쓰인다.

모든 정리의 매개변수는 $n\ge0$이며 OEIS offset과 일치한다. 자연수의 4로
나눈 몫은 바닥 나눗셈이므로 `power_of_two_eq_a033638`은 정확히
$a(2^n)=\lfloor n^2/4\rfloor+1$을 말한다. 고정한 원문 파일은 나머지 세
등식만 형식화한다. A033638 정리는 canonical OEIS 항목을 따라 그 누락을
의도적으로 채운다.

## 기계 검증과 재현

등록한 Lean 정리들이 보편 명제를 증명한다. 표준 라이브러리만 쓰는 Python
스크립트는 음수 입력까지 포함한 정수 첨자 점화식을 독립적으로 계산하고
$0\le n\le64$에서 두 사슬을 검사한다. 이 유한 검사는 전사 오류 방지용이며
증명을 대신하지 않는다.

저장소 루트에서 다음을 실행한다.

```bash
lake build AgenticConjectures.OeisA112970
python3 problems/oeis-a112970/verify_identities.py --max-exponent 64
```

2026-08-12 개발 실행에서 Python 검사는 메모한 점화식 상태 377개를 0.09초에
검사했다. 저장소 CI도 모듈을 빌드하고 공리를 감사하며 유한 검사를 다시
실행한다.
