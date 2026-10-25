[English](DETAILS.md) | **한국어**

# 세타 산술합: 항등식, 상계, 그리고 계산

이 문서 전체에서 $k$는 홀수 소수이고 $n=(k-1)/2$입니다. 다루는 대상은 다음과 같습니다.

\[
S'(h,k)=\sum_{j=1}^{k-1}(-1)^{j+1+\lfloor hj/k\rfloor},\qquad
S(k)=\sum_{h=1}^{k-1}S'(h,k).
\]

논문은 $S'(h,k)$를 $S(h,k)$로 쓰고, 업스트림 Lean 파일은 기호가 겹치지 않도록 `S'`를
씁니다. 2–6절은 정확한 항등식이고, 7절은 무조건적 상계이며, 8절은 미해결 추측에 정확히
무엇이 필요한지 설명하고, 9절은 계산을 설명합니다.

## 1. 기호와 진술

$x\notin\mathbb Z$이면 $((x))=x-\lfloor x\rfloor-\tfrac12$, $x\in\mathbb Z$이면
$((x))=0$으로 둡니다. $c\ge1$이고 $\gcd(h,c)=1$일 때

\[
s(h,c)=\sum_{i=1}^{c-1}\Bigl(\Bigl(\frac ic\Bigr)\Bigr)\Bigl(\Bigl(\frac{hi}c\Bigr)\Bigr),\qquad
s_3(h,c)=\sum_{i=1}^{c-1}(-1)^i\Bigl(\Bigl(\frac{hi}c\Bigr)\Bigr),\qquad
s_4(v,k)=\sum_{j=1}^{k-1}(-1)^{\lfloor vj/k\rfloor}
\]

로 둡니다. $s(h,c)$는 고전적인 Dedekind 합이며, $s$와 $s_3$은 $h\bmod c$에만 의존합니다.
논문의 $S(h,k)$(여기서는 $S'$), $s_3$, $s_4$는 Berndt [Be78]의 여섯 *Hardy 합* 가운데
셋이며, Goldberg [Go81], Berndt와 Goldberg [BG84], Sitaramachandrarao [Si87]도 이 합들을
연구했습니다. Zhang [Zh03], Dağlı [Da20] 등은 이 합들의 거듭제곱 평균값과 혼합
평균값을 연구합니다. 마지막으로

\[
H(k)=\sum_{\substack{1\le v\le k-2\\ v\text{ odd}}}\frac1v,\qquad
V(k)=\sum_{\substack{3\le v\le k-2\\ v\text{ odd}}}s_3(k\bmod v,\;v)
\]

로 둡니다. $k-1$이 짝수이므로 $H(k)$는 논문의 $H(k)=\sum_{j\le k-1,\ j\text{ odd}}1/j$와
같습니다.

업스트림 파일은 홀수 소수 $k$에 대해 다음을 진술합니다(arXiv v1의 번호).

- 추측 1.1: $S(k)>0$;
- 추측 4.1: $k>5$이면 $S(k)>k$;
- 추측 4.2: $k>233$이면 $S(k)>2k$;
- 추측 4.3: $k>3119$이면 $S(k)>3k$;
- 추측 4.4: 모든 $n\in\mathbb N$에 대해, 충분히 큰 모든 $k$에서 $S(k)>nk$.

추측 3.3은 arXiv v2(2025년 12월 2일)에 처음 나오며, v3(2026년 1월 9일) 4쪽의 문장도
같습니다. v1을 따르는 업스트림 파일에는 없습니다.

> “Let $C_1$ and $C_2$ be any fixed positive numbers. Let $\epsilon>0$ be fixed. Then, for all
> primes $k$ sufficiently large, $C_1k<S(k)<C_2k^{1+\epsilon}$.”

즉 $C_1$, $C_2$는 임의의 양수이고 $\epsilon>0$을 고정하면, 충분히 큰 모든 소수 $k$에서
$C_1k<S(k)<C_2k^{1+\epsilon}$라는 주장입니다. 상수가 임의이므로 이 추측은 각자 문턱을 갖는
두 진술과 동치입니다.

- *첫 번째 부등식:* 모든 $C_1>0$에 대해, 충분히 큰 모든 소수 $k$에서 $S(k)>C_1k$;
- *두 번째 부등식:* 모든 $C_2>0$과 $\varepsilon>0$에 대해, 충분히 큰 모든 소수 $k$에서
  $S(k)<C_2k^{1+\varepsilon}$.

첫 번째는 추측 4.4와 동치입니다. 한 방향은 $C_1=n+1$, 다른 방향은 $n=\lceil C_1\rceil$로
두면 됩니다. 두 번째는 7절에서 증명합니다. Lean은 추측과 두 부등식을 진술하고
(`statement_3_3`, `statement_3_3_lower`, `statement_3_3_upper`) 두 동치를 증명하지만
(`statement_3_3_iff`, `statement_3_3_lower_iff`), 어느 부등식도 증명하지 않습니다.

## 2. 반사: Lean으로 검증한 환원식

**보조정리 2.1.** $0<j<k$이고 $k\nmid hj$이면
$\lfloor hj/k\rfloor+\lfloor h(k-j)/k\rfloor=h-1$입니다.

*증명.* 두 몫 $hj/k$와 $h(k-j)/k$의 합은 정수 $h$이고, 둘 다 정수가 아닙니다. $\square$

소수 $k$와 $1\le h,j\le k-1$에서는 항상 $k\nmid hj$입니다. $j$를 $k-j$와 짝지으면, $k$가
홀수이므로 둘은 서로 다릅니다.

1. **홀수 $h$에 대해 $S'(h,k)=0$.** 짝지은 두 항의 지수의 합은
   $(j+1)+(k-j+1)+(h-1)=k+h+1$로 홀수이므로 두 항이 상쇄됩니다. 이는 논문의 보조정리
   5.7(v1), 명제 7.5(v3)의 소수 경우이며, 홀수 $k$와 $\gcd(h,k)=1$에 대해서는
   [Zh03, Lemma 5]에도 포함되어 있습니다. Lean: `S'_eq_zero_of_odd`.
2. **$0<v<k$에 대해 $S'(k-v,k)=s_4(v,k)$.** 여기서
   $\lfloor (k-v)j/k\rfloor=j-1-\lfloor vj/k\rfloor$이므로 지수
   $2j-\lfloor vj/k\rfloor$의 홀짝은 $\lfloor vj/k\rfloor$의 홀짝과 같습니다. Lean:
   `S'_sub_eq_s4`.
3. **짝수 $v$에 대해 $s_4(v,k)=0$.** 짝지은 지수의 합은 홀수 $v-1$입니다. Lean:
   `s4_eq_zero_of_even`.
4. **홀수 $v$.** 짝지은 지수의 합이 짝수 $v-1$이므로
   $s_4(v,k)=2\sum_{j=1}^{n}(-1)^{\lfloor vj/k\rfloor}$입니다. Lean: `s4_eq_two_mul`.

2번 항목을 $v=k-h$에 대해 더한 뒤 3번과 4번 항목을 쓰면 다음을 얻습니다.

\[
S(k)=\sum_{v=1}^{k-1}s_4(v,k)=\sum_{a=1}^{k-1}\sum_{b=1}^{k-1}(-1)^{\lfloor ab/k\rfloor}
=\sum_{\substack{v<k\\ v\text{ odd}}}s_4(v,k)
=2\sum_{\substack{v<k\\ v\text{ odd}}}\ \sum_{j=1}^{n}(-1)^{\lfloor vj/k\rfloor}.
\tag{2.1}
\]

Lean에서는 각각 `S_eq_sum_s4`, `S_eq_sum_sq`, `S_eq_sum_odd`, `S_eq_fastS`입니다. 마지막
형태는 약 $k^2/4$번의 홀짝 판정으로 계산됩니다. 커널은 `small_primes`에서 $k<300$인 모든
홀수 소수에 대해 이를 계산합니다. Lean은 `floor_eq`도 증명합니다. 즉 업스트림의
$\mathbb Q$ 바닥 함수 $\lfloor (hj:\mathbb Q)/k\rfloor_+$가 자연수 몫 `h * j / k`와
같습니다. 이 모든 결과는 업스트림 정의 자체에 관한 것입니다.

## 3. 격자 형태와 Dedekind 합 닫힌 형태(방법 A)

**명제 3.1(격자 형태).**

\[
S(k)=-2\sum_{s=1}^{n}\sum_{t=1}^{n}(-1)^{\lfloor 4st/k\rfloor}.
\]

*증명.* $A,B\subseteq\{1,\dots,k-1\}$에 대해
$Q(A,B)=\sum_{a\in A,\,b\in B}(-1)^{\lfloor ab/k\rfloor}$로 두고, $E$와 $O$를 각각 짝수
원소와 홀수 원소의 집합이라 합시다.

- $k$가 홀수이므로 $a\mapsto k-a$는 $E$를 $O$ 위로 보냅니다.
- 보조정리 2.1에 의해 $(-1)^{\lfloor (k-a)b/k\rfloor}=(-1)^{b-1}(-1)^{\lfloor ab/k\rfloor}$입니다.
- 따라서 $Q(O,E)=-Q(E,E)$이고 $Q(O,O)=Q(E,O)$입니다.
- 대칭성에 의해 $Q(E,O)=Q(O,E)$입니다.

그러므로 (2.1)에서 $S(k)=Q(E,E)+Q(E,O)+Q(O,E)+Q(O,O)=-2Q(E,E)$를 얻습니다. 마지막으로
$E=\{2s:1\le s\le n\}$입니다. $\square$

한 주기만 확인하면 두 톱니 함수 항등식을 얻습니다. $x\notin\mathbb Z$와
$1\le t\le k-1$에 대해

\[
(-1)^{\lfloor x\rfloor}=2((x))-4((x/2)),\qquad
[\,t\le n\,]=\tfrac12+\Bigl(\Bigl(\frac{2t}k\Bigr)\Bigr)-2\Bigl(\Bigl(\frac tk\Bigr)\Bigr).
\tag{3.1}
\]

$k$와 서로소인 $c$를 잡고 두 번째 항등식에 $((ct/k))$를 곱합니다. $1\le t\le k-1$에 대해
더하고 $u\equiv 2t\pmod k$로 치환하며, $\sum_t((ct/k))=0$임에 유의합니다. $\bar2$를 $k$를
법으로 한 $2$의 역원이라 하면 다음을 얻습니다.

\[
\sum_{t=1}^{n}\Bigl(\Bigl(\frac{ct}k\Bigr)\Bigr)=s(c\bar2,k)-2s(c,k).
\tag{3.2}
\]

이제 (3.1)의 첫 번째 항등식을 $x=4mt/k$에 적용하고($1\le m,t\le n$이면 정수가 아닙니다),
$c=4m$과 $c=2m$에 대해 (3.2)를 적용하면

\[
\sum_{t=1}^{n}(-1)^{\lfloor 4mt/k\rfloor}
=2\bigl(s(2m,k)-2s(4m,k)\bigr)-4\bigl(s(m,k)-2s(2m,k)\bigr)
=10s(2m,k)-4s(m,k)-4s(4m,k).
\]

**명제 3.2(Dedekind 형태).** $m$에 대해 더하고 명제 3.1을 쓰면

\[
S(k)=\sum_{m=1}^{n}\bigl(8s(m,k)-20s(2m,k)+8s(4m,k)\bigr).
\tag{D}
\]

*선행 연구.* Sitaramachandrarao [Si87]는 Hardy 합을 Dedekind 합으로 표현했습니다. 특히
$h+k$가 홀수이면 $S'(h,k)=8s(h,2k)+8s(2h,k)-20s(h,k)$입니다. 홀수 $k$와 $h=2m$에 대해
$s(2m,2k)=s(m,k)$이므로 (D)의 각 항은 $S'(2m,k)$이고, 홀수 $h$는 기여하지 않으므로(2절)
(D)가 곧바로 나옵니다. 위의 격자 유도는 [Si87]를 쓰지 않지만, (D)는 내용상 새로운
것이 아닙니다. 이 공식은 [Da20, (3)]의 인용에서 가져왔고 [Si87] 자체는 보지 않았습니다.
`verify.py`는 $k<150$인 모든 홀수 $k$에 대해 이 공식을 검사합니다.

방법 A(`s_dedekind.cpp`)는 Dedekind 합의 고전적인 연분수 공식 [Ba77, Hi77, Kn77]으로
(D)를 계산합니다. $0<h<k$이고 $\gcd(h,k)=1$이라 합시다. $(k,h)$에 대한 유클리드
호제법의 몫을 $q_1,\dots,q_r$이라 하고, $0<h'<k$이며 $hh'\equiv1\pmod k$라 하면

\[
12k\,s(h,k)=h+h'+k\Bigl(\sum_{i=1}^{r}(-1)^{i+1}q_i-2+(-1)^r\Bigr).
\tag{BHK}
\]

*증명.* [Ba77, Hi77, Kn77]은 직접 보지 않았으므로, Dedekind 상호 법칙 [RG72]
$12hk\bigl(s(h,k)+s(k,h)\bigr)=h^2+k^2+1-3hk$에서 증명합니다. $r$에 대한 귀납법을 씁니다.
$r=1$이면 $h=h'=1$, $q_1=k$이고, (BHK)는 고전적인 값 $12k\,s(1,k)=(k-1)(k-2)$입니다.
$r\ge2$이면 다음 나머지를 $c=k-q_1h$라 하고, $0<c^*<h$이며 $cc^*\equiv1\pmod h$라 합시다.
$(h,c)$에 대한 유클리드 호제법의 몫은 $q_2,\dots,q_r$이므로 귀납 가정에 의해
$12h\,s(c,h)=c+c^*+h\bigl(\sum_{i=2}^{r}(-1)^iq_i-2-(-1)^r\bigr)$입니다. 상호 법칙에
$s(k,h)=s(c,h)$와 $k(k-c)=q_1hk$를 쓰면

\[
12k\,s(h,k)=h+\frac{1-kc^*}h+k\Bigl(\sum_{i=1}^{r}(-1)^{i+1}q_i-1+(-1)^r\Bigr)
\]

를 얻습니다. 마지막으로 $h'=k+(1-kc^*)/h$입니다. $kc^*\equiv cc^*\equiv1\pmod h$이므로
정수이고, $1\le h-c^*\le h-1$이므로 $(0,k)$ 안에 있으며, $hh'=kh+1-kc^*\equiv1\pmod k$입니다.
$\square$

Dedekind 합 하나에 확장 유클리드 호제법을 한 번 쓰므로 비용은 $O(\log k)$이고, 소수 하나에
$O(k\log k)$가 듭니다. 합계는 정확한 128비트 정수로 누적하며, 프로그램은 합계가 $12k$로
나누어떨어지는지 검사합니다. `verify.py`는 서로소인 모든 $0<h<k\le500$에 대해 (BHK)를
정의와 비교하고, $k\le400$인 모든 소수에 대해 (D)를 검사합니다.

## 4. 상호 법칙과 정확한 공식(방법 B)

**명제 4.1.** 홀수 $v\ge1$이고 $\gcd(v,k)=1$이면

\[
s_4(v,k)=\frac kv-1+2s_3(k\bmod v,\;v).
\tag{4.1}
\]

*증명.* $j\in[1,k-1]$을 $q=\lfloor vj/k\rfloor\in[0,v-1]$에 따라 묶습니다.
$0\le q\le v-1$에 대해 $F(q)=\lfloor qk/v\rfloor$, 그리고 $F(v)=k-1$로 둡니다. $0<q<v$이면
$qk/v\notin\mathbb Z$이므로 $\lfloor vj/k\rfloor=q$인 첨자 $j$는 정확히 $F(q+1)-F(q)$개입니다.
$v$가 홀수임을 써서 부분합 공식을 적용하면

\[
s_4(v,k)=\sum_{q=0}^{v-1}(-1)^q\bigl(F(q+1)-F(q)\bigr)
=2\sum_{q=1}^{v-1}(-1)^{q-1}F(q)+k-1.
\]

이제 $F(q)=qk/v-((qk/v))-\tfrac12$를 대입합니다.
$\sum_{q=1}^{v-1}(-1)^{q-1}q=-(v-1)/2$, $\sum_{q=1}^{v-1}(-1)^{q-1}=0$,
$((qk/v))=((q(k\bmod v)/v))$를 쓰면
$s_4(v,k)=-k(v-1)/v+2s_3(k\bmod v,v)+k-1$을 얻습니다. $\square$

다시 말해 홀수 $v$에 대해 $2s_3(k,v)-s_4(v,k)=1-k/v$입니다. Hardy 합에 대한 이런 종류의
상호 법칙은 Berndt [Be78]와 Goldberg [Go81]로 거슬러 올라가며, [Si87]도 참고하십시오.
위의 증명은 초등적입니다.

**보조정리 4.2.** 홀수 $c$와 $\gcd(h,c)=1$에 대해 $s_3(h,c)=2s(h,c)-4s(2h,c)$입니다.

*증명.* 사상 $i\mapsto c-i$는 홀수 $i$를 짝수 $i$로 보냅니다. 이 사상은 $(-1)^i$와
$((hi/c))$의 부호를 모두 바꾸므로 $s_3$의 홀수 부분과 짝수 부분은 같습니다. 따라서
$s_3(h,c)=2\sum_{t=1}^{(c-1)/2}((2ht/c))$이고, 법을 $c$로 둔 (3.2)가 증명을 마무리합니다.
$\square$

이는 [Da20]의 공식 (1)이며, 그 논문은 이를 [Si87]의 결과로 소개합니다.

$c=k\bmod v$, $T(c,v)=12v\,s(c,v)\in\mathbb Z$로 둡니다. 그러면 (4.1)과 보조정리 4.2에서
$12v\,s_4(v,k)=12k-12v+4T(c,v)-8T(2c\bmod v,v)$를 얻습니다. 방법 B(`s_hardy.cpp`)는
Dedekind 상호 법칙 [RG72]으로 $T$를 정확히 계산합니다.

\[
c\,T(c,v)+v\,T(v\bmod c,\;c)=c^2+v^2+1-3cv,\qquad T(1,v)=(v-1)(v-2).
\tag{4.2}
\]

이 방법도 소수 하나에 $O(k\log k)$가 듭니다. 프로그램은 오버플로 검사를 하는 64비트
정수를 쓰며, 모든 항에 대해 정확성 검사를 합니다.

**정리 4.3(정확한 공식).** 모든 홀수 소수 $k$에 대해

\[
S(k)=k\,H(k)-\frac{k-1}2+2V(k).
\tag{4.3}
\]

*증명.* (2.1)에 의해 $S(k)=\sum_{v\text{ odd},\,v\le k-2}s_4(v,k)$입니다. 여기서
$s_4(1,k)=k-1$이고, $3\le v\le k-2$에는 (4.1)이 적용됩니다. 홀수 $v$는 모두 $n$개입니다.
$\square$

$\gamma$를 오일러 상수라 하면 $H(k)=\tfrac12\ln k+\tfrac12(\ln2+\gamma)+O(1/k)$이므로

\[
\frac{S(k)}k=\frac12\ln k+c_0+\frac{2V(k)}k+O\Bigl(\frac1k\Bigr),\qquad
c_0=\frac{\ln2+\gamma-1}2=0.1351\ldots
\tag{4.4}
\]

따라서 주항 $\tfrac12 k\ln k$는 명시적이며, 모든 추측은 $V(k)$에 관한 진술이
됩니다(8절).

정리 4.3은 논문 하계(5절)의 바탕에 있는 분해를, 각 항을 (4.1)로 정확히 계산해 적은
것입니다. (4.3)이 이 형태로 진술된 것은 보지 못했지만, 모든 재료는 고전적입니다. Dedekind
합의 정수값 유사체에 대한 관련 관계식은 [BD82]와 [Me97]에 있습니다. `verify.py`는 서로소인
쌍들의 범위에서 (4.1), 보조정리 4.2, (4.2)를 정의와 비교하고, $k\le400$인 모든 소수에
대해 (4.3)을 유리수 연산으로 정확히 검사합니다.

Lean은 (4.1)과 (4.3)을 일반적으로 검증합니다. 각각 `s4_eq_reciprocity`와 `S_eq_exact`이며,
$s_3$, $H$, $V$는 `s3`, `H`, `V`로 씁니다. Lean에서 $H$와 $V$는 모든 홀수 $v<k$에 대한
합입니다. 홀수 $k$에서는 같은 범위이고, `V`에 더해지는 $v=1$ 항은 $0$입니다. Lean의 (4.1)
증명은 부분합 공식 대신 $(-1)^n=1+2\sum_{q=1}^{n}(-1)^q$로 전개하고,
$\lfloor vj/k\rfloor\ge q$인 $j\in[1,k-1]$를 셉니다. 그런 $j$는
$k-1-\lfloor qk/v\rfloor$개입니다.

## 5. 논문 하계의 정확한 오차항

논문의 하계(v3 정리 6.3, v1 정리 6.4)는 네 단계로 이루어집니다.

1. $S(k)=\tfrac{(k-1)^2}2-2\sum_{j\text{ odd}}r(j,k)$로 씁니다. 여기서
   $r(j,k)=\sum_{h=1}^{k-1}\bigl(\lfloor hj/k\rfloor-2\lfloor hj/2k\rfloor\bigr)$입니다.
2. $\varepsilon_j(k)=r(j,k)/k-(j-1)/(2j)$로 정의합니다.
3. $\varepsilon_j(k)\le(j-1)/(2k)$를 증명합니다.
4. $S(k)\ge-\tfrac{k-1}2+kH(k)-\tfrac{(k-1)(k+1)}4$로 결론짓습니다.

저자들은 이어서 “a proper upper bound for $\epsilon_j(k)$ is crucial”이라고 적습니다.
즉 $\varepsilon_j(k)$의 적절한 상계가 핵심이라는 것입니다.

**명제 5.1.** $1\le j\le k-2$인 홀수 $j$에 대해

\[
r(j,k)=\frac{k-1-s_4(j,k)}2=\frac{k(j-1)}{2j}-s_3(k\bmod j,\;j),
\qquad\text{따라서}\qquad
\varepsilon_j(k)=-\frac{s_3(k\bmod j,\;j)}k\quad\text{(정확히)}.
\]

*증명.* $\lfloor hj/k\rfloor-2\lfloor hj/2k\rfloor$는 $\lfloor hj/k\rfloor$의
홀짝입니다. 따라서 $r(j,k)$는 $\lfloor hj/k\rfloor$가 홀수인 $h$의 개수이고, 이는
$(k-1-s_4(j,k))/2$입니다. 이제 (4.1)을 적용합니다. $\square$

따라서 논문의 상계 $\varepsilon_j(k)\le(j-1)/(2k)$는 항별 하계 $s_3(c,j)\ge-(j-1)/2$와
같습니다. 정확한 값을 $j$에 대해 더하면 (4.3)으로 돌아갑니다.

이 항별 하계는 무한히 많은 항에서 참값과 약 $2$배 이내로 차이 납니다. 6절에 의해
$j\mid 2k-1$일 때마다 $s_3(k\bmod j,j)=-(j-1)^2/(4j)$, 즉
$\varepsilon_j(k)=(j-1)^2/(4jk)$입니다. 따라서 더 나은 항별 상계는 불가능하며, 개선하려면
서로 다른 $j$ 사이의 상쇄를 이용해야 합니다. `verify.py`는 $k\le400$인 모든 소수와
$j\le k-2$인 모든 홀수 $j$에 대해 $r(j,k)$의 항등식을 검사합니다.

## 6. 약수 항

**명제 6.1.** $j\ge3$이 홀수라 합시다. $j\mid 2k-1$이면
$s_3(k\bmod j,j)=-(j-1)^2/(4j)$이고, $j\mid 2k+1$이면 $s_3(k\bmod j,j)=+(j-1)^2/(4j)$입니다.

*증명.* $j\mid 2k-1$이면 $k\equiv\bar2\pmod j$입니다.

- 보조정리 4.2와 $s(\bar h,j)=s(h,j)$에 의해 $s_3(\bar2,j)=2s(2,j)-4s(1,j)$입니다.
- 고전적인 값은 $s(1,j)=\frac{(j-1)(j-2)}{12j}$, 그리고 홀수 $j$에 대해
  $s(2,j)=\frac{(j-1)(j-5)}{24j}$입니다 [RG72].
- 이 둘을 조합하면 $-(j-1)^2/(4j)$가 됩니다.

$j\mid 2k+1$이면 $k\equiv-\bar2\pmod j$이고 $s_3(-h,j)=-s_3(h,j)$입니다. $\square$

$2k\mp1=jd$로 씁니다. $j\mid 2k-1$인 항은 $2V(k)/k$에 $-(j-1)^2/(2jk)\approx-1/d$를
더합니다. 따라서 $2k-1$의 약수 $j\ge3$ 전체에서 이 항들은 $S(k)/k$에 약
$-(\sigma_{-1}(2k-1)-1)$만큼 기여합니다. $2k+1$의 약수들은 약
$+(\sigma_{-1}(2k+1)-1)$만큼 기여합니다.

이 항들은 소수 $k$를 따라 유계가 아닙니다. 홀수 $M$에 대해 Dirichlet 정리는
$k\equiv(M+1)/2\pmod M$인 소수가 무한히 많음을 보장하고, 이런 $k$에서는 $M\mid 2k-1$이므로
$\sigma_{-1}(2k-1)\ge\sigma_{-1}(M)$입니다. 그리고 $\sigma_{-1}$은 홀수에서 유계가 아닙니다.
반면 Mertens 정리에 의해 $\sigma_{-1}(m)\le\prod_{p\mid m}p/(p-1)=O(\log\log m)$이므로 이
항들의 크기는 많아야 $\log\log k$ 정도로, 주항 $\tfrac12\ln k$보다 훨씬 작습니다. 데이터의
극값도 이 그림과 맞습니다.

- $10^3<k\le2\cdot10^6$인 소수에서 $E(k)=S(k)/k-\tfrac12\ln k$의 최솟값은
  $k=750749$에서의 $-2.160$이며, 이때 $2k-1=3^5\cdot37\cdot167$입니다.
- 최댓값은 $k=1735651$에서의 $+2.363$이며, 이때 $2k+1=3\cdot11\cdot37\cdot2843$입니다.

`verify.py`는 $k\le400$인 모든 소수에 대해 명제 6.1을 검사하고 이 극값들을 출력합니다.

## 7. 무조건적 상계

**정리 7.1.** 모든 홀수 소수 $k$에 대해

\[
|S(k)|<6k(1+\ln k)^2+8k.
\]

특히 $S(k)=O(k\log^2k)$입니다. 따라서 추측 3.3의 두 번째 부등식이 성립합니다. 모든
$C_2>0$과 $\varepsilon>0$에 대해 충분히 큰 모든 $k$에서
$6k(1+\ln k)^2+8k<C_2k^{1+\varepsilon}$이므로, 충분히 큰 모든 소수 $k$에서
$S(k)<C_2k^{1+\varepsilon}$입니다. Lean에서는 이것이 `statement_3_3_upper`이며, 진술만 하고
증명하지는 않았습니다.

아래 증명은 손으로 쓴 것이며 기계 검증되지 않았습니다. 독립적인 검토 한 번(별도의 AI
세션)이 모든 단계를 다시 유도했고 빈틈을 찾지 못했습니다. `verify.py`는 $k\le400$인 모든
소수에 대해 증명의 각 주장을 검사합니다.

- 1단계의 잉여류 주장과 부등식;
- 모든 $h$에 대한 2단계의 두 추정;
- 3단계의 연분수 다항식(continuant) 항등식, 모든 사중쌍이 만족하는 조건, 사실 1–3, 그리고
  표시된 부등식 사슬의 각 고리;
- 결론의 두 고리.

로그가 들어간 고리는 부동소수점으로, 나머지는 모두 정확하게 검사합니다. `verify.py`는
커밋된 표의 모든 행에서도 최종 상계를 검사하지만, 거기서는 여유가 40배 이상이므로
($|S(k)|$와 상계의 비는 $k=7$에서 가장 크며 $0.024$입니다) 이 검사는 건전성 확인일
뿐입니다.

*1단계: $|S(k)|\le18\sum_{h=1}^{k-1}|s(h,k)|$.* $c\in\{1,2,4\}$를 잡으면 $c$는 $k$를
법으로 가역입니다. $1\le m\le n$에 대한 $2n$개의 잉여 $\pm cm$은 정확히 $1,\dots,k-1$이고,
$|s(-h,k)|=|s(h,k)|$입니다. 따라서 각 $c$에 대해
$\sum_{m=1}^{n}|s(cm,k)|=\tfrac12\sum_h|s(h,k)|$이고, (D)에서
$|S(k)|\le\tfrac{8+20+8}2\sum_h|s(h,k)|$를 얻습니다.

*2단계: $|s(h,k)|<(A(k/h)+5)/12$. 여기서 $A(k/h)=q_1+\dots+q_r$은 부분 몫의 합입니다.*
(BHK)에서 $0<h+h'<2k$이고 $\bigl|\sum(-1)^{i+1}q_i-2+(-1)^r\bigr|\le A(k/h)+3$입니다.

*3단계: $\sum_{h=1}^{k-1}A(k/h)\le4k(1+\ln k)^2$.* $(k,h)$에 유클리드 호제법을 적용합니다.
$r_0=k$, $r_1=h$, $r_{i-1}=q_ir_i+r_{i+1}$이고, $r_m=1$, $r_{m+1}=0$에서 끝납니다.
연분수 다항식(continuant) $Q_{-1}=0$, $Q_0=1$, $Q_i=q_iQ_{i-1}+Q_{i-2}$를 쓰면 $i$에 대한
귀납법으로

\[
k=Q_{i-1}r_{i-1}+Q_{i-2}r_i\qquad(1\le i\le m)
\]

를 얻습니다. 각 단계 $(h,i)$를 사중쌍 $(Q,Q',a,b)=(Q_{i-1},Q_{i-2},r_{i-1},r_i)$로
보냅니다. 그러면 $Qa+Q'b=k$, $a>b\ge1$, $Q\ge1$, $0\le Q'\le Q$이고
$q_i\le a/b\le k/(Qb)$입니다. 세 가지 사실로 합을 제한합니다.

1. *같은 사중쌍을 주는 단계는 많아야 둘입니다.* $Q'=0$은 $i=1$일 때뿐입니다. 그 밖의
   경우 $Q/Q'=[q_{i-1};q_{i-2},\dots,q_1]$이고 모든 성분이 $1$ 이상입니다. 이는 유리수의
   두 연분수 전개를 제외하면 $(q_1,\dots,q_{i-1})$을 결정합니다. 그런 다음 $(a,b)$에서
   호제법을 거꾸로 실행하면 $h=r_1$이 복원됩니다.
2. *$Q$와 $b$를 고정하면 사중쌍은 많아야 둘입니다.* $\gcd(Q,b)$는 소수 $k$를 나눕니다.
   이 값이 $k$이면 $Q\ge k$, $Qa\ge2k$가 되므로 불가능합니다. 따라서 $Q'$는
   $Q'b\equiv k\pmod Q$에 의해 $Q$를 법으로 결정되고, $[0,Q]$ 안에는 많아야 두 값이
   남으며, 그러면 $a=(k-Q'b)/Q$도 결정됩니다.
3. *범위.* $b<a\le k/Q$이므로 $b<k/Q$이고 $Q<k$입니다.

따라서

\[
\sum_{h=1}^{k-1}A(k/h)\le2\sum_{(Q,Q',a,b)}\frac ab
\le4\sum_{Q=1}^{k-1}\ \sum_{1\le b<k/Q}\frac k{Qb}
\le4k\sum_{Q=1}^{k-1}\frac{1+\ln(k/Q)}Q\le4k(1+\ln k)^2.
\]

*결론.* $|S(k)|\le18\sum_h|s(h,k)|<\tfrac32\sum_hA(k/h)+\tfrac{15}2(k-1)
<6k(1+\ln k)^2+8k$. $\square$

정확한 평균은 $\sum_hA(k/h)=\tfrac6{\pi^2}k\ln^2k+O(k\log k(\log\log k)^2)$입니다
[YK75]. $k=999983$에서 비율 $\sum_hA(k/h)/(k\ln^2k)$는 $0.719$입니다. 따라서 1, 2단계와
[YK75]만으로도 $S(k)=O(k\log^2k)$를 얻으며, 3단계는 모든 $k$에 대해 상계를 명시적으로
만들 뿐입니다. 정리 7.1은 최적과는 거리가 멉니다. (4.4)와 데이터에 따르면 $S(k)$는 약
$\tfrac12k\ln k$이며, 남는 로그 하나는 삼각 부등식을 쓴 대가입니다.

## 8. 추측에 필요한 것

추측 1.1과 4.1–4.4는 여전히 미해결이며, 추측 3.3의 첫 번째 부등식(추측 4.4와 동치, 1절)도
마찬가지입니다. (4.3)과 (4.4)에 의해 다음이 성립합니다.

- **추측 1.1**은 모든 홀수 소수 $k$에 대해
  $V(k)>\tfrac12\bigl(\tfrac{k-1}2-kH(k)\bigr)$라는 것과 동치이며, 이 하계의 크기는
  $-\tfrac14k\ln k$ 정도입니다(Lean: `statement_1_1_iff`).
- **추측 4.4**는 소수를 따라 $\tfrac12\ln k+2V(k)/k\to\infty$라는 것과 동치입니다.
  $\liminf V(k)/(k\ln k)>-\tfrac14$이면 충분합니다.

따라서 충분히 큰 모든 $k$에 대한 하계 $V(k)\ge-(\tfrac14-\delta)k\ln k$가 있으면 추측
4.4가 해결됩니다. 이 하계는 명시적인 지점 이후로 추측 1.1과 4.1–4.3도 해결하며, 남는
유한 범위는 계산으로 처리할 수 있을 것입니다.

위의 도구들로는 그런 하계에 이르지 못합니다.

- **항별 상계.** 이런 상계는 $2k-1$의 약수에서 $s_3=-(j-1)^2/(4j)$가 되는 경우를
  허용해야 합니다(6절).
- **부분 몫의 평균.** 7절처럼 이 방법은 $|V(k)|=O(k\log^2k)$만 주며, 로그가 하나
  남습니다.
- **디리클레 지표.** 아래 명제 8.1은 $S(k)$를 $k$를 법으로 하는 홀수 지표들에 대한
  가중합으로 정확히 씁니다. 이 합을 아래에서 제한하는 결과는 알지 못합니다.

**명제 8.1(지표합 표현).** 모든 소수 $k\ge5$에 대해

\[
S(k)=\frac{4k}{(k-1)\pi^2}\sum_{\chi(-1)=-1}|L(1,\chi)|^2\,|2\bar\chi(2)-1|^2\,
\bigl(2\bar\chi(2)-1\bigr)\,B_{1,\bar\chi},
\qquad B_{1,\bar\chi}=\frac1k\sum_{a=1}^{k-1}a\,\bar\chi(a)
\]

입니다. 여기서 $\chi$는 $k$를 법으로 하는 홀수 디리클레 지표 전체를 움직입니다.

*증명.* $\chi$가 홀수 지표라 합시다. 코탄젠트의 부분분수 전개에서
$\sum_a\chi(a)\cot(\pi a/k)=(2k/\pi)L(1,\chi)$를 얻습니다. 이를 $s(a,k)$의 코탄젠트 공식
[RG72]과 함께 쓰면 $\sum_a\chi(a)s(a,k)=(k/\pi^2)|L(1,\chi)|^2$이 되며, 이는 Walum
항등식 [Wa82]의 바탕에 있는 계산입니다. $s(-a,k)=-s(a,k)$이므로 짝수 지표는 $0$을
줍니다. (3.1)에 의해 $\sum_{m\le n}\bar\chi(m)=(\chi(2)-2)B_{1,\bar\chi}$입니다.
$s(cm,k)$를 지표로 전개하고 두 계산을 (D)에 대입한 뒤, $x=\bar\chi(2)$에 대해
$(8-20x+8x^2)(\bar x-2)=4(2x-1)|2x-1|^2$을 쓰면 됩니다. $\square$

명제 8.1은 [Zh03, Lemma 5]의 직접적인 결과입니다. 이 보조정리는 $k$가 홀수이고
$\gcd(h,k)=1$일 때 각 $S'(h,k)$를 홀수 지표로 전개합니다. 소수 $k$와 짝수 $h$에 대해서는
$S'(h,k)=-\frac{16k}{(k-1)\pi^2}\sum_{\chi(-1)=-1}\chi(h)|L(1,\chi\chi_2^0)|^2$이 되며,
$\chi_2^0$은 $2$를 법으로 하는 주지표입니다. 이를 짝수 $h$에 대해 더하고
$|L(1,\chi\chi_2^0)|=\tfrac12|2-\chi(2)|\,|L(1,\chi)|$와 $|2-\chi(2)|=|2\chi(2)-1|$을 쓴
뒤 $\chi$를 $\bar\chi$로 바꾸면 명제 8.1이 됩니다.

여기서 가우스 합 $\tau(\bar\chi)=\sum_a\bar\chi(a)e^{2\pi ia/k}$에 대해
$B_{1,\bar\chi}=\tfrac i\pi\,\tau(\bar\chi)L(1,\chi)$이므로
$|B_{1,\bar\chi}|=\sqrt k\,|L(1,\chi)|/\pi$입니다. 따라서 추측 1.1은 $L(1,\chi)$와 가우스
합의 한 혼합 평균값이 양수라는 명제입니다. `verify.py`는 $5\le k\le100$인 모든 소수에
대해 명제 8.1, [Zh03, Lemma 5]에서 인용한 전개, $|B_{1,\bar\chi}|$의 값을 부동소수점으로
검사하며, $L(1,\chi)$는 디감마 함수로 독립적으로 계산합니다.

*증명이 아닌 휴리스틱.* 6절은 $E(k)=S(k)/k-\tfrac12\ln k=c_0+2V(k)/k$가 $\log\log k$
규모로 요동한다는 것을 시사합니다. 데이터도 이와 맞습니다.

- $10^3<k\le2\cdot10^6$인 소수에서 $E(k)$는 $[-2.2,2.4]$ 안에 있습니다.
- $E(k)$의 십진 구간별 평균은 약 $0.24$입니다.
- $k>10^3$에서 최소제곱법으로 $S(k)/k\approx0.5005\ln k+0.2325$를 얻습니다.

$|V(k)|=o(k\log k)$이면 추측 4.4와 3.3이 따라 나옵니다.

## 9. 계산

세 프로그램이 $S(k)$를 정확히 계산합니다.

| 프로그램 | 방법 | $k$당 비용 | 산술 |
|---|---|---|---|
| `s_dedekind.cpp` (A) | (D)와 (BHK) | $O(k\log k)$ | `__int128`, 나눗셈 검사 |
| `s_hardy.cpp` (B) | (2.1), (4.1), (4.2) | $O(k\log k)$ | 오버플로와 정확성을 검사하는 `int64_t` |
| `s_literal.cpp` (C) | 정의 그대로, 항등식 없음 | $O(k^2)$ | `int64_t` |

방법 A와 B는 $S(k)$의 서로 다른 분해와 Dedekind 합의 서로 다른 계산법을 씁니다. 둘 다
Dedekind 합의 고전 이론에 기대며, `verify.py`가 그 항등식들을 정의와 비교해 검사합니다.
방법 C는 항등식을 전혀 쓰지 않습니다.

Apple M5 Max에서 작업마다 스레드 하나로 실행했으며, 로그는 `logs/`에 있습니다. 시간은
`/usr/bin/time -p`가 출력한 CPU(user) 시간입니다. 스레드 두 개 한도를 지키려고 Lean 빌드
중에는 일부 작업을 일시 정지했고, `time`이 출력한 `real` 값 몇 개가 로그의 시작·종료 시각과
맞지 않으므로 실제 경과 시간은 적지 않습니다.

| 실행 | 범위 | CPU 시간 |
|---|---|---|
| A | 홀수 소수 $3\le k\le10^6$ | 2055초 |
| B | 홀수 소수 $3\le k\le10^6$ | 1882초 |
| A, B(커밋된 소스, clang++ -O3) | 홀수 소수 $\le2\cdot10^5$ | 78초, 71초; 첫 실행과 동일 |
| A | $(10^6,1.5\cdot10^6]$와 $(1.5\cdot10^6,2\cdot10^6]$의 홀수 소수 | 2406초, 3347초 |
| B | 같은 두 구간 | 2211초, 3055초 |
| C | 홀수 소수 $\le30000$ | 446초 |
| C | 모든 $1\le k\le10000$ | 162초 |
| C | $k=10395,17017,19019$ | 1초 미만 |

결과:

- A와 B는 $k\le2\cdot10^6$인 모든 홀수 소수에서 일치합니다. C는 $k\le30000$인 모든 홀수
  소수에서 A와 일치합니다.
- $k\le10^4$에서 C는 논문의 음수 값 151개(모두 합성수 $k$)와 논문이 인용한 합성수 값을
  재현합니다.
- $k\le2\cdot10^6$인 홀수 소수 가운데 추측 1.1, 4.1, 4.2, 4.3을 위반하는 것은 없습니다.
- 소수 $k>5$에서 $S(k)/k$의 최솟값은 $k=11$에서의 $14/11$입니다.
- $S(k)\le3k$인 가장 큰 소수는 논문과 같이 $3119$입니다. $S(k)\le4k$인 가장 큰 소수는
  $58013$이고, $S(k)\le5k$인 가장 큰 소수는 $869399$입니다. $S(k)\le6k$는 범위 끝에 가까운
  $k=1999619$에서도 나타납니다.
- $10^4$ 아래에서 $S(k)<2k$인 소수 17개와 $S(k)\le3k$인 소수 87개라는 논문의 목록이
  그대로 재현됩니다.

논문(v3, 3절)은 $k\le50000$인 소수에서 $S(k)>4k$를 위반하는 쌍이 8개라고 합니다. 표에서
그 8개는 정확히 $(30000,50000]$에서 $S(k)\le4k$인 소수들입니다. $(10^4,5\cdot10^4]$에는
그런 소수가 79개 있고, $5\cdot10^4$ 이하에는 508개의 홀수 소수가 있습니다. 논문의 그
문장은 아마 30000보다 큰 범위를 가리키는 것으로 보입니다.

데이터 파일(각 줄에 `k S(k)` 한 쌍):

- `data/S_odd_primes.txt`: $k\le2\cdot10^6$인 모든 홀수 소수, 방법 A와 B.
- `data/S_all_k_le_10000.txt`: $1\le k\le10000$인 모든 $k$, 방법 C.

`verify.py`(CI 모드, 약 15초. `g++`와 `mpmath`가 있는 Python 3가 필요하며, `mpmath`는
CI에서처럼 `sympy`와 함께 설치됩니다)는 세 가지를 합니다.

1. 2–8절의 모든 항등식을 작은 범위에서 검사하고, $k\le400$인 모든 소수에 대해 정리 7.1
   증명의 각 주장을 검사합니다. 명제 8.1과 7절에서 로그가 들어간 고리는 부동소수점으로,
   나머지는 정확하게 검사합니다.
2. 세 프로그램을 컴파일하고, $50000$ 이하의 모든 홀수 소수에서 A와 B를 표와 비교하며,
   $2500$ 이하의 모든 소수, $1500$ 이하의 모든 $k$, 논문의 합성수 값에서 C를 비교합니다.
3. 두 표 전체를 감사합니다.

`verify.py --full`은 표 전체에 대해 모든 것을 다시 실행하며 몇 시간이 걸립니다.

## 10. 참고문헌

- [BBMXZ] B. C. Berndt, R. N. Bhat, J. L. Meyer, L. Xie, A. Zaharescu, *An arithmetic sum
  associated with the classical theta function*, arXiv:2501.03234 (v1–v3); Results Math. 81,
  no. 1, doi:10.1007/s00025-025-02584-2 (확인하지 않음; 여기의 번호는 arXiv를 따름).
- [Ba77] P. Barkan, Sur les sommes de Dedekind et les fractions continues finies, C. R. Acad.
  Sci. Paris Sér. A 284 (1977), 923–926.
- [Be78] B. C. Berndt, Analytic Eisenstein series, theta-functions, and series relations in the
  spirit of Ramanujan, J. Reine Angew. Math. 304 (1978), 332–365.
- [BD82] B. C. Berndt, U. Dieter, Sums involving the greatest integer function and
  Riemann–Stieltjes integration, J. Reine Angew. Math. 337 (1982), 208–220.
- [BG84] B. C. Berndt, L. A. Goldberg, Analytic properties of arithmetic sums arising in the
  theory of the classical theta-functions, SIAM J. Math. Anal. 15 (1984), 143–150.
- [Da20] M. C. Dağlı, New relations concerning a mean value of some Hardy sums and Ramanujan
  sum, Süleyman Demirel Univ. J. Sci. (Fac. Arts Sci.) 15 (2020), 148–157,
  doi:10.29233/sdufeffd.702928.
- [Go81] L. A. Goldberg, *Transformations of theta-functions and analogues of Dedekind sums*,
  Ph.D. thesis, University of Illinois at Urbana-Champaign, 1981.
- [Hi77] D. Hickerson, Continued fractions and density results for Dedekind sums, J. Reine
  Angew. Math. 290 (1977), 113–116.
- [Kn77] D. E. Knuth, Notes on generalized Dedekind sums, Acta Arith. 33 (1977), 297–325.
- [Me97] J. L. Meyer, Properties of certain integer-valued analogues of Dedekind sums, Acta
  Arith. 82 (1997), 229–242.
- [RG72] H. Rademacher, E. Grosswald, *Dedekind Sums*, Carus Math. Monographs 16, MAA, 1972.
- [Si87] R. Sitaramachandrarao, Dedekind and Hardy sums, Acta Arith. 48 (1987), 325–340.
- [Wa82] H. Walum, An exact formula for an average of $L$-series, Illinois J. Math. 26 (1982),
  1–3.
- [YK75] A. C. Yao, D. E. Knuth, Analysis of the subtractive algorithm for greatest common
  divisors, Proc. Nat. Acad. Sci. USA 72 (1975), 4720–4722.
- [Zh03] W. Zhang, On a hybrid mean value of certain Hardy sums and Ramanujan sum, Osaka J.
  Math. 40 (2003), 365–373.
