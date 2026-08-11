[English](PROOF.md) | **한국어**

# WOWII Graph Conjecture 61의 부분정리

## 표기와 기본 부등식

유한 단순 연결 그래프 \(G\)에 대해

- \(\alpha(G)\): 독립수,
- \(f(G)\): 최대 유도 숲의 정점 수,
- \(r(G)\): Havel--Hakimi residue,
- \(D(G)\): 지름

으로 쓴다. Havel--Hakimi residue는 차수열에 Havel--Hakimi 소거를
반복한 뒤 남는 0의 개수다. 이 문서에서는 기본 부등식

\[
r(G)\le\alpha(G) \tag{1}
\]

을 사용한다. 검토할 원 부등식은

\[
f(G)\ge r(G)+\left\lceil\frac{D(G)}3\right\rceil. \tag{2}
\]

## 정리 1: 독립수와 지름을 쓰는 일반 하계

모든 유한 단순 연결 그래프 \(G\)에 대해

\[
\boxed{f(G)\ge\alpha(G)+\left\lceil\frac{D(G)}4\right\rceil.} \tag{3}
\]

### 증명

\(D=0\)이면 한 정점 그래프이므로 자명하다. 이제 \(D\ge1\)이라 하자.
최대 독립집합을 \(I\), 지름을 실현하는 측지경로를

\[
P=v_0v_1\cdots v_D
\]

라 한다. 위치 집합

\[
S:=\{i\in\{0,\ldots,D\}:v_i\notin I\}
\]

를 정의한다. \(I\)가 독립집합이므로 연속한 \(v_i,v_{i+1}\)가 동시에
\(I\)에 속할 수 없다. 따라서 모든 연속 위치쌍 \(\{i,i+1\}\)은 \(S\)와
만난다.

\(S\)에서 다음 탐욕 선택을 수행한다.

\[
s_1=\min S,
\]

\[
s_{j+1}=\min\{s\in S:s\ge s_j+3\}
\]

로 두고, 다음 선택이 없으면 멈춘다. 선택 수를 \(m\)이라 하자. 첫 연속
위치쌍이 \(S\)와 만나므로 \(s_1\le1\)이다. 다음 선택이 존재하면
\(s_j+3,s_j+4\) 중 적어도 하나가 \(S\)에 있으므로

\[
s_{j+1}\le s_j+4.
\]

마지막 선택 뒤에 \(D\ge s_m+4\)라면 \(s_m+3,s_m+4\) 중 하나를 더 고를
수 있으므로 모순이다. 따라서

\[
D\le s_m+3\le1+4(m-1)+3=4m.
\]

즉

\[
m\ge\left\lceil\frac D4\right\rceil. \tag{4}
\]

\[
X:=\{v_{s_1},\ldots,v_{s_m}\}
\]

로 두자. \(X\)의 서로 다른 두 정점 사이의 \(P\) 위 거리는 적어도
3이다. 측지경로의 부분경로도 측지경로이므로 두 정점의 \(G\)-거리도
적어도 3이다. 따라서 두 정점은 서로 인접하지 않고 공통 이웃도 갖지
않는다.

이에 따라 \(G[I\cup X]\)에서는

- \(I\) 내부에 간선이 없고,
- \(X\) 내부에 간선이 없으며,
- \(I\)의 한 정점이 \(X\)의 두 정점과 동시에 인접할 수 없다.

그러므로 \(G[I\cup X]\)는 중심이 \(X\)에 있는 서로소인 별들과
고립점들의 합이고, 특히 숲이다. 따라서

\[
f(G)\ge|I|+|X|
\ge\alpha(G)+\left\lceil\frac D4\right\rceil.
\]

## 정리 2: 최소 여유와 지름

정점이 두 개 이상인 연결 그래프에서는

\[
f(G)\ge\alpha(G)+1. \tag{5}
\]

또한

\[
\boxed{f(G)=\alpha(G)+1\implies D(G)\le4.} \tag{6}
\]

### 증명

최대 독립집합 \(I\)를 택한다. 연결 비자명 그래프에서는
\(I\ne V(G)\)이므로 \(x\in V(G)\setminus I\)를 하나 고를 수 있다.
\(G[I\cup\{x\}]\)는 하나의 별과 고립점들의 합이므로 유도 숲이고,
(5)가 성립한다.

이제 \(f(G)=\alpha(G)+1\)을 가정하고

\[
J:=V(G)\setminus I
\]

로 둔다. \(|J|=1\)이면 연결성 때문에 \(G\)는 별이고 \(D\le2\)이다.

\(|J|\ge2\)라 하고 서로 다른 \(x,y\in J\)를 택하자.
\(I\cup\{x,y\}\)의 크기는 \(\alpha+2\)이므로 이 집합은 숲을 유도할 수
없고, 따라서 사이클을 포함한다.

\(xy\in E(G)\)이면 \(d(x,y)=1\)이다. \(xy\notin E(G)\)이면 \(I\)가
독립이고 \(I\) 밖의 정점은 \(x,y\)뿐이므로 사이클은

\[
x-u-y-v-x
\]

꼴의 4-cycle을 포함한다. 따라서 \(x,y\)는 공통 이웃을 가지며
\(d(x,y)=2\)다. 결국

\[
d(x,y)\le2\qquad(x,y\in J). \tag{7}
\]

각 \(i\in I\)는 연결성 때문에 \(J\)에 이웃을 가진다. 따라서

\[
d(i,y)\le3\qquad(i\in I,\ y\in J),
\]

\[
d(i,j)\le4\qquad(i,j\in I).
\]

모든 두 정점 사이의 거리가 4 이하이므로 \(D(G)\le4\)다.

## 정리 3: 완전히 판정되는 지름

(2)는

\[
\boxed{D(G)\in\{0,1,2,3,5,6,9\}}
\]

인 모든 연결 그래프에서 성립한다.

### 증명

\(D=0\)이면 한 정점 그래프이고 (1)로 자명하다.

\(D\in\{1,2,3\}\)이면

\[
\left\lceil\frac D4\right\rceil
=\left\lceil\frac D3\right\rceil=1.
\]

따라서 (1), (3)에서

\[
f(G)\ge\alpha(G)+1\ge r(G)+1.
\]

\(D\in\{5,6\}\)이면 (5)에 따라 \(f\ge\alpha+1\)이다. (6)에 의해
등호일 수 없고 \(f,\alpha\)가 정수이므로

\[
f(G)\ge\alpha(G)+2.
\]

또한 \(\lceil D/3\rceil=2\)이므로 (2)가 성립한다.

\(D=9\)이면 (3)에서

\[
f(G)\ge\alpha(G)+\left\lceil\frac94\right\rceil
=\alpha(G)+3\ge r(G)+3,
\]

이고 \(\lceil9/3\rceil=3\)이다.

## 정리 4: 모든 나무

모든 유한 나무 \(T\)는 지름과 관계없이 (2)를 만족한다.

### 증명

\[
n:=|V(T)|,
\]

\[
\nu(T):=\text{최대 매칭 수},
\qquad
\tau(T):=\text{최소 정점덮개 수}
\]

로 둔다. 나무 자체가 숲이므로

\[
f(T)=n. \tag{8}
\]

독립집합과 정점덮개의 여집합 관계로

\[
\alpha(T)=n-\tau(T). \tag{9}
\]

모든 정점덮개는 매칭의 각 간선에서 서로 다른 끝점을 적어도 하나씩
포함해야 하므로

\[
\tau(T)\ge\nu(T). \tag{10}
\]

지름 경로는 \(D+1\)개의 정점을 가지며, 교대로 간선을 고르면 크기

\[
\left\lfloor\frac{D+1}{2}\right\rfloor
=\left\lceil\frac D2\right\rceil
\]

의 매칭을 얻는다. 따라서

\[
\nu(T)\ge\left\lceil\frac D2\right\rceil. \tag{11}
\]

(1), (9)--(11)을 결합하면

\[
r(T)\le\alpha(T)\le n-\left\lceil\frac D2\right\rceil.
\]

그러므로

\[
\begin{aligned}
r(T)+\left\lceil\frac D3\right\rceil
&\le n-\left\lceil\frac D2\right\rceil
+\left\lceil\frac D3\right\rceil\\
&\le n=f(T).
\end{aligned}
\]

따라서 모든 나무에서 (2)가 성립한다.
