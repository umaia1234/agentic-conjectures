[English](README.md) | **한국어**

# Frankl's union-closed sets conjecture

확인 기준일: 2026-08-11.

## 문제

`{empty set}` 하나만으로 이루어진 경우를 제외한 모든 유한 union-closed
family `F`에 대해, `|F|/2`개 이상의 member set에 포함되는 원소가 항상
존재하는지를 묻는다.

## 현재 상태와 알려진 부분결과

2026년 저널 게재 논문도 이를 추측으로 다루며 최소 반례가 만족해야 할 새
필요조건을 제시한다. 알려진 계산 보조 결과와 일반 하한은 다음과 같다.

- ground set 크기 12 이하에서는 추측이 성립한다.
- 일반적인 family에는 적어도 한 원소가 약 `0.38234 |F|`개의 집합에
  포함된다는 무차원 하한이 증명되어 있다.

따라서 ground set 크기 13은 완전 확인된 범위 바로 다음의 유한 경우이다.
이 말은 13이 최소 반례의 크기라고 알려졌다는 뜻은 아니다.

## 계산 관점

ground set 크기 13에는 가능한 member set가 8,192개 있다. Union closure,
원소별 빈도 상한, 동형 제거를 SAT, ILP 또는 BDD에 함께 넣을 수 있다.
계산 결과를 일반 정리로 해석하려면 전체 경우의 포괄성과 인증 가능한
UNSAT 증명이 필요하다.

## FormalConjectures 원본

[로컬 upstream snapshot](upstream/README.md)은 일반 Frankl 추측과 알려진
12원소 변형의 Lean 명제를 함께 보존한다. 두 선언의 `sorry`는 명제
표시일 뿐 이 파일 안의 형식 증명이 아니며, 이 디렉터리도 13원소 경우를
해결하지 않는다. 다음 절의 고전적 특수 경우들은 이 저장소에서 upstream
정의의 사본에 대해 Lean으로 검증했다.

## Lean 4 형식화: 고전적 특수 경우 (2026-10-24)

[`AgenticConjectures/FranklUnionClosed.lean`](../../AgenticConjectures/FranklUnionClosed.lean)
(namespace `AgenticConjectures.FranklUnionClosed`, `sorry` 없음, mathlib만
사용)은 추측을 `Prop`으로 기록하고 다음 특수 경우들을 증명한다. 여기서
`A : Finset (Finset n)`은 집합족, `#A`는 구성원 집합의 개수, `A.sup id`는
모든 구성원 집합의 합집합이다.

| 선언 | 내용 |
|---|---|
| `IsUnionClosed` | upstream `UnionClosed.IsUnionClosed`를 항 그대로 옮긴 것: `∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A` |
| `statement` | upstream `UnionClosed.union_closed`, 즉 미해결 추측을 `Prop`으로 기록한 것(**증명하지 않음**) |
| `card_filter_notMem_le_of_singleton_mem` | `{a} ∈ A` ⇒ `#{x ∈ A \| a ∉ x} ≤ #{x ∈ A \| a ∈ x}` (단사 `x ↦ x ∪ {a}`) |
| `card_le_two_mul_card_filter_mem_of_singleton_mem`, `half_le_card_filter_mem_of_singleton_mem` | **한원소 집합 경우**: `{a} ∈ A` ⇒ `#A ≤ 2 * #{x ∈ A \| a ∈ x}`, 동치로 `(1 / 2 : ℚ) * #A ≤ #{x ∈ A \| a ∈ x}` |
| `singleton_mem` | upstream `union_closed.variants.singleton_mem`과 가정·결론이 같음 |
| `card_filter_not_or_le_of_pair_mem` | `{a, b} ∈ A` ⇒ `a`와 `b`를 모두 피하는 구성원 집합은 둘 다 포함하는 구성원 집합보다 많지 않음 (단사 `x ↦ x ∪ {a, b}`) |
| `card_le_card_filter_mem_add_card_filter_mem_of_pair_mem` | **두원소 집합 경우**의 개수 형태: `{a, b} ∈ A` ⇒ `#A ≤ #{x ∈ A \| a ∈ x} + #{x ∈ A \| b ∈ x}` |
| `pair_mem`, `exists_of_pair_mem` | **두원소 집합 경우**: `a` 또는 `b`가 구성원 집합의 절반 이상에 들어 있음(논리합 형태와 upstream의 존재 명제 형태); `a ≠ b`는 가정하지 않음 |
| `sum_card_filter_mem_eq_sum_card` | 이중 셈: `∑ i ∈ A.sup id, #{x ∈ A \| i ∈ x} = ∑ x ∈ A, #x` |
| `exists_card_le_two_mul_card_filter_mem_of_average` | **평균 보조정리**: `#(A.sup id) * #A ≤ 2 * ∑ x ∈ A, #x` ⇒ 어떤 `i ∈ A.sup id`가 `#A ≤ 2 * #{x ∈ A \| i ∈ x}`를 만족 |
| `sup_mem_of_nonempty` | 비어 있지 않은 union-closed family는 구성원 집합 전체의 합집합을 포함 |
| `union_closed_of_card_sup_le_six` | **합집합의 원소가 6개 이하인 집합족에 대한 추측** (upstream 가정에 `#(A.sup id) ≤ 6`을 추가) |
| `univ_card_le_six` | upstream `union_closed.variants.univ_card`에서 `Fintype.card n ≤ 12`를 `Fintype.card n ≤ 6`으로 바꾼 것 |
| `univ_card_two` | upstream `union_closed.variants.univ_card_two` 그대로 |

방법. `{a} ∈ A`이면 `x ↦ x ∪ {a}`는 `a`를 피하는 구성원 집합을 `a`를
포함하는 구성원 집합으로 단사적으로 보낸다(`a`를 다시 빼면 원래 집합이
복원된다). 따라서 구성원 집합의 절반 이상이 `a`를 포함한다. `{a, b} ∈ A`이면
`x ↦ x ∪ {a, b}`는 둘 다 피하는 구성원 집합을 둘 다 포함하는 구성원
집합으로 단사적으로 보낸다. 포함배제 원리에 의해
`#{x ∈ A | a ∈ x} + #{x ∈ A | b ∈ x}`는
`#{x ∈ A | a ∈ x ∨ b ∈ x} + #{x ∈ A | a ∈ x ∧ b ∈ x}`와 같고, 위 단사에
의해 이 값은 `#A` 이상이므로 `a`나 `b`가 구성원 집합의 절반 이상에 들어
있다. 이중 셈으로 합집합 `U`에 대해
`∑ i ∈ U, #{x ∈ A | i ∈ x} = ∑ x ∈ A, #x`를 얻으므로, 구성원 집합의 평균
크기가 `#U / 2` 이상이면 `U`의 어떤 원소가 구성원 집합의 절반 이상에 들어
있다. `#U ≤ 6`인 경우, 크기 1 또는 2인 구성원 집합이 있으면 위의 두 경우로
끝난다. 그렇지 않으면 비어 있지 않은 모든 구성원 집합의 크기가
`3 ≥ #U / 2` 이상이고, 합집합에 대해 닫혀 있으므로 `U` 자신도 구성원
집합이다. `U`의 여분 `#U / 2`가 구성원 `∅`이 있을 때의 부족분을 메우므로
평균 보조정리를 적용할 수 있다.

명제 충실성. `IsUnionClosed`는 [upstream snapshot](upstream/UnionClosed.lean)에서
항 그대로 옮겼다. `statement`는 upstream `union_closed`의 section 변수를
명시적으로 묶은 것이다:
`∀ (n : Type u) [DecidableEq n] [Nonempty n] (A : Finset (Finset n)),
A ≠ {∅} → IsUnionClosed A → ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}`.
집합족은 임의의 바탕 타입 위 `Finset`들의 `Finset`이므로 유한 집합들의
유한 집합족이고, "절반 이상"은 유리수 부등식이므로 나눗셈이나 `ℕ`의 절단
뺄셈이 등장하지 않는다. 집합족 `{∅}`는 제외되며, 그 밖의 경우에는 `∅`가
구성원일 수 있고, 빈 집합족도 허용된다(이때 결론은 임의의 `i`에 대해
성립하므로 `[Nonempty n]`을 가정한다). upstream의 `Type*`는 universe
다형적이며, `statement`는 universe를 매개변수로 받는다. 모든 정리는
upstream의 결론 형태를 쓴다. upstream은 이미 `variants.singleton_mem`(같은
단사로), `variants.univ_card_two`(`decide +revert +kernel`로),
`variants.sharpness`를 증명한다. 앞의 둘은 여기서 복사한 정의에 대해 다시
증명했고(`univ_card_two`는 `univ_card_le_six`의 따름정리로), `sharpness`는
반복하지 않았다. 한원소·두원소 집합 경우에는 `A ≠ {∅}`도 `[Nonempty n]`도
필요 없다. 구성원 `{a}` 또는 `{a, b}`가 `A = {∅}`를 배제하고 증인을
제공하기 때문이다.

재현(저장소 루트에서 실행하며, `lake build`와 `check_axioms.py`에는
mathlib 캐시 `lake exe cache get`이 필요하다):

```bash
lake build AgenticConjectures.FranklUnionClosed   # 이 모듈만, mathlib 빌드 후 약 6초
lake build                                        # 전체 라이브러리 (check_axioms.py에 필요)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py                   # propext / Classical.choice / Quot.sound만 허용
```

주장하지 않는 것. 추측은 증명되지 않았으며, 원소가 13개 이상인 바탕 집합에
대해서는 아무것도 말하지 않는다. 위 결과는 모두 고전적이며 새로움을
주장하지 않는다. 한원소·두원소 집합 경우는 Sarvate와 Renaud(1989)의
결과이고, 평균 보조정리는 표준적인 이중 셈이며, 합집합 크기 `≤ 6` 경우는
Vuckovic과 Zivkovic의 알려진 12원소 정리보다 훨씬 약하다. sorry로 남아 있는
upstream 명제 `union_closed`, `variants.yu`, `variants.univ_card`,
`variants.family_card`, `variants.cardinality_even_of_union_closed_tight`는
여기서 형식화하지 않았다.

## 근거

- Sarvate와 Renaud, "On the union-closed sets conjecture", *Ars Combinatoria* 27 (1989), 149–153 (한원소·두원소 집합 경우)
- [Bouchard, *Le Matematiche* 81(1), 2026](https://arxiv.org/abs/2503.00277)
- [Vuckovic--Zivkovic의 12원소 계산 증명](https://ipsitransactions.org/journals/papers/tir/2017jan/p9.pdf)
- [Yu의 `0.38234` 하한](https://www.mdpi.com/1099-4300/25/5/767)
