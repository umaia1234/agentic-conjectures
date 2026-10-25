**English** | [한국어](README.ko.md)

# Frankl's union-closed sets conjecture

Status checked as of: 2026-08-11.

## Problem

The question is whether, for every finite union-closed family `F` other than
the one consisting solely of `{empty set}`, there always exists an element
contained in at least `|F|/2` of the member sets.

## Current status and known partial results

A 2026 journal-published paper also treats this as a conjecture and presents
new necessary conditions that a minimal counterexample must satisfy. The
known computer-assisted results and the general lower bound are as follows.

- The conjecture holds for ground sets of size at most 12.
- For general families, a dimension-free lower bound has been proved: at
  least one element is contained in about `0.38234 |F|` of the sets.

Therefore ground set size 13 is the finite case immediately after the fully
verified range. This does not mean that 13 is known to be the size of a
minimal counterexample.

## Computational perspective

For ground set size 13 there are 8,192 possible member sets. Union closure,
per-element frequency upper bounds, and isomorphism elimination can be put
together into SAT, ILP, or BDD. Interpreting a computational result as a
general theorem requires exhaustiveness over all cases and a certifiable
UNSAT proof.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves both the Lean
statement of the general Frankl conjecture and that of the known 12-element
variant. The `sorry` in the two declarations is only a statement marker, not
a formal proof inside that file, and this directory likewise does not
resolve the 13-element case. The classical special cases in the next
section are Lean-verified here against a copy of the upstream definition.

## Lean 4 formalization: classical special cases (2026-10-24)

[`AgenticConjectures/FranklUnionClosed.lean`](../../AgenticConjectures/FranklUnionClosed.lean)
(namespace `AgenticConjectures.FranklUnionClosed`, `sorry`-free, mathlib
only) records the conjecture as a `Prop` and proves the following special
cases. Here `A : Finset (Finset n)` is the family, `#A` its number of
members, and `A.sup id` the union of all members.

| Declaration | Content |
|---|---|
| `IsUnionClosed` | upstream `UnionClosed.IsUnionClosed`, term for term: `∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A` |
| `statement` | upstream `UnionClosed.union_closed`, the open conjecture, as a `Prop` (**not** proved) |
| `card_filter_notMem_le_of_singleton_mem` | `{a} ∈ A` ⇒ `#{x ∈ A \| a ∉ x} ≤ #{x ∈ A \| a ∈ x}` (injection `x ↦ x ∪ {a}`) |
| `card_le_two_mul_card_filter_mem_of_singleton_mem`, `half_le_card_filter_mem_of_singleton_mem` | **singleton case**: `{a} ∈ A` ⇒ `#A ≤ 2 * #{x ∈ A \| a ∈ x}`, equivalently `(1 / 2 : ℚ) * #A ≤ #{x ∈ A \| a ∈ x}` |
| `singleton_mem` | upstream `union_closed.variants.singleton_mem`, same hypotheses and conclusion |
| `card_filter_not_or_le_of_pair_mem` | `{a, b} ∈ A` ⇒ the members avoiding both `a` and `b` are at most as many as those containing both (injection `x ↦ x ∪ {a, b}`) |
| `card_le_card_filter_mem_add_card_filter_mem_of_pair_mem` | **two-element case**, counting form: `{a, b} ∈ A` ⇒ `#A ≤ #{x ∈ A \| a ∈ x} + #{x ∈ A \| b ∈ x}` |
| `pair_mem`, `exists_of_pair_mem` | **two-element case**: `a` or `b` lies in at least half of the members (as a disjunction, and in the existential upstream form); `a ≠ b` is not assumed |
| `sum_card_filter_mem_eq_sum_card` | double counting: `∑ i ∈ A.sup id, #{x ∈ A \| i ∈ x} = ∑ x ∈ A, #x` |
| `exists_card_le_two_mul_card_filter_mem_of_average` | **averaging lemma**: `#(A.sup id) * #A ≤ 2 * ∑ x ∈ A, #x` ⇒ some `i ∈ A.sup id` has `#A ≤ 2 * #{x ∈ A \| i ∈ x}` |
| `sup_mem_of_nonempty` | a nonempty union-closed family contains the union of its members |
| `union_closed_of_card_sup_le_six` | **the conjecture for families whose union has at most 6 elements** (upstream hypotheses plus `#(A.sup id) ≤ 6`) |
| `univ_card_le_six` | upstream `union_closed.variants.univ_card` with `Fintype.card n ≤ 12` replaced by `Fintype.card n ≤ 6` |
| `univ_card_two` | upstream `union_closed.variants.univ_card_two`, verbatim |

Method. If `{a} ∈ A`, then `x ↦ x ∪ {a}` maps the members avoiding `a`
injectively (remove `a` again) into the members containing `a`, so at least
half of the members contain `a`. If `{a, b} ∈ A`, then `x ↦ x ∪ {a, b}`
maps the members avoiding both injectively into the members containing
both. By inclusion–exclusion, `#{x ∈ A | a ∈ x} + #{x ∈ A | b ∈ x}`
equals `#{x ∈ A | a ∈ x ∨ b ∈ x} + #{x ∈ A | a ∈ x ∧ b ∈ x}`, which is at
least `#A` by that injection, so `a` or `b` lies in at least half of the
members. Double counting gives
`∑ i ∈ U, #{x ∈ A | i ∈ x} = ∑ x ∈ A, #x` for the union `U`, so if the
average member size is at least `#U / 2`, some element of `U` lies in at
least half of the members. For `#U ≤ 6`: a member of size 1 or 2 is
handled by the two cases above; otherwise every nonempty member has at
least `3 ≥ #U / 2` elements, and since `U` itself is a member (union
closure), its surplus `#U / 2` makes up for a possible member `∅`, so the
averaging lemma applies.

Statement faithfulness. `IsUnionClosed` is copied term for term from the
[upstream snapshot](upstream/UnionClosed.lean). `statement` is the upstream
`union_closed` with its section variables bound explicitly:
`∀ (n : Type u) [DecidableEq n] [Nonempty n] (A : Finset (Finset n)),
A ≠ {∅} → IsUnionClosed A → ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}`.
Families are `Finset`s of `Finset`s over an arbitrary ground type, hence
finite families of finite sets; "at least half" is a rational inequality,
so no division or truncated `ℕ` subtraction occurs. The family `{∅}` is
excluded, `∅` may otherwise be a member, and the empty family is allowed
(its conclusion holds for any `i`, which is why `[Nonempty n]` is assumed).
Upstream's `Type*` is universe polymorphic; `statement` takes the universe
as a parameter. All theorems use the upstream conclusion form. Upstream
already proves `variants.singleton_mem` (by the same injection),
`variants.univ_card_two` (by `decide +revert +kernel`) and
`variants.sharpness`; the first two are re-proved here against the copied
definition, `univ_card_two` as a corollary of `univ_card_le_six`, and
`sharpness` is not repeated. The singleton and two-element cases need
neither `A ≠ {∅}` nor `[Nonempty n]`, because the member `{a}` or `{a, b}`
excludes `A = {∅}` and supplies the witness.

Reproduce (from the repository root; `lake build` and `check_axioms.py`
need the mathlib cache, `lake exe cache get`):

```bash
lake build AgenticConjectures.FranklUnionClosed   # this module alone, ~6 s once mathlib is built
lake build                                        # whole library (needed by check_axioms.py)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py                   # only propext / Classical.choice / Quot.sound
```

Not claimed. The conjecture is not proved, and nothing is said about
ground sets of 13 or more elements. Every result above is classical and no
novelty is claimed: the 1-set and 2-set cases are due to Sarvate and Renaud
(1989), the averaging lemma is standard double counting, and the
union-size `≤ 6` case is much weaker than the known 12-element theorem of
Vuckovic and Zivkovic. The sorry-backed upstream statements `union_closed`,
`variants.yu`, `variants.univ_card`, `variants.family_card` and
`variants.cardinality_even_of_union_closed_tight` remain unformalized here.

## Evidence

- Sarvate and Renaud, "On the union-closed sets conjecture", *Ars Combinatoria* 27 (1989), 149–153 (the 1-set and 2-set cases)
- [Bouchard, *Le Matematiche* 81(1), 2026](https://arxiv.org/abs/2503.00277)
- [Vuckovic--Zivkovic's 12-element computational proof](https://ipsitransactions.org/journals/papers/tir/2017jan/p9.pdf)
- [Yu's `0.38234` lower bound](https://www.mdpi.com/1099-4300/25/5/767)
