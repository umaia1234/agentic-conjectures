**English** | [한국어](README.ko.md)

# Erdős problem #385 / #430(i)

The official problem number is #385. The `ep430_*` names of the source files
are pre-existing names written after the equivalence with the first question
of #430, so they were kept for the sake of reproduction history. The two
programs are finite-range experiments and are not a proof of the full
problem.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the exact Lean
statements of parts (i), (ii) and the lower-bound variant. The research
statements contain `sorry`, and the finite-range computations below prove
none of them.

## AlphaProof Nexus benchmark provenance

The pinned [list of attempts](https://github.com/google-deepmind/alphaproof-nexus-results/blob/0647711a71183c1ea492ad60860776617ce1ea88/erdos_problems_attempted.txt)
in Google DeepMind's AlphaProof Nexus `science-submission` snapshot commit
[`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88)
records all of `erdos_385.parts.i`, `erdos_385.parts.ii`, and
`erdos_385.variants.lb`. However, that snapshot's `APNOutputs/ErdosProblems`
and `NaturalLanguageProofs/ErdosProblems` contain no successful result for
#385. Therefore this is an attempt history, not a solved result. The C++
programs below investigate the quantity `F(n)-n` of parts (i) and (ii) only
over a finite range and prove none of these three conjectures.

```bash
g++ -O3 -std=c++17 problems/erdos-385/ep430_experiment.cpp -o /tmp/ep385
g++ -O3 -std=c++17 problems/erdos-385/ep430_segmented.cpp -o /tmp/ep385_segmented
```
