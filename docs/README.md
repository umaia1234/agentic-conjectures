**English** | [한국어](README.ko.md)

# Documentation

Repository entry points stay at the root, while research material lives next
to the code and certificates it explains. This index links the longer
repository-wide references and the problem-local mathematical details.

## Where things live

- [`README.md`](../README.md), [`AGENTS.md`](../AGENTS.md), and
  [`CONTRIBUTING.md`](../CONTRIBUTING.md) remain at the root for GitHub and
  agent discovery.
- `problems/<id>/` is the complete capsule for one problem: status, write-up,
  proofs, verification notes, source snapshots, code, and certificates.
- The [upstream source snapshot guide](upstream/README.md) documents shared
  preservation, restoration, and licensing policy. Its changing repository
  table is generated from [`sources.yaml`](upstream/sources.yaml).
- The [weekly highlights archive](HIGHLIGHTS.md) keeps every past week of
  the front page's rotating-curator ritual, generated from
  [`highlights.yaml`](highlights.yaml).

## Problem-local mathematical details

The following list is generated from artifacts tagged `mathematical-details`
in each problem's `status.yaml`. Edit the linked documents beside their
problem rather than assembling another global copy.

<!-- DETAILS:BEGIN (scripts/gen_readme.py) -->
| Problem | Claimed status | Mathematical details |
|---|---|---|
| [Erdős #385 / #430(i) — odd indices and exact verification through 10^9](../problems/erdos-385/README.md) | 🟡 partial | [Detailed derivation](../problems/erdos-385/DETAILS.md) |
| [Erdős #671 — everywhere-unbounded Lagrange arrays proved](../problems/erdos-671/README.md) | ✅ proved | [Detailed derivation](../problems/erdos-671/DETAILS.md) |
| [Let's Prove Goldbach prize problem 3 — literal finite-set representation proved](../problems/goldbach-prize-3/README.md) | ✅ proved | [Detailed derivation](../problems/goldbach-prize-3/DETAILS.md) |
| [Let's Prove Goldbach prize problem 4 — universal assertion refuted](../problems/goldbach-prize-4/README.md) | 🔴 refuted | [Detailed derivation](../problems/goldbach-prize-4/DETAILS.md) |
| [OEIS A000224 — R(n)(R(n)-1) divides n^2-1 iff n is an odd prime](../problems/oeis-a000224/README.md) | 🟡 partial | [Detailed derivation](../problems/oeis-a000224/DETAILS.md) |
| [OEIS A076141 — n occurs at most once in binary of n^2, checked to 2^40](../problems/oeis-a076141/README.md) | 🟡 partial | [Detailed derivation](../problems/oeis-a076141/DETAILS.md) |
| [OEIS A245211: a(n)=n only for n=21](../problems/oeis-a245211/README.md) | 🟡 partial | [Detailed derivation](../problems/oeis-a245211/DETAILS.md) |
| [OEIS A354747 first unknown case a(100943)](../problems/oeis-a354747/README.md) | 🔴 refuted | [Detailed derivation](../problems/oeis-a354747/DETAILS.md) |
| [OEIS A395412 certified finite nonvanishing extension](../problems/oeis-a395412/README.md) | 🟡 partial | [Detailed derivation](../problems/oeis-a395412/DETAILS.md) |
| [Graph recoloring radius — subdivided-claw counterexample](../problems/recoloring-radius-q15/README.md) | 🔴 refuted | [Detailed derivation](../problems/recoloring-radius-q15/DETAILS.md) |
<!-- DETAILS:END -->
