**English** | [한국어](UPSTREAM_SOURCES.ko.md)

# Upstream source snapshots

The full clones of external repositories used for investigation in this
workspace were deleted after the per-problem cleanup. The Lean sources
directly corresponding to each current problem are preserved in that
problem's `upstream/` directory, and AlphaProof Nexus records that had no
corresponding successful result were reduced to facts and scope in the
problem's `README.md`.

## Pinned repository states

| Repository | Commit | Purpose at the time |
|---|---|---|
| [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) | [`9118d083ffca1536f521f9a7d103201f537ea670`](https://github.com/google-deepmind/formal-conjectures/tree/9118d083ffca1536f521f9a7d103201f537ea670) | `main` as of 2026-08-11; canonical sources of the manually formalized OEIS/Erdős/WOWII/other statements |
| [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) | [`67338a157bbb8d87e9a349d662f82a868bda6327`](https://github.com/google-deepmind/formal-conjectures/tree/67338a157bbb8d87e9a349d662f82a868bda6327) | `auto_oeis` working snapshot; auto-formalized OEIS sources |
| [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) | [`7a41db3d761324599812d6ca6cb6a9f311046dc7`](https://github.com/google-deepmind/formal-conjectures/tree/7a41db3d761324599812d6ca6cb6a9f311046dc7) | Snapshot at which the FormalBench candidate set was checked |
| [AlphaProof Nexus Results](https://github.com/google-deepmind/alphaproof-nexus-results) | [`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88) | Audit of the intersection between public success results and attempt lists |

All four worktrees had an empty `git status --short` immediately before
deletion. `formal-auto-oeis` and `formal-bench` were detached linked
worktrees of the first repository; the other two were independent clones.

## Preservation scope

- Corresponding Lean files keep their original basenames, copyright headers,
  and exact bytes.
- Each `upstream/README.md` records the original path, pinned commit URL,
  SHA-256, central declaration, and the relationship to the current problem's
  results.
- These files are **formalization snapshots** of the original conjectures.
  Declarations containing `sorry` must not be read as formal proofs.
- The Formal Conjectures-specific imports and auxiliary definitions were not
  re-vendored in full, so a local Lean file alone usually does not compile.
  If a build is needed, restore the original repository at the corresponding
  commit as shown below.
- The thousands of formalizations unrelated to the current 35 problems, the
  `.git` objects, `.lake` caches, site sources, and CI configuration were not
  copied into the problem directories.

## Restoring the original repositories

```bash
git clone https://github.com/google-deepmind/formal-conjectures.git /tmp/formal-conjectures
git -C /tmp/formal-conjectures fetch origin 9118d083ffca1536f521f9a7d103201f537ea670
git -C /tmp/formal-conjectures checkout 9118d083ffca1536f521f9a7d103201f537ea670

git clone https://github.com/google-deepmind/alphaproof-nexus-results.git /tmp/alphaproof-nexus-results
git -C /tmp/alphaproof-nexus-results checkout 0647711a71183c1ea492ad60860776617ce1ea88
```

The other two Formal Conjectures snapshots can be restored from the same
clone by fetching and checking out the corresponding commits.

## Licenses and third-party sources

The copied Formal Conjectures Lean sources keep the original Apache-2.0
copyright headers. The [full Apache-2.0 text](THIRD_PARTY_LICENSES/Apache-2.0.txt)
is preserved alongside, and the
[upstream AUTHORS](THIRD_PARTY_LICENSES/Formal-Conjectures-AUTHORS.txt) file
was copied from the same snapshot. The original repository distributes other
material under CC BY 4.0 and notes that material originating from OEIS,
Wikipedia, or MathOverflow may carry the original sources' terms, such as
CC BY-SA 4.0. This is why each problem keeps both the canonical source link
and the pinned upstream link.
