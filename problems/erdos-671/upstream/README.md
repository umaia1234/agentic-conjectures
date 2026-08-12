**English** | [한국어](README.ko.md)

# Public Erdős #671 solution source

This directory records the exact public source used to reproduce the complete
Lean proof of Erdős Problem #671.

## Provenance

- Canonical problem: [Erdős Problem #671](https://www.erdosproblems.com/671)
- Public solution post: [discussion thread](https://www.erdosproblems.com/forum/thread/671#post-7142), posted 2026-06-22
- Public proof write-up: [Overleaf read link](https://www.overleaf.com/read/gqmfrhsprtqm#59ac11)
- Public Lean source: Lean web-editor payload linked directly by that post
- Retrieved: 2026-08-12
- Local exact payload: [Erdos671.public.lean](Erdos671.public.lean)
- Machine-checkable manifest: [SHA256SUMS](SHA256SUMS)
- SHA-256: `3854ae85aca322b5ad2c65fb9c7bae5ca19ed939ceca99521365d8690b8d8923`
- Central declaration: `Erdos671.erdos_671`

The discussion post attributes the argument to “GPT Pro” and the Lean
formalization to “Codex”. It gives no exact model or harness names; this
repository deliberately leaves those fields `unspecified` rather than
guessing.

## Retrieval

The post's Lean link stores the source in its `#codez=` fragment using
LZ-String's Base64 codec. The exact file can be recovered by extracting that
fragment, URL-decoding it, and applying `decompressFromBase64`. The local
snapshot is the decoded payload byte-for-byte after UTF-8 encoding.

From the problem directory, verify that snapshot with
`(cd upstream && sha256sum -c SHA256SUMS)`.

## Relation to the checked module

The checked module at
[`AgenticConjectures/Erdos671.lean`](../../../AgenticConjectures/Erdos671.lean)
preserves the proof body. It adds repository provenance, changes the namespace
to `AgenticConjectures.Erdos671`, and factors the final proposition into
`statement` plus `erdos_671 : statement`. These integration changes do not
alter the mathematical construction or proof.

## License and use

The public web-editor payload did not include a copyright or license header.
It is retained here for research verification and source attribution. The
repository makes no claim to authorship or novelty of the copied proof and
does not submit it to any external venue.
