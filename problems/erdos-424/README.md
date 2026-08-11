**English** | [한국어](README.ko.md)

# Erdős problem #424

This is an exact finite experiment that generates the set of generated
integers in ascending order from distinct previously generated integers
\(x,y\) with \(n+1=xy\), and probes for omissions in each residue class.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the exact Lean
statement asking for positive density. Green's open problem 63 is merely an
alias pointing to the same statement, and the finite search below does not
prove positive density.

```bash
g++ -O3 -std=c++17 problems/erdos-424/erdos424_probe.cpp -o /tmp/erdos424_probe
/tmp/erdos424_probe 1000000 500
```
