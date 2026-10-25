#!/usr/bin/env python3
"""Generate, or check, the Lean certificate modules CertX.lean and CertY.lean of oooooob-version-c.

Version C of "Generalizing OOOOOOB" (Danai, Ellis, Thanatipanonda, arXiv:2605.23213v1): a move
removes one token from one pile, or one token from each of two different piles.  Every position
reached from X = (2,2,2,2,2,2,3) or Y = (2,2,2,2,2,2,4) (counts of piles of sizes 1..7) has at
most 16 piles of sizes at most 7, so it is packed as

    key = sum over x = 1..7 of (number of piles of size x) * 32^(x - 1).

A move code is c = 8x + y: one token from a pile of size x (y = 0), or from a pile of size x and
a different pile of size y (x <= y).  This matches `cnt`, `legal`, `app` and `moveCodes` in
AgenticConjectures/OooooobVersionC/Checker.lean.

For a root P-position the generator builds a set S of P-positions with replies: for each y in S
and each legal move of y, in the order of the move codes, a reply move to a position in S or to
a position with all piles even (P by the paper's proposition on even piles).  The replies are
packed in base 64.  S starts from a greedy breadth-first construction and is then shrunk by
re-routing replies to positions many other replies already use, until it stops changing.  S is
written as a balanced binary search tree; its subtrees at a fixed depth are checked one per
`decide +kernel` theorem.  The outcomes come from this file's own memoized solver; the
independent solvers are oooc_counts.cpp and oooc_tuples.py.

usage:
  python3 gen_certificate.py --check   rebuild both modules and compare them with the committed
                                       files (exit 1 on any difference)
  python3 gen_certificate.py --write   rebuild both modules and overwrite the committed files
Standard library only; deterministic.
"""
import sys
import textwrap
from collections import Counter
from functools import lru_cache
from pathlib import Path

sys.setrecursionlimit(100000)

REPO = Path(__file__).resolve().parents[2]
OUT_DIR = REPO / "AgenticConjectures" / "OooooobVersionC"
CODES = [8 * x + y for x in range(1, 8) for y in [0] + list(range(x, 8))]


def wt(x):
    return 0 if x == 0 else 32 ** (x - 1)


def cnt(k, x):
    return k // 32 ** (x - 1) % 32


def legal(k, c):
    x, y = divmod(c, 8)
    if not 8 <= c < 64:
        return False
    if y == 0:
        return cnt(k, x) >= 1
    if x == y:
        return cnt(k, x) >= 2
    return cnt(k, x) >= 1 and cnt(k, y) >= 1


def app(k, c):
    x, y = divmod(c, 8)
    return k + wt(max(x - 1, 0)) + wt(max(y - 1, 0)) - wt(x) - wt(y)


def all_even(k):
    return all(cnt(k, x) == 0 for x in (1, 3, 5, 7))


def pack(counts):
    return sum(c * 32 ** i for i, c in enumerate(counts))


@lru_cache(maxsize=None)
def options(k):
    """(code, packed option) for every legal move, in code order."""
    return tuple((c, app(k, c)) for c in CODES if legal(k, c))


@lru_cache(maxsize=None)
def is_p(k):
    return all(not is_p(z) for _, z in options(k))


def tokens(k):
    return sum(x * cnt(k, x) for x in range(1, 8))


def piles(k):
    return sum(cnt(k, x) for x in range(1, 8))


# order in which the greedy construction prefers new members of S
ORDERS = {"max-tokens": lambda v: (-tokens(v), v), "fewest-piles": lambda v: (piles(v), v)}


def p_replies(z):
    """Reply moves from z to P-positions, as (code, target)."""
    return [(r, v) for r, v in options(z) if is_p(v)]


def greedy(root, order):
    members, queue = {root}, [root]
    for y in queue:
        for _, z in options(y):
            cands = p_replies(z)
            if any(all_even(v) for _, v in cands):
                continue
            if any(v in members for _, v in cands):
                continue
            v = min((v for _, v in cands), key=order)
            members.add(v)
            queue.append(v)
    return members


def closure(root, choose):
    """The members reached from root when every option z is answered by choose(z)."""
    members, stack = {root}, [root]
    while stack:
        y = stack.pop()
        for _, z in options(y):
            r, v = choose(z)
            if not all_even(v) and v not in members:
                members.add(v)
                stack.append(v)
    return members


def chooser(members):
    """Reply rule: an all-even target if any, else the member of `members` that the most replies
    could use, else the target with the fewest moves."""
    popular = Counter()
    for y in members:
        for _, z in options(y):
            for _, v in options(z):
                if v in members:
                    popular[v] += 1

    def choose(z):
        cands = p_replies(z)
        even = [(r, v) for r, v in cands if all_even(v)]
        if even:
            return even[0]
        inside = [(r, v) for r, v in cands if v in members]
        if inside:
            return max(inside, key=lambda rv: (popular[rv[1]], -len(options(rv[1])), -rv[1]))
        return min(cands, key=lambda rv: (len(options(rv[1])), rv[1]))

    return choose


def certificate(root, order):
    """S as {packed position: list of reply codes in the order of its legal moves}."""
    assert is_p(root)
    members = greedy(root, order)
    for _ in range(50):
        choose = chooser(members)
        new = closure(root, choose)
        if new == members:
            break
        members = new
    else:
        raise RuntimeError("shrinking did not converge")
    cert = {}
    for y in sorted(members):
        reps = []
        for _, z in options(y):
            r, v = choose(z)
            assert legal(z, r) and is_p(v) and (all_even(v) or v in members)
            reps.append(r)
        cert[y] = reps
    return cert


def pack_replies(reps):
    out = 0
    for r in reversed(reps):
        out = out * 64 + r
    return out


def wrap(tokens_, indent="  ", width=100):
    lines, cur = [], indent
    for tok in tokens_:
        if len(cur) + len(tok) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += tok + " "
    if cur.strip():
        lines.append(cur.rstrip())
    return "\n".join(lines)


def tree_tokens(keys, cert, lo, hi, out):
    if lo >= hi:
        out.append(".leaf")
        return
    mid = (lo + hi) // 2
    out.append("(.node")
    tree_tokens(keys, cert, lo, mid, out)
    out.append(str(keys[mid]))
    out.append(str(pack_replies(cert[keys[mid]])))
    tree_tokens(keys, cert, mid + 1, hi, out)
    out[-1] += ")"


def module(name, title, root, root_doc, cert, depth):
    keys = sorted(cert)
    chunks = []

    def skeleton(lo, hi, d):
        if lo >= hi:
            return ".leaf"
        if d == depth:
            chunks.append((lo, hi))
            return f"{name}_{len(chunks) - 1}"
        mid = (lo + hi) // 2
        k = keys[mid]
        left = skeleton(lo, mid, d + 1)
        right = skeleton(mid + 1, hi, d + 1)
        return f"(.node {left} {k} {pack_replies(cert[k])} {right})"

    def proof(lo, hi, d, out):
        if lo >= hi:
            out.append("rfl")
        elif d == depth:
            out.append(f"{name}_ok_{chunks.index((lo, hi))}")
        else:
            mid = (lo + hi) // 2
            out.append("(allOk_node (by decide +kernel)")
            proof(lo, mid, d + 1, out)
            proof(mid + 1, hi, d + 1, out)
            out[-1] += ")"

    top = skeleton(0, len(keys), 0)
    top_proof = []
    proof(0, len(keys), 0, top_proof)
    checks = sum(len(v) for v in cert.values())
    about = textwrap.fill(
        f"`{name}` is a set of {len(keys)} packed P-positions of Version C, among them {root_doc}, "
        f"packed as `{root}`. For each of its positions it stores a reply to every legal move "
        f"({checks} replies in all), leading back into `{name}` or to a position whose piles all "
        f"have even size. `{name}_ok` checks every reply with `decide +kernel`, one subtree at a "
        f"time.", width=100)
    out = [f"""import AgenticConjectures.OooooobVersionC.Checker

/-!
# OOOOOOB Version C — certificate for {title}

Generated by `problems/oooooob-version-c/gen_certificate.py`; do not edit by hand
(`python3 gen_certificate.py --check` regenerates it and compares).

{about}
-/

namespace AgenticConjectures.OooooobVersionC

noncomputable section
"""]
    for i, (lo, hi) in enumerate(chunks):
        toks = []
        tree_tokens(keys, cert, lo, hi, toks)
        out.append(f"/-- Part {i} of `{name}`. -/\ndef {name}_{i} : Tree :=\n{wrap(toks)}\n")
    out.append(f"/-- The certificate tree; its subtrees at depth {depth} are `{name}_0`, ... -/\n"
               f"def {name} : Tree :=\n{wrap(top.split(' '))}\n")
    for i in range(len(chunks)):
        out.append(f"theorem {name}_ok_{i} : allOk {name} {name}_{i} = true := by decide +kernel\n")
    out.append(f"/-- Every node of `{name}` passes `checkMoves` against `{name}`. -/\n"
               f"theorem {name}_ok : allOk {name} {name} = true :=\n"
               f"{wrap(top_proof)}\n")
    out.append(f"/-- {root_doc[0].upper() + root_doc[1:]} is a key of `{name}`. -/\n"
               f"theorem {name}_mem : {name}.mem {root} = true := by decide +kernel\n")
    out.append("end\n\nend AgenticConjectures.OooooobVersionC\n")
    return "\n".join(out), len(keys), checks


def build():
    x = pack((2, 2, 2, 2, 2, 2, 3))
    y = pack((2, 2, 2, 2, 2, 2, 4))
    x0 = app(x, 9)  # one token from each of the two piles of size 1
    assert x0 == pack((0, 2, 2, 2, 2, 2, 3))
    assert not is_p(x) and is_p(x0) and is_p(y)
    cert_x = certificate(x0, ORDERS["max-tokens"])
    cert_y = certificate(y, ORDERS["fewest-piles"])
    mx = module("certX", "X = (2,2,2,2,2,2,3)", x0,
                "the position (0,2,2,2,2,2,3) reached from X by one move", cert_x, 3)
    my = module("certY", "Y = (2,2,2,2,2,2,4)", y, "the position Y = (2,2,2,2,2,2,4)", cert_y, 4)
    return {"CertX.lean": mx, "CertY.lean": my}


def main(argv):
    if len(argv) != 2 or argv[1] not in ("--check", "--write"):
        print(__doc__)
        return 2
    ok = True
    for fname, (text, n, checks) in build().items():
        path = OUT_DIR / fname
        print(f"{fname}: {n} positions, {checks} replies, {len(text)} characters")
        if argv[1] == "--write":
            path.write_text(text, encoding="utf-8")
        elif not path.exists() or path.read_text(encoding="utf-8") != text:
            print(f"MISMATCH: {path.relative_to(REPO)} differs from the regenerated text")
            ok = False
    if argv[1] == "--check":
        print("OK: both certificate modules match" if ok else "certificate check FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
