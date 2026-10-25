/-!
# OOOOOOB Version C — the kernel checker for the certificates

This module has no imports: it only defines the functions that `decide +kernel` evaluates on the
certificate data in `CertX` and `CertY`. What they mean for the game, and why a certificate that
passes them proves an outcome, is in `AgenticConjectures.OooooobVersionC`.

* A *packed position* is a natural number `k` whose base-32 digit `x - 1` is the number of piles of
  size `x`, for `1 ≤ x ≤ 7` (`cnt k x`). A pile of size `x ≥ 1` adds `wt x = 32 ^ (x - 1)`.
* A *move code* is `c = 8 * x + y` with `1 ≤ x ≤ 7`. If `y = 0`, it removes one token from a pile
  of size `x`. Otherwise `x ≤ y ≤ 7`, and it removes one token from a pile of size `x` and one from
  a different pile of size `y`. `legal k c` says the move can be made in `k`, and `app k c` is the
  packed position after it. `moveCodes` lists the 35 codes.
* A certificate is a binary search tree of packed positions (`Tree`). The node of a position `y`
  stores in `reps`, in base 64, one reply code for each legal move of `y`, in the order of
  `moveCodes`. `allOk root t` checks every node of `t`: after each legal move, the stored reply is
  legal and leads to a position with no pile of odd size (`allEven`) or to a key of `root`.

Everything is written with recursors, `Bool.rec` (through `pick`) and the `Nat` primitives that
the kernel evaluates with GMP, because `if`, `cond`, `match` and the arithmetic notation unfold
through several definitions in the kernel. On the certificate of `CertX` this made
`decide +kernel` about 2.6 times faster than the same functions written with `if`.
-/

namespace AgenticConjectures.OooooobVersionC

noncomputable section

/-- `pick b t e` is `if b then t else e`, written with the recursor of `Bool`. -/
abbrev pick {α : Sort _} (b : Bool) (t e : α) : α := Bool.rec (motive := fun _ => α) e t b

/-- The number of piles of size `x` in the packed position `k`: its base-32 digit `x - 1`. -/
def cnt (k x : Nat) : Nat := Nat.mod (Nat.div k (Nat.pow 32 (Nat.sub x 1))) 32

/-- The weight of one pile of size `x` in a packed position. Piles of size 0 weigh nothing. -/
def wt (x : Nat) : Nat := pick (Nat.beq x 0) 0 (Nat.pow 32 (Nat.sub x 1))

/-- The move with code `c = 8 * x + y` can be made in the packed position `k`. -/
def legal (k c : Nat) : Bool :=
  pick (Nat.ble 8 c) (pick (Nat.ble 64 c) false
    (pick (Nat.beq (Nat.mod c 8) 0) (Nat.ble 1 (cnt k (Nat.div c 8)))
      (pick (Nat.beq (Nat.div c 8) (Nat.mod c 8)) (Nat.ble 2 (cnt k (Nat.div c 8)))
        (pick (Nat.ble 1 (cnt k (Nat.div c 8))) (Nat.ble 1 (cnt k (Nat.mod c 8))) false))))
    false

/-- The packed position after the move with code `c = 8 * x + y`: the removed piles of sizes `x`
and `y` come back with sizes `x - 1` and `y - 1` (`wt 0 = 0`, so `y = 0` changes nothing). -/
def app (k c : Nat) : Nat :=
  Nat.sub (Nat.sub (Nat.add (Nat.add k (wt (Nat.sub (Nat.div c 8) 1)))
    (wt (Nat.sub (Nat.mod c 8) 1))) (wt (Nat.div c 8))) (wt (Nat.mod c 8))

/-- The packed position `k` has no pile of size 1, 3, 5 or 7. -/
def allEven (k : Nat) : Bool :=
  pick (Nat.beq (cnt k 1) 0) (pick (Nat.beq (cnt k 3) 0)
    (pick (Nat.beq (cnt k 5) 0) (Nat.beq (cnt k 7) 0) false) false) false

/-- The 35 move codes `8 * x` and `8 * x + y` with `1 ≤ x ≤ y ≤ 7`, in increasing order. -/
def moveCodes : List Nat :=
  [8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 31, 32, 36,
    37, 38, 39, 40, 45, 46, 47, 48, 54, 55, 56, 63]

/-- A binary search tree of packed positions; `reps` holds the replies of the node's position. -/
inductive Tree where
  | leaf : Tree
  | node (l : Tree) (key reps : Nat) (r : Tree) : Tree

/-- `t.mem k`: the packed position `k` is a key of the search tree `t`. -/
def Tree.mem (t : Tree) : Nat → Bool :=
  Tree.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ key _ _ ihl ihr k => pick (Nat.beq k key) true (pick (Nat.ble key k) (ihr k) (ihl k))) t

/-- `checkMoves root y ms R`: for every code `m` of `ms` that is legal in `y`, the next base-64
digit of `R` is a reply legal after `m` that leads to an all-even position or to a key of
`root`. -/
def checkMoves (root : Tree) (y : Nat) (ms : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun m _ ih R =>
      pick (legal y m)
        (pick (legal (app y m) (Nat.mod R 64))
          (pick (pick (allEven (app (app y m) (Nat.mod R 64))) true
              (root.mem (app (app y m) (Nat.mod R 64))))
            (ih (Nat.div R 64)) false) false)
        (ih R)) ms

/-- Every node of `t` passes `checkMoves` against the whole certificate `root`. -/
def allOk (root : Tree) (t : Tree) : Bool :=
  Tree.rec (motive := fun _ => Bool) true
    (fun _ key reps _ ihl ihr =>
      pick (checkMoves root key moveCodes reps) (pick ihl ihr false) false) t

/-- Assembles `allOk` for a node from its parts; the generated certificates use it for the top of
the tree, whose subtrees are checked one by one. -/
theorem allOk_node {root l r : Tree} {key reps : Nat}
    (h : checkMoves root key moveCodes reps = true) (hl : allOk root l = true)
    (hr : allOk root r = true) : allOk root (.node l key reps r) = true := by
  show pick (checkMoves root key moveCodes reps) (pick (allOk root l) (allOk root r) false)
    false = true
  rw [h, hl, hr]

end

end AgenticConjectures.OooooobVersionC
