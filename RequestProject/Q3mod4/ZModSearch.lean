module

public import RequestProject.Q3mod4.PairSearch

/-!
# Running the pair search over `ZMod p`

Computable data (a table of squares and the lists of non-zero squares and of non-squares) for
the prime field `ZMod p`, and the reduction `pairingsLinear_zmod`, which turns three finite
checks (evaluated by `native_decide` for each concrete `p`, with the table of squares
`t := sqTab p` stored as a top-level constant so that it is computed only once) into
`PairingsLinear (ZMod p)`.
-/

@[expose] public section

namespace CompleteExterior

variable (p : ℕ) [Fact p.Prime]

/-- The elements of `ZMod p`. -/
def zEls : List (ZMod p) := List.map (Nat.cast : ℕ → ZMod p) (List.range p)

/-- Table of squares modulo `p`: entry `i` is `true` iff `i` is a square mod `p`. -/
def sqTab : Array Bool :=
  ((List.range p).map fun i => (List.range p).any fun r => r * r % p == i).toArray

/-- Squareness test in `ZMod p` via a table `t` (intended to be `sqTab p`). -/
def zSq (t : Array Bool) (x : ZMod p) : Bool := t[x.val]!

/-- Table of inverses modulo `p` (entry `0` is `0`). -/
def invTab : Array ℕ :=
  (List.range p).map (fun i => ((List.range p).find? fun j => i * j % p == 1).getD 0) |>.toArray

/-- Inversion in `ZMod p` via a table `it` (intended to be `invTab p`). -/
def zInv (it : Array ℕ) (x : ZMod p) : ZMod p := (it[x.val]! : ℕ)

/-- The non-zero squares of `ZMod p` other than `1`. -/
def zSqs (t : Array Bool) : List (ZMod p) :=
  (zEls p).filter fun x => x != 0 && x != 1 && zSq p t x

/-- The non-squares of `ZMod p`. -/
def zNs (t : Array Bool) : List (ZMod p) := (zEls p).filter fun x => !zSq p t x

lemma mem_zEls (x : ZMod p) : x ∈ zEls p :=
  List.mem_map.2 ⟨x.val, List.mem_range.2 (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

/-- **Reduction for prime fields**: three finite checks imply that every good pairing of
`GF(p)*` is linear. -/
theorem pairingsLinear_zmod (t : Array Bool) (it : Array ℕ)
    (hspec : ∀ x : ZMod p, zSq p t x = decide (∃ r : ZMod p, x = r * r))
    (hinv : ∀ x : ZMod p, x ≠ 0 → x * zInv p it x = 1)
    (hnd : (zSqs p t).Nodup)
    (h : (zNs p t).all (fun m =>
      pairSearch (fun x => !zSq p t x) (ratioOK ZMod.val (zInv p it) m) (zNs p t) (zSqs p t)
        [(1, m)]) = true) :
    PairingsLinear (ZMod p) := by
  have hsq : ∀ x, zSq p t x = true ↔ IsSquare x := by
    intro x; rw [hspec x, decide_eq_true_iff]; rfl
  refine pairingsLinear_of_search (zSq p t) hsq ZMod.val (zInv p it) hinv (zSqs p t) (zNs p t)
    ?_ hnd ?_ h
  · intro x
    simp only [zSqs, List.mem_filter, mem_zEls, true_and, Bool.and_eq_true, bne_iff_ne, ne_eq,
      hsq, and_assoc]
  · intro x hx
    simp only [zNs, List.mem_filter, mem_zEls, true_and, Bool.not_eq_true', Bool.eq_false_iff,
      ne_eq, hsq]
    exact hx

end CompleteExterior
