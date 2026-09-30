module

public import RequestProject.Core

/-!
# The directed Paley-tournament reduction

For `q ≡ 3 (mod 4)`, negation reverses quadratic character.  Thus a good pairing
induces a permutation of the non-zero squares by `s ↦ -ψ s`.  This file records the
exact two-sign decomposition supplied by the `GoodPairing.pair` axiom.  It isolates
the additional local-orientation assertion needed for a directed-Paley approach;
that assertion is not implied by `GoodPairing` alone.
-/

@[expose] public section

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- For `q ≡ 3 (mod 4)`, `-1` is a non-square. -/
lemma quadraticChar_neg_one_eq_neg_one (hq : Fintype.card F % 4 = 3) :
    quadraticChar F (-1) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare]
  intro h
  have := FiniteField.isSquare_neg_one_iff.mp h
  omega

/-- For `q ≡ 3 (mod 4)`, negation reverses quadratic character. -/
lemma quadraticChar_neg_of_card_mod_four_eq_three (hq : Fintype.card F % 4 = 3) (x : F) :
    quadraticChar F (-x) = -quadraticChar F x := by
  rw [neg_eq_neg_one_mul, map_mul, quadraticChar_neg_one_eq_neg_one hq, neg_one_mul]

/-- The map on non-zero squares induced by a good pairing in the directed Paley tournament. -/
def GoodPairing.tournamentMap (ψ : F → F) (s : F) : F := -ψ s

namespace GoodPairing

variable {ψ : F → F}

/-- The induced tournament map sends non-zero squares to non-zero squares. -/
lemma tournamentMap_square (hq : Fintype.card F % 4 = 3) (hψ : GoodPairing ψ) {s : F}
    (hs : quadraticChar F s = 1) :
    quadraticChar F (tournamentMap ψ s) = 1 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hs
    norm_num at hs
  rw [tournamentMap, quadraticChar_neg_of_card_mod_four_eq_three hq, hψ.chi_apply hs0, hs]
  norm_num

/-- The induced tournament map is injective on non-zero squares. -/
lemma tournamentMap_inj (hψ : GoodPairing ψ) {s t : F} (hs : quadraticChar F s = 1)
    (ht : quadraticChar F t = 1) (h : tournamentMap ψ s = tournamentMap ψ t) : s = t := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, quadraticChar_zero] at hs
    norm_num at hs
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, quadraticChar_zero] at ht
    norm_num at ht
  apply hψ.inj hs0 ht0
  simpa [tournamentMap] using congrArg Neg.neg h

/-- The factor comparing the original square arguments and their paired arguments. -/
def directFactor (ψ : F → F) (s t : F) : F := (s - t) * (ψ s - ψ t)

/-- The factor formed from the two cross differences. -/
def crossFactor (ψ : F → F) (s t : F) : F := (s - ψ t) * (ψ s - t)

/-- `GoodPairing.pair` says that the direct and cross factors have opposite characters. -/
lemma direct_cross_nonsquare (hψ : GoodPairing ψ) {s t : F} (hs : quadraticChar F s = 1)
    (ht : quadraticChar F t = 1) (hst : s ≠ t) :
    quadraticChar F (directFactor ψ s t * crossFactor ψ s t) = -1 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hs
    norm_num at hs
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at ht
    norm_num at ht
  have htψ : t ≠ ψ s := by
    intro h
    have := hψ.chi_apply hs0
    rw [← h, ht, hs] at this
    norm_num at this
  rw [show directFactor ψ s t * crossFactor ψ s t =
    (s - t) * (s - ψ t) * (ψ s - t) * (ψ s - ψ t) by
      simp only [directFactor, crossFactor]
      ring]
  exact hψ.pair s t hs0 ht0 (Ne.symm hst) htψ

/-- The direct factor is the negation of the directed-Paley orientation product. -/
lemma directFactor_eq_neg_orientationProduct (ψ : F → F) (s t : F) :
    directFactor ψ s t = -((s - t) * (tournamentMap ψ s - tournamentMap ψ t)) := by
  simp only [directFactor, tournamentMap]
  ring

/-- Local orientation preservation is exactly the branch where the direct factor is a non-square. -/
lemma local_orientation_iff_direct_nonsquare (hq : Fintype.card F % 4 = 3) (ψ : F → F)
    (s t : F) :
    quadraticChar F ((s - t) * (tournamentMap ψ s - tournamentMap ψ t)) = 1 ↔
      quadraticChar F (directFactor ψ s t) = -1 := by
  rw [directFactor_eq_neg_orientationProduct, quadraticChar_neg_of_card_mod_four_eq_three hq]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    simpa using congrArg Neg.neg h

/-- For a good pairing, the cross-factor square branch is equivalent to local orientation
preservation.  Proving that this branch always occurs is the missing directed-Paley rigidity
step; it is not a consequence of the current `GoodPairing` axioms. -/
lemma local_orientation_iff_cross_square (hq : Fintype.card F % 4 = 3) (hψ : GoodPairing ψ)
    {s t : F} (hs : quadraticChar F s = 1) (ht : quadraticChar F t = 1) (hst : s ≠ t) :
    quadraticChar F ((s - t) * (tournamentMap ψ s - tournamentMap ψ t)) = 1 ↔
      quadraticChar F (crossFactor ψ s t) = 1 := by
  rw [local_orientation_iff_direct_nonsquare hq]
  constructor
  · intro hdirect
    have h := hψ.direct_cross_nonsquare hs ht hst
    rw [map_mul, hdirect] at h
    norm_num at h ⊢
    exact h
  · intro hcross
    have h := hψ.direct_cross_nonsquare hs ht hst
    rw [map_mul, hcross] at h
    norm_num at h ⊢
    exact h

end GoodPairing

end CompleteExterior
