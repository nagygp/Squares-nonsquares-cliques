module

public import RequestProject.Main
public import RequestProject.Direct.Main

/-!
# The main theorem without the Carlitz–McConnel hypothesis

Replacing the use of the Carlitz–McConnel theorem by the self-contained proof
`Direct.goodPairing_eq_div_direct`, the theorem of Blokhuis, Seress and Wilbrink holds with no
extra hypothesis.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace CompleteExterior.Direct

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Theorem (Blokhuis–Seress–Wilbrink), unconditional.** Let `q = |F| ≡ 1 (mod 4)` and let `S`
be a set of `(q + 1) / 2` exterior points of the conic `x z = y²` in `PG(2, q)` such that every
line through two distinct points of `S` is a passant.  Then `S` is the set of exterior points on
some passant. -/
theorem complete_exterior_set_eq_exterior_points_of_passant'
    (hq : Fintype.card F % 4 = 1)
    (S : Finset (Point F)) (hcard : S.card = (Fintype.card F + 1) / 2)
    (hext : ∀ P ∈ S, IsExterior P)
    (hpass : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      ∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassant ℓ) :
    ∃ ℓ : Line F, IsPassant ℓ ∧ ∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ IsExterior P) := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hext' : ∀ P ∈ S, quadraticChar F (cf P.rep) = 1 := fun P hP =>
    (isExterior_iff hF P).1 (hext P hP)
  have hdisc : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → quadraticChar F (disc P.rep Q.rep) = -1 := by
    intro P hP Q hQ hPQ
    have hcf : cf P.rep ≠ 0 := by
      intro h; have := hext' P hP; rw [h] at this; simp at this
    exact disc_of_passant hF hPQ hcf (hpass P hP Q hQ hPQ)
  obtain ⟨u, hu, haniso, hS⟩ :=
    alg_core hF (pairingsLinear_of_card_mod_four hq) S hcard hext' hdisc
  refine ⟨mk F (polarVec u) (polarVec_ne_zero hF2 hu), ?_, ?_⟩
  · intro P hP hPc
    rw [incident_polar_iff hF2 P hu] at hP
    rw [onConic_iff] at hPc
    exact haniso P.rep P.rep_nonzero hP hPc
  · intro P
    rw [hS P, incident_polar_iff hF2 P hu, isExterior_iff hF P]

end CompleteExterior.Direct
