module

public import RequestProject.Geometry
public import RequestProject.Converse
public import RequestProject.Example

/-!
# Characterization of complete exterior sets of conics

A formalization of

  A. Blokhuis, Á. Seress, H. A. Wilbrink,
  *Characterization of complete exterior sets of conics*, Combinatorica 12 (2) (1992) 143–147.

**Theorem.** Let `𝒮` be a set of `(q + 1) / 2` exterior points of a nondegenerate conic `𝒞` in
the Desarguesian plane `PG(2, q)`, `q ≡ 1 (mod 4)`, with the property that the line joining any
two points of `𝒮` misses the conic.  Then `𝒮` consists of the exterior points on a passant.

As in the paper, the conic is `x z = y²` (every nondegenerate conic is projectively equivalent to
it), and the proof relies on the theorem of Carlitz and McConnel, which the paper quotes without
proof; it enters as the explicit hypothesis `CarlitzMcConnel F`.

The file structure is:
* `Defs`        — the projective plane, the conic, tangents, passants, exterior points, and the
                  statement of the Carlitz–McConnel theorem;
* `Paley`, `Core` — character sums and the Paley-graph parity argument ("extra property");
* `Involution`  — use of the Carlitz–McConnel theorem to show `φ(x) = n / x`;
* `Algebra`, `Normalized`, `Reflection` — the translation into quadratic-form language, the
                  labelling of exterior points by pairs of points of the conic, and the reduction
                  (by an isometry) to a set containing the point with labels `(0, ∞)`;
* `Geometry`    — the dictionary between geometry and the quadratic form;
* `Converse`    — the exterior points on a passant do form a complete exterior set;
* `Example`     — for `q = 7` there is a complete exterior set not on a passant, so the
                  hypothesis `q ≡ 1 (mod 4)` cannot be dropped.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Theorem (Blokhuis–Seress–Wilbrink).** Let `q = |F| ≡ 1 (mod 4)` and let `S` be a set of
`(q + 1) / 2` exterior points of the conic `x z = y²` in `PG(2, q)` such that every line through
two distinct points of `S` is a passant.  Then there is a passant `ℓ` such that `S` is exactly
the set of exterior points on `ℓ`.

The theorem of Carlitz and McConnel, used (but not proved) in the paper, is assumed as the
hypothesis `hCM`. -/
theorem complete_exterior_set_eq_exterior_points_of_passant
    (hq : Fintype.card F % 4 = 1) (hCM : CarlitzMcConnel F)
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
    alg_core hF (fun _ hψ => goodPairing_eq_div hq hCM hψ) S hcard hext' hdisc
  refine ⟨mk F (polarVec u) (polarVec_ne_zero hF2 hu), ?_, ?_⟩
  · intro P hP hPc
    rw [incident_polar_iff hF2 P hu] at hP
    rw [onConic_iff] at hPc
    exact haniso P.rep P.rep_nonzero hP hPc
  · intro P
    rw [hS P, incident_polar_iff hF2 P hu, isExterior_iff hF P]

/-- **Characterization.**  For `q ≡ 1 (mod 4)` (and assuming the theorem of Carlitz–McConnel),
a set `S` of points of `PG(2, q)` is a complete exterior set of the conic `x z = y²` — i.e. it
consists of `(q + 1) / 2` exterior points, any two of which are joined only by passants — if and
only if `S` is the set of exterior points on some passant. -/
theorem complete_exterior_set_iff (hq : Fintype.card F % 4 = 1) (hCM : CarlitzMcConnel F)
    (S : Finset (Point F)) :
    (S.card = (Fintype.card F + 1) / 2 ∧ (∀ P ∈ S, IsExterior P) ∧
      ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassant ℓ) ↔
    ∃ ℓ : Line F, IsPassant ℓ ∧ ∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ IsExterior P) := by
  constructor
  · rintro ⟨hcard, hext, hpass⟩
    exact complete_exterior_set_eq_exterior_points_of_passant hq hCM S hcard hext hpass
  · rintro ⟨ℓ, hℓ, hS⟩
    obtain ⟨T, hT, hTcard, hTpass⟩ :=
      exterior_points_of_passant (ringChar_ne_two_of_card_mod_four hq) hℓ
    have hST : S = T := by
      ext P; rw [hS, hT]
    subst hST
    exact ⟨hTcard, fun P hP => ((hS P).1 hP).2, hTpass⟩

end CompleteExterior
