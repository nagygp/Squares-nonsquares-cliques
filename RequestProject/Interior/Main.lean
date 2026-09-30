module

public import RequestProject.Interior.Q29
public import RequestProject.Interior.Q17
public import RequestProject.Interior.Counterexamples
public import RequestProject.Interior.Converse

/-!
# Sets of interior points of a conic pairwise joined by passants

**Claim.** Let `S` be a set of interior points of the conic `𝒞 : x y = z²` in `PG(2, q)` such
that every line through two points of `S` is an external line (passant) of `𝒞`.  If
`q ≡ 1 (mod 4)`, `q ≥ 27` and `|S| = (q + 1) / 2`, then `S` is the set of interior points on some
passant.

What is established here:
* `interior_set_eq_interior_points_of_passant` — the general statement; its proof is **open**
  (it is left as `sorry`);
* `interior_set_eq_interior_points_of_passant_29` — the case `q = 29`, proved by a verified
  exhaustive search (`Q29`);
* `interior_set_eq_interior_points_of_passant_card_27` — the case `q = 27`: since
  `27 ≡ 3 (mod 4)`, the hypotheses can never be met, so the statement holds vacuously;
  `not_interiorStatement_27` shows that the conclusion *does* fail for `q = 27` once the
  hypothesis `q ≡ 1 (mod 4)` is dropped;
* `interior_points_of_passant` (`Converse`) — for every odd `q`, the interior points on a
  passant do form such a set, so for `q = 29` we get the full characterization
  `interior_set_iff_29`;
* additional data: the conclusion holds for `q = 17` (`Q17`) but fails for `q = 5, 13, 25`
  (`Counterexamples`), so the bound `q ≥ 27` cannot be lowered to `q ≥ 17`.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace InteriorPassant

open CompleteExterior

variable {F : Type*} [Field F] [Fintype F]

/-- **The requested theorem** (general `q`).  Let `q = |F| ≡ 1 (mod 4)`, `q ≥ 27`, and let `S` be
a set of `(q + 1) / 2` interior points of the conic `x y = z²` in `PG(2, q)` such that every line
through two distinct points of `S` is a passant.  Then there is a passant `ℓ` such that `S` is
exactly the set of interior points on `ℓ`.

The proof for general `q` is not available: this statement is left open (`sorry`).  It is
verified for `q = 29` below (and for `q = 17`), and it holds vacuously for `q = 27`. -/
theorem interior_set_eq_interior_points_of_passant
    (hq : Fintype.card F % 4 = 1) (hq27 : 27 ≤ Fintype.card F)
    (S : Finset (Point F)) (hcard : S.card = (Fintype.card F + 1) / 2)
    (hint : ∀ P ∈ S, IsInteriorXY P)
    (hpass : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      ∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassantXY ℓ) :
    ∃ ℓ : Line F, IsPassantXY ℓ ∧ ∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ IsInteriorXY P) := by
  sorry

/-- **The case `q = 27`** of the requested theorem: it holds vacuously, because
`27 ≢ 1 (mod 4)`.  (See `not_interiorStatement_27`: without the congruence condition the
conclusion fails for `q = 27`.) -/
theorem interior_set_eq_interior_points_of_passant_card_27 (h27 : Fintype.card F = 27) :
    Fintype.card F % 4 = 1 → 27 ≤ Fintype.card F → InteriorStatement F := by
  intro hq
  rw [h27] at hq; norm_num at hq

/-- **Characterization for `q = 29`.**  A set `S` of points of `PG(2, 29)` consists of `15`
interior points of `x y = z²`, any two of which are joined only by passants, if and only if `S`
is the set of interior points on some passant. -/
theorem interior_set_iff_29 (S : Finset (Point (ZMod 29))) :
    (S.card = (Fintype.card (ZMod 29) + 1) / 2 ∧ (∀ P ∈ S, IsInteriorXY P) ∧
      ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∀ ℓ : Line (ZMod 29), Incident P ℓ → Incident Q ℓ →
        IsPassantXY ℓ) ↔
    ∃ ℓ : Line (ZMod 29), IsPassantXY ℓ ∧
      ∀ P : Point (ZMod 29), P ∈ S ↔ (Incident P ℓ ∧ IsInteriorXY P) := by
  constructor
  · rintro ⟨hcard, hint, hpass⟩
    exact interior_set_eq_interior_points_of_passant_29 S hcard hint hpass
  · rintro ⟨ℓ, hℓ, hS⟩
    obtain ⟨T, hT, hTcard, hTpass⟩ :=
      interior_points_of_passant (by rw [ZMod.ringChar_zmod_n]; norm_num) hℓ
    have hST : S = T := by
      ext P; rw [hS, hT]
    subst hST
    exact ⟨hTcard, fun P hP => ((hS P).1 hP).2, hTpass⟩

omit [Field F] in
/-- `q = 27` does not satisfy the congruence hypothesis of the theorem. -/
theorem card_27_not_one_mod_four (h27 : Fintype.card F = 27) : ¬ Fintype.card F % 4 = 1 := by
  rw [h27]; norm_num

end InteriorPassant
