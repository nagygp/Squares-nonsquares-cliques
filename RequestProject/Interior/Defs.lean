module

public import RequestProject.Defs

/-!
# Sets of interior points of a conic joined by external lines: definitions

We keep the model of `PG(2, q)` used for the exterior case (points and lines are elements of
`ℙ F (Fin 3 → F)`, incidence is the vanishing of the dot product), but now use the conic

  `𝒞 : x y = z²`.

* a *tangent* is a line meeting `𝒞` in exactly one point;
* a *passant* (external line) is a line containing no point of `𝒞`;
* an *interior point* is a point off `𝒞` which lies on no tangent.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace InteriorPassant

open CompleteExterior

variable {F : Type*} [Field F]

/-- The point `P = (x : y : z)` lies on the conic `𝒞 : x y = z²`. -/
def OnConicXY (P : Point F) : Prop :=
  P.rep 0 * P.rep 1 = P.rep 2 ^ 2

/-- A tangent line of `𝒞 : x y = z²`: a line meeting the conic in exactly one point. -/
def IsTangentXY (ℓ : Line F) : Prop :=
  ∃! P : Point F, Incident P ℓ ∧ OnConicXY P

/-- A passant (external line) of `𝒞 : x y = z²`: a line containing no point of the conic. -/
def IsPassantXY (ℓ : Line F) : Prop :=
  ∀ P : Point F, Incident P ℓ → ¬ OnConicXY P

/-- An interior point of `𝒞 : x y = z²`: a point off the conic lying on no tangent line. -/
def IsInteriorXY (P : Point F) : Prop :=
  ¬ OnConicXY P ∧ ∀ ℓ : Line F, Incident P ℓ → ¬ IsTangentXY ℓ

/-- The statement of the requested theorem for a fixed field `F` with `q` elements, without
the arithmetic conditions on `q`: every set `S` of `(q + 1) / 2` interior points of
`x y = z²` such that every line through two distinct points of `S` is a passant is the set of
interior points on some passant. -/
def InteriorStatement (F : Type*) [Field F] [Fintype F] : Prop :=
  ∀ S : Finset (Point F), S.card = (Fintype.card F + 1) / 2 →
    (∀ P ∈ S, IsInteriorXY P) →
    (∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassantXY ℓ) →
    ∃ ℓ : Line F, IsPassantXY ℓ ∧ ∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ IsInteriorXY P)

end InteriorPassant
