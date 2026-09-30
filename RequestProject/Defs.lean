module

public import Mathlib

/-!
# Complete exterior sets of conics: definitions

We work in the Desarguesian projective plane `PG(2, q)` over a finite field `F` with `q`
elements.  Both points and lines are modelled as elements of the projectivization
`ℙ F (Fin 3 → F)`; a point `P` lies on a line `ℓ` iff the dot product of their homogeneous
coordinates vanishes.

As in the paper, we fix the nondegenerate conic `𝒞 : x z = y²` (every nondegenerate conic of
`PG(2, q)` is projectively equivalent to this one).
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace CompleteExterior

variable (F : Type*) [Field F]

/-- Points of the projective plane `PG(2, F)`. -/
abbrev Point := ℙ F (Fin 3 → F)

/-- Lines of the projective plane `PG(2, F)`, given by their (dual) homogeneous coordinates. -/
abbrev Line := ℙ F (Fin 3 → F)

variable {F}

/-- Incidence: the point `P` lies on the line `ℓ`. -/
def Incident (P : Point F) (ℓ : Line F) : Prop :=
  ℓ.rep ⬝ᵥ P.rep = 0

/-- The point `P = (x : y : z)` lies on the conic `𝒞 : x z = y²`. -/
def OnConic (P : Point F) : Prop :=
  P.rep 0 * P.rep 2 = P.rep 1 ^ 2

/-- A tangent line of `𝒞`: a line meeting the conic in exactly one point. -/
def IsTangent (ℓ : Line F) : Prop :=
  ∃! P : Point F, Incident P ℓ ∧ OnConic P

/-- A passant (external line) of `𝒞`: a line containing no point of the conic. -/
def IsPassant (ℓ : Line F) : Prop :=
  ∀ P : Point F, Incident P ℓ → ¬ OnConic P

/-- An exterior point of `𝒞`: a point off the conic lying on two (distinct) tangent lines. -/
def IsExterior (P : Point F) : Prop :=
  ¬ OnConic P ∧ ∃ ℓ₁ ℓ₂ : Line F, ℓ₁ ≠ ℓ₂ ∧ IsTangent ℓ₁ ∧ IsTangent ℓ₂ ∧
    Incident P ℓ₁ ∧ Incident P ℓ₂

variable (F) [Fintype F]

/-- The theorem of Carlitz and McConnel (in the form used in the paper, "Result"):
if `f : GF(q) → GF(q)` is such that `(f x - f y) / (x - y)` is a non-square for all `x ≠ y`,
then `f x = a + b x^(p^j)` where `p` is the characteristic and `b` is a non-square.

This is an external result quoted (not proved) in the paper; our main theorem takes it as an
explicit hypothesis. -/
def CarlitzMcConnel : Prop :=
  ∀ f : F → F, (∀ x y : F, x ≠ y → ¬ IsSquare ((f x - f y) / (x - y))) →
    ∃ a b : F, ∃ j : ℕ, ¬ IsSquare b ∧ ∀ x : F, f x = a + b * x ^ (ringChar F ^ j)

end CompleteExterior
