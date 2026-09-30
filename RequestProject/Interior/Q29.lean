module

public import RequestProject.Interior.Reduction
import all RequestProject.Interior.Compute
import all RequestProject.Interior.Search
import all RequestProject.Interior.Criteria
import all RequestProject.Algebra

/-!
# The case `q = 29`

For `q = 29` the requested statement is verified by an exhaustive (verified) search over all
sets of `15` interior points of `x y = z²` in `PG(2, 29)` which are pairwise joined by passants.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace InteriorPassant

open CompleteExterior

instance fact_prime_29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-- All elements of `GF(29)`. -/
def els29 : List (ZMod 29) := List.finRange 29

/-- The (normalized coordinates of the) `406` interior points of `x y = z²` in `PG(2, 29)`. -/
def W29 : Array (Fin 3 → ZMod 29) := (verts els29).toArray

/-- The adjacency table ("the joining line is a passant") between the interior points. -/
def A29 : Array (Array Bool) := adjArr els29

/-- The exhaustive search: every `15`-clique is the set of interior points on a line. -/
theorem check29 : search (adjA A29) (okA W29) (List.range W29.size) W29.size 15 [] = true := by
  native_decide

/-- **The case `q = 29`** of the requested theorem: in `PG(2, 29)`, every set `S` of `15` interior
points of the conic `x y = z²` such that every line through two distinct points of `S` is a
passant is the set of interior points on some passant. -/
theorem interior_set_eq_interior_points_of_passant_29
    (S : Finset (Point (ZMod 29))) (hcard : S.card = (Fintype.card (ZMod 29) + 1) / 2)
    (hint : ∀ P ∈ S, IsInteriorXY P)
    (hpass : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      ∀ ℓ : Line (ZMod 29), Incident P ℓ → Incident Q ℓ → IsPassantXY ℓ) :
    ∃ ℓ : Line (ZMod 29), IsPassantXY ℓ ∧ ∀ P : Point (ZMod 29), P ∈ S ↔ (Incident P ℓ ∧ IsInteriorXY P) :=
  statement_of_check (by rw [ZMod.ringChar_zmod_n]; norm_num) els29 (fun x => List.mem_finRange x)
    W29 rfl A29 rfl 15 (by rw [ZMod.card]) check29 S hcard hint hpass

end InteriorPassant
