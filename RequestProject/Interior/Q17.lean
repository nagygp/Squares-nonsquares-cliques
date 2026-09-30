module

public import RequestProject.Interior.Reduction
import all RequestProject.Interior.Compute
import all RequestProject.Interior.Search
import all RequestProject.Interior.Criteria
import all RequestProject.Algebra

/-!
# The case `q = 17`

For `q = 17` the requested statement is verified by an exhaustive (verified) search over all
sets of `9` interior points of `x y = z²` in `PG(2, 17)` which are pairwise joined by passants.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace InteriorPassant

open CompleteExterior

instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- All elements of `GF(17)`. -/
def els17 : List (ZMod 17) := List.finRange 17

/-- The (normalized coordinates of the) `136` interior points of `x y = z²` in `PG(2, 17)`. -/
def W17 : Array (Fin 3 → ZMod 17) := (verts els17).toArray

/-- The adjacency table ("the joining line is a passant") between the interior points. -/
def A17 : Array (Array Bool) := adjArr els17

/-- The exhaustive search: every `9`-clique is the set of interior points on a line. -/
theorem check17 : search (adjA A17) (okA W17) (List.range W17.size) W17.size 9 [] = true := by
  native_decide

/-- **The case `q = 17`** (not covered by the hypothesis `q ≥ 27`, but still true): in `PG(2, 17)`, every set `S` of `9` interior
points of the conic `x y = z²` such that every line through two distinct points of `S` is a
passant is the set of interior points on some passant. -/
theorem interior_set_eq_interior_points_of_passant_17
    (S : Finset (Point (ZMod 17))) (hcard : S.card = (Fintype.card (ZMod 17) + 1) / 2)
    (hint : ∀ P ∈ S, IsInteriorXY P)
    (hpass : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      ∀ ℓ : Line (ZMod 17), Incident P ℓ → Incident Q ℓ → IsPassantXY ℓ) :
    ∃ ℓ : Line (ZMod 17), IsPassantXY ℓ ∧ ∀ P : Point (ZMod 17), P ∈ S ↔ (Incident P ℓ ∧ IsInteriorXY P) :=
  statement_of_check (by rw [ZMod.ringChar_zmod_n]; norm_num) els17 (fun x => List.mem_finRange x)
    W17 rfl A17 rfl 9 (by rw [ZMod.card]) check17 S hcard hint hpass

end InteriorPassant
