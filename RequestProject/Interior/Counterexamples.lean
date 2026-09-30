module

public import RequestProject.Interior.Witness
public import RequestProject.Interior.GF27
public import RequestProject.Interior.GF25
import all RequestProject.Interior.GF25
import all RequestProject.Interior.Witness
import all RequestProject.Interior.Compute
import all RequestProject.Interior.Criteria
import all RequestProject.Interior.GF27
import all RequestProject.Algebra

/-!
# Small counterexamples

Without the hypotheses `q ≡ 1 (mod 4)` and `q ≥ 27` the statement can fail:

* `q = 27` (`q ≡ 3 (mod 4)`): a set of `14` interior points, pairwise joined by passants, not on
  a line;
* `q = 25`, `q = 13` and `q = 5` (`q ≡ 1 (mod 4)`, but `q < 27`): sets of `13`, `7`, resp. `3`,
  such points not on a line.

The witnesses were found by a computer search; every property used is checked in Lean.
-/

@[expose] public section

namespace InteriorPassant

open GF27

instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- All elements of `GF(13)`. -/
def els13 : List (ZMod 13) := List.finRange 13

/-- All elements of `GF(5)`. -/
def els5 : List (ZMod 5) := List.finRange 5

/-- A set of `7` interior points of `x y = z²` in `PG(2, 13)`, pairwise joined by passants and
not collinear. -/
def wit13 : List (Fin 3 → ZMod 13) :=
  [![1, 1, 3], ![1, 12, 12], ![1, 11, 10], ![1, 11, 0], ![1, 10, 11], ![1, 5, 8], ![1, 5, 7]]

theorem witness13 : witnessB els13 wit13 = true := by
  native_decide

/-- **`q = 13`**: the statement fails (so the hypothesis `q ≥ 27` cannot simply be dropped). -/
theorem not_interiorStatement_13 : ¬ InteriorStatement (ZMod 13) :=
  not_statement_of_witness (by rw [ZMod.ringChar_zmod_n]; norm_num) els13
    (fun x => List.mem_finRange x) wit13 (by rw [ZMod.card]; rfl) witness13

/-- A set of `3` interior points of `x y = z²` in `PG(2, 5)`, pairwise joined by passants and
not collinear. -/
def wit5 : List (Fin 3 → ZMod 5) := [![1, 1, 2], ![1, 4, 4], ![1, 2, 3]]

theorem witness5 : witnessB els5 wit5 = true := by
  native_decide

/-- **`q = 5`**: the statement fails. -/
theorem not_interiorStatement_5 : ¬ InteriorStatement (ZMod 5) :=
  not_statement_of_witness (by rw [ZMod.ringChar_zmod_n]; norm_num) els5
    (fun x => List.mem_finRange x) wit5 (by rw [ZMod.card]; rfl) witness5

/-- All elements of `GF(27)`. -/
def els27 : List GF27 := (List.finRange 27).map fun i => g i.val

lemma mem_els27 (x : GF27) : x ∈ els27 := by
  simp only [els27, List.mem_map, List.mem_finRange, true_and]
  refine ⟨x, ?_⟩
  change (⟨(x : Fin 27).val % 27, _⟩ : Fin 27) = x
  exact Fin.ext (Nat.mod_eq_of_lt (x : Fin 27).isLt)

/-- A set of `14` interior points of `x y = z²` in `PG(2, 27)`, pairwise joined by passants and
not collinear (coordinates given by the codes of `GF27`). -/
def wit27 : List (Fin 3 → GF27) :=
  [![g 1, g 1, g 0], ![g 1, g 26, g 23], ![g 1, g 25, g 4], ![g 1, g 22, g 5],
    ![g 1, g 21, g 13], ![g 1, g 16, g 7], ![g 1, g 15, g 15], ![g 1, g 12, g 16],
    ![g 1, g 10, g 6], ![g 1, g 9, g 17], ![g 1, g 8, g 20], ![g 1, g 5, g 18],
    ![g 1, g 4, g 2], ![g 1, g 2, g 3]]

theorem witness27 : witnessB els27 wit27 = true := by
  native_decide

/-- **`q = 27`**: the statement (without the hypothesis `q ≡ 1 (mod 4)`) fails for the field
with `27` elements. -/
theorem not_interiorStatement_27 : ¬ InteriorStatement GF27 :=
  not_statement_of_witness ringChar_ne_two els27 mem_els27 wit27 (by rw [card_eq]; rfl) witness27

/-- All elements of `GF(25)`. -/
def els25 : List GF25 := (List.finRange 25).map fun i => GF25.g i.val

lemma mem_els25 (x : GF25) : x ∈ els25 := by
  simp only [els25, List.mem_map, List.mem_finRange, true_and]
  refine ⟨x, ?_⟩
  change (⟨(x : Fin 25).val % 25, _⟩ : Fin 25) = x
  exact Fin.ext (Nat.mod_eq_of_lt (x : Fin 25).isLt)

/-- A set of `13` interior points of `x y = z²` in `PG(2, 25)`, pairwise joined by passants and
not collinear (coordinates given by the codes of `GF25`). -/
def wit25 : List (Fin 3 → GF25) :=
  [![GF25.g 1, GF25.g 1, GF25.g 7], ![GF25.g 1, GF25.g 24, GF25.g 24],
    ![GF25.g 1, GF25.g 23, GF25.g 16], ![GF25.g 1, GF25.g 23, GF25.g 6],
    ![GF25.g 1, GF25.g 23, GF25.g 4], ![GF25.g 1, GF25.g 21, GF25.g 2],
    ![GF25.g 1, GF25.g 20, GF25.g 12], ![GF25.g 1, GF25.g 13, GF25.g 19],
    ![GF25.g 1, GF25.g 12, GF25.g 18], ![GF25.g 1, GF25.g 9, GF25.g 1],
    ![GF25.g 1, GF25.g 8, GF25.g 0], ![GF25.g 1, GF25.g 3, GF25.g 23],
    ![GF25.g 1, GF25.g 2, GF25.g 17]]

theorem witness25 : witnessB els25 wit25 = true := by
  native_decide

/-- **`q = 25`**: the statement fails for the field with `25` elements, although
`25 ≡ 1 (mod 4)`. -/
theorem not_interiorStatement_25 : ¬ InteriorStatement GF25 :=
  not_statement_of_witness GF25.ringChar_ne_two els25 mem_els25 wit25 (by rw [GF25.card_eq]; rfl)
    witness25

end InteriorPassant
