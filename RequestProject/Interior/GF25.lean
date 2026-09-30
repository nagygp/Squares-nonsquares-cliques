module

public import Mathlib

/-!
# A concrete model of the field with `25` elements

`GF25` is `GF(5)[t] / (t² - 2)`; the element `a + b t` (`a, b ∈ {0, …, 4}`) is encoded as the
number `a + 5 b < 25`.  The field axioms are checked by exhaustive computation.
-/

@[expose] public section

namespace InteriorPassant

/-- The field with `25` elements, `GF(5)[t] / (t² - 2)`. -/
def GF25 : Type := Fin 25

namespace GF25

instance : DecidableEq GF25 := inferInstanceAs (DecidableEq (Fin 25))
instance : Fintype GF25 := inferInstanceAs (Fintype (Fin 25))

/-- The element with code `n % 25`, i.e. `a + b t` for `n % 25 = a + 5 b`. -/
def g (n : ℕ) : GF25 := (⟨n % 25, Nat.mod_lt _ (by norm_num)⟩ : Fin 25)

/-- The coefficients of `1, t`. -/
def d0 (x : GF25) : ℕ := (x : Fin 25).val % 5
def d1 (x : GF25) : ℕ := (x : Fin 25).val / 5 % 5

/-- The element `a + b t` (coefficients reduced mod `5`). -/
def enc (a b : ℕ) : GF25 := g (a % 5 + 5 * (b % 5))

def add (x y : GF25) : GF25 := enc (d0 x + d0 y) (d1 x + d1 y)
def neg (x : GF25) : GF25 := enc (4 * d0 x) (4 * d1 x)
/-- Multiplication, using `t² = 2`. -/
def mul (x y : GF25) : GF25 :=
  enc (d0 x * d0 y + 2 * (d1 x * d1 y)) (d0 x * d1 y + d1 x * d0 y)
def inv (x : GF25) : GF25 := ((List.finRange 25).map g).find? (fun y => mul x y = g 1) |>.getD (g 0)

instance : Zero GF25 := ⟨g 0⟩
instance : One GF25 := ⟨g 1⟩
instance : Add GF25 := ⟨add⟩
instance : Neg GF25 := ⟨neg⟩
instance : Mul GF25 := ⟨mul⟩
instance : Inv GF25 := ⟨inv⟩

lemma add_assoc' : ∀ a b c : GF25, a + b + c = a + (b + c) := by decide +kernel
lemma zero_add' : ∀ a : GF25, 0 + a = a := by decide +kernel
lemma add_zero' : ∀ a : GF25, a + 0 = a := by decide +kernel
lemma neg_add_cancel' : ∀ a : GF25, -a + a = 0 := by decide +kernel
lemma add_comm' : ∀ a b : GF25, a + b = b + a := by decide +kernel
lemma mul_assoc' : ∀ a b c : GF25, a * b * c = a * (b * c) := by decide +kernel
lemma one_mul' : ∀ a : GF25, 1 * a = a := by decide +kernel
lemma mul_one' : ∀ a : GF25, a * 1 = a := by decide +kernel
lemma zero_mul' : ∀ a : GF25, 0 * a = 0 := by decide +kernel
lemma mul_zero' : ∀ a : GF25, a * 0 = 0 := by decide +kernel
lemma left_distrib' : ∀ a b c : GF25, a * (b + c) = a * b + a * c := by decide +kernel
lemma right_distrib' : ∀ a b c : GF25, (a + b) * c = a * c + b * c := by decide +kernel
lemma mul_comm' : ∀ a b : GF25, a * b = b * a := by decide +kernel
lemma mul_inv_cancel' : ∀ a : GF25, a ≠ 0 → a * a⁻¹ = 1 := by decide +kernel
lemma inv_zero' : (0 : GF25)⁻¹ = 0 := by decide +kernel
lemma zero_ne_one' : (0 : GF25) ≠ 1 := by decide +kernel

instance : Field GF25 where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancel'
  add_comm := add_comm'
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  mul_comm := mul_comm'
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := inv_zero'
  exists_pair_ne := ⟨0, 1, zero_ne_one'⟩
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

lemma card_eq : Fintype.card GF25 = 25 := Fintype.card_fin 25

lemma two_ne_zero' : (2 : GF25) ≠ 0 := by decide +kernel

lemma ringChar_ne_two : ringChar GF25 ≠ 2 := by
  intro h
  apply two_ne_zero'
  have := ringChar.Nat.cast_ringChar (R := GF25)
  rw [h] at this
  exact_mod_cast this

end GF25

end InteriorPassant
