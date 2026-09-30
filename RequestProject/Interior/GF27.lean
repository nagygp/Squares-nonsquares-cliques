module

public import Mathlib

/-!
# A concrete model of the field with `27` elements

`GF27` is `GF(3)[t] / (t³ - t - 1)`; the element `a + b t + c t²` (`a, b, c ∈ {0, 1, 2}`) is
encoded as the number `a + 3 b + 9 c < 27`.  The field axioms are checked by exhaustive
computation.
-/

@[expose] public section

namespace InteriorPassant

/-- The field with `27` elements, `GF(3)[t] / (t³ - t - 1)`. -/
def GF27 : Type := Fin 27

namespace GF27

instance : DecidableEq GF27 := inferInstanceAs (DecidableEq (Fin 27))
instance : Fintype GF27 := inferInstanceAs (Fintype (Fin 27))

/-- The element with code `n % 27`, i.e. `a + b t + c t²` for `n % 27 = a + 3 b + 9 c`. -/
def g (n : ℕ) : GF27 := (⟨n % 27, Nat.mod_lt _ (by norm_num)⟩ : Fin 27)

/-- The coefficients of `1, t, t²`. -/
def d0 (x : GF27) : ℕ := (x : Fin 27).val % 3
def d1 (x : GF27) : ℕ := (x : Fin 27).val / 3 % 3
def d2 (x : GF27) : ℕ := (x : Fin 27).val / 9 % 3

/-- The element `a + b t + c t²` (coefficients reduced mod `3`). -/
def enc (a b c : ℕ) : GF27 := g (a % 3 + 3 * (b % 3) + 9 * (c % 3))

def add (x y : GF27) : GF27 := enc (d0 x + d0 y) (d1 x + d1 y) (d2 x + d2 y)
def neg (x : GF27) : GF27 := enc (2 * d0 x) (2 * d1 x) (2 * d2 x)
/-- Multiplication, using `t³ = t + 1` and `t⁴ = t² + t`. -/
def mul (x y : GF27) : GF27 :=
  let r0 := d0 x * d0 y
  let r1 := d0 x * d1 y + d1 x * d0 y
  let r2 := d0 x * d2 y + d1 x * d1 y + d2 x * d0 y
  let r3 := d1 x * d2 y + d2 x * d1 y
  let r4 := d2 x * d2 y
  enc (r0 + r3) (r1 + r3 + r4) (r2 + r4)
def inv (x : GF27) : GF27 := ((List.finRange 27).map g).find? (fun y => mul x y = g 1) |>.getD (g 0)

instance : Zero GF27 := ⟨g 0⟩
instance : One GF27 := ⟨g 1⟩
instance : Add GF27 := ⟨add⟩
instance : Neg GF27 := ⟨neg⟩
instance : Mul GF27 := ⟨mul⟩
instance : Inv GF27 := ⟨inv⟩

lemma add_assoc' : ∀ a b c : GF27, a + b + c = a + (b + c) := by decide +kernel
lemma zero_add' : ∀ a : GF27, 0 + a = a := by decide +kernel
lemma add_zero' : ∀ a : GF27, a + 0 = a := by decide +kernel
lemma neg_add_cancel' : ∀ a : GF27, -a + a = 0 := by decide +kernel
lemma add_comm' : ∀ a b : GF27, a + b = b + a := by decide +kernel
lemma mul_assoc' : ∀ a b c : GF27, a * b * c = a * (b * c) := by decide +kernel
lemma one_mul' : ∀ a : GF27, 1 * a = a := by decide +kernel
lemma mul_one' : ∀ a : GF27, a * 1 = a := by decide +kernel
lemma zero_mul' : ∀ a : GF27, 0 * a = 0 := by decide +kernel
lemma mul_zero' : ∀ a : GF27, a * 0 = 0 := by decide +kernel
lemma left_distrib' : ∀ a b c : GF27, a * (b + c) = a * b + a * c := by decide +kernel
lemma right_distrib' : ∀ a b c : GF27, (a + b) * c = a * c + b * c := by decide +kernel
lemma mul_comm' : ∀ a b : GF27, a * b = b * a := by decide +kernel
lemma mul_inv_cancel' : ∀ a : GF27, a ≠ 0 → a * a⁻¹ = 1 := by decide +kernel
lemma inv_zero' : (0 : GF27)⁻¹ = 0 := by decide +kernel
lemma zero_ne_one' : (0 : GF27) ≠ 1 := by decide +kernel

instance : Field GF27 where
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

lemma card_eq : Fintype.card GF27 = 27 := Fintype.card_fin 27

lemma two_ne_zero' : (2 : GF27) ≠ 0 := by decide +kernel

lemma ringChar_ne_two : ringChar GF27 ≠ 2 := by
  intro h
  apply two_ne_zero'
  have := ringChar.Nat.cast_ringChar (R := GF27)
  rw [h] at this
  exact_mod_cast this

end GF27

end InteriorPassant
