module

public import Mathlib

/-!
# The Paley graph counting argument

This file contains the combinatorial heart of the paper: the proof of the "extra property"
via counting in the Paley graph of `GF(q)`, `q ≡ 1 (mod 4)`.

Throughout, `ψ` is an involution of `GF(q)*` such that each pair `{x, ψ x}` consists of a
square and a non-square, and such that for any two different pairs the product of the four
cross differences is a non-square (condition (1) of the paper).
-/

@[expose] public section

open Finset

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Basic facts about the quadratic character -/

omit [DecidableEq F] in
lemma ringChar_ne_two_of_card_mod_four (hq : Fintype.card F % 4 = 1) : ringChar F ≠ 2 := by
  intro h
  have := FiniteField.even_card_iff_char_two.mp h
  omega

lemma quadraticChar_neg_one_eq_one (hq : Fintype.card F % 4 = 1) :
    quadraticChar F (-1) = 1 := by
  rw [quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)]
  exact FiniteField.isSquare_neg_one_iff.mpr (by omega)

lemma quadraticChar_neg' (hq : Fintype.card F % 4 = 1) (x : F) :
    quadraticChar F (-x) = quadraticChar F x := by
  rw [neg_eq_neg_one_mul, map_mul, quadraticChar_neg_one_eq_one hq, one_mul]

lemma quadraticChar_sub_comm (hq : Fintype.card F % 4 = 1) (x y : F) :
    quadraticChar F (x - y) = quadraticChar F (y - x) := by
  rw [← neg_sub, quadraticChar_neg' hq]

lemma quadraticChar_mul_sq {x y : F} (hy : y ≠ 0) :
    quadraticChar F (x * y ^ 2) = quadraticChar F x := by
  rw [map_mul, quadraticChar_sq_one' hy, mul_one]

lemma quadraticChar_div (x : F) {y : F} (hy : y ≠ 0) :
    quadraticChar F (x / y) = quadraticChar F (x * y) := by
  have : x / y = x * y * (y⁻¹) ^ 2 := by field_simp
  rw [this, quadraticChar_mul_sq (inv_ne_zero hy)]

lemma quadraticChar_eq_one_or_neg_one {x : F} (hx : x ≠ 0) :
    quadraticChar F x = 1 ∨ quadraticChar F x = -1 :=
  quadraticChar_dichotomy hx

/-! ### The indicator of non-zero squares -/

/-- `sqInd x = 1` if `x` is a non-zero square and `0` otherwise. -/
def sqInd (x : F) : ℤ := if quadraticChar F x = 1 then 1 else 0

lemma sqInd_nonneg (x : F) : 0 ≤ sqInd x := by unfold sqInd; split_ifs <;> norm_num

lemma sqInd_le_one (x : F) : sqInd x ≤ 1 := by unfold sqInd; split_ifs <;> norm_num

lemma two_mul_sqInd (x : F) :
    2 * sqInd x = quadraticChar F x + quadraticChar F x ^ 2 := by
  unfold sqInd
  by_cases hx : x = 0
  · subst hx; simp
  · rcases quadraticChar_dichotomy hx with h | h <;> simp [h]

lemma sqInd_neg (hq : Fintype.card F % 4 = 1) (x : F) : sqInd (-x) = sqInd x := by
  simp [sqInd, quadraticChar_neg' hq]

lemma sqInd_sub_comm (hq : Fintype.card F % 4 = 1) (x y : F) : sqInd (x - y) = sqInd (y - x) := by
  rw [← neg_sub, sqInd_neg hq]

lemma sqInd_of_one {x : F} (h : quadraticChar F x = 1) : sqInd x = 1 := by simp [sqInd, h]

lemma sqInd_of_neg_one {x : F} (h : quadraticChar F x = -1) : sqInd x = 0 := by
  simp [sqInd, h]

lemma sqInd_zero : sqInd (0 : F) = 0 := by simp [sqInd]

/-- If the product of four non-zero elements is a non-square, then an odd number of them
are squares. -/
lemma sqInd_four_odd {x₁ x₂ x₃ x₄ : F} (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (h₃ : x₃ ≠ 0) (h₄ : x₄ ≠ 0)
    (h : quadraticChar F (x₁ * x₂ * x₃ * x₄) = -1) :
    (sqInd x₁ + sqInd x₂ + sqInd x₃ + sqInd x₄) % 2 = 1 := by
  simp only [map_mul] at h
  rcases quadraticChar_dichotomy h₁ with e₁ | e₁ <;>
  rcases quadraticChar_dichotomy h₂ with e₂ | e₂ <;>
  rcases quadraticChar_dichotomy h₃ with e₃ | e₃ <;>
  rcases quadraticChar_dichotomy h₄ with e₄ | e₄ <;>
  simp_all [sqInd]

/-! ### Character sums -/

lemma sum_quadraticChar_sub (hF : ringChar F ≠ 2) (v : F) :
    ∑ w : F, quadraticChar F (w - v) = 0 := by
  rw [← quadraticChar_sum_zero hF]
  exact Fintype.sum_equiv (Equiv.subRight v) _ _ (fun _ => rfl)

lemma sum_quadraticChar_sq_sub (v : F) :
    ∑ w : F, quadraticChar F (w - v) ^ 2 = Fintype.card F - 1 := by
  have h1 : ∑ w : F, quadraticChar F (w - v) ^ 2 = ∑ w : F, quadraticChar F w ^ 2 :=
    Fintype.sum_equiv (Equiv.subRight v) _ _ (fun _ => rfl)
  have h2 : ∀ w : F, quadraticChar F w ^ 2 = if w = 0 then 0 else 1 := by
    intro w
    split_ifs with hw
    · subst hw; simp
    · exact quadraticChar_sq_one hw
  rw [h1, Finset.sum_congr rfl (fun w _ => h2 w), Finset.sum_ite]
  simp [Finset.filter_ne', Finset.card_univ, Nat.cast_sub (Fintype.card_pos : 0 < Fintype.card F)]

/-- The Jacobi-sum identity `∑_x χ(x - u) χ(x - v) = -1` for `u ≠ v`. -/
lemma sum_quadraticChar_mul_sub (hF : ringChar F ≠ 2) {u v : F} (huv : u ≠ v) :
    ∑ w : F, quadraticChar F (w - u) * quadraticChar F (w - v) = -1 := by
  set χ := quadraticChar F
  have hd : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hJ : jacobiSum χ χ = -χ (-1) := by
    have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic F).inv] at this
  -- substitute `w = u + (v - u) * s`
  let e : F ≃ F := (Equiv.mulLeft₀ (v - u) hd).trans (Equiv.addLeft u)
  have h1 : ∑ w : F, χ (w - u) * χ (w - v) = ∑ s : F, χ (e s - u) * χ (e s - v) :=
    (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have h2 : ∀ s : F, χ (e s - u) * χ (e s - v) = χ (-1) * (χ s * χ (1 - s)) := by
    intro s
    have he : e s = u + (v - u) * s := rfl
    have hsq : χ (v - u) ^ 2 = 1 := quadraticChar_sq_one hd
    rw [he, show u + (v - u) * s - u = (v - u) * s by ring,
      show u + (v - u) * s - v = (v - u) * ((-1) * (1 - s)) by ring]
    simp only [map_mul]
    linear_combination (χ s * χ (-1) * χ (1 - s)) * hsq
  rw [h1, Finset.sum_congr rfl (fun s _ => h2 s), ← Finset.mul_sum]
  have : ∑ s : F, χ s * χ (1 - s) = jacobiSum χ χ := rfl
  rw [this, hJ]
  have : χ (-1) ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  linear_combination (-1 : ℤ) * this

lemma sum_sqInd_sub (hF : ringChar F ≠ 2) (v : F) :
    2 * ∑ w : F, sqInd (w - v) = Fintype.card F - 1 := by
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun w _ => two_mul_sqInd (w - v)),
    Finset.sum_add_distrib, sum_quadraticChar_sub hF, sum_quadraticChar_sq_sub]
  ring

/-- The number of common neighbours of two distinct vertices `u, v` of the Paley graph:
`4 * #{w : w - u, w - v non-zero squares} = q - 3 - 2 χ(u - v)`. -/
lemma sum_sqInd_mul (hq : Fintype.card F % 4 = 1) {u v : F} (huv : u ≠ v) :
    4 * ∑ w : F, sqInd (w - u) * sqInd (w - v) =
      Fintype.card F - 3 - 2 * quadraticChar F (u - v) := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  set χ := quadraticChar F
  have key : ∀ w : F, 4 * (sqInd (w - u) * sqInd (w - v)) =
      χ (w - u) * χ (w - v) + χ (w - u) * χ (w - v) ^ 2 + χ (w - u) ^ 2 * χ (w - v)
        + χ (w - u) ^ 2 * χ (w - v) ^ 2 := by
    intro w
    have h1 := two_mul_sqInd (w - u)
    have h2 := two_mul_sqInd (w - v)
    linear_combination (2 * sqInd (w - v)) * h1 + (χ (w - u) + χ (w - u) ^ 2) * h2
  -- auxiliary sums
  have sq_eq : ∀ x : F, χ x ^ 2 = if x = 0 then 0 else 1 := by
    intro x
    split_ifs with hx
    · subst hx; simp [χ]
    · exact quadraticChar_sq_one hx
  have hA : ∑ w : F, χ (w - u) * χ (w - v) ^ 2 = - χ (v - u) := by
    have : ∀ w : F, χ (w - u) * χ (w - v) ^ 2 = χ (w - u) - if w = v then χ (v - u) else 0 := by
      intro w
      rw [sq_eq]
      by_cases hw : w = v
      · subst hw; simp
      · simp [hw, sub_eq_zero]
    rw [Finset.sum_congr rfl (fun w _ => this w), Finset.sum_sub_distrib,
      sum_quadraticChar_sub hF]
    simp
  have hB : ∑ w : F, χ (w - u) ^ 2 * χ (w - v) = - χ (u - v) := by
    have : ∀ w : F, χ (w - u) ^ 2 * χ (w - v) = χ (w - v) - if w = u then χ (u - v) else 0 := by
      intro w
      rw [sq_eq]
      by_cases hw : w = u
      · subst hw; simp
      · simp [hw, sub_eq_zero]
    rw [Finset.sum_congr rfl (fun w _ => this w), Finset.sum_sub_distrib,
      sum_quadraticChar_sub hF]
    simp
  have hC : ∑ w : F, χ (w - u) ^ 2 * χ (w - v) ^ 2 = Fintype.card F - 2 := by
    have : ∀ w : F, χ (w - u) ^ 2 * χ (w - v) ^ 2 =
        χ (w - u) ^ 2 - if w = v then 1 else 0 := by
      intro w
      rw [sq_eq, sq_eq]
      by_cases hw : w = v
      · subst hw; simp [sub_eq_zero, Ne.symm huv]
      · by_cases hw' : w = u
        · subst hw'; simp [hw]
        · simp [hw, hw', sub_eq_zero]
    rw [Finset.sum_congr rfl (fun w _ => this w), Finset.sum_sub_distrib,
      sum_quadraticChar_sq_sub]
    simp; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun w _ => key w)]
  simp only [Finset.sum_add_distrib]
  rw [sum_quadraticChar_mul_sub hF huv, hA, hB, hC, quadraticChar_sub_comm hq v u]
  ring

end CompleteExterior
