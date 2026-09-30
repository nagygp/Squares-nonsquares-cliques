module

public import Mathlib

/-!
# Coefficients of functions on a finite field

Every function `u : GF(q) → GF(q)` is a polynomial function of degree `< q`.  We extract the
coefficients by the sums `coef u j = ∑ x, u x * x ^ (q - 1 - j)` (which is `-1` times the
coefficient of `x ^ j`, for `1 ≤ j ≤ q - 2`), and compute a few sums needed later.
-/

@[expose] public section

open Finset

namespace CompleteExterior.Direct

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Power sums over a finite field, for a positive exponent. -/
lemma sum_pow_pos {e : ℕ} (he : 0 < e) :
    ∑ x : F, x ^ e = if Fintype.card F - 1 ∣ e then -1 else 0 := by
  rw [← FiniteField.sum_pow_units F e]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : F => x ≠ 0) (fun x : F => x ^ e)]
  have h2 : ∑ x : {x : F // ¬ x ≠ 0}, (x : F) ^ e = 0 := by
    apply Finset.sum_eq_zero; intro x _; have := x.2; push_neg at this
    rw [this, zero_pow he.ne']
  rw [h2, add_zero]
  exact (Fintype.sum_equiv (unitsEquivNeZero) _ _ (fun u => rfl)).symm

/-- The basic orthogonality relation for monomials. -/
lemma sum_pow_shift {l k : ℕ} (hl : l ≤ Fintype.card F - 2) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card F - 2) :
    ∑ x : F, x ^ (l + (Fintype.card F - 1 - k)) = if l = k then -1 else 0 := by
  rw [sum_pow_pos (by omega)]
  by_cases hlk : l = k
  · subst hlk; rw [if_pos (show _ from ⟨1, by omega⟩), if_pos rfl]
  · rw [if_neg hlk, if_neg]
    rintro ⟨c, hc⟩
    generalize hQ : Fintype.card F - 1 = Q at hc
    rcases c with _ | _ | c
    · omega
    · omega
    · have : Q * (c + 1 + 1) ≥ 2 * Q := by nlinarith
      omega

/-- The coefficient functional: for `1 ≤ j ≤ q - 2`, `coef u j` is minus the coefficient of
`x ^ j` in the polynomial representing `u`. -/
def coef (u : F → F) (j : ℕ) : F := ∑ x, u x * x ^ (Fintype.card F - 1 - j)

/-- Fourier inversion: a function with `u 0 = 0` and `∑ u = 0` is represented by its
coefficients. -/
lemma repr (u : F → F) (h0 : u 0 = 0) (hsum : ∑ x, u x = 0) (x : F) :
    u x = -∑ i ∈ range (Fintype.card F - 1), coef u i * x ^ i := by
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  simp only [coef, Finset.sum_mul]
  rw [Finset.sum_comm]
  by_cases hx : x = 0
  · subst hx
    rw [h0]
    have : ∀ y : F, ∑ i ∈ range (Fintype.card F - 1),
        u y * y ^ (Fintype.card F - 1 - i) * (0 : F) ^ i = u y * y ^ (Fintype.card F - 1) := by
      intro y
      rcases Nat.lt_or_ge 1 (Fintype.card F) with h | h
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro i _ hi; rw [zero_pow hi, mul_zero]
        · intro h'; exfalso; apply h'; simp; omega
      · have : Fintype.card F - 1 = 0 := by omega
        rw [this]; simp
        have : Fintype.card F = 1 := by omega
        exact (Fintype.card_eq_one_iff.mp this).elim fun a ha => by
          rw [ha y, ← ha 0, h0]
    simp_rw [this]
    have e : ∀ y : F, u y * y ^ (Fintype.card F - 1) = u y := by
      intro y
      by_cases hy : y = 0
      · rw [hy, h0, zero_mul]
      · rw [FiniteField.pow_card_sub_one_eq_one y hy, mul_one]
    simp_rw [e]; rw [hsum, neg_zero]
  · have key : ∀ y : F, ∑ i ∈ range (Fintype.card F - 1),
        u y * y ^ (Fintype.card F - 1 - i) * x ^ i = if y = x then -u y else 0 := by
      intro y
      by_cases hy : y = 0
      · subst hy; rw [h0, if_neg (Ne.symm hx)]; simp
      · have e : ∀ i ∈ range (Fintype.card F - 1),
            u y * y ^ (Fintype.card F - 1 - i) * x ^ i = u y * (x / y) ^ i := by
          intro i hi
          rw [Finset.mem_range] at hi
          rw [pow_sub₀ y hy hi.le, FiniteField.pow_card_sub_one_eq_one y hy, div_pow]
          field_simp
        rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
        by_cases hyx : y = x
        · subst hyx
          rw [if_pos rfl, div_self hy]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [Nat.cast_sub hq1, Nat.cast_one, FiniteField.cast_card_eq_zero]; ring
        · rw [if_neg hyx]
          have hr : x / y ≠ 1 := by
            intro h; apply hyx; rw [div_eq_one_iff_eq hy] at h; exact h.symm
          rw [geom_sum_eq hr, div_pow, FiniteField.pow_card_sub_one_eq_one x hx,
            FiniteField.pow_card_sub_one_eq_one y hy]
          simp
    simp_rw [key]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ _), neg_neg]

/-- The coefficients of a translate. -/
lemma sum_translate (a : ℕ → F) (u : F → F)
    (hu : ∀ z, u z = ∑ i ∈ range (Fintype.card F - 1), a i * z ^ i) (c : F) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card F - 2) :
    ∑ x, u (x + c) * x ^ (Fintype.card F - 1 - k) =
      -∑ i ∈ range (Fintype.card F - 1), a i * (i.choose k : F) * c ^ (i - k) := by
  simp_rw [hu, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp_rw [add_pow, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ l ∈ range (i + 1), ∑ x : F, a i * (x ^ l * c ^ (i - l) * (i.choose l : F)) *
      x ^ (Fintype.card F - 1 - k) =
      if l = k then -(a i * (i.choose k : F) * c ^ (i - k)) else 0 := by
    intro l hl
    rw [Finset.mem_range] at hl
    have : ∀ x : F, a i * (x ^ l * c ^ (i - l) * (i.choose l : F)) *
        x ^ (Fintype.card F - 1 - k) =
        (a i * c ^ (i - l) * (i.choose l : F)) * x ^ (l + (Fintype.card F - 1 - k)) := by
      intro x; rw [pow_add]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_pow_shift (by omega) hk1 hk]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' (range (i + 1)) k]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

end CompleteExterior.Direct
