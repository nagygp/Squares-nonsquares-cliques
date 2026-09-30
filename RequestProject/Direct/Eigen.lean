module

public import RequestProject.Direct.Coeff
public import RequestProject.Paley

/-!
# Anti-automorphisms of the Paley graph and an eigenvalue identity

An *anti-automorphism* of the Paley graph fixing `0` is a map `u : GF(q) → GF(q)` with `u 0 = 0`
and `χ (u x - u y) = - χ (x - y)` for all `x, y`.  For such a map we prove the identity
`∑ y, χ (x - y) χ y u y = κ u x`, and translate it into a condition on the coefficients of `u`:
the coefficient of `x ^ j` can only be non-zero if `ρ j = ρ 1`, where
`ρ j = -(-1) ^ j * binom((q-1)/2, j)`.
-/

@[expose] public section

open Finset

namespace CompleteExterior.Direct

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `u` is an anti-automorphism of the Paley graph fixing `0`. -/
def IsAnti (u : F → F) : Prop :=
  u 0 = 0 ∧ ∀ x y, quadraticChar F (u x - u y) = - quadraticChar F (x - y)

namespace IsAnti

variable {u : F → F}

lemma chi (hu : IsAnti u) (y : F) : quadraticChar F (u y) = - quadraticChar F y := by
  have := hu.2 y 0
  rwa [hu.1, sub_zero, sub_zero] at this

lemma injective (hu : IsAnti u) : Function.Injective u := by
  intro x y h
  by_contra hxy
  have := hu.2 x y
  rw [h, sub_self, quadraticChar_zero] at this
  have h2 : quadraticChar F (x - y) = 0 := by linarith
  exact hxy (sub_eq_zero.mp ((quadraticChar_eq_zero_iff).mp h2))

lemma bijective (hu : IsAnti u) : Function.Bijective u :=
  Finite.injective_iff_bijective.mp hu.injective

lemma sum_eq_zero (hu : IsAnti u) (hq : 3 ≤ Fintype.card F) : ∑ x, u x = 0 := by
  rw [Fintype.sum_bijective u hu.bijective (fun x => u x) (fun x => x) (fun _ => rfl)]
  have := FiniteField.sum_pow_lt_card_sub_one F 1 (by omega)
  simpa using this

lemma translate (hu : IsAnti u) (c : F) : IsAnti (fun x => u (x + c) - u c) := by
  refine ⟨by simp, fun x y => ?_⟩
  have := hu.2 (x + c) (y + c)
  simp only [sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] at this ⊢
  exact this

lemma comp_frobenius (hu : IsAnti u) (hF : ringChar F ≠ 2) (a : ℕ) :
    IsAnti (fun x => u (x ^ (ringChar F ^ a))) := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  have hodd : Odd (ringChar F ^ a) :=
    Odd.pow (Nat.Prime.odd_of_ne_two (CharP.char_is_prime F (ringChar F)) hF)
  have hpos : ringChar F ^ a ≠ 0 := hodd.pos.ne'
  refine ⟨by simp only; rw [zero_pow hpos, hu.1], fun x y => ?_⟩
  simp only
  rw [hu.2]
  congr 1
  rw [← sub_pow_char_pow, map_pow]
  by_cases h : x - y = 0
  · rw [h, quadraticChar_zero, zero_pow hpos]
  · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h']
    · exact one_pow _
    · exact hodd.neg_one_pow

end IsAnti

omit [DecidableEq F] in
lemma card_ge_five (hq : Fintype.card F % 4 = 1) : 5 ≤ Fintype.card F := by
  have := Fintype.one_lt_card (α := F)
  omega

lemma chi_mul_self {z : F} (hz : z ≠ 0) :
    ((quadraticChar F z : ℤ) : F) * (quadraticChar F z : F) = 1 := by
  have := quadraticChar_sq_one hz
  rw [← Int.cast_mul, ← sq, this, Int.cast_one]

/-- The constant `κ = ∑ t, χ (t (1 - t)) t`. -/
def kappa : F := ∑ t : F, (quadraticChar F (t * (1 - t)) : F) * t

lemma sum_chi_mul_id (hq : Fintype.card F % 4 = 1) (w : F) :
    ∑ z : F, (quadraticChar F (w - z) : F) * (quadraticChar F z : F) * z = kappa * w := by
  by_cases hw : w = 0
  · subst hw
    have e : ∀ z : F, (quadraticChar F (0 - z) : F) * (quadraticChar F z : F) * z = z := by
      intro z
      by_cases hz : z = 0
      · simp [hz]
      · rw [zero_sub, quadraticChar_neg' hq, chi_mul_self hz, one_mul]
    simp_rw [e]; rw [mul_zero]
    simpa using FiniteField.sum_pow_lt_card_sub_one F 1 (by have := card_ge_five hq; omega)
  · rw [kappa, Finset.sum_mul]
    refine (Fintype.sum_bijective (fun t => w * t) (mulLeft_bijective₀ w hw) _ _ ?_).symm
    intro t
    simp only
    rw [show w - w * t = w * (1 - t) by ring, map_mul, map_mul, map_mul]
    push_cast
    have := chi_mul_self hw
    linear_combination (-((quadraticChar F t : F) * (quadraticChar F (1 - t) : F) * t * w)) *
      this

lemma IsAnti.sum_eq {u : F → F} (hq : Fintype.card F % 4 = 1) (hu : IsAnti u) (x : F) :
    ∑ y, (quadraticChar F (x - y) : F) * (quadraticChar F y : F) * u y = kappa * u x := by
  rw [← sum_chi_mul_id hq (u x)]
  refine Fintype.sum_bijective u hu.bijective _ _ (fun y => ?_)
  rw [hu.2 x y, hu.chi y]; push_cast; ring

/-- The eigenvalues `ρ j = ∑ s, χ (s - 1) s ^ (q - 1 - j)`. -/
def rho (j : ℕ) : F := ∑ s : F, (quadraticChar F (s - 1) : F) * s ^ (Fintype.card F - 1 - j)

lemma coef_sum_chi (v : F → F) {j : ℕ} (hj : j ≤ Fintype.card F - 2) :
    ∑ x, (∑ y, (quadraticChar F (x - y) : F) * (quadraticChar F y : F) * v y) *
      x ^ (Fintype.card F - 1 - j) = rho j * coef v j := by
  have hN : Fintype.card F - 1 - j ≠ 0 := by
    have := Fintype.one_lt_card (α := F); omega
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, coef, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y = 0
  · subst hy; simp [zero_pow hN]
  · rw [rho, Finset.sum_mul]
    refine (Fintype.sum_bijective (fun s => y * s) (mulLeft_bijective₀ y hy) _ _ ?_).symm
    intro s
    simp only
    rw [show y * s - y = y * (s - 1) by ring, map_mul, mul_pow]
    push_cast
    have := chi_mul_self hy
    linear_combination (-((quadraticChar F (s - 1) : F) * s ^ (Fintype.card F - 1 - j) * v y *
      y ^ (Fintype.card F - 1 - j))) * this

lemma kappa_eq_rho_one (hq : Fintype.card F % 4 = 1) : (kappa : F) = rho 1 := by
  have h5 := card_ge_five hq
  have h := coef_sum_chi (fun x : F => x) (j := 1) (by omega)
  simp_rw [sum_chi_mul_id hq] at h
  have hc : coef (fun x : F => x) 1 = -1 := by
    rw [coef]
    have : ∀ x : F, x * x ^ (Fintype.card F - 1 - 1) = x ^ (Fintype.card F - 1) := by
      intro x; rw [← pow_succ']; congr 1; omega
    simp_rw [this]
    rw [sum_pow_pos (by omega), if_pos dvd_rfl]
  simp_rw [mul_assoc, ← Finset.mul_sum] at h
  rw [show (∑ x : F, x * x ^ (Fintype.card F - 1 - 1)) = coef (fun x : F => x) 1 from rfl,
    hc] at h
  linear_combination -h

/-- The explicit value of `ρ j`. -/
lemma rho_eq (hq : Fintype.card F % 4 = 1) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ Fintype.card F - 2) :
    (rho j : F) = -((-1) ^ j * ((Fintype.card F / 2).choose j : F)) := by
  have h5 := card_ge_five hq
  have hF := ringChar_ne_two_of_card_mod_four hq
  set m := Fintype.card F / 2 with hm
  have hmeven : Even m := ⟨Fintype.card F / 4, by omega⟩
  rw [rho]
  simp_rw [quadraticChar_eq_pow_of_char_ne_two' hF, ← hm, sub_pow, one_pow, mul_one,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ k ∈ range (m + 1), ∑ s : F, (-1) ^ (k + m) * s ^ k * (m.choose k : F) *
      s ^ (Fintype.card F - 1 - j) =
      if k = j then -((-1) ^ j * (m.choose j : F)) else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have : ∀ s : F, (-1) ^ (k + m) * s ^ k * (m.choose k : F) * s ^ (Fintype.card F - 1 - j) =
        ((-1) ^ (k + m) * (m.choose k : F)) * s ^ (k + (Fintype.card F - 1 - j)) := by
      intro s; rw [pow_add]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_pow_shift (by omega) hj1 hj]
    split_ifs with h
    · subst h; rw [pow_add, hmeven.neg_one_pow]; ring
    · ring
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' (range (m + 1)) j]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- **The coefficient condition.**  If `u` is an anti-automorphism of the Paley graph fixing `0`,
then for `1 ≤ j ≤ q - 2` the coefficient `coef u j` vanishes unless `ρ j = ρ 1`. -/
lemma IsAnti.coef_eq_zero {u : F → F} (hq : Fintype.card F % 4 = 1) (hu : IsAnti u) {j : ℕ}
    (hj : j ≤ Fintype.card F - 2) (hne : (rho j : F) ≠ rho 1) : coef u j = 0 := by
  have h := coef_sum_chi u hj
  simp_rw [hu.sum_eq hq, mul_assoc, ← Finset.mul_sum] at h
  rw [kappa_eq_rho_one hq] at h
  change rho 1 * coef u j = rho j * coef u j at h
  have : (rho 1 - rho j) * coef u j = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hne))

end CompleteExterior.Direct
