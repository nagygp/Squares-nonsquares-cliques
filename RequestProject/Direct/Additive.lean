module

public import RequestProject.Direct.Eigen

/-!
# Anti-automorphisms of the Paley graph are additive

Let `q ≡ 1 (mod 4)` and let `u` be an anti-automorphism of the Paley graph of `GF(q)` fixing `0`.
From the coefficient condition (`IsAnti.coef_eq_zero`) we show:

* if `p ∤ j` and `j ≥ 2` then the coefficient of `x ^ j` in `u` vanishes (comparing the
  coefficients of `x ^ j` and `x ^ (j - 1)` in all translates `u (x + c) - u c`);
* composing with a power of the Frobenius map, the same holds for every `j` that is not a power of
  `p`;

so `u` is a linearized polynomial `∑ a_b x ^ (p ^ b)`, hence additive.
-/

@[expose] public section

open Finset Polynomial

namespace CompleteExterior.Direct

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
lemma two_mul_half_add_one (hq : Fintype.card F % 4 = 1) :
    2 * ((Fintype.card F / 2 : ℕ) : F) + 1 = 0 := by
  have : Fintype.card F = 2 * (Fintype.card F / 2) + 1 := by omega
  have h := FiniteField.cast_card_eq_zero F
  rw [this] at h
  push_cast at h
  exact h

lemma rho_one (hq : Fintype.card F % 4 = 1) :
    (rho 1 : F) = ((Fintype.card F / 2 : ℕ) : F) := by
  have h5 := card_ge_five hq
  rw [rho_eq hq le_rfl (by omega)]
  simp

/-- Two consecutive eigenvalues cannot both be equal to `ρ 1`. -/
lemma rho_not_both (hq : Fintype.card F % 4 = 1) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ Fintype.card F - 2) (h1 : (rho (k + 1) : F) = rho 1) (h2 : (rho k : F) = rho 1) :
    False := by
  have h5 := card_ge_five hq
  have hm := two_mul_half_add_one hq
  rw [rho_one hq, rho_eq hq (by omega) hk] at h1
  rw [rho_one hq, rho_eq hq hk1 (by omega)] at h2
  set m := Fintype.card F / 2 with hmdef
  have hm0 : (m : F) ≠ 0 := by
    intro h; rw [h] at hm; simp at hm
  have hkm : k ≤ m := by
    by_contra hlt
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h2
    simp at h2
    exact hm0 h2.symm
  have hid := Nat.choose_succ_right_eq m k
  have hid' : (m.choose (k + 1) : F) * (k + 1) = (m.choose k : F) * (m - k) := by
    have := congrArg (fun n : ℕ => (n : F)) hid
    push_cast [Nat.cast_sub hkm] at this
    exact this
  have hsq : ((-1 : F) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have e1 : (m.choose (k + 1) : F) = (-1) ^ k * m := by
    have : (m.choose (k + 1) : F) * ((-1) ^ k) ^ 2 = (-1) ^ k * m := by
      rw [pow_succ] at h1; linear_combination ((-1 : F) ^ k) * h1
    rwa [hsq, mul_one] at this
  have e2 : (m.choose k : F) = -((-1) ^ k * m) := by
    have : (m.choose k : F) * ((-1) ^ k) ^ 2 = -((-1) ^ k * m) := by
      linear_combination (-(-1 : F) ^ k) * h2
    rwa [hsq, mul_one] at this
  rw [e1, e2] at hid'
  have hk0 : ((-1 : F) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have : ((-1 : F) ^ k * m) * (m + 1) = 0 := by linear_combination hid'
  rcases mul_eq_zero.mp this with h | h
  · exact mul_ne_zero hk0 hm0 h
  · have : (1 : F) = 0 := by linear_combination 2 * h - hm
    exact one_ne_zero this

/-- The coefficients of `u` at exponents `j ≥ 2` not divisible by `p` vanish. -/
lemma IsAnti.coef_eq_zero_of_cast_ne_zero {u : F → F} (hq : Fintype.card F % 4 = 1)
    (hu : IsAnti u) {j : ℕ} (h2 : 2 ≤ j) (hj : j ≤ Fintype.card F - 2) (hjF : (j : F) ≠ 0) :
    coef u j = 0 := by
  have h5 := card_ge_five hq
  by_contra hc
  have hρj : (rho j : F) = rho 1 := by
    by_contra hne; exact hc (hu.coef_eq_zero hq hj hne)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hρk : (rho k : F) ≠ rho 1 := fun h => rho_not_both hq (by omega) hj hρj h
  set a : ℕ → F := fun i => -coef u i with ha
  have hrep : ∀ z, u z = ∑ i ∈ range (Fintype.card F - 1), a i * z ^ i := by
    intro z
    rw [repr u hu.1 (hu.sum_eq_zero (by omega)) z, ← Finset.sum_neg_distrib]
    simp [ha]
  -- vanishing of a polynomial in the translation parameter `c`
  have hvan : ∀ c : F, ∑ i ∈ range (Fintype.card F - 1), a i * (i.choose k : F) * c ^ (i - k)
      = 0 := by
    intro c
    have h0 := (hu.translate c).coef_eq_zero hq (j := k) (by omega) hρk
    rw [coef] at h0
    have hN : ∑ x : F, x ^ (Fintype.card F - 1 - k) = 0 :=
      FiniteField.sum_pow_lt_card_sub_one F _ (by omega)
    simp_rw [sub_mul] at h0
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hN, mul_zero, sub_zero,
      sum_translate a u hrep c (by omega) (by omega)] at h0
    exact neg_eq_zero.mp h0
  set P : F[X] := ∑ i ∈ range (Fintype.card F - 1), C (a i * (i.choose k : F)) * X ^ (i - k)
    with hP
  have hPeval : ∀ c : F, P.eval c = 0 := by
    intro c; rw [hP, eval_finset_sum]; simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact hvan c
  have hPdeg : P.natDegree < Fintype.card F := by
    have : P.natDegree ≤ Fintype.card F - 2 := by
      rw [hP]
      apply natDegree_sum_le_of_forall_le
      intro i hi
      rw [Finset.mem_range] at hi
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    omega
  have hP0 : P = 0 := P.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (f := fun c : F => c) Function.injective_id hPeval hPdeg
  have hcoeff := congrArg (fun Q : F[X] => Q.coeff 1) hP0
  simp only [hP, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at hcoeff
  rw [Finset.sum_eq_single (k + 1)] at hcoeff
  · rw [if_pos (by omega), Nat.choose_succ_self_right] at hcoeff
    apply hc
    have : a (k + 1) * ((k + 1 : ℕ) : F) = 0 := hcoeff
    rcases mul_eq_zero.mp this with h | h
    · simpa [ha] using h
    · exact absurd h hjF
  · intro i _ hi; rw [if_neg (by omega)]
  · intro h; exfalso; apply h; rw [Finset.mem_range]; omega

/-- The coefficients of `u` vanish except at powers of the characteristic. -/
lemma IsAnti.eq_pow_of_coef_ne_zero {u : F → F} (hq : Fintype.card F % 4 = 1)
    (hu : IsAnti u) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ Fintype.card F - 2) (hc : coef u i ≠ 0) :
    ∃ b, i = ringChar F ^ b := by
  have h5 := card_ge_five hq
  have hF := ringChar_ne_two_of_card_mod_four hq
  set p := ringChar F with hp
  have hpp : p.Prime := CharP.char_is_prime F p
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨b, j, hndvd, hij⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show i ≠ 0 by omega) p
    hpp.one_lt.ne'
  have hj0 : j ≠ 0 := by rintro rfl; simp at hndvd
  by_cases hj1 : j = 1
  · exact ⟨b, by rw [hij, hj1, mul_one]⟩
  exfalso
  obtain ⟨e, -, hqe⟩ := FiniteField.card F p
  set n : ℕ := (e : ℕ)
  have hPb : 1 ≤ p ^ b := Nat.one_le_pow _ _ hpp.pos
  have hji : j ≤ i := by rw [hij]; exact Nat.le_mul_of_pos_left j hPb
  have hbn : b ≤ n := by
    by_contra hlt
    have : p ^ n < p ^ b := Nat.pow_lt_pow_right hpp.one_lt (by omega)
    have : p ^ b ≤ i := by rw [hij]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  set v : F → F := fun x => u (x ^ (p ^ (n - b))) with hv
  have hvA : IsAnti v := hu.comp_frobenius hF (n - b)
  have hjF : (j : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p]; exact hndvd
  have hvc := hvA.coef_eq_zero_of_cast_ne_zero hq (j := j) (by omega) (by omega) hjF
  apply hc
  rw [← hvc, coef, coef]
  -- substitute `x = y ^ (p ^ b)`
  have hbij : Function.Bijective (fun y : F => y ^ (p ^ b)) := by
    have hinj : Function.Injective (fun y : F => y ^ (p ^ b)) :=
      (iterateFrobenius F p b).injective
    exact Finite.injective_iff_bijective.mp hinj
  refine Fintype.sum_bijective (fun y : F => y ^ (p ^ b)) hbij _ _ (fun y => ?_)
  simp only [hv]
  rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hbn, ← hqe, FiniteField.pow_card, ← pow_mul]
  congr 1
  by_cases hy : y = 0
  · rw [hy, zero_pow (by omega), zero_pow]
    apply Nat.mul_ne_zero (by omega) (by omega)
  · have hexp : p ^ b * (Fintype.card F - 1 - j) =
        (p ^ b - 1) * (Fintype.card F - 1) + (Fintype.card F - 1 - i) := by
      have h1 : p ^ b * (Fintype.card F - 1 - j) = p ^ b * (Fintype.card F - 1) - i := by
        rw [Nat.mul_sub, hij]
      rw [h1, Nat.sub_one_mul]
      have : Fintype.card F - 1 ≤ p ^ b * (Fintype.card F - 1) :=
        Nat.le_mul_of_pos_left _ hPb
      omega
    rw [hexp, pow_add, pow_mul', FiniteField.pow_card_sub_one_eq_one y hy, one_pow, one_mul]

/-- **Additivity.**  For `q ≡ 1 (mod 4)`, every anti-automorphism of the Paley graph of `GF(q)`
fixing `0` is additive. -/
theorem IsAnti.map_add {u : F → F} (hq : Fintype.card F % 4 = 1) (hu : IsAnti u) (x y : F) :
    u (x + y) = u x + u y := by
  have h5 := card_ge_five hq
  have hsum := hu.sum_eq_zero (by omega)
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  have hc0 : coef u 0 = 0 := by
    rw [coef, ← hsum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z = 0
    · rw [hz, hu.1, zero_mul]
    · rw [Nat.sub_zero, FiniteField.pow_card_sub_one_eq_one z hz, mul_one]
  have hterm : ∀ i ∈ range (Fintype.card F - 1),
      coef u i * (x + y) ^ i = coef u i * x ^ i + coef u i * y ^ i := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hci : coef u i = 0
    · simp [hci]
    · have hi1 : 1 ≤ i := by
        by_contra h; apply hci; rw [show i = 0 by omega, hc0]
      obtain ⟨b, rfl⟩ := hu.eq_pow_of_coef_ne_zero hq hi1 (by omega) hci
      rw [add_pow_char_pow, mul_add]
  rw [repr u hu.1 hsum (x + y), repr u hu.1 hsum x, repr u hu.1 hsum y,
    Finset.sum_congr rfl hterm, Finset.sum_add_distrib, neg_add]

end CompleteExterior.Direct
