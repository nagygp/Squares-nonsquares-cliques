module

public import RequestProject.Core
public import RequestProject.Defs

/-!
# Determining the involution via the theorem of Carlitz and McConnel

Using the extra property and the theorem of Carlitz–McConnel, a good pairing `ψ` of `GF(q)*`
(`q ≡ 1 mod 4`) must be of the form `ψ x = n / x` for a non-square `n`.
-/

@[expose] public section

open Finset

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A field automorphism of order dividing two of a finite field of odd characteristic that fixes
a non-square is the identity. -/
lemma ringHom_eq_self_of_involutive (hF : ringChar F ≠ 2) (σ : F →+* F)
    (hσ : ∀ x, σ (σ x) = x) {b : F} (hb : σ b = b) (hbsq : ¬ IsSquare b) : ∀ x, σ x = x := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz⟩ := hcon
  let K : Subfield F := σ.eqLocusField (RingHom.id F)
  have memK : ∀ x : F, x ∈ K ↔ σ x = x := fun x => Iff.rfl
  have hzσ : z - σ z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  -- the map `K × K → F`, `(α, β) ↦ α + β z` is a bijection
  let φ : K × K → F := fun p => (p.1 : F) + (p.2 : F) * z
  have hφinj : Function.Injective φ := by
    rintro ⟨α, β⟩ ⟨α', β'⟩ h
    simp only [φ] at h
    by_cases hβ : (β : F) = β'
    · have hα : (α : F) = α' := by rw [hβ] at h; exact add_right_cancel h
      exact Prod.ext (Subtype.ext hα) (Subtype.ext hβ)
    · exfalso
      have hβ' : (β' : F) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
      have hzK : z = ((α : F) - α') / ((β' : F) - β) := by
        rw [eq_div_iff hβ']; linear_combination (-1 : F) * h
      apply hz
      rw [hzK, map_div₀, map_sub, map_sub, (memK _).1 α.2, (memK _).1 α'.2, (memK _).1 β.2,
        (memK _).1 β'.2]
  have hφsurj : Function.Surjective φ := by
    intro w
    set β : F := (w - σ w) / (z - σ z) with hβ
    have hβK : σ β = β := by
      rw [hβ, map_div₀, map_sub, map_sub, hσ, hσ]
      have : σ z - z ≠ 0 := sub_ne_zero.mpr hz
      field_simp; ring
    have hαK : σ (w - β * z) = w - β * z := by
      rw [map_sub, map_mul, hβK]
      rw [hβ]; field_simp; ring
    exact ⟨(⟨w - β * z, hαK⟩, ⟨β, hβK⟩), by simp [φ]⟩
  have hcard : Nat.card F = Nat.card K * Nat.card K := by
    rw [← Nat.card_prod]; exact (Nat.card_eq_of_bijective φ ⟨hφinj, hφsurj⟩).symm
  have hb0 : b ≠ 0 := by rintro rfl; exact hbsq ⟨0, by simp⟩
  letI : Fintype K := Fintype.ofFinite K
  have hbK : b ∈ K := hb
  have hpow : ((⟨b, hbK⟩ : K) ^ (Fintype.card K - 1)) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (fun h => hb0 (congrArg Subtype.val h))
  have hpow' : b ^ (Fintype.card K - 1) = 1 := by
    have := congrArg Subtype.val hpow
    simpa using this
  set k := Fintype.card K with hk
  have hq : Fintype.card F = k * k := by
    rw [Fintype.card_eq_nat_card, hcard, hk, Fintype.card_eq_nat_card]
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  rw [hq] at hodd
  have hkodd : k % 2 = 1 :=
    Nat.odd_iff.mp (Nat.odd_mul.mp (Nat.odd_iff.mpr hodd)).1
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  have hhalf : Fintype.card F / 2 = (k - 1) * (m + 1) := by
    rw [hq, hm]
    have : (2 * m + 1) * (2 * m + 1) = 2 * (2 * m * (m + 1)) + 1 := by ring
    rw [this, Nat.mul_add_div (by norm_num : 0 < 2)]
    simp only [Nat.reduceDiv, add_zero, add_tsub_cancel_right]
  apply hbsq
  rw [FiniteField.isSquare_iff hF hb0, hhalf, pow_mul, hpow', one_pow]

omit [DecidableEq F] in
/-- The characteristic of a finite field is prime. -/
lemma fact_prime_ringChar : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩

/-- For a good pairing `ψ`, the function `f` with `f 0 = 0` and `f x = 1 / ψ x` has all its
difference quotients non-squares (the hypothesis of the theorem of Carlitz and McConnel). -/
lemma quot_nonsquare (hq : Fintype.card F % 4 = 1) {ψ : F → F} (hψ : GoodPairing ψ)
    {x y : F} (hxy : x ≠ y) :
    quadraticChar F (((if x = 0 then 0 else (ψ x)⁻¹) - (if y = 0 then 0 else (ψ y)⁻¹)) *
      (x - y)) = -1 := by
  set χ := quadraticChar F
  -- a symmetric reformulation for the case of two nonzero arguments
  have main : ∀ x y : F, x ≠ 0 → y ≠ 0 → x ≠ y → χ x = 1 →
      χ (((ψ x)⁻¹ - (ψ y)⁻¹) * (x - y)) = -1 := by
    intro x y hx hy hxy hχx
    have hψx := hψ.ne_zero hx
    have hψy := hψ.ne_zero hy
    have e : ((ψ x)⁻¹ - (ψ y)⁻¹) * (x - y) =
        ((ψ x - ψ y) * (x - y)) * (-(ψ x * ψ y)) * ((ψ x * ψ y)⁻¹) ^ 2 := by
      field_simp; ring
    rw [e, quadraticChar_mul_sq (inv_ne_zero (mul_ne_zero hψx hψy)), map_mul,
      quadraticChar_neg' hq, map_mul χ (ψ x) (ψ y), hψ.chi_apply hx, hψ.chi_apply hy, hχx]
    rcases quadraticChar_dichotomy hy with hχy | hχy
    · have := extra_property hq hψ hχx hχy hxy
      rw [mul_comm (x - y)] at this
      rw [this, hχy]; norm_num
    · rw [hχy]
      suffices χ ((ψ x - ψ y) * (x - y)) = 1 by rw [this]; norm_num
      -- `t = ψ y` is a square
      set t := ψ y with ht
      have hχt : χ t = 1 := by rw [ht, hψ.chi_apply hy, hχy]; norm_num
      have hψt : ψ t = y := hψ.inv y hy
      by_cases htx : t = x
      · have hyψx : y = ψ x := by rw [← hψt, htx]
        have e2 : (ψ x - t) * (x - y) = -((x - y) ^ 2) := by rw [htx, ← hyψx]; ring
        rw [e2, quadraticChar_neg' hq, quadraticChar_sq_one' (sub_ne_zero.mpr hxy)]
      · have hyψx : y ≠ ψ x := by
          intro h; apply htx; rw [ht, h, hψ.inv x hx]
        have h1 := hψ.pair x y hx hy (Ne.symm hxy) hyψx
        have h2 := extra_property hq hψ hχx hχt (Ne.symm htx)
        rw [hψt] at h2
        have e3 : (x - y) * (x - ψ y) * (ψ x - y) * (ψ x - ψ y) =
            ((ψ x - t) * (x - y)) * ((x - t) * (ψ x - y)) := by rw [ht]; ring
        rw [e3, map_mul, h2] at h1
        linarith
  by_cases hx : x = 0
  · subst hx
    have hy : y ≠ 0 := Ne.symm hxy
    simp only [if_true, hy, if_false, zero_sub]
    have e : -(ψ y)⁻¹ * -y = (y * ψ y) * ((ψ y)⁻¹) ^ 2 := by
      have := hψ.ne_zero hy; field_simp
    rw [e, quadraticChar_mul_sq (inv_ne_zero (hψ.ne_zero hy)), hψ.mix y hy]
  by_cases hy : y = 0
  · subst hy
    simp only [hx, if_false, if_true, sub_zero]
    have e : (ψ x)⁻¹ * x = (x * ψ x) * ((ψ x)⁻¹) ^ 2 := by
      have := hψ.ne_zero hx; field_simp
    rw [e, quadraticChar_mul_sq (inv_ne_zero (hψ.ne_zero hx)), hψ.mix x hx]
  simp only [hx, hy, if_false]
  rcases quadraticChar_dichotomy hx with hχx | hχx
  · exact main x y hx hy hxy hχx
  rcases quadraticChar_dichotomy hy with hχy | hχy
  · have := main y x hy hx (Ne.symm hxy) hχy
    rwa [show ((ψ y)⁻¹ - (ψ x)⁻¹) * (y - x) = ((ψ x)⁻¹ - (ψ y)⁻¹) * (x - y) by ring] at this
  -- both non-squares: pass to `s = ψ x`, `t = ψ y`
  have hψx := hψ.ne_zero hx
  have hψy := hψ.ne_zero hy
  have hs : χ (ψ x) = 1 := by rw [hψ.chi_apply hx, hχx]; norm_num
  have ht : χ (ψ y) = 1 := by rw [hψ.chi_apply hy, hχy]; norm_num
  have hst : ψ x ≠ ψ y := fun h => hxy (hψ.inj hx hy h)
  have h := extra_property hq hψ hs ht hst
  rw [hψ.inv x hx, hψ.inv y hy] at h
  have e' : ((ψ x)⁻¹ - (ψ y)⁻¹) * (x - y) =
      ((ψ x - ψ y) * (x - y)) * (-(ψ x * ψ y)) * ((ψ x * ψ y)⁻¹) ^ 2 := by
    field_simp; ring
  rw [e', quadraticChar_mul_sq (inv_ne_zero (mul_ne_zero hψx hψy)), map_mul, h,
    quadraticChar_neg' hq, map_mul, hs, ht]
  norm_num

/-- **Main step of the paper**: a good pairing `ψ` of `GF(q)*`, `q ≡ 1 (mod 4)`, is of the form
`ψ x = n / x` for some non-square `n`.  This uses the theorem of Carlitz–McConnel. -/
theorem goodPairing_eq_div (hq : Fintype.card F % 4 = 1) (hCM : CarlitzMcConnel F)
    {ψ : F → F} (hψ : GoodPairing ψ) :
    ∃ n : F, quadraticChar F n = -1 ∧ ∀ x, x ≠ 0 → ψ x = n / x := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  set f : F → F := fun x => if x = 0 then 0 else (ψ x)⁻¹ with hf
  have hf_quot : ∀ x y : F, x ≠ y → ¬ IsSquare ((f x - f y) / (x - y)) := by
    intro x y hxy
    rw [← quadraticChar_neg_one_iff_not_isSquare, quadraticChar_div _ (sub_ne_zero.mpr hxy)]
    exact quot_nonsquare hq hψ hxy
  obtain ⟨a, b, j, hb, hfab⟩ := hCM f hf_quot
  haveI := fact_prime_ringChar (F := F)
  set p := ringChar F
  set σ : F →+* F := iterateFrobenius F p j with hσdef
  have hσ : ∀ x, σ x = x ^ (p ^ j) := fun x => rfl
  have hb0 : b ≠ 0 := by rintro rfl; exact hb ⟨0, by simp⟩
  have ha : a = 0 := by
    have := hfab 0
    simp only [hf, if_true] at this
    rw [← hσ, map_zero, mul_zero, add_zero] at this
    exact this.symm
  have hψx : ∀ x, x ≠ 0 → ψ x = (b * σ x)⁻¹ := by
    intro x hx
    have := hfab x
    simp only [hf, hx, if_false, ha, zero_add, ← hσ] at this
    rw [← this, inv_inv]
  have hσx0 : ∀ x, x ≠ 0 → σ x ≠ 0 := fun x hx h => hx (by simpa using (map_eq_zero σ).1 h)
  have key : ∀ x, x ≠ 0 → σ b * σ (σ x) = b * x := by
    intro x hx
    have h1 := hψ.inv x hx
    have hψ0 := hψ.ne_zero hx
    rw [hψx _ hψ0, hψx x hx, map_inv₀, map_mul] at h1
    have : σ b ≠ 0 := hσx0 b hb0
    have : σ (σ x) ≠ 0 := hσx0 _ (hσx0 x hx)
    field_simp at h1
    linear_combination h1
  have hσb : σ b = b := by
    have := key 1 one_ne_zero
    simpa using this
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have := key x hx
      rw [hσb] at this
      exact mul_left_cancel₀ hb0 this
  have hid := ringHom_eq_self_of_involutive hF σ hσσ hσb hb
  refine ⟨b⁻¹, ?_, ?_⟩
  · rw [quadraticChar_neg_one_iff_not_isSquare]
    intro h; apply hb
    have := h.inv
    simpa using this
  · intro x hx
    rw [hψx x hx, hid x]
    field_simp

end CompleteExterior
