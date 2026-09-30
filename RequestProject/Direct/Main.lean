module

public import RequestProject.Direct.Additive
public import RequestProject.Involution

/-!
# Good pairings are linear: a self-contained algebraic proof

For `q ≡ 1 (mod 4)` we prove, without the theorem of Carlitz–McConnel and without any geometry,
that every good pairing `ψ` of `GF(q)*` has the form `ψ x = n / x` for a non-square `n`.

Outline.  Put `f x = 1 / ψ x` (and `f 0 = 0`).

1. By the extra property (the Paley-graph parity count of the paper, `Core.lean`), `f` is an
   anti-automorphism of the Paley graph: `χ (f x - f y) = - χ (x - y)` (`quot_nonsquare`).
2. Every such map is additive (`IsAnti.map_add`, proved from an eigenvalue identity for the
   coefficients of `f` in `Direct/Eigen.lean` and `Direct/Additive.lean`).
3. `f` also satisfies `f (1 / f x) = 1 / x` (because `ψ` is an involution).  With additivity,
   Hua's identity `x² = x - (x⁻¹ + (1 - x)⁻¹)⁻¹` gives `f (x²) = f x ² / f 1`, so `σ = f / f 1`
   is a field automorphism with `σ² = id` fixing the non-square `f 1`; hence `σ = id`.
-/

@[expose] public section

namespace CompleteExterior.Direct

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma quadraticChar_inv' (y : F) : quadraticChar F y⁻¹ = quadraticChar F y := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [inv_eq_one_div, quadraticChar_div _ hy, one_mul]

/-- **Hua step.**  An additive bijection `f` with `f (f x)⁻¹ = x⁻¹` for all `x`, such that
`f 1` is a non-square, is `x ↦ f 1 * x`. -/
lemma eq_mul_of_additive_of_inv (hF : ringChar F ≠ 2) {f : F → F}
    (hinj : Function.Injective f) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hinv : ∀ x, f (f x)⁻¹ = x⁻¹) (hsq : ¬ IsSquare (f 1)) : ∀ x, f x = f 1 * x := by
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  let fa : F →+ F := AddMonoidHom.mk' f hadd
  have hf0 : f 0 = 0 := fa.map_zero
  have hsub : ∀ x y, f (x - y) = f x - f y := fa.map_sub
  have hne : ∀ x, x ≠ 0 → f x ≠ 0 := fun x hx h => hx (hinj (h.trans hf0.symm))
  set a := f 1 with ha
  have ha0 : a ≠ 0 := hne 1 one_ne_zero
  -- `f (x²) * a = (f x)²`
  have hsqr : ∀ x, f (x ^ 2) * a = f x ^ 2 := by
    intro x
    by_cases hx0 : x = 0
    · rw [hx0]; simp [hf0]
    by_cases hx1 : x = 1
    · rw [hx1, one_pow, ← ha]; ring
    have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    set X := f x with hX
    set Y := f (1 - x) with hY
    have hX0 : X ≠ 0 := hne x hx0
    have hY0 : Y ≠ 0 := hne _ h1x
    have hXY : X + Y = a := by rw [hX, hY, ← hadd, add_sub_cancel]
    have hw : x⁻¹ + (1 - x)⁻¹ = f (X⁻¹ + Y⁻¹) := by rw [hadd, hinv, hinv]
    have hsq' : x ^ 2 = x - (x⁻¹ + (1 - x)⁻¹)⁻¹ := by
      field_simp
      ring
    have hXY0 : X⁻¹ + Y⁻¹ ≠ 0 := by
      intro h
      have : X + Y = 0 := by field_simp at h; linear_combination h
      rw [hXY] at this; exact ha0 this
    have hXYne : X + Y ≠ 0 := by rw [hXY]; exact ha0
    rw [hsq', hsub, hw, hinv, ← hX, ← hXY, inv_add_inv hX0 hY0, inv_div]
    rw [sub_mul, div_mul_cancel₀ _ hXYne]
    ring
  -- `σ = f / a` is a ring homomorphism
  have hmul : ∀ x y, f (x * y) * a = f x * f y := by
    intro x y
    have h := hsqr (x + y)
    rw [show (x + y) ^ 2 = x ^ 2 + (x * y + x * y) + y ^ 2 by ring, hadd, hadd, hadd, hadd] at h
    have h2 := hsqr x
    have h3 := hsqr y
    have : 2 * (f (x * y) * a - f x * f y) = 0 := by linear_combination h - h2 - h3
    have := (mul_eq_zero.mp this).resolve_left hF2
    linear_combination this
  let σ : F →+* F :=
    { toFun := fun x => f x / a
      map_one' := by simp [← ha, div_self ha0]
      map_mul' := by
        intro x y
        show f (x * y) / a = f x / a * (f y / a)
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero ha0 ha0), div_mul_eq_mul_div,
          div_eq_iff ha0 ] at *
        linear_combination a * hmul x y
      map_zero' := by simp [hf0]
      map_add' := by
        intro x y
        show f (x + y) / a = f x / a + f y / a
        rw [hadd, add_div] }
  have hσ : ∀ x, σ x = f x / a := fun x => rfl
  have hfσ : ∀ x, f x = a * σ x := by intro x; rw [hσ]; field_simp
  -- `σ` is an involution fixing `a`
  have key : ∀ x, a * (σ a)⁻¹ * (σ (σ x))⁻¹ = x⁻¹ := by
    intro x
    have := hinv x
    rw [hfσ (f x)⁻¹, hfσ x, mul_inv, map_mul, map_inv₀, map_inv₀] at this
    rw [← this]; ring
  have hσa : σ a = a := by
    have := key 1
    simp only [map_one, inv_one, mul_one] at this
    have hσa0 : σ a ≠ 0 := by
      intro h; rw [h, inv_zero, mul_zero] at this; exact zero_ne_one this
    field_simp at this
    exact this.symm
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    have := key x
    rw [hσa, mul_inv_cancel₀ ha0, one_mul] at this
    exact inv_injective this
  have hid := ringHom_eq_self_of_involutive hF σ hσσ hσa hsq
  intro x
  rw [hfσ x, hid x]

/-- **Main result (self-contained).**  For `q ≡ 1 (mod 4)`, every good pairing `ψ` of `GF(q)*`
has the form `ψ x = n / x` for a non-square `n`.  Unlike `goodPairing_eq_div`, this does not
assume the theorem of Carlitz–McConnel. -/
theorem goodPairing_eq_div_direct (hq : Fintype.card F % 4 = 1) {ψ : F → F}
    (hψ : GoodPairing ψ) :
    ∃ n : F, quadraticChar F n = -1 ∧ ∀ x, x ≠ 0 → ψ x = n / x := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  set f : F → F := fun x => if x = 0 then 0 else (ψ x)⁻¹ with hf
  have hA : IsAnti f := by
    refine ⟨by simp [hf], fun x y => ?_⟩
    by_cases hxy : x = y
    · rw [hxy, sub_self, sub_self, quadraticChar_zero, neg_zero]
    · have h := quot_nonsquare hq hψ hxy
      rw [map_mul] at h
      rcases quadraticChar_dichotomy (sub_ne_zero.mpr hxy) with e | e <;>
        rw [e] at h ⊢ <;> linarith
  have hinv : ∀ x, f (f x)⁻¹ = x⁻¹ := by
    intro x
    by_cases hx : x = 0
    · simp [hf, hx]
    · have hψx := hψ.ne_zero hx
      simp only [hf, hx, if_false, inv_inv, hψx, hψ.inv x hx]
  have hsq : ¬ IsSquare (f 1) := by
    rw [← quadraticChar_neg_one_iff_not_isSquare]
    simp only [hf, one_ne_zero, if_false]
    rw [quadraticChar_inv', hψ.chi_apply one_ne_zero, map_one]
  have hlin := eq_mul_of_additive_of_inv hF hA.injective (hA.map_add hq) hinv hsq
  refine ⟨(f 1)⁻¹, ?_, fun x hx => ?_⟩
  · rw [quadraticChar_inv', quadraticChar_neg_one_iff_not_isSquare]; exact hsq
  · have h := hlin x
    simp only [hf, hx, if_false] at h
    have hψx := hψ.ne_zero hx
    rw [← inv_inv (ψ x), h]
    simp only [hf, one_ne_zero, if_false]
    field_simp

/-- For `q ≡ 1 (mod 4)` every good pairing of `GF(q)*` is linear (no extra hypotheses). -/
theorem pairingsLinear_of_card_mod_four (hq : Fintype.card F % 4 = 1) : PairingsLinear F :=
  fun _ hψ => goodPairing_eq_div_direct hq hψ

end CompleteExterior.Direct
