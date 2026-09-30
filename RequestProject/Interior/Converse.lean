module

public import RequestProject.Interior.Criteria

/-!
# The interior points on a passant

For odd `q`, the interior points on a passant form a set of `(q + 1) / 2` points, and the line
joining any two of them (the passant itself) is a passant.  So the sets described in the
conclusion of the requested theorem do satisfy its hypotheses.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace InteriorPassant

open CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of `y` with `y² - n` a non-square is `(q + 1) / 2` for a non-square `n`. -/
lemma card_sq_sub_nonsquare_neg (hF : ringChar F ≠ 2) {n : F} (hn : quadraticChar F n = -1) :
    (Finset.univ.filter (fun y : F => quadraticChar F (y ^ 2 - n) = -1)).card =
      (Fintype.card F + 1) / 2 := by
  have h1 := card_sq_sub_nonsquare hF hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hne : ∀ y : F, y ^ 2 - n ≠ 0 := by
    intro y h
    have : n = y ^ 2 := by linear_combination -h
    rw [this, quadraticChar_sq_one' (by rintro rfl; simp at this; exact hn0 this)] at hn
    norm_num at hn
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset F)) (fun y : F => quadraticChar F (y ^ 2 - n) = 1)
  have heq : (Finset.univ.filter (fun y : F => ¬ quadraticChar F (y ^ 2 - n) = 1)) =
      Finset.univ.filter (fun y : F => quadraticChar F (y ^ 2 - n) = -1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases quadraticChar_dichotomy (hne y) with h | h <;> simp [h]
  rw [heq, Finset.card_univ] at hsplit
  omega

/-- The interior points of the conic `x z = y²` on a passant: there are `(q + 1) / 2` of them. -/
theorem interior_points_of_passant_xz (hF : ringChar F ≠ 2) {ℓ : Line F} (hℓ : IsPassant ℓ) :
    ∃ S : Finset (Point F),
      (∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ quadraticChar F (cf P.rep) = -1)) ∧
      S.card = (Fintype.card F + 1) / 2 := by
  classical
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set L := ℓ.rep with hL
  set u : Fin 3 → F := ![-L 2, L 1 / 2, -L 0] with hu
  have hpolL : ∀ v : Fin 3 → F, L ⬝ᵥ v = pol u v := by
    intro v; simp [hu, pol, dotProduct, Fin.sum_univ_three]; field_simp; ring
  have hinc : ∀ P : Point F, Incident P ℓ ↔ pol u P.rep = 0 := by
    intro P; rw [Incident, ← hL, hpolL]
  have hu0 : u ≠ 0 := by
    intro h
    apply ℓ.rep_nonzero
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp [hu, hF2] at h0 h1 h2
    funext i; fin_cases i <;> simp [← hL, h0, h1, h2]
  have hcfu : cf u ≠ 0 := by
    intro h
    apply hℓ (mk F u hu0)
    · rw [hinc]
      obtain ⟨c, hc, hrep⟩ := rep_mk_eq_smul u hu0
      rw [hrep, pol_smul_right, pol_self, h, mul_zero, mul_zero]
    · rw [onConic_of_rep _ u hu0 rfl]; exact h
  set n := cf u with hn
  set u₀ : Fin 3 → F := ![1, 0, -n] with hu₀
  have hcfu₀ : cf u₀ = n := by simp [hu₀, cf]
  have hpolu₀ : ∀ w : Fin 3 → F, pol u₀ w = n * w 0 - w 2 := by
    intro w; simp [hu₀, pol]; ring
  obtain ⟨d, hd, hdu⟩ := exists_refl_to hF2 hcfu₀.symm hcfu
  set τ := refl d with hτ
  have hτinj : Function.Injective τ := refl_injective hd
  let Φ : Point F → Point F := map τ hτinj
  have hΦΦ : ∀ P, Φ (Φ P) = P := map_refl_map_refl hd
  have hΦinj : Function.Injective Φ := Function.LeftInverse.injective hΦΦ
  -- `pol u v = 0 ↔ pol u₀ (τ v) = 0`
  have hpolτ : ∀ v : Fin 3 → F, pol u v = 0 ↔ pol u₀ (τ v) = 0 := by
    intro v
    rcases hdu with h | h
    · rw [← h, pol_refl hd]
    · rw [show u₀ = -(τ u) by rw [h, neg_neg], pol_neg_left, pol_refl hd, neg_eq_zero]
  -- `n` is a non-square, since `ℓ` is a passant
  have hnsq : quadraticChar F n = -1 := by
    rw [quadraticChar_neg_one_iff_not_isSquare]
    rintro ⟨s, hs⟩
    set X : Fin 3 → F := ![1, s, n] with hX
    have hX0 : X ≠ 0 := by intro h; have := congrFun h 0; simp [hX] at this
    have hτX0 : τ X ≠ 0 := fun h => hX0 (hτinj (by rw [h, map_zero]))
    apply hℓ (mk F (τ X) hτX0)
    · rw [incident_of_rep _ _ _ hτX0 rfl, ← hL, hpolL, hpolτ, refl_refl hd, hpolu₀]
      simp [hX]
    · rw [onConic_of_rep _ _ hτX0 rfl, cf_refl hd]
      simp [hX, cf, hs]; ring
  -- the explicit set in normal form
  set Y := Finset.univ.filter (fun y : F => quadraticChar F (y ^ 2 - n) = -1) with hY
  let f : F → Point F := fun y => mk F ![1, y, n] (by intro h; have := congrFun h 0; simp at this)
  have hfinj : Function.Injective f := by
    intro y y' h
    simp only [f] at h
    rw [mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp at h0 h1
    rw [h0, one_mul] at h1
    exact h1.symm
  set T := Y.image f with hT
  have hTcard : T.card = (Fintype.card F + 1) / 2 := by
    rw [hT, Finset.card_image_of_injective _ hfinj, hY, card_sq_sub_nonsquare_neg hF hnsq]
  have hTmem : ∀ Q : Point F, Q ∈ T ↔
      (n * Q.rep 0 = Q.rep 2 ∧ quadraticChar F (cf Q.rep) = -1) := by
    intro Q
    rw [hT, Finset.mem_image]
    simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and, f]
    constructor
    · rintro ⟨y, hy, h⟩
      obtain ⟨c, hc, hrep⟩ := rep_eq_smul_of_eq_mk Q _ _ h.symm
      rw [hrep, quadraticChar_cf_smul hc]
      refine ⟨by simp; ring, ?_⟩
      simpa [cf] using hy
    · rintro ⟨h1, h2⟩
      by_cases h0 : Q.rep 0 = 0
      · exfalso
        have h2' : Q.rep 2 = 0 := by rw [← h1, h0, mul_zero]
        have hcf : cf Q.rep = Q.rep 1 ^ 2 := by simp [cf, h0]
        rw [hcf] at h2
        by_cases h1' : Q.rep 1 = 0
        · rw [h1'] at h2; simp at h2
        · rw [quadraticChar_sq_one' h1'] at h2; norm_num at h2
      · refine ⟨Q.rep 1 / Q.rep 0, ?_, ?_⟩
        · have : (Q.rep 1 / Q.rep 0) ^ 2 - n = cf Q.rep * (Q.rep 0)⁻¹ ^ 2 := by
            simp only [cf]; rw [← h1]; field_simp
          rw [this, quadraticChar_mul_sq (inv_ne_zero h0), h2]
        · symm
          apply eq_mk_of_rep_eq_smul Q _ _ (Q.rep 0)
          funext i; fin_cases i <;> simp [← h1] <;> field_simp
  refine ⟨T.image Φ, ?_, ?_⟩
  · intro P
    have : P ∈ T.image Φ ↔ Φ P ∈ T := by
      constructor
      · intro h
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h
        rwa [hΦΦ]
      · intro h
        exact Finset.mem_image.2 ⟨Φ P, h, hΦΦ P⟩
    rw [this, hTmem, hinc, hpolτ]
    obtain ⟨c, hc, hrep⟩ := rep_map_refl hd P
    simp only [Φ]
    rw [hrep, quadraticChar_cf_smul hc, cf_refl hd, hpolu₀]
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have : c * (n * (τ P.rep) 0 - (τ P.rep) 2) = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_left hc
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination c * h1, h2⟩
  · rw [Finset.card_image_of_injective _ hΦinj, hTcard]

/-- **Converse.**  For odd `q`, the interior points of `x y = z²` on a passant form a set of
`(q + 1) / 2` points, and every line through two of them is a passant. -/
theorem interior_points_of_passant (hF : ringChar F ≠ 2) {ℓ : Line F} (hℓ : IsPassantXY ℓ) :
    ∃ S : Finset (Point F), (∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ IsInteriorXY P)) ∧
      S.card = (Fintype.card F + 1) / 2 ∧
      ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∀ ℓ' : Line F, Incident P ℓ' → Incident Q ℓ' →
        IsPassantXY ℓ' := by
  classical
  obtain ⟨T, hT, hTcard⟩ := interior_points_of_passant_xz hF ((isPassant_swapP ℓ).2 hℓ)
  have hmem : ∀ P : Point F, P ∈ T.image swapP ↔ (Incident P ℓ ∧ IsInteriorXY P) := by
    intro P
    have : P ∈ T.image swapP ↔ swapP P ∈ T := by
      constructor
      · intro h
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h
        rwa [swapP_swapP]
      · intro h
        exact Finset.mem_image.2 ⟨swapP P, h, swapP_swapP P⟩
    rw [this, hT, incident_swapP, isInteriorXY_iff_swapP, isInterior_iff hF]
  refine ⟨T.image swapP, hmem, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (Function.LeftInverse.injective swapP_swapP), hTcard]
  · intro P hP Q hQ hPQ ℓ' h1 h2
    rw [← line_unique hPQ ((hmem P).1 hP).1 ((hmem Q).1 hQ).1 h1 h2]
    exact hℓ

end InteriorPassant
