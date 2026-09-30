module

public import RequestProject.Geometry

/-!
# The converse: the exterior points on a passant form a complete exterior set

For odd `q`, the exterior points on any passant are `(q + 1) / 2` in number, and the line
joining any two of them (the passant itself) misses the conic.  Together with the main theorem
this gives a characterization of complete exterior sets when `q ≡ 1 (mod 4)`.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace CompleteExterior

section Lines

variable {F : Type*} [Field F]

lemma linearIndependent_rep_of_ne {P Q : Point F} (hPQ : P ≠ Q) :
    LinearIndependent F ![P.rep, Q.rep] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases hs : s = 0
  · subst hs
    simp only [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right Q.rep_nonzero⟩
  · exfalso; apply hPQ
    rw [← mk_rep P, ← mk_rep Q, mk_eq_mk_iff']
    refine ⟨-t / s, ?_⟩
    have h1 : s • P.rep = (-t) • Q.rep := by rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hst
    rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- Every line through two distinct points `P, Q` is the line with coordinates `P × Q`. -/
lemma eq_cross_of_incident {P Q : Point F} (hPQ : P ≠ Q) {ℓ : Line F}
    (hP : Incident P ℓ) (hQ : Incident Q ℓ) :
    ℓ = mk F (crossProduct P.rep Q.rep)
      (crossProduct_ne_zero_iff_linearIndependent.2 (linearIndependent_rep_of_ne hPQ)) := by
  have hc : crossProduct P.rep Q.rep ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.2 (linearIndependent_rep_of_ne hPQ)
  have hcl : crossProduct (crossProduct P.rep Q.rep) ℓ.rep = 0 := by
    rw [cross_cross_eq_smul_sub_smul]
    simp only [Incident] at hP hQ
    rw [dotProduct_comm P.rep, dotProduct_comm Q.rep, hP, hQ, zero_smul, zero_smul, sub_zero]
  have hdep : ¬ LinearIndependent F ![crossProduct P.rep Q.rep, ℓ.rep] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not]; exact hcl
  rw [LinearIndependent.pair_iff] at hdep
  push_neg at hdep
  obtain ⟨s, t, hst, hne⟩ := hdep
  have ht : t ≠ 0 := by
    intro ht; subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact hne (hst.resolve_right hc) rfl
  rw [← mk_rep ℓ, mk_eq_mk_iff']
  refine ⟨-s / t, ?_⟩
  have h1 : t • ℓ.rep = (-s) • crossProduct P.rep Q.rep := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hst
  rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]

lemma pol_neg_left (u v : Fin 3 → F) : pol (-u) v = - pol u v := by
  simp [pol]; ring

/-- Two distinct points lie on at most one line. -/
lemma line_unique {P Q : Point F} (hPQ : P ≠ Q) {ℓ ℓ' : Line F}
    (h1 : Incident P ℓ) (h2 : Incident Q ℓ) (h3 : Incident P ℓ') (h4 : Incident Q ℓ') :
    ℓ = ℓ' := by
  rw [eq_cross_of_incident hPQ h1 h2, eq_cross_of_incident hPQ h3 h4]

/-- A reflection mapping `u` to `± u₀` when `cf u = cf u₀ ≠ 0`. -/
lemma exists_refl_to (hF2 : (2 : F) ≠ 0) {u u₀ : Fin 3 → F} (h : cf u = cf u₀)
    (hne : cf u ≠ 0) : ∃ d : Fin 3 → F, cf d ≠ 0 ∧ (refl d u = u₀ ∨ refl d u = -u₀) := by
  by_cases hd : cf (u - u₀) = 0
  · refine ⟨u + u₀, ?_, Or.inr ?_⟩
    · rw [cf_add]; rw [cf_sub] at hd
      intro h'
      have : (2 * 2) * cf u = 0 := by linear_combination h' + hd + 2 * h
      exact hne ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hF2 hF2))
    · have hp : pol u (u + u₀) = cf (u + u₀) := by
        rw [pol_add_right, pol_self, cf_add, ← h]; ring
      have hcf : cf (u + u₀) ≠ 0 := by
        rw [cf_add]; rw [cf_sub] at hd
        intro h'
        have : (2 * 2) * cf u = 0 := by linear_combination h' + hd + 2 * h
        exact hne ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hF2 hF2))
      rw [refl_apply, hp, div_self hcf, one_smul]; abel
  · refine ⟨u - u₀, hd, Or.inl ?_⟩
    have hp : pol u (u - u₀) = cf (u - u₀) := by
      rw [pol_sub_right, pol_self, cf_sub, ← h]; ring
    rw [refl_apply, hp, div_self hd, one_smul]; abel

end Lines

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `∑_y χ(y² - n) = -1` for `n ≠ 0`. -/
lemma sum_quadraticChar_sq_sub_const (hF : ringChar F ≠ 2) {n : F} (hn : n ≠ 0) :
    ∑ y : F, quadraticChar F (y ^ 2 - n) = -1 := by
  have key : ∀ g : F → ℤ, ∑ y : F, g (y ^ 2) = ∑ x : F, (quadraticChar F x + 1) * g x := by
    intro g
    rw [← Finset.sum_fiberwise Finset.univ (fun y => y ^ 2) (fun y => g (y ^ 2))]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.1 hy).2]),
      Finset.sum_const, ← quadraticChar_card_sqrts hF x, nsmul_eq_mul]
    congr 3
    ext y; simp
  rw [key (fun x => quadraticChar F (x - n))]
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  have h1 := sum_quadraticChar_mul_sub hF (u := 0) (v := n) (Ne.symm hn)
  simp only [sub_zero] at h1
  rw [h1, sum_quadraticChar_sub hF]; ring

/-- The number of `y` with `y² - n` a non-zero square is `(q - 1) / 2` for a non-square `n`. -/
lemma card_sq_sub_nonsquare (hF : ringChar F ≠ 2) {n : F} (hn : quadraticChar F n = -1) :
    2 * (Finset.univ.filter (fun y : F => quadraticChar F (y ^ 2 - n) = 1)).card + 1 =
      Fintype.card F := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hne : ∀ y : F, y ^ 2 - n ≠ 0 := by
    intro y h
    have : n = y ^ 2 := by linear_combination -h
    rw [this, quadraticChar_sq_one' (by rintro rfl; simp at this; exact hn0 this)] at hn
    norm_num at hn
  have hval : ∀ y : F, quadraticChar F (y ^ 2 - n) =
      2 * (if quadraticChar F (y ^ 2 - n) = 1 then 1 else 0) - 1 := by
    intro y
    rcases quadraticChar_dichotomy (hne y) with h | h <;> simp [h]
  have hsum := sum_quadraticChar_sq_sub_const hF hn0
  rw [Finset.sum_congr rfl (fun y _ => hval y), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  have : (2 * (Finset.univ.filter (fun y : F => quadraticChar F (y ^ 2 - n) = 1)).card + 1 : ℤ)
      = Fintype.card F := by linear_combination hsum
  exact_mod_cast this

/-- The points of the normalized line `z = n x` with `cf` a non-zero square. -/
lemma normal_line_points {n : F} (hn : quadraticChar F n = -1)
    (Q : Point F) :
    (Q = mk F e1 e1_ne_zero ∨ ∃ y : F, quadraticChar F (y ^ 2 - n) = 1 ∧
        Q = mk F ![1, y, n] (by intro h; have := congrFun h 0; simp at this)) ↔
      (n * Q.rep 0 = Q.rep 2 ∧ quadraticChar F (cf Q.rep) = 1) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  constructor
  · rintro (h | ⟨y, hy, h⟩)
    · obtain ⟨c, hc, hrep⟩ := rep_eq_smul_of_eq_mk Q _ _ h
      rw [hrep, quadraticChar_cf_smul hc, cf_e1]
      simp [e1]
    · obtain ⟨c, hc, hrep⟩ := rep_eq_smul_of_eq_mk Q _ _ h
      rw [hrep, quadraticChar_cf_smul hc]
      refine ⟨by simp; ring, ?_⟩
      simpa [cf] using hy
  · rintro ⟨h1, h2⟩
    by_cases h0 : Q.rep 0 = 0
    · left
      have h2' : Q.rep 2 = 0 := by rw [← h1, h0, mul_zero]
      apply eq_mk_of_rep_eq_smul Q e1 e1_ne_zero (Q.rep 1)
      funext i; fin_cases i <;> simp [e1, h0, h2']
    · right
      refine ⟨Q.rep 1 / Q.rep 0, ?_, ?_⟩
      · have : (Q.rep 1 / Q.rep 0) ^ 2 - n = cf Q.rep * (Q.rep 0)⁻¹ ^ 2 := by
          simp only [cf]; rw [← h1]; field_simp
        rw [this, quadraticChar_mul_sq (inv_ne_zero h0), h2]
      · apply eq_mk_of_rep_eq_smul Q _ _ (Q.rep 0)
        funext i; fin_cases i <;> simp [← h1] <;> field_simp

/-- **Converse.**  For odd `q`, the exterior points on a passant form a set of `(q + 1) / 2`
points, any two of which are joined only by passants. -/
theorem exterior_points_of_passant (hF : ringChar F ≠ 2) {ℓ : Line F} (hℓ : IsPassant ℓ) :
    ∃ S : Finset (Point F), (∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ IsExterior P)) ∧
      S.card = (Fintype.card F + 1) / 2 ∧
      ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∀ ℓ' : Line F, Incident P ℓ' → Incident Q ℓ' → IsPassant ℓ' := by
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
  set Y := Finset.univ.filter (fun y : F => quadraticChar F (y ^ 2 - n) = 1) with hY
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
  have hE : mk F e1 e1_ne_zero ∉ Y.image f := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro y _ h
    simp only [f] at h
    rw [mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    have := congrFun hc 0
    simp [e1] at this
  set T := insert (mk F e1 e1_ne_zero) (Y.image f) with hT
  have hTcard : T.card = (Fintype.card F + 1) / 2 := by
    rw [hT, Finset.card_insert_of_notMem hE, Finset.card_image_of_injective _ hfinj]
    have := card_sq_sub_nonsquare hF hnsq
    rw [← hY] at this
    omega
  have hTmem : ∀ Q : Point F, Q ∈ T ↔ (n * Q.rep 0 = Q.rep 2 ∧ quadraticChar F (cf Q.rep) = 1) := by
    intro Q
    rw [← normal_line_points hnsq Q, hT, Finset.mem_insert, Finset.mem_image]
    simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and, f]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, h.symm⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, h.symm⟩
  refine ⟨T.image Φ, ?_, ?_, ?_⟩
  · intro P
    have : P ∈ T.image Φ ↔ Φ P ∈ T := by
      constructor
      · intro h
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h
        rwa [hΦΦ]
      · intro h
        exact Finset.mem_image.2 ⟨Φ P, h, hΦΦ P⟩
    rw [this, hTmem, hinc, isExterior_iff hF, hpolτ]
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
  · intro P hP Q hQ hPQ ℓ' h1 h2
    have hPℓ : Incident P ℓ := by
      obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hP
      rw [hinc, hpolτ]
      obtain ⟨c, hc, hrep⟩ := rep_map_refl hd R
      simp only [Φ] at hrep ⊢
      rw [hrep, map_smul, refl_refl hd, pol_smul_right]
      have := ((hTmem R).1 hR).1
      rw [hpolu₀, ← this, sub_self, mul_zero]
    have hQℓ : Incident Q ℓ := by
      obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hQ
      rw [hinc, hpolτ]
      obtain ⟨c, hc, hrep⟩ := rep_map_refl hd R
      simp only [Φ] at hrep ⊢
      rw [hrep, map_smul, refl_refl hd, pol_smul_right]
      have := ((hTmem R).1 hR).1
      rw [hpolu₀, ← this, sub_self, mul_zero]
    rw [← line_unique hPQ hPℓ hQℓ h1 h2]
    exact hℓ

end CompleteExterior
