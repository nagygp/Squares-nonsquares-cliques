module

public import RequestProject.Normalized

/-!
# Reduction to the normalized case

Using a reflection (an isometry of the quadratic form `cf`, hence a collineation preserving the
conic) we move an arbitrary point of a complete exterior set to `(0 : 1 : 0)`, and deduce the
algebraic form of the main theorem in general.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace CompleteExterior

section Refl

variable {F : Type*} [Field F]

lemma pol_sub_right (u v w : Fin 3 → F) : pol u (v - w) = pol u v - pol u w := by
  simp [pol]; ring

lemma pol_add_right (u v w : Fin 3 → F) : pol u (v + w) = pol u v + pol u w := by
  simp [pol]; ring

/-- The reflection in the vector `d` with respect to the quadratic form `cf`. -/
def refl (d : Fin 3 → F) : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun x := x - (pol x d / cf d) • d
  map_add' x y := by rw [pol_add_left, add_div, add_smul]; abel
  map_smul' c x := by
    rw [pol_smul_left, mul_div_assoc, mul_smul]
    simp [smul_sub]

lemma refl_apply (d x : Fin 3 → F) : refl d x = x - (pol x d / cf d) • d := rfl

variable {d : Fin 3 → F}

lemma pol_refl_left (hd : cf d ≠ 0) (x : Fin 3 → F) : pol (refl d x) d = - pol x d := by
  rw [refl_apply, pol_sub_left, pol_smul_left, pol_self]
  field_simp; ring

lemma refl_refl (hd : cf d ≠ 0) (x : Fin 3 → F) : refl d (refl d x) = x := by
  rw [refl_apply (x := refl d x), pol_refl_left hd, refl_apply, neg_div, neg_smul,
    sub_neg_eq_add, sub_add_cancel]

lemma refl_injective (hd : cf d ≠ 0) : Function.Injective (refl d) :=
  Function.LeftInverse.injective (refl_refl hd)

lemma cf_refl (hd : cf d ≠ 0) (x : Fin 3 → F) : cf (refl d x) = cf x := by
  rw [refl_apply, sub_eq_add_neg, ← neg_smul, cf_add_smul]
  field_simp; ring

lemma pol_refl (hd : cf d ≠ 0) (x y : Fin 3 → F) : pol (refl d x) (refl d y) = pol x y := by
  simp only [refl_apply, pol_sub_left, pol_sub_right, pol_smul_left, pol_smul_right, pol_self,
    pol_comm d y]
  field_simp; ring

lemma pol_refl_swap (hd : cf d ≠ 0) (x y : Fin 3 → F) : pol (refl d x) y = pol x (refl d y) := by
  conv_lhs => rw [← refl_refl hd y]
  rw [pol_refl hd]

lemma disc_refl (hd : cf d ≠ 0) (x y : Fin 3 → F) :
    disc (refl d x) (refl d y) = disc x y := by
  simp only [disc, pol_refl hd, cf_refl hd]

/-- The induced map on points. -/
lemma rep_map_refl (hd : cf d ≠ 0) (P : ℙ F (Fin 3 → F)) :
    ∃ c : F, c ≠ 0 ∧ (map (refl d) (refl_injective hd) P).rep = c • refl d P.rep := by
  have h : map (refl d) (refl_injective hd) P =
      mk F (refl d P.rep) ((refl_injective hd).ne P.rep_nonzero |>.trans_eq (map_zero _)) := by
    conv_lhs => rw [← mk_rep P]
    rfl
  rw [h]
  exact rep_mk_eq_smul _ _

lemma map_refl_map_refl (hd : cf d ≠ 0) (P : ℙ F (Fin 3 → F)) :
    map (refl d) (refl_injective hd) (map (refl d) (refl_injective hd) P) = P := by
  induction P using Projectivization.ind with
  | h v hv => simp only [map_mk, refl_refl hd]

end Refl

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The algebraic form of the main theorem.**  Assume every good pairing is linear (true for
`q ≡ 1 (mod 4)` by `goodPairing_eq_div`).  If `S` is a set of `(q + 1) / 2` points with
`cf` a non-zero square (exterior points), such that `disc` is a non-square for any two of them
(the joining line is a passant), then there is a vector `u` whose polar line `pol u · = 0` is
anisotropic (a passant), and `S` is exactly the set of exterior points on this line. -/
theorem alg_core (hF : ringChar F ≠ 2) (hGP : PairingsLinear F)
    (S : Finset (ℙ F (Fin 3 → F))) (hcard : S.card = (Fintype.card F + 1) / 2)
    (hext : ∀ P ∈ S, quadraticChar F (cf P.rep) = 1)
    (hdisc : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → quadraticChar F (disc P.rep Q.rep) = -1) :
    ∃ u : Fin 3 → F, u ≠ 0 ∧ (∀ v : Fin 3 → F, v ≠ 0 → pol u v = 0 → cf v ≠ 0) ∧
      ∀ P : ℙ F (Fin 3 → F), P ∈ S ↔ (pol u P.rep = 0 ∧ quadraticChar F (cf P.rep) = 1) := by
  classical
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  -- pick a point of `S`
  have hne : S.Nonempty := by
    rw [← Finset.card_pos, hcard]
    have := Fintype.card_pos (α := F); omega
  obtain ⟨P₀, hP₀⟩ := hne
  set v := P₀.rep with hv
  have hcf0 : cf v ≠ 0 := by intro h; have := hext P₀ hP₀; rw [← hv, h] at this; simp at this
  obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare hcf0).1 (hext P₀ hP₀)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hcf0 hr
  set v' := r⁻¹ • v with hv'
  have hcfv' : cf v' = 1 := by
    rw [hv', cf_smul, hr]; field_simp
  -- a reflection moving `v'` to `± e1`
  obtain ⟨d, hd, hdv⟩ : ∃ d : Fin 3 → F, cf d ≠ 0 ∧ (refl d v' = e1 ∨ refl d v' = -e1) := by
    by_cases h : cf (v' - e1) = 0
    · refine ⟨v' + e1, ?_, Or.inr ?_⟩
      · rw [cf_add]; rw [cf_sub, hcfv', cf_e1] at h
        rw [hcfv', cf_e1]
        intro h'
        have : (4 : F) = 0 := by linear_combination h' + h
        have h4 : (4 : F) = 2 * 2 := by norm_num
        rw [h4] at this
        exact hF2 ((mul_eq_zero.1 this).elim id id)
      · have hp : pol v' (v' + e1) = cf (v' + e1) := by
          rw [pol_add_right, pol_self, cf_add, hcfv', cf_e1]; ring
        rw [refl_apply, hp, div_self (by
          rw [cf_add]; rw [cf_sub, hcfv', cf_e1] at h
          rw [hcfv', cf_e1]
          intro h'
          have : (4 : F) = 0 := by linear_combination h' + h
          have h4 : (4 : F) = 2 * 2 := by norm_num
          rw [h4] at this
          exact hF2 ((mul_eq_zero.1 this).elim id id)), one_smul]
        abel
    · refine ⟨v' - e1, h, Or.inl ?_⟩
      have hp : pol v' (v' - e1) = cf (v' - e1) := by
        rw [pol_sub_right, pol_self, cf_sub, hcfv', cf_e1]; ring
      rw [refl_apply, hp, div_self h, one_smul]
      abel
  set τ := refl d with hτ
  have hτinj : Function.Injective τ := refl_injective hd
  let Φ : ℙ F (Fin 3 → F) → ℙ F (Fin 3 → F) := map τ hτinj
  have hΦΦ : ∀ P, Φ (Φ P) = P := map_refl_map_refl hd
  have hΦinj : Function.Injective Φ := Function.LeftInverse.injective hΦΦ
  set S' := S.image Φ with hS'
  have hS'card : S'.card = (Fintype.card F + 1) / 2 := by
    rw [hS', Finset.card_image_of_injective _ hΦinj, hcard]
  have hmemS' : ∀ P, Φ P ∈ S' ↔ P ∈ S := by
    intro P
    constructor
    · intro h
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.1 h
      rwa [← hΦinj hQP]
    · exact Finset.mem_image_of_mem Φ
  have hext' : ∀ P ∈ S', quadraticChar F (cf P.rep) = 1 := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨c, hc, hrep⟩ := rep_map_refl hd Q
    simp only [Φ]
    rw [hrep, quadraticChar_cf_smul hc, cf_refl hd]
    exact hext Q hQ
  have hdisc' : ∀ P ∈ S', ∀ Q ∈ S', P ≠ Q → quadraticChar F (disc P.rep Q.rep) = -1 := by
    intro P hP Q hQ hPQ
    obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨Q₁, hQ₁, rfl⟩ := Finset.mem_image.1 hQ
    obtain ⟨c, hc, hrepP⟩ := rep_map_refl hd P₁
    obtain ⟨c', hc', hrepQ⟩ := rep_map_refl hd Q₁
    simp only [Φ]
    rw [hrepP, hrepQ, quadraticChar_disc_smul hc hc', disc_refl hd]
    exact hdisc P₁ hP₁ Q₁ hQ₁ (fun h => hPQ (h ▸ rfl))
  have hE' : mk F e1 e1_ne_zero ∈ S' := by
    have : Φ P₀ = mk F e1 e1_ne_zero := by
      simp only [Φ]
      conv_lhs => rw [← mk_rep P₀]
      rw [map_mk, mk_eq_mk_iff']
      have hvv : P₀.rep = r • v' := by rw [hv', smul_smul, mul_inv_cancel₀ hr0, one_smul]
      rw [hvv, map_smul]
      rcases hdv with h | h
      · exact ⟨r, by rw [h]⟩
      · exact ⟨-r, by rw [h, smul_neg, neg_smul]⟩
    rw [← this]; exact Finset.mem_image_of_mem Φ hP₀
  obtain ⟨n, hn, hS'n⟩ := alg_core_normalized hF hGP S' hS'card hext' hdisc' hE'
  set u' : Fin 3 → F := ![1, 0, -n] with hu'
  have hpolu' : ∀ w : Fin 3 → F, pol u' w = n * w 0 - w 2 := by
    intro w; simp [pol, hu']; ring
  refine ⟨τ u', ?_, ?_, ?_⟩
  · intro h
    have : u' = 0 := by rw [← refl_refl hd u', ← hτ, h, map_zero]
    have := congrFun this 0
    simp [hu'] at this
  · intro w hw hpw
    rw [pol_refl_swap hd, hpolu', sub_eq_zero] at hpw
    rw [← cf_refl hd w]
    set z := τ w with hz
    have hz0 : z ≠ 0 := fun h => hw (hτinj (by rw [← hz, h, map_zero]))
    intro hcf
    simp only [cf, ← hpw] at hcf
    by_cases h0 : z 0 = 0
    · have h1 : z 1 = 0 := by rw [h0] at hcf; simpa using hcf
      have h2 : z 2 = 0 := by rw [← hpw, h0, mul_zero]
      apply hz0
      funext i; fin_cases i <;> simp [h0, h1, h2]
    · have : IsSquare n := ⟨z 1 / z 0, by field_simp; linear_combination -hcf⟩
      exact (quadraticChar_neg_one_iff_not_isSquare.1 hn) this
  · intro P
    rw [← hmemS', hS'n]
    obtain ⟨c, hc, hrep⟩ := rep_map_refl hd P
    simp only [Φ]
    rw [hrep, quadraticChar_cf_smul hc, cf_refl hd, pol_refl_swap hd, hpolu']
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have : c * (n * (τ P.rep) 0 - (τ P.rep) 2) = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_left hc
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination c * h1, h2⟩

end CompleteExterior
