module

public import RequestProject.Reflection

/-!
# From geometry to algebra

We relate the geometric notions (tangent lines, passants, exterior points) of the conic
`x z = y²` to the quadratic form `cf` and its polar form `pol`.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace CompleteExterior

section Geom

variable {F : Type*} [Field F]

lemma onConic_iff (P : Point F) : OnConic P ↔ cf P.rep = 0 := by
  unfold OnConic cf; rw [sub_eq_zero, eq_comm]

/-- The coordinate vector of the polar line of `u`. -/
def polarVec (u : Fin 3 → F) : Fin 3 → F := ![-u 2, 2 * u 1, -u 0]

lemma polarVec_dot (u v : Fin 3 → F) : polarVec u ⬝ᵥ v = pol u v := by
  simp [polarVec, pol, dotProduct, Fin.sum_univ_three]; ring

lemma polarVec_ne_zero (hF2 : (2 : F) ≠ 0) {u : Fin 3 → F} (hu : u ≠ 0) : polarVec u ≠ 0 := by
  intro h
  apply hu
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [polarVec] at h0 h1 h2
  funext i; fin_cases i <;> simp [h0, h2, h1.resolve_left hF2]

lemma incident_mk_iff (P : Point F) (w : Fin 3 → F) (hw : w ≠ 0) :
    Incident P (mk F w hw) ↔ w ⬝ᵥ P.rep = 0 := by
  obtain ⟨c, hc, h⟩ := rep_mk_eq_smul w hw
  simp only [Incident, h, smul_dotProduct, smul_eq_mul, mul_eq_zero, hc, false_or]

lemma incident_polar_iff (hF2 : (2 : F) ≠ 0) (P : Point F) {u : Fin 3 → F} (hu : u ≠ 0) :
    Incident P (mk F (polarVec u) (polarVec_ne_zero hF2 hu)) ↔ pol u P.rep = 0 := by
  rw [incident_mk_iff, polarVec_dot]

lemma incident_of_rep (P : Point F) (ℓ : Line F) (v : Fin 3 → F) (hv : v ≠ 0)
    (hP : P = mk F v hv) : Incident P ℓ ↔ ℓ.rep ⬝ᵥ v = 0 := by
  obtain ⟨c, hc, h⟩ := rep_eq_smul_of_eq_mk P v hv hP
  simp only [Incident, h, dotProduct_smul, smul_eq_mul, mul_eq_zero, hc, false_or]

lemma onConic_of_rep (P : Point F) (v : Fin 3 → F) (hv : v ≠ 0)
    (hP : P = mk F v hv) : OnConic P ↔ cf v = 0 := by
  obtain ⟨c, hc, h⟩ := rep_eq_smul_of_eq_mk P v hv hP
  rw [onConic_iff, h, cf_smul]
  simp [hc]

/-- The key identity: if `t` is on the conic and `pol t v = 0`, then `t₀² cf v` is a square. -/
lemma cf_identity {t v : Fin 3 → F} (ht : cf t = 0) (hp : pol t v = 0) :
    t 0 ^ 2 * cf v = (t 0 * v 1 - t 1 * v 0) ^ 2 := by
  simp only [cf, pol] at ht hp ⊢
  linear_combination (t 0 * v 0) * hp + (-(v 0 ^ 2)) * ht

/-- The only point of the conic on the polar line of a point `t` of the conic is `t` itself. -/
lemma eq_of_polar_of_cf {t x : Fin 3 → F} (ht0 : t ≠ 0) (ht : cf t = 0)
    (hp : pol t x = 0) (hx : cf x = 0) : ∃ c : F, x = c • t := by
  have hid := cf_identity ht hp
  rw [hx, mul_zero, eq_comm, sq_eq_zero_iff, sub_eq_zero] at hid
  simp only [cf, pol] at ht hp hx
  by_cases h0 : t 0 = 0
  · have h1 : t 1 = 0 := by simpa [h0] using ht
    have h2 : t 2 ≠ 0 := by
      intro h2; apply ht0; funext i; fin_cases i <;> simp [h0, h1, h2]
    have hx0 : x 0 = 0 := by
      rw [h0, h1] at hp; simp at hp; exact hp.resolve_left h2
    have hx1 : x 1 = 0 := by simpa [hx0] using hx
    refine ⟨x 2 / t 2, ?_⟩
    funext i; fin_cases i <;> simp [h0, h1, hx0, hx1]
    field_simp
  · have h' : t 0 * x 2 = 2 * t 1 * x 1 - t 2 * x 0 := by linear_combination -hp
    have hx2' : t 0 * (t 0 * x 2 - t 2 * x 0) = 0 := by
      linear_combination (t 0) * h' + (2 * t 1) * hid + (2 * x 0) * ht
    have hx2 : t 0 * x 2 = t 2 * x 0 := sub_eq_zero.1 ((mul_eq_zero.1 hx2').resolve_left h0)
    refine ⟨x 0 / t 0, ?_⟩
    funext i; fin_cases i
    · simp; field_simp
    · simp; field_simp; linear_combination hid
    · simp; field_simp; linear_combination hx2

/-- The polar line of a point `t` of the conic is a tangent line. -/
lemma isTangent_polar (hF2 : (2 : F) ≠ 0) {t : Fin 3 → F} (ht0 : t ≠ 0) (ht : cf t = 0) :
    IsTangent (mk F (polarVec t) (polarVec_ne_zero hF2 ht0)) ∧
      ∀ Q : Point F, Incident Q (mk F (polarVec t) (polarVec_ne_zero hF2 ht0)) →
        OnConic Q → Q = mk F t ht0 := by
  have huniq : ∀ Q : Point F, Incident Q (mk F (polarVec t) (polarVec_ne_zero hF2 ht0)) →
      OnConic Q → Q = mk F t ht0 := by
    intro Q hQ hQc
    rw [incident_polar_iff hF2 Q ht0] at hQ
    rw [onConic_iff] at hQc
    obtain ⟨c, hc⟩ := eq_of_polar_of_cf ht0 ht hQ hQc
    exact eq_mk_of_rep_eq_smul Q t ht0 c hc
  refine ⟨⟨mk F t ht0, ⟨?_, ?_⟩, fun Q hQ => huniq Q hQ.1 hQ.2⟩, huniq⟩
  · rw [incident_of_rep _ _ t ht0 rfl]
    obtain ⟨c, hc, h⟩ := rep_mk_eq_smul (polarVec t) (polarVec_ne_zero hF2 ht0)
    rw [h, smul_dotProduct, polarVec_dot, pol_self, ht]; simp
  · rw [onConic_of_rep _ t ht0 rfl]; exact ht

lemma cf_smul_add_smul (a b : F) (v w : Fin 3 → F) :
    cf (a • v + b • w) = a ^ 2 * cf v + a * b * pol v w + b ^ 2 * cf w := by
  simp [cf, pol]; ring

end Geom

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A point is exterior iff `cf` of its coordinates is a non-zero square. -/
theorem isExterior_iff (hF : ringChar F ≠ 2) (P : Point F) :
    IsExterior P ↔ quadraticChar F (cf P.rep) = 1 := by
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set v := P.rep with hv
  constructor
  · rintro ⟨hnot, ℓ₁, -, -, ⟨T, ⟨hTi, hTc⟩, hTu⟩, -, hi₁, -⟩
    rw [onConic_iff] at hnot hTc
    have hcf0 : cf v ≠ 0 := hnot
    set t := T.rep with htdef
    have ht0 : t ≠ 0 := T.rep_nonzero
    -- the polar of `t` passes through `P`
    have hpol : pol t v = 0 := by
      by_contra hp
      set lam := - cf v / pol t v with hlam
      set w := v + lam • t with hw
      have hcfw : cf w = 0 := by
        rw [hw, cf_add_smul, hTc, pol_comm v t, hlam]; field_simp; ring
      have hw0 : w ≠ 0 := by
        intro h
        have : v = (-lam) • t := by rw [neg_smul, eq_neg_iff_add_eq_zero, ← hw, h]
        apply hcf0; rw [this, cf_smul, hTc, mul_zero]
      have hwi : ℓ₁.rep ⬝ᵥ w = 0 := by
        rw [hw, dotProduct_add, dotProduct_smul, smul_eq_mul]
        simp only [Incident] at hTi hi₁
        rw [← hv] at hi₁; rw [← htdef] at hTi; rw [hi₁, hTi, mul_zero, add_zero]
      have hQ := hTu (mk F w hw0) ⟨(incident_of_rep _ _ w hw0 rfl).2 hwi,
        (onConic_of_rep _ w hw0 rfl).2 hcfw⟩
      rw [← mk_rep T, mk_eq_mk_iff'] at hQ
      obtain ⟨a, ha⟩ := hQ
      apply hcf0
      have ha' : a • t = w := ha
      have : v = (a - lam) • t := by rw [sub_smul, ha', hw]; abel
      rw [this, cf_smul, hTc, mul_zero]
    have hid := cf_identity hTc hpol
    rw [quadraticChar_one_iff_isSquare hcf0]
    by_cases h0 : t 0 = 0
    · have h1 : t 1 = 0 := by
        have := hTc; simp only [cf, h0, zero_mul, sub_zero] at this
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      have h2 : t 2 ≠ 0 := by
        intro h2; apply ht0; funext i; fin_cases i <;> simp [h0, h1, h2]
      have hv0 : v 0 = 0 := by
        have := hpol; simp only [pol, h0, h1] at this; simp at this
        exact this.resolve_left h2
      exact ⟨v 1, by simp only [cf, hv0, zero_mul, sub_zero]; ring⟩
    · exact ⟨(t 0 * v 1 - t 1 * v 0) / t 0, by field_simp; linear_combination hid⟩
  · intro h
    have hcf0 : cf v ≠ 0 := by intro h0; rw [h0] at h; simp at h
    refine ⟨by rw [onConic_iff]; exact hcf0, ?_⟩
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare hcf0).1 h
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hcf0 hr
    -- two distinct points of the conic whose polars pass through `P`
    obtain ⟨t, t', ht0, ht'0, htc, ht'c, htp, ht'p, htt'⟩ : ∃ t t' : Fin 3 → F,
        ∃ (ht0 : t ≠ 0) (ht'0 : t' ≠ 0), cf t = 0 ∧ cf t' = 0 ∧ pol t v = 0 ∧ pol t' v = 0 ∧
          mk F t ht0 ≠ mk F t' ht'0 := by
      by_cases hv0 : v 0 = 0
      · have hv1 : v 1 ≠ 0 := by
          intro hv1; apply hcf0; simp [cf, hv0, hv1]
        refine ⟨![0, 0, 1], ![1, v 2 / (2 * v 1), (v 2 / (2 * v 1)) ^ 2], ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · intro h; have := congrFun h 2; simp at this
        · intro h; have := congrFun h 0; simp at this
        · simp [cf]
        · simp [cf]
        · simp [pol, hv0]
        · simp [pol, hv0]; field_simp; ring
        · rw [Ne, mk_eq_mk_iff']
          rintro ⟨a, ha⟩
          have h0 := congrFun ha 0
          have h2 := congrFun ha 2
          simp at h0 h2
          rw [h0] at h2; simp at h2
      · set s := (v 1 + r) / v 0
        set s' := (v 1 - r) / v 0
        refine ⟨![1, s, s ^ 2], ![1, s', s' ^ 2], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro h; have := congrFun h 0; simp at this
        · intro h; have := congrFun h 0; simp at this
        · simp [cf]
        · simp [cf]
        · simp only [cf] at hr
          simp [pol, s]; field_simp; linear_combination hr
        · simp only [cf] at hr
          simp [pol, s']; field_simp; linear_combination hr
        · rw [Ne, mk_eq_mk_iff']
          rintro ⟨a, ha⟩
          have h0 := congrFun ha 0
          have h1 := congrFun ha 1
          simp at h0 h1
          subst h0
          simp only [one_mul, s, s'] at h1
          rw [div_left_inj' hv0] at h1
          have : 2 * r = 0 := by linear_combination -h1
          exact hr0 ((mul_eq_zero.1 this).resolve_left hF2)
    obtain ⟨hT, hTu⟩ := isTangent_polar hF2 ht0 htc
    obtain ⟨hT', hT'u⟩ := isTangent_polar hF2 ht'0 ht'c
    refine ⟨_, _, ?_, hT, hT', (incident_polar_iff hF2 P ht0).2 htp,
      (incident_polar_iff hF2 P ht'0).2 ht'p⟩
    intro heq
    apply htt'
    have hinc : Incident (mk F t ht0) (mk F (polarVec t') (polarVec_ne_zero hF2 ht'0)) := by
      rw [← heq, incident_polar_iff hF2 _ ht0]
      obtain ⟨c, hc, h⟩ := rep_mk_eq_smul t ht0
      rw [h, pol_smul_right, pol_self, htc, mul_zero, mul_zero]
    exact hT'u _ hinc ((onConic_of_rep _ t ht0 rfl).2 htc)

/-- If every line through two distinct points `P, Q` (with `P` off the conic) is a passant,
then `disc P Q` is a non-square. -/
theorem disc_of_passant (hF : ringChar F ≠ 2) {P Q : Point F} (hPQ : P ≠ Q)
    (hP : cf P.rep ≠ 0)
    (hpass : ∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassant ℓ) :
    quadraticChar F (disc P.rep Q.rep) = -1 := by
  set v := P.rep with hv
  set w := Q.rep with hw
  have hli : LinearIndependent F ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases hs : s = 0
    · subst hs
      simp only [zero_smul, zero_add, smul_eq_zero] at hst
      exact ⟨rfl, hst.resolve_right Q.rep_nonzero⟩
    · exfalso; apply hPQ
      rw [← mk_rep P, ← mk_rep Q, mk_eq_mk_iff']
      refine ⟨-t / s, ?_⟩
      have h1 : s • v = (-t) • w := by rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hst
      have : v = (-t / s) • w := by
        rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [← hv, ← hw, this]
  have hcross : crossProduct v w ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.2 hli
  set ℓ : Line F := mk F (crossProduct v w) hcross
  have hPℓ : Incident P ℓ := by
    rw [incident_mk_iff, dotProduct_comm, ← hv, dot_self_cross]
  have hQℓ : Incident Q ℓ := by
    rw [incident_mk_iff, dotProduct_comm, ← hw, dot_cross_self]
  have hpas := hpass ℓ hPℓ hQℓ
  rw [quadraticChar_neg_one_iff_not_isSquare]
  rintro ⟨r, hr⟩
  set X := (r - pol v w) • v + (2 * cf v) • w with hX
  have hX0 : X ≠ 0 := by
    intro h
    rw [LinearIndependent.pair_iff] at hli
    have := (hli _ _ h).2
    exact hP (by
      have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
      exact (mul_eq_zero.1 this).resolve_left h2)
  have hXc : cf X = 0 := by
    rw [hX, cf_smul_add_smul]
    simp only [disc] at hr
    linear_combination (-cf v) * hr
  have hXℓ : ℓ.rep ⬝ᵥ X = 0 := by
    obtain ⟨c, hc, h⟩ := rep_mk_eq_smul (crossProduct v w) hcross
    rw [h, hX, smul_dotProduct, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_comm _ v, dotProduct_comm _ w, dot_self_cross, dot_cross_self]
    simp
  exact hpas (mk F X hX0) ((incident_of_rep _ _ X hX0 rfl).2 hXℓ)
    ((onConic_of_rep _ X hX0 rfl).2 hXc)

end CompleteExterior
