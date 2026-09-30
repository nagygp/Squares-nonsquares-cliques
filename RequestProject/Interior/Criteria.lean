module

public import RequestProject.Main
public import RequestProject.Interior.Defs

/-!
# Algebraic criteria for interior points and passants of `x y = z²`

The coordinate swap `(x, y, z) ↦ (x, z, y)` maps the conic `x y = z²` onto the conic
`x z = y²` used in the exterior case and preserves incidence.  Transporting the criteria proved
there we obtain:

* `P` is an interior point iff `z² - x y` is a non-square (`isInteriorXY_mk_iff`);
* for distinct `P, Q` with `P` off the conic, every line through `P` and `Q` is a passant iff
  the discriminant `disc (sw P) (sw Q)` is a non-square (`passantXY_mk_iff`).
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace InteriorPassant

open CompleteExterior

section Swap

variable {F : Type*} [Field F]

/-- The coordinate swap `(x, y, z) ↦ (x, z, y)`. -/
def sw (v : Fin 3 → F) : Fin 3 → F := ![v 0, v 2, v 1]

omit [Field F] in
lemma sw_sw (v : Fin 3 → F) : sw (sw v) = v := by
  funext i; fin_cases i <;> rfl

lemma sw_ne_zero {v : Fin 3 → F} (hv : v ≠ 0) : sw v ≠ 0 := by
  intro h; apply hv; rw [← sw_sw v, h]; funext i; fin_cases i <;> rfl

lemma sw_smul (c : F) (v : Fin 3 → F) : sw (c • v) = c • sw v := by
  funext i; fin_cases i <;> rfl

lemma dot_sw (a b : Fin 3 → F) : sw a ⬝ᵥ sw b = a ⬝ᵥ b := by
  simp [sw, dotProduct, Fin.sum_univ_three]; ring

lemma cf_sw (v : Fin 3 → F) : cf (sw v) = v 2 ^ 2 - v 0 * v 1 := by
  simp [cf, sw]

/-- The coordinate swap acting on points (and lines). -/
noncomputable def swapP (P : Point F) : Point F := mk F (sw P.rep) (sw_ne_zero P.rep_nonzero)

lemma swapP_mk (v : Fin 3 → F) (hv : v ≠ 0) :
    swapP (mk F v hv) = mk F (sw v) (sw_ne_zero hv) := by
  obtain ⟨c, hc, h⟩ := rep_mk_eq_smul v hv
  unfold swapP
  rw [mk_eq_mk_iff']
  exact ⟨c, by simp only [h, sw_smul]⟩

lemma swapP_swapP (P : Point F) : swapP (swapP P) = P := by
  rw [show swapP (swapP P) = swapP (mk F (sw P.rep) (sw_ne_zero P.rep_nonzero)) from rfl,
    swapP_mk]
  simp only [sw_sw, mk_rep]

/-- The coordinate swap as a bijection of the points (and lines). -/
noncomputable def swapEquiv : Point F ≃ Point F where
  toFun := swapP
  invFun := swapP
  left_inv := swapP_swapP
  right_inv := swapP_swapP

lemma swapP_rep (P : Point F) : ∃ c : F, c ≠ 0 ∧ (swapP P).rep = c • sw P.rep :=
  rep_mk_eq_smul _ _

lemma incident_swapP (P ℓ : Point F) : Incident (swapP P) (swapP ℓ) ↔ Incident P ℓ := by
  obtain ⟨c, hc, h⟩ := swapP_rep P
  obtain ⟨d, hd, h'⟩ := swapP_rep ℓ
  simp only [Incident, h, h', smul_dotProduct, dotProduct_smul, dot_sw, smul_eq_mul,
    mul_eq_zero, hc, hd, false_or]

lemma onConic_swapP (P : Point F) : OnConic (swapP P) ↔ OnConicXY P := by
  obtain ⟨c, hc, h⟩ := swapP_rep P
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [onConic_iff, h, cf_smul, cf_sw, OnConicXY, mul_eq_zero, or_iff_right hc2, sub_eq_zero,
    eq_comm]

lemma forall_swapP {p : Point F → Prop} : (∀ P, p P) ↔ ∀ P, p (swapP P) :=
  ⟨fun h P => h _, fun h P => by simpa [swapP_swapP] using h (swapP P)⟩

lemma isTangent_swapP (ℓ : Line F) : IsTangent (swapP ℓ) ↔ IsTangentXY ℓ := by
  unfold IsTangent IsTangentXY
  symm
  refine (swapEquiv (F := F)).existsUnique_congr ?_
  intro P
  change _ ↔ Incident (swapP P) (swapP ℓ) ∧ OnConic (swapP P)
  rw [incident_swapP, onConic_swapP]

lemma isPassant_swapP (ℓ : Line F) : IsPassant (swapP ℓ) ↔ IsPassantXY ℓ := by
  unfold IsPassant IsPassantXY
  rw [forall_swapP]
  simp only [incident_swapP, onConic_swapP]

lemma isInteriorXY_iff_swapP (P : Point F) :
    IsInteriorXY P ↔ (¬ OnConic (swapP P) ∧ ∀ ℓ : Line F, Incident (swapP P) ℓ → ¬ IsTangent ℓ) := by
  unfold IsInteriorXY
  rw [onConic_swapP]
  refine and_congr Iff.rfl ?_
  conv_rhs => rw [forall_swapP]
  simp only [incident_swapP, isTangent_swapP]

end Swap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A point off the conic `x z = y²` lying on a tangent has `cf` a non-zero square. -/
lemma quadraticChar_cf_of_tangent {P : Point F} (hnot : ¬ OnConic P) {ℓ₁ : Line F}
    (hT : IsTangent ℓ₁) (hi₁ : Incident P ℓ₁) : quadraticChar F (cf P.rep) = 1 := by
  obtain ⟨T, ⟨hTi, hTc⟩, hTu⟩ := hT
  set v := P.rep with hv
  rw [onConic_iff] at hnot hTc
  have hcf0 : cf v ≠ 0 := hnot
  set t := T.rep with htdef
  have ht0 : t ≠ 0 := T.rep_nonzero
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

/-- A point is interior to `x z = y²` iff `cf` of its coordinates is a non-square. -/
theorem isInterior_iff (hF : ringChar F ≠ 2) (P : Point F) :
    (¬ OnConic P ∧ ∀ ℓ : Line F, Incident P ℓ → ¬ IsTangent ℓ) ↔
      quadraticChar F (cf P.rep) = -1 := by
  constructor
  · rintro ⟨hnot, hnt⟩
    have hcf0 : cf P.rep ≠ 0 := by rwa [onConic_iff] at hnot
    rcases quadraticChar_dichotomy hcf0 with h | h
    · obtain ⟨-, ℓ₁, -, -, hT, -, hi, -⟩ := (isExterior_iff hF P).2 h
      exact absurd hT (hnt ℓ₁ hi)
    · exact h
  · intro h
    have hcf0 : cf P.rep ≠ 0 := by intro h0; rw [h0] at h; simp at h
    have hnot : ¬ OnConic P := by rwa [onConic_iff]
    refine ⟨hnot, fun ℓ hi hT => ?_⟩
    have := quadraticChar_cf_of_tangent hnot hT hi
    rw [this] at h; norm_num at h

/-- **Criterion for interior points** of `x y = z²`: the point `(x : y : z)` is interior iff
`z² - x y` is a non-square. -/
theorem isInteriorXY_mk_iff (hF : ringChar F ≠ 2) (v : Fin 3 → F) (hv : v ≠ 0) :
    IsInteriorXY (mk F v hv) ↔ ¬ IsSquare (cf (sw v)) := by
  rw [isInteriorXY_iff_swapP, isInterior_iff hF, swapP_mk]
  obtain ⟨c, hc, h⟩ := rep_mk_eq_smul (sw v) (sw_ne_zero hv)
  rw [h, quadraticChar_cf_smul hc, quadraticChar_neg_one_iff_not_isSquare]

/-- **Criterion for passants** through two points of `PG(2, q)` (for the conic `x y = z²`). -/
theorem passantXY_mk_iff (hF : ringChar F ≠ 2) (v w : Fin 3 → F) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : mk F v hv ≠ mk F w hw) (hcf : cf (sw v) ≠ 0) :
    (∀ ℓ : Line F, Incident (mk F v hv) ℓ → Incident (mk F w hw) ℓ → IsPassantXY ℓ) ↔
      ¬ IsSquare (disc (sw v) (sw w)) := by
  have hne : swapP (mk F v hv) ≠ swapP (mk F w hw) := fun h =>
    hvw (by rw [← swapP_swapP (mk F v hv), h, swapP_swapP])
  obtain ⟨c, hc, h⟩ := swapP_rep (mk F v hv)
  obtain ⟨d, hd, h'⟩ := swapP_rep (mk F w hw)
  obtain ⟨c', hc', h1⟩ := rep_mk_eq_smul v hv
  obtain ⟨d', hd', h2⟩ := rep_mk_eq_smul w hw
  have hcf' : cf (swapP (mk F v hv)).rep ≠ 0 := by
    rw [h, h1, sw_smul, smul_smul, cf_smul]; exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hc hc')) hcf
  have key := passant_iff_disc hF hne hcf'
  rw [h, h', h1, h2, sw_smul, sw_smul, smul_smul, smul_smul,
    quadraticChar_disc_smul (mul_ne_zero hc hc') (mul_ne_zero hd hd'),
    quadraticChar_neg_one_iff_not_isSquare] at key
  rw [← key]
  conv_rhs => rw [forall_swapP]
  simp only [incident_swapP, isPassant_swapP]

end InteriorPassant
