module

public import RequestProject.Converse

/-!
# The hypothesis `q ≡ 1 (mod 4)` cannot be dropped

In the final remarks the paper points out that for `q ≡ 3 (mod 4)` there are complete exterior
sets which are not the set of exterior points of a passant; e.g. for `q = 7` there is one
consisting of `4` points, no three collinear.  We verify such an example.

For this we first prove the converse of `disc_of_passant`: if `disc P Q` is a non-square, then
every line through `P` and `Q` is a passant.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace CompleteExterior

section Span

variable {F : Type*} [Field F]

/-- A vector orthogonal to `v × w` (with `v, w` independent) lies in the span of `v` and `w`. -/
lemma exists_eq_add_of_dot_cross {v w x : Fin 3 → F} (hli : LinearIndependent F ![v, w])
    (hx : crossProduct v w ⬝ᵥ x = 0) : ∃ a b : F, x = a • v + b • w := by
  have hdet : Matrix.det ![x, v, w] = 0 := by
    rw [← triple_product_eq_det, dotProduct_comm]; exact hx
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hlin : c 0 • x + c 1 • v + c 2 • w = 0 := by
    funext j
    have := congrFun hc j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this
  rw [LinearIndependent.pair_iff] at hli
  have h0 : c 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hlin
    obtain ⟨h1, h2⟩ := hli _ _ hlin
    apply hc0; funext i; fin_cases i <;> simp [h0, h1, h2]
  refine ⟨-c 1 / c 0, -c 2 / c 0, ?_⟩
  have : c 0 • x = (-c 1) • v + (-c 2) • w := by
    rw [neg_smul, neg_smul, ← neg_add, eq_neg_iff_add_eq_zero, ← add_assoc]; exact hlin
  rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← this, smul_smul,
    inv_mul_cancel₀ h0, one_smul]

end Span

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- If `disc P Q` is a non-square, then every line through `P` and `Q` is a passant. -/
theorem passant_of_disc {P Q : Point F} (hPQ : P ≠ Q)
    (h : quadraticChar F (disc P.rep Q.rep) = -1) :
    ∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassant ℓ := by
  intro ℓ hP hQ X hX hXc
  set v := P.rep
  set w := Q.rep
  have hli := linearIndependent_rep_of_ne hPQ
  rw [eq_cross_of_incident hPQ hP hQ, incident_mk_iff] at hX
  obtain ⟨a, b, hab⟩ := exists_eq_add_of_dot_cross hli hX
  rw [onConic_iff, hab, cf_smul_add_smul] at hXc
  rw [quadraticChar_neg_one_iff_not_isSquare] at h
  apply h
  by_cases hb : b = 0
  · -- then `cf v = 0` and `disc v w` is a square
    have ha : a ≠ 0 := by
      intro ha; apply X.rep_nonzero; rw [hab, ha, hb, zero_smul, zero_smul, add_zero]
    rw [hb] at hXc
    have hcf : cf v = 0 := by
      have : a ^ 2 * cf v = 0 := by linear_combination hXc
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 ha)
    exact ⟨pol v w, by simp only [disc, hcf]; ring⟩
  · refine ⟨(2 * a * cf v + b * pol v w) / b, ?_⟩
    simp only [disc]
    field_simp
    linear_combination (-4 * cf v) * hXc

/-- **Characterization of passants** (the lemma in the proof of the paper, in quadratic-form
language): for two distinct points `P, Q` with `P` off the conic, the line `PQ` is a passant iff
`disc P Q = pol(P, Q)² - 4 cf(P) cf(Q)` is a non-square.  For the exterior points with labels
`(a, b)` and `(c, d)` one has `disc = 16 (a - c)(a - d)(b - c)(b - d)` (see `disc_lab`). -/
theorem passant_iff_disc (hF : ringChar F ≠ 2) {P Q : Point F} (hPQ : P ≠ Q)
    (hP : cf P.rep ≠ 0) :
    (∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassant ℓ) ↔
      quadraticChar F (disc P.rep Q.rep) = -1 :=
  ⟨disc_of_passant hF hPQ hP, passant_of_disc hPQ⟩

end CompleteExterior

namespace CompleteExterior.Q7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma disc_12 : ¬ IsSquare (disc (![0, 1, 0] : Fin 3 → ZMod 7) ![1, 1, 6]) := by
  simp only [disc, pol, cf]; simp; decide

lemma disc_13 : ¬ IsSquare (disc (![0, 1, 0] : Fin 3 → ZMod 7) ![1, 2, 3]) := by
  simp only [disc, pol, cf]; simp; decide

lemma disc_14 : ¬ IsSquare (disc (![0, 1, 0] : Fin 3 → ZMod 7) ![1, 4, 5]) := by
  simp only [disc, pol, cf]; simp; decide

lemma disc_23 : ¬ IsSquare (disc (![1, 1, 6] : Fin 3 → ZMod 7) ![1, 2, 3]) := by
  simp only [disc, pol, cf]; simp; decide

lemma disc_24 : ¬ IsSquare (disc (![1, 1, 6] : Fin 3 → ZMod 7) ![1, 4, 5]) := by
  simp only [disc, pol, cf]; simp; decide

lemma disc_34 : ¬ IsSquare (disc (![1, 2, 3] : Fin 3 → ZMod 7) ![1, 4, 5]) := by
  simp only [disc, pol, cf]; simp; decide

lemma cf_1 : IsSquare (cf (![0, 1, 0] : Fin 3 → ZMod 7)) ∧ cf (![0, 1, 0] : Fin 3 → ZMod 7) ≠ 0 := by
  simp [cf]

lemma cf_2 : IsSquare (cf (![1, 1, 6] : Fin 3 → ZMod 7)) ∧ cf (![1, 1, 6] : Fin 3 → ZMod 7) ≠ 0 := by
  simp only [cf]; simp; decide

lemma cf_3 : IsSquare (cf (![1, 2, 3] : Fin 3 → ZMod 7)) ∧ cf (![1, 2, 3] : Fin 3 → ZMod 7) ≠ 0 := by
  simp only [cf]; simp; decide

lemma cf_4 : IsSquare (cf (![1, 4, 5] : Fin 3 → ZMod 7)) ∧ cf (![1, 4, 5] : Fin 3 → ZMod 7) ≠ 0 := by
  simp only [cf]; simp; decide

lemma det_234 : Matrix.det ![(![1, 1, 6] : Fin 3 → ZMod 7), ![1, 2, 3], ![1, 4, 5]] ≠ 0 := by
  rw [Matrix.det_fin_three]; simp; decide

/-- The example from the final remarks: for `q = 7` the four points
`(0:1:0), (1:1:6), (1:2:3), (1:4:5)` form a complete exterior set of `x z = y²` which is not the
set of exterior points of a passant (no three of the points are collinear). -/
theorem exists_non_linear_complete_exterior_set :
    ∃ S : Finset (Point (ZMod 7)),
      S.card = (Fintype.card (ZMod 7) + 1) / 2 ∧ (∀ P ∈ S, IsExterior P) ∧
      (∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∀ ℓ : Line (ZMod 7), Incident P ℓ → Incident Q ℓ →
        IsPassant ℓ) ∧
      ¬ ∃ ℓ : Line (ZMod 7), IsPassant ℓ ∧ ∀ P, P ∈ S ↔ (Incident P ℓ ∧ IsExterior P) := by
  classical
  have hF : ringChar (ZMod 7) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  let v₁ : Fin 3 → ZMod 7 := ![0, 1, 0]
  let v₂ : Fin 3 → ZMod 7 := ![1, 1, 6]
  let v₃ : Fin 3 → ZMod 7 := ![1, 2, 3]
  let v₄ : Fin 3 → ZMod 7 := ![1, 4, 5]
  have h₁ : v₁ ≠ 0 := by intro h; have := congrFun h 1; simp [v₁] at this
  have h₂ : v₂ ≠ 0 := by intro h; have := congrFun h 0; simp [v₂] at this
  have h₃ : v₃ ≠ 0 := by intro h; have := congrFun h 0; simp [v₃] at this
  have h₄ : v₄ ≠ 0 := by intro h; have := congrFun h 0; simp [v₄] at this
  set P₁ := mk (ZMod 7) v₁ h₁
  set P₂ := mk (ZMod 7) v₂ h₂
  set P₃ := mk (ZMod 7) v₃ h₃
  set P₄ := mk (ZMod 7) v₄ h₄
  -- the points are pairwise distinct
  have hne : ∀ (x y : Fin 3 → ZMod 7) (hx : x ≠ 0) (hy : y ≠ 0),
      (∀ c : ZMod 7, c • y ≠ x) → mk (ZMod 7) x hx ≠ mk (ZMod 7) y hy := by
    intro x y hx hy h he
    rw [mk_eq_mk_iff'] at he
    obtain ⟨c, hc⟩ := he
    exact h c hc
  have d12 : P₁ ≠ P₂ := hne _ _ _ _ (by
    intro c h; have e0 := congrFun h 0; have e1 := congrFun h 1
    simp [v₁, v₂] at e0 e1; rw [e0] at e1; revert e1; decide)
  have d13 : P₁ ≠ P₃ := hne _ _ _ _ (by
    intro c h; have e0 := congrFun h 0; have e1 := congrFun h 1
    simp [v₁, v₃] at e0 e1; rw [e0] at e1; revert e1; decide)
  have d14 : P₁ ≠ P₄ := hne _ _ _ _ (by
    intro c h; have e0 := congrFun h 0; have e1 := congrFun h 1
    simp [v₁, v₄] at e0 e1; rw [e0] at e1; revert e1; decide)
  have d23 : P₂ ≠ P₃ := hne _ _ _ _ (by
    intro c h; have e0 := congrFun h 0; have e1 := congrFun h 1
    simp [v₂, v₃] at e0 e1; rw [e0] at e1; revert e1; decide)
  have d24 : P₂ ≠ P₄ := hne _ _ _ _ (by
    intro c h; have e0 := congrFun h 0; have e1 := congrFun h 1
    simp [v₂, v₄] at e0 e1; rw [e0] at e1; revert e1; decide)
  have d34 : P₃ ≠ P₄ := hne _ _ _ _ (by
    intro c h; have e0 := congrFun h 0; have e1 := congrFun h 1
    simp [v₃, v₄] at e0 e1; rw [e0] at e1; revert e1; decide)
  -- the quadratic character of `cf` and `disc` at the points
  have hχcf : ∀ (x : Fin 3 → ZMod 7) (hx : x ≠ 0), quadraticChar (ZMod 7) (cf x) = 1 →
      IsExterior (mk (ZMod 7) x hx) := by
    intro x hx h
    rw [isExterior_iff hF]
    obtain ⟨c, hc, hrep⟩ := rep_mk_eq_smul x hx
    rw [hrep, quadraticChar_cf_smul hc]; exact h
  have hχdisc : ∀ (x y : Fin 3 → ZMod 7) (hx : x ≠ 0) (hy : y ≠ 0),
      mk (ZMod 7) x hx ≠ mk (ZMod 7) y hy → quadraticChar (ZMod 7) (disc x y) = -1 →
      ∀ ℓ : Line (ZMod 7), Incident (mk (ZMod 7) x hx) ℓ → Incident (mk (ZMod 7) y hy) ℓ →
        IsPassant ℓ := by
    intro x y hx hy hxy h
    apply passant_of_disc hxy
    obtain ⟨c, hc, hrep⟩ := rep_mk_eq_smul x hx
    obtain ⟨c', hc', hrep'⟩ := rep_mk_eq_smul y hy
    rw [hrep, hrep', quadraticChar_disc_smul hc hc']; exact h
  have nsq : ∀ z : ZMod 7, ¬ IsSquare z → quadraticChar (ZMod 7) z = -1 :=
    fun z h => quadraticChar_neg_one_iff_not_isSquare.2 h
  have sq : ∀ z : ZMod 7, z ≠ 0 → IsSquare z → quadraticChar (ZMod 7) z = 1 :=
    fun z hz h => (quadraticChar_one_iff_isSquare hz).2 h
  refine ⟨{P₁, P₂, P₃, P₄}, ?_, ?_, ?_, ?_⟩
  · rw [ZMod.card, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair d34]
    · simp [d23, d24]
    · simp [d12, d13, d14]
  · intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl | rfl <;> apply hχcf
    · exact sq _ cf_1.2 cf_1.1
    · exact sq _ cf_2.2 cf_2.1
    · exact sq _ cf_3.2 cf_3.1
    · exact sq _ cf_4.2 cf_4.1
  · have p12 := hχdisc _ _ h₁ h₂ d12 (nsq _ disc_12)
    have p13 := hχdisc _ _ h₁ h₃ d13 (nsq _ disc_13)
    have p14 := hχdisc _ _ h₁ h₄ d14 (nsq _ disc_14)
    have p23 := hχdisc _ _ h₂ h₃ d23 (nsq _ disc_23)
    have p24 := hχdisc _ _ h₂ h₄ d24 (nsq _ disc_24)
    have p34 := hχdisc _ _ h₃ h₄ d34 (nsq _ disc_34)
    intro P hP Q hQ hPQ ℓ hPℓ hQℓ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP hQ
    rcases hP with rfl | rfl | rfl | rfl <;> rcases hQ with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hPQ
      | exact p12 ℓ hPℓ hQℓ | exact p12 ℓ hQℓ hPℓ
      | exact p13 ℓ hPℓ hQℓ | exact p13 ℓ hQℓ hPℓ
      | exact p14 ℓ hPℓ hQℓ | exact p14 ℓ hQℓ hPℓ
      | exact p23 ℓ hPℓ hQℓ | exact p23 ℓ hQℓ hPℓ
      | exact p24 ℓ hPℓ hQℓ | exact p24 ℓ hQℓ hPℓ
      | exact p34 ℓ hPℓ hQℓ | exact p34 ℓ hQℓ hPℓ
  · rintro ⟨ℓ, -, hS⟩
    have i₂ := ((hS P₂).1 (by simp)).1
    have i₃ := ((hS P₃).1 (by simp)).1
    have i₄ := ((hS P₄).1 (by simp)).1
    rw [incident_of_rep _ _ _ h₂ rfl] at i₂
    rw [incident_of_rep _ _ _ h₃ rfl] at i₃
    rw [incident_of_rep _ _ _ h₄ rfl] at i₄
    have hdet : Matrix.det ![v₂, v₃, v₄] = 0 := by
      apply Matrix.exists_mulVec_eq_zero_iff.1
      refine ⟨ℓ.rep, ℓ.rep_nonzero, ?_⟩
      funext i
      fin_cases i
      · simpa [Matrix.mulVec, dotProduct_comm] using i₂
      · simpa [Matrix.mulVec, dotProduct_comm] using i₃
      · simpa [Matrix.mulVec, dotProduct_comm] using i₄
    exact det_234 hdet

end CompleteExterior.Q7
