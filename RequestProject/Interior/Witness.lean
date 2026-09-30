module

public import RequestProject.Interior.Reduction

/-!
# Refuting the statement for a fixed field by an explicit witness

`not_statement_of_witness`: a list of `(q + 1) / 2` normalized coordinate vectors of interior
points, pairwise joined by passants and not all on one line, refutes `InteriorStatement F`.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace InteriorPassant

open CompleteExterior

variable {F : Type*} [Field F] [DecidableEq F]

/-- The finite check on a candidate counterexample. -/
def witnessB (els : List F) (vs : List (Fin 3 → F)) : Bool :=
  decide vs.Nodup && vs.all (intB els) &&
    vs.all (fun v => vs.all fun w => decide (v = w) || adjB els v w) &&
    vs.any (fun a => vs.any fun b => vs.any fun c => decide (dt (cr a b) c ≠ 0))

omit [DecidableEq F] in
/-- Three points on a common line have vanishing determinant. -/
lemma dt_cr_eq_zero {l a b c : Fin 3 → F} (hl : l ≠ 0) (ha : dt l a = 0) (hb : dt l b = 0)
    (hc : dt l c = 0) : dt (cr a b) c = 0 := by
  have key : ∀ i, l i * dt (cr a b) c =
      dt l a * cr b c i + dt l b * cr c a i + dt l c * cr a b i := by
    intro i; fin_cases i <;> simp [dt, cr] <;> ring
  by_contra hD
  apply hl
  funext i
  have := key i
  rw [ha, hb, hc] at this
  simp only [zero_mul, add_zero] at this
  exact (mul_eq_zero.1 this).resolve_right hD

lemma nrm_eq_of_mk_eq {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) (h : mk F v hv = mk F w hw) :
    nrm v = nrm w := by
  rw [mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hv ha.symm
  rw [← ha, nrm_smul ha0]

variable [Fintype F]

/-- **Refutation by a witness.** -/
theorem not_statement_of_witness (hF : ringChar F ≠ 2) (els : List F) (hels : ∀ x, x ∈ els)
    (vs : List (Fin 3 → F)) (hk : vs.length = (Fintype.card F + 1) / 2)
    (hw : witnessB els vs = true) : ¬ InteriorStatement F := by
  classical
  intro H
  simp only [witnessB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.any_eq_true] at hw
  obtain ⟨⟨⟨hnd, hint⟩, hadj⟩, a, ha, b, hb, c, hc, hdet⟩ := hw
  have hint' : ∀ v ∈ vs, v ≠ 0 ∧ nrm v = v ∧ ¬ IsSquare (cf (sw v)) := by
    intro v hv
    have := hint v hv
    simp only [intB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', ← Bool.not_eq_true,
      sqB_iff hels] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  let pt : (Fin 3 → F) → Point F := fun v => if h : v = 0 then mk F e1 e1_ne_zero else mk F v h
  have hpt : ∀ v (hv : v ≠ 0), pt v = mk F v hv := fun v hv => dif_neg hv
  set S := vs.toFinset.image pt
  have hinj : ∀ v ∈ vs, ∀ w ∈ vs, pt v = pt w → v = w := by
    intro v hv w hw h
    obtain ⟨hv0, hvn, -⟩ := hint' v hv
    obtain ⟨hw0, hwn, -⟩ := hint' w hw
    rw [hpt v hv0, hpt w hw0] at h
    rw [← hvn, ← hwn]; exact nrm_eq_of_mk_eq hv0 hw0 h
  have hcard : S.card = (Fintype.card F + 1) / 2 := by
    rw [Finset.card_image_of_injOn (fun v hv w hw h => hinj v (List.mem_toFinset.1 hv) w
      (List.mem_toFinset.1 hw) h), List.toFinset_card_of_nodup hnd, hk]
  obtain ⟨ℓ, -, hℓ⟩ := H S hcard
    (by
      intro P hP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
      rw [List.mem_toFinset] at hv
      obtain ⟨hv0, -, hsq⟩ := hint' v hv
      rw [hpt v hv0, isInteriorXY_mk_iff hF]; exact hsq)
    (by
      intro P hP Q hQ hPQ
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hQ
      rw [List.mem_toFinset] at hv hw
      obtain ⟨hv0, -, hsq⟩ := hint' v hv
      obtain ⟨hw0, -, -⟩ := hint' w hw
      have hvw : v ≠ w := fun h => hPQ (by rw [h])
      rw [hpt v hv0, hpt w hw0] at hPQ ⊢
      have hcf : cf (sw v) ≠ 0 := fun h0 => hsq ⟨0, by rw [h0]; ring⟩
      rw [passantXY_mk_iff hF v w hv0 hw0 hPQ hcf]
      have := (hadj v hv w hw).resolve_left hvw
      rw [adjB, Bool.not_eq_true', ← Bool.not_eq_true, sqB_iff hels] at this
      exact this)
  have hon : ∀ v ∈ vs, dt ℓ.rep v = 0 := by
    intro v hv
    obtain ⟨hv0, -, -⟩ := hint' v hv
    have := ((hℓ (pt v)).1 (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hv))).1
    rw [hpt v hv0, incident_of_rep _ _ v hv0 rfl] at this
    rw [dt_eq]; exact this
  exact hdet (dt_cr_eq_zero ℓ.rep_nonzero (hon a ha) (hon b hb) (hon c hc))

end InteriorPassant
