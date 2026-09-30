module

public import RequestProject.Involution

/-!
# Algebraic reformulation

We translate the problem into the language of the quadratic form `cf v = v₁² - v₀ v₂`
(whose zero set is the conic `x z = y²`) and (twice) its polar form `pol`.

* a point `P` is exterior iff `cf P` is a non-zero square;
* the line joining two points `P, Q` is a passant iff `disc P Q = pol P Q ² - 4 cf P cf Q` is a
  non-square.

The exterior point with "labels" `a, b` (i.e. lying on the tangents at `(1 : a : a²)` and
`(1 : b : b²)`) is `lab a b = (2 : a + b : 2 a b)`; the point `e1 = (0 : 1 : 0)` has labels
`0, ∞`.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace CompleteExterior

section Basic

variable {F : Type*} [Field F]

/-- The quadratic form `y² - x z`; the conic is its zero set. -/
def cf (v : Fin 3 → F) : F := v 1 ^ 2 - v 0 * v 2

/-- Twice the polar bilinear form of `cf`. -/
def pol (u v : Fin 3 → F) : F := 2 * u 1 * v 1 - u 0 * v 2 - u 2 * v 0

/-- The discriminant deciding whether the line through `u` and `v` meets the conic. -/
def disc (u v : Fin 3 → F) : F := pol u v ^ 2 - 4 * cf u * cf v

/-- The exterior point with labels `a, b`. -/
def lab (a b : F) : Fin 3 → F := ![2, a + b, 2 * a * b]

/-- The point `(0 : 1 : 0)`, with labels `0` and `∞`. -/
def e1 : Fin 3 → F := ![0, 1, 0]

lemma cf_smul (c : F) (v : Fin 3 → F) : cf (c • v) = c ^ 2 * cf v := by
  simp [cf]; ring

lemma pol_smul_left (c : F) (u v : Fin 3 → F) : pol (c • u) v = c * pol u v := by
  simp [pol]; ring

lemma pol_smul_right (c : F) (u v : Fin 3 → F) : pol u (c • v) = c * pol u v := by
  simp [pol]; ring

lemma pol_add_left (u v w : Fin 3 → F) : pol (u + v) w = pol u w + pol v w := by
  simp [pol]; ring

lemma pol_sub_left (u v w : Fin 3 → F) : pol (u - v) w = pol u w - pol v w := by
  simp [pol]; ring

lemma pol_comm (u v : Fin 3 → F) : pol u v = pol v u := by
  simp [pol]; ring

lemma pol_self (v : Fin 3 → F) : pol v v = 2 * cf v := by
  simp [pol, cf]; ring

lemma cf_add_smul (x d : Fin 3 → F) (t : F) :
    cf (x + t • d) = cf x + t * pol x d + t ^ 2 * cf d := by
  simp [cf, pol]; ring

lemma cf_sub (x d : Fin 3 → F) : cf (x - d) = cf x - pol x d + cf d := by
  simp [cf, pol]; ring

lemma cf_add (x d : Fin 3 → F) : cf (x + d) = cf x + pol x d + cf d := by
  simp [cf, pol]; ring

lemma disc_smul (c d : F) (u v : Fin 3 → F) :
    disc (c • u) (d • v) = c ^ 2 * d ^ 2 * disc u v := by
  simp [disc, cf, pol]; ring

lemma disc_lab (a b c d : F) :
    disc (lab a b) (lab c d) = 16 * ((a - c) * (a - d) * (b - c) * (b - d)) := by
  simp [disc, lab, cf, pol]; ring

lemma disc_e1 (v : Fin 3 → F) : disc v e1 = 4 * (v 0 * v 2) := by
  simp [disc, e1, cf, pol]; ring

lemma cf_lab (a b : F) : cf (lab a b) = (a - b) ^ 2 := by
  simp [cf, lab]; ring

lemma cf_e1 : cf (e1 : Fin 3 → F) = 1 := by simp [cf, e1]

lemma lab_comm (a b : F) : lab a b = lab b a := by
  simp only [lab]; rw [add_comm, mul_assoc, mul_assoc, mul_comm a b]

lemma lab_ne_zero (hF2 : (2 : F) ≠ 0) (a b : F) : lab a b ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [lab] at this
  exact hF2 this

lemma e1_ne_zero : (e1 : Fin 3 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [e1] at this

/-- The representative of `mk v` is a non-zero multiple of `v`. -/
lemma rep_mk_eq_smul (v : Fin 3 → F) (hv : v ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ (mk F v hv).rep = c • v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep F v hv
  exact ⟨a, a.ne_zero, by rw [← ha, Units.smul_def]⟩

lemma eq_mk_of_rep_eq_smul (P : ℙ F (Fin 3 → F)) (v : Fin 3 → F) (hv : v ≠ 0) (c : F)
    (h : P.rep = c • v) : P = mk F v hv := by
  rw [← mk_rep P, mk_eq_mk_iff']
  exact ⟨c, h.symm⟩

lemma rep_eq_smul_of_eq_mk (P : ℙ F (Fin 3 → F)) (v : Fin 3 → F) (hv : v ≠ 0)
    (h : P = mk F v hv) : ∃ c : F, c ≠ 0 ∧ P.rep = c • v := by
  subst h; exact rep_mk_eq_smul v hv

end Basic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma quadraticChar_cf_smul {c : F} (hc : c ≠ 0) (v : Fin 3 → F) :
    quadraticChar F (cf (c • v)) = quadraticChar F (cf v) := by
  rw [cf_smul, mul_comm, quadraticChar_mul_sq hc]

lemma quadraticChar_disc_smul {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) (u v : Fin 3 → F) :
    quadraticChar F (disc (c • u) (d • v)) = quadraticChar F (disc u v) := by
  rw [disc_smul, show c ^ 2 * d ^ 2 * disc u v = disc u v * (c * d) ^ 2 by ring,
    quadraticChar_mul_sq (mul_ne_zero hc hd)]

/-- An exterior point off the line `x = 0` is of the form `lab a b` with `a ≠ b`. -/
lemma exists_lab (hF2 : (2 : F) ≠ 0) {v : Fin 3 → F} (h0 : v 0 ≠ 0)
    (hsq : quadraticChar F (cf v) = 1) :
    ∃ a b : F, a ≠ b ∧ ∃ c : F, c ≠ 0 ∧ v = c • lab a b := by
  have hcf0 : cf v ≠ 0 := by intro h; rw [h] at hsq; simp at hsq
  obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare hcf0).1 hsq
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hcf0 hr
  refine ⟨(v 1 + r) / v 0, (v 1 - r) / v 0, ?_, v 0 / 2, div_ne_zero h0 hF2, ?_⟩
  · intro h
    rw [div_left_inj' h0] at h
    have : 2 * r = 0 := by linear_combination h
    exact hr0 ((mul_eq_zero.1 this).resolve_left hF2)
  · simp only [cf] at hr
    funext i
    fin_cases i
    · simp [lab]; field_simp
    · simp [lab]; field_simp; ring
    · simp [lab]; field_simp; linear_combination (-1 : F) * hr

end CompleteExterior
