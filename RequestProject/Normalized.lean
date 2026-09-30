module

public import RequestProject.Algebra

/-!
# The normalized case

We prove the algebraic form of the theorem for a complete exterior set containing the
point `(0 : 1 : 0)` (the exterior point with labels `0` and `∞`).
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma quadraticChar_four (hF : ringChar F ≠ 2) : quadraticChar F 4 = 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [show (4 : F) = 1 * 2 ^ 2 by norm_num, quadraticChar_mul_sq h2, map_one]

lemma quadraticChar_sixteen (hF : ringChar F ≠ 2) : quadraticChar F 16 = 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [show (16 : F) = 1 * (2 * 2) ^ 2 by norm_num, quadraticChar_mul_sq (mul_ne_zero h2 h2),
    map_one]

lemma quadraticChar_disc_of_eq_mk (hF : ringChar F ≠ 2) {P Q : ℙ F (Fin 3 → F)} {a b c d : F}
    (hP : P = mk F (lab a b) (lab_ne_zero (Ring.two_ne_zero hF) a b))
    (hQ : Q = mk F (lab c d) (lab_ne_zero (Ring.two_ne_zero hF) c d)) :
    quadraticChar F (disc P.rep Q.rep) =
      quadraticChar F ((a - c) * (a - d) * (b - c) * (b - d)) := by
  obtain ⟨x, hx, hPx⟩ := rep_eq_smul_of_eq_mk P _ _ hP
  obtain ⟨y, hy, hQy⟩ := rep_eq_smul_of_eq_mk Q _ _ hQ
  rw [hPx, hQy, quadraticChar_disc_smul hx hy, disc_lab, map_mul, quadraticChar_sixteen hF,
    one_mul]

omit [Fintype F] [DecidableEq F] in
lemma lab_mk_ne_e1 (hF2 : (2 : F) ≠ 0) (a b : F) :
    mk F (lab a b) (lab_ne_zero hF2 a b) ≠ mk F e1 e1_ne_zero := by
  rw [Ne, mk_eq_mk_iff']
  rintro ⟨c, hc⟩
  have := congrFun hc 0
  simp [lab, e1] at this
  exact hF2 this.symm

/-- **The normalized algebraic theorem.**  If every good pairing is linear (which holds for
`q ≡ 1 (mod 4)` by `goodPairing_eq_div`), a complete exterior set containing `(0 : 1 : 0)`
consists of the exterior points on the passant `z = n x` for a non-square `n`. -/
theorem alg_core_normalized (hF : ringChar F ≠ 2) (hGP : PairingsLinear F)
    (S : Finset (ℙ F (Fin 3 → F))) (hcard : S.card = (Fintype.card F + 1) / 2)
    (hext : ∀ P ∈ S, quadraticChar F (cf P.rep) = 1)
    (hdisc : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → quadraticChar F (disc P.rep Q.rep) = -1)
    (hE : mk F e1 e1_ne_zero ∈ S) :
    ∃ n : F, quadraticChar F n = -1 ∧
      ∀ P : ℙ F (Fin 3 → F), P ∈ S ↔
        (n * P.rep 0 = P.rep 2 ∧ quadraticChar F (cf P.rep) = 1) := by
  classical
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set E : ℙ F (Fin 3 → F) := mk F e1 e1_ne_zero with hEdef
  let M : F → F → ℙ F (Fin 3 → F) := fun a b => mk F (lab a b) (lab_ne_zero hF2 a b)
  have hMcomm : ∀ a b, M a b = M b a := by
    intro a b; simp only [M]; congr 1; exact lab_comm a b
  have hME : ∀ a b, M a b ≠ E := lab_mk_ne_e1 hF2
  -- (a) the points other than `E`
  have hoff : ∀ P ∈ S, P ≠ E → quadraticChar F (P.rep 0 * P.rep 2) = -1 := by
    intro P hP hPE
    have := hdisc P hP E hE hPE
    obtain ⟨c, hc, hcE⟩ := rep_mk_eq_smul (e1 : Fin 3 → F) e1_ne_zero
    rw [hcE, show disc P.rep (c • e1) = disc P.rep e1 * c ^ 2 by
      simpa [mul_comm] using disc_smul (1 : F) c P.rep e1, quadraticChar_mul_sq hc, disc_e1,
      map_mul, quadraticChar_four hF, one_mul] at this
    exact this
  have hrepr : ∀ P ∈ S, P ≠ E → ∃ a b : F, a ≠ b ∧ a ≠ 0 ∧ b ≠ 0 ∧ P = M a b := by
    intro P hP hPE
    have h := hoff P hP hPE
    have h0 : P.rep 0 ≠ 0 := by intro h0; rw [h0, zero_mul] at h; simp at h
    have h2 : P.rep 2 ≠ 0 := by intro h2; rw [h2, mul_zero] at h; simp at h
    obtain ⟨a, b, hab, c, hc, hv⟩ := exists_lab hF2 h0 (hext P hP)
    have hv2 := congrFun hv 2
    simp only [lab, Pi.smul_apply, smul_eq_mul] at hv2
    refine ⟨a, b, hab, ?_, ?_, eq_mk_of_rep_eq_smul P _ _ c hv⟩
    · rintro rfl; apply h2; rw [hv2]; simp
    · rintro rfl; apply h2; rw [hv2]; simp
  have hmix : ∀ a b, M a b ∈ S → quadraticChar F (a * b) = -1 := by
    intro a b hab
    have h := hoff _ hab (hME a b)
    obtain ⟨c, hc, hv⟩ := rep_mk_eq_smul (lab a b) (lab_ne_zero hF2 a b)
    simp only [M] at h
    rw [hv] at h
    simp only [lab, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at h
    rw [show c * 2 * (c * (2 * a * b)) = a * b * (2 * c) ^ 2 by ring,
      quadraticChar_mul_sq (mul_ne_zero hF2 hc)] at h
    exact h
  -- (b) labels
  let L : ℙ F (Fin 3 → F) → Finset F := fun P =>
    Finset.univ.filter (fun x => x ^ 2 * P.rep 0 - 2 * x * P.rep 1 + P.rep 2 = 0)
  have hL : ∀ a b, L (M a b) = {a, b} := by
    intro a b
    obtain ⟨c, hc, hv⟩ := rep_mk_eq_smul (lab a b) (lab_ne_zero hF2 a b)
    ext x
    simp only [L, M, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hv]
    simp only [lab, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [show x ^ 2 * (c * 2) - 2 * x * (c * (a + b)) + c * (2 * a * b) =
      (2 * c) * ((x - a) * (x - b)) by ring]
    simp [hc, hF2, sub_eq_zero]
  set S' := S.erase E with hS'
  have hS'card : S'.card = (Fintype.card F + 1) / 2 - 1 := by
    rw [hS', Finset.card_erase_of_mem hE, hcard]
  have hL0 : ∀ P ∈ S', L P ⊆ Finset.univ.erase 0 := by
    intro P hP
    obtain ⟨hPE, hPS⟩ := Finset.mem_erase.1 hP
    obtain ⟨a, b, -, ha, hb, rfl⟩ := hrepr P hPS hPE
    rw [hL]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have hLcard : ∀ P ∈ S', (L P).card = 2 := by
    intro P hP
    obtain ⟨hPE, hPS⟩ := Finset.mem_erase.1 hP
    obtain ⟨a, b, hab, -, -, rfl⟩ := hrepr P hPS hPE
    rw [hL, Finset.card_pair hab]
  -- a label determines the other one
  have hlabel : ∀ P ∈ S', ∀ x ∈ L P, ∃ y, x ≠ y ∧ P = M x y := by
    intro P hP x hx
    obtain ⟨hPE, hPS⟩ := Finset.mem_erase.1 hP
    obtain ⟨a, b, hab, -, -, rfl⟩ := hrepr P hPS hPE
    rw [hL] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, Ne.symm hab, hMcomm _ _⟩
  have hdiscM : ∀ a b c d, M a b ∈ S → M c d ∈ S → M a b ≠ M c d →
      quadraticChar F ((a - c) * (a - d) * (b - c) * (b - d)) = -1 := by
    intro a b c d h1 h2 h12
    rw [← quadraticChar_disc_of_eq_mk hF rfl rfl]
    exact hdisc _ h1 _ h2 h12
  have hdisj : ∀ P ∈ S', ∀ Q ∈ S', P ≠ Q → Disjoint (L P) (L Q) := by
    intro P hP Q hQ hPQ
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    obtain ⟨y, -, rfl⟩ := hlabel P hP x hxP
    obtain ⟨z, -, rfl⟩ := hlabel Q hQ x hxQ
    have := hdiscM x y x z (Finset.mem_erase.1 hP).2 (Finset.mem_erase.1 hQ).2 hPQ
    simp at this
  -- (c) counting: the labels cover `GF(q)*`
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hcover : S'.biUnion L = Finset.univ.erase 0 := by
    apply Finset.eq_of_subset_of_card_le (Finset.biUnion_subset.2 hL0)
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hLcard, Finset.sum_const, hS'card,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]
    omega
  have hex : ∀ x : F, x ≠ 0 → ∃ y, x ≠ y ∧ M x y ∈ S := by
    intro x hx
    have : x ∈ S'.biUnion L := by rw [hcover]; simpa using hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 this
    obtain ⟨y, hxy, rfl⟩ := hlabel P hP x hxP
    exact ⟨y, hxy, (Finset.mem_erase.1 hP).2⟩
  have huniq : ∀ x y y', M x y ∈ S → M x y' ∈ S → y = y' := by
    intro x y y' h1 h2
    by_cases heq : M x y = M x y'
    · simp only [M] at heq
      rw [mk_eq_mk_iff'] at heq
      obtain ⟨c, hc⟩ := heq
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      simp only [lab, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one] at h0 h1
      have hc1 : c = 1 := by
        have : (c - 1) * 2 = 0 := by linear_combination h0
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hF2)
      subst hc1
      linear_combination (-1 : F) * h1
    · have := hdiscM x y x y' h1 h2 heq
      simp at this
  -- (d) the involution
  let ψ : F → F := fun x => if h : x = 0 then 0 else (hex x h).choose
  have hψspec : ∀ x, x ≠ 0 → x ≠ ψ x ∧ M x (ψ x) ∈ S := by
    intro x hx
    simp only [ψ, hx, dif_neg, not_false_eq_true]
    exact (hex x hx).choose_spec
  have hψuniq : ∀ x y, x ≠ 0 → M x y ∈ S → ψ x = y := fun x y hx h =>
    huniq x _ _ (hψspec x hx).2 h
  have hψ : GoodPairing ψ := by
    constructor
    · intro x hx
      have hS := (hψspec x hx).2
      have hψ0 : ψ x ≠ 0 := by
        intro h; have := hmix _ _ hS; rw [h, mul_zero] at this; simp at this
      exact hψuniq _ _ hψ0 (hMcomm _ _ ▸ hS)
    · intro x hx
      exact hmix _ _ (hψspec x hx).2
    · intro x y hx hy hyx hyψx
      have hPQ : M x (ψ x) ≠ M y (ψ y) := by
        intro h
        have := congrArg L h
        rw [hL, hL] at this
        have hy' : y ∈ ({x, ψ x} : Finset F) := by rw [this]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
        rcases hy' with h' | h'
        · exact hyx h'
        · exact hyψx h'
      exact hdiscM _ _ _ _ (hψspec x hx).2 (hψspec y hy).2 hPQ
  obtain ⟨n, hn, hψn⟩ := hGP ψ hψ
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨n, hn, fun P => ⟨fun hP => ?_, fun ⟨h1, h2⟩ => ?_⟩⟩
  · refine ⟨?_, hext P hP⟩
    by_cases hPE : P = E
    · obtain ⟨c, hc, hv⟩ := rep_eq_smul_of_eq_mk P e1 e1_ne_zero hPE
      rw [hv]; simp [e1]
    · obtain ⟨a, b, hab, ha, hb, hPM⟩ := hrepr P hP hPE
      have hb' : b = n / a := by rw [← hψn a ha]; exact (hψuniq a b ha (hPM ▸ hP)).symm
      obtain ⟨c, hc, hv⟩ := rep_eq_smul_of_eq_mk P _ _ hPM
      rw [hv]
      simp only [lab, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, hb']
      field_simp
  · by_cases h0 : P.rep 0 = 0
    · have h2' : P.rep 2 = 0 := by rw [← h1, h0, mul_zero]
      have hPE : P = E := by
        apply eq_mk_of_rep_eq_smul P e1 e1_ne_zero (P.rep 1)
        funext i
        fin_cases i <;> simp [e1, h0, h2']
      rw [hPE]; exact hE
    · obtain ⟨a, b, hab, c, hc, hv⟩ := exists_lab hF2 h0 h2
      have hv0 := congrFun hv 0
      have hv2 := congrFun hv 2
      simp only [lab, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons] at hv0 hv2
      have hn' : a * b = n := by
        rw [hv0, hv2] at h1
        have : (2 * c) * (a * b - n) = 0 := by linear_combination (-1 : F) * h1
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hF2 hc))
      have ha : a ≠ 0 := by rintro rfl; rw [zero_mul] at hn'; exact hn0 hn'.symm
      have hψa : ψ a = b := by rw [hψn a ha, ← hn']; field_simp
      have := (hψspec a ha).2
      rw [hψa] at this
      rw [eq_mk_of_rep_eq_smul P _ (lab_ne_zero hF2 a b) c hv]
      exact this

end CompleteExterior
