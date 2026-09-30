module

public import RequestProject.Main
public import RequestProject.Q3mod4.PairSearch

/-!
# The conjecture of the final remarks (`q ≡ 3 (mod 4)`)

In the final remarks of the paper, Blokhuis, Seress and Wilbrink conjecture that for
`q ≡ 3 (mod 4)` and `q > 31` every complete exterior set of a conic in `PG(2, q)` consists of the
exterior points on a passant ("is linear").

This file
* states the conjecture (`exterior_conjecture`, left open);
* proves, for **every** odd `q`, that "every complete exterior set is linear" is *equivalent* to
  the purely algebraic statement `PairingsLinear F`: every good pairing `ψ` of `GF(q)*` is of the
  form `x ↦ n / x` (`exteriorSetsLinear_iff`).  The direction `←` is the reduction step of the
  paper (normalization and labelling), which does not depend on `q mod 4`; the direction `→`
  builds a complete exterior set from a good pairing.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A **complete exterior set**: `(q + 1) / 2` exterior points of the conic, any two of which
are joined only by passants. -/
def IsCompleteExteriorSet (S : Finset (Point F)) : Prop :=
  S.card = (Fintype.card F + 1) / 2 ∧ (∀ P ∈ S, IsExterior P) ∧
    ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∀ ℓ : Line F, Incident P ℓ → Incident Q ℓ → IsPassant ℓ

/-- A set of points is **linear** if it is the set of exterior points on some passant. -/
def IsLinearExteriorSet (S : Finset (Point F)) : Prop :=
  ∃ ℓ : Line F, IsPassant ℓ ∧ ∀ P : Point F, P ∈ S ↔ (Incident P ℓ ∧ IsExterior P)

variable (F) in
/-- Every complete exterior set of the conic in `PG(2, F)` is linear. -/
def ExteriorSetsLinear : Prop :=
  ∀ S : Finset (Point F), IsCompleteExteriorSet S → IsLinearExteriorSet S

omit [Fintype F] [DecidableEq F] in
lemma disc_comm (u v : Fin 3 → F) : disc u v = disc v u := by
  simp only [disc, pol_comm u v]; ring

/-- **Reduction (`←`)**, valid for every odd `q`: if every good pairing is linear, then every
complete exterior set is linear. -/
theorem exteriorSetsLinear_of_pairingsLinear (hF : ringChar F ≠ 2) (hGP : PairingsLinear F) :
    ExteriorSetsLinear F := by
  rintro S ⟨hcard, hext, hpass⟩
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hext' : ∀ P ∈ S, quadraticChar F (cf P.rep) = 1 := fun P hP =>
    (isExterior_iff hF P).1 (hext P hP)
  have hdisc : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → quadraticChar F (disc P.rep Q.rep) = -1 := by
    intro P hP Q hQ hPQ
    have hcf : cf P.rep ≠ 0 := by
      intro h; have := hext' P hP; rw [h] at this; simp at this
    exact disc_of_passant hF hPQ hcf (hpass P hP Q hQ hPQ)
  obtain ⟨u, hu, haniso, hS⟩ := alg_core hF hGP S hcard hext' hdisc
  refine ⟨mk F (polarVec u) (polarVec_ne_zero hF2 hu), ?_, ?_⟩
  · intro P hP hPc
    rw [incident_polar_iff hF2 P hu] at hP
    rw [onConic_iff] at hPc
    exact haniso P.rep P.rep_nonzero hP hPc
  · intro P
    rw [hS P, incident_polar_iff hF2 P hu, isExterior_iff hF P]

/-- **Converse (`→`)**, valid for every odd `q`: a good pairing `ψ` yields the complete exterior
set consisting of `(0 : 1 : 0)` (labels `0, ∞`) and the points with labels `(s, ψ s)`,
`s` a non-zero square; if this set is linear, then `ψ` is linear. -/
theorem pairingsLinear_of_exteriorSetsLinear (hF : ringChar F ≠ 2) (h : ExteriorSetsLinear F) :
    PairingsLinear F := by
  classical
  intro ψ hψ
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set χ := quadraticChar F with hχ
  let M : F → Point F := fun a => mk F (lab a (ψ a)) (lab_ne_zero hF2 a (ψ a))
  set E : Point F := mk F e1 e1_ne_zero with hE
  set Sq : Finset F := Finset.univ.filter (fun x => χ x = 1) with hSq
  set NSq : Finset F := Finset.univ.filter (fun x => χ x = -1) with hNSq
  set S : Finset (Point F) := insert E (Sq.image M) with hSdef
  have hmemSq : ∀ s, s ∈ Sq ↔ χ s = 1 := by intro s; simp [hSq]
  have hmemNSq : ∀ s, s ∈ NSq ↔ χ s = -1 := by intro s; simp [hNSq]
  have hsq0 : ∀ s ∈ Sq, s ≠ 0 := by
    intro s hs h0; rw [hmemSq, h0, quadraticChar_zero] at hs; norm_num at hs
  have hψsq : ∀ s ∈ Sq, χ (ψ s) = -1 := by
    intro s hs; rw [hχ, hψ.chi_apply (hsq0 s hs), ← hχ, (hmemSq s).1 hs]
  -- the discriminant between points with labels `(s, ψ s)` and `(t, ψ t)`
  have hpairM : ∀ s ∈ Sq, ∀ t ∈ Sq, s ≠ t → χ (disc (M s).rep (M t).rep) = -1 := by
    intro s hs t ht hst
    rw [hχ, quadraticChar_disc_of_eq_mk hF rfl rfl]
    refine hψ.pair s t (hsq0 s hs) (hsq0 t ht) (Ne.symm hst) ?_
    intro h
    have := hψsq s hs
    rw [← h, (hmemSq t).1 ht] at this
    norm_num at this
  have hMinj : ∀ s ∈ Sq, ∀ t ∈ Sq, M s = M t → s = t := by
    intro s hs t ht hMst
    by_contra hst
    have := hpairM s hs t ht hst
    rw [← hMst, show disc (M s).rep (M s).rep = 0 by simp only [disc, pol_self]; ring,
      hχ, quadraticChar_zero] at this
    norm_num at this
  have hME : ∀ s, M s ≠ E := fun s => lab_mk_ne_e1 hF2 s (ψ s)
  have hEnot : E ∉ Sq.image M := by
    intro hmem
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 hmem
    exact hME s hs
  -- the discriminant between `E` and a point with labels `(s, ψ s)`
  have hEM : ∀ s ∈ Sq, χ (disc (M s).rep E.rep) = -1 := by
    intro s hs
    obtain ⟨c, hc, hcv⟩ := rep_mk_eq_smul (lab s (ψ s)) (lab_ne_zero hF2 s (ψ s))
    obtain ⟨d, hd, hdv⟩ := rep_mk_eq_smul (e1 : Fin 3 → F) e1_ne_zero
    rw [hcv, hdv, hχ, quadraticChar_disc_smul hc hd, disc_e1]
    simp only [lab, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [show 4 * (2 * (2 * s * ψ s)) = s * ψ s * 4 ^ 2 by ring,
      quadraticChar_mul_sq (by
        rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero hF2 hF2)]
    exact hψ.mix s (hsq0 s hs)
  -- counting
  have hSqcard : Sq.card = (Fintype.card F - 1) / 2 := by
    have h1 : Sq.card ≤ NSq.card := by
      apply Finset.card_le_card_of_injOn ψ
      · intro s hs; rw [Finset.mem_coe, hmemNSq]; exact hψsq s hs
      · intro s hs t ht hst; exact hψ.inj (hsq0 s hs) (hsq0 t ht) hst
    have h2 : NSq.card ≤ Sq.card := by
      apply Finset.card_le_card_of_injOn ψ
      · intro s hs
        rw [Finset.mem_coe, hmemNSq] at hs
        have hs0 : s ≠ 0 := by rintro rfl; rw [hχ, quadraticChar_zero] at hs; norm_num at hs
        rw [Finset.mem_coe, hmemSq, hχ, hψ.chi_apply hs0, ← hχ, hs]; norm_num
      · intro s hs t ht hst
        rw [Finset.mem_coe, hmemNSq] at hs ht
        have hs0 : s ≠ 0 := by rintro rfl; rw [hχ, quadraticChar_zero] at hs; norm_num at hs
        have ht0 : t ≠ 0 := by rintro rfl; rw [hχ, quadraticChar_zero] at ht; norm_num at ht
        exact hψ.inj hs0 ht0 hst
    have hunion : Sq ∪ NSq = Finset.univ.erase 0 := by
      ext x
      simp only [Finset.mem_union, hmemSq, hmemNSq, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro (h | h) h0 <;> rw [h0, quadraticChar_zero] at h <;> norm_num at h
      · intro hx; exact quadraticChar_dichotomy hx
    have hdisj : Disjoint Sq NSq := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [hmemSq] at hx; rw [hmemNSq, hx] at hx'; norm_num at hx'
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    omega
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hScard : S.card = (Fintype.card F + 1) / 2 := by
    rw [hSdef, Finset.card_insert_of_notMem hEnot,
      Finset.card_image_of_injOn (fun s hs t ht hst => hMinj s hs t ht hst), hSqcard]
    omega
  -- exterior points
  have hext : ∀ P ∈ S, IsExterior P := by
    intro P hP
    rw [isExterior_iff hF P]
    rcases Finset.mem_insert.1 hP with rfl | hP
    · obtain ⟨d, hd, hdv⟩ := rep_mk_eq_smul (e1 : Fin 3 → F) e1_ne_zero
      rw [hdv, quadraticChar_cf_smul hd, cf_e1, map_one]
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hP
      obtain ⟨c, hc, hcv⟩ := rep_mk_eq_smul (lab s (ψ s)) (lab_ne_zero hF2 s (ψ s))
      simp only [M]
      rw [hcv, quadraticChar_cf_smul hc, cf_lab]
      apply quadraticChar_sq_one'
      intro h
      have := hψsq s hs
      rw [← sub_eq_zero.1 h, (hmemSq s).1 hs] at this
      norm_num at this
  -- passants
  have hdiscS : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → χ (disc P.rep Q.rep) = -1 := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_insert.1 hP with rfl | hP <;> rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact absurd rfl hPQ
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hQ
      rw [disc_comm]; exact hEM t ht
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hP
      exact hEM s hs
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hP
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hQ
      exact hpairM s hs t ht (fun h => hPQ (h ▸ rfl))
  obtain ⟨ℓ, -, hℓ⟩ := h S ⟨hScard, hext, fun P hP Q hQ hPQ =>
    passant_of_disc hPQ (hdiscS P hP Q hQ hPQ)⟩
  -- read off the line
  set L := ℓ.rep with hL
  have hL1 : L 1 = 0 := by
    have hinc := ((hℓ E).1 (Finset.mem_insert_self _ _)).1
    obtain ⟨d, hd, hdv⟩ := rep_mk_eq_smul (e1 : Fin 3 → F) e1_ne_zero
    rw [Incident, hdv, dotProduct_smul, smul_eq_mul] at hinc
    simpa [e1, dotProduct, Fin.sum_univ_three, hd] using hinc
  have hlin : ∀ s ∈ Sq, L 0 + s * ψ s * L 2 = 0 := by
    intro s hs
    have hinc := ((hℓ (M s)).1 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem M hs))).1
    obtain ⟨c, hc, hcv⟩ := rep_mk_eq_smul (lab s (ψ s)) (lab_ne_zero hF2 s (ψ s))
    simp only [M] at hinc
    rw [Incident, hcv, dotProduct_smul, smul_eq_mul, ← hL] at hinc
    have hinc' := (mul_eq_zero.1 hinc).resolve_left hc
    simp only [lab, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hL1] at hinc'
    have : 2 * (L 0 + s * ψ s * L 2) = 0 := by linear_combination hinc'
    exact (mul_eq_zero.1 this).resolve_left hF2
  have h1Sq : (1 : F) ∈ Sq := by rw [hmemSq]; simp [hχ]
  have hL2 : L 2 ≠ 0 := by
    intro hL2
    have hL0 : L 0 = 0 := by simpa [hL2] using hlin 1 h1Sq
    apply ℓ.rep_nonzero
    funext i; fin_cases i
    · exact hL0
    · exact hL1
    · exact hL2
  apply hψ.linear_of_prod
  intro s t hs0 hss ht0 hts
  have hs : s ∈ Sq := by rw [hmemSq, hχ]; exact (quadraticChar_one_iff_isSquare hs0).2 hss
  have ht : t ∈ Sq := by rw [hmemSq, hχ]; exact (quadraticChar_one_iff_isSquare ht0).2 hts
  have e1 := hlin s hs
  have e2 := hlin t ht
  have : (s * ψ s - t * ψ t) * L 2 = 0 := by linear_combination e1 - e2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hL2)

/-- **Equivalence**, for every odd `q`: every complete exterior set is linear iff every good
pairing of `GF(q)*` is linear. -/
theorem exteriorSetsLinear_iff (hF : ringChar F ≠ 2) :
    ExteriorSetsLinear F ↔ PairingsLinear F :=
  ⟨pairingsLinear_of_exteriorSetsLinear hF, exteriorSetsLinear_of_pairingsLinear hF⟩

/-- For `q ≡ 1 (mod 4)` (assuming the theorem of Carlitz–McConnel) every complete exterior set is
linear: this is the main theorem of the paper, restated with the definitions of this file. -/
theorem exteriorSetsLinear_of_mod_four_eq_one (hq : Fintype.card F % 4 = 1)
    (hCM : CarlitzMcConnel F) : ExteriorSetsLinear F :=
  exteriorSetsLinear_of_pairingsLinear (ringChar_ne_two_of_card_mod_four hq)
    (fun _ hψ => goodPairing_eq_div hq hCM hψ)

/-- **The conjecture of Blokhuis, Seress and Wilbrink** (final remarks of the paper): for
`q ≡ 3 (mod 4)` and `q > 31`, every complete exterior set of the conic in `PG(2, q)` consists of
the exterior points on a passant.

This is an open problem; it is **not** proved here.  What is proved: it is equivalent to
`PairingsLinear F` (`exteriorSetsLinear_iff`); it holds for every field with `31 < q ≤ 131`
(`exterior_conjecture_of_le_131` in `RequestProject/Q3mod4/Main.lean`); and the bound `q > 31`
cannot be lowered (see `RequestProject/Q3mod4/Counterexamples.lean`). -/
theorem exterior_conjecture (hq : Fintype.card F % 4 = 3) (h31 : 31 < Fintype.card F) :
    ExteriorSetsLinear F := by
  sorry

end CompleteExterior
