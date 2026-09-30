module

public import RequestProject.Interior.Compute

/-!
# Reduction of the statement for a fixed field to a finite computation

`statement_of_check`: if the exhaustive clique search over the interior points of `x y = z²`
(with adjacency "the joining line is a passant") succeeds, then the requested statement holds
for the field in question.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace InteriorPassant

open CompleteExterior

variable {F : Type*} [Field F] [DecidableEq F]

lemma sqB_iff {els : List F} (hels : ∀ x, x ∈ els) (x : F) : sqB els x = true ↔ IsSquare x := by
  simp [sqB, IsSquare, hels]

lemma nrm_eq_smul {v : Fin 3 → F} (hv : v ≠ 0) : ∃ c : F, c ≠ 0 ∧ nrm v = c • v := by
  unfold nrm
  split_ifs with h0 h1
  · exact ⟨_, inv_ne_zero h0, rfl⟩
  · exact ⟨_, inv_ne_zero h1, rfl⟩
  · have h2 : v 2 ≠ 0 := by
      intro h2; apply hv; funext i; fin_cases i <;> simp_all
    exact ⟨_, inv_ne_zero h2, rfl⟩

lemma nrm_ne_zero {v : Fin 3 → F} (hv : v ≠ 0) : nrm v ≠ 0 := by
  obtain ⟨c, hc, h⟩ := nrm_eq_smul hv
  rw [h]; exact smul_ne_zero hc hv

lemma nrm_smul {c : F} (hc : c ≠ 0) (v : Fin 3 → F) : nrm (c • v) = nrm v := by
  unfold nrm
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or]
  split_ifs <;> rw [smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

lemma nrm_nrm {v : Fin 3 → F} (hv : v ≠ 0) : nrm (nrm v) = nrm v := by
  obtain ⟨c, hc, h⟩ := nrm_eq_smul hv
  rw [h, nrm_smul hc]; exact h

lemma mk_nrm {v : Fin 3 → F} (hv : v ≠ 0) : mk F (nrm v) (nrm_ne_zero hv) = mk F v hv := by
  obtain ⟨c, hc, h⟩ := nrm_eq_smul hv
  rw [mk_eq_mk_iff']
  exact ⟨c, h.symm⟩

lemma mk_nrm_rep (P : Point F) : mk F (nrm P.rep) (nrm_ne_zero P.rep_nonzero) = P := by
  rw [mk_nrm P.rep_nonzero, mk_rep]

lemma eq_of_nrm_rep_eq {P Q : Point F} (h : nrm P.rep = nrm Q.rep) : P = Q := by
  rw [← mk_nrm_rep P, ← mk_nrm_rep Q, mk_eq_mk_iff']
  exact ⟨1, by rw [one_smul, h]⟩

omit [Field F] [DecidableEq F] in
lemma mem_allVecs {F : Type*} {els : List F} (hels : ∀ x, x ∈ els) (v : Fin 3 → F) : v ∈ allVecs els := by
  simp only [allVecs, List.mem_flatMap, List.mem_map]
  exact ⟨v 0, hels _, v 1, hels _, v 2, hels _, by funext i; fin_cases i <;> rfl⟩

omit [DecidableEq F] in
lemma isSquare_sq_mul_iff {c : F} (hc : c ≠ 0) (x : F) : IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / c, ?_⟩
    field_simp
    linear_combination hr
  · rintro ⟨r, hr⟩
    exact ⟨c * r, by rw [hr]; ring⟩

omit [DecidableEq F] in
lemma cr_self (v : Fin 3 → F) : cr v v = 0 := by
  funext i; fin_cases i <;> simp [cr] <;> ring

omit [DecidableEq F] in
lemma dt_eq (a b : Fin 3 → F) : dt a b = a ⬝ᵥ b := by
  simp [dt, dotProduct, Fin.sum_univ_three]

omit [DecidableEq F] in
lemma dt_smul_right (a b : Fin 3 → F) (c : F) : dt a (c • b) = c * dt a b := by
  simp [dt]; ring

variable [Fintype F]

lemma isInteriorXY_iff_mem_verts (hF : ringChar F ≠ 2) {els : List F} (hels : ∀ x, x ∈ els)
    (P : Point F) : IsInteriorXY P ↔ nrm P.rep ∈ verts els := by
  have h1 : IsInteriorXY P ↔ ¬ IsSquare (cf (sw P.rep)) := by
    rw [← isInteriorXY_mk_iff hF P.rep P.rep_nonzero, mk_rep]
  obtain ⟨c, hc, h⟩ := nrm_eq_smul P.rep_nonzero
  rw [h1, verts, List.mem_filter, intB]
  simp only [mem_allVecs hels, true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    ← Bool.not_eq_true, sqB_iff hels]
  rw [nrm_nrm P.rep_nonzero, h, sw_smul, cf_smul, isSquare_sq_mul_iff hc]
  simp [smul_ne_zero hc P.rep_nonzero]

/-- **Reduction to a finite check.** -/
theorem statement_of_check (hF : ringChar F ≠ 2) (els : List F) (hels : ∀ x, x ∈ els)
    (W : Array (Fin 3 → F)) (hW : W = (verts els).toArray)
    (A : Array (Array Bool)) (hA : A = adjArr els) (k : ℕ) (hk : (Fintype.card F + 1) / 2 = k)
    (hcheck : search (adjA A) (okA W) (List.range W.size) W.size k [] = true) :
    InteriorStatement F := by
  classical
  intro S hcard hint hpass
  set L := verts els with hL
  have hWsize : W.size = L.length := by simp [hW]
  have hWget : ∀ i (hi : i < L.length), W.getD i 0 = L[i]'hi := by
    intro i hi; subst hW; simp [Array.getD, hi]
  have hAget : ∀ i (hi : i < L.length) j (hj : j < L.length),
      adjA A i j = adjB els (L[i]'hi) (L[j]'hj) := by
    intro i hi j hj; subst hA; simp [adjA, adjArr, Array.getD, hi, hj, L]
  have hmemL : ∀ P : Point F, IsInteriorXY P → nrm P.rep ∈ L := fun P hP =>
    (isInteriorXY_iff_mem_verts hF hels P).1 hP
  let idx : Point F → ℕ := fun P => L.idxOf (nrm P.rep)
  have hidx_lt : ∀ P : Point F, IsInteriorXY P → idx P < L.length := fun P hP =>
    List.idxOf_lt_length_of_mem (hmemL P hP)
  have hidx_get : ∀ P : Point F, ∀ hP : IsInteriorXY P, L[idx P]'(hidx_lt P hP) = nrm P.rep :=
    fun P hP => List.getElem_idxOf _
  have hidx_inj : ∀ P Q : Point F, IsInteriorXY P → IsInteriorXY Q → idx P = idx Q → P = Q := by
    intro P Q hP hQ h
    apply eq_of_nrm_rep_eq
    rw [← hidx_get P hP, ← hidx_get Q hQ]
    simp only [h]
  have hcf : ∀ P : Point F, IsInteriorXY P → cf (sw (nrm P.rep)) ≠ 0 := by
    intro P hP h0
    have := (isInteriorXY_mk_iff hF _ (nrm_ne_zero P.rep_nonzero)).1 (by rwa [mk_nrm_rep])
    rw [h0] at this; exact this ⟨0, by ring⟩
  set K := S.image idx with hKdef
  have hK : K.card = k := by
    rw [Finset.card_image_of_injOn (fun P hP Q hQ h => hidx_inj P Q (hint P hP) (hint Q hQ) h),
      hcard, hk]
  obtain ⟨l, hl, hlmem⟩ := search_sound (adjA A) (okA W) W.size (List.range W.size)
    List.length_range k [] hcheck List.nodup_range K hK
    (by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      rw [List.mem_range, hWsize]; exact hidx_lt P (hint P hP))
    (by
      intro x hx y hy hxy
      rw [Finset.mem_image] at hx hy
      obtain ⟨P, hP, rfl⟩ := hx
      obtain ⟨Q, hQ, rfl⟩ := hy
      have hPQ : P ≠ Q := fun h => hxy (by rw [h])
      rw [hAget _ (hidx_lt P (hint P hP)) _ (hidx_lt Q (hint Q hQ)), hidx_get P (hint P hP),
        hidx_get Q (hint Q hQ), adjB, Bool.not_eq_true', ← Bool.not_eq_true, sqB_iff hels]
      have key := passantXY_mk_iff hF (nrm P.rep) (nrm Q.rep) (nrm_ne_zero P.rep_nonzero)
        (nrm_ne_zero Q.rep_nonzero) (by rw [mk_nrm_rep, mk_nrm_rep]; exact hPQ)
        (hcf P (hint P hP))
      rw [← key, mk_nrm_rep, mk_nrm_rep]
      exact hpass P hP Q hQ hPQ)
  have hlK : ∀ x, x ∈ l ↔ x ∈ K := fun x => by simpa using hlmem x
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [okA] at hl
  · simp [okA] at hl
  simp only [okA, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, List.mem_range] at hl
  obtain ⟨⟨hl0, hlon⟩, hlall⟩ := hl
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 ((hlK a).1 (by simp))
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 ((hlK b).1 (by simp))
  have hgetP := hWget _ (hidx_lt P (hint P hP))
  have hgetQ := hWget _ (hidx_lt Q (hint Q hQ))
  rw [hidx_get P (hint P hP)] at hgetP
  rw [hidx_get Q (hint Q hQ)] at hgetQ
  set lv := cr (W.getD (idx P) 0) (W.getD (idx Q) 0) with hlv
  have hPQ : P ≠ Q := by
    rintro rfl; apply hl0; rw [hlv, cr_self]
  set ℓ : Line F := mk F lv hl0
  have hinc : ∀ X : Point F, Incident X ℓ ↔ dt lv (nrm X.rep) = 0 := by
    intro X
    rw [incident_mk_iff, ← dt_eq]
    obtain ⟨c, hc, h⟩ := nrm_eq_smul X.rep_nonzero
    rw [h, dt_smul_right, mul_eq_zero, or_iff_right hc]
  have hincS : ∀ X ∈ S, Incident X ℓ := by
    intro X hX
    rw [hinc, ← hidx_get X (hint X hX), ← hWget _ (hidx_lt X (hint X hX))]
    exact hlon _ ((hlK _).2 (Finset.mem_image_of_mem _ hX))
  refine ⟨ℓ, hpass P hP Q hQ hPQ ℓ (hincS P hP) (hincS Q hQ), fun X => ⟨fun hX =>
    ⟨hincS X hX, hint X hX⟩, fun ⟨hXl, hXi⟩ => ?_⟩⟩
  have hj := hidx_lt X hXi
  rcases hlall (idx X) (by rw [hWsize]; exact hj) with h | h
  · exfalso; apply h
    rw [hWget _ hj, hidx_get X hXi, ← hinc]; exact hXl
  · obtain ⟨Y, hY, hYX⟩ := Finset.mem_image.1 ((hlK _).1 h)
    rw [← hidx_inj Y X (hint Y hY) hXi hYX]; exact hY

end InteriorPassant
