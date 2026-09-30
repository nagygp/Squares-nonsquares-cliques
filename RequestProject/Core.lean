module

public import RequestProject.Paley

/-!
# The extra property

For a "good pairing" `ψ` of `GF(q)*` (`q ≡ 1 mod 4`) we show, by the parity count in the
Paley graph from the paper, that `(s - t)(ψ s - ψ t)` is a non-square for all distinct
non-zero squares `s, t`.
-/

@[expose] public section

open Finset

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The combinatorial data coming from a complete exterior set containing the exterior point
labelled `(0, ∞)`: a fixed-point-free involution `ψ` of `GF(q)*`, each pair `{x, ψ x}`
consisting of a square and a non-square, and condition (1) of the paper. -/
structure GoodPairing (ψ : F → F) : Prop where
  inv : ∀ x, x ≠ 0 → ψ (ψ x) = x
  mix : ∀ x, x ≠ 0 → quadraticChar F (x * ψ x) = -1
  pair : ∀ x y, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ ψ x →
    quadraticChar F ((x - y) * (x - ψ y) * (ψ x - y) * (ψ x - ψ y)) = -1

namespace GoodPairing

variable {ψ : F → F}

lemma ne_zero (hψ : GoodPairing ψ) {x : F} (hx : x ≠ 0) : ψ x ≠ 0 := by
  intro h
  have := hψ.mix x hx
  rw [h, mul_zero, quadraticChar_zero] at this
  norm_num at this

lemma chi_apply (hψ : GoodPairing ψ) {x : F} (hx : x ≠ 0) :
    quadraticChar F (ψ x) = - quadraticChar F x := by
  have := hψ.mix x hx
  rw [map_mul] at this
  rcases quadraticChar_dichotomy hx with h | h <;> rw [h] at this ⊢ <;> linarith

lemma inj (hψ : GoodPairing ψ) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : ψ x = ψ y) : x = y := by
  rw [← hψ.inv x hx, ← hψ.inv y hy, h]

end GoodPairing

variable (F) in
/-- Every good pairing of `GF(q)*` is "linear", i.e. of the form `x ↦ n / x` for a non-square
`n`.  For `q ≡ 1 (mod 4)` this is the main step of the paper (`goodPairing_eq_div`); for
`q ≡ 3 (mod 4)` it is equivalent to the conjecture of the final remarks. -/
def PairingsLinear : Prop :=
  ∀ ψ : F → F, GoodPairing ψ → ∃ n : F, quadraticChar F n = -1 ∧ ∀ x, x ≠ 0 → ψ x = n / x

lemma sqInd_sq (x : F) : sqInd x ^ 2 = sqInd x := by
  unfold sqInd; split_ifs <;> norm_num

lemma sqInd_add_of_mul {x y : F} (h : quadraticChar F (x * y) = -1) :
    sqInd x + sqInd y = 1 := by
  rw [map_mul] at h
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have hy : y ≠ 0 := by rintro rfl; simp at h
  rcases quadraticChar_dichotomy hx with e₁ | e₁ <;>
  rcases quadraticChar_dichotomy hy with e₂ | e₂ <;> simp_all [sqInd]

lemma int_sq_parity (n : ℤ) (h0 : 0 ≤ n) (h5 : n ≤ 5) : (4 : ℤ) ∣ n ^ 2 - 2 * n + n % 2 := by
  interval_cases n <;> decide

/-- The contradiction obtained from the configuration `{0, a, b, c, d}` in the Paley graph. -/
lemma core_config (hq : Fintype.card F % 4 = 1) {ψ : F → F} (hψ : GoodPairing ψ) {a c : F}
    (ha : quadraticChar F a = 1) (hc : quadraticChar F c = 1)
    (hac : quadraticChar F (a - c) = 1) (hbd : quadraticChar F (ψ a - ψ c) = 1)
    (hbc : quadraticChar F (ψ a - c) = 1) (had : quadraticChar F (a - ψ c) = -1) : False := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  set χ := quadraticChar F with hχ
  have ha0 : a ≠ 0 := by rintro rfl; simp [χ] at ha
  have hc0 : c ≠ 0 := by rintro rfl; simp [χ] at hc
  set b := ψ a with hb
  set d := ψ c with hd
  have hb0 : b ≠ 0 := hψ.ne_zero ha0
  have hd0 : d ≠ 0 := hψ.ne_zero hc0
  have hbχ : χ b = -1 := by rw [hb, hψ.chi_apply ha0, ha]
  have hdχ : χ d = -1 := by rw [hd, hψ.chi_apply hc0, hc]
  have hψb : ψ b = a := hψ.inv a ha0
  have hψd : ψ d = c := hψ.inv c hc0
  have ne_of_chi : ∀ x y : F, χ x ≠ χ y → x ≠ y := fun x y h e => h (e ▸ rfl)
  have hab : a ≠ b := ne_of_chi _ _ (by rw [ha, hbχ]; norm_num)
  have hcd : c ≠ d := ne_of_chi _ _ (by rw [hc, hdχ]; norm_num)
  have had' : a ≠ d := ne_of_chi _ _ (by rw [ha, hdχ]; norm_num)
  have hbc' : b ≠ c := ne_of_chi _ _ (by rw [hc, hbχ]; norm_num)
  have hac' : a ≠ c := by intro h; rw [h, sub_self] at hac; simp [χ] at hac
  have hbd' : b ≠ d := by intro h; rw [h, sub_self] at hbd; simp [χ] at hbd
  -- the characters of all the differences
  have hn : ∀ x : F, χ (-x) = χ x := quadraticChar_neg' hq
  have hsc : ∀ x y : F, χ (x - y) = χ (y - x) := quadraticChar_sub_comm hq
  have hab_ne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hcd_ne : c - d ≠ 0 := sub_ne_zero.mpr hcd
  -- the function counting neighbours in `{0, a, b, c, d}`
  let i : F → ℤ := fun w =>
    sqInd (w - 0) + sqInd (w - a) + sqInd (w - b) + sqInd (w - c) + sqInd (w - d)
  have hi_nonneg : ∀ w, 0 ≤ i w := fun w => by
    have := sqInd_nonneg (w - 0); have := sqInd_nonneg (w - a); have := sqInd_nonneg (w - b)
    have := sqInd_nonneg (w - c); have := sqInd_nonneg (w - d)
    simp only [i]; linarith
  have hi_le : ∀ w, i w ≤ 5 := fun w => by
    have := sqInd_le_one (w - 0); have := sqInd_le_one (w - a); have := sqInd_le_one (w - b)
    have := sqInd_le_one (w - c); have := sqInd_le_one (w - d)
    simp only [i]; linarith
  -- sums over the whole field
  have hS1 : 2 * ∑ w, i w = 5 * (Fintype.card F - 1) := by
    simp only [i, Finset.sum_add_distrib, mul_add, sum_sqInd_sub hF]; ring
  have hsq : ∀ w, i w ^ 2 = i w + 2 * (
      sqInd (w - 0) * sqInd (w - a) + sqInd (w - 0) * sqInd (w - b) +
      sqInd (w - 0) * sqInd (w - c) + sqInd (w - 0) * sqInd (w - d) +
      sqInd (w - a) * sqInd (w - b) + sqInd (w - a) * sqInd (w - c) +
      sqInd (w - a) * sqInd (w - d) + sqInd (w - b) * sqInd (w - c) +
      sqInd (w - b) * sqInd (w - d) + sqInd (w - c) * sqInd (w - d)) := by
    intro w
    simp only [i]
    linear_combination sqInd_sq (w - 0) + sqInd_sq (w - a) + sqInd_sq (w - b) +
      sqInd_sq (w - c) + sqInd_sq (w - d)
  have hS2 : 4 * ∑ w, i w ^ 2 = 4 * ∑ w, i w + 2 * (10 * (Fintype.card F - 3) - 2 * (
      χ (0 - a) + χ (0 - b) + χ (0 - c) + χ (0 - d) + χ (a - b) + χ (a - c) + χ (a - d) +
      χ (b - c) + χ (b - d) + χ (c - d))) := by
    rw [Finset.sum_congr rfl (fun w _ => hsq w)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 := sum_sqInd_mul hq ha0.symm
    have e2 := sum_sqInd_mul hq hb0.symm
    have e3 := sum_sqInd_mul hq hc0.symm
    have e4 := sum_sqInd_mul hq hd0.symm
    have e5 := sum_sqInd_mul hq hab
    have e6 := sum_sqInd_mul hq hac'
    have e7 := sum_sqInd_mul hq had'
    have e8 := sum_sqInd_mul hq hbc'
    have e9 := sum_sqInd_mul hq hbd'
    have e10 := sum_sqInd_mul hq hcd
    linear_combination 2 * (e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10)
  have v1 : χ (0 - a) = 1 := by rw [zero_sub, hn, ha]
  have v2 : χ (0 - b) = -1 := by rw [zero_sub, hn, hbχ]
  have v3 : χ (0 - c) = 1 := by rw [zero_sub, hn, hc]
  have v4 : χ (0 - d) = -1 := by rw [zero_sub, hn, hdχ]
  rw [v1, v2, v3, v4, hac, had, hbc, hbd] at hS2
  -- the vertex set `V` and its complement `W`
  set V : Finset F := {0, a, b, c, d} with hV
  set W : Finset F := univ \ V with hW
  have hVcard : V.card = 5 := by
    rw [hV, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair hcd]
    · simp [hbc', hbd']
    · simp [hab, hac', had']
    · simp [ha0.symm, hb0.symm, hc0.symm, hd0.symm]
  have hWcard : (W.card : ℤ) = Fintype.card F - 5 := by
    rw [hW, Finset.card_univ_diff, hVcard]
    have : 5 ≤ Fintype.card F := hVcard ▸ Finset.card_le_univ V
    push_cast [this]; ring
  have hsplit : ∀ f : F → ℤ, ∑ w, f w = ∑ w ∈ W, f w + ∑ w ∈ V, f w := by
    intro f
    rw [hW, Finset.sum_sdiff (Finset.subset_univ V)]
  have hVsum : ∀ f : F → ℤ, ∑ w ∈ V, f w = f 0 + f a + f b + f c + f d := by
    intro f
    rw [hV, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_pair hcd]
    · ring
    · simp [hbc', hbd']
    · simp [hab, hac', had']
    · simp [ha0.symm, hb0.symm, hc0.symm, hd0.symm]
  -- parity: the involution `ψ` pairs off the points of `W`
  have hWmem : ∀ w, w ∈ W ↔ w ≠ 0 ∧ w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ w ≠ d := by
    intro w; simp [hW, hV]
  have hψW : ∀ w ∈ W, ψ w ∈ W := by
    intro w hw
    rw [hWmem] at hw ⊢
    obtain ⟨h0, h1, h2, h3, h4⟩ := hw
    refine ⟨hψ.ne_zero h0, ?_, ?_, ?_, ?_⟩
    · intro h; apply h2; rw [← hψ.inv w h0, h]
    · intro h; exact h1 (hψ.inj h0 ha0 h)
    · intro h; apply h4; rw [← hψ.inv w h0, h]
    · intro h; exact h3 (hψ.inj h0 hc0 h)
  have hpar : ∀ w ∈ W, (i w + i (ψ w)) % 2 = 1 := by
    intro w hw
    have hw' := (hWmem w).1 hw
    obtain ⟨h0, h1, h2, h3, h4⟩ := hw'
    have hψw := (hWmem _).1 (hψW w hw)
    obtain ⟨g0, g1, g2, g3, g4⟩ := hψw
    have p0 : sqInd (w - 0) + sqInd (ψ w - 0) = 1 := by
      apply sqInd_add_of_mul; simpa using hψ.mix w h0
    have pab := hψ.pair w a h0 ha0 (Ne.symm h1) (Ne.symm g1)
    have pcd := hψ.pair w c h0 hc0 (Ne.symm h3) (Ne.symm g3)
    have qab := sqInd_four_odd (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)
      (sub_ne_zero.mpr g1) (sub_ne_zero.mpr g2) pab
    have qcd := sqInd_four_odd (sub_ne_zero.mpr h3) (sub_ne_zero.mpr h4)
      (sub_ne_zero.mpr g3) (sub_ne_zero.mpr g4) pcd
    simp only [i]
    omega
  set O := W.filter (fun w => i w % 2 = 1) with hO
  set E := W.filter (fun w => ¬ (i w % 2 = 1)) with hE
  have hOE : O.card + E.card = W.card := Finset.card_filter_add_card_filter_not _
  have hO_le : O.card ≤ E.card := by
    apply Finset.card_le_card_of_injOn ψ
    · intro w hw
      rw [hO, Finset.mem_coe, Finset.mem_filter] at hw
      rw [hE, Finset.mem_coe, Finset.mem_filter]
      refine ⟨hψW w hw.1, ?_⟩
      have := hpar w hw.1; omega
    · intro x hx y hy hxy
      have hx0 := ((hWmem x).1 (Finset.mem_filter.1 hx).1).1
      have hy0 := ((hWmem y).1 (Finset.mem_filter.1 hy).1).1
      exact hψ.inj hx0 hy0 hxy
  have hE_le : E.card ≤ O.card := by
    apply Finset.card_le_card_of_injOn ψ
    · intro w hw
      rw [hE, Finset.mem_coe, Finset.mem_filter] at hw
      rw [hO, Finset.mem_coe, Finset.mem_filter]
      refine ⟨hψW w hw.1, ?_⟩
      have := hpar w hw.1; omega
    · intro x hx y hy hxy
      have hx0 := ((hWmem x).1 (Finset.mem_filter.1 hx).1).1
      have hy0 := ((hWmem y).1 (Finset.mem_filter.1 hy).1).1
      exact hψ.inj hx0 hy0 hxy
  have hodd : ∑ w ∈ W, i w % 2 = O.card := by
    rw [hO, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro w _
    have := Int.emod_two_eq (i w)
    split_ifs with h <;> push_cast <;> omega
  have hdvd : (4 : ℤ) ∣ ∑ w ∈ W, (i w ^ 2 - 2 * i w + i w % 2) :=
    Finset.dvd_sum (fun w _ => int_sq_parity (i w) (hi_nonneg w) (hi_le w))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hdvd
  have hS1' := hsplit i
  have hS2' := hsplit (fun w => i w ^ 2)
  rw [hVsum] at hS1' hS2'
  -- evaluate `i` on the five special points
  have s1 : ∀ {x : F}, χ x = 1 → sqInd x = 1 := fun h => sqInd_of_one h
  have s2 : ∀ {x : F}, χ x = -1 → sqInd x = 0 := fun h => sqInd_of_neg_one h
  have k1 := s1 v1; have k2 := s2 v2; have k3 := s1 v3; have k4 := s2 v4
  have k1' : sqInd (a - 0) = 1 := s1 (by rw [sub_zero, ha])
  have k2' : sqInd (b - 0) = 0 := s2 (by rw [sub_zero, hbχ])
  have k3' : sqInd (c - 0) = 1 := s1 (by rw [sub_zero, hc])
  have k4' : sqInd (d - 0) = 0 := s2 (by rw [sub_zero, hdχ])
  have k5 := s1 hac; have k5' : sqInd (c - a) = 1 := s1 (by rw [hsc, hac])
  have k6 := s1 hbd; have k6' : sqInd (d - b) = 1 := s1 (by rw [hsc, hbd])
  have k7 := s1 hbc; have k7' : sqInd (c - b) = 1 := s1 (by rw [hsc, hbc])
  have k8 := s2 had; have k8' : sqInd (d - a) = 0 := s2 (by rw [hsc, had])
  have z : ∀ x : F, sqInd (x - x) = 0 := fun x => by rw [sub_self, sqInd_zero]
  have hab' : sqInd (b - a) = sqInd (a - b) := sqInd_sub_comm hq _ _
  have hcd' : sqInd (d - c) = sqInd (c - d) := sqInd_sub_comm hq _ _
  have i0 : i 0 = 2 := by simp only [i, z, k1, k2, k3, k4]; norm_num
  have ia : i a = 2 + sqInd (a - b) := by simp only [i, z, k1', k5, k8]; ring
  have ib : i b = 2 + sqInd (a - b) := by simp only [i, z, k2', hab', k7, k6]; ring
  have ic : i c = 3 + sqInd (c - d) := by simp only [i, z, k3', k5', k7']; ring
  have id : i d = 1 + sqInd (c - d) := by simp only [i, z, k4', k8', k6', hcd']; ring
  rw [i0, ia, ib, ic, id] at hS1' hS2'
  have hχab : χ (a - b) = 2 * sqInd (a - b) - 1 := by
    rcases quadraticChar_dichotomy hab_ne with α | α
    · rw [s1 α, α]; norm_num
    · rw [s2 α, α]; norm_num
  have hχcd : χ (c - d) = 2 * sqInd (c - d) - 1 := by
    rcases quadraticChar_dichotomy hcd_ne with α | α
    · rw [s1 α, α]; norm_num
    · rw [s2 α, α]; norm_num
  rw [hχab, hχcd] at hS2
  have hα : sqInd (a - b) = 0 ∨ sqInd (a - b) = 1 := by
    have := sqInd_nonneg (a - b); have := sqInd_le_one (a - b); omega
  have hγ : sqInd (c - d) = 0 ∨ sqInd (c - d) = 1 := by
    have := sqInd_nonneg (c - d); have := sqInd_le_one (c - d); omega
  rcases hα with α | α <;> rcases hγ with γ | γ <;>
  · rw [α, γ] at hS1' hS2' hS2
    norm_num at hS1' hS2' hS2
    omega

/-- The extra property in the case where both differences are squares is impossible. -/
lemma core_sq (hq : Fintype.card F % 4 = 1) {ψ : F → F} (hψ : GoodPairing ψ) {s t : F}
    (hs : quadraticChar F s = 1) (ht : quadraticChar F t = 1) (hst : s ≠ t)
    (h1 : quadraticChar F (s - t) = 1) (h2 : quadraticChar F (ψ s - ψ t) = 1) : False := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hψs : quadraticChar F (ψ s) = -1 := by rw [hψ.chi_apply hs0, hs]
  have hψt : quadraticChar F (ψ t) = -1 := by rw [hψ.chi_apply ht0, ht]
  have htψs : t ≠ ψ s := by intro h; rw [h, hψs] at ht; norm_num at ht
  have key := hψ.pair s t hs0 ht0 (Ne.symm hst) htψs
  simp only [map_mul, h1, h2] at key
  have hne1 : s - ψ t ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, hψt] at hs; norm_num at hs
  have hne2 : ψ s - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htψs)
  rcases quadraticChar_dichotomy hne2 with e | e
  · rw [e] at key
    exact core_config hq hψ hs ht h1 h2 e (by linarith)
  · rw [e] at key
    refine core_config hq hψ ht hs ?_ ?_ ?_ ?_
    · rw [quadraticChar_sub_comm hq, h1]
    · rw [quadraticChar_sub_comm hq, h2]
    · rw [quadraticChar_sub_comm hq]; linarith
    · rw [quadraticChar_sub_comm hq, e]

/-- **The extra property**: for distinct non-zero squares `s, t`, the element
`(s - t)(ψ s - ψ t)` is a non-square. -/
theorem extra_property (hq : Fintype.card F % 4 = 1) {ψ : F → F} (hψ : GoodPairing ψ) {s t : F}
    (hs : quadraticChar F s = 1) (ht : quadraticChar F t = 1) (hst : s ≠ t) :
    quadraticChar F ((s - t) * (ψ s - ψ t)) = -1 := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hne : (s - t) * (ψ s - ψ t) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hst) (sub_ne_zero.mpr (fun h => hst (hψ.inj hs0 ht0 h)))
  rcases quadraticChar_dichotomy hne with h | h
  swap; · exact h
  exfalso
  rw [map_mul] at h
  have hne1 : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hne2 : ψ s - ψ t ≠ 0 := sub_ne_zero.mpr (fun h => hst (hψ.inj hs0 ht0 h))
  rcases quadraticChar_dichotomy hne1 with e1 | e1 <;>
  rcases quadraticChar_dichotomy hne2 with e2 | e2 <;> rw [e1, e2] at h <;> norm_num at h
  · exact core_sq hq hψ hs ht hst e1 e2
  -- both differences are non-squares: apply the transformation `x ↦ n / x`
  obtain ⟨n, hn⟩ := quadraticChar_exists_neg_one hF
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  set χ := quadraticChar F
  have hψs0 := hψ.ne_zero hs0
  have hψt0 := hψ.ne_zero ht0
  have hψs : χ (ψ s) = -1 := by rw [hψ.chi_apply hs0, hs]
  have hψt : χ (ψ t) = -1 := by rw [hψ.chi_apply ht0, ht]
  let ψ' : F → F := fun x => n / ψ (n / x)
  have hψ' : GoodPairing ψ' := by
    constructor
    · intro x hx
      have h1 : n / x ≠ 0 := div_ne_zero hn0 hx
      have h2 := hψ.ne_zero h1
      simp only [ψ']
      rw [div_div_cancel₀ hn0, hψ.inv _ h1, div_div_cancel₀ hn0]
    · intro x hx
      have h1 : n / x ≠ 0 := div_ne_zero hn0 hx
      have h2 := hψ.ne_zero h1
      have := hψ.mix _ h1
      simp only [ψ']
      have e : x * (n / ψ (n / x)) = (n / x * ψ (n / x)) * (x / ψ (n / x)) ^ 2 := by
        field_simp
      rw [e, quadraticChar_mul_sq (div_ne_zero hx h2), this]
    · intro x y hx hy hyx hyψx
      have hX : n / x ≠ 0 := div_ne_zero hn0 hx
      have hY : n / y ≠ 0 := div_ne_zero hn0 hy
      have hψX := hψ.ne_zero hX
      have hψY := hψ.ne_zero hY
      have hYX : n / y ≠ n / x := by
        intro h; apply hyx
        have := congrArg (fun z => n / z) h
        simpa [div_div_cancel₀ hn0] using this
      have hYψX : n / y ≠ ψ (n / x) := by
        intro h; apply hyψx
        simp only [ψ']
        rw [← h, div_div_cancel₀ hn0]
      have := hψ.pair _ _ hX hY hYX hYψX
      simp only [ψ']
      set X := n / x
      set Y := n / y
      have hxX : x = n / X := by simp [X, div_div_cancel₀ hn0]
      have hyY : y = n / Y := by simp [Y, div_div_cancel₀ hn0]
      rw [hxX, hyY]
      have e : (n / X - n / Y) * (n / X - n / ψ Y) * (n / ψ X - n / Y) * (n / ψ X - n / ψ Y) =
          ((X - Y) * (X - ψ Y) * (ψ X - Y) * (ψ X - ψ Y)) *
            (n ^ 2 / (X * Y * ψ X * ψ Y)) ^ 2 := by
        field_simp
        ring
      rw [e, quadraticChar_mul_sq (div_ne_zero (pow_ne_zero 2 hn0)
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hX hY) hψX) hψY)), this]
  have hs' : χ (n / ψ s) = 1 := by
    rw [quadraticChar_div _ hψs0, map_mul, hn, hψs]; norm_num
  have ht' : χ (n / ψ t) = 1 := by
    rw [quadraticChar_div _ hψt0, map_mul, hn, hψt]; norm_num
  have hst' : n / ψ s ≠ n / ψ t := by
    intro h; apply hne2
    have := congrArg (fun z => n / z) h
    simp only [div_div_cancel₀ hn0] at this
    rw [this, sub_self]
  have hψ's : ψ' (n / ψ s) = n / s := by
    simp only [ψ']; rw [div_div_cancel₀ hn0, hψ.inv s hs0]
  have hψ't : ψ' (n / ψ t) = n / t := by
    simp only [ψ']; rw [div_div_cancel₀ hn0, hψ.inv t ht0]
  refine core_sq hq hψ' hs' ht' hst' ?_ ?_
  · have e : n / ψ s - n / ψ t = (n * (ψ t - ψ s)) / (ψ s * ψ t) := by field_simp
    rw [e, quadraticChar_div _ (mul_ne_zero hψs0 hψt0)]
    rw [map_mul, map_mul, map_mul, hn, hψs, hψt, quadraticChar_sub_comm hq, e2]; norm_num
  · rw [hψ's, hψ't]
    have e : n / s - n / t = (n * (t - s)) / (s * t) := by field_simp
    rw [e, quadraticChar_div _ (mul_ne_zero hs0 ht0)]
    rw [map_mul, map_mul, map_mul, hn, hs, ht, quadraticChar_sub_comm hq, e1]; norm_num

end CompleteExterior
