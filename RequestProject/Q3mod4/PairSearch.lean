module

public import RequestProject.Core

/-!
# A verified backtracking search for good pairings

For a fixed finite field we enumerate all good pairings `ψ` of `GF(q)*`: the squares are
processed one by one, each is given a non-square partner compatible with all partners chosen so
far, and at each leaf we check that all products `s · ψ s` coincide (i.e. that the pairing is
`x ↦ n / x`).  The soundness theorem `pairingsLinear_of_search` turns a successful run of the
search into the statement `PairingsLinear F`.
-/

@[expose] public section

namespace CompleteExterior

variable {F : Type*} [Field F] [DecidableEq F]

/-- All products `p.1 * p.2` in the list coincide. -/
def allProdEq : List (F × F) → Bool
  | [] => true
  | p :: t => t.all fun r => r.1 * r.2 == p.1 * p.2

/-- The backtracking search: give each element of the list (the squares) a partner `n` from
`ns` (the non-squares) such that `allowed s n` holds and `(s, n)` is compatible with all
previously chosen pairs, and check `allProdEq` at the leaves.  Compatibility of `(s, n)` with
`(c, d)` means that `(s - c)(s - d)(n - c)(n - d)` is a non-square (`nsq`). -/
def pairSearch (nsq : F → Bool) (allowed : F → F → Bool) (ns : List F) :
    List F → List (F × F) → Bool
  | [], acc => allProdEq acc
  | s :: rest, acc => ns.all fun n =>
      !(allowed s n && acc.all fun p => nsq ((s - p.1) * (s - p.2) * (n - p.1) * (n - p.2))) ||
        pairSearch nsq allowed ns rest ((s, n) :: acc)

lemma allProdEq_spec : ∀ l : List (F × F), allProdEq l = true →
    ∀ p ∈ l, ∀ r ∈ l, p.1 * p.2 = r.1 * r.2
  | [], _ => by simp
  | p :: t, h => by
    simp only [allProdEq, List.all_eq_true, beq_iff_eq] at h
    intro a ha b hb
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (h b hb).symm
    · exact h a ha
    · rw [h a ha, h b hb]

/-- **Soundness of the search.** -/
theorem pairSearch_sound (nsq : F → Bool) (allowed : F → F → Bool) (ns : List F) (ψ : F → F) :
    ∀ (L : List F) (acc : List (F × F)), pairSearch nsq allowed ns L acc = true → L.Nodup →
      (∀ s ∈ L, ψ s ∈ ns) → (∀ s ∈ L, allowed s (ψ s) = true) →
      (∀ s ∈ L, ∀ p ∈ acc, nsq ((s - p.1) * (s - p.2) * (ψ s - p.1) * (ψ s - p.2)) = true) →
      (∀ s ∈ L, ∀ t ∈ L, s ≠ t →
        nsq ((s - t) * (s - ψ t) * (ψ s - t) * (ψ s - ψ t)) = true) →
      ∀ p ∈ L.map (fun s => (s, ψ s)) ++ acc, ∀ r ∈ L.map (fun s => (s, ψ s)) ++ acc,
        p.1 * p.2 = r.1 * r.2
  | [], acc, h, _, _, _, _, _ => by
    simpa using allProdEq_spec acc (by simpa [pairSearch] using h)
  | s :: rest, acc, h, hnd, hns, hal, hacc, hpair => by
    simp only [pairSearch, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    have h1 := h (ψ s) (hns s (by simp))
    have hall : (allowed s (ψ s) && acc.all fun p =>
        nsq ((s - p.1) * (s - p.2) * (ψ s - p.1) * (ψ s - p.2))) = true := by
      rw [Bool.and_eq_true, List.all_eq_true]; exact ⟨hal s (by simp), hacc s (by simp)⟩
    rcases h1 with h1 | h1
    · rw [hall] at h1; exact absurd h1 (by simp)
    rw [List.nodup_cons] at hnd
    have key := pairSearch_sound nsq allowed ns ψ rest ((s, ψ s) :: acc) h1 hnd.2
      (fun t ht => hns t (by simp [ht])) (fun t ht => hal t (by simp [ht]))
      (by
        intro t ht p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hpair t (by simp [ht]) s (by simp) (fun h => hnd.1 (h ▸ ht))
        · exact hacc t (by simp [ht]) p hp)
      (fun t ht u hu htu => hpair t (by simp [ht]) u (by simp [hu]) htu)
    intro p hp r hr
    apply key
    · simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hp ⊢
      tauto
    · simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hr ⊢
      tauto

variable [Fintype F]

/-- Good pairings are preserved by the scalings `x ↦ c x`. -/
lemma GoodPairing.scale {ψ : F → F} (hψ : GoodPairing ψ) {c : F} (hc : c ≠ 0) :
    GoodPairing (fun x => ψ (c * x) / c) := by
  constructor
  · intro x hx
    rw [mul_div_cancel₀ _ hc, hψ.inv _ (mul_ne_zero hc hx), mul_div_cancel_left₀ _ hc]
  · intro x hx
    rw [show x * (ψ (c * x) / c) = (c * x * ψ (c * x)) * (c⁻¹) ^ 2 by field_simp,
      quadraticChar_mul_sq (inv_ne_zero hc)]
    exact hψ.mix _ (mul_ne_zero hc hx)
  · intro x y hx hy hyx hyψ
    simp only at hyψ ⊢
    have h := hψ.pair (c * x) (c * y) (mul_ne_zero hc hx) (mul_ne_zero hc hy)
      (fun h => hyx (mul_left_cancel₀ hc h))
      (fun h => hyψ (by rw [← h]; field_simp))
    rw [show (x - ψ (c * y) / c) = (c * x - ψ (c * y)) / c by field_simp,
      show (ψ (c * x) / c - y) = (ψ (c * x) - c * y) / c by field_simp,
      show (ψ (c * x) / c - ψ (c * y) / c) = (ψ (c * x) - ψ (c * y)) / c by field_simp,
      show x - y = (c * x - c * y) / c by field_simp]
    rw [show (c * x - c * y) / c * ((c * x - ψ (c * y)) / c) * ((ψ (c * x) - c * y) / c) *
        ((ψ (c * x) - ψ (c * y)) / c) = ((c * x - c * y) * (c * x - ψ (c * y)) *
        (ψ (c * x) - c * y) * (ψ (c * x) - ψ (c * y))) * ((c⁻¹) ^ 2) ^ 2 by field_simp,
      quadraticChar_mul_sq (pow_ne_zero 2 (inv_ne_zero hc))]
    exact h

/-- A good pairing for which all products `s · ψ s` over the non-zero squares coincide is
linear. -/
lemma GoodPairing.linear_of_prod {ψ : F → F} (hψ : GoodPairing ψ)
    (hprod : ∀ s t : F, s ≠ 0 → IsSquare s → t ≠ 0 → IsSquare t → s * ψ s = t * ψ t) :
    ∃ n : F, quadraticChar F n = -1 ∧ ∀ x, x ≠ 0 → ψ x = n / x := by
  have h1 : IsSquare (1 : F) := ⟨1, by simp⟩
  refine ⟨1 * ψ 1, hψ.mix 1 one_ne_zero, fun x hx => ?_⟩
  by_cases hxs : IsSquare x
  · rw [← hprod x 1 hx hxs one_ne_zero h1]
    field_simp
  · have hy0 : ψ x ≠ 0 := hψ.ne_zero hx
    have hys : IsSquare (ψ x) := by
      rw [← quadraticChar_one_iff_isSquare hy0, hψ.chi_apply hx,
        quadraticChar_neg_one_iff_not_isSquare.2 hxs]
      norm_num
    have := hprod (ψ x) 1 hy0 hys one_ne_zero h1
    rw [hψ.inv x hx] at this
    rw [← this]
    field_simp

/-- The pruning predicate used by the search, relative to the partner `m` of `1`:
both ratios `n / s` and `s / n` have key at least `key m`.  Here `inv'` is a (fast) inverse
function, e.g. a lookup table. -/
def ratioOK (key : F → ℕ) (inv' : F → F) (m s n : F) : Bool :=
  decide (key m ≤ key (n * inv' s)) && decide (key m ≤ key (s * inv' n))

/-- **From a successful search to `PairingsLinear`.**  Here `isSq` is a decision procedure for
squares, `sqs` lists the non-zero squares other than `1` without repetition, and `ns` contains
all non-squares.  Using the scalings `x ↦ c x` we may assume that the partner `m` of `1`
minimizes `key (ψ x / x)`; the search runs over all choices of `m`. -/
theorem pairingsLinear_of_search (isSq : F → Bool) (hsq : ∀ x, isSq x = true ↔ IsSquare x)
    (key : F → ℕ) (inv' : F → F) (hinv : ∀ x, x ≠ 0 → x * inv' x = 1)
    (sqs ns : List F) (hsqs : ∀ x, x ∈ sqs ↔ x ≠ 0 ∧ x ≠ 1 ∧ IsSquare x)
    (hnd : sqs.Nodup) (hns : ∀ x, ¬ IsSquare x → x ∈ ns)
    (h : ns.all (fun m => pairSearch (fun x => !isSq x) (ratioOK key inv' m) ns sqs [(1, m)]) =
      true) :
    PairingsLinear F := by
  classical
  intro ψ₀ hψ₀
  have hnsq : ∀ x, quadraticChar F x = -1 → (!isSq x) = true := by
    intro x hx
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, hsq]
    exact quadraticChar_neg_one_iff_not_isSquare.1 hx
  -- choose the scaling
  obtain ⟨c, hc, hcmin⟩ := (Finset.univ.erase (0 : F)).exists_min_image
    (fun x => key (ψ₀ x / x)) ⟨1, by simp⟩
  rw [Finset.mem_erase] at hc
  set ψ : F → F := fun x => ψ₀ (c * x) / c with hψdef
  have hψ : GoodPairing ψ := hψ₀.scale hc.1
  have hmin : ∀ x, x ≠ 0 → key (ψ 1) ≤ key (ψ x / x) := by
    intro x hx
    have := hcmin (c * x) (by simp [hc.1, hx])
    simp only [hψdef, mul_one]
    rw [show ψ₀ (c * x) / c / x = ψ₀ (c * x) / (c * x) by field_simp]
    exact this
  have hsqs' : ∀ x ∈ sqs, x ≠ 0 ∧ x ≠ 1 ∧ quadraticChar F x = 1 := by
    intro x hx
    obtain ⟨hx0, hx1, hxs⟩ := (hsqs x).1 hx
    exact ⟨hx0, hx1, (quadraticChar_one_iff_isSquare hx0).2 hxs⟩
  have hns' : ∀ s, s ≠ 0 → quadraticChar F s = 1 → ψ s ∈ ns := by
    intro s hs0 hs1
    apply hns
    rw [← quadraticChar_neg_one_iff_not_isSquare, hψ.chi_apply hs0, hs1]
  have hψ1 : ψ 1 ∈ ns := hns' 1 one_ne_zero (by simp)
  rw [List.all_eq_true] at h
  have hinv' : ∀ x, x ≠ 0 → inv' x = x⁻¹ := fun x hx => eq_inv_of_mul_eq_one_right (hinv x hx)
  have key' := pairSearch_sound (fun x => !isSq x) (ratioOK key inv' (ψ 1)) ns ψ sqs [(1, ψ 1)]
    (h _ hψ1) hnd
    (fun s hs => hns' s (hsqs' s hs).1 (hsqs' s hs).2.2)
    (by
      intro s hs
      obtain ⟨hs0, -, -⟩ := hsqs' s hs
      simp only [ratioOK, Bool.and_eq_true, decide_eq_true_eq]
      rw [hinv' s hs0, hinv' (ψ s) (hψ.ne_zero hs0), ← div_eq_mul_inv, ← div_eq_mul_inv]
      refine ⟨hmin s hs0, ?_⟩
      have := hmin (ψ s) (hψ.ne_zero hs0)
      rwa [hψ.inv s hs0] at this)
    (by
      intro s hs p hp
      simp only [List.mem_singleton] at hp
      subst hp
      obtain ⟨hs0, hs1, hsq1⟩ := hsqs' s hs
      apply hnsq
      refine hψ.pair s 1 hs0 one_ne_zero (Ne.symm hs1) ?_
      intro h
      have := hψ.chi_apply hs0
      rw [← h, hsq1] at this
      norm_num at this)
    (by
      intro s hs t ht hst
      obtain ⟨hs0, -, hs1⟩ := hsqs' s hs
      obtain ⟨ht0, -, ht1⟩ := hsqs' t ht
      apply hnsq
      refine hψ.pair s t hs0 ht0 (Ne.symm hst) ?_
      intro h
      rw [h, hψ.chi_apply hs0, hs1] at ht1
      norm_num at ht1)
  have hmem : ∀ s : F, s ≠ 0 → IsSquare s →
      (s, ψ s) ∈ sqs.map (fun s => (s, ψ s)) ++ [(1, ψ 1)] := by
    intro s hs0 hss
    by_cases hs1 : s = 1
    · subst hs1; simp
    · simp [(hsqs s).2 ⟨hs0, hs1, hss⟩]
  obtain ⟨n, hn, hψn⟩ := hψ.linear_of_prod (fun s t hs0 hss ht0 hts =>
    key' _ (hmem s hs0 hss) _ (hmem t ht0 hts))
  refine ⟨n * c ^ 2, ?_, fun x hx => ?_⟩
  · rw [quadraticChar_mul_sq hc.1, hn]
  · have := hψn (x / c) (div_ne_zero hx hc.1)
    simp only [hψdef, mul_div_cancel₀ _ hc.1] at this
    rw [div_eq_iff hc.1] at this
    rw [this]
    field_simp

end CompleteExterior
