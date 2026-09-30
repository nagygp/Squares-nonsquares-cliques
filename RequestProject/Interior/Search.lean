module

public import Mathlib

/-!
# A verified exhaustive clique search

`search adj ok cand k cl` enumerates all `k`-subsets of the list `cand` which are cliques for the
(boolean) adjacency relation `adj`, and checks `ok` on each of them (together with the already
chosen vertices `cl`).  The soundness theorem `search_sound` says that if the search returns
`true`, then every `k`-clique contained in `cand` passes the test `ok`.
-/

@[expose] public section

namespace InteriorPassant

variable {V : Type*} [DecidableEq V] (adj : V → V → Bool) (ok : List V → Bool)

/-- Exhaustive search over the `k`-cliques contained in the candidate list. -/
def search : List V → ℕ → ℕ → List V → Bool
  | [], _, 0, cl => ok cl
  | [], _, _ + 1, _ => true
  | _ :: _, _, 0, cl => ok cl
  | v :: rest, len, k + 1, cl =>
      if len < k + 1 then true
      else
        (let f := rest.filter (adj v); search f f.length k (v :: cl)) &&
          search rest (len - 1) (k + 1) cl
termination_by cand _ _ _ => cand.length
decreasing_by
  all_goals simp_wf
  all_goals grind [List.length_filter_le]

omit [DecidableEq V] in
lemma card_le_of_subset_list {K : Finset V} {l : List V} (h : ∀ x ∈ K, x ∈ l) :
    K.card ≤ l.length := by
  classical
  calc K.card ≤ l.toFinset.card := Finset.card_le_card (fun x hx => List.mem_toFinset.2 (h x hx))
    _ ≤ l.length := List.toFinset_card_le l

/-- **Soundness of the clique search.** -/
theorem search_sound : ∀ (n : ℕ) (cand : List V), cand.length = n → ∀ (k : ℕ) (cl : List V),
    search adj ok cand n k cl = true → cand.Nodup → ∀ K : Finset V, K.card = k →
    (∀ x ∈ K, x ∈ cand) → (∀ x ∈ K, ∀ y ∈ K, x ≠ y → adj x y = true) →
    ∃ l : List V, ok l = true ∧ ∀ x, x ∈ l ↔ (x ∈ K ∨ x ∈ cl) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro cand hn k cl hs hnd K hK hsub hadj
  rcases cand with _ | ⟨v, rest⟩ <;> rcases k with _ | k
  · -- [], 0
    rw [Finset.card_eq_zero] at hK; subst hK
    exact ⟨cl, by simpa [search] using hs, by simp⟩
  · -- [], k + 1
    exfalso
    have := card_le_of_subset_list hsub
    rw [hK] at this; simp at this
  · -- v :: rest, 0
    rw [Finset.card_eq_zero] at hK; subst hK
    exact ⟨cl, by simpa [search] using hs, by simp⟩
  · -- v :: rest, k + 1
    rw [search] at hs
    simp only [List.length_cons] at hn
    subst hn
    by_cases hlen : rest.length + 1 < k + 1
    · exfalso
      have := card_le_of_subset_list hsub
      simp at this; omega
    rw [if_neg hlen, Bool.and_eq_true] at hs
    simp only [Nat.add_sub_cancel] at hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [List.nodup_cons] at hnd
    by_cases hv : v ∈ K
    · obtain ⟨l, hl, hmem⟩ := ih (rest.filter (adj v)).length
        (by have := List.length_filter_le (adj v) rest; omega)
        (rest.filter (adj v)) rfl k (v :: cl) hs1 (hnd.2.filter _) (K.erase v)
        (by rw [Finset.card_erase_of_mem hv, hK]; rfl)
        (by
          intro x hx
          rw [Finset.mem_erase] at hx
          rw [List.mem_filter]
          refine ⟨?_, hadj v hv x hx.2 (Ne.symm hx.1)⟩
          have := hsub x hx.2
          rw [List.mem_cons] at this
          exact this.resolve_left hx.1)
        (fun x hx y hy hxy => hadj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy)
      refine ⟨l, hl, fun x => ?_⟩
      rw [hmem, Finset.mem_erase, List.mem_cons]
      constructor
      · rintro (⟨-, hx⟩ | rfl | hx)
        · exact Or.inl hx
        · exact Or.inl hv
        · exact Or.inr hx
      · rintro (hx | hx)
        · by_cases hxv : x = v
          · exact Or.inr (Or.inl hxv)
          · exact Or.inl ⟨hxv, hx⟩
        · exact Or.inr (Or.inr hx)
    · exact ih rest.length (by omega) rest rfl (k + 1) cl hs2 hnd.2 K hK
        (by
          intro x hx
          have := hsub x hx
          rw [List.mem_cons] at this
          exact this.resolve_left (fun h => hv (h ▸ hx)))
        hadj

end InteriorPassant
