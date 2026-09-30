module

public import RequestProject.Core

/-!
# Transport of `PairingsLinear` along ring isomorphisms
-/

@[expose] public section

namespace CompleteExterior

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Fintype K] [DecidableEq K]

lemma quadraticChar_ringEquiv (e : F ≃+* K) (x : F) :
    quadraticChar K (e x) = quadraticChar F x := by
  by_cases hx : x = 0
  · simp [hx]
  have hex : e x ≠ 0 := by simpa using hx
  have hsq : IsSquare (e x) ↔ IsSquare x := by
    constructor
    · rintro ⟨r, hr⟩; exact ⟨e.symm r, by apply e.injective; simp [hr]⟩
    · rintro ⟨r, hr⟩; exact ⟨e r, by simp [hr]⟩
  rcases quadraticChar_dichotomy hx with h | h
  · rw [h]
    exact (quadraticChar_one_iff_isSquare hex).2 (hsq.2 ((quadraticChar_one_iff_isSquare hx).1 h))
  · rw [h]
    exact quadraticChar_neg_one_iff_not_isSquare.2
      (fun hs => (quadraticChar_neg_one_iff_not_isSquare.1 h) (hsq.1 hs))

/-- `PairingsLinear` is invariant under ring isomorphisms. -/
theorem pairingsLinear_of_ringEquiv (e : F ≃+* K) (h : PairingsLinear F) : PairingsLinear K := by
  intro ψ hψ
  set φ : F → F := fun x => e.symm (ψ (e x)) with hφdef
  have hφ : GoodPairing φ := by
    constructor
    · intro x hx
      simp only [hφdef, RingEquiv.apply_symm_apply]
      rw [hψ.inv (e x) (by simpa using hx), RingEquiv.symm_apply_apply]
    · intro x hx
      rw [← quadraticChar_ringEquiv e]
      simp only [hφdef, map_mul e, RingEquiv.apply_symm_apply]
      exact hψ.mix (e x) (by simpa using hx)
    · intro x y hx hy hyx hyψ
      rw [← quadraticChar_ringEquiv e]
      simp only [hφdef, map_mul e, map_sub e, RingEquiv.apply_symm_apply]
      refine hψ.pair (e x) (e y) (by simpa using hx) (by simpa using hy)
        (fun h => hyx (e.injective h)) (fun h => hyψ ?_)
      apply e.injective
      simp only [hφdef, RingEquiv.apply_symm_apply]
      exact h
  obtain ⟨n, hn, hφn⟩ := h φ hφ
  refine ⟨e n, by rw [quadraticChar_ringEquiv]; exact hn, fun y hy => ?_⟩
  have h1 := hφn (e.symm y) (by simpa using hy)
  simp only [hφdef, RingEquiv.apply_symm_apply] at h1
  have h2 := congrArg e h1
  simpa [map_div₀] using h2

end CompleteExterior
