module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
public import RequestProject.Interior.GF27

/-!
# The bound `q > 31` in the conjecture is sharp

For every `q ≡ 3 (mod 4)` with `7 ≤ q ≤ 31`, i.e. `q = 7, 11, 19, 23, 27, 31`, there is a
complete exterior set which is **not** the set of exterior points of a passant, matching the
final remarks of the paper.  In each case we exhibit an explicit non-linear good pairing (found by
a computer search), check the defining properties by `decide`, and apply the equivalence
`exteriorSetsLinear_iff`.
-/

@[expose] public section

namespace CompleteExterior

section General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A finite check that `ψ` is a good pairing, with squares tested by brute force over a list
`els` containing all elements of `F`. -/
theorem goodPairing_of_check (els : List F) (hels : ∀ x, x ∈ els) (ψ : F → F)
    (h : els.all (fun x => x == 0 || (ψ (ψ x) == x && !(els.any fun r => r * r == x * ψ x) &&
      els.all (fun y => y == 0 || y == x || y == ψ x ||
        !(els.any fun r => r * r == (x - y) * (x - ψ y) * (ψ x - y) * (ψ x - ψ y))))) = true) :
    GoodPairing ψ := by
  have hsq : ∀ a, (els.any fun r => r * r == a) = false → quadraticChar F a = -1 := by
    intro a ha
    rw [quadraticChar_neg_one_iff_not_isSquare]
    rintro ⟨r, hr⟩
    have := List.any_eq_false.1 ha r (hels r)
    simp [hr] at this
  rw [List.all_eq_true] at h
  have h' : ∀ x, x ≠ 0 → ψ (ψ x) = x ∧ (els.any fun r => r * r == x * ψ x) = false ∧
      ∀ y, y ≠ 0 → y ≠ x → y ≠ ψ x →
        (els.any fun r => r * r == (x - y) * (x - ψ y) * (ψ x - y) * (ψ x - ψ y)) = false := by
    intro x hx
    have hx' := h x (hels x)
    simp only [Bool.or_eq_true, beq_iff_eq, hx, false_or, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true] at hx'
    refine ⟨hx'.1.1, hx'.1.2, fun y hy hyx hyψ => ?_⟩
    have := hx'.2 y (hels y)
    simpa [hy, hyx, hyψ] using this
  exact ⟨fun x hx => (h' x hx).1, fun x hx => hsq _ (h' x hx).2.1,
    fun x y hx hy hyx hyψ => hsq _ ((h' x hx).2.2 y hy hyx hyψ)⟩

/-- A good pairing with two different products `s · ψ s ≠ 1 · ψ 1` is not linear. -/
theorem not_pairingsLinear_of {ψ : F → F} (hψ : GoodPairing ψ) (s : F) (hs : s ≠ 0)
    (h : s * ψ s ≠ ψ 1) : ¬ PairingsLinear F := by
  intro hL
  obtain ⟨n, -, hn⟩ := hL ψ hψ
  apply h
  rw [hn s hs, hn 1 one_ne_zero]
  field_simp

/-- If some good pairing is not linear, there is a complete exterior set that is not linear. -/
theorem exists_nonlinear_of_not_pairingsLinear (hF : ringChar F ≠ 2) (h : ¬ PairingsLinear F) :
    ∃ S : Finset (Point F), IsCompleteExteriorSet S ∧ ¬ IsLinearExteriorSet S := by
  by_contra hne
  push_neg at hne
  exact h ((exteriorSetsLinear_iff hF).1 hne)

end General

instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance fact_prime_19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩
instance fact_prime_23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩
instance fact_prime_31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- A non-linear good pairing of `GF(7)*`. -/
def psi7 (x : ZMod 7) : ZMod 7 := ([0, 3, 6, 1, 5, 4, 2] : List (ZMod 7)).getD x.val 0

/-- A non-linear good pairing of `GF(11)*`. -/
def psi11 (x : ZMod 11) : ZMod 11 :=
  ([0, 2, 1, 6, 8, 10, 3, 9, 4, 7, 5] : List (ZMod 11)).getD x.val 0

/-- A non-linear good pairing of `GF(19)*`. -/
def psi19 (x : ZMod 19) : ZMod 19 :=
  ([0, 2, 1, 4, 3, 8, 13, 10, 5, 15, 7, 18, 16, 6, 17, 9, 12, 14, 11] : List (ZMod 19)).getD
    x.val 0

/-- A non-linear good pairing of `GF(23)*`. -/
def psi23 (x : ZMod 23) : ZMod 23 :=
  ([0, 5, 7, 15, 17, 1, 22, 2, 14, 21, 13, 16, 19, 10, 8, 3, 11, 4, 20, 12, 18, 9, 6] :
    List (ZMod 23)).getD x.val 0

/-- A non-linear good pairing of `GF(31)*`. -/
def psi31 (x : ZMod 31) : ZMod 31 :=
  ([0, 3, 30, 1, 24, 15, 19, 11, 29, 21, 26, 7, 14, 25, 12, 5, 23, 28, 22, 6, 27, 9, 18, 16, 4,
    13, 10, 20, 17, 8, 2] : List (ZMod 31)).getD x.val 0

open InteriorPassant in
/-- A non-linear good pairing of `GF(27)*`, where `GF(27) = GF(3)[t]/(t³ - t - 1)` and the
element `a + b t + c t²` is encoded as `a + 3 b + 9 c`. -/
def psi27 (x : GF27) : GF27 :=
  ([0, 2, 1, 23, 26, 18, 16, 9, 13, 7, 15, 14, 17, 8, 11, 10, 6, 12, 5, 25, 21, 20, 24, 3, 22,
    19, 4].map GF27.g).getD (x : Fin 27).val 0

lemma hF7 : ringChar (ZMod 7) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
lemma hF11 : ringChar (ZMod 11) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
lemma hF19 : ringChar (ZMod 19) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
lemma hF23 : ringChar (ZMod 23) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
lemma hF31 : ringChar (ZMod 31) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num

/-- `q = 7`: there is a complete exterior set that is not linear. -/
theorem not_exteriorSetsLinear_7 : ¬ ExteriorSetsLinear (ZMod 7) := fun h =>
  not_pairingsLinear_of (goodPairing_of_check (zEls 7) (mem_zEls 7) psi7 (by decide +kernel))
    2 (by decide) (by decide +kernel) ((exteriorSetsLinear_iff hF7).1 h)

/-- `q = 11`: there is a complete exterior set that is not linear. -/
theorem not_exteriorSetsLinear_11 : ¬ ExteriorSetsLinear (ZMod 11) := fun h =>
  not_pairingsLinear_of (goodPairing_of_check (zEls 11) (mem_zEls 11) psi11 (by decide +kernel))
    3 (by decide) (by decide +kernel) ((exteriorSetsLinear_iff hF11).1 h)

/-- `q = 19`: there is a complete exterior set that is not linear. -/
theorem not_exteriorSetsLinear_19 : ¬ ExteriorSetsLinear (ZMod 19) := fun h =>
  not_pairingsLinear_of (goodPairing_of_check (zEls 19) (mem_zEls 19) psi19 (by decide +kernel))
    3 (by decide) (by decide +kernel) ((exteriorSetsLinear_iff hF19).1 h)

/-- `q = 23`: there is a complete exterior set that is not linear. -/
theorem not_exteriorSetsLinear_23 : ¬ ExteriorSetsLinear (ZMod 23) := fun h =>
  not_pairingsLinear_of (goodPairing_of_check (zEls 23) (mem_zEls 23) psi23 (by decide +kernel))
    2 (by decide) (by decide +kernel) ((exteriorSetsLinear_iff hF23).1 h)

open InteriorPassant in
/-- `q = 27`: there is a complete exterior set that is not linear. -/
theorem not_exteriorSetsLinear_27 : ¬ ExteriorSetsLinear GF27 := fun h =>
  not_pairingsLinear_of (goodPairing_of_check (F := GF27) (List.finRange 27)
      (fun x => List.mem_finRange (x : Fin 27)) psi27
      (by decide +kernel))
    (GF27.g 3) (by decide +kernel) (by decide +kernel)
    ((exteriorSetsLinear_iff GF27.ringChar_ne_two).1 h)

/-- `q = 31`: there is a complete exterior set that is not linear. -/
theorem not_exteriorSetsLinear_31 : ¬ ExteriorSetsLinear (ZMod 31) := fun h =>
  not_pairingsLinear_of (goodPairing_of_check (zEls 31) (mem_zEls 31) psi31 (by decide +kernel))
    2 (by decide) (by decide +kernel) ((exteriorSetsLinear_iff hF31).1 h)

end CompleteExterior
