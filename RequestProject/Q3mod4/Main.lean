module

public import RequestProject.Q3mod4.Transport
public import RequestProject.Q3mod4.Counterexamples
public import RequestProject.Q3mod4.Tournament
public import RequestProject.Q3mod4.P43
public import RequestProject.Q3mod4.P47
public import RequestProject.Q3mod4.P59
public import RequestProject.Q3mod4.P67
public import RequestProject.Q3mod4.P71
public import RequestProject.Q3mod4.P79
public import RequestProject.Q3mod4.P83
public import RequestProject.Q3mod4.P103
public import RequestProject.Q3mod4.P107
public import RequestProject.Q3mod4.P127
public import RequestProject.Q3mod4.P131

/-!
# The conjecture of the final remarks: summary

* `exterior_conjecture` (in `Statement.lean`): the open conjecture, stated and left unproved.
* `exteriorSetsLinear_iff`: for every odd `q`, the conjecture for `GF(q)` is equivalent to
  "every good pairing of `GF(q)*` is `x ↦ n / x`".
* `exterior_conjecture_of_le_131`: the conjecture holds for every finite field with
  `31 < q ≤ 131` (all such `q ≡ 3 (mod 4)` are primes; each case is a verified search).
* `not_exteriorSetsLinear_7`, …, `not_exteriorSetsLinear_31`: for `q = 7, 11, 19, 23, 27, 31`
  there are non-linear complete exterior sets, so the bound `q > 31` cannot be lowered.
-/

@[expose] public section

namespace CompleteExterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- In the range `31 < q ≤ 131`, every prime power `q ≡ 3 (mod 4)` is a prime. -/
lemma prime_of_isPrimePow_of_range :
    ∀ q < 132, 31 < q → q % 4 = 3 → IsPrimePow q → q.Prime := by
  decide +kernel

lemma pairingsLinear_of_card_eq (p : ℕ) [hp : Fact p.Prime] (h : PairingsLinear (ZMod p))
    (hcard : Fintype.card F = p) : PairingsLinear F :=
  pairingsLinear_of_ringEquiv (ZMod.ringEquivOfPrime F hp.out hcard) h

/-- **The conjecture holds for `31 < q ≤ 131`**: for every finite field `F` with
`|F| ≡ 3 (mod 4)` and `31 < |F| ≤ 131`, every complete exterior set of the conic in `PG(2, F)`
consists of the exterior points on a passant.  (These are the fields `GF(q)`,
`q = 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131`.) -/
theorem exterior_conjecture_of_le_131 (hq : Fintype.card F % 4 = 3)
    (h31 : 31 < Fintype.card F) (h131 : Fintype.card F ≤ 131) : ExteriorSetsLinear F := by
  have hF : ringChar F ≠ 2 := by
    intro h; rw [FiniteField.even_card_iff_char_two] at h; omega
  apply exteriorSetsLinear_of_pairingsLinear hF
  have hprime := prime_of_isPrimePow_of_range _ (by omega) h31 hq (FiniteField.isPrimePow_card F)
  obtain ⟨q, hqF⟩ : ∃ q, Fintype.card F = q := ⟨_, rfl⟩
  rw [hqF] at hq h31 h131 hprime
  interval_cases q <;>
    first
    | omega
    | exact pairingsLinear_of_card_eq 43 pairingsLinear_43 hqF
    | exact pairingsLinear_of_card_eq 47 pairingsLinear_47 hqF
    | exact pairingsLinear_of_card_eq 59 pairingsLinear_59 hqF
    | exact pairingsLinear_of_card_eq 67 pairingsLinear_67 hqF
    | exact pairingsLinear_of_card_eq 71 pairingsLinear_71 hqF
    | exact pairingsLinear_of_card_eq 79 pairingsLinear_79 hqF
    | exact pairingsLinear_of_card_eq 83 pairingsLinear_83 hqF
    | exact pairingsLinear_of_card_eq 103 pairingsLinear_103 hqF
    | exact pairingsLinear_of_card_eq 107 pairingsLinear_107 hqF
    | exact pairingsLinear_of_card_eq 127 pairingsLinear_127 hqF
    | exact pairingsLinear_of_card_eq 131 pairingsLinear_131 hqF
    | (exfalso; revert hprime; norm_num)

end CompleteExterior
