module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 107`

Every good pairing of `GF(107)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 107)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_107 : Fact (Nat.Prime 107) := ⟨by norm_num⟩

/-- Table of squares modulo `107`. -/
def sqTab107 : Array Bool := sqTab 107

/-- Table of inverses modulo `107`. -/
def invTab107 : Array ℕ := invTab 107

/-- Every good pairing of `GF(107)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_107 : PairingsLinear (ZMod 107) :=
  pairingsLinear_zmod 107 sqTab107 invTab107 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 107`**: every complete exterior set of the conic in
`PG(2, 107)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_107 : ExteriorSetsLinear (ZMod 107) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_107

end CompleteExterior
