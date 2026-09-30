module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 131`

Every good pairing of `GF(131)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 131)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_131 : Fact (Nat.Prime 131) := ⟨by norm_num⟩

/-- Table of squares modulo `131`. -/
def sqTab131 : Array Bool := sqTab 131

/-- Table of inverses modulo `131`. -/
def invTab131 : Array ℕ := invTab 131

/-- Every good pairing of `GF(131)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_131 : PairingsLinear (ZMod 131) :=
  pairingsLinear_zmod 131 sqTab131 invTab131 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 131`**: every complete exterior set of the conic in
`PG(2, 131)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_131 : ExteriorSetsLinear (ZMod 131) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_131

end CompleteExterior
