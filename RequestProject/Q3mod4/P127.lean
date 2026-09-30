module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 127`

Every good pairing of `GF(127)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 127)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_127 : Fact (Nat.Prime 127) := ⟨by norm_num⟩

/-- Table of squares modulo `127`. -/
def sqTab127 : Array Bool := sqTab 127

/-- Table of inverses modulo `127`. -/
def invTab127 : Array ℕ := invTab 127

/-- Every good pairing of `GF(127)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_127 : PairingsLinear (ZMod 127) :=
  pairingsLinear_zmod 127 sqTab127 invTab127 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 127`**: every complete exterior set of the conic in
`PG(2, 127)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_127 : ExteriorSetsLinear (ZMod 127) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_127

end CompleteExterior
