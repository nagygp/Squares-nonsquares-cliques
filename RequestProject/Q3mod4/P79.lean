module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 79`

Every good pairing of `GF(79)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 79)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_79 : Fact (Nat.Prime 79) := ⟨by norm_num⟩

/-- Table of squares modulo `79`. -/
def sqTab79 : Array Bool := sqTab 79

/-- Table of inverses modulo `79`. -/
def invTab79 : Array ℕ := invTab 79

/-- Every good pairing of `GF(79)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_79 : PairingsLinear (ZMod 79) :=
  pairingsLinear_zmod 79 sqTab79 invTab79 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 79`**: every complete exterior set of the conic in
`PG(2, 79)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_79 : ExteriorSetsLinear (ZMod 79) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_79

end CompleteExterior
