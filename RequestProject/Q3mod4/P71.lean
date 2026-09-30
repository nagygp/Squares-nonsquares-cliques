module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 71`

Every good pairing of `GF(71)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 71)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_71 : Fact (Nat.Prime 71) := ⟨by norm_num⟩

/-- Table of squares modulo `71`. -/
def sqTab71 : Array Bool := sqTab 71

/-- Table of inverses modulo `71`. -/
def invTab71 : Array ℕ := invTab 71

/-- Every good pairing of `GF(71)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_71 : PairingsLinear (ZMod 71) :=
  pairingsLinear_zmod 71 sqTab71 invTab71 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 71`**: every complete exterior set of the conic in
`PG(2, 71)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_71 : ExteriorSetsLinear (ZMod 71) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_71

end CompleteExterior
