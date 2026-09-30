module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 83`

Every good pairing of `GF(83)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 83)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_83 : Fact (Nat.Prime 83) := ⟨by norm_num⟩

/-- Table of squares modulo `83`. -/
def sqTab83 : Array Bool := sqTab 83

/-- Table of inverses modulo `83`. -/
def invTab83 : Array ℕ := invTab 83

/-- Every good pairing of `GF(83)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_83 : PairingsLinear (ZMod 83) :=
  pairingsLinear_zmod 83 sqTab83 invTab83 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 83`**: every complete exterior set of the conic in
`PG(2, 83)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_83 : ExteriorSetsLinear (ZMod 83) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_83

end CompleteExterior
