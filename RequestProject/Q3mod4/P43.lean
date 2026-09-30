module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 43`

Every good pairing of `GF(43)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 43)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_43 : Fact (Nat.Prime 43) := ⟨by norm_num⟩

/-- Table of squares modulo `43`. -/
def sqTab43 : Array Bool := sqTab 43

/-- Table of inverses modulo `43`. -/
def invTab43 : Array ℕ := invTab 43

/-- Every good pairing of `GF(43)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_43 : PairingsLinear (ZMod 43) :=
  pairingsLinear_zmod 43 sqTab43 invTab43 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 43`**: every complete exterior set of the conic in
`PG(2, 43)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_43 : ExteriorSetsLinear (ZMod 43) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_43

end CompleteExterior
