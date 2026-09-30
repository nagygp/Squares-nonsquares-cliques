module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 47`

Every good pairing of `GF(47)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 47)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_47 : Fact (Nat.Prime 47) := ⟨by norm_num⟩

/-- Table of squares modulo `47`. -/
def sqTab47 : Array Bool := sqTab 47

/-- Table of inverses modulo `47`. -/
def invTab47 : Array ℕ := invTab 47

/-- Every good pairing of `GF(47)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_47 : PairingsLinear (ZMod 47) :=
  pairingsLinear_zmod 47 sqTab47 invTab47 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 47`**: every complete exterior set of the conic in
`PG(2, 47)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_47 : ExteriorSetsLinear (ZMod 47) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_47

end CompleteExterior
