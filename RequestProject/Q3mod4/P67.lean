module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 67`

Every good pairing of `GF(67)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 67)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_67 : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- Table of squares modulo `67`. -/
def sqTab67 : Array Bool := sqTab 67

/-- Table of inverses modulo `67`. -/
def invTab67 : Array ℕ := invTab 67

/-- Every good pairing of `GF(67)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_67 : PairingsLinear (ZMod 67) :=
  pairingsLinear_zmod 67 sqTab67 invTab67 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 67`**: every complete exterior set of the conic in
`PG(2, 67)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_67 : ExteriorSetsLinear (ZMod 67) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_67

end CompleteExterior
