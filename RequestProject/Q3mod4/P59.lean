module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 59`

Every good pairing of `GF(59)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 59)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_59 : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- Table of squares modulo `59`. -/
def sqTab59 : Array Bool := sqTab 59

/-- Table of inverses modulo `59`. -/
def invTab59 : Array ℕ := invTab 59

/-- Every good pairing of `GF(59)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_59 : PairingsLinear (ZMod 59) :=
  pairingsLinear_zmod 59 sqTab59 invTab59 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 59`**: every complete exterior set of the conic in
`PG(2, 59)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_59 : ExteriorSetsLinear (ZMod 59) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_59

end CompleteExterior
