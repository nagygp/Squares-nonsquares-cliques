module

public import RequestProject.Q3mod4.Statement
public import RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.ZModSearch
import all RequestProject.Q3mod4.PairSearch

/-!
# The conjecture for `q = 103`

Every good pairing of `GF(103)*` is linear (verified exhaustive search, evaluated with
`native_decide`), hence every complete exterior set in `PG(2, 103)` is linear.
-/

@[expose] public section

namespace CompleteExterior

instance fact_prime_103 : Fact (Nat.Prime 103) := ⟨by norm_num⟩

/-- Table of squares modulo `103`. -/
def sqTab103 : Array Bool := sqTab 103

/-- Table of inverses modulo `103`. -/
def invTab103 : Array ℕ := invTab 103

/-- Every good pairing of `GF(103)*` is of the form `x ↦ n / x`. -/
theorem pairingsLinear_103 : PairingsLinear (ZMod 103) :=
  pairingsLinear_zmod 103 sqTab103 invTab103 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- **The conjecture holds for `q = 103`**: every complete exterior set of the conic in
`PG(2, 103)` consists of the exterior points on a passant. -/
theorem exteriorSetsLinear_103 : ExteriorSetsLinear (ZMod 103) :=
  exteriorSetsLinear_of_pairingsLinear (by rw [ZMod.ringChar_zmod_n]; norm_num) pairingsLinear_103

end CompleteExterior
