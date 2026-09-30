# Summary of changes for run c622db22-739e-46d4-b10c-3e29e1ae9198
I proved in Lean that for q ≡ 1 (mod 4), every good pairing ψ of GF(q)* has the form ψ(x) = n/x for some non-square n. As you asked, the proof does not assume the Carlitz–McConnel theorem and uses no geometry. The theorem is `CompleteExterior.Direct.goodPairing_eq_div_direct` in `RequestProject/Direct/Main.lean`. It builds with no `sorry` and uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The argument is written out in `direct_proof.md`.

**How the proof goes.** Let f(0) = 0 and f(x) = 1/ψ(x).
1. **Paley graph.** The paper's parity count in the Paley graph (already in the project, and purely combinatorial) shows that f turns edges into non-edges and vice versa: χ(f x − f y) = −χ(x − y). Because ψ is an involution, f(1/f(x)) = 1/x.
2. **f is additive** (`IsAnti.map_add`, in `Direct/Eigen.lean` and `Direct/Additive.lean`). This holds for any map u with u(0) = 0 that swaps edges and non-edges of the Paley graph.
   - Substituting y ↦ u(y) gives Σ_y χ(x−y)χ(y)u(y) = κ·u(x) for a constant κ.
   - Read coefficient by coefficient, this says: if the coefficient of x^j in u is non-zero, then ρ_j = ρ_1. Here ρ_j = −(−1)^j·C((q−1)/2, j).
   - Two consecutive ρ's cannot both equal ρ_1, because 2·(q−1)/2 + 1 = 0 in F.
   - The translates u(x+c) − u(c) satisfy the same condition. Comparing their coefficients of x^(j−1), as polynomials in c, rules out every exponent j ≥ 2 with p ∤ j.
   - Composing with a power of the Frobenius map reduces every other exponent that is not a power of p to that case.
   - So only exponents p^b occur, which makes u additive. Lucas's theorem is not needed.
3. **Hua's identity.** From x² = x − (x⁻¹ + (1−x)⁻¹)⁻¹, additivity, and f(1/f(z)) = 1/z, we get f(x²) = f(x)²/f(1). So σ = f/f(1) is a field automorphism, with σ² = id, and it fixes the non-square f(1). The project's existing fixed-field lemma then gives σ = id. Hence f(x) = f(1)·x, and ψ(x) = n/x with n = 1/f(1).

**Consequences.** The paper's main theorem no longer needs the Carlitz–McConnel hypothesis. I proved this version as `Direct.complete_exterior_set_eq_exterior_points_of_passant'` in `RequestProject/Direct/Unconditional.lean`, also with only the standard axioms. I also added `pairingsLinear_of_card_mod_four`, which states the result in the project's existing `PairingsLinear` form.

**Files.** Everything new is in `RequestProject/Direct/` (`Coeff`, `Eigen`, `Additive`, `Main`, `Unconditional`), plus `direct_proof.md`. I did not modify any existing Lean file, and the original results that take the Carlitz–McConnel hypothesis are still there.

# Summary of changes for run baeae2b0-6df2-4405-a0da-c9a05cfe3264
I did not prove the conjecture in general. It is stated in Lean as `exterior_conjecture` in `RequestProject/Q3mod4/Statement.lean`, and its proof is left as `sorry`. The paper's own remark that the authors had no idea how to prove it still applies. I did prove the following, in the new folder `RequestProject/Q3mod4/`:

**1. A reformulation that works for every odd q** (`exteriorSetsLinear_iff`, standard axioms only). "Every complete exterior set of `PG(2,q)` lies on a passant" holds if and only if every good pairing of `GF(q)*` has the form `ψ(x) = n/x`. A good pairing is an involution pairing each square with a non-square and satisfying the paper's condition (1).
- The paper's normalisation and labelling step never uses `q ≡ 1 (mod 4)`. I changed the earlier `alg_core` and `alg_core_normalized` to take "every good pairing is `n/x`" (`PairingsLinear`) as a hypothesis instead of `q ≡ 1 (mod 4)` plus Carlitz–McConnel. The statement of the main theorem is unchanged, and it still builds.
- The converse is new: a good pairing that is not `n/x` yields a complete exterior set that is not on a passant.
- So for `q ≡ 3 (mod 4)` the conjecture is exactly a statement about such involutions. The paper's Paley-graph parity step fails there, because −1 is a non-square.

**2. The conjecture holds for all fields with 31 < q ≤ 131** (`exterior_conjecture_of_le_131`, in `Q3mod4/Main.lean`). This is the range of Brouwer's search reported in the paper: q = 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131.
- Every prime power in that range that is ≡ 3 (mod 4) is prime, and fields of prime order are isomorphic to `ZMod q`. So this covers every finite field in the range.
- Each prime is handled by an exhaustive search over good pairings. The search's correctness is proved in Lean. It uses the scaling symmetry `ψ ↦ ψ(c·)/c`, which cuts the search roughly tenfold.
- The search runs with `native_decide`, so these results also trust the Lean compiler. The files `P127.lean` and `P131.lean` take about 10 minutes each to build.

**3. The bound q > 31 cannot be lowered** (`not_exteriorSetsLinear_7`, `_11`, `_19`, `_23`, `_27`, `_31`). For each of these q there is a complete exterior set not on a passant, matching the paper's final remarks. The witnesses are explicit pairings found by computer search. Every property is then checked by the Lean kernel, without `native_decide`. For q = 27 I reused the existing explicit field model `GF27`.

**Not verified:** an unoptimised search I ran outside Lean found only linear pairings for q = 139, 151, 163, 167 and 179. This was not checked in Lean.

The full project builds. The only `sorry`s are this conjecture and the earlier open interior-point claim. `exterior_conjecture.md` explains the reduction, how the search works, and how to check another prime.

# Summary of changes for run 0da42a0e-22d2-4ae1-b774-43926b31b171
I wrote `interior_points.md` in the project root. It summarizes the open problem, what was found, and how the computation for a single value of q works. I changed no Lean files. `RequestProject.Interior.Main` still builds, and its one remaining `sorry` is the general theorem.

**The open problem.** Take the conic `xy = z²` in PG(2,q). Let S be a set of (q+1)/2 interior points such that every line through two points of S is a passant. The claim is that if q ≡ 1 (mod 4) and q ≥ 27, then S is the set of interior points on some passant. The theorem is stated in Lean, but it is not proved for general q. The Blokhuis–Seress–Wilbrink paper proves the matching result for exterior points and does not discuss interior points. The paper's own conjecture is a different one, about q ≡ 3 (mod 4) and q > 31, and the note keeps the two apart.

**What was found.** The note has a table of results, all proved in Lean. The checks for particular q rely on `native_decide`, so they trust the Lean compiler as well as the standard axioms.
- **General q:**
  - A point is interior exactly when `z² − xy` is a non-square.
  - The line through two points is a passant exactly when a discriminant is a non-square.
  - Conversely, the interior points on any passant always form a set of the required kind.
- **Where the claim holds:** q = 29 (which gives an "if and only if" there) and q = 17. It holds for q = 27 only vacuously, because 27 is not ≡ 1 (mod 4).
- **Where the conclusion fails:** q = 5, 13 and 25 (all ≡ 1 mod 4), each with an explicit set of points. It also fails for q = 27 if the mod-4 condition is dropped.

These results show that some lower bound on q is needed, that q ≥ 27 cannot be lowered to q ≥ 17, and that plain counting cannot prove the claim. Suggestions that the claim holds for q = 37 and 41 and fails for q = 9 came from computations outside Lean and are marked as not verified.

**How the check for one q works** (section 3 of the note):
1. **Criteria:** the geometric conditions are replaced by the two square/non-square tests above.
2. **Graph:** the program lists one representative of each of the q(q−1)/2 interior points and builds a table recording which pairs are joined by a passant. It also has a test for whether a chosen set is exactly the interior points on the line through its first two members.
3. **Clique search:** a branch-and-bound search enumerates every clique of size (q+1)/2 in that graph. At each point it either includes the point, keeping only its neighbours as candidates, or skips it, and it abandons a branch once too few candidates remain. Its correctness is proved in Lean by induction.

A reduction theorem shows that if the search succeeds, the claim holds for that field. For q = 29 the search runs through `native_decide` and takes about 4½ minutes to build. Counterexamples are checked the same way with an explicit list of points, which includes three non-collinear ones.

Section 4 explains how to run the check for a new q:
- **Prime q:** copy the q = 29 file and change the numbers.
- **Prime-power q:** first build a concrete model of the field, as was done for 25 and 27.
- **Cost:** the note explains how the running time grows with q, and that fixing one point of S in advance by symmetry could speed the search up. That speed-up has not been implemented.

# Summary of changes for run 4538ec4e-6eef-4d12-8b9e-7e7f694aa2d5
I formalized the theorem and proved it in Lean for q = 29. For q = 27 it holds only vacuously, because 27 ≡ 3 (mod 4) fails your hypothesis q ≡ 1 (mod 4). I did not prove the general theorem: it is stated in Lean but its proof is left as `sorry`. The new work is in `RequestProject/Interior/`, and the whole project builds.

**Statement.** I read "points of B" in your request as "points of S". Following your wording, the conic is `x y = z²`, and an interior point is a point off the conic that lies on no tangent (`Defs.lean`). The general theorem is `interior_set_eq_interior_points_of_passant` in `Main.lean`, with hypotheses `q ≡ 1 (mod 4)`, `q ≥ 27` and `|S| = (q+1)/2`.

**Checks for particular q.** All of these are proved. The ones that rely on computation use `native_decide`, so they depend on the Lean compiler as well as the standard axioms.
- **q = 29** (`interior_set_eq_interior_points_of_passant_29`): the theorem holds. The proof has two parts.
  - A general reduction: a point is interior exactly when `z² − xy` is a non-square, and a joining line is a passant exactly when a discriminant is a non-square.
  - An exhaustive search over all 15-point sets of the 406 interior points. The search code is proved correct in Lean. It finds exactly 406 such sets, one on each passant.
- **q = 27**: the theorem holds vacuously (`interior_set_eq_interior_points_of_passant_card_27`). If the mod-4 hypothesis is dropped, the conclusion fails: there are 14 interior points pairwise joined by passants that are not on one line (`not_interiorStatement_27`). This uses a concrete 27-element field whose field axioms are checked by Lean's kernel.
- **The bound q ≥ 27:** the conclusion fails for q = 5, 13 and 25, all ≡ 1 (mod 4) (`Counterexamples.lean`). It holds for q = 17 (`Q17.lean`), so the bound cannot simply be lowered to q ≥ 17. The counterexamples were found by a computer search, and every property used is then checked in Lean.

**Converse.** For every odd q, the interior points on a passant form a set of the required kind (`interior_points_of_passant`, `Converse.lean`). Combined with the q = 29 result, this gives a full "if and only if" characterization for q = 29 (`interior_set_iff_29`).

**General proof: not achieved.** Plain point–line counting cannot work, because the q = 25 counterexamples satisfy the same counts. The exterior-point analogue already needed the Carlitz–McConnel theorem, which that project assumes rather than proves. The threshold at 27 suggests the general proof needs a deeper quantitative argument that I could not supply here.

**Unverified exploration.** Scratch computations outside Lean suggested the theorem also holds for q = 37 and 41, and fails for q = 9. These were not checked in Lean.

# Summary of changes for run 58605dc5-f606-4d50-b427-6c9b539cd094
I formalized the Blokhuis–Seress–Wilbrink paper *Characterization of complete exterior sets of conics* in Lean 4 with Mathlib. The project builds with no `sorry`, and the main results use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**One result is assumed, not proved.** The paper quotes the Carlitz–McConnel theorem from the literature without proving it. I stated it as `CarlitzMcConnel F` in `RequestProject/Defs.lean`. The main theorem and the characterization take it as an explicit hypothesis `hCM`. Proving it would remove that hypothesis; I did not attempt this.

**Setup** (`RequestProject/Defs.lean`)
- Points and lines of `PG(2,q)` are elements of `ℙ F (Fin 3 → F)`, with incidence given by the dot product.
- As in the paper, the conic is fixed as `xz = y²`; every nondegenerate conic is projectively equivalent to it.
- A tangent is a line meeting the conic in exactly one point, and a passant is a line missing it.
- An exterior point is a point off the conic lying on two distinct tangents.

**Main theorem** (`RequestProject/Main.lean`, `complete_exterior_set_eq_exterior_points_of_passant`): for `q ≡ 1 (mod 4)`, a set of `(q+1)/2` exterior points in which every line through two of the points is a passant is exactly the set of exterior points on some passant.

**How the proof follows the paper**
- **Geometric criteria:** a point is exterior iff `y² − xz` is a non-zero square (`isExterior_iff`). The line `PQ` is a passant iff a discriminant is a non-square (`passant_iff_disc`). For points labelled `(a,b)` and `(c,d)` that discriminant is `16(a−c)(a−d)(b−c)(b−d)`, which is the paper's cross-ratio criterion.
- **Normalization:** where the paper uses the transitivity of `PGL(2,q)`, I used a reflection that preserves the conic to move one point of the set to the point labelled `(0,∞)`.
- **Labelling:** exterior points are labelled by pairs of points of the conic, and a counting argument shows the labels partition `GF(q)*`. This produces the involution `φ`, packaged as `GoodPairing`, satisfying condition (1).
- **The "extra property"** (`extra_property`): proved by the paper's parity count in the Paley graph. The common-neighbour counts come from a Jacobi-sum identity, and the case where both differences are non-squares is handled with the substitution `x ↦ n/x`.
- **Conclusion** (`goodPairing_eq_div`): the Carlitz–McConnel theorem, together with a short fixed-field argument ruling out a non-trivial Frobenius power, gives `φ(x) = n/x`.

**Additions beyond the paper's main theorem**
- **Converse** (`exterior_points_of_passant`, `RequestProject/Converse.lean`): for every odd `q`, the exterior points on a passant number `(q+1)/2`, and any two of them are joined only by passants. This does not use Carlitz–McConnel.
- **Characterization** (`complete_exterior_set_iff`): combining the two, for `q ≡ 1 (mod 4)` a set is a complete exterior set iff it is the set of exterior points on a passant.
- **The case q = 7** (`Q7.exists_non_linear_complete_exterior_set`, `RequestProject/Example.lean`), from the paper's final remarks: the points `(0:1:0), (1:1:6), (1:2:3), (1:4:5)` form a complete exterior set in `PG(2,7)` that is not on any passant. So the hypothesis `q ≡ 1 (mod 4)` cannot be dropped. I found these points with a computer search; every fact about them is then checked in Lean with `decide`.

The proof is split across `Paley`, `Core`, `Involution`, `Algebra`, `Normalized`, `Reflection`, `Geometry`, `Converse` and `Example`, all imported by `RequestProject/Main.lean`.