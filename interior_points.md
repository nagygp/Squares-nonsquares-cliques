# Sets of interior points of a conic joined only by passants

This note covers the "interior points" statement that was studied after the
Blokhuis–Seress–Wilbrink paper was formalized. It gives the open problem, what
was proved in Lean and what was not, and how the check for a single value of
`q` works. All Lean files named here are in `RequestProject/Interior/`.

---

## 1. The problem

Work in `PG(2, q)` with `q` odd, and use the conic

    C :  x·y = z².

* A **tangent** is a line meeting `C` in exactly one point.
* A **passant** (external line) is a line containing no point of `C`.
* An **interior point** is a point off `C` that lies on no tangent.

These are the definitions in `Defs.lean` (`IsTangentXY`, `IsPassantXY`, `IsInteriorXY`).

**Claim** (`interior_set_eq_interior_points_of_passant`, `Main.lean`).
Let `q ≡ 1 (mod 4)` and `q ≥ 27`. Let `S` be a set of `(q+1)/2` interior points
of `C` such that every line through two distinct points of `S` is a passant.
Then `S` is exactly the set of interior points on some passant.

The paper proves the analogous theorem for **exterior** points, for every
`q ≡ 1 (mod 4)` and assuming the Carlitz–McConnel theorem. The paper does not
discuss the interior-point version. The paper's own open question is different:
it conjectures that for `q ≡ 3 (mod 4)` and `q > 31` every complete exterior set
lies on a passant.

**Status: the claim for general `q` is open in this project.** It is stated in
Lean, but its proof is `sorry`. It is the only `sorry` in the project, and the
build reports it as a warning.

---

## 2. What was established (all checked in Lean)

| Result | Lean name | File | How it is proved |
|---|---|---|---|
| Interior-point criterion: `(x:y:z)` is interior ⇔ `z² − xy` is a non-square | `isInteriorXY_mk_iff` | `Criteria.lean` | general proof, every odd `q` |
| Passant criterion: the line `PQ` is a passant ⇔ a discriminant is a non-square | `passantXY_mk_iff` | `Criteria.lean` | general proof, every odd `q` |
| Converse: the interior points on a passant are `(q+1)/2` points, pairwise joined by passants | `interior_points_of_passant` | `Converse.lean` | general proof, every odd `q` |
| Claim holds for `q = 29` | `interior_set_eq_interior_points_of_passant_29` | `Q29.lean` | verified exhaustive search |
| "If and only if" for `q = 29` | `interior_set_iff_29` | `Main.lean` | `q = 29` case plus the converse |
| Claim holds for `q = 17` | `interior_set_eq_interior_points_of_passant_17` | `Q17.lean` | verified exhaustive search |
| `q = 27` is covered only vacuously (`27 ≡ 3 mod 4`) | `interior_set_eq_interior_points_of_passant_card_27` | `Main.lean` | arithmetic |
| Without `q ≡ 1 (mod 4)` the conclusion fails for `q = 27` | `not_interiorStatement_27` | `Counterexamples.lean` | explicit set of 14 points |
| Conclusion fails for `q = 25` | `not_interiorStatement_25` | `Counterexamples.lean` | explicit set of 13 points |
| Conclusion fails for `q = 13` | `not_interiorStatement_13` | `Counterexamples.lean` | explicit set of 7 points |
| Conclusion fails for `q = 5` | `not_interiorStatement_5` | `Counterexamples.lean` | explicit set of 3 points |

The theorems for particular `q` rely on `native_decide`. They therefore trust the
Lean compiler, in addition to the standard axioms `propext`, `Classical.choice`
and `Quot.sound`. For `q = 25` and `q = 27` there are explicit models of the
fields, `GF25 = GF(5)[t]/(t² − 2)` and `GF27 = GF(3)[t]/(t³ − t − 1)`. Their
field axioms are checked by the Lean kernel (`decide +kernel`).

### What the findings show

* **The bound matters.** `5`, `13` and `25` are all `≡ 1 (mod 4)`, yet the
  conclusion fails for each of them, so some lower bound on `q` is needed. For
  `q = 17` the conclusion holds, so the failures do not simply stop at one
  threshold. Hence `q ≥ 27` cannot be replaced by `q ≥ 17`.
* **The congruence matters, at least at `q = 27`.** In `PG(2, 27)` there are
  14 interior points, pairwise joined by passants, that are not collinear.
* **Counting alone cannot prove the claim.** Plain point–line counting cannot
  tell the `q = 25` counterexamples apart from the sets on a line, because both
  satisfy the same incidence counts. The exterior-point proof in the paper
  needed an algebraic ingredient: an involution `φ(x) = n/x` pinned down by the
  Carlitz–McConnel theorem. A general proof of the interior claim probably needs
  a comparable, quantitative argument that only takes effect for large `q`.
  None was found.

### Not verified

Informal computations done outside Lean suggested that the claim also holds for
`q = 37` and `q = 41`, and fails for `q = 9`. **None of these was checked in
Lean.** Section 4 explains how to check them.

---

## 3. How the computation for a fixed `q` works

For one field `F` with `q` elements, the check turns the geometric statement
into a finite graph problem and solves it by a clique search whose correctness
is proved in Lean. It has three stages.

### Stage 1 – Algebraic criteria (proved for every odd `q`)

Write `sw(x, y, z) = (x, z, y)` (`sw` in `Criteria.lean`). This coordinate swap
takes the conic `xy = z²` to the paper's conic `xz = y²` and preserves incidence.
So the criteria proved for the exterior case carry over:

* `(x:y:z)` is **interior** ⇔ `cf(sw v) = z² − xy` is a **non-square** in `F`
  (`isInteriorXY_mk_iff`).
* For distinct points `v`, `w` with `v` off the conic, **every line through
  them is a passant** ⇔ the discriminant

      disc(u, u') = pol(u, u')² − 4·cf(u)·cf(u'),   u = sw v, u' = sw w,
      cf(u) = u₁² − u₀u₂,   pol(u, u') = 2u₁u'₁ − u₀u'₂ − u₂u'₀

  is a **non-square** (`passantXY_mk_iff`). Here `pol(u, u')² − 4·cf(u)·cf(u')`
  is the discriminant of the quadratic equation `cf(λu + μu') = 0`. The line
  misses the conic exactly when that equation has no root in `F`.

After this stage, no lines or tangents remain in the problem. Only
square/non-square tests on explicit polynomials are needed.

### Stage 2 – Computable data (`Compute.lean`)

Given a list `els` of all elements of `F`:

1. **Squareness test** `sqB els x`: is `x = r·r` for some `r` in `els`?
2. **Point enumeration**: go through all vectors `(a, b, c) ∈ F³` (`allVecs`).
   Keep a vector if it is non-zero, already normalized (its first non-zero
   coordinate is `1`, i.e. `nrm v = v`), and interior by Stage 1 (`intB`). This
   gives the list `verts els` with exactly one representative for each interior
   point. There are `q(q−1)/2` of them: 136 for `q = 17` and 406 for `q = 29`.
3. **Adjacency table** `adjArr`: a Boolean matrix with entry `(i, j)` equal to
   "`disc(sw vᵢ, sw vⱼ)` is a non-square", i.e. the line `vᵢvⱼ` is a passant.
   This defines the **passant graph** on the interior points.
4. **Leaf test** `okA`: given a chosen list of indices `a, b, …`, compute the
   line `ℓ = vₐ × v_b` (cross product), then check three things:
   * `ℓ ≠ 0`;
   * every chosen point lies on `ℓ`;
   * every interior point that lies on `ℓ` was chosen.

   In other words, the chosen set is exactly the set of interior points on the
   line through its first two members.

A set `S` satisfying the hypotheses of the claim is exactly a **clique of size
`k = (q+1)/2` in the passant graph**. The claim for this `q` says that every such
clique passes `okA`.

### Stage 3 – Verified exhaustive clique search (`Search.lean`)

`search adj ok cand len k cl` is a standard branch-and-bound enumeration of the
`k`-cliques contained in the candidate list `cand`. Here `cl` holds the vertices
already chosen. At the first candidate `v` it branches:

* **include `v`**: restrict the candidates to the later vertices adjacent to
  `v` (`rest.filter (adj v)`), add `v` to `cl`, and look for a `(k−1)`-clique;
* **exclude `v`**: continue with `rest`, still looking for a `k`-clique.

**Pruning:** if fewer than `k` candidates remain (`len < k`), the branch is
dropped and counts as a success. When `k` reaches `0`, the finished clique `cl`
is checked with `ok`. Restricting to neighbours at each step keeps the search
small. Each chosen vertex removes about half of the remaining candidates,
because roughly half of all discriminants are non-squares. As a result the
search tree is tiny compared with the `C(406, 15)` subsets of size 15.

**Soundness** (`search_sound`, proved by strong induction on the length of the
candidate list): if the search returns `true` and `cand` has no duplicates, then
for every `k`-clique `K ⊆ cand`, the test `ok` accepts the list `K ∪ cl`.

### Putting it together (`Reduction.lean`)

`statement_of_check` proves the implication:

    search (adjA A) (okA W) (List.range W.size) W.size ((q+1)/2) [] = true
      →  the claim holds for F   (InteriorStatement F)

given that `q` is odd, `els` lists all of `F`, `W = verts els` and
`A = adjArr els`. The proof works as follows:

* Send each point `P ∈ S` to the position of `nrm P.rep` in `W`. This map is
  injective on interior points, so `S` becomes a set `K` of `(q+1)/2` indices.
* The passant hypothesis together with `passantXY_mk_iff` shows that `K` is a
  clique of the table `A`.
* `search_sound` returns a list accepted by `okA`. The line `ℓ` computed there
  is a passant, because it is the line through two points of `S`. The `okA`
  conditions translate back to "`P ∈ S` ⇔ `P` is on `ℓ` and interior".

For a particular `q`, the only thing left to prove is the Boolean equation
itself, e.g. `check29`, which `native_decide` evaluates. Building
`RequestProject.Interior.Q29` takes about 4½ minutes; `Q17` is much faster.

### Counterexamples (`Witness.lean`)

To refute the claim for a particular `q`, give an explicit list of normalized
vectors and check `witnessB`: the entries are distinct, all interior, pairwise
adjacent in the passant graph, and some triple `a, b, c` is not collinear
(`det(a, b, c) = (a × b)·c ≠ 0`). If the list has `(q+1)/2` entries,
`not_statement_of_witness` then proves `¬ InteriorStatement F`. The witnesses
for `q = 5, 13, 25, 27` were found by a separate search outside Lean. Only the
final check is done in Lean, and that check is all the proof relies on.

---

## 4. Running the check for a new value of `q`

* **`q` an odd prime** (e.g. 37, 41): copy `Q29.lean` and replace `29` by `q`
  and `15` by `(q+1)/2`, using `ZMod q` and `els := List.finRange q`. If
  `native_decide` returns `true`, the claim for `q` follows from
  `statement_of_check`. If it returns `false`, some clique fails the test. Find
  one, e.g. by instrumenting the search, and prove the failure with
  `witnessB` / `not_statement_of_witness`.
* **`q` a prime power** (e.g. 9, 49, 81): a concrete computable model of
  `GF(q)` is needed first. As in `GF25.lean` and `GF27.lean`: pick an
  irreducible polynomial, encode elements as numbers `< q`, define the ring
  operations, and check the field axioms by exhaustive computation. Then
  proceed as for primes.
* **Cost**: there are `q(q−1)/2` vertices, the adjacency table has
  `~q⁴/4` entries, and the clique size is `(q+1)/2`. The running time is
  dominated by the clique search. It grows quickly with `q`: `q = 29` already
  takes a few minutes inside Lean. Much larger `q` would need a faster search
  inside the checked code, for example symmetry breaking. The
  stabiliser of the conic, `PGL(2, q)`, acts transitively on interior points, so
  one point of `S` could be fixed in advance. That would require an extra
  (proved) symmetry argument, which has not been implemented.
