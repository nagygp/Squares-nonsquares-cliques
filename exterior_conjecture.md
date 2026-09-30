# The conjecture of the final remarks (q ≡ 3 mod 4)

In the final remarks of their paper, Blokhuis, Seress and Wilbrink report
computer searches (by themselves and by A. Brouwer) and conjecture:

> for `q ≡ 3 (mod 4)` and `q > 31` every complete exterior set of a conic in
> `PG(2, q)` consists of the exterior points on a passant.

They add that they have no idea how to prove it. This note describes what was
done in this project. All Lean files named here are in `RequestProject/Q3mod4/`.

## Status

**The conjecture is not proved in general.** It is stated as
`exterior_conjecture` (`Statement.lean`) and its proof is `sorry`. The following
results are proved.

| Result | Lean name | File | How |
|---|---|---|---|
| Statement of the conjecture | `exterior_conjecture` | `Statement.lean` | **open (`sorry`)** |
| For every odd `q`: "all complete exterior sets are linear" ⇔ "all good pairings of `GF(q)*` are `x ↦ n/x`" | `exteriorSetsLinear_iff` | `Statement.lean` | general proof |
| Conjecture holds for every field with `31 < q ≤ 131` | `exterior_conjecture_of_le_131` | `Main.lean` | verified search, one file per prime |
| Individual primes `q = 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131` | `exteriorSetsLinear_43`, … | `P43.lean`, … | verified search (`native_decide`) |
| Conjecture fails for `q = 7, 11, 19, 23, 27, 31` | `not_exteriorSetsLinear_7`, … | `Counterexamples.lean` | explicit witnesses, kernel `decide` |
| Paper's main theorem in this language (`q ≡ 1 mod 4`, assuming Carlitz–McConnel) | `exteriorSetsLinear_of_mod_four_eq_one` | `Statement.lean` | from the main theorem |

So the bound `q > 31` is sharp, and the conjecture is verified in Lean on
exactly the range `43 ≤ q ≤ 131` of Brouwer's search. In that range every
`q ≡ 3 (mod 4)` that is a prime power is prime (`prime_of_isPrimePow_of_range`),
and any field of prime order is isomorphic to `ZMod q`, so the result covers all
finite fields in the range.

The checks for particular primes use `native_decide`, so they also trust the
Lean compiler (axiom `Lean.ofReduceBool`). The counterexamples use only kernel
`decide`.

## The reduction (valid for all odd q)

The first part of the paper's proof never uses `q ≡ 1 (mod 4)`. A reflection
preserving the conic moves one point of the set to `(0:1:0)`, the exterior point
whose tangency points have parameters `0` and `∞`. Labelling every other point by
its two tangency parameters `{x, ψ(x)}` gives an involution `ψ` of `GF(q)*` (a
*good pairing*, `GoodPairing` in `Core.lean`) such that

* `x · ψ(x)` is a non-square, so each pair has one square and one non-square;
* `(x − y)(x − ψy)(ψx − y)(ψx − ψy)` is a non-square for distinct pairs
  (condition (1) of the paper).

The set lies on a passant exactly when `ψ(x) = n/x` for a non-square `n`.

To make this reusable, the earlier theorems `alg_core_normalized` and `alg_core`
now take the hypothesis `PairingsLinear F` ("every good pairing is `x ↦ n/x`")
instead of `q ≡ 1 (mod 4)` together with Carlitz–McConnel. The main theorem
supplies that hypothesis through `goodPairing_eq_div`, and its statement is
unchanged. The converse direction
(`pairingsLinear_of_exteriorSetsLinear`) is new. From a good pairing it builds
the complete exterior set made of `(0:1:0)` and the points labelled `(s, ψ s)`
for `s` a non-zero square. If that set lies on a line, `ψ` must be `x ↦ n/x`.

For `q ≡ 1 (mod 4)` the paper shows `PairingsLinear` with a parity count in the
Paley graph followed by Carlitz–McConnel. For `q ≡ 3 (mod 4)` the Paley graph is
not defined, because `−1` is a non-square. The counterexamples below 32 show that
any proof must use that `q` is large, for instance through character-sum
estimates. No such argument was found.

## How the finite checks work

`PairSearch.lean` contains a backtracking search whose soundness is proved in Lean
(`pairSearch_sound`, `pairingsLinear_of_search`):

1. The squares `s ≠ 1` are processed in a fixed order. Each is given a non-square
   partner `n` compatible with all pairs chosen so far, meaning that
   `(s−c)(s−d)(n−c)(n−d)` is a non-square.
2. At each leaf the search checks that all products `s · ψ(s)` are equal. This
   makes the pairing `x ↦ n/x` (`GoodPairing.linear_of_prod`).
3. **Symmetry reduction.** Good pairings are preserved by the scalings
   `ψ ↦ (x ↦ ψ(cx)/c)` (`GoodPairing.scale`). So we may assume that the partner
   `m` of `1` minimises `key(ψ(x)/x)` (here `key = ZMod.val`), and the search
   prunes every candidate whose ratio `n/s` or `s/n` has a smaller key. This cuts
   the search tree by about a factor of ten.

`ZModSearch.lean` supplies the data for `ZMod p`: a table of squares and a table
of inverses, each checked against its specification by `native_decide`, plus the
lists of squares and non-squares. For `q = 131` the search visits about 600,000
nodes, and the whole set of eleven primes takes about ten minutes of build time
in parallel.

## Not verified

Outside Lean, computations with an unoptimised search (plain C, not checked)
gave the same answer for `139 ≤ q ≤ 179`: every good pairing is linear. **These
were not checked in Lean.** To check a further prime `p ≡ 3 (mod 4)`, copy
`P131.lean` and change the number. The cost grows roughly like the search-tree
size, which is about 1.4 million nodes for `q = 151`.
