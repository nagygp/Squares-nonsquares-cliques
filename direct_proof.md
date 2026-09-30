# Good pairings are `n/x` (q ≡ 1 mod 4): a self-contained algebraic proof

Lean files: `RequestProject/Direct/` (`Coeff`, `Eigen`, `Additive`, `Main`, `Unconditional`).
Main theorem: `CompleteExterior.Direct.goodPairing_eq_div_direct`. It uses no Carlitz–McConnel
hypothesis and no geometry, and depends only on the standard axioms.

Throughout, `q = |F| ≡ 1 (mod 4)`, `χ` is the quadratic character, and `m = (q-1)/2`, which is
even. A *good pairing* `ψ` is an involution of `F*` with `χ(xψx) = -1` that satisfies condition (1)
of the paper.

## Step 0: from good pairings to Paley anti-automorphisms
Set `f(0) = 0` and `f(x) = 1/ψ(x)`. The existing Paley-graph parity count (the "extra property",
`Core.lean`, purely combinatorial) gives `χ((f x - f y)(x - y)) = -1` for all `x ≠ y`
(`quot_nonsquare`). So `f` is an **anti-automorphism** of the Paley graph fixing 0:
`χ(f x - f y) = -χ(x - y)` (`IsAnti`). Because `ψ` is an involution,
`f(1/f(x)) = 1/x` for all `x`.

## Step 1: an eigenvalue identity
Let `κ = Σ_t χ(t(1-t))·t` and `(Tv)(x) = Σ_y χ(x-y)χ(y)v(y)`. For any anti-automorphism `u`
fixing 0, substituting `y ↦ u(y)` gives `Tu = κ·u`. Both sign changes cancel.

Write `coef(v, j) = Σ_x v(x)·x^(q-1-j)`, which for `1 ≤ j ≤ q-2` is minus the coefficient of
`x^j`. Substituting `x = y·s` gives `coef(Tv, j) = ρ_j · coef(v, j)`, where
`ρ_j = Σ_s χ(s-1)·s^(q-1-j)`. Applying this to `v = id` shows `κ = ρ_1`. Expanding
`χ(s-1) = (s-1)^m` with the binomial theorem gives

    ρ_j = -(-1)^j · C(m, j)   (1 ≤ j ≤ q-2),   so ρ_1 = m = -1/2 in F.

Hence **`coef(u, j) ≠ 0` implies `ρ_j = ρ_1`** (`IsAnti.coef_eq_zero`).

## Step 2: anti-automorphisms are additive
* **Consecutive exponents.** `ρ_{k+1} = ρ_k = ρ_1` is impossible. The identity
  `C(m,k+1)(k+1) = C(m,k)(m-k)` would force `m(m+1) = 0`, but `2m+1 = 0` in `F`.
* **Exponents `j ≥ 2` with `p ∤ j`.** Every translate `u(x+c) - u(c)` is again an
  anti-automorphism fixing 0. Suppose `coef(u, j) ≠ 0`. Then `ρ_j = ρ_1`, so `ρ_{j-1} ≠ ρ_1`, so
  the `x^(j-1)` coefficient of every translate is zero. That coefficient is a polynomial in `c` of
  degree `< q`, so the polynomial is identically zero. Its linear coefficient is
  `j·(coefficient of x^j in u)`, so `coef(u, j) = 0`, a contradiction.
* **General exponents.** If `j = p^b·j'` with `p ∤ j'` and `j' ≥ 2`, then `u(x^(p^(e-b)))`
  (where `q = p^e`) is again an anti-automorphism fixing 0. Its `j'`-th coefficient equals the
  `j`-th coefficient of `u`, which reduces this case to the previous one.

So only the exponents `p^b` can appear, which means `u` is additive (`IsAnti.map_add`). This
argument does not use the binomial-coefficient theorem of Lucas.

## Step 3: Hua's identity
For `x ≠ 0, 1` we have `x² = x - (x⁻¹ + (1-x)⁻¹)⁻¹`. Apply `f`, using additivity and
`f(1/f(z)) = 1/z`: this gives `f(x²) = f(x)²/f(1)`. Polarising then shows that
`σ = f/f(1)` is a field automorphism. From `f(1/f(x)) = 1/x` we get `σ(f 1) = f 1` and `σ² = id`.
Also `f(1) = 1/ψ(1)` is a non-square. The existing fixed-field lemma
`ringHom_eq_self_of_involutive` then gives `σ = id`, so `f(x) = f(1)·x`. Therefore
`ψ(x) = n/x` with `n = 1/f(1)` a non-square.

## Consequence
`Direct.complete_exterior_set_eq_exterior_points_of_passant'` is the paper's main theorem with the
Carlitz–McConnel hypothesis removed.
