module

public import RequestProject.Interior.Criteria
public import RequestProject.Interior.Search

/-!
# Computable data for the exhaustive check

For a finite field `F` given together with a list `els` of all its elements we compute
* the list `verts els` of normalized coordinate vectors of the interior points of `x y = z²`;
* the adjacency relation "the joining line is a passant", via the discriminant criterion;
* a test `okA` checking that a set of interior points is the set of all interior points on the
  line joining its first two members.
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization Matrix

namespace InteriorPassant

open CompleteExterior

variable {F : Type*} [Field F] [DecidableEq F]

/-- Squareness test, given a list of all field elements. -/
def sqB (els : List F) (x : F) : Bool := els.any fun r => decide (x = r * r)

/-- Normalization of a coordinate vector: the first non-zero coordinate is made `1`. -/
def nrm (v : Fin 3 → F) : Fin 3 → F :=
  if v 0 ≠ 0 then (v 0)⁻¹ • v else if v 1 ≠ 0 then (v 1)⁻¹ • v else (v 2)⁻¹ • v

/-- All coordinate vectors built from the list `els`. -/
def allVecs (els : List F) : List (Fin 3 → F) :=
  els.flatMap fun a => els.flatMap fun b => els.map fun c => ![a, b, c]

/-- Normalized coordinate vectors of interior points of `x y = z²`. -/
def intB (els : List F) (v : Fin 3 → F) : Bool :=
  decide (v ≠ 0) && decide (nrm v = v) && !sqB els (cf (sw v))

/-- The list of (normalized coordinate vectors of) interior points. -/
def verts (els : List F) : List (Fin 3 → F) := (allVecs els).filter (intB els)

/-- Adjacency: the line joining the two points is a passant. -/
def adjB (els : List F) (v w : Fin 3 → F) : Bool := !sqB els (disc (sw v) (sw w))

/-- Cross product (coordinates of the line joining two points). -/
def cr (a b : Fin 3 → F) : Fin 3 → F :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- Dot product. -/
def dt (a b : Fin 3 → F) : F := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- The adjacency table between the interior points (indexed by position in `verts els`). -/
def adjArr (els : List F) : Array (Array Bool) :=
  Array.ofFn fun i : Fin (verts els).length =>
    Array.ofFn fun j : Fin (verts els).length => adjB els (verts els)[i] (verts els)[j]

/-- Adjacency lookup in a table. -/
def adjA (A : Array (Array Bool)) (i j : ℕ) : Bool := (A.getD i #[]).getD j false

/-- Leaf test: the chosen points (given by indices into `W`) are exactly the points of `W` on the
line joining the first two of them. -/
def okA (W : Array (Fin 3 → F)) : List ℕ → Bool
  | a :: b :: rest =>
      let l := cr (W.getD a 0) (W.getD b 0)
      decide (l ≠ 0) && (a :: b :: rest).all (fun i => decide (dt l (W.getD i 0) = 0)) &&
        (List.range W.size).all (fun j => decide (dt l (W.getD j 0) ≠ 0) || (a :: b :: rest).contains j)
  | _ => false

end InteriorPassant
