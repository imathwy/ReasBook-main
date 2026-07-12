import Mathlib
import StacksProject_2024.Chap14.Definition_14_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

/-- The constant `0`-simplex of `Δ[1]` in cosimplicial degree `n`. -/
def deltaOneZeroEndpoint
    (n : SimplexCategory) : (Δ[1] : SSet).obj (op n) :=
  SSet.stdSimplex.const 1 0 (op n)

/-- The constant `1`-simplex of `Δ[1]` in cosimplicial degree `n`. -/
def deltaOneOneEndpoint
    (n : SimplexCategory) : (Δ[1] : SSet).obj (op n) :=
  SSet.stdSimplex.const 1 1 (op n)

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {U V : CosimplicialObject C}

/- Domain-style sampling for Definition 14.28.1:
- primary domain: cosimplicial homotopies defined through the standard `1`-simplex cotensor;
- inspected same-kind owner declarations:
  `CategoryTheory.homFromSimplicialSet`,
  `CategoryTheory.homFromSimplicialSet_map_π`,
  `CategoryTheory.SimplicialObject.Homotopy`,
  `CategoryTheory.SimplicialObject.Homotopic`,
  `Relation.EqvGen`;
- target layer: `source-facing`;
- core/canonical owner:
  `homFromSimplicialSet (Δ[1] : SSet) V`, built from the more general owner
  `homFromCosimplicialSet`;
- canonical owner for the zigzag relation: `Relation.EqvGen` on directed homotopies;
- bridge/view data: degreewise evaluation at a simplex `α : [n] ⟶ [1]`, derived from the
  source-facing owner and its canonical projection square `homFromSimplicialSet_map_π`.
-/

/-- Definition 14.28.1: a homotopy from `a` to `b` is a morphism `U ⟶ Hom(Δ[1], V)` whose
endpoint evaluations recover `a` and `b`. -/
structure Homotopy (a b : U ⟶ V) where
  /-- The underlying map to the standard `1`-simplex cotensor. -/
  hom : U ⟶ homFromSimplicialSet (Δ[1] : SSet) V
  /-- Evaluation at the constant `0` simplex recovers `a`. -/
  zero_endpoint (n : SimplexCategory) :
    hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (deltaOneZeroEndpoint n) =
      a.app n
  /-- Evaluation at the constant `1` simplex recovers `b`. -/
  one_endpoint (n : SimplexCategory) :
    hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (deltaOneOneEndpoint n) =
      b.app n

namespace Homotopy

@[ext] theorem ext {a b : U ⟶ V} {H K : Homotopy a b}
    (h : H.hom = K.hom) : H = K := by
  cases H with
  | mk hom zero_endpoint one_endpoint =>
    cases K with
    | mk hom' zero_endpoint' one_endpoint' =>
      cases h
      have hzero : zero_endpoint = zero_endpoint' := Subsingleton.elim _ _
      cases hzero
      have hone : one_endpoint = one_endpoint' := Subsingleton.elim _ _
      cases hone
      rfl

/-- Evaluating a cosimplicial homotopy at a simplex of `Δ[1]` gives the corresponding degreewise
component map `U_n ⟶ V_n`. -/
def app {a b : U ⟶ V} (H : Homotopy a b) {n : SimplexCategory}
    (α : (Δ[1] : SSet).obj (op n)) : U.obj n ⟶ V.obj n :=
  H.hom.app n ≫ Pi.π (fun _ ↦ V.obj n) α

instance {a b : U ⟶ V} :
    CoeFun (Homotopy a b) (fun _ ↦ ∀ ⦃n : SimplexCategory⦄,
      (Δ[1] : SSet).obj (op n) → (U.obj n ⟶ V.obj n)) where
  coe H := fun {_} α ↦ H.app α

@[simp] theorem app_zero_endpoint {a b : U ⟶ V} (H : Homotopy a b) (n : SimplexCategory) :
    H (deltaOneZeroEndpoint n) = a.app n :=
  H.zero_endpoint n

@[simp] theorem app_one_endpoint {a b : U ⟶ V} (H : Homotopy a b) (n : SimplexCategory) :
    H (deltaOneOneEndpoint n) = b.app n :=
  H.one_endpoint n

/-- Evaluating a cosimplicial homotopy at a simplex of `Δ[1]` is compatible with the
cosimplicial structure maps via the canonical commutative square. -/
theorem naturality {a b : U ⟶ V} (H : Homotopy a b)
    {m n : SimplexCategory} (f : n ⟶ m) (α : (Δ[1] : SSet).obj (op m)) :
    CommSq (U.map f) (H ((Δ[1] : SSet).map f.op α)) (H α) (V.map f) := by
  simpa [Homotopy.app] using
    (homFromSimplicialSet_hom_naturality
      (U := (Δ[1] : SSet))
      (V := V)
      H.hom
      f
      α)

end Homotopy

/-- Two morphisms of cosimplicial objects are homotopic if they are connected by a finite zigzag
of directed cosimplicial homotopies. -/
def Homotopic (a b : U ⟶ V) : Prop :=
  Relation.EqvGen
    (fun f g : U ⟶ V ↦ Nonempty (Homotopy f g))
    a b

@[refl] lemma Homotopic.refl (a : U ⟶ V) : Homotopic a a :=
  Relation.EqvGen.refl a

@[symm] lemma Homotopic.symm {a b : U ⟶ V} (h : Homotopic a b) : Homotopic b a := by
  simpa [Homotopic] using Relation.EqvGen.symm a b h

@[trans] lemma Homotopic.trans {a b c : U ⟶ V}
    (hab : Homotopic a b) (hbc : Homotopic b c) : Homotopic a c := by
  simpa [Homotopic] using Relation.EqvGen.trans a b c hab hbc

-- Proof sketch: a directed cosimplicial homotopy is one generating relation for the equivalence
-- closure defining `Homotopic`.
/-- A directed cosimplicial homotopy gives the associated zigzag homotopy relation. -/
lemma Homotopic.of_homotopy {a b : U ⟶ V} (h : Homotopy a b) : Homotopic a b :=
  Relation.EqvGen.rel a b ⟨h⟩

end CategoryTheory.CosimplicialObject
