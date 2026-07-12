import Mathlib
import StacksProject_2024.Chap14.Definition_14_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

universe u v u' v'

noncomputable section

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

/- Domain-style sampling for Remark 14.28.2:
- primary domain: cosimplicial homotopies for cosimplicial objects, with the product-free
  `Δ[1]`-indexed family description bridged to the canonical cotensor-style owner;
- inspected same-kind owner declarations:
  `CategoryTheory.homFromCosimplicialSet`,
  `CategoryTheory.homFromCosimplicialSet_map_π`,
  `CategoryTheory.CosimplicialObject.Homotopy`,
  `CategoryTheory.CosimplicialObject.Homotopic`;
- best owner abstraction: the canonical owner remains `Homotopy a b`, built from
  `homFromCosimplicialSet (Δ[1] : SSet) V`;
- primitive data here are exactly the degreewise maps `h_{n,α}` with endpoints and naturality;
  the `Hom(Δ[1], V)`-valued map and the zigzag relation are derived by bridge constructions, so
  this file should keep the source-facing family formulation but reuse the upstream owner API for
  the canonical comparison. -/

/-- Remark 14.28.2: a product-free homotopy from `a` to `b` is a family of maps
`h_{n,\alpha} : U_n ⟶ V_n`, indexed by simplices `α ∈ Δ[1]_n`, with the specified endpoints and
naturality. In categories with finite products this is equivalent to the `Hom(Δ[1], V)`-based
formulation of Definition 14.28.1. -/
@[stacks 0FKJ]
structure DeltaOneHomotopy (a b : U ⟶ V) where
  /-- The degreewise component indexed by a simplex `α : [n] ⟶ [1]`. -/
  hom {n : SimplexCategory} (i : (Δ[1] : SSet.{0}).obj (Opposite.op n)) : U.obj n ⟶ V.obj n
  /-- The component at the constant `0` simplex recovers `a`. -/
  zero_endpoint (n : SimplexCategory) :
    hom (deltaOneZeroEndpoint n) = a.app n
  /-- The component at the constant `1` simplex recovers `b`. -/
  one_endpoint (n : SimplexCategory) :
    hom (deltaOneOneEndpoint n) = b.app n
  /-- The family `h_{n,\alpha}` is natural in the simplex operator via the canonical
  commutative square. -/
  naturality {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
      (i : (Δ[1] : SSet).obj (Opposite.op n₂)) :
    CommSq (U.map σ) (hom ((Δ[1] : SSet).map σ.op i)) (hom i) (V.map σ)

namespace DeltaOneHomotopy

@[ext] theorem ext {H K : DeltaOneHomotopy a b}
    (h : ∀ ⦃n : SimplexCategory⦄, (i : (Δ[1] : SSet.{0}).obj (Opposite.op n)) →
      H.hom i = K.hom i) : H = K := by
  cases H with
  | mk hom zero_endpoint one_endpoint naturality =>
    cases K with
    | mk hom' zero_endpoint' one_endpoint' naturality' =>
      have hhom : @hom = @hom' := by
        funext n i
        exact h i
      cases hhom
      have hzero : zero_endpoint = zero_endpoint' := Subsingleton.elim _ _
      cases hzero
      have hone : one_endpoint = one_endpoint' := Subsingleton.elim _ _
      cases hone
      have hnat : @naturality = @naturality' := by
        exact Subsingleton.elim _ _
      cases hnat
      rfl

/-- A `Δ[1]`-indexed homotopy can be evaluated at a simplex in each degree to recover its
underlying family of component morphisms. -/
instance :
    CoeFun (DeltaOneHomotopy a b) (fun _ ↦ ∀ ⦃n : SimplexCategory⦄,
      (Δ[1] : SSet.{0}).obj (Opposite.op n) → (U.obj n ⟶ V.obj n)) where
  coe H := fun {_} i ↦ H.hom i

/-- Any functor carries a `Δ[1]`-indexed homotopy to the induced `Δ[1]`-indexed homotopy between
the whiskered morphisms. -/
def whiskerRight (H : DeltaOneHomotopy a b) (F : C ⥤ D) :
    DeltaOneHomotopy (Functor.whiskerRight a F) (Functor.whiskerRight b F) where
  hom i := F.map (H.hom i)
  zero_endpoint n := by
    simpa using congrArg F.map (H.zero_endpoint n)
  one_endpoint n := by
    simpa using congrArg F.map (H.one_endpoint n)
  naturality σ i := by
    simpa using (H.naturality σ i).map F

section

variable [HasFiniteProducts C]

/-- In a category with finite products, a `Δ[1]`-indexed family of components assembles into the
canonical `Hom(Δ[1], V)`-valued cosimplicial homotopy. -/
def toHomotopy (H : DeltaOneHomotopy a b) : Homotopy a b where
  hom :=
    { app := fun n ↦ Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i)
      naturality := by
        intro n₁ n₂ σ
        apply Pi.hom_ext
        intro i
        calc
          (U.map σ ≫
              Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₂) ↦ H.hom i)) ≫
              Pi.π (fun _ ↦ V.obj n₂) i
              = U.map σ ≫ H.hom i := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ U.map σ ≫ k)
                      (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₂) ↦ H.hom i) i)
          _ = H.hom ((Δ[1] : SSet).map σ.op i) ≫ V.map σ := (H.naturality σ i).w
          _ = ((Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)) ≫
                Pi.π (fun _ ↦ V.obj n₁) ((Δ[1] : SSet).map σ.op i)) ≫ V.map σ := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ k ≫ V.map σ)
                      (Pi.lift_π
                        (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)
                        ((Δ[1] : SSet).map σ.op i)).symm
          _ = ((Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)) ≫
                (homFromSimplicialSet (Δ[1] : SSet) V).map σ) ≫
                Pi.π (fun _ ↦ V.obj n₂) i := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦
                        (Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)) ≫ k)
                      ((homFromSimplicialSet_map_π (Δ[1] : SSet) V σ i).w).symm }
  zero_endpoint n := by
    exact
      (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i)
        (deltaOneZeroEndpoint n)).trans (H.zero_endpoint n)
  one_endpoint n := by
    exact
      (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i)
        (deltaOneOneEndpoint n)).trans (H.one_endpoint n)

/-- The canonical `Hom(Δ[1], V)`-valued homotopy can be evaluated at each simplex of `Δ[1]` to
recover the product-free family formulation. -/
def ofHomotopy (H : Homotopy a b) : DeltaOneHomotopy a b where
  hom i := H.app i
  zero_endpoint := H.app_zero_endpoint
  one_endpoint := H.app_one_endpoint
  naturality σ i := by
    simpa [Homotopy.app] using H.naturality σ i

@[simp] theorem ofHomotopy_toHomotopy (H : DeltaOneHomotopy a b) :
    ofHomotopy H.toHomotopy = H := by
  apply ext
  intro n i
  simpa [ofHomotopy, toHomotopy] using
    Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i) i

@[simp] theorem toHomotopy_ofHomotopy (H : Homotopy a b) :
    (ofHomotopy H).toHomotopy = H := by
  apply Homotopy.ext
  ext n
  apply Pi.hom_ext
  intro i
  simpa [ofHomotopy, toHomotopy] using
    (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.app i) i)

/-- Under finite products, the source-facing `Δ[1]`-indexed family formulation and the canonical
cotensor-valued homotopy notion are equivalent as directed homotopy data. -/
def equivHomotopy : DeltaOneHomotopy a b ≃ Homotopy a b where
  toFun := toHomotopy
  invFun := ofHomotopy
  left_inv := ofHomotopy_toHomotopy
  right_inv := toHomotopy_ofHomotopy

end

end DeltaOneHomotopy

/-- Two morphisms of cosimplicial objects are `Δ[1]`-homotopic if they are connected by a finite
zigzag of directed `Δ[1]`-indexed homotopies in either direction. -/
def DeltaOneHomotopic (a b : U ⟶ V) : Prop :=
  Relation.EqvGen (fun f g : U ⟶ V ↦ Nonempty (DeltaOneHomotopy f g)) a b

@[refl] lemma DeltaOneHomotopic.refl (a : U ⟶ V) : DeltaOneHomotopic a a :=
  Relation.EqvGen.refl a

@[symm] lemma DeltaOneHomotopic.symm {a b : U ⟶ V} (h : DeltaOneHomotopic a b) :
    DeltaOneHomotopic b a := by
  simpa [DeltaOneHomotopic] using Relation.EqvGen.symm a b h

@[trans] lemma DeltaOneHomotopic.trans {a b c : U ⟶ V}
    (hab : DeltaOneHomotopic a b) (hbc : DeltaOneHomotopic b c) :
    DeltaOneHomotopic a c := by
  simpa [DeltaOneHomotopic] using Relation.EqvGen.trans a b c hab hbc

-- Proof sketch: a directed `Δ[1]`-indexed homotopy contributes one generating step in the
-- defining relation for `DeltaOneHomotopic`, so apply `Relation.EqvGen.rel`.
/-- A directed `Δ[1]`-indexed homotopy gives the corresponding zigzag homotopy relation. -/
theorem DeltaOneHomotopic.of_homotopy (h : DeltaOneHomotopy a b) :
    DeltaOneHomotopic a b :=
  Relation.EqvGen.rel a b ⟨h⟩

-- Proof sketch: send each generating directed homotopy step of the zigzag to its image under
-- `DeltaOneHomotopy.whiskerRight`; the induced map on generators extends to the whiskered
-- zigzag.
/-- Functors preserve the zigzag relation generated by `Δ[1]`-indexed cosimplicial homotopies. -/
theorem DeltaOneHomotopic.whiskerRight (h : DeltaOneHomotopic a b) (F : C ⥤ D) :
    DeltaOneHomotopic (Functor.whiskerRight a F) (Functor.whiskerRight b F) := by
  induction h with
  | rel x y hxy =>
      exact DeltaOneHomotopic.of_homotopy (hxy.some.whiskerRight F)
  | refl x =>
      exact DeltaOneHomotopic.refl (Functor.whiskerRight x F)
  | symm x y hxy ih =>
      exact DeltaOneHomotopic.symm ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact DeltaOneHomotopic.trans ihxy ihyz

section

variable [HasFiniteProducts C]

/-- Under finite products, the zigzag relation generated by the product-free `Δ[1]`-indexed
families agrees with the canonical cotensor-valued homotopy relation. -/
theorem deltaOneHomotopic_iff_homotopic :
    DeltaOneHomotopic a b ↔ Homotopic a b := by
  refine ⟨?_, ?_⟩
  · intro h
    simpa [DeltaOneHomotopic, Homotopic] using
      (Relation.EqvGen.mono
        (fun x y hxy ↦ ⟨hxy.some.toHomotopy⟩)
        h)
  · intro h
    simpa [DeltaOneHomotopic, Homotopic] using
      (Relation.EqvGen.mono
        (fun x y hxy ↦ ⟨DeltaOneHomotopy.ofHomotopy hxy.some⟩)
        h)

end

end CategoryTheory.CosimplicialObject
