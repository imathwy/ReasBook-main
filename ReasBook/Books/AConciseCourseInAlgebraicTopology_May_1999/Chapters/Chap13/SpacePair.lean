import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Equiv

open CategoryTheory
open HomotopicalAlgebra
open scoped unitInterval

universe u

-- Semantic recall via `lean_leansearch` and local precedent from Chapters 14 and 19:
-- weak-equivalence structure is handled by `[CategoryWithWeakEquivalences C]` together with
-- `[WeakEquivalence f]`. This file therefore fixes one concrete weak-equivalence owner on
-- `SpacePair`, modeled by homotopy-equivalence data on the ambient spaces that is compatible
-- with the chosen subspaces.

/-- A pair of spaces `(X, A)` with `A ⊆ X`. -/
structure SpacePair where
  space : TopCat.{u}
  subspace : Set space

namespace SpacePair

/-- A map of pairs `(X, A) ⟶ (Y, B)` is a continuous map `X ⟶ Y` sending `A` into `B`. -/
structure Hom (P Q : SpacePair.{u}) where
  hom : P.space ⟶ Q.space
  map_subspace' {x : P.space} (hx : x ∈ P.subspace) : hom x ∈ Q.subspace

attribute [simp] Hom.map_subspace'

/-- Two maps of pairs are equal when their underlying maps of spaces are equal. -/
@[ext] theorem hom_ext {P Q : SpacePair.{u}} (f g : Hom P Q) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity map of a pair. -/
def id (P : SpacePair.{u}) : Hom P P where
  hom := 𝟙 P.space
  map_subspace' := by
    intro x hx
    simpa using hx

/-- The composite of maps of pairs. -/
def comp {P Q R : SpacePair.{u}} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  map_subspace' := by
    intro x hx
    exact g.map_subspace' (f.map_subspace' hx)

/-- The category of pairs of spaces. -/
instance : Category SpacePair where
  Hom P Q := Hom P Q
  id := id
  comp f g := comp f g
  id_comp := by
    intro P Q f
    ext
    rfl
  comp_id := by
    intro P Q f
    ext
    rfl
  assoc := by
    intro P Q R S f g h
    ext
    rfl

namespace Hom

/-- The predicate saying that a continuous map `P.space ⟶ Q.space` carries the distinguished
subspace of `P` into the distinguished subspace of `Q`. -/
def mapSubspaceCondition (P Q : SpacePair.{u}) : C(P.space, Q.space) → Prop :=
  fun f ↦ Set.MapsTo f P.subspace Q.subspace

/-- A homotopy of maps of pairs is a homotopy through maps carrying the distinguished subspace of
the source pair into the distinguished subspace of the target pair. -/
abbrev Homotopy {P Q : SpacePair.{u}} (f₀ f₁ : P ⟶ Q) : Type _ :=
  ContinuousMap.HomotopyWith f₀.hom.hom f₁.hom.hom (mapSubspaceCondition P Q)

namespace Homotopy

/-- Every stage of a homotopy of pair maps is again a map carrying the distinguished subspace of
the source pair into that of the target pair. -/
theorem mapsTo {P Q : SpacePair.{u}} {f₀ f₁ : P ⟶ Q} (H : Homotopy f₀ f₁) (t : I) :
    Set.MapsTo (H.toHomotopy.curry t) P.subspace Q.subspace :=
  H.prop t

end Homotopy

/-- Two maps of pairs are homotopic when they are connected by a homotopy through pair maps. -/
abbrev Homotopic {P Q : SpacePair.{u}} (f₀ f₁ : P ⟶ Q) : Prop :=
  ContinuousMap.HomotopicWith f₀.hom.hom f₁.hom.hom (mapSubspaceCondition P Q)

namespace Homotopic

/-- Every map of pairs is homotopic to itself through pair maps. -/
theorem refl {P Q : SpacePair.{u}} (f : P ⟶ Q) : Homotopic f f :=
  ContinuousMap.HomotopicWith.refl f.hom.hom <| by
    intro x hx
    simpa using f.map_subspace' hx

/-- Homotopy through pair maps is symmetric. -/
@[symm] theorem symm {P Q : SpacePair.{u}} {f₀ f₁ : P ⟶ Q} (h : Homotopic f₀ f₁) :
    Homotopic f₁ f₀ :=
  ContinuousMap.HomotopicWith.symm h

/-- Homotopy through pair maps is transitive. -/
@[trans] theorem trans {P Q : SpacePair.{u}} {f₀ f₁ f₂ : P ⟶ Q}
    (h₀ : Homotopic f₀ f₁) (h₁ : Homotopic f₁ f₂) : Homotopic f₀ f₂ :=
  ContinuousMap.HomotopicWith.trans h₀ h₁

end Homotopic
end Hom

/-- The absolute pair `(X, ∅)`. -/
def absolute (X : TopCat.{u}) : SpacePair where
  space := X
  subspace := ∅

/-- The base pair `(*, ∅)`. -/
def point : SpacePair :=
  absolute (TopCat.of PUnit)

/-- The subspace `A` of a pair `(X, A)`, regarded as the absolute pair `(A, ∅)`. -/
def subspaceAbsolute (P : SpacePair.{u}) : SpacePair where
  space := TopCat.of P.subspace
  subspace := ∅

/-- The pair `(X \ U, A \ U)` obtained by excising a subset `U ⊆ X`. -/
def removeSubset (P : SpacePair.{u}) (U : Set P.space) : SpacePair where
  space := TopCat.of { x : P.space // x ∉ U }
  subspace := { x | x.1 ∈ P.subspace }

/-- The coproduct pair `∐ i, (Xᵢ, Aᵢ)` with underlying sigma space and sigma subspace. -/
def sigmaPair {ι : Type u} (P : ι → SpacePair.{u}) : SpacePair where
  space := TopCat.of (Sigma fun i ↦ (P i).space)
  subspace := { x | x.2 ∈ (P x.1).subspace }

/-- The inclusion `(A, ∅) ⟶ (X, ∅)` attached to a pair `(X, A)`. -/
def subspaceInclusion (P : SpacePair.{u}) : subspaceAbsolute P ⟶ absolute P.space where
  hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  map_subspace' := by
    intro x hx
    cases hx

/-- The identity map `(X, ∅) ⟶ (X, A)` on the ambient space of a pair. -/
def absoluteToRelative (P : SpacePair.{u}) : absolute P.space ⟶ P where
  hom := 𝟙 P.space
  map_subspace' := by
    intro x hx
    cases hx

/-- The inclusion `(X \ U, A \ U) ⟶ (X, A)` induced by the subtype embedding. -/
def removeSubsetInclusion (P : SpacePair.{u}) (U : Set P.space) : removeSubset P U ⟶ P where
  hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  map_subspace' := by
    intro x hx
    exact hx

/-- The endofunctor `(X, A) ↦ (X, ∅)`. -/
def ambientFunctor : SpacePair.{u} ⥤ SpacePair.{u} where
  obj P := absolute P.space
  map f := {
    hom := f.hom
    map_subspace' := by
      intro x hx
      cases hx
  }
  map_id := by
    intro P
    apply hom_ext
    rfl
  map_comp := by
    intro P Q R f g
    apply hom_ext
    rfl

/-- The endofunctor `(X, A) ↦ (A, ∅)`. -/
def subspaceFunctor : SpacePair.{u} ⥤ SpacePair.{u} where
  obj P := subspaceAbsolute P
  map f := {
    hom :=
      TopCat.ofHom
        ⟨fun x ↦ ⟨f.hom x.1, f.map_subspace' x.2⟩,
          ((map_continuous f.hom.hom).comp continuous_subtype_val).subtype_mk
            fun x ↦ f.map_subspace' x.2⟩
    map_subspace' := by
      intro x hx
      cases hx
  }
  map_id := by
    intro P
    apply hom_ext
    ext x
    rfl
  map_comp := by
    intro P Q R f g
    apply hom_ext
    ext x
    rfl

/-- The natural inclusion `(A, ∅) ⟶ (X, ∅)` over all pairs `(X, A)`. -/
def subspaceInclusionNatTrans : subspaceFunctor ⟶ ambientFunctor where
  app P := (subspaceInclusion P : subspaceFunctor.obj P ⟶ ambientFunctor.obj P)
  naturality := by
    intro P Q f
    apply hom_ext
    ext x
    rfl

/-- The natural comparison `(X, ∅) ⟶ (X, A)` over all pairs `(X, A)`. -/
def absoluteToRelativeNatTrans : ambientFunctor ⟶ 𝟭 SpacePair.{u} where
  app P := (absoluteToRelative P : ambientFunctor.obj P ⟶ (𝟭 SpacePair).obj P)
  naturality := by
    intro P Q f
    apply hom_ext
    ext x
    rfl

end SpacePair

open scoped ContinuousMap
open SpacePair

/-- A map of pairs is a weak equivalence when its underlying map of spaces is part of a homotopy
equivalence whose inverse also carries the chosen subspace of the target back into the chosen
subspace of the source. -/
def SpacePair.IsWeakEquivalence {P Q : SpacePair.{u}} (f : P ⟶ Q) : Prop :=
  ∃ e : P.space ≃ₕ Q.space,
    e.toFun = f.hom.hom ∧ ∀ ⦃y : Q.space⦄, y ∈ Q.subspace → e.symm y ∈ P.subspace

/-- The intended weak-equivalence structure on pairs of spaces used for relative homology in this
chapter, formalized here by homotopy-equivalence data on the ambient spaces compatible with the
designated subspaces. -/
@[reducible] instance spacePairWeakEquivalences : CategoryWithWeakEquivalences SpacePair.{u} where
  weakEquivalences _ _ f := SpacePair.IsWeakEquivalence f

/-- For the canonical Chapter 13 weak-equivalence owner on `SpacePair`, the typeclass-level weak
equivalences are exactly the source-facing predicate `SpacePair.IsWeakEquivalence`. -/
theorem spacePair_weakEquivalence_iff {P Q : SpacePair.{u}} (f : P ⟶ Q) :
    WeakEquivalence f ↔ SpacePair.IsWeakEquivalence f := by
  rw [weakEquivalence_iff]
  rfl
