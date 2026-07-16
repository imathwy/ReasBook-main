import stacks_proof.stacks_project.Chap13.Definition_13_3_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe vA vA' vD vD' uA uA' uD uD'

namespace CategoryTheory

namespace DeltaFunctor

/-
Domain-style sampling for Lemma 13.4.21:
- primary domain: composition of `δ`-functors with exact functors on the triangulated target side
  and on the abelian source side;
- sampled owner declarations in this domain:
  `CategoryTheory.DeltaFunctor`,
  `CategoryTheory.Functor.map_distinguished`,
  `CategoryTheory.Functor.commShiftIso_hom_naturality`,
  `ShortComplex.ShortExact.map_of_exact`;
- best owner abstraction: the public source-facing owners are the two composition constructors
  `DeltaFunctor.postcomposeExactFunctor` and `DeltaFunctor.precomposeExactFunctor`; the mapped
  distinguished-triangle and naturality facts are derived fields of those owners, not separate
  public wrapper theorems;
- primitive data: a `DeltaFunctor G`, together with either an exact triangulated functor
  `F : D ⥤ D'` or an exact functor `H : A' ⥤ₑ A` between abelian categories;
- derived API: the resulting composite `DeltaFunctor`s and their underlying-functor
  identification lemmas;
- source/core/bridge triage:
  `source-facing`: `DeltaFunctor.postcomposeExactFunctor` and
    `DeltaFunctor.precomposeExactFunctor`;
  `core/canonical`: `DeltaFunctor`, `Functor.map_distinguished`,
    `Functor.commShiftIso_hom_naturality`, and `ShortComplex.ShortExact.map_of_exact`;
  `bridge/view`: the induced connecting morphisms obtained by postcomposition or precomposition.

The distinguished-triangle and naturality proofs are implementation scaffolding for the two owner
constructions, so this file should expose the constructors directly and keep those proofs out of
the public API surface.
-/

section Postcompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type uD'} [Category.{vD'} D'] [HasZeroObject D'] [HasShift D' ℤ]
variable [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

variable (G : DeltaFunctor A D) (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/-- Lemma 13.4.21 (1): postcomposing a `δ`-functor `G : A ⥤ D` with an exact functor of
triangulated categories `F : D ⥤ D'` yields a `δ`-functor `A ⥤ D'`. -/
@[stacks 0151]
noncomputable def postcomposeExactFunctor : DeltaFunctor A D' where
  toFunctor := G.toFunctor ⋙ F
  additive := inferInstance
  δ := fun {S} hS ↦
    F.map (G.δ hS) ≫ (F.commShiftIso (1 : ℤ)).hom.app (G.obj S.X₁)
  map_distinguished := fun {S} hS ↦ by
    simpa using
      F.map_distinguished (G.triangle hS) (G.triangle_distinguished hS)
  δ_naturality := fun {S T} hS hS' φ ↦ by
    simpa [Functor.comp_map, Category.assoc] using
      CommSq.vert_comp
        ((G.δ_naturality hS hS' φ).map F)
        (CommSq.mk (F.commShiftIso_hom_naturality (G.map φ.τ₁) (1 : ℤ)))

/-- The underlying functor of the postcomposed `δ`-functor is the ordinary composite functor. -/
@[simp] theorem postcomposeExactFunctor_toFunctor :
    (G.postcomposeExactFunctor F).toFunctor = G.toFunctor ⋙ F := rfl

end Postcompose

section Precompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (G : DeltaFunctor A D) (H : A' ⥤ₑ A)

/-- Lemma 13.4.21 (2): precomposing a `δ`-functor `G : A ⥤ D` with an exact functor
`H : A' ⥤ A` of abelian categories yields a `δ`-functor `A' ⥤ D`. -/
@[stacks 0151]
noncomputable def precomposeExactFunctor : DeltaFunctor A' D where
  toFunctor := H.obj ⋙ G.toFunctor
  additive := by
    letI : H.obj.Additive := ((AdditiveFunctor.ofExact A' A).obj H).property
    infer_instance
  δ := fun {_} hS ↦ G.δ (hS.map_of_exact H.obj)
  map_distinguished := fun {_} hS ↦ by
    simpa [Functor.comp_map] using
      G.map_distinguished (hS.map_of_exact H.obj)
  δ_naturality := fun {_ _} hS hS' φ ↦ by
    simpa [Functor.comp_map] using
      G.δ_naturality (hS.map_of_exact H.obj) (hS'.map_of_exact H.obj)
        ((H.obj.mapShortComplex).map φ)

/-- The underlying functor of the precomposed `δ`-functor is the ordinary composite functor. -/
@[simp] theorem precomposeExactFunctor_toFunctor :
    (G.precomposeExactFunctor H).toFunctor = H.obj ⋙ G.toFunctor := rfl

end Precompose

end DeltaFunctor

end CategoryTheory
