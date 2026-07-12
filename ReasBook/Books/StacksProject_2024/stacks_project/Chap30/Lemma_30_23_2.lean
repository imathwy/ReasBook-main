import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.restrictFunctor`,
-- `Scheme.IdealSheafData`, `ShortComplex.Exact`, and `CategoryTheory.exactFunctor`; local
-- precedent supplies `RingedSpace.Coh` and `SequentialInverseSystem`.

/-- The object property defining coherent formal modules along `I`: an inverse system of coherent
modules whose affine sections are killed by the corresponding powers of `I`, and whose transition
maps identify the expected affine quotients. -/
def IsCoherentFormalModuleSystem {X : Scheme.{u}} (I : X.IdealSheafData) :
    ObjectProperty (SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace)) :=
  fun F ↦
    (∀ n : ℕ, ∀ U : X.affineOpens,
      I.ideal U ^ n •
          (⊤ : Submodule Γ(X, U.1) ((F.obj (op n)).obj.val.obj (op U.1))) = ⊥) ∧
    ∀ n : ℕ, ∀ U : X.affineOpens,
      ∃ hquot :
          I.ideal U ^ n •
              (⊤ : Submodule Γ(X, U.1)
                ((F.obj (op (n + 1))).obj.val.obj (op U.1))) ≤
            (((F.stepMap n).hom.val.app (op U.1)).hom).ker,
        Function.Bijective
          (Submodule.liftQ
            (I.ideal U ^ n •
              (⊤ : Submodule Γ(X, U.1)
                ((F.obj (op (n + 1))).obj.val.obj (op U.1))))
            (((F.stepMap n).hom.val.app (op U.1)).hom)
            hquot)

/-- The source-facing category `\textit{Coh}(X, \mathcal I)` of coherent formal modules along
the ideal sheaf data `I`. -/
@[stacks 087X]
abbrev CoherentFormalModules (X : Scheme.{u}) (I : X.IdealSheafData) :=
  (IsCoherentFormalModuleSystem I).FullSubcategory

/-- Source-semantic unfolding of `IsCoherentFormalModuleSystem`. -/
theorem isCoherentFormalModuleSystem_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace)) :
    IsCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ, ∀ U : X.affineOpens,
        I.ideal U ^ n •
            (⊤ : Submodule Γ(X, U.1) ((F.obj (op n)).obj.val.obj (op U.1))) = ⊥) ∧
      ∀ n : ℕ, ∀ U : X.affineOpens,
        ∃ hquot :
            I.ideal U ^ n •
                (⊤ : Submodule Γ(X, U.1)
                  ((F.obj (op (n + 1))).obj.val.obj (op U.1))) ≤
              (((F.stepMap n).hom.val.app (op U.1)).hom).ker,
          Function.Bijective
            (Submodule.liftQ
              (I.ideal U ^ n •
                (⊤ : Submodule Γ(X, U.1)
                  ((F.obj (op (n + 1))).obj.val.obj (op U.1))))
              (((F.stepMap n).hom.val.app (op U.1)).hom)
              hquot) := sorry

/-- Objects of `CoherentFormalModules X I` satisfy the defining coherent-formal-module property.
-/
theorem coherentFormalModules_obj_property {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : CoherentFormalModules X I) :
    IsCoherentFormalModuleSystem I M.obj := sorry

/-- A functor is the restriction functor on coherent formal modules when it restricts every stage
and every stagewise morphism by the canonical module restriction functor. -/
class IsCoherentFormalModulesRestrictionFunctor {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens)
    (F : CoherentFormalModules X I ⥤
      CoherentFormalModules (X.restrict U.isOpenEmbedding)
        (I.comap (X.ofRestrict U.isOpenEmbedding))) : Prop where
  /-- On objects, the `n`th stage is the restriction of the original `n`th coherent sheaf. -/
  obj_eq : ∀ (M : CoherentFormalModules X I) (n : ℕ),
    (((F.obj M).obj).obj (op n)).obj =
      (Modules.restrictFunctor (X.ofRestrict U.isOpenEmbedding)).obj
        (((M.obj).obj (op n)).obj)
  /-- On morphisms, the `n`th stage map is obtained by restricting the original `n`th stage map. -/
  map_eq : ∀ {M N : CoherentFormalModules X I} (f : M ⟶ N) (n : ℕ),
    ((F.map f).hom.app (op n)).hom =
      eqToHom (obj_eq M n) ≫
        (Modules.restrictFunctor (X.ofRestrict U.isOpenEmbedding)).map
          ((f.hom.app (op n)).hom) ≫
        eqToHom (Eq.symm (obj_eq N n))

/-- A stagewise restriction functor on coherent formal modules preserves zero morphisms. -/
instance instPreservesZeroMorphismsOfCoherentFormalModulesRestrictionFunctor
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens)
    (F : CoherentFormalModules X I ⥤
      CoherentFormalModules (X.restrict U.isOpenEmbedding)
        (I.comap (X.ofRestrict U.isOpenEmbedding)))
    [IsCoherentFormalModulesRestrictionFunctor I U F] :
    F.PreservesZeroMorphisms := sorry

/-- The object and morphism specifications for a coherent-formal-module restriction functor. -/
theorem isCoherentFormalModulesRestrictionFunctor_spec {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opens)
    (F : CoherentFormalModules X I ⥤
      CoherentFormalModules (X.restrict U.isOpenEmbedding)
        (I.comap (X.ofRestrict U.isOpenEmbedding)))
    [hF : IsCoherentFormalModulesRestrictionFunctor I U F] :
    (∀ (M : CoherentFormalModules X I) (n : ℕ),
      (((F.obj M).obj).obj (op n)).obj =
        (Modules.restrictFunctor (X.ofRestrict U.isOpenEmbedding)).obj
          (((M.obj).obj (op n)).obj)) ∧
      ∀ {M N : CoherentFormalModules X I} (f : M ⟶ N) (n : ℕ),
        ((F.map f).hom.app (op n)).hom =
          eqToHom (hF.obj_eq M n) ≫
            (Modules.restrictFunctor (X.ofRestrict U.isOpenEmbedding)).map
              ((f.hom.app (op n)).hom) ≫
            eqToHom (Eq.symm (hF.obj_eq N n)) := sorry

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
instance instIsNoetherianRestrictOfIsNoetherian {X : Scheme.{u}}
    [IsNoetherian X] (U : X.Opens) :
    IsNoetherian (X.restrict U.isOpenEmbedding) := sorry

/-- Lemma 30.23.2 (1): for a Noetherian scheme `X` and a quasi-coherent ideal sheaf `I`, the
category `\textit{Coh}(X, \mathcal I)` of coherent formal modules is abelian. -/
@[stacks 087X]
instance coherentFormalModules_abelian {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : Abelian (CoherentFormalModules X I) := sorry

/-- Lemma 30.23.2 (2): for an open subset `U` of `X`, the restriction functor
`\textit{Coh}(X, \mathcal I) \to \textit{Coh}(U, \mathcal I|_U)` is exact. -/
@[stacks 087X]
theorem coherentFormalModules_restrictionFunctor_exact {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    (restrictionFunctor : CoherentFormalModules X I ⥤
      CoherentFormalModules (X.restrict U.isOpenEmbedding)
        (I.comap (X.ofRestrict U.isOpenEmbedding)))
    [IsCoherentFormalModulesRestrictionFunctor I U restrictionFunctor] :
    exactFunctor (CoherentFormalModules X I)
      (CoherentFormalModules (X.restrict U.isOpenEmbedding)
        (I.comap (X.ofRestrict U.isOpenEmbedding)))
      restrictionFunctor := sorry

/-- Lemma 30.23.2 (3): exactness in `\textit{Coh}(X, \mathcal I)` may be checked after restricting
to every member of an open covering of `X`. -/
@[stacks 087X]
theorem coherentFormalModules_exact_iff_of_openCover {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    {ι : Type v} (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (restrictionFunctor : ∀ i : ι,
      CoherentFormalModules X I ⥤
        CoherentFormalModules (X.restrict (U i).isOpenEmbedding)
          (I.comap (X.ofRestrict (U i).isOpenEmbedding)))
    [∀ i : ι, IsCoherentFormalModulesRestrictionFunctor I (U i) (restrictionFunctor i)]
    (S : ShortComplex (CoherentFormalModules X I)) :
    S.Exact ↔ ∀ i : ι, (S.map (restrictionFunctor i)).Exact := sorry

end AlgebraicGeometry.Scheme
