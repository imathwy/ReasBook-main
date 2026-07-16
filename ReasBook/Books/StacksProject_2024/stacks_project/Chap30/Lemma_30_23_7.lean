import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Abelian

noncomputable section

universe u v

-- Semantic recall: `lean_leansearch` surfaced `Ext.mapExactFunctor` and
-- `Functor.mapExtAddHom` as the canonical exact-functor maps on Ext; local Chapter 30 precedent
-- supplies `CoherentCompletionFunctor` for the completion functor and the affine-open
-- ideal-power annihilation predicate for coherent source modules.

/-- Lemma 30.23.7 (1): for a Noetherian scheme `X` and a quasi-coherent ideal sheaf `I`,
any object of `Coh(X, I)` annihilated by a power of `I` lies in the essential image of the
completion functor (30.23.3.1). -/
@[stacks 0EHP]
theorem coherentFormalModule_isEssentialImage_of_isAnnihilatedByIdealPower
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (targetAnnihilatedByIdealPower : Scheme.CoherentFormalModules X I → Prop)
    (E : Scheme.CoherentFormalModules X I) (hE : targetAnnihilatedByIdealPower E) :
    ∃ F : RingedSpace.Coh X.toRingedSpace,
      Nonempty (ctx.obj F ≅ E) := sorry

/-- Lemma 30.23.7 (2): if one of two coherent `\mathcal O_X`-modules is annihilated by a
power of `I`, then completion induces a bijection on Hom sets
`Hom_X(F, G) -> Hom_{Coh(X,I)}(F^, G^)`. -/
@[stacks 0EHP]
theorem coherentCompletionFunctor_hom_bijective_of_isAnnihilatedByIdealPower
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace)
    (hFG : Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
      Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) :
    Function.Bijective (fun f : F ⟶ G ↦ ctx.map f) := sorry

section ExtMap

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
variable (ctx : CoherentCompletionFunctor X I)
variable [hSourceAbelian : Abelian (RingedSpace.Coh X.toRingedSpace)]
variable [hTargetAbelian : Abelian (Scheme.CoherentFormalModules X I)]

/-- Local preadditive structure used to elaborate the source Ext-map owner. -/
local instance coherentCompletionExtSourcePreadditive :
    Preadditive (RingedSpace.Coh X.toRingedSpace) :=
  hSourceAbelian.toPreadditive

/-- Local preadditive structure used to elaborate the target Ext-map owner. -/
local instance coherentCompletionExtTargetPreadditive :
    Preadditive (Scheme.CoherentFormalModules X I) :=
  hTargetAbelian.toPreadditive

/-- Lemma 30.23.7 (3): if one of two coherent `\mathcal O_X`-modules is annihilated by a
power of `I`, then the exact completion functor induces a bijection on extension classes
`Ext_X(F, G) -> Ext_{Coh(X,I)}(F^, G^)`. -/
@[stacks 0EHP]
theorem coherentCompletionFunctor_ext_bijective_of_isAnnihilatedByIdealPower
    [HasExt (RingedSpace.Coh X.toRingedSpace)] [HasExt (Scheme.CoherentFormalModules X I)]
    [ctx.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits ctx]
    [CategoryTheory.Limits.PreservesFiniteColimits ctx]
    (F G : RingedSpace.Coh X.toRingedSpace)
    (hFG : Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
      Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) :
    Function.Bijective
      (fun e : Ext F G 1 ↦
        ctx.mapExtAddHom F G 1 e) := sorry

end ExtMap
