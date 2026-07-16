import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_10_2
import StacksProject_2024.stacks_project.Chap30.«30_23_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of module sheaves has kernel and cokernel annihilated by powers of the ideal
sheaf. -/
def HasIdealPowerTorsionKernelCokernel
    (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) : Prop :=
  IsAnnihilatedByIdealPowerOnAffineOpens I (kernel f) ∧
    IsAnnihilatedByIdealPowerOnAffineOpens I (cokernel f)

/-- Unfold the source-side kernel-and-cokernel ideal-power torsion condition for a morphism of
module sheaves. -/
theorem hasIdealPowerTorsionKernelCokernel_iff
    (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) :
    HasIdealPowerTorsionKernelCokernel I f ↔
      IsAnnihilatedByIdealPowerOnAffineOpens I (kernel f) ∧
        IsAnnihilatedByIdealPowerOnAffineOpens I (cokernel f) := sorry

end AlgebraicGeometry.Scheme.Modules

/-- The underlying morphism of `X.Modules` attached to a morphism in the coherent full
subcategory. -/
abbrev coherentModuleUnderlyingHom {X : Scheme.{u}}
    {F G : RingedSpace.Coh X.toRingedSpace} (f : F ⟶ G) : F.obj ⟶ G.obj :=
  (SheafOfModules.isCoherent X.toRingedSpace).ι.map f

/-- Unfold the underlying morphism of a coherent-module morphism. -/
theorem coherentModuleUnderlyingHom_def {X : Scheme.{u}}
    {F G : RingedSpace.Coh X.toRingedSpace} (f : F ⟶ G) :
    coherentModuleUnderlyingHom f =
      (SheafOfModules.isCoherent X.toRingedSpace).ι.map f := sorry

/-- Algebraization data for a morphism from a formal coherent object to the completion of a
coherent module. -/
structure FormalMapToCompletionAlgebraization.{u₁, v₁}
    {X : Scheme.{u₁}} {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (E : Scheme.CoherentFormalModules X I) (G : RingedSpace.Coh X.toRingedSpace)
    (alpha : E ⟶ ctx.obj G) where
  F : RingedSpace.Coh X.toRingedSpace
  a : F ⟶ G
  torsion : Scheme.Modules.HasIdealPowerTorsionKernelCokernel I (coherentModuleUnderlyingHom a)
  beta : E ≅ ctx.obj F
  comm : alpha = beta.hom ≫ ctx.map a

/-- The compatibility condition for an isomorphism between two algebraizations of a morphism
from a formal coherent object to a completion. -/
def FormalMapToCompletionAlgebraization.IsomorphismCompatible
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {E : Scheme.CoherentFormalModules X I} {G : RingedSpace.Coh X.toRingedSpace}
    {alpha : E ⟶ ctx.obj G}
    (z z' : FormalMapToCompletionAlgebraization ctx E G alpha) (e : z.F ≅ z'.F) : Prop :=
  e.hom ≫ z'.a = z.a ∧
    z.beta.hom ≫ ctx.map e.hom = z'.beta.hom

/-- Unfold the compatibility condition for isomorphisms between algebraizations of morphisms
from formal coherent objects to completions. -/
theorem FormalMapToCompletionAlgebraization.isomorphismCompatible_iff
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {E : Scheme.CoherentFormalModules X I} {G : RingedSpace.Coh X.toRingedSpace}
    {alpha : E ⟶ ctx.obj G}
    (z z' : FormalMapToCompletionAlgebraization ctx E G alpha) (e : z.F ≅ z'.F) :
    FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e ↔
      e.hom ≫ z'.a = z.a ∧
        z.beta.hom ≫ ctx.map e.hom = z'.beta.hom := sorry

/-- Algebraization data for a morphism from the completion of a coherent module to a formal
coherent object. -/
structure CompletionToFormalMapAlgebraization.{u₁, v₁}
    {X : Scheme.{u₁}} {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (G : RingedSpace.Coh X.toRingedSpace) (E : Scheme.CoherentFormalModules X I)
    (alpha : ctx.obj G ⟶ E) where
  F : RingedSpace.Coh X.toRingedSpace
  a : G ⟶ F
  torsion : Scheme.Modules.HasIdealPowerTorsionKernelCokernel I (coherentModuleUnderlyingHom a)
  beta : ctx.obj F ≅ E
  comm : alpha = ctx.map a ≫ beta.hom

/-- The compatibility condition for an isomorphism between two algebraizations of a morphism
from a completion to a formal coherent object. -/
def CompletionToFormalMapAlgebraization.IsomorphismCompatible
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {G : RingedSpace.Coh X.toRingedSpace} {E : Scheme.CoherentFormalModules X I}
    {alpha : ctx.obj G ⟶ E}
    (z z' : CompletionToFormalMapAlgebraization ctx G E alpha) (e : z.F ≅ z'.F) : Prop :=
  z.a ≫ e.hom = z'.a ∧
    ctx.map e.hom ≫ z'.beta.hom = z.beta.hom

/-- Unfold the compatibility condition for isomorphisms between algebraizations of morphisms
from completions to formal coherent objects. -/
theorem CompletionToFormalMapAlgebraization.isomorphismCompatible_iff
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {ctx : CoherentCompletionFunctor X I}
    {G : RingedSpace.Coh X.toRingedSpace} {E : Scheme.CoherentFormalModules X I}
    {alpha : ctx.obj G ⟶ E}
    (z z' : CompletionToFormalMapAlgebraization ctx G E alpha) (e : z.F ≅ z'.F) :
    CompletionToFormalMapAlgebraization.IsomorphismCompatible z z' e ↔
      z.a ≫ e.hom = z'.a ∧
        ctx.map e.hom ≫ z'.beta.hom = z.beta.hom := sorry

-- Semantic recall hits: `AdicCompletion` and `IsAdicComplete`; local precedent in
-- `30_23_3_1` supplies `CoherentCompletionFunctor`, while Chapter 30 ideal-power statements use
-- affine-open section modules for source-side annihilation by an ideal sheaf.

/-- Lemma 30.23.6 (1): for a Noetherian scheme `X`, an ideal sheaf `I`, a coherent module `G`,
and an object `E` of `Coh(X, I)`, any map `E -> G^` whose kernel and cokernel are annihilated by
powers of `I` is induced, uniquely up to unique isomorphism, by a coherent module map
`F -> G` with the same source-side ideal-power torsion condition. -/
@[stacks 0889]
theorem existsUnique_algebraization_of_formalMap_to_completion
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (targetPowerTorsion :
      {E₁ E₂ : Scheme.CoherentFormalModules X I} → (E₁ ⟶ E₂) → Prop)
    (E : Scheme.CoherentFormalModules X I) (G : RingedSpace.Coh X.toRingedSpace)
    (alpha : E ⟶ ctx.obj G)
    (halpha : targetPowerTorsion alpha) :
    ∃ z : FormalMapToCompletionAlgebraization ctx E G alpha,
      ∀ z' : FormalMapToCompletionAlgebraization ctx E G alpha,
        ∃! e : z.F ≅ z'.F,
          FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e := sorry

/-- Lemma 30.23.6 (2): for a Noetherian scheme `X`, an ideal sheaf `I`, a coherent module `G`,
and an object `E` of `Coh(X, I)`, any map `G^ -> E` whose kernel and cokernel are annihilated by
powers of `I` is induced, uniquely up to unique isomorphism, by a coherent module map
`G -> F` with the same source-side ideal-power torsion condition. -/
@[stacks 0889]
theorem existsUnique_algebraization_of_completion_to_formalMap
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (targetPowerTorsion :
      {E₁ E₂ : Scheme.CoherentFormalModules X I} → (E₁ ⟶ E₂) → Prop)
    (G : RingedSpace.Coh X.toRingedSpace) (E : Scheme.CoherentFormalModules X I)
    (alpha : ctx.obj G ⟶ E)
    (halpha : targetPowerTorsion alpha) :
    ∃ z : CompletionToFormalMapAlgebraization ctx G E alpha,
      ∀ z' : CompletionToFormalMapAlgebraization ctx G E alpha,
        ∃! e : z.F ≅ z'.F,
          CompletionToFormalMapAlgebraization.IsomorphismCompatible z z' e := sorry
