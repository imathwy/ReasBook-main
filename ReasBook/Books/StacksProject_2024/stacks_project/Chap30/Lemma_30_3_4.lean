import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical morphism predicates
`QuasiCompact` and `IsAffineHom`; local Chapter 30 precedent represents quasi-coherent ideal
sheaves as subobjects of `\mathcal O_X`, and mathlib exposes higher direct images through
`(pushforward f).rightDerived`. -/

/-- Lemma 30.3.4: let `f : X ⟶ Y` be a quasi-compact morphism with `X` and `Y`
quasi-separated. If `R^1 f_* I = 0` for every quasi-coherent sheaf of ideals `I` on
`X`, then `f` is affine. -/
@[stacks 0F83]
theorem isAffineHom_of_R1_pushforward_vanishes_for_quasiCoherent_idealSheaves
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparatedSpace X.carrier] [QuasiSeparatedSpace Y.carrier]
    [HasInjectiveResolutions X.Modules]
    (hR1 : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj (Subobject.underlying.obj I))) :
    IsAffineHom f := sorry

end AlgebraicGeometry.Scheme
