import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module S M]

namespace GenericFlatness

/- Domain-style sampling for 10.118.3.1:
* primary domain: localization away from one element in commutative algebra and module theory;
* sampled canonical declarations:
  `Localization.Away`,
  `LocalizedModule.Away`,
  `Localization.awayMapₐ`,
  `Module.compHom`;
* source-facing owner here: `LocalizationCondition R S M f`;
* core/canonical owner for the localized comparison algebra: `Localization.awayMapₐ`;
* primitive data: the commutative semirings/algebra/semimodule together with the localization
  parameter `f`;
* derived API: finite presentation and freeness of the localized algebra and localized module.
-/

/-- The localization of `S` away from the image of `f` in `S` is canonically an algebra over
`R_f`. -/
noncomputable instance (f : R) :
    Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
  by
    simpa [Algebra.ofId_apply] using
      (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra

/-- The localization of `M` away from the image of `f` in `S` carries its canonical restricted
`R_f`-module structure. -/
noncomputable instance (f : R) :
    Module (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M) :=
  by
    simpa [Algebra.ofId_apply] using
      (Module.compHom (LocalizedModule.Away ((Algebra.ofId R S) f) M)
        (Localization.awayMapₐ (Algebra.ofId R S) f).toRingHom)

/-- 10.118.3.1: the localization conditions used in generic flatness, namely that `S_f` is finitely
presented over `R_f`, that `M_f` is finitely presented as an `S_f`-module, and that both `S_f`
and `M_f` are free as `R_f`-modules. -/
class LocalizationCondition
    (R : Type u) [CommSemiring R]
    (S : Type v) [CommSemiring S] [Algebra R S]
    (M : Type w) [AddCommMonoid M] [Module S M]
    (f : R) : Prop where
  /-- The localized algebra `S_f` is finitely presented over `R_f`. -/
  finitePresentation_algebra :
    Algebra.FinitePresentation (Localization.Away f) (Localization.Away (algebraMap R S f))
  /-- The localized module `M_f` is finitely presented over `S_f`. -/
  finitePresentation_module :
    Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)
  /-- The localized algebra `S_f` is free as an `R_f`-module. -/
  free_algebra :
    Module.Free (Localization.Away f) (Localization.Away (algebraMap R S f))
  /-- The localized module `M_f` is free as an `R_f`-module. -/
  free_module :
    Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M)

attribute [instance] LocalizationCondition.finitePresentation_algebra
attribute [instance] LocalizationCondition.finitePresentation_module
attribute [instance] LocalizationCondition.free_algebra
attribute [instance] LocalizationCondition.free_module

/-- Separate localized finite-presentation and freeness assumptions assemble into the generic-flatness
localization condition at `f`. -/
instance (f : R)
    [Algebra.FinitePresentation (Localization.Away f) (Localization.Away (algebraMap R S f))]
    [Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [Module.Free (Localization.Away f) (Localization.Away (algebraMap R S f))]
    [Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M)] :
    LocalizationCondition R S M f :=
  { finitePresentation_algebra := inferInstance
    finitePresentation_module := inferInstance
    free_algebra := inferInstance
    free_module := inferInstance }

end GenericFlatness

end
