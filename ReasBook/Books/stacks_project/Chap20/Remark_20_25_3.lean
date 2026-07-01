import Mathlib
import stacks_project.Chap20.Lemma_20_25_1

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {ι : Type u}
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

variable (𝒰 : ι → Opens X.carrier)

local notation "Dplus" => CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat
local notation "CechF" =>
  (moduleCechDerivedFunctor X 𝒰 : CochainComplex.Plus (RingedSpace.Modules X) ⥤ Dplus)
local notation "RGammaF" => moduleDerivedGlobalSectionsFunctor X

-- Proof sketch: start with the comparison natural transformation from Lemma `20.25.1`. The
-- source shift is induced by the totalization-versus-bidegree-shift comparison of Remark
-- `12.18.5`, while the target shift is the canonical shift-commuting structure on the bounded-
-- below derived global-sections functor. Replacing a bounded-below complex by an injective
-- resolution reduces the square to the injective case, where the sign computation defining `γ`
-- gives commutativity.
/-- Remark 20.25.3: for an open covering `𝒰` of a ringed space `X`, the Čech-to-derived-global-
sections comparison of Lemma `20.25.1` can be chosen compatibly with every integer shift.
Equivalently, for every bounded-below complex `\mathcal F^\bullet` of `\mathcal O_X`-modules and
every integer `b`, the canonical map
`Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet))[b] \to
R\Gamma(X, \mathcal F^\bullet)[b]` fits into the commutative shifted square described in the
remark. -/
theorem exists_moduleCechDerivedFunctor_comparison_commShift
    (h𝒰 : iSup 𝒰 = ⊤)
    [Functor.CommShift CechF ℤ]
    [Functor.CommShift RGammaF ℤ] :
    ∃ τ : CechF ⟶ RGammaF, NatTrans.CommShift τ ℤ := sorry

-- Proof sketch: this is the objectwise square expressing compatibility of `τ` with the shift.
-- It is exactly the specialization of `NatTrans.shift_app_comm` to the Čech comparison and the
-- bounded-below derived global-sections functor.
/-- A shift-compatible Čech-to-derived-global-sections comparison yields the commutative square on
each bounded-below complex and each integer shift. -/
theorem moduleCechDerivedFunctor_comparison_shift_app_comm
    [Functor.CommShift CechF ℤ]
    [Functor.CommShift RGammaF ℤ]
    {τ : CechF ⟶ RGammaF} [NatTrans.CommShift τ ℤ]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) (b : ℤ) :
    (Functor.commShiftIso CechF b).hom.app K ≫ (τ.app K)⟦b⟧' =
      τ.app ((shiftFunctor (CochainComplex.Plus (RingedSpace.Modules X)) b).obj K) ≫
        (Functor.commShiftIso RGammaF b).hom.app K := sorry

end

end AlgebraicGeometry.RingedSpace
