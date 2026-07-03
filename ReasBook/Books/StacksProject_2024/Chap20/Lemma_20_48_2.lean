import Mathlib
import StacksProject_2024.Chap17.Definition_17_4_1
import StacksProject_2024.Chap17.Definition_17_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
section

variable {X : RingedSpace}
variable [monoidal :
  MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [Abelian (RingedSpace.Modules X)]
variable [((curriedTensor (RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 :
    CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

/-- A source-level tor-amplitude predicate for a cochain complex of `\mathcal O_X`-modules,
expressed by exactness of tensoring with every degree-zero module sheaf outside the interval
`[a, b]`. -/
def HasComplexTorAmplitudeIn
    (E : CochainComplex (RingedSpace.Modules X) ℤ)
    (a b : ℤ) : Prop :=
  ∀ (ℱ : (RingedSpace.Modules X)) (i : ℤ), i ∉ Set.Icc a b →
    HomologicalComplex.ExactAt
      (HomologicalComplex.tensorObj ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ) E) i

-- Proof sketch: this is just the defining predicate for `HasComplexTorAmplitudeIn` unfolded.
/-- The complex-level tor-amplitude predicate is exactly exactness of tensoring with every
degree-zero module sheaf outside the interval `[a, b]`. -/
theorem hasComplexTorAmplitudeIn_iff
    (E : CochainComplex (RingedSpace.Modules X) ℤ) (a b : ℤ) :
    HasComplexTorAmplitudeIn E a b ↔
      ∀ (ℱ : (RingedSpace.Modules X)) (i : ℤ), i ∉ Set.Icc a b →
        HomologicalComplex.ExactAt
          (HomologicalComplex.tensorObj ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ) E)
          i :=
  sorry

-- Proof sketch: for any `\mathcal F`, the tor-amplitude hypothesis gives exactness of
-- `\mathcal E^\bullet \otimes \mathcal F` at degree `a - 1`. The bounded-above flat hypotheses
-- make `\mathcal E^{a - 2} ⟶ \mathcal E^{a - 1} ⟶ \mathcal E^a ⟶ \operatorname{coker}(d^{a-1})
-- ⟶ 0` a flat resolution of the cokernel, so `\operatorname{Tor}_1` of the cokernel against any
-- `\mathcal F` vanishes. Then apply the flatness criterion from Lemma `20.26.16`.
/-- Lemma 20.48.2: if `\mathcal E^\bullet` is a bounded above complex of flat
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)` and has tor-amplitude in `[a, b]`,
then the cokernel of `d_{\mathcal E^\bullet}^{a - 1}` is a flat `\mathcal O_X`-module. -/
theorem cokernel_differential_isFlat_of_hasComplexTorAmplitudeIn
    (E : CochainComplex (RingedSpace.Modules X) ℤ) (a b : ℤ)
    (hbounded : ∃ n : ℤ, E.IsStrictlyLE n)
    (hFlat : ∀ n : ℤ, (E.X n).IsFlat)
    (hTor : HasComplexTorAmplitudeIn E a b) :
    (cokernel (E.d (a - 1) a)).IsFlat := sorry

end

end AlgebraicGeometry.RingedSpace
