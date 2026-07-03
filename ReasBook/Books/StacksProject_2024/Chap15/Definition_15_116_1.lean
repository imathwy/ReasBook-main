import Mathlib
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Remark_15_115_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Definition 15.116.1:
- primary domain: weakly unramified and formally smooth localized branches arising from reduced
  tensor-product base change for extensions of discrete valuation rings;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings.WeaklyUnramified`,
  `IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal`,
  `RingHom.formally_smooth_for_adic`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`;
- best owner abstraction: the source-facing predicates `IsWeakSolutionFor` and `IsSolutionFor`
  should quantify over maximal branches with the canonical localized branch algebra from Remark
  `15.115.1`; the weak-solution predicate uses `WeaklyUnramified` directly, the solution
  predicate uses `RingHom.formally_smooth_for_adic`, and the maximal-ideal equality remains a
  companion bridge theorem rather than primitive public data;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, and the finite extension `K₁ / K`; the localized branch extension structure and
  its ramification/smoothness properties are derived API.

Source/core/bridge triage:
- `source-facing`: `IsWeakSolutionFor`, `IsSolutionFor`, `IsSeparableSolutionFor`;
- `core/canonical`: `WeaklyUnramified`, `RingHom.formally_smooth_for_adic`,
  `Localization.localRingHom`;
- `bridge/view`: `IsWeakSolutionFor.map_maximalIdeal`.
-/

open scoped TensorProduct
open IsExtensionOfDiscreteValuationRings
open IsLocalRing

universe u v w x y

noncomputable section

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance : CommRing A1 :=
  inferInstance

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance : CommRing B1 :=
  inferInstance

private noncomputable instance localizedBranchAlgebra
    (p : Ideal A1) [p.IsPrime] (q : Ideal B1) [q.IsPrime] [q.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p)).toAlgebra

private def IsWeakSolutionBranch
    (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p] :
    Prop :=
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    localizedBranchAlgebra p q
  let _ : IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p) (Localization.AtPrime q) :=
    isExtensionOfDiscreteValuationRings_localizationBranch p q
  WeaklyUnramified (Localization.AtPrime p) (Localization.AtPrime q)

private def IsSolutionBranch
    (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p] :
    Prop :=
  (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p)).formally_smooth_for_adic
    (maximalIdeal (Localization.AtPrime q))

variable (A) (B) (K) (L) (K1) in
/-- Definition 15.116.1: a finite field extension `K₁ / K` is a weak solution for `A ⊂ B` if for
every maximal ideal `p` of `A₁ = integralClosure A K₁` and every maximal ideal `q` of
`B₁ = integralClosure B ((L ⊗[K] K₁)_red)` lying over `p`, the localized extension
`(A₁)_p ⊂ (B₁)_q` is weakly unramified. -/
def IsWeakSolutionFor : Prop :=
  ∀ (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p],
    IsWeakSolutionBranch p q

variable (A) (B) (K) (L) (K1) in
/-- A finite field extension `K₁ / K` is a solution for `A ⊂ B` if every localized extension
`(A₁)_p ⊂ (B₁)_q` from Remark `15.115.1` is formally smooth for the `q`-adic topology. -/
def IsSolutionFor : Prop :=
  ∀ (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p],
    IsSolutionBranch p q

variable (A) (B) (K) (L) (K1) in
/-- Companion bridge: the weak-solution condition is equivalent to the maximal-ideal equality on
each localized branch. -/
theorem isWeakSolutionFor_iff_map_maximalIdeal :
    IsWeakSolutionFor A B K L K1 ↔
      ∀ (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p],
        Ideal.map
            (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p))
            (maximalIdeal (Localization.AtPrime p)) =
          maximalIdeal (Localization.AtPrime q) := by
  sorry

variable (A) (B) (K) (L) (K1) in
/-- A separable solution is a solution for `A ⊂ B` whose field extension `K₁ / K` is separable. -/
def IsSeparableSolutionFor : Prop :=
  IsSolutionFor A B K L K1 ∧ Algebra.IsSeparable K K1

end
