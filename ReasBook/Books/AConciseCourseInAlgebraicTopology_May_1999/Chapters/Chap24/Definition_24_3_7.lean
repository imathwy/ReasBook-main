import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Chapter 23 fixes `ThomSpace n E` as the Thom-space owner, and Chapter 23's pullback API uses
-- the canonical family `proj *ᵖ E` for an actual bundle pullback along `proj`. This file records
-- the Thom class directly from the actual exterior powers of that pullback bundle over
-- `ThomSpace n E`; chosen bundle presentations survive only as comparison API.

universe u

section

open Bundle

variable {B : Type u} [TopologicalSpace B] {n : ℕ} (E : ComplexPlaneBundle n B)
variable [TopologicalSpace (ThomSpace n E.fiber)]

/-- The fiberwise `i`th exterior power of the actual pullback bundle `proj *ᵖ E` over
`ThomSpace n E.fiber`. -/
abbrev thomClassExteriorPowerBundle
    (proj : ContinuousMap (ThomSpace n E.fiber) B)
    (i : ℕ) :
    ThomSpace n E.fiber → Type :=
  fun x ↦ ↥(⋀[ℂ]^i ((ComplexPlaneBundle.pullback E proj).fiber x))

/-- The type of honest complex vector bundle presentations over `ThomSpace n E.fiber`. -/
abbrev ThomBundlePresentation :=
  ComplexVectorBundle.Presentation (ThomSpace n E.fiber)

/-- An honest presentation is an actual presentation of `Λ^i(proj *ᵖ E)` when its underlying
bundle family is exactly the actual `i`th exterior-power bundle. -/
def IsActualThomClassExteriorPowerPresentation
    (proj : ContinuousMap (ThomSpace n E.fiber) B)
    (i : Fin (n + 1))
    (actualExteriorPowerPresentation : ThomBundlePresentation E) : Prop :=
  actualExteriorPowerPresentation.bundle = thomClassExteriorPowerBundle E proj (i : ℕ)

/-- A chosen honest presentation bridges to an actual `i`th exterior-power presentation when the
two presentations are isomorphic as complex vector bundles. -/
def IsThomClassExteriorPowerPresentation
    (actualExteriorPowerPresentation : ThomBundlePresentation E)
    (exteriorPowerPresentation : ThomBundlePresentation E) : Prop :=
  Nonempty (ComplexVectorBundle.Iso
    exteriorPowerPresentation
    actualExteriorPowerPresentation)

/-- A family of honest presentations realizes the actual exterior-power bundles of `proj *ᵖ E`
when each member presents the corresponding actual exterior-power bundle. -/
def IsActualThomClassExteriorPowerPresentationFamily
    (proj : ContinuousMap (ThomSpace n E.fiber) B)
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E) : Prop :=
  ∀ i : Fin (n + 1),
    IsActualThomClassExteriorPowerPresentation E proj i (actualExteriorPowerPresentation i)

/-- A chosen family of honest presentations is a bridge to the actual exterior powers of
`proj *ᵖ E` when each chosen presentation is isomorphic to the corresponding actual honest
presentation. -/
def IsThomClassExteriorPowerPresentationFamily
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E) : Prop :=
  ∀ i : Fin (n + 1),
    IsThomClassExteriorPowerPresentation E
      (actualExteriorPowerPresentation i)
      (exteriorPowerPresentation i)

/-- The alternating-sum formula computed from a chosen family of honest presentations of the
actual exterior powers of `proj *ᵖ E`. This is bridge/view API rather than the main Thom-class
owner. -/
noncomputable def complexBundleThomClassFormula
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E) :
    complexKTheory (ThomSpace n E.fiber) :=
  ∑ i : Fin (n + 1),
    (((-1 : complexKTheory (ThomSpace n E.fiber)) ^ (i : ℕ)) *
      ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i))

/-- `complexBundleThomClassFormula exteriorPowerPresentation` is the alternating sum of the
chosen presentation classes. -/
theorem complexBundleThomClassFormula_def
    {B : Type} [TopologicalSpace B] {n : ℕ} (E : ComplexPlaneBundle n B)
    [TopologicalSpace (ThomSpace n E.fiber)]
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E) :
    complexBundleThomClassFormula E exteriorPowerPresentation =
      ∑ i : Fin (n + 1),
        (((-1 : complexKTheory (ThomSpace n E.fiber)) ^ (i : ℕ)) *
          ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i)) :=
  rfl

/-- Two chosen presentations of the actual `i`th exterior power determine the same `K`-theory
class once both bridge by honest bundle isomorphisms to the same actual honest presentation. -/
theorem thomClassExteriorPowerClass_eq_of_iso
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (exteriorPowerPresentation exteriorPowerPresentation' :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (hExteriorPowerPresentation :
      IsThomClassExteriorPowerPresentationFamily E
        actualExteriorPowerPresentation exteriorPowerPresentation)
    (hExteriorPowerPresentation' :
      IsThomClassExteriorPowerPresentationFamily E
        actualExteriorPowerPresentation exteriorPowerPresentation')
    (i : Fin (n + 1)) :
    ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i) =
      ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation' i) := by
  sorry

/-- A class `α ∈ K(ThomSpace n E.fiber)` is the actual class `[Λ^i(proj *ᵖ E)]` when it is
computed by some honest presentation family bridging to an actual honest presentation family for
the exterior powers of `proj *ᵖ E`. -/
def IsThomClassExteriorPowerClass
    (proj : ContinuousMap (ThomSpace n E.fiber) B)
    (i : Fin (n + 1))
    (α : complexKTheory (ThomSpace n E.fiber)) : Prop :=
  ∃ actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E,
    IsActualThomClassExteriorPowerPresentationFamily E proj actualExteriorPowerPresentation ∧
      ∃ exteriorPowerPresentation :
          (i : Fin (n + 1)) → ThomBundlePresentation E,
        IsThomClassExteriorPowerPresentationFamily E
            actualExteriorPowerPresentation exteriorPowerPresentation ∧
          α = ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i)

/-- Any chosen presentation family that bridges to an actual presentation family computes the
source-facing actual exterior-power class. -/
theorem isThomClassExteriorPowerClass_of_presentation
    (proj : ContinuousMap (ThomSpace n E.fiber) B)
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (hActualExteriorPowerPresentation :
      IsActualThomClassExteriorPowerPresentationFamily E proj actualExteriorPowerPresentation)
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (hExteriorPowerPresentation :
      IsThomClassExteriorPowerPresentationFamily E
        actualExteriorPowerPresentation exteriorPowerPresentation)
    (i : Fin (n + 1)) :
    IsThomClassExteriorPowerClass E proj i
      (ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i)) := by
  exact ⟨actualExteriorPowerPresentation, hActualExteriorPowerPresentation,
    exteriorPowerPresentation, hExteriorPowerPresentation, rfl⟩

/-- A source-facing actual exterior-power class is represented by some chosen presentation family
bridging to some actual presentation family for the exterior powers of `proj *ᵖ E`. -/
theorem IsThomClassExteriorPowerClass.exists_eq_presentation
    {proj : ContinuousMap (ThomSpace n E.fiber) B}
    {i : Fin (n + 1)}
    {α : complexKTheory (ThomSpace n E.fiber)}
    (hClass : IsThomClassExteriorPowerClass E proj i α) :
    ∃ actualExteriorPowerPresentation exteriorPowerPresentation,
      IsActualThomClassExteriorPowerPresentationFamily E proj actualExteriorPowerPresentation ∧
        IsThomClassExteriorPowerPresentationFamily E
          actualExteriorPowerPresentation exteriorPowerPresentation ∧
        α = ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i) := by
  rcases hClass with ⟨actualExteriorPowerPresentation, hActualExteriorPowerPresentation,
    exteriorPowerPresentation, hExteriorPowerPresentation, hClass⟩
  exact ⟨actualExteriorPowerPresentation, exteriorPowerPresentation,
    hActualExteriorPowerPresentation, hExteriorPowerPresentation, hClass⟩

/-- The alternating-sum formula is independent of the chosen presentation family once the two
families both bridge to the same actual presentation family. -/
theorem complexBundleThomClassFormula_eq_of_iso
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (exteriorPowerPresentation' :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (hExteriorPowerPresentation :
      IsThomClassExteriorPowerPresentationFamily E
        actualExteriorPowerPresentation exteriorPowerPresentation)
    (hExteriorPowerPresentation' :
      IsThomClassExteriorPowerPresentationFamily E
        actualExteriorPowerPresentation exteriorPowerPresentation') :
    complexBundleThomClassFormula E exteriorPowerPresentation =
      complexBundleThomClassFormula E exteriorPowerPresentation' := by
  unfold complexBundleThomClassFormula
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [thomClassExteriorPowerClass_eq_of_iso
    E actualExteriorPowerPresentation exteriorPowerPresentation exteriorPowerPresentation'
    hExteriorPowerPresentation hExteriorPowerPresentation' i]

/-- Definition 24.3.7. A class `lambda_E ∈ K(ThomSpace n E)` is the `K`-theory Thom class for
the actual pullback map `proj : ThomSpace n E.fiber → B` when some honest presentation family
really presents the actual exterior-power bundles of `proj *ᵖ E`, and `lambda_E` is the
alternating-sum formula computed from that actual presentation family. Chosen presentation
families remain only bridge/view API via bundle isomorphisms to this actual family. -/
def IsComplexBundleThomClass
    (proj : ContinuousMap (ThomSpace n E.fiber) B)
    (lambda_E : complexKTheory (ThomSpace n E.fiber)) : Prop :=
  ∃ actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E,
    IsActualThomClassExteriorPowerPresentationFamily E proj actualExteriorPowerPresentation ∧
      ∃ exteriorPowerPresentation :
          (i : Fin (n + 1)) → ThomBundlePresentation E,
        IsThomClassExteriorPowerPresentationFamily E
            actualExteriorPowerPresentation exteriorPowerPresentation ∧
          lambda_E = complexBundleThomClassFormula E exteriorPowerPresentation

/-- Any chosen presentation family bridging to an actual exterior-power presentation family
computes a class that satisfies `IsComplexBundleThomClass`. -/
theorem isComplexBundleThomClass_of_presentation
    (proj : ContinuousMap (ThomSpace n E.fiber) B)
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (hActualExteriorPowerPresentation :
      IsActualThomClassExteriorPowerPresentationFamily E proj actualExteriorPowerPresentation)
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (hExteriorPowerPresentation :
      IsThomClassExteriorPowerPresentationFamily E
        actualExteriorPowerPresentation exteriorPowerPresentation) :
    IsComplexBundleThomClass E proj
      (complexBundleThomClassFormula E exteriorPowerPresentation) := by
  exact ⟨actualExteriorPowerPresentation, hActualExteriorPowerPresentation,
    exteriorPowerPresentation, hExteriorPowerPresentation, rfl⟩

/-- A Thom class is computed by some presentation-family formula bridging to some actual
presentation family for the exterior powers of `proj *ᵖ E`. -/
theorem IsComplexBundleThomClass.exists_eq_formula
    {proj : ContinuousMap (ThomSpace n E.fiber) B}
    {lambda_E : complexKTheory (ThomSpace n E.fiber)}
    (hThom : IsComplexBundleThomClass E proj lambda_E) :
    ∃ actualExteriorPowerPresentation exteriorPowerPresentation,
      IsActualThomClassExteriorPowerPresentationFamily E proj actualExteriorPowerPresentation ∧
        IsThomClassExteriorPowerPresentationFamily E
          actualExteriorPowerPresentation exteriorPowerPresentation ∧
        lambda_E = complexBundleThomClassFormula E exteriorPowerPresentation := by
  rcases hThom with ⟨actualExteriorPowerPresentation, hActualExteriorPowerPresentation,
    exteriorPowerPresentation, hExteriorPowerPresentation, hThom⟩
  exact ⟨actualExteriorPowerPresentation, exteriorPowerPresentation,
    hActualExteriorPowerPresentation, hExteriorPowerPresentation, hThom⟩

/-- If two Thom classes are both computed by the same chosen honest presentation family of the
actual exterior powers, then they agree. -/
theorem complexBundleThomClass_eq_of_eq_formula
    {lambda_E lambda_E' : complexKTheory (ThomSpace n E.fiber)}
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ThomBundlePresentation E)
    (hFormula :
      lambda_E = complexBundleThomClassFormula E exteriorPowerPresentation)
    (hFormula' :
      lambda_E' = complexBundleThomClassFormula E exteriorPowerPresentation) :
    lambda_E = lambda_E' := by
  rw [hFormula, hFormula']

end
