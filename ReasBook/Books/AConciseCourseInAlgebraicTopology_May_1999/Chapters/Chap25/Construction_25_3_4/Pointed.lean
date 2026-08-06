import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_1_16

open CategoryTheory

universe u v

noncomputable section

section

variable (BO : ℕ → Type u)
variable [∀ n, TopologicalSpace (BO n)]
variable (γ : ∀ n, BO n → Type v)
variable [∀ n, TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) (γ n))]
variable [∀ n, (b : BO n) → TopologicalSpace (γ n b)]
variable [∀ n, FiberBundle (Fin n → ℝ) (γ n)]
variable [∀ n, (b : BO n) → AddCommGroup (γ n b)]
variable [∀ n, (b : BO n) → Module ℝ (γ n b)]
variable [∀ n, RealPlaneBundleClassifyingSpace n (BO n) (γ n)]

/-- Explicit stagewise norm data on the chosen universal bundles `γ n`. Construction 25.3.4 uses
these norms to access the Thom-space topology, but the source-facing existence theorem packages
them explicitly rather than leaving them as hidden ambient assumptions. -/
class TOStagewiseNormedBundle where
  /-- Each fiber `γ n b` is a normed additive commutative group. -/
  fiberNormedAddCommGroup : ∀ n, (b : BO n) → NormedAddCommGroup (γ n b)
  /-- Each fiber `γ n b` is a real normed vector space. -/
  fiberNormedSpace : ∀ n, (b : BO n) → NormedSpace ℝ (γ n b)

attribute [reducible, instance] TOStagewiseNormedBundle.fiberNormedAddCommGroup
attribute [reducible, instance] TOStagewiseNormedBundle.fiberNormedSpace

/-- Existing fiberwise normed-space instances package into the explicit owner
`TOStagewiseNormedBundle BO γ`. -/
@[reducible] def TOStagewiseNormedBundle.ofFiberwiseInstances
    [∀ n, (b : BO n) → NormedAddCommGroup (γ n b)]
    [∀ n, (b : BO n) → NormedSpace ℝ (γ n b)] :
    TOStagewiseNormedBundle BO γ where
  fiberNormedAddCommGroup := inferInstance
  fiberNormedSpace := inferInstance

/-- Compatibility bridge: callers that already provide the old ambient fiberwise norms still get
the explicit stagewise norm owner used by the `Construction_25_3_4` foundation API. -/
instance instTOStagewiseNormedBundleOfFiberwiseInstances
    [∀ n, (b : BO n) → NormedAddCommGroup (γ n b)]
    [∀ n, (b : BO n) → NormedSpace ℝ (γ n b)] :
    TOStagewiseNormedBundle BO γ :=
  TOStagewiseNormedBundle.ofFiberwiseInstances BO γ

/-- The carrier of `TO n`, viewed through a local alias so this item-local foundation can equip it
with the compactly generated reflection topology without changing the ambient Thom-space owner. -/
abbrev TOCompactlyGeneratedType (n : ℕ) :=
  TO n (BO n) (γ n)

variable [TOStagewiseNormedBundle BO γ]

/-- The compactly generated reflection topology on the local carrier alias for `TO n`. -/
instance toCompactlyGeneratedType_topologicalSpace (n : ℕ) :
    TopologicalSpace (TOCompactlyGeneratedType BO γ n) :=
  TopologicalSpace.compactlyGenerated.{max u v, max u v}
    (TOCompactlyGeneratedType BO γ n)

/-- The compactly generated reflection topology on `TO n` is compactly generated. -/
instance toCompactlyGeneratedType_uCompactlyGeneratedSpace (n : ℕ) :
    UCompactlyGeneratedSpace.{max u v} (TOCompactlyGeneratedType BO γ n) := by
  let _ : TopologicalSpace (TOCompactlyGeneratedType BO γ n) :=
    instTopologicalSpaceThomSpace n (γ n)
  exact
    (uCompactlyGeneratedSpaceCompactlyGenerated :
      @UCompactlyGeneratedSpace.{max u v}
        (TOCompactlyGeneratedType BO γ n)
        (TopologicalSpace.compactlyGenerated.{max u v, max u v}
          (TOCompactlyGeneratedType BO γ n)))

/-- A chosen pointed compactly generated model of the Thom space `TO n`, based at the common
point at infinity in the fiber over the chosen basepoint `bInf n`. -/
abbrev TOPointedCompactlyGenerated
    (bInf : ∀ n, BO n) (n : ℕ) :=
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (TOCompactlyGeneratedType BO γ n))
    (thomSpaceMk n (γ n) (bInf n) (OnePoint.infty : OnePoint (γ n (bInf n))))

/-- The prespectrum whose `n`th term is the chosen pointed model of the Thom space `TO n`. -/
def TO_prespectrum
    (bInf : ∀ n, BO n)
    (structureMap :
      ∀ n : ℕ,
        reducedSuspension
            (TOPointedCompactlyGenerated BO γ bInf n) ⟶
          TOPointedCompactlyGenerated BO γ bInf (n + 1)) :
    Prespectrum where
  spaces := TOPointedCompactlyGenerated BO γ bInf
  structureMap := structureMap

omit [∀ n, TopologicalSpace (BO n)]
  [∀ n, (b : BO n) → TopologicalSpace (γ n b)]
  [∀ n, FiberBundle (Fin n → ℝ) (γ n)]
  [∀ n, (b : BO n) → AddCommGroup (γ n b)]
  [∀ n, (b : BO n) → Module ℝ (γ n b)]
  [∀ n, RealPlaneBundleClassifyingSpace n (BO n) (γ n)] in
/-- Evaluating `TO_prespectrum` at degree `n` returns the chosen pointed model of the Thom space
`TO n`. -/
@[simp] theorem TO_prespectrum_apply
    [TOStagewiseNormedBundle BO γ]
    (bInf : ∀ n, BO n)
    (structureMap :
      ∀ n : ℕ,
        reducedSuspension
            (TOPointedCompactlyGenerated BO γ bInf n) ⟶
          TOPointedCompactlyGenerated BO γ bInf (n + 1))
    (n : ℕ) :
    TO_prespectrum BO γ bInf structureMap n =
      TOPointedCompactlyGenerated BO γ bInf n := rfl

end
