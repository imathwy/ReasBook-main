import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Problem_9_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContinuousMap

-- Semantic recall via `lean_leansearch`: the canonical owner for ordinary homotopy equivalences
-- is `ContinuousMap.HomotopyEquiv`. Chapter 23 already fixes `ThomSpace` as the Thom-space owner,
-- while `StiefelWhitneyNormalization` already owns the chosen tautological real line bundle over
-- `RealProjectiveInfinity`, so this file records Lemma 23.6.1 as a bridge on that existing API.

noncomputable section

variable {H2 : ModTwoCohomologyTheory}

/-- The universal real line bundle `γ₁` over `RP^∞` chosen by `normalizationData`. -/
abbrev universalRealLineBundle
    (normalizationData : StiefelWhitneyNormalization H2) :
    TopCat.of RealProjectiveInfinity → Type _ :=
  normalizationData.tautologicalLineBundle.fiber

/-- The Thom space `T(γ₁)` of the universal real line bundle over `RP^∞`. -/
abbrev universalLineBundleThomSpace
    (normalizationData : StiefelWhitneyNormalization H2) : Type _ :=
  ThomSpace 1 (universalRealLineBundle normalizationData)

/-- Unfolding `universalLineBundleThomSpace` recovers the Thom space of the tautological real line
bundle over `RealProjectiveInfinity`. -/
theorem universalLineBundleThomSpace_def
    (normalizationData : StiefelWhitneyNormalization H2) :
    universalLineBundleThomSpace normalizationData =
      ThomSpace 1 normalizationData.tautologicalLineBundle.fiber :=
  rfl

section

variable (normalizationData : StiefelWhitneyNormalization H2)

local instance : TopologicalSpace
    (Bundle.TotalSpace (Fin 1 → ℝ) (universalRealLineBundle normalizationData)) :=
  normalizationData.tautologicalLineBundle.totalSpace_topology

variable [∀ b : TopCat.of RealProjectiveInfinity,
  NormedAddCommGroup ((universalRealLineBundle normalizationData) b)]
variable [∀ b : TopCat.of RealProjectiveInfinity,
  NormedSpace ℝ ((universalRealLineBundle normalizationData) b)]

local instance : TopologicalSpace (universalLineBundleThomSpace normalizationData) :=
  instTopologicalSpaceThomSpace 1 (universalRealLineBundle normalizationData)

/-- The canonical zero section of the universal real line bundle, viewed as a map into its Thom
space. -/
noncomputable def universalLineBundleZeroSectionToThomSpace :
    C(TopCat.of RealProjectiveInfinity, universalLineBundleThomSpace normalizationData) where
  toFun := fun ℓ ↦
    thomSpaceMk 1 (universalRealLineBundle normalizationData) ℓ
      (OnePoint.some (0 : (universalRealLineBundle normalizationData) ℓ))
  continuous_toFun := by
    sorry

/-- The zero-section map `RP^∞ → T(γ₁)` is a homotopy equivalence. This is the canonical
comparison map underlying Lemma 23.6.1. -/
theorem universalLineBundleZeroSectionToThomSpace_exists_homotopyEquiv :
    ∃ e : TopCat.of RealProjectiveInfinity ≃ₕ universalLineBundleThomSpace normalizationData,
      e.toFun = universalLineBundleZeroSectionToThomSpace normalizationData := sorry

/-- Lemma 23.6.1. There is a homotopy equivalence `RP^∞ → T(γ₁)`, where `T(γ₁)` is the Thom space
of the canonical tautological real line bundle over `RealProjectiveInfinity`. -/
theorem realProjectiveInfinity_nonempty_homotopyEquiv_universalLineBundleThomSpace :
    Nonempty
      (TopCat.of RealProjectiveInfinity ≃ₕ universalLineBundleThomSpace normalizationData) := by
  rcases universalLineBundleZeroSectionToThomSpace_exists_homotopyEquiv normalizationData with
    ⟨e, _⟩
  exact ⟨e⟩

end
