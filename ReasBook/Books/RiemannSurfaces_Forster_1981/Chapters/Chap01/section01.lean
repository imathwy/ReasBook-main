import Mathlib
import Mathlib.Topology.Compactification.OnePoint.Sphere

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_1 (from Chap01) -/
open Set
open scoped ContDiff Manifold

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `StructureGroupoid.compatible`, `IsManifold.mk'`,
  `contDiffGroupoid`.
- Verified locally: `OpenPartialHomeomorph`, `atlas`, `HasGroupoid`, and `IsManifold`.
- Owner choice: Definition 1.1 is source-facing bridge API over mathlib's canonical analytic
  manifold owner `IsManifold 𝓘(ℂ) ω X`; the underlying transition groupoid is the canonical
  `contDiffGroupoid ω 𝓘(ℂ)`.
-/

/- Definition 1.1: a complex chart on `X` is represented canonically by
`OpenPartialHomeomorph X ℂ`, i.e. an open partial homeomorphism from `X` to `ℂ`. The textbook's
"biholomorphic transition maps" are the standard analytic transition maps encoded by
`contDiffGroupoid ω 𝓘(ℂ)`. -/

/-- The source-facing name for the canonical analytic structure groupoid on `ℂ`. This is a thin
bridge to `contDiffGroupoid ω 𝓘(ℂ)`, not a new owner. -/
abbrev biholomorphicGroupoid : StructureGroupoid ℂ :=
  contDiffGroupoid ω 𝓘(ℂ)

section ChartCompatibility

variable {X : Type u} [TopologicalSpace X]

/-- Definition 1.1 (1): two complex charts are holomorphically compatible when their transition map
belongs to the canonical analytic groupoid on `ℂ`. -/
def holomorphicallyCompatible (e e' : OpenPartialHomeomorph X ℂ) : Prop :=
  e.symm ≫ₕ e' ∈ biholomorphicGroupoid

/-- Holomorphic compatibility of complex charts is symmetric. -/
theorem holomorphicallyCompatible_symm {e e' : OpenPartialHomeomorph X ℂ} :
    holomorphicallyCompatible e e' ↔ holomorphicallyCompatible e' e := sorry

section ChartedSpace

variable [ChartedSpace ℂ X]

/-- A chosen complex atlas has biholomorphic transition maps exactly when it defines a
`HasGroupoid X biholomorphicGroupoid` structure. This is the source-facing compatibility bridge
to the canonical charted-space owner. -/
theorem hasGroupoid_iff_holomorphicallyCompatible :
    HasGroupoid X biholomorphicGroupoid ↔
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e' := by
  constructor
  · intro h e e' he he'
    letI : HasGroupoid X biholomorphicGroupoid := h
    exact StructureGroupoid.compatible biholomorphicGroupoid he he'
  · intro h
    exact ⟨fun he he' ↦ h he he'⟩

/-- The canonical biholomorphic groupoid witness on a complex charted space is exactly the
corresponding analytic manifold structure. -/
instance instIsManifoldOfHasGroupoid [HasGroupoid X biholomorphicGroupoid] :
    IsManifold 𝓘(ℂ) ω X :=
  IsManifold.mk' 𝓘(ℂ) ω X

/-- Definition 1.1 (2): a complex atlas on `X` is represented canonically by the analytic manifold
typeclass `IsManifold 𝓘(ℂ) ω X`; equivalently, its chosen charts are pairwise holomorphically
compatible. -/
theorem isManifold_iff_holomorphicallyCompatible :
    IsManifold 𝓘(ℂ) ω X ↔
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e' := by
  constructor
  · intro h
    letI : HasGroupoid X biholomorphicGroupoid := h.toHasGroupoid
    exact (hasGroupoid_iff_holomorphicallyCompatible).1 inferInstance
  · intro h
    letI : HasGroupoid X biholomorphicGroupoid :=
      (hasGroupoid_iff_holomorphicallyCompatible).2 h
    exact IsManifold.mk' 𝓘(ℂ) ω X

/-- Definition 1.1 (2): holomorphic compatibility of the chosen atlas gives the corresponding
`HasGroupoid` witness on the canonical analytic transition groupoid. -/
theorem hasGroupoid_of_holomorphicallyCompatible
    (hcompat :
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e') :
    HasGroupoid X biholomorphicGroupoid :=
  (hasGroupoid_iff_holomorphicallyCompatible).2 hcompat

/-- Definition 1.1 (2): holomorphic compatibility of the chosen atlas gives the canonical analytic
manifold structure on `X`. -/
theorem isManifold_of_holomorphicallyCompatible
    (hcompat :
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e') :
    IsManifold 𝓘(ℂ) ω X :=
  (isManifold_iff_holomorphicallyCompatible).2 hcompat

/-- Definition 1.1 (3): two complex atlases on `X` are analytically equivalent when every chart of
the first atlas is holomorphically compatible with every chart of the second atlas. -/
def analyticallyEquivalent (c c' : ChartedSpace ℂ X) : Prop :=
  ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
    e ∈ c.atlas → e' ∈ c'.atlas → holomorphicallyCompatible e e'

/-- Analytic equivalence of complex atlases is symmetric. -/
theorem analyticallyEquivalent_symm {c c' : ChartedSpace ℂ X} :
    analyticallyEquivalent c c' ↔ analyticallyEquivalent c' c := sorry

end ChartedSpace
end ChartCompatibility

/-! ### Exercise_1_1 (from Chap01) -/
open scoped OnePoint
open Metric

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `onePointEquivSphereOfFinrankEq`, `stereographic'`,
  `OnePoint.instTopologicalSpace`.
- Verified locally: `OnePoint.isOpen_iff_of_mem`, `onePointEquivSphereOfFinrankEq`,
  `EuclideanSpace.finAddEquivProd`, and the `CompactSpace`/`T2Space` instances on
  `OnePoint (EuclideanSpace ℝ (Fin n))`.
- Owner choice: model the textbook space `ℝ^n ∪ {∞}` by the canonical one-point compactification
  `OnePoint (EuclideanSpace ℝ (Fin n))`; keep compactness and Hausdorffness on that owner, and
  expose the stereographic projection itself by the textbook coordinate formula.
-/

/-- Exercise 1.1 (1): the one-point compactification `OnePoint (EuclideanSpace ℝ (Fin n))`,
i.e. the textbook space `ℝ^n ∪ {∞}` with the compact-complement topology at `∞`, is compact. In
particular this gives the stated result for `n ≥ 1`. -/
theorem onePointEuclidean_compact (n : ℕ) :
    CompactSpace (OnePoint (EuclideanSpace ℝ (Fin n))) :=
  inferInstance

/-- Exercise 1.1 (2): the one-point compactification `OnePoint (EuclideanSpace ℝ (Fin n))` of
`ℝ^n` is Hausdorff. In particular this gives the stated result for `n ≥ 1`. -/
theorem onePointEuclidean_hausdorff (n : ℕ) :
    T2Space (OnePoint (EuclideanSpace ℝ (Fin n))) :=
  inferInstance

/-- The textbook stereographic projection `S^n → ℝ^n ∪ {∞}` written on the canonical target
`OnePoint (EuclideanSpace ℝ (Fin n))`. -/
def stereographicProjection (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      OnePoint (EuclideanSpace ℝ (Fin n)) :=
  fun x ↦
    let e : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) :=
      EuclideanSpace.finAddEquivProd
    let y : EuclideanSpace ℝ (Fin n) :=
      (e x.1).1
    let t : ℝ :=
      ((e x.1).2 : EuclideanSpace ℝ (Fin 1)) 0
    if t = 1 then
      (∞ : OnePoint (EuclideanSpace ℝ (Fin n)))
    else
      (((1 : ℝ) / (1 - t)) • y : EuclideanSpace ℝ (Fin n))

/-- The defining formula for `stereographicProjection`. -/
theorem stereographicProjection_def (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    stereographicProjection n x =
      let e : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) :=
        EuclideanSpace.finAddEquivProd
      let y : EuclideanSpace ℝ (Fin n) :=
        (e x.1).1
      let t : ℝ :=
        ((e x.1).2 : EuclideanSpace ℝ (Fin 1)) 0
      if t = 1 then
        (∞ : OnePoint (EuclideanSpace ℝ (Fin n)))
      else
        (((1 : ℝ) / (1 - t)) • y : EuclideanSpace ℝ (Fin n)) := rfl

/-- The Euclidean dimension count needed to invoke the canonical one-point compactification
homeomorphism. -/
private theorem finrank_euclideanSpace_add_one_eq_card_fin_succ (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1 = Fintype.card (Fin (n + 1)) := by
  simp

private def canonicalOnePointEuclideanSphereHomeomorph (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ
      OnePoint (EuclideanSpace ℝ (Fin n)) :=
  (onePointEquivSphereOfFinrankEq (finrank_euclideanSpace_add_one_eq_card_fin_succ n)).symm

/-- Exercise 1.1 (3): the unit sphere `S^n ⊆ ℝ^{n+1}` is homeomorphic to the one-point
compactification `ℝ^n ∪ {∞}`. This bundles the textbook stereographic projection itself as a
homeomorphism, using the canonical one-point compactification homeomorphism only as a private
bridge for the inverse and continuity data. -/
def stereographicProjectionHomeomorph (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ
      OnePoint (EuclideanSpace ℝ (Fin n)) where
  toEquiv :=
    { toFun := stereographicProjection n
      invFun := (canonicalOnePointEuclideanSphereHomeomorph n).symm
      left_inv := by
        sorry
      right_inv := by
        sorry }
  continuous_toFun := by
    sorry
  continuous_invFun := (canonicalOnePointEuclideanSphereHomeomorph n).symm.continuous

@[simp] theorem stereographicProjectionHomeomorph_apply (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    stereographicProjectionHomeomorph n x = stereographicProjection n x :=
  rfl

/-- Exercise 1.1 (3): the textbook stereographic projection itself is a homeomorphism from `S^n`
to the one-point compactification `ℝ^n ∪ {∞}`. -/
theorem stereographicProjection_homeomorphism (n : ℕ) :
    IsHomeomorph (stereographicProjection n) := by
  simpa using (stereographicProjectionHomeomorph n).isHomeomorph
