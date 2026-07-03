import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_1_2 (from Chap01) -/
open scoped Manifold OnePoint

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `OnePoint.map`, `UpperHalfPlane.coe_specialLinearGroup_apply`.
- Verified locally: `OnePoint.smul_some_eq_ite`, `OnePoint.smul_infty_eq_ite`,
  `RiemannSurface.Holomorphic`, `Structomorph`, and the `RiemannSurface (OnePoint ℂ)` instance.
- Owner choice: use the canonical `GL (Fin 2) ℂ` action on `OnePoint ℂ = ℙ¹(ℂ)` from
  `Mathlib.Topology.Compactification.OnePoint.ProjectiveLine` as the projective-line extension of
  the textbook linear fractional formula, and express biholomorphicity via
  `Structomorph biholomorphicGroupoid (OnePoint ℂ) (OnePoint ℂ)`.
-/

/-- The extension of the linear fractional transformation attached to `g ∈ GL(2, ℂ)` to the
Riemann sphere `ℙ¹(ℂ) = OnePoint ℂ`. -/
def linearFractionalExtension (g : GL (Fin 2) ℂ) : OnePoint ℂ → OnePoint ℂ :=
  fun z ↦ g • z

instance instContinuousConstSMul : ContinuousConstSMul (GL (Fin 2) ℂ) (OnePoint ℂ) where
  continuous_const_smul g := by
    sorry

/-- Exercise 1.2 (2): the extended linear fractional transformation attached to `g ∈ GL(2, ℂ)` as
a bundled biholomorphic self-equivalence of the Riemann sphere. -/
def linearFractionalStructomorph (g : GL (Fin 2) ℂ) :
    Structomorph biholomorphicGroupoid (OnePoint ℂ) (OnePoint ℂ) where
  toHomeomorph := Homeomorph.smul g
  mem_groupoid := by
    sorry

@[simp] theorem linearFractionalStructomorph_apply (g : GL (Fin 2) ℂ) (z : OnePoint ℂ) :
    (linearFractionalStructomorph g).toHomeomorph z = linearFractionalExtension g z :=
  by simp [linearFractionalStructomorph, linearFractionalExtension]

/-- On the finite chart of `ℙ¹(ℂ)`, `linearFractionalExtension g` is the usual linear fractional
formula. -/
theorem linearFractionalExtension_apply_coe (g : GL (Fin 2) ℂ) (z : ℂ) :
    linearFractionalExtension g (z : OnePoint ℂ) =
      if g 1 0 * z + g 1 1 = 0 then
        (∞ : OnePoint ℂ)
      else
        (((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) : OnePoint ℂ) := sorry

/-- At `∞`, the extended linear fractional transformation takes the expected projective value. -/
theorem linearFractionalExtension_apply_infty (g : GL (Fin 2) ℂ) :
    linearFractionalExtension g (∞ : OnePoint ℂ) =
      if g 1 0 = 0 then
        (∞ : OnePoint ℂ)
      else
        ((g 0 0 / g 1 0 : ℂ) : OnePoint ℂ) := sorry

/-- Exercise 1.2 (1): for `g ∈ GL(2, ℂ)`, the linear fractional transformation extends from the
finite chart to a holomorphic self-map of `ℙ¹(ℂ) = OnePoint ℂ`, hence to a meromorphic function on
the projective line. -/
theorem linearFractionalExtension_holomorphic (g : GL (Fin 2) ℂ) :
    RiemannSurface.Holomorphic (linearFractionalExtension g) := by
  simpa [linearFractionalExtension] using
    RiemannSurface.structomorph_holomorphic (linearFractionalStructomorph g)

/-! ### Remark_1_2 (from Chap01) -/
universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `OpenPartialHomeomorph.restrOpen`, `StructureGroupoid.trans_restricted`.
- Verified locally: `holomorphicallyCompatible`, `analyticallyEquivalent`,
  `OpenPartialHomeomorph.restrOpen`.
- Owner choice: keep the remark on the canonical `OpenPartialHomeomorph` and `ChartedSpace`
  surfaces introduced in Definition 1.1.
-/

section

variable {X : Type u} [TopologicalSpace X]

/-- Remark 1.2 (1): restricting a complex chart to an open subset of its source yields a complex
chart holomorphically compatible with the original chart. -/
theorem holomorphicallyCompatible_restrOpen (e : OpenPartialHomeomorph X ℂ) {s : Set X}
    (hs : IsOpen s) :
    holomorphicallyCompatible (e.restrOpen s hs) e := sorry

namespace ChartedSpace

/-- A chosen charted-space structure on `X` is a complex atlas when its charts are pairwise
holomorphically compatible. This is the source-facing compatibility condition from Definition 1.1
applied to a specific `ChartedSpace` value. -/
def IsComplexAtlas (c : ChartedSpace ℂ X) : Prop :=
  ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
    e ∈ c.atlas → e' ∈ c.atlas → holomorphicallyCompatible e e'

/-- A chosen charted-space structure is a complex atlas exactly when it is analytically equivalent
to itself. -/
theorem isComplexAtlas_iff_analyticallyEquivalent_self (c : ChartedSpace ℂ X) :
    c.IsComplexAtlas ↔ analyticallyEquivalent c c :=
  Iff.rfl

end ChartedSpace

/-- Analytic equivalence of complex atlases is reflexive. -/
theorem analyticallyEquivalent_refl {c : ChartedSpace ℂ X} (hc : c.IsComplexAtlas) :
    analyticallyEquivalent c c :=
  hc

/-- Analytic equivalence of complex atlases is transitive. -/
theorem analyticallyEquivalent_trans {c₁ c₂ c₃ : ChartedSpace ℂ X}
    (h₁₂ : analyticallyEquivalent c₁ c₂) (h₂₃ : analyticallyEquivalent c₂ c₃) :
    analyticallyEquivalent c₁ c₃ := by
  letI : ChartedSpace ℂ X := c₂
  intro e e' he he'
  exact biholomorphicGroupoid.compatible_of_mem_maximalAtlas
    (by
      intro f hf
      exact ⟨h₁₂ he hf, (holomorphicallyCompatible_symm).1 (h₁₂ he hf)⟩)
    (by
      intro f hf
      exact ⟨(holomorphicallyCompatible_symm).1 (h₂₃ hf he'), h₂₃ hf he'⟩)

/-- Remark 1.2 (2): analytic equivalence of complex atlases is an equivalence relation. -/
theorem analyticallyEquivalent_equivalence :
    Equivalence
      (fun c c' : { c : ChartedSpace ℂ X // c.IsComplexAtlas } ↦
        analyticallyEquivalent c.1 c'.1) where
  refl c := analyticallyEquivalent_refl c.2
  symm := by
    intro _ _ h e e' he he'
    exact (holomorphicallyCompatible_symm).1 (h he' he)
  trans h₁₂ h₂₃ := analyticallyEquivalent_trans h₁₂ h₂₃

/-- Analytic equivalence equips complex atlases on `X` with their canonical equivalence relation. -/
instance analyticallyEquivalentSetoid :
    Setoid { c : ChartedSpace ℂ X // c.IsComplexAtlas } where
  r c c' := analyticallyEquivalent c.1 c'.1
  iseqv := analyticallyEquivalent_equivalence

end

/-! ### Remark_1_extra_2 (from Chap01) -/
open scoped Manifold

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `chartAt`, `OpenPartialHomeomorph.bijOn`, `StructureGroupoid.compatible`.
- Verified locally: `chartAt`, `OpenPartialHomeomorph.bijOn`, `holomorphicallyCompatible`, and
  `StructureGroupoid.compatible`.
- Owner choice: keep the remark on the canonical `ChartedSpace`/`HasGroupoid` layer. The local
  model clause is witnessed by `chartAt ℂ x`, while chart-independence is stated for arbitrary
  atlas charts so no chart is treated as mathematically distinguished.
-/

section

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Remark 1-extra-2 (1): for each point of a Riemann surface, the chosen chart at that point
identifies an open neighborhood of the point bijectively with an open subset of `ℂ`. -/
theorem chartAt_bijOn (x : X) :
    Set.BijOn (chartAt ℂ x) (chartAt ℂ x).source (chartAt ℂ x).target :=
  (chartAt ℂ x).bijOn

/-- Remark 1-extra-2 (2): any two complex charts belonging to the atlas of a Riemann surface have
biholomorphic transition map, so chartwise notions descend exactly when they are invariant under
such changes of coordinates. -/
theorem atlasCharts_holomorphicallyCompatible [HasGroupoid X biholomorphicGroupoid]
    {e e' : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X)
    (he' : e' ∈ atlas ℂ X) :
    holomorphicallyCompatible e e' := by
  simpa [holomorphicallyCompatible] using
    StructureGroupoid.compatible biholomorphicGroupoid he he'

end
