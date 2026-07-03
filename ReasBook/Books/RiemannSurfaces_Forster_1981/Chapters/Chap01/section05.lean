import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Compactification.OnePoint.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_5 (from Chap01) -/
open scoped Manifold OnePoint Topology
open TopologicalSpace Filter OnePoint
open AddAction

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `ChartedSpace`, `OnePoint`, `PeriodPair`.
- Verified locally: `RiemannSurface`, `TopologicalSpace.Opens.instChartedSpace`,
  `TopologicalSpace.Opens.instHasGroupoid`, `AddAction.instChartedSpaceQuotient`,
  `PeriodPair`, and `PeriodPair.lattice`.
- Owner choice: use the local `RiemannSurface` class on the canonical ambient charted-space layer;
  domains are modeled as open subsets `Opens X`, the sphere as `OnePoint ℂ` with its two standard
  affine charts, and tori as quotients by the lattice attached to a `PeriodPair`.
-/

/-- The finite chart domain `U₁ = ℙ¹(ℂ) \ {∞}` on the Riemann sphere. -/
def riemannSphereU1 : Opens (OnePoint ℂ) :=
  ⟨{(∞ : OnePoint ℂ)}ᶜ, isOpen_compl_singleton⟩

/-- The complementary chart domain `U₂ = ℙ¹(ℂ) \ {0}` on the Riemann sphere. -/
def riemannSphereU2 : Opens (OnePoint ℂ) :=
  ⟨{((0 : ℂ) : OnePoint ℂ)}ᶜ, isOpen_compl_singleton⟩

lemma riemannSphereU1_nonempty : Nonempty riemannSphereU1 :=
  ⟨⟨(0 : ℂ), by simp [riemannSphereU1]⟩⟩

lemma riemannSphereU2_nonempty : Nonempty riemannSphereU2 :=
  ⟨⟨(∞ : OnePoint ℂ), by simp [riemannSphereU2]⟩⟩

/-- The chart `φ₁ : U₁ → ℂ` on the Riemann sphere, given by the identity on the finite part. -/
def riemannSphereChart1 : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OpenPartialHomeomorph.refl ℂ).lift_openEmbedding OnePoint.isOpenEmbedding_coe

/-- The affine coordinate `z ↦ z⁻¹` on the chart domain `U₂`. -/
def riemannSphereInv : OnePoint ℂ → ℂ :=
  fun z ↦ z.elim 0 (fun w : ℂ ↦ w⁻¹)

lemma tendsto_inv_coclosedCompact :
    Tendsto (fun z : ℂ ↦ z⁻¹) (coclosedCompact ℂ) (nhds (0 : ℂ)) := by
  rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  simpa using (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ ↦ z⁻¹) _ _)

lemma riemannSphereInv_continuousAt_infty :
    ContinuousAt riemannSphereInv (∞ : OnePoint ℂ) := by
  rw [OnePoint.continuousAt_infty']
  simpa [riemannSphereInv] using tendsto_inv_coclosedCompact

lemma riemannSphereInv_continuousAt_coe {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt riemannSphereInv (z : OnePoint ℂ) := by
  rw [OnePoint.continuousAt_coe]
  change ContinuousAt (fun w : ℂ ↦ w⁻¹) z
  exact continuousAt_inv₀ hz

lemma riemannSphereInv_continuousOn :
    ContinuousOn riemannSphereInv (riemannSphereU2 : Set (OnePoint ℂ)) := by
  intro x hx
  rcases eq_or_ne x (∞ : OnePoint ℂ) with rfl | hx'
  · exact riemannSphereInv_continuousAt_infty.continuousWithinAt
  · obtain ⟨z, rfl⟩ := (OnePoint.ne_infty_iff_exists).1 hx'
    have hz : z ≠ 0 := by
      simpa [riemannSphereU2] using hx
    exact (riemannSphereInv_continuousAt_coe hz).continuousWithinAt

/-- The inverse affine chart map `ℂ → U₂`, with `0` sent to `∞`. -/
def riemannSphereU2Symm : ℂ → riemannSphereU2 := fun z ↦
  ⟨if z = 0 then (∞ : OnePoint ℂ) else ((z⁻¹ : ℂ) : OnePoint ℂ), by
    by_cases hz : z = 0
    · simp [riemannSphereU2, hz]
    · simp [riemannSphereU2, hz]⟩

lemma riemannSphereU2Symm_continuous :
    Continuous (fun z : ℂ ↦ (riemannSphereU2Symm z : OnePoint ℂ)) := by
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  by_cases hz : z = 0
  · subst z
    rw [continuousAt_iff_punctured_nhds]
    have h_inv :
        Tendsto (fun w : ℂ ↦ (w⁻¹ : ℂ)) (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
          (coclosedCompact ℂ) := by
      rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      simpa using (tendsto_inv₀_nhdsNE_zero : Tendsto (fun w : ℂ ↦ w⁻¹) _ _)
    have h_coe :
        Tendsto (fun w : ℂ ↦ ((w : ℂ) : OnePoint ℂ)) (coclosedCompact ℂ)
          (nhds (∞ : OnePoint ℂ)) :=
      OnePoint.tendsto_coe_infty
    have h_eq :
        (fun w : ℂ ↦ (riemannSphereU2Symm w : OnePoint ℂ)) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ)]
          fun w : ℂ ↦ ((w⁻¹ : ℂ) : OnePoint ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have h0 : w ≠ 0 := by simpa using hw
      simp [riemannSphereU2Symm, h0]
    simpa [riemannSphereU2Symm] using Tendsto.congr' h_eq.symm (h_coe.comp h_inv)
  · have h_eq :
        (fun w : ℂ ↦ (riemannSphereU2Symm w : OnePoint ℂ)) =ᶠ[nhds z]
          fun w : ℂ ↦ ((w⁻¹ : ℂ) : OnePoint ℂ) := by
      filter_upwards [compl_singleton_mem_nhds hz] with w hw
      have h0 : w ≠ 0 := by simpa using hw
      simp [riemannSphereU2Symm, h0]
    exact (continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr h_eq.symm

def riemannSphereU2Equiv : riemannSphereU2 ≃ ℂ where
  toFun z := riemannSphereInv z.1
  invFun := riemannSphereU2Symm
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨x, hx⟩
    by_cases hxInf : x = (∞ : OnePoint ℂ)
    · subst x
      simp [riemannSphereInv, riemannSphereU2Symm]
    · obtain ⟨w, rfl⟩ := (OnePoint.ne_infty_iff_exists).1 hxInf
      have hw : w ≠ 0 := by
        simpa [riemannSphereU2] using hx
      simp [riemannSphereInv, riemannSphereU2Symm, hw]
  right_inv z := by
    by_cases hz : z = 0
    · subst z
      simp [riemannSphereInv, riemannSphereU2Symm]
    · simp [riemannSphereInv, riemannSphereU2Symm, hz]

lemma riemannSphereU2Equiv_continuous :
    Continuous riemannSphereU2Equiv := by
  simpa [riemannSphereU2Equiv, riemannSphereInv]
    using (continuousOn_iff_continuous_restrict.mp riemannSphereInv_continuousOn)

lemma riemannSphereU2Equiv_symm_continuous :
    Continuous riemannSphereU2Equiv.symm := by
  simpa [riemannSphereU2Equiv] using
    (riemannSphereU2Symm_continuous.codRestrict fun z ↦ (riemannSphereU2Symm z).2)

/-- The chart `φ₂ : U₂ → ℂ` on the Riemann sphere, given by inversion on `ℂˣ` and `φ₂(∞) = 0`. -/
def riemannSphereChart2 : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (riemannSphereU2.openPartialHomeomorphSubtypeCoe riemannSphereU2_nonempty).symm.trans
    (riemannSphereU2Equiv.toHomeomorphOfContinuousOpen
      riemannSphereU2Equiv_continuous
      (riemannSphereU2Equiv.continuous_symm_iff.mp riemannSphereU2Equiv_symm_continuous)
    ).toOpenPartialHomeomorph

/-- The two standard charts on `OnePoint ℂ` define the charted-space structure of the Riemann
sphere. -/
instance riemannSphereChartedSpace : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {riemannSphereChart1, riemannSphereChart2}
  chartAt z :=
    match z with
    | ∞ => riemannSphereChart2
    | (_ : ℂ) => riemannSphereChart1
  mem_chart_source z := by
    cases z using OnePoint.rec with
    | infty =>
        simp [riemannSphereChart2, riemannSphereU2]
    | coe w =>
        simp [riemannSphereChart1]
  chart_mem_atlas z := by
    cases z using OnePoint.rec <;> simp

/-- The two standard charts on the Riemann sphere are biholomorphically compatible. -/
instance riemannSphereHasGroupoid : HasGroupoid (OnePoint ℂ) biholomorphicGroupoid := sorry

/-- Example 1.5 (1): the complex plane `ℂ` is a Riemann surface via its identity chart. -/
instance complexPlaneRiemannSurface : RiemannSurface ℂ := inferInstance

/-- Example 1.5 (2): every connected open subset of a Riemann surface inherits a natural Riemann
surface structure from the restricted complex charts. -/
instance domainRiemannSurface {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (Y : Opens X) [ConnectedSpace Y] : RiemannSurface Y := inferInstance

/-- Every connected open subset of `ℂ` is a Riemann surface. -/
instance complexDomainRiemannSurface (Y : Opens ℂ) [ConnectedSpace Y] : RiemannSurface Y :=
  domainRiemannSurface Y

/-- Example 1.5 (3): the Riemann sphere `ℙ¹(ℂ)`, modeled as `OnePoint ℂ`, is a Riemann surface via
its two standard charts. -/
instance riemannSphereRiemannSurface : RiemannSurface (OnePoint ℂ) := inferInstance

/-- The lattice action on `ℂ` attached to a period pair is properly discontinuous. -/
instance torusProperlyDiscontinuousVAdd (L : PeriodPair) :
    ProperlyDiscontinuousVAdd L.lattice.toAddSubgroup ℂ := by
  let S : AddSubgroup ℂ := L.lattice.toAddSubgroup
  have hSclosed : IsClosed (S : Set ℂ) := by
    simpa [S] using L.isClosed_lattice
  have hSdiscrete : IsDiscrete (S : Set ℂ) := by
    rw [SetLike.isDiscrete_iff_discreteTopology]
    change DiscreteTopology L.lattice
    infer_instance
  have hS :
      Tendsto S.subtype cofinite (cocompact ℂ) :=
    hSclosed.tendsto_coe_cofinite_of_isDiscrete hSdiscrete
  exact S.properlyDiscontinuousVAdd_of_tendsto_cofinite hS

/-- The quotient charts on the torus `ℂ / Γ` have biholomorphic transition maps. -/
instance torusHasGroupoid (L : PeriodPair) :
    HasGroupoid (orbitRel.Quotient L.lattice.toAddSubgroup ℂ) biholomorphicGroupoid := sorry

/-- Example 1.5 (4): the complex torus `ℂ / Γ`, for the lattice `Γ` spanned by a period pair, is a
Riemann surface. -/
instance torusRiemannSurface (L : PeriodPair) :
    RiemannSurface (orbitRel.Quotient L.lattice.toAddSubgroup ℂ) := inferInstance

/-! ### Exercise_1_5 (from Chap01) -/
open scoped MatrixGroups
open scoped Pointwise
open AddAction

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `UpperHalfPlane.coe_specialLinearGroup_apply`,
  `UpperHalfPlane.SLAction`.
- Verified locally: `PeriodPair`, `PeriodPair.lattice`, `Structomorph`,
  `RiemannSurface.Holomorphic`, `RiemannSurface.isomorphic`, and `orbitRel.Quotient`.
- Owner choice: attach the torus quotient directly to its period-pair owner as `L.Torus`, and
  attach the standard pair and torus for `τ : UpperHalfPlane` to that owner as
  `UpperHalfPlane.periodPair τ` and `X(τ)`. The modular transformation in part (c) is expressed by
  the canonical `SL(2, ℤ)` action on `UpperHalfPlane`.
-/

/-- Auxiliary linear independence for the standard torus periods `1` and `τ`. -/
private theorem oneAndTauLinearIndependent (τ : UpperHalfPlane) :
    LinearIndependent ℝ ![(1 : ℂ), (τ : ℂ)] := sorry

namespace UpperHalfPlane

/-- The standard period pair attached to `τ ∈ ℍ`, corresponding to the lattice
`ℤ + ℤ τ ⊂ ℂ`. -/
def periodPair (τ : UpperHalfPlane) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := oneAndTauLinearIndependent τ

/-- The first standard period attached to `τ ∈ ℍ` is `1`. -/
@[simp] theorem periodPair_omega1 (τ : UpperHalfPlane) :
    τ.periodPair.ω₁ = 1 :=
  rfl

/-- The second standard period attached to `τ ∈ ℍ` is `τ`. -/
@[simp] theorem periodPair_omega2 (τ : UpperHalfPlane) :
    τ.periodPair.ω₂ = τ :=
  rfl

end UpperHalfPlane

namespace PeriodPair

/-- The complex torus attached to a period pair `L`, realized as the quotient `ℂ / L.lattice`. -/
abbrev Torus (L : PeriodPair) :=
  orbitRel.Quotient L.lattice.toAddSubgroup ℂ

/-- Multiplication by `α` on `ℂ` descends to the quotient tori whenever it sends the lattice of
`L` into the lattice of `L'`. -/
def smulTorusMap (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) :
    L.Torus → L'.Torus :=
  Quotient.map' (fun z : ℂ ↦ α * z) fun z w hzw ↦ by
    rw [orbitRel_apply] at hzw ⊢
    rcases hzw with ⟨g, hg⟩
    have hαg : α * (g : ℂ) ∈ (L'.lattice : Set ℂ) := by
      apply hα
      refine ⟨(g : ℂ), g.2, ?_⟩
      simp [smul_eq_mul]
    refine ⟨⟨α * g, hαg⟩, ?_⟩
    have hg' : (g : ℂ) + w = z := by
      simpa [vadd_eq_add] using hg
    change α * (g : ℂ) + α * w = α * z
    rw [← hg']
    ring

/-- On quotient representatives, `smulTorusMap` is induced by multiplication by `α`. -/
@[simp] theorem smulTorusMap_mk (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) (z : ℂ) :
    L.smulTorusMap L' α hα (Quotient.mk'' z) = Quotient.mk'' (α * z) := by
  simp [smulTorusMap]

end PeriodPair

namespace UpperHalfPlane

/-- The standard complex torus attached to `τ ∈ ℍ`. -/
abbrev torus (τ : UpperHalfPlane) :=
  τ.periodPair.Torus

end UpperHalfPlane

notation "X(" τ ")" => UpperHalfPlane.torus τ

/-- Exercise 1.5 (1): if multiplication by `α` sends the lattice of `L` into the lattice of `L'`,
then the induced map between the associated complex tori is holomorphic. -/
theorem latticeMul_descendsToHolomorphicTorusMap (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) :
    RiemannSurface.Holomorphic (L.smulTorusMap L' α hα) := sorry

/-- Exercise 1.5 (1), source-facing existence form: the descended multiplication map on the torus is
represented by the canonical quotient map `PeriodPair.smulTorusMap`. -/
theorem latticeMul_descendsToHolomorphicTorusMap_exists (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) :
    ∃ f : L.Torus → L'.Torus,
      RiemannSurface.Holomorphic f ∧
        ∀ z : ℂ, f (Quotient.mk'' z) = Quotient.mk'' (α * z) := by
  refine ⟨L.smulTorusMap L' α hα, latticeMul_descendsToHolomorphicTorusMap L L' α hα,
    ?_⟩
  intro z
  simp

/-- Exercise 1.5 (2): the descended map attached to multiplication by `α` is biholomorphic exactly
when the scaled source lattice equals the target lattice. -/
theorem latticeMul_descendsToBiholomorph_iff (L L' : PeriodPair) (α : ℂ)
    :
    (∃ F : Structomorph biholomorphicGroupoid
        L.Torus
        L'.Torus,
      ∀ z : ℂ, F.toHomeomorph (Quotient.mk'' z) = Quotient.mk'' (α * z)) ↔
        α • (L.lattice : Set ℂ) = (L'.lattice : Set ℂ) := sorry

/-- Exercise 1.5 (3): every complex torus `ℂ / Γ` is isomorphic to a torus of the form
`ℂ / (ℤ + ℤ τ)` for some `τ` with positive imaginary part. -/
theorem torus_isomorphic_standardTorus (L : PeriodPair) :
    ∃ τ : UpperHalfPlane,
      RiemannSurface.isomorphic L.Torus X(τ) := sorry

/-- Exercise 1.5 (4): if `τ' = (aτ + b) / (cτ + d)` for a matrix
`((a, b), (c, d)) ∈ SL(2, ℤ)`, then the standard tori `X(τ)` and `X(τ')` are isomorphic; in the
canonical API this is `τ' = A • τ`. -/
theorem standardTorus_isomorphic_of_sl2z (τ : UpperHalfPlane) (A : SL(2, ℤ)) :
    RiemannSurface.isomorphic X(τ) X(A • τ) := sorry
