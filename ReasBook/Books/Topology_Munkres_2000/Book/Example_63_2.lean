module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Example_63_2.BingBraidCoordinates
public import Topology_Munkres_2000.Book.Example_63_2.BingDoubleGeometry
public import Topology_Munkres_2000.Book.Example_63_2.LinkedHornApproximation
public import Topology_Munkres_2000.Book.Example_63_2.RadialAnnulus
public import Topology_Munkres_2000.Book.Example_58_3
public import Topology_Munkres_2000.Book.Lemma_60_5
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Compactification.OnePoint.Sphere

import all Topology_Munkres_2000.Book.Example_58_3.PlaneModels
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

public section

open Set
open scoped commutatorElement

/-- Helper for Example 63.2: distinct elements of a fundamental group obstruct simple
connectedness. -/
lemma not_isSimplyConnected_of_fundamentalGroup_ne {X : Type*} [TopologicalSpace X]
    (U : Set X) (u : U) (g h : FundamentalGroup U u) (hgh : g ≠ h) :
    ¬ IsSimplyConnected U := by
  -- Simple connectedness makes every based fundamental group a subsingleton.
  intro hU
  letI : SimplyConnectedSpace U := hU.simplyConnectedSpace
  exact hgh (Subsingleton.elim g h)

/-- Helper for Example 63.2: the range of an embedding is homeomorphic to its domain. -/
lemma hornedSphereRange_homeomorph
    (f : StandardSphere 2 → StandardSphere 3) (hf : Topology.IsEmbedding f) :
    Nonempty (Set.range f ≃ₜ StandardSphere 2) := by
  -- Reverse the canonical homeomorphism from the domain onto the embedding range.
  exact ⟨hf.toHomeomorph.symm⟩

/-- Helper for Example 63.2: an ambient homeomorphism restricts to a homeomorphism from
the complement of a set to the complement of its image. -/
def complImageHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K : Set X) : ↥(Kᶜ) ≃ₜ ↥((e '' K)ᶜ) :=
  (e.image Kᶜ).trans (Homeomorph.setCongr (e.image_compl K))

/-- Helper for Example 63.2: restricting an ambient homeomorphism to a complement does
not change its underlying point map. -/
lemma complImageHomeomorph_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (K : Set X) (x : ↥(Kᶜ)) :
    ((complImageHomeomorph e K x : ↥((e '' K)ᶜ)) : Y) = e x := by
  -- Both restriction steps retain the ambient value `e x`.
  rfl

/-- Helper for Example 63.2: the inverse complement restriction is the restriction of the
inverse ambient homeomorphism. -/
lemma complImageHomeomorph_symm_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (K : Set X) (y : ↥((e '' K)ᶜ)) :
    ((complImageHomeomorph e K).symm y : X) = e.symm y := by
  -- The set-congruence inverse is pointwise the identity before applying `e.symm`.
  rfl

/-- Helper for Example 63.2: pulling a detector back through the complement-image
homeomorphism preserves its value at the transported basepoint. -/
lemma complImageDetector_base
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (K : Set X) (b : ↥(Kᶜ)) (q : C(↥(Kᶜ), Z))
    {z : Z} (hq : q b = z) :
    (q.comp ((complImageHomeomorph e K).symm :
      C(↥((e '' K)ᶜ), ↥(Kᶜ)))) (complImageHomeomorph e K b) = z := by
  -- Cancel the restricted homeomorphism with its inverse, then use the original base law.
  calc
    (q.comp ((complImageHomeomorph e K).symm :
        C(↥((e '' K)ᶜ), ↥(Kᶜ)))) (complImageHomeomorph e K b) =
      q ((complImageHomeomorph e K).symm (complImageHomeomorph e K b)) := rfl
    _ = q b := congrArg q ((complImageHomeomorph e K).symm_apply_apply b)
    _ = z := hq

/-- Helper for Example 63.2: transporting a loop and its detector across an ambient
homeomorphism preserves the detected fundamental-group class. -/
lemma detectedClass_complImageHomeomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (K : Set X) (b : ↥(Kᶜ)) (mu : Path b b)
    (q : C(↥(Kᶜ), Z)) {z : Z} (hq : q b = z) :
    FundamentalGroup.mapOfEq
        (q.comp ((complImageHomeomorph e K).symm :
          C(↥((e '' K)ᶜ), ↥(Kᶜ)))) (complImageDetector_base e K b q hq)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (mu.map (complImageHomeomorph e K).continuous))) =
      FundamentalGroup.mapOfEq q hq
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk mu)) := by
  -- After applying the inverse complement homeomorphism, the transported path is pointwise
  -- the original path; endpoint casts do not change those point values.
  have hpaths :
      (((mu.map (complImageHomeomorph e K).continuous).map
          (q.comp ((complImageHomeomorph e K).symm :
            C(↥((e '' K)ᶜ), ↥(Kᶜ)))).continuous).cast
        (complImageDetector_base e K b q hq).symm
        (complImageDetector_base e K b q hq).symm) =
        (mu.map q.continuous).cast hq.symm hq.symm := by
    ext t
    exact congrArg q ((complImageHomeomorph e K).symm_apply_apply (mu t))
  -- Expand both induced maps to mapped path classes and use the pointwise path equality.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
    ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    hpaths]

/-- Helper for Example 63.2: a based loop that is not nullhomotopic represents a nonidentity
element of the fundamental group. -/
lemma fundamentalGroup_fromPath_ne_one_of_not_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} (μ : Path x x) (hμ : ¬ Path.Homotopic μ (Path.refl x)) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ) ≠ 1 := by
  -- Equality with the identity quotient would be exactly a nullhomotopy of the loop.
  intro hμone
  apply hμ
  exact (FundamentalGroupoid.fromPath_eq_iff_homotopic μ (Path.refl x)).mp hμone

/-- Helper for Example 63.2: a based map that sends a fundamental-group class to a
nonidentity class proves that the original class is nonidentity. -/
lemma fundamentalGroup_ne_one_of_map_eq_ne_one
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (q : C(X, Y)) (hq : q x = y) (g : FundamentalGroup X x)
    (z : FundamentalGroup Y y) (hmap : FundamentalGroup.mapOfEq q hq g = z)
    (hz : z ≠ 1) : g ≠ 1 := by
  -- Mapping a hypothetical identity class would force the detected class to be the identity.
  intro hg
  apply hz
  calc
    z = FundamentalGroup.mapOfEq q hq g := hmap.symm
    _ = FundamentalGroup.mapOfEq q hq 1 := congrArg _ hg
    _ = 1 := map_one _

/-- Helper for Example 63.2: a nonidentity based loop class prevents the loop from being
nullhomotopic. -/
lemma not_homotopic_refl_of_fundamentalGroup_fromPath_ne_one
    {X : Type*} [TopologicalSpace X] {x : X} (μ : Path x x)
    (hμ : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ) ≠ 1) :
    ¬ Path.Homotopic μ (Path.refl x) := by
  -- A nullhomotopy would identify the loop class with the constant-loop identity.
  intro hnull
  apply hμ
  exact (FundamentalGroupoid.fromPath_eq_iff_homotopic μ (Path.refl x)).mpr hnull

/-- Helper for Example 63.2: a nonzero circle degree detected by a based continuous map
obstructs a nullhomotopy of the original loop. -/
lemma not_homotopic_refl_of_circleDegree_ne_zero
    {X : Type*} [TopologicalSpace X] {x : X} (q : C(X, Circle)) (hq : q x = 1)
    (μ : Path x x)
    (hdegree : Multiplicative.toAdd (Circle.fundamentalGroupEquivInt
      (FundamentalGroup.mapOfEq q hq
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ)))) ≠ 0) :
    ¬ Path.Homotopic μ (Path.refl x) := by
  -- Route correction: use functorial circle degree rather than a bespoke linking number.
  -- A nullhomotopy identifies the loop class with the identity before applying the detector.
  intro hμ
  apply hdegree
  have hclass :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ) = 1 := by
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic μ (Path.refl x)).mpr hμ
  -- Both the induced map and the circle coordinate equivalence preserve the identity.
  rw [hclass, map_one, map_one]
  rfl

/-- Helper for Example 63.2: a detector that assigns degree one to a finite-stage
meridian proves that the meridian is not nullhomotopic. -/
lemma not_homotopic_refl_of_finiteStageDetector
    {X : Type*} [TopologicalSpace X] {x : X} (q : C(X, Circle)) (hq : q x = 1)
    (μ : Path x x)
    (hdegree : Circle.fundamentalGroupEquivInt
      (FundamentalGroup.mapOfEq q hq
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ))) =
      Multiplicative.ofAdd 1) :
    ¬ Path.Homotopic μ (Path.refl x) := by
  -- Reduce the geometric interface to the generic nonzero-degree obstruction.
  apply not_homotopic_refl_of_circleDegree_ne_zero q hq μ
  rw [hdegree]
  exact one_ne_zero

/-- Helper for Example 63.2: the positive generator of the circle fundamental group has a
based loop representative with degree one. -/
lemma exists_circleLoop_degree_one :
    ∃ μ : Path (1 : Circle) 1,
      Circle.fundamentalGroupEquivInt
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ)) =
          Multiplicative.ofAdd 1 := by
  -- Choose the fundamental-group element corresponding to the positive integer generator.
  let g : FundamentalGroup Circle 1 :=
    Circle.fundamentalGroupEquivInt.symm (Multiplicative.ofAdd 1)
  -- Represent that quotient class by an actual based loop.
  obtain ⟨μ, hμ⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  refine ⟨μ, ?_⟩
  calc
    Circle.fundamentalGroupEquivInt
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ)) =
      Circle.fundamentalGroupEquivInt
        (FundamentalGroup.fromPath (FundamentalGroup.toPath g)) := by
          rw [hμ]
    _ = Circle.fundamentalGroupEquivInt g := by rfl
    _ = Multiplicative.ofAdd 1 :=
      Circle.fundamentalGroupEquivInt.apply_symm_apply _

namespace AlexanderHornGeometry

/-- Helper for Example 63.2: the affine complex plane has the dimension required for its
one-point compactification to model `StandardSphere 2`. -/
lemma complexOnePointSphere_finrank :
    Module.finrank ℝ ℂ + 1 = Fintype.card (Fin (2 + 1)) := by
  -- Reduce both dimensions to their explicit finite values.
  rw [Complex.finrank_real_complex]
  norm_num

/-- Helper for Example 63.2: compactifying the affine complex plane gives the standard
two-sphere used as the source of the horned-sphere embedding. -/
noncomputable def complexOnePointSphereHomeomorph :
    OnePoint ℂ ≃ₜ StandardSphere 2 :=
  onePointEquivSphereOfFinrankEq complexOnePointSphere_finrank

/-- Helper for Example 63.2: the affine model `ℝ × ℂ` has real dimension three. -/
lemma realProdComplexOnePointSphere_finrank :
    Module.finrank ℝ (ℝ × ℂ) + 1 = Fintype.card (Fin (3 + 1)) := by
  -- Add the one real coordinate to the two real coordinates of `ℂ`.
  rw [Module.finrank_prod, Module.finrank_self, Complex.finrank_real_complex]
  norm_num

/-- Helper for Example 63.2: compactifying the affine framed-block model gives the standard
three-sphere used as the ambient space. -/
noncomputable def realProdComplexOnePointSphereHomeomorph :
    OnePoint (ℝ × ℂ) ≃ₜ StandardSphere 3 :=
  onePointEquivSphereOfFinrankEq realProdComplexOnePointSphere_finrank

/-- Helper for Example 63.2: the explicit strict-collar radial rotation underlying the
framed Bing braid. -/
noncomputable def framedRadialRotation (center : ℂ) (turn : ℝ) (z : ℂ) : ℂ :=
  center +
    (Circle.exp ((turn * Real.pi) *
      radialTwistCutoff (3 / 8) (1 / 2) ‖z - center‖) : ℂ) * (z - center)

/-- Helper for Example 63.2: a framed radial rotation preserves distance from its center. -/
lemma norm_framedRadialRotation_sub_center (center : ℂ) (turn : ℝ) (z : ℂ) :
    ‖framedRadialRotation center turn z - center‖ = ‖z - center‖ := by
  -- Translation cancels and the circle exponential has norm one.
  rw [framedRadialRotation, add_sub_cancel_left, norm_mul, Circle.norm_coe, one_mul]

/-- Helper for Example 63.2: negating the turn parameter is a left inverse. -/
lemma framedRadialRotation_neg_left (center : ℂ) (turn : ℝ) (z : ℂ) :
    framedRadialRotation center (-turn) (framedRadialRotation center turn z) = z := by
  -- Radius preservation makes the second angular factor the inverse of the first.
  rw [framedRadialRotation, norm_framedRadialRotation_sub_center]
  simp only [framedRadialRotation, add_sub_cancel_left, Circle.coe_exp]
  have hangle :
      (-turn * Real.pi) * radialTwistCutoff (3 / 8) (1 / 2) ‖z - center‖ =
        -((turn * Real.pi) * radialTwistCutoff (3 / 8) (1 / 2) ‖z - center‖) := by
    ring
  rw [hangle]
  rw [← mul_assoc, ← Complex.exp_add]
  simp only [Complex.ofReal_neg, neg_mul, neg_add_cancel, Complex.exp_zero, one_mul,
    add_sub_cancel]

/-- Helper for Example 63.2: negating the turn parameter is also a right inverse. -/
lemma framedRadialRotation_neg_right (center : ℂ) (turn : ℝ) (z : ℂ) :
    framedRadialRotation center turn (framedRadialRotation center (-turn) z) = z := by
  -- Apply the left-inverse computation to the already negated turn.
  simpa only [neg_neg] using framedRadialRotation_neg_left center (-turn) z

/-- Helper for Example 63.2: every fixed-turn framed radial rotation is continuous. -/
lemma continuous_framedRadialRotation (center : ℂ) (turn : ℝ) :
    Continuous (framedRadialRotation center turn) := by
  -- The formula uses only continuous arithmetic, norm, cutoff, and circle exponential.
  have hcutoff : Continuous
      (fun z : ℂ ↦ radialTwistCutoff (3 / 8) (1 / 2) ‖z - center‖) :=
    (continuous_radialTwistCutoff (3 / 8) (1 / 2)).comp
      (continuous_norm.comp (continuous_id.sub continuous_const))
  unfold framedRadialRotation
  fun_prop

/-- Helper for Example 63.2: the strict-collar radial twist used in the framed Bing braid. -/
noncomputable def framedRadialTwist (center : ℂ) (turn : ℝ) : ℂ ≃ₜ ℂ :=
  {
    toFun := framedRadialRotation center turn
    invFun := framedRadialRotation center (-turn)
    left_inv := framedRadialRotation_neg_left center turn
    right_inv := framedRadialRotation_neg_right center turn
    continuous_toFun := continuous_framedRadialRotation center turn
    continuous_invFun := continuous_framedRadialRotation center (-turn)
  }

/-- Helper for Example 63.2: evaluation of a framed radial twist uses its radial formula. -/
lemma framedRadialTwist_apply (center : ℂ) (turn : ℝ) (z : ℂ) :
    framedRadialTwist center turn z = framedRadialRotation center turn z := by
  -- Expose the forward map while keeping the bundled inverse opaque.
  rfl

/-- Helper for Example 63.2: the inverse framed twist uses the negated angular profile. -/
lemma framedRadialTwist_symm_apply (center : ℂ) (turn : ℝ) (z : ℂ) :
    (framedRadialTwist center turn).symm z = framedRadialRotation center (-turn) z := by
  -- Read the inverse field supplied by the explicit homeomorphism structure.
  rfl

/-- Helper for Example 63.2: zero turn gives the identity plane homeomorphism. -/
lemma framedRadialTwist_zero (center : ℂ) :
    framedRadialTwist center 0 = Homeomorph.refl ℂ := by
  -- The zero angular profile makes every radial multiplier equal to one.
  ext z
  rw [framedRadialTwist_apply]
  simp only [framedRadialRotation]
  simp only [zero_mul, Circle.exp_zero, Circle.coe_one, one_mul, add_sub_cancel,
    Homeomorph.refl_apply, id_eq]

/-- Helper for Example 63.2: every framed twist fixes the complement of its outer disk. -/
lemma framedRadialTwist_apply_of_outer_le (center : ℂ) (turn : ℝ) (z : ℂ)
    (hz : (1 / 2 : ℝ) ≤ ‖z - center‖) :
    framedRadialTwist center turn z = z := by
  -- Outside radius `1/2` the cutoff is zero, independently of the turn parameter.
  have hinnerOuter : (3 / 8 : ℝ) < 1 / 2 := by
    norm_num
  rw [framedRadialTwist_apply, framedRadialRotation,
    radialTwistCutoff_eq_zero_of_le hinnerOuter hz]
  simp only [mul_zero, Circle.exp_zero, Circle.coe_one, one_mul, add_sub_cancel]

/-- Helper for Example 63.2: the inverse framed twist fixes the complement of its outer disk. -/
lemma framedRadialTwist_symm_apply_of_outer_le (center : ℂ) (turn : ℝ) (z : ℂ)
    (hz : (1 / 2 : ℝ) ≤ ‖z - center‖) :
    (framedRadialTwist center turn).symm z = z := by
  -- Apply the inverse to the forward fixed-point equation.
  have hfixed := framedRadialTwist_apply_of_outer_le center turn z hz
  calc
    (framedRadialTwist center turn).symm z =
        (framedRadialTwist center turn).symm
          (framedRadialTwist center turn z) := congrArg _ hfixed.symm
    _ = z := (framedRadialTwist center turn).symm_apply_apply z

/-- Helper for Example 63.2: one full framed turn is a half-turn on the inner disk. -/
lemma framedRadialTwist_one_apply_of_le_inner (center z : ℂ)
    (hz : ‖z - center‖ ≤ (3 / 8 : ℝ)) :
    framedRadialTwist center 1 z = 2 * center - z := by
  -- On the strict inner disk the cutoff is one and the angle is exactly `Real.pi`.
  have hinnerOuter : (3 / 8 : ℝ) < 1 / 2 := by
    norm_num
  rw [framedRadialTwist_apply, framedRadialRotation,
    radialTwistCutoff_eq_one_of_le hinnerOuter hz]
  simp only [one_mul, mul_one, Circle.coe_exp, Complex.exp_pi_mul_I]
  ring

/-- Helper for Example 63.2: the inverse full framed turn is the same inner half-turn. -/
lemma framedRadialTwist_one_symm_apply_of_le_inner (center z : ℂ)
    (hz : ‖z - center‖ ≤ (3 / 8 : ℝ)) :
    (framedRadialTwist center 1).symm z = 2 * center - z := by
  -- The half-turn preserves the inner radius and is its own inverse.
  have hreflect : ‖(2 * center - z) - center‖ = ‖z - center‖ := by
    have hreflectCoords : (2 * center - z) - center = -(z - center) := by
      ring
    rw [hreflectCoords, norm_neg]
  have hforward : framedRadialTwist center 1 (2 * center - z) = z := by
    rw [framedRadialTwist_one_apply_of_le_inner center (2 * center - z)
      (hreflect.trans_le hz)]
    ring
  calc
    (framedRadialTwist center 1).symm z =
        (framedRadialTwist center 1).symm
          (framedRadialTwist center 1 (2 * center - z)) := congrArg _ hforward.symm
    _ = 2 * center - z :=
      (framedRadialTwist center 1).symm_apply_apply (2 * center - z)

/-- Helper for Example 63.2: framed radial twists vary jointly continuously with turn and point. -/
lemma continuous_framedRadialTwist_apply (center : ℂ) :
    Continuous (fun p : ℝ × ℂ ↦ framedRadialTwist center p.1 p.2) := by
  -- The explicit radial formula is built from continuous arithmetic, norm, cutoff, and exp.
  have hcutoff : Continuous
      (fun p : ℝ × ℂ ↦ radialTwistCutoff (3 / 8) (1 / 2) ‖p.2 - center‖) :=
    (continuous_radialTwistCutoff (3 / 8) (1 / 2)).comp
      (continuous_norm.comp (continuous_snd.sub continuous_const))
  simp only [framedRadialTwist_apply]
  unfold framedRadialRotation
  fun_prop

/-- Helper for Example 63.2: inverse framed twists also vary jointly continuously. -/
lemma continuous_framedRadialTwist_symm_apply (center : ℂ) :
    Continuous (fun p : ℝ × ℂ ↦ (framedRadialTwist center p.1).symm p.2) := by
  -- The inverse has the same explicit formula with a negated continuous angle.
  have hcutoff : Continuous
      (fun p : ℝ × ℂ ↦ radialTwistCutoff (3 / 8) (1 / 2) ‖p.2 - center‖) :=
    (continuous_radialTwistCutoff (3 / 8) (1 / 2)).comp
      (continuous_norm.comp (continuous_snd.sub continuous_const))
  simp only [framedRadialTwist_symm_apply]
  unfold framedRadialRotation
  fun_prop

/-- Helper for Example 63.2: membership in a closed ball gives an upper bound relative to
any second center. -/
lemma norm_sub_le_radius_add_norm_sub_of_mem_closedBall {z c a : ℂ} {r : ℝ}
    (hz : z ∈ Metric.closedBall c r) : ‖z - a‖ ≤ r + ‖c - a‖ := by
  -- Insert the ball center and apply the norm triangle inequality.
  have hzNorm : ‖z - c‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hcoords : z - a = (z - c) + (c - a) := by
    ring
  calc
    ‖z - a‖ = ‖(z - c) + (c - a)‖ := congrArg norm hcoords
    _ ≤ ‖z - c‖ + ‖c - a‖ := norm_add_le _ _
    _ ≤ r + ‖c - a‖ := add_le_add hzNorm le_rfl

/-- Helper for Example 63.2: membership in a closed ball gives the reverse-triangle lower
bound relative to any second center. -/
lemma norm_sub_radius_le_norm_sub_of_mem_closedBall {z c a : ℂ} {r : ℝ}
    (hz : z ∈ Metric.closedBall c r) : ‖c - a‖ - r ≤ ‖z - a‖ := by
  -- Bound the center separation by the two sides through `z` and rearrange.
  have hzNorm : ‖z - c‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have htriangle : ‖c - a‖ ≤ ‖c - z‖ + ‖z - a‖ := by
    have hcoords : c - a = (c - z) + (z - a) := by
      ring
    calc
      ‖c - a‖ = ‖(c - z) + (z - a)‖ := congrArg norm hcoords
      _ ≤ ‖c - z‖ + ‖z - a‖ := norm_add_le _ _
  rw [norm_sub_rev c z] at htriangle
  linarith

/-- Helper for Example 63.2: the framed left half-twist has a genuine collar around its
two marked fibers. -/
noncomputable def framedLeftBingHalfTwist : ℂ ≃ₜ ℂ :=
  framedRadialTwist (-(1 / 4 : ℂ)) 1

/-- Helper for Example 63.2: the framed right half-twist has a genuine collar around its
two marked fibers. -/
noncomputable def framedRightBingHalfTwist : ℂ ≃ₜ ℂ :=
  framedRadialTwist (1 / 4 : ℂ) 1

/-- Helper for Example 63.2: one framed left-positive, right-negative Bing braid pair. -/
noncomputable def framedBingBraidPair : ℂ ≃ₜ ℂ :=
  framedLeftBingHalfTwist.trans framedRightBingHalfTwist.symm

/-- Helper for Example 63.2: on the left framing disk one braid pair translates points to
the right framing disk. -/
lemma framedBingBraidPair_apply_of_mem_leftDisk {z : ℂ}
    (hz : z ∈ Metric.closedBall (-(1 / 2 : ℂ)) (1 / 16)) :
    framedBingBraidPair z = z + 1 := by
  -- The left letter is a rigid half-turn throughout the input disk.
  have hleftInner : ‖z - (-(1 / 4 : ℂ))‖ ≤ (3 / 8 : ℝ) := by
    calc
      ‖z - (-(1 / 4 : ℂ))‖ ≤
          (1 / 16 : ℝ) + ‖(-(1 / 2 : ℂ)) - (-(1 / 4 : ℂ))‖ :=
        norm_sub_le_radius_add_norm_sub_of_mem_closedBall hz
      _ ≤ 3 / 8 := by norm_num [Complex.norm_real]
  have hleft : framedLeftBingHalfTwist z = -(1 / 2 : ℂ) - z := by
    calc
      framedLeftBingHalfTwist z = 2 * (-(1 / 4 : ℂ)) - z :=
        framedRadialTwist_one_apply_of_le_inner (-(1 / 4 : ℂ)) z hleftInner
      _ = -(1 / 2 : ℂ) - z := by ring
  -- Its image lies near zero, hence inside the rigid disk of the inverse right letter.
  have hleftImageMem : (-(1 / 2 : ℂ) - z) ∈ Metric.closedBall 0 (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - (-(1 / 2 : ℂ))‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : (-(1 / 2 : ℂ) - z) - 0 = -(z - (-(1 / 2 : ℂ))) := by
      ring
    rw [hcoords, norm_neg]
    exact hzNorm
  have hrightInner : ‖(-(1 / 2 : ℂ) - z) - (1 / 4 : ℂ)‖ ≤ (3 / 8 : ℝ) := by
    calc
      ‖(-(1 / 2 : ℂ) - z) - (1 / 4 : ℂ)‖ ≤
          (1 / 16 : ℝ) + ‖(0 : ℂ) - (1 / 4 : ℂ)‖ :=
        norm_sub_le_radius_add_norm_sub_of_mem_closedBall hleftImageMem
      _ ≤ 3 / 8 := by norm_num [Complex.norm_real]
  have hright : framedRightBingHalfTwist.symm (-(1 / 2 : ℂ) - z) = z + 1 := by
    have hformula := framedRadialTwist_one_symm_apply_of_le_inner
      (1 / 4 : ℂ) (-(1 / 2 : ℂ) - z) hrightInner
    calc
      framedRightBingHalfTwist.symm (-(1 / 2 : ℂ) - z) =
          2 * (1 / 4 : ℂ) - (-(1 / 2 : ℂ) - z) := hformula
      _ = z + 1 := by ring
  -- Compose the two certified rigid formulas.
  rw [framedBingBraidPair, Homeomorph.trans_apply, hleft, hright]

/-- Helper for Example 63.2: on the middle framing disk one braid pair reflects points into
the left framing disk. -/
lemma framedBingBraidPair_apply_of_mem_middleDisk {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 (1 / 16)) :
    framedBingBraidPair z = -(1 / 2 : ℂ) - z := by
  -- The left letter is again a rigid half-turn on the middle disk.
  have hleftInner : ‖z - (-(1 / 4 : ℂ))‖ ≤ (3 / 8 : ℝ) := by
    calc
      ‖z - (-(1 / 4 : ℂ))‖ ≤
          (1 / 16 : ℝ) + ‖(0 : ℂ) - (-(1 / 4 : ℂ))‖ :=
        norm_sub_le_radius_add_norm_sub_of_mem_closedBall hz
      _ ≤ 3 / 8 := by norm_num [Complex.norm_real]
  have hleft : framedLeftBingHalfTwist z = -(1 / 2 : ℂ) - z := by
    calc
      framedLeftBingHalfTwist z = 2 * (-(1 / 4 : ℂ)) - z :=
        framedRadialTwist_one_apply_of_le_inner (-(1 / 4 : ℂ)) z hleftInner
      _ = -(1 / 2 : ℂ) - z := by ring
  -- That image is uniformly outside the right letter's support disk.
  have hleftImageMem : (-(1 / 2 : ℂ) - z) ∈
      Metric.closedBall (-(1 / 2 : ℂ)) (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - 0‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : (-(1 / 2 : ℂ) - z) - (-(1 / 2 : ℂ)) = -(z - 0) := by
      ring
    rw [hcoords, norm_neg]
    exact hzNorm
  have hrightOuter : (1 / 2 : ℝ) ≤ ‖(-(1 / 2 : ℂ) - z) - (1 / 4 : ℂ)‖ := by
    calc
      (1 / 2 : ℝ) ≤ ‖(-(1 / 2 : ℂ)) - (1 / 4 : ℂ)‖ - 1 / 16 := by
        norm_num [Complex.norm_real]
      _ ≤ ‖(-(1 / 2 : ℂ) - z) - (1 / 4 : ℂ)‖ :=
        norm_sub_radius_le_norm_sub_of_mem_closedBall hleftImageMem
  have hright := framedRadialTwist_symm_apply_of_outer_le
    (1 / 4 : ℂ) 1 (-(1 / 2 : ℂ) - z) hrightOuter
  -- The inverse right letter is the identity there.
  rw [framedBingBraidPair, Homeomorph.trans_apply, hleft]
  simpa only [framedRightBingHalfTwist] using hright

/-- Helper for Example 63.2: on the right framing disk one braid pair reflects points into
the middle framing disk. -/
lemma framedBingBraidPair_apply_of_mem_rightDisk {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 16)) :
    framedBingBraidPair z = (1 / 2 : ℂ) - z := by
  -- The left letter is uniformly outside its support on the right disk.
  have hleftOuter : (1 / 2 : ℝ) ≤ ‖z - (-(1 / 4 : ℂ))‖ := by
    calc
      (1 / 2 : ℝ) ≤ ‖(1 / 2 : ℂ) - (-(1 / 4 : ℂ))‖ - 1 / 16 := by
        norm_num [Complex.norm_real]
      _ ≤ ‖z - (-(1 / 4 : ℂ))‖ :=
        norm_sub_radius_le_norm_sub_of_mem_closedBall hz
  have hleft := framedRadialTwist_apply_of_outer_le
    (-(1 / 4 : ℂ)) 1 z hleftOuter
  have hleft' : framedLeftBingHalfTwist z = z := hleft
  -- The inverse right letter is a rigid half-turn throughout the input disk.
  have hrightInner : ‖z - (1 / 4 : ℂ)‖ ≤ (3 / 8 : ℝ) := by
    calc
      ‖z - (1 / 4 : ℂ)‖ ≤
          (1 / 16 : ℝ) + ‖(1 / 2 : ℂ) - (1 / 4 : ℂ)‖ :=
        norm_sub_le_radius_add_norm_sub_of_mem_closedBall hz
      _ ≤ 3 / 8 := by norm_num [Complex.norm_real]
  have hright := framedRadialTwist_one_symm_apply_of_le_inner
    (1 / 4 : ℂ) z hrightInner
  have hright' : framedRightBingHalfTwist.symm z = (1 / 2 : ℂ) - z := by
    calc
      framedRightBingHalfTwist.symm z = 2 * (1 / 4 : ℂ) - z := hright
      _ = (1 / 2 : ℂ) - z := by ring
  -- Compose the fixed left letter with the certified right half-turn.
  rw [framedBingBraidPair, Homeomorph.trans_apply]
  rw [hleft', hright']

/-- Helper for Example 63.2: the endpoint homeomorphism of the framed six-letter word. -/
noncomputable def framedBingBraidMonodromy : ℂ ≃ₜ ℂ :=
  (framedBingBraidPair.trans framedBingBraidPair).trans framedBingBraidPair

/-- Helper for Example 63.2: the framed six-letter word is the identity on the left seed
disk. -/
lemma framedBingBraidMonodromy_apply_of_mem_leftDisk {z : ℂ}
    (hz : z ∈ Metric.closedBall (-(1 / 2 : ℂ)) (1 / 16)) :
    framedBingBraidMonodromy z = z := by
  -- The first pair sends the left disk to the right disk without changing its displacement.
  have hfirst := framedBingBraidPair_apply_of_mem_leftDisk hz
  have hrightMem : z + 1 ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - (-(1 / 2 : ℂ))‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : (z + 1) - (1 / 2 : ℂ) = z - (-(1 / 2 : ℂ)) := by
      ring
    rw [hcoords]
    exact hzNorm
  -- The second pair sends that right disk to the middle disk.
  have hsecond : framedBingBraidPair (z + 1) = -(1 / 2 : ℂ) - z := by
    calc
      framedBingBraidPair (z + 1) = (1 / 2 : ℂ) - (z + 1) :=
        framedBingBraidPair_apply_of_mem_rightDisk hrightMem
      _ = -(1 / 2 : ℂ) - z := by ring
  have hmiddleMem : (-(1 / 2 : ℂ) - z) ∈ Metric.closedBall 0 (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - (-(1 / 2 : ℂ))‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : (-(1 / 2 : ℂ) - z) - 0 = -(z - (-(1 / 2 : ℂ))) := by
      ring
    rw [hcoords, norm_neg]
    exact hzNorm
  -- The third pair returns the middle disk point to its starting point.
  have hthird : framedBingBraidPair (-(1 / 2 : ℂ) - z) = z := by
    calc
      framedBingBraidPair (-(1 / 2 : ℂ) - z) =
          -(1 / 2 : ℂ) - (-(1 / 2 : ℂ) - z) :=
        framedBingBraidPair_apply_of_mem_middleDisk hmiddleMem
      _ = z := by ring
  rw [framedBingBraidMonodromy, Homeomorph.trans_apply, Homeomorph.trans_apply,
    hfirst, hsecond, hthird]

/-- Helper for Example 63.2: the framed six-letter word is the identity on the middle seed
disk. -/
lemma framedBingBraidMonodromy_apply_of_mem_middleDisk {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 (1 / 16)) :
    framedBingBraidMonodromy z = z := by
  -- The first pair sends the middle disk to the left disk.
  have hfirst := framedBingBraidPair_apply_of_mem_middleDisk hz
  have hleftMem : (-(1 / 2 : ℂ) - z) ∈
      Metric.closedBall (-(1 / 2 : ℂ)) (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - 0‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : (-(1 / 2 : ℂ) - z) - (-(1 / 2 : ℂ)) = -(z - 0) := by
      ring
    rw [hcoords, norm_neg]
    exact hzNorm
  -- The second pair sends the left disk to the right disk.
  have hsecond : framedBingBraidPair (-(1 / 2 : ℂ) - z) = (1 / 2 : ℂ) - z := by
    calc
      framedBingBraidPair (-(1 / 2 : ℂ) - z) =
          (-(1 / 2 : ℂ) - z) + 1 :=
        framedBingBraidPair_apply_of_mem_leftDisk hleftMem
      _ = (1 / 2 : ℂ) - z := by ring
  have hrightMem : (1 / 2 : ℂ) - z ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - 0‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : ((1 / 2 : ℂ) - z) - (1 / 2 : ℂ) = -(z - 0) := by
      ring
    rw [hcoords, norm_neg]
    exact hzNorm
  -- The third pair returns the right disk point to its starting point.
  have hthird : framedBingBraidPair ((1 / 2 : ℂ) - z) = z := by
    calc
      framedBingBraidPair ((1 / 2 : ℂ) - z) =
          (1 / 2 : ℂ) - ((1 / 2 : ℂ) - z) :=
        framedBingBraidPair_apply_of_mem_rightDisk hrightMem
      _ = z := by ring
  rw [framedBingBraidMonodromy, Homeomorph.trans_apply, Homeomorph.trans_apply,
    hfirst, hsecond, hthird]

/-- Helper for Example 63.2: the framed six-letter word is the identity on the right seed
disk. -/
lemma framedBingBraidMonodromy_apply_of_mem_rightDisk {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 16)) :
    framedBingBraidMonodromy z = z := by
  -- The first pair sends the right disk to the middle disk.
  have hfirst := framedBingBraidPair_apply_of_mem_rightDisk hz
  have hmiddleMem : (1 / 2 : ℂ) - z ∈ Metric.closedBall 0 (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - (1 / 2 : ℂ)‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : ((1 / 2 : ℂ) - z) - 0 = -(z - (1 / 2 : ℂ)) := by
      ring
    rw [hcoords, norm_neg]
    exact hzNorm
  -- The second pair sends the middle disk to the left disk.
  have hsecond : framedBingBraidPair ((1 / 2 : ℂ) - z) = z - 1 := by
    calc
      framedBingBraidPair ((1 / 2 : ℂ) - z) =
          -(1 / 2 : ℂ) - ((1 / 2 : ℂ) - z) :=
        framedBingBraidPair_apply_of_mem_middleDisk hmiddleMem
      _ = z - 1 := by ring
  have hleftMem : z - 1 ∈ Metric.closedBall (-(1 / 2 : ℂ)) (1 / 16) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzNorm : ‖z - (1 / 2 : ℂ)‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hcoords : (z - 1) - (-(1 / 2 : ℂ)) = z - (1 / 2 : ℂ) := by
      ring
    rw [hcoords]
    exact hzNorm
  -- The third pair returns the left disk point to its starting point.
  have hthird : framedBingBraidPair (z - 1) = z := by
    calc
      framedBingBraidPair (z - 1) = (z - 1) + 1 :=
        framedBingBraidPair_apply_of_mem_leftDisk hleftMem
      _ = z := by ring
  rw [framedBingBraidMonodromy, Homeomorph.trans_apply, Homeomorph.trans_apply,
    hfirst, hsecond, hthird]

/-- Helper for Example 63.2: the three marked fibers of the framed Bing braid. -/
noncomputable def framedBingMarkedPoint : Fin 3 → ℂ :=
  ![-(1 / 2 : ℂ), 0, (1 / 2 : ℂ)]

/-- Helper for Example 63.2: the framed monodromy is exactly the identity on a uniform
closed disk around every marked fiber. -/
lemma framedBingBraidMonodromy_eqOn_framingDisks (i : Fin 3) :
    Set.EqOn framedBingBraidMonodromy id
      (Metric.closedBall (framedBingMarkedPoint i) (1 / 16)) := by
  -- Reduce the finite index to the three certified disk calculations.
  intro z hz
  fin_cases i
  · simpa only [framedBingMarkedPoint, Matrix.cons_val_zero, id_eq] using
      framedBingBraidMonodromy_apply_of_mem_leftDisk hz
  · simpa only [framedBingMarkedPoint, Matrix.cons_val_one, Matrix.cons_val_zero, id_eq] using
      framedBingBraidMonodromy_apply_of_mem_middleDisk hz
  · simpa only [framedBingMarkedPoint, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, id_eq] using
      framedBingBraidMonodromy_apply_of_mem_rightDisk hz

/-- Helper for Example 63.2: one framed braid pair with a continuously varying turn. -/
noncomputable def framedBingBraidPairAt (turn : ℝ) : ℂ ≃ₜ ℂ :=
  (framedRadialTwist (-(1 / 4 : ℂ)) turn).trans
    (framedRadialTwist (1 / 4 : ℂ) turn).symm

/-- Helper for Example 63.2: the simultaneous-turn isotopy through the framed six-letter
word. -/
noncomputable def framedBingBraidMotion (t : unitInterval) : ℂ ≃ₜ ℂ :=
  ((framedBingBraidPairAt (t : ℝ)).trans (framedBingBraidPairAt (t : ℝ))).trans
    (framedBingBraidPairAt (t : ℝ))

/-- Helper for Example 63.2: the varying framed braid pair is the identity at zero turn. -/
lemma framedBingBraidPairAt_zero :
    framedBingBraidPairAt 0 = Homeomorph.refl ℂ := by
  -- Both constituent zero-turn twists are identity homeomorphisms.
  rw [framedBingBraidPairAt, framedRadialTwist_zero, framedRadialTwist_zero,
    Homeomorph.refl_symm]
  rfl

/-- Helper for Example 63.2: the framed braid motion starts at the identity. -/
lemma framedBingBraidMotion_zero :
    framedBingBraidMotion 0 = Homeomorph.refl ℂ := by
  -- At time zero every radial twist is the identity.
  have hcoe : ((0 : unitInterval) : ℝ) = 0 := rfl
  ext z
  rw [framedBingBraidMotion, hcoe, framedBingBraidPairAt_zero,
    Homeomorph.trans_apply, Homeomorph.trans_apply]
  rfl

/-- Helper for Example 63.2: the framed braid motion ends at the certified monodromy. -/
lemma framedBingBraidMotion_one :
    framedBingBraidMotion 1 = framedBingBraidMonodromy := by
  -- At time one the varying pair is the previously defined full-turn pair.
  rfl

/-- Helper for Example 63.2: evaluation of the framed braid motion is jointly continuous. -/
lemma continuous_framedBingBraidMotion_apply :
    Continuous (fun p : unitInterval × ℂ ↦ framedBingBraidMotion p.1 p.2) := by
  -- First compose the joint left-twist law with the interval coercion.
  have hturnPoint : Continuous
      (fun p : unitInterval × ℂ ↦ ((p.1 : ℝ), p.2)) := by
    fun_prop
  have hleft : Continuous
      (fun p : unitInterval × ℂ ↦
        framedRadialTwist (-(1 / 4 : ℂ)) (p.1 : ℝ) p.2) :=
    (continuous_framedRadialTwist_apply (-(1 / 4 : ℂ))).comp hturnPoint
  -- Postcompose by the inverse right twist to obtain one varying braid pair.
  have hrightInput : Continuous
      (fun p : unitInterval × ℂ ↦
        ((p.1 : ℝ), framedRadialTwist (-(1 / 4 : ℂ)) (p.1 : ℝ) p.2)) := by
    fun_prop
  have hpair : Continuous
      (fun p : unitInterval × ℂ ↦ framedBingBraidPairAt (p.1 : ℝ) p.2) := by
    have hright :=
      (continuous_framedRadialTwist_symm_apply (1 / 4 : ℂ)).comp hrightInput
    simpa only [Function.comp_def, framedBingBraidPairAt, Homeomorph.trans_apply] using
      hright
  -- Apply the same continuous pair twice more to reach the six-letter word.
  have hsecondInput : Continuous
      (fun p : unitInterval × ℂ ↦
        (p.1, framedBingBraidPairAt (p.1 : ℝ) p.2)) := by
    fun_prop
  have hsecond : Continuous
      (fun p : unitInterval × ℂ ↦
        framedBingBraidPairAt (p.1 : ℝ) (framedBingBraidPairAt (p.1 : ℝ) p.2)) :=
    hpair.comp hsecondInput
  have hthirdInput : Continuous
      (fun p : unitInterval × ℂ ↦
        (p.1, framedBingBraidPairAt (p.1 : ℝ)
          (framedBingBraidPairAt (p.1 : ℝ) p.2))) := by
    fun_prop
  have hthird := hpair.comp hthirdInput
  simpa only [Function.comp_def, framedBingBraidMotion, Homeomorph.trans_apply] using hthird

/-- Helper for Example 63.2: inverse evaluation of the framed braid motion is jointly
continuous. -/
lemma continuous_framedBingBraidMotion_symm_apply :
    Continuous (fun p : unitInterval × ℂ ↦ (framedBingBraidMotion p.1).symm p.2) := by
  -- A varying pair inverse first applies the right twist and then the inverse left twist.
  have hturnPoint : Continuous
      (fun p : unitInterval × ℂ ↦ ((p.1 : ℝ), p.2)) := by
    fun_prop
  have hright : Continuous
      (fun p : unitInterval × ℂ ↦
        framedRadialTwist (1 / 4 : ℂ) (p.1 : ℝ) p.2) :=
    (continuous_framedRadialTwist_apply (1 / 4 : ℂ)).comp hturnPoint
  have hleftInput : Continuous
      (fun p : unitInterval × ℂ ↦
        ((p.1 : ℝ), framedRadialTwist (1 / 4 : ℂ) (p.1 : ℝ) p.2)) := by
    fun_prop
  have hpairInv : Continuous
      (fun p : unitInterval × ℂ ↦ (framedBingBraidPairAt (p.1 : ℝ)).symm p.2) := by
    have hleftInv :=
      (continuous_framedRadialTwist_symm_apply (-(1 / 4 : ℂ))).comp hleftInput
    simpa only [Function.comp_def, framedBingBraidPairAt, Homeomorph.symm_trans_apply,
      Homeomorph.trans_apply, Homeomorph.symm_symm] using hleftInv
  -- Apply the varying pair inverse three times in the reverse composite.
  have hsecondInput : Continuous
      (fun p : unitInterval × ℂ ↦
        (p.1, (framedBingBraidPairAt (p.1 : ℝ)).symm p.2)) := by
    fun_prop
  have hsecond : Continuous
      (fun p : unitInterval × ℂ ↦
        (framedBingBraidPairAt (p.1 : ℝ)).symm
          ((framedBingBraidPairAt (p.1 : ℝ)).symm p.2)) :=
    hpairInv.comp hsecondInput
  have hthirdInput : Continuous
      (fun p : unitInterval × ℂ ↦
        (p.1, (framedBingBraidPairAt (p.1 : ℝ)).symm
          ((framedBingBraidPairAt (p.1 : ℝ)).symm p.2))) := by
    fun_prop
  have hthird := hpairInv.comp hthirdInput
  simpa only [Function.comp_def, framedBingBraidMotion, Homeomorph.symm_trans_apply] using
    hthird

/-- Helper for Example 63.2: each varying braid pair fixes every point outside the ambient
radius-`3/4` disk. -/
lemma framedBingBraidPairAt_apply_of_norm_ge (turn : ℝ) (z : ℂ)
    (hz : (3 / 4 : ℝ) ≤ ‖z‖) : framedBingBraidPairAt turn z = z := by
  -- Reverse triangle inequalities put `z` outside both radius-`1/2` twist supports.
  have hleftTriangle : ‖z‖ ≤ ‖z - (-(1 / 4 : ℂ))‖ + ‖(-(1 / 4 : ℂ))‖ := by
    have hcoords : z = (z - (-(1 / 4 : ℂ))) + (-(1 / 4 : ℂ)) := by
      ring
    calc
      ‖z‖ = ‖(z - (-(1 / 4 : ℂ))) + (-(1 / 4 : ℂ))‖ :=
        congrArg norm hcoords
      _ ≤ ‖z - (-(1 / 4 : ℂ))‖ + ‖(-(1 / 4 : ℂ))‖ := norm_add_le _ _
  have hleftOuter : (1 / 2 : ℝ) ≤ ‖z - (-(1 / 4 : ℂ))‖ := by
    have hleftCoords : z - (-(1 / 4 : ℂ)) = z + (1 / 4 : ℂ) := by
      ring
    have hleftNorm : ‖z - (-(1 / 4 : ℂ))‖ = ‖z + (1 / 4 : ℂ)‖ :=
      congrArg norm hleftCoords
    rw [hleftNorm]
    norm_num [Complex.norm_real] at hleftTriangle
    linarith
  have hrightTriangle : ‖z‖ ≤ ‖z - (1 / 4 : ℂ)‖ + ‖(1 / 4 : ℂ)‖ := by
    have hcoords : z = (z - (1 / 4 : ℂ)) + (1 / 4 : ℂ) := by
      ring
    calc
      ‖z‖ = ‖(z - (1 / 4 : ℂ)) + (1 / 4 : ℂ)‖ := congrArg norm hcoords
      _ ≤ ‖z - (1 / 4 : ℂ)‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
  have hrightOuter : (1 / 2 : ℝ) ≤ ‖z - (1 / 4 : ℂ)‖ := by
    norm_num [Complex.norm_real] at hrightTriangle
    linarith
  have hleft := framedRadialTwist_apply_of_outer_le
    (-(1 / 4 : ℂ)) turn z hleftOuter
  have hright := framedRadialTwist_symm_apply_of_outer_le
    (1 / 4 : ℂ) turn z hrightOuter
  -- Both letters fix `z`, so their composite does too.
  rw [framedBingBraidPairAt, Homeomorph.trans_apply, hleft, hright]

/-- Helper for Example 63.2: the full framed braid motion has fixed outer support. -/
lemma framedBingBraidMotion_apply_of_norm_ge (t : unitInterval) (z : ℂ)
    (hz : (3 / 4 : ℝ) ≤ ‖z‖) : framedBingBraidMotion t z = z := by
  -- Apply the fixed-point law to all three copies of the varying pair.
  have hpair := framedBingBraidPairAt_apply_of_norm_ge (t : ℝ) z hz
  rw [framedBingBraidMotion, Homeomorph.trans_apply, Homeomorph.trans_apply,
    hpair, hpair, hpair]

/-- Helper for Example 63.2: the forward cylinder map varies continuously. -/
lemma continuous_framedBingBraidCylinderMap :
    Continuous (fun p : unitInterval × ℂ ↦ (p.1, framedBingBraidMotion p.1 p.2)) := by
  -- Combine the unchanged time coordinate with joint motion continuity.
  exact continuous_fst.prodMk continuous_framedBingBraidMotion_apply

/-- Helper for Example 63.2: the inverse cylinder map varies continuously. -/
lemma continuous_framedBingBraidCylinderInvMap :
    Continuous
      (fun p : unitInterval × ℂ ↦ (p.1, (framedBingBraidMotion p.1).symm p.2)) := by
  -- Combine the unchanged time coordinate with joint inverse-motion continuity.
  exact continuous_fst.prodMk continuous_framedBingBraidMotion_symm_apply

/-- Helper for Example 63.2: the proposed inverse cylinder map is a left inverse. -/
lemma framedBingBraidCylinderMap_leftInverse (p : unitInterval × ℂ) :
    (p.1, (framedBingBraidMotion p.1).symm (framedBingBraidMotion p.1 p.2)) = p := by
  -- Time is unchanged and the slice homeomorphism cancels with its inverse.
  apply Prod.ext
  · rfl
  · exact (framedBingBraidMotion p.1).symm_apply_apply p.2

/-- Helper for Example 63.2: the proposed inverse cylinder map is a right inverse. -/
lemma framedBingBraidCylinderMap_rightInverse (p : unitInterval × ℂ) :
    (p.1, framedBingBraidMotion p.1 ((framedBingBraidMotion p.1).symm p.2)) = p := by
  -- Time is unchanged and the inverse slice cancels with its homeomorphism.
  apply Prod.ext
  · rfl
  · exact (framedBingBraidMotion p.1).apply_symm_apply p.2

/-- Helper for Example 63.2: the framed braid isotopy as a homeomorphism of the product
cylinder. -/
noncomputable def framedBingBraidCylinderHomeomorph :
    unitInterval × ℂ ≃ₜ unitInterval × ℂ :=
  {
    toFun := fun p ↦ (p.1, framedBingBraidMotion p.1 p.2)
    invFun := fun p ↦ (p.1, (framedBingBraidMotion p.1).symm p.2)
    left_inv := framedBingBraidCylinderMap_leftInverse
    right_inv := framedBingBraidCylinderMap_rightInverse
    continuous_toFun := continuous_framedBingBraidCylinderMap
    continuous_invFun := continuous_framedBingBraidCylinderInvMap
  }

/-- Helper for Example 63.2: evaluation of the framed cylinder homeomorphism preserves time. -/
lemma framedBingBraidCylinderHomeomorph_apply (p : unitInterval × ℂ) :
    framedBingBraidCylinderHomeomorph p =
      (p.1, framedBingBraidMotion p.1 p.2) := by
  -- Expose the forward projection formula.
  rfl

/-- Helper for Example 63.2: inverse evaluation of the framed cylinder homeomorphism
preserves time. -/
lemma framedBingBraidCylinderHomeomorph_symm_apply (p : unitInterval × ℂ) :
    framedBingBraidCylinderHomeomorph.symm p =
      (p.1, (framedBingBraidMotion p.1).symm p.2) := by
  -- Expose the inverse projection formula.
  rfl

/-- Helper for Example 63.2: the framed cylinder homeomorphism fixes the initial face. -/
lemma framedBingBraidCylinderHomeomorph_apply_zero (z : ℂ) :
    framedBingBraidCylinderHomeomorph (0, z) = (0, z) := by
  -- Use the identity slice at the initial endpoint.
  rw [framedBingBraidCylinderHomeomorph_apply, framedBingBraidMotion_zero]
  rfl

/-- Helper for Example 63.2: the framed cylinder homeomorphism fixes every endpoint seed
disk pointwise. -/
lemma framedBingBraidCylinderHomeomorph_apply_one_of_mem_framingDisk
    (i : Fin 3) {z : ℂ}
    (hz : z ∈ Metric.closedBall (framedBingMarkedPoint i) (1 / 16)) :
    framedBingBraidCylinderHomeomorph (1, z) = (1, z) := by
  -- Replace the endpoint slice by monodromy and apply its uniform framing certificate.
  have hfixed := framedBingBraidMonodromy_eqOn_framingDisks i hz
  rw [framedBingBraidCylinderHomeomorph_apply, framedBingBraidMotion_one, hfixed]
  rfl

/-- Helper for Example 63.2: the framed cylinder homeomorphism fixes the outer support
region pointwise. -/
lemma framedBingBraidCylinderHomeomorph_apply_of_norm_ge
    (p : unitInterval × ℂ) (hp : (3 / 4 : ℝ) ≤ ‖p.2‖) :
    framedBingBraidCylinderHomeomorph p = p := by
  -- Use the fixed-support law in the slice at `p.1`.
  rw [framedBingBraidCylinderHomeomorph_apply,
    framedBingBraidMotion_apply_of_norm_ge p.1 p.2 hp]

/-- Helper for Example 63.2: the triangular folded-time coordinate is nonnegative. -/
lemma framedBingFoldedTime_nonneg (t : ℝ) :
    0 ≤ max 0 (1 - |t - 1|) := by
  -- The maximum with zero is nonnegative independently of the time coordinate.
  exact le_max_left _ _

/-- Helper for Example 63.2: the triangular folded-time coordinate is at most one. -/
lemma framedBingFoldedTime_le_one (t : ℝ) :
    max 0 (1 - |t - 1|) ≤ 1 := by
  -- The absolute-value term can only decrease `1`, and zero is also at most one.
  apply max_le
  · norm_num
  · exact sub_le_self 1 (abs_nonneg _)

/-- Helper for Example 63.2: real time folds the braid forward on `[0,1]`, backward on
`[1,2]`, and to its initial slice outside that collar. -/
def framedBingFoldedTime (t : ℝ) : unitInterval :=
  ⟨max 0 (1 - |t - 1|), framedBingFoldedTime_nonneg t,
    framedBingFoldedTime_le_one t⟩

/-- Helper for Example 63.2: folded time agrees with ordinary time on the forward half of
the collar. -/
lemma framedBingFoldedTime_eq_of_mem_unitInterval (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    framedBingFoldedTime t = ⟨t, ht⟩ := by
  -- On `[0,1]`, the absolute value turns `t - 1` into `1 - t`.
  apply Subtype.ext
  simp only [framedBingFoldedTime, abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub]
  have hlinear : 1 - (1 - t) = t := by
    ring
  rw [hlinear, max_eq_right ht.1]

/-- Helper for Example 63.2: reversing a time in `[1,2]` gives a point of the unit
interval. -/
lemma framedBingReturnTime_mem_unitInterval (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    2 - t ∈ Set.Icc (0 : ℝ) 1 := by
  -- Both endpoint inequalities are immediate from the return-collar bounds.
  constructor
  · exact sub_nonneg.mpr ht.2
  · rw [sub_le_iff_le_add]
    linarith [ht.1]

/-- Helper for Example 63.2: folded time reverses ordinary time on the return half of the
collar. -/
lemma framedBingFoldedTime_eq_of_mem_returnInterval (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    framedBingFoldedTime t =
      ⟨2 - t, framedBingReturnTime_mem_unitInterval t ht⟩ := by
  -- On `[1,2]`, the triangular coordinate is the decreasing affine function `2 - t`.
  apply Subtype.ext
  simp only [framedBingFoldedTime, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  have hprofile : 0 ≤ 1 - (t - 1) := by
    linarith [ht.2]
  rw [max_eq_right hprofile]
  ring

/-- Helper for Example 63.2: folded time is zero before the compact time collar. -/
lemma framedBingFoldedTime_eq_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) :
    framedBingFoldedTime t = 0 := by
  -- Before time zero, the triangular expression is nonpositive.
  apply Subtype.ext
  simp only [framedBingFoldedTime, abs_of_nonpos (sub_nonpos.mpr (ht.trans zero_le_one)),
    neg_sub]
  have hlinear : 1 - (1 - t) = t := by
    ring
  rw [hlinear, max_eq_left ht]
  rfl

/-- Helper for Example 63.2: folded time is zero after the compact time collar. -/
lemma framedBingFoldedTime_eq_zero_of_two_le (t : ℝ) (ht : 2 ≤ t) :
    framedBingFoldedTime t = 0 := by
  -- After time two, the decreasing affine branch is nonpositive.
  apply Subtype.ext
  simp only [framedBingFoldedTime, abs_of_nonneg (sub_nonneg.mpr (by linarith : 1 ≤ t))]
  rw [max_eq_left]
  · rfl
  · linarith

/-- Helper for Example 63.2: the folded-time coordinate varies continuously. -/
lemma continuous_framedBingFoldedTime : Continuous framedBingFoldedTime := by
  -- The triangular profile is assembled from continuous subtraction, absolute value, and max.
  exact Continuous.subtype_mk
    (continuous_const.max
      (continuous_const.sub
        (continuous_abs.comp (continuous_id.sub continuous_const)))) _

/-- Helper for Example 63.2: the forward folded ambient braid map is continuous. -/
lemma continuous_framedBingAmbientMotionMap :
    Continuous (fun p : ℝ × ℂ ↦
      (p.1, framedBingBraidMotion (framedBingFoldedTime p.1) p.2)) := by
  -- First assemble the parameter pair, keeping the expensive braid evaluation behind its
  -- established joint-continuity lemma.
  have hinput : Continuous (fun p : ℝ × ℂ ↦
      (framedBingFoldedTime p.1, p.2)) :=
    (continuous_framedBingFoldedTime.comp continuous_fst).prodMk continuous_snd
  have hspatial : Continuous (fun p : ℝ × ℂ ↦
      framedBingBraidMotion (framedBingFoldedTime p.1) p.2) := by
    simpa only [Function.comp_def] using
      continuous_framedBingBraidMotion_apply.comp hinput
  exact continuous_fst.prodMk hspatial

/-- Helper for Example 63.2: the inverse folded ambient braid map is continuous. -/
lemma continuous_framedBingAmbientMotionInvMap :
    Continuous (fun p : ℝ × ℂ ↦
      (p.1, (framedBingBraidMotion (framedBingFoldedTime p.1)).symm p.2)) := by
  -- Assemble the same parameter pair before invoking joint continuity of inverse evaluation.
  have hinput : Continuous (fun p : ℝ × ℂ ↦
      (framedBingFoldedTime p.1, p.2)) :=
    (continuous_framedBingFoldedTime.comp continuous_fst).prodMk continuous_snd
  have hspatial : Continuous (fun p : ℝ × ℂ ↦
      (framedBingBraidMotion (framedBingFoldedTime p.1)).symm p.2) := by
    simpa only [Function.comp_def] using
      continuous_framedBingBraidMotion_symm_apply.comp hinput
  exact continuous_fst.prodMk hspatial

/-- Helper for Example 63.2: the proposed inverse ambient motion is a left inverse. -/
lemma framedBingAmbientMotionMap_leftInverse (p : ℝ × ℂ) :
    (p.1, (framedBingBraidMotion (framedBingFoldedTime p.1)).symm
      (framedBingBraidMotion (framedBingFoldedTime p.1) p.2)) = p := by
  -- The time coordinate is fixed and the fiber homeomorphism cancels with its inverse.
  apply Prod.ext
  · rfl
  · exact (framedBingBraidMotion (framedBingFoldedTime p.1)).symm_apply_apply p.2

/-- Helper for Example 63.2: the proposed inverse ambient motion is a right inverse. -/
lemma framedBingAmbientMotionMap_rightInverse (p : ℝ × ℂ) :
    (p.1, framedBingBraidMotion (framedBingFoldedTime p.1)
      ((framedBingBraidMotion (framedBingFoldedTime p.1)).symm p.2)) = p := by
  -- The time coordinate is fixed and the fiber inverse cancels with the homeomorphism.
  apply Prod.ext
  · rfl
  · exact (framedBingBraidMotion (framedBingFoldedTime p.1)).apply_symm_apply p.2

/-- Helper for Example 63.2: the framed braid extends to a compactly supported ambient
homeomorphism of the affine three-space model `ℝ × ℂ`. -/
noncomputable def framedBingAmbientMotionHomeomorph : (ℝ × ℂ) ≃ₜ (ℝ × ℂ) :=
  {
    toFun := fun p ↦ (p.1, framedBingBraidMotion (framedBingFoldedTime p.1) p.2)
    invFun := fun p ↦
      (p.1, (framedBingBraidMotion (framedBingFoldedTime p.1)).symm p.2)
    left_inv := framedBingAmbientMotionMap_leftInverse
    right_inv := framedBingAmbientMotionMap_rightInverse
    continuous_toFun := continuous_framedBingAmbientMotionMap
    continuous_invFun := continuous_framedBingAmbientMotionInvMap
  }

/-- Helper for Example 63.2: evaluation of the ambient braid preserves the real-time
coordinate. -/
lemma framedBingAmbientMotionHomeomorph_apply (p : ℝ × ℂ) :
    framedBingAmbientMotionHomeomorph p =
      (p.1, framedBingBraidMotion (framedBingFoldedTime p.1) p.2) := by
  -- Expose the forward projection formula.
  rfl

/-- Helper for Example 63.2: the ambient braid agrees with the original cylinder braid on
the forward time collar. -/
lemma framedBingAmbientMotionHomeomorph_apply_of_mem_unitInterval
    (t : ℝ) (z : ℂ) (ht : t ∈ Set.Icc 0 1) :
    framedBingAmbientMotionHomeomorph (t, z) =
      (t, framedBingBraidMotion ⟨t, ht⟩ z) := by
  -- Replace folded time by its forward-interval formula.
  rw [framedBingAmbientMotionHomeomorph_apply,
    framedBingFoldedTime_eq_of_mem_unitInterval t ht]

/-- Helper for Example 63.2: the ambient braid traverses the original cylinder motion in
reverse on the return time collar. -/
lemma framedBingAmbientMotionHomeomorph_apply_of_mem_returnInterval
    (t : ℝ) (z : ℂ) (ht : t ∈ Set.Icc 1 2) :
    framedBingAmbientMotionHomeomorph (t, z) =
      (t, framedBingBraidMotion
        ⟨2 - t, framedBingReturnTime_mem_unitInterval t ht⟩ z) := by
  -- Replace folded time by its decreasing return-interval formula.
  rw [framedBingAmbientMotionHomeomorph_apply,
    framedBingFoldedTime_eq_of_mem_returnInterval t ht]

/-- Helper for Example 63.2: the ambient braid is the identity before the time collar. -/
lemma framedBingAmbientMotionHomeomorph_apply_of_nonpos
    (t : ℝ) (z : ℂ) (ht : t ≤ 0) :
    framedBingAmbientMotionHomeomorph (t, z) = (t, z) := by
  -- Fold to the initial braid slice, which is the identity.
  rw [framedBingAmbientMotionHomeomorph_apply,
    framedBingFoldedTime_eq_zero_of_nonpos t ht, framedBingBraidMotion_zero]
  simp only [Homeomorph.refl_apply, id_eq]

/-- Helper for Example 63.2: the ambient braid is the identity after the time collar. -/
lemma framedBingAmbientMotionHomeomorph_apply_of_two_le
    (t : ℝ) (z : ℂ) (ht : 2 ≤ t) :
    framedBingAmbientMotionHomeomorph (t, z) = (t, z) := by
  -- Fold to the initial braid slice, which is the identity.
  rw [framedBingAmbientMotionHomeomorph_apply,
    framedBingFoldedTime_eq_zero_of_two_le t ht, framedBingBraidMotion_zero]
  simp only [Homeomorph.refl_apply, id_eq]

/-- Helper for Example 63.2: the ambient braid is the identity outside the spatial support
radius. -/
lemma framedBingAmbientMotionHomeomorph_apply_of_norm_ge
    (p : ℝ × ℂ) (hp : (3 / 4 : ℝ) ≤ ‖p.2‖) :
    framedBingAmbientMotionHomeomorph p = p := by
  -- The fixed-support law holds on every folded-time slice.
  rw [framedBingAmbientMotionHomeomorph_apply,
    framedBingBraidMotion_apply_of_norm_ge (framedBingFoldedTime p.1) p.2 hp]

/-- Helper for Example 63.2: compactifying the ambient affine braid gives a global
homeomorphism of the standard three-sphere. -/
noncomputable def framedBingAmbientSphereHomeomorph :
    StandardSphere 3 ≃ₜ StandardSphere 3 :=
  realProdComplexOnePointSphereHomeomorph.symm.trans
    (framedBingAmbientMotionHomeomorph.onePointCongr.trans
      realProdComplexOnePointSphereHomeomorph)

/-- Helper for Example 63.2: on affine points, the compactified ambient braid is the affine
motion conjugated by the fixed sphere chart. -/
lemma framedBingAmbientSphereHomeomorph_apply_affine (p : ℝ × ℂ) :
    framedBingAmbientSphereHomeomorph
        (realProdComplexOnePointSphereHomeomorph (p : OnePoint (ℝ × ℂ))) =
      realProdComplexOnePointSphereHomeomorph
        (framedBingAmbientMotionHomeomorph p : OnePoint (ℝ × ℂ)) := by
  -- Conjugation cancels the sphere chart and `onePointCongr` evaluates by the affine map.
  simp only [framedBingAmbientSphereHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply, Homeomorph.onePointCongr_apply, OnePoint.map_some]

/-- Helper for Example 63.2: the compactified ambient braid fixes the point at infinity. -/
lemma framedBingAmbientSphereHomeomorph_apply_infinity :
    framedBingAmbientSphereHomeomorph
        (realProdComplexOnePointSphereHomeomorph
          (OnePoint.infty : OnePoint (ℝ × ℂ))) =
      realProdComplexOnePointSphereHomeomorph OnePoint.infty := by
  -- Every `onePointCongr` fixes the compactification point.
  simp only [framedBingAmbientSphereHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply, Homeomorph.onePointCongr_apply, OnePoint.map_infty]

/-- Helper for Example 63.2: the seed cylinder around a marked braid fiber. -/
def framedBingSeedCylinder (i : Fin 3) : Set (unitInterval × ℂ) :=
  Set.univ ×ˢ Metric.closedBall (framedBingMarkedPoint i) (1 / 16)

/-- Helper for Example 63.2: the three seed cylinders are pairwise disjoint. -/
lemma framedBingSeedCylinders_disjoint :
    Disjoint (framedBingSeedCylinder 0) (framedBingSeedCylinder 1) ∧
      Disjoint (framedBingSeedCylinder 0) (framedBingSeedCylinder 2) ∧
        Disjoint (framedBingSeedCylinder 1) (framedBingSeedCylinder 2) := by
  -- Reduce product disjointness to the three fixed-radius disk separations.
  constructor
  · simp only [framedBingSeedCylinder]
    rw [Set.disjoint_prod]
    right
    apply Metric.closedBall_disjoint_closedBall
    simp only [framedBingMarkedPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num [Complex.dist_eq, Complex.norm_real]
  · constructor
    · simp only [framedBingSeedCylinder]
      rw [Set.disjoint_prod]
      right
      apply Metric.closedBall_disjoint_closedBall
      simp only [framedBingMarkedPoint, Matrix.cons_val_zero, Matrix.cons_val_two]
      norm_num [Complex.dist_eq, Complex.norm_real]
    · simp only [framedBingSeedCylinder]
      rw [Set.disjoint_prod]
      right
      apply Metric.closedBall_disjoint_closedBall
      simp only [framedBingMarkedPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      norm_num [Complex.dist_eq, Complex.norm_real]

/-- Helper for Example 63.2: the product homeomorphism carries the three seed cylinders to
pairwise disjoint framed tubes. -/
lemma framedBingBraidCylinderHomeomorph_seedImages_disjoint :
    Disjoint
        (framedBingBraidCylinderHomeomorph '' framedBingSeedCylinder 0)
        (framedBingBraidCylinderHomeomorph '' framedBingSeedCylinder 1) ∧
      Disjoint
          (framedBingBraidCylinderHomeomorph '' framedBingSeedCylinder 0)
          (framedBingBraidCylinderHomeomorph '' framedBingSeedCylinder 2) ∧
        Disjoint
          (framedBingBraidCylinderHomeomorph '' framedBingSeedCylinder 1)
          (framedBingBraidCylinderHomeomorph '' framedBingSeedCylinder 2) := by
  -- Injectivity transports each source-cylinder separation to its image tube.
  rcases framedBingSeedCylinders_disjoint with ⟨h01, h02, h12⟩
  exact ⟨Set.disjoint_image_of_injective framedBingBraidCylinderHomeomorph.injective h01,
    Set.disjoint_image_of_injective framedBingBraidCylinderHomeomorph.injective h02,
    Set.disjoint_image_of_injective framedBingBraidCylinderHomeomorph.injective h12⟩

/-- Helper for Example 63.2: the image of one marked seed cylinder under the framed
Bing braid. -/
def framedBingTube (i : Fin 3) : Set (unitInterval × ℂ) :=
  framedBingBraidCylinderHomeomorph '' framedBingSeedCylinder i

/-- Helper for Example 63.2: a framed Bing tube is canonically homeomorphic to its seed
cylinder. -/
noncomputable def framedBingTubeHomeomorph (i : Fin 3) :
    framedBingSeedCylinder i ≃ₜ framedBingTube i :=
  framedBingBraidCylinderHomeomorph.image (framedBingSeedCylinder i)

/-- Helper for Example 63.2: each framed Bing tube is compact. -/
lemma isCompact_framedBingTube (i : Fin 3) : IsCompact (framedBingTube i) := by
  -- Compactness of the interval and disk first gives compactness of the seed cylinder.
  have hseed : IsCompact (framedBingSeedCylinder i) := by
    rw [framedBingSeedCylinder]
    exact isCompact_univ.prod (isCompact_closedBall _ _)
  -- A homeomorphism preserves compactness of the seed image.
  exact framedBingBraidCylinderHomeomorph.isCompact_image.mpr hseed

/-- Helper for Example 63.2: each framed Bing tube is closed. -/
lemma isClosed_framedBingTube (i : Fin 3) : IsClosed (framedBingTube i) := by
  -- The ambient product is Hausdorff, so the compact tube is closed.
  exact (isCompact_framedBingTube i).isClosed

/-- Helper for Example 63.2: the initial and terminal slices of a framed tube are exactly
the original framing disk. -/
lemma framedBingTube_boundarySlices (i : Fin 3) (z : ℂ) :
    ((0, z) ∈ framedBingTube i ↔
        z ∈ Metric.closedBall (framedBingMarkedPoint i) (1 / 16)) ∧
      ((1, z) ∈ framedBingTube i ↔
        z ∈ Metric.closedBall (framedBingMarkedPoint i) (1 / 16)) := by
  -- On the initial face, injectivity and the pointwise fixed-face law recover the seed point.
  constructor
  · constructor
    · rintro ⟨p, hp, himage⟩
      have hpEq : p = (0, z) :=
        framedBingBraidCylinderHomeomorph.injective
          (himage.trans (framedBingBraidCylinderHomeomorph_apply_zero z).symm)
      rw [hpEq] at hp
      exact hp.2
    · intro hz
      exact ⟨(0, z), ⟨Set.mem_univ _, hz⟩,
        framedBingBraidCylinderHomeomorph_apply_zero z⟩
  · constructor
    · rintro ⟨p, hp, himage⟩
      have htime : p.1 = 1 := by
        have := congrArg Prod.fst himage
        simpa only [framedBingBraidCylinderHomeomorph_apply] using this
      have hpPair : p = (1, p.2) := by
        apply Prod.ext
        · exact htime
        · rfl
      have hfixed : framedBingBraidCylinderHomeomorph p = p := by
        rw [hpPair]
        exact framedBingBraidCylinderHomeomorph_apply_one_of_mem_framingDisk i hp.2
      have hpEq : p = (1, z) := hfixed.symm.trans himage
      rw [hpEq] at hp
      exact hp.2
    · intro hz
      exact ⟨(1, z), ⟨Set.mem_univ _, hz⟩,
        framedBingBraidCylinderHomeomorph_apply_one_of_mem_framingDisk i hz⟩

/-- Helper for Example 63.2: every point of a seed cylinder has spatial norm at most
`9 / 16`. -/
lemma norm_snd_le_of_mem_framedBingSeedCylinder (i : Fin 3)
    {p : unitInterval × ℂ} (hp : p ∈ framedBingSeedCylinder i) :
    ‖p.2‖ ≤ (9 / 16 : ℝ) := by
  -- The three marked centers all have norm at most one half.
  have hcenter : ‖framedBingMarkedPoint i‖ ≤ (1 / 2 : ℝ) := by
    fin_cases i <;>
      norm_num [framedBingMarkedPoint, Complex.norm_real]
  -- Add the framing radius to that center bound.
  have htriangle := norm_sub_le_radius_add_norm_sub_of_mem_closedBall
    (z := p.2) (c := framedBingMarkedPoint i) (a := 0) (r := (1 / 16 : ℝ)) hp.2
  have hcenter' : ‖framedBingMarkedPoint i - 0‖ ≤ (1 / 2 : ℝ) := by
    simpa only [sub_zero] using hcenter
  have hsum : (1 / 16 : ℝ) + ‖framedBingMarkedPoint i - 0‖ ≤ 9 / 16 := by
    linarith
  simpa only [sub_zero] using htriangle.trans hsum

/-- Helper for Example 63.2: every framed tube remains in the radius-`3 / 4` spatial
cylinder. -/
lemma framedBingTube_subset_closedBall (i : Fin 3) :
    framedBingTube i ⊆ Set.univ ×ˢ Metric.closedBall 0 (3 / 4) := by
  -- Pull an image point back to its seed point and use the compact-support fixed-point law.
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨Set.mem_univ _, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hpBound := norm_snd_le_of_mem_framedBingSeedCylinder i hp
  have hpStrict : ‖p.2‖ < (3 / 4 : ℝ) := by
    linarith
  by_contra hbound
  have himageBound : (3 / 4 : ℝ) ≤
      ‖(framedBingBraidCylinderHomeomorph p).2‖ := by
    exact le_of_not_ge hbound
  have hfixed := framedBingBraidCylinderHomeomorph_apply_of_norm_ge
    (framedBingBraidCylinderHomeomorph p) himageBound
  have hpEq : p = framedBingBraidCylinderHomeomorph p :=
    framedBingBraidCylinderHomeomorph.injective hfixed.symm
  have hnormEq : ‖p.2‖ = ‖(framedBingBraidCylinderHomeomorph p).2‖ :=
    congrArg (fun q : unitInterval × ℂ ↦ ‖q.2‖) hpEq
  linarith

/-- Helper for Example 63.2: the diameter of each standard framed Bing tube is at most
`3 / 2`. -/
lemma framedBingTube_diam_le (i : Fin 3) :
    Metric.diam (framedBingTube i) ≤ (3 / 2 : ℝ) := by
  -- Bound the two product coordinates separately inside the standard spatial cylinder.
  refine Metric.diam_le_of_forall_dist_le (by norm_num) ?_
  intro x hx y hy
  have hxCylinder := framedBingTube_subset_closedBall i hx
  have hyCylinder := framedBingTube_subset_closedBall i hy
  have htime : dist x.1 y.1 ≤ (1 : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq]
    exact abs_sub_le_iff.mpr ⟨by linarith [x.1.property.2, y.1.property.1],
      by linarith [y.1.property.2, x.1.property.1]⟩
  have hxSpatial : dist x.2 0 ≤ (3 / 4 : ℝ) := by
    simpa only [Metric.mem_closedBall] using hxCylinder.2
  have hySpatial : dist 0 y.2 ≤ (3 / 4 : ℝ) := by
    rw [dist_comm]
    simpa only [Metric.mem_closedBall] using hyCylinder.2
  have hspatial : dist x.2 y.2 ≤ (3 / 2 : ℝ) := by
    calc
      dist x.2 y.2 ≤ dist x.2 0 + dist 0 y.2 := dist_triangle _ _ _
      _ ≤ 3 / 4 + 3 / 4 := add_le_add hxSpatial hySpatial
      _ = 3 / 2 := by norm_num
  rw [Prod.dist_eq]
  exact max_le (htime.trans (by norm_num)) hspatial

/-- Helper for Example 63.2: simultaneous scaling of the interval and complex coordinates
compresses the standard framed Bing block into `ℝ × ℂ`. -/
noncomputable def framedBingAffineCompression (scale : ℝ) :
    unitInterval × ℂ → ℝ × ℂ :=
  fun p ↦ scale • ((p.1 : ℝ), p.2)

/-- Helper for Example 63.2: the affine compression of the framed Bing block is
continuous. -/
lemma continuous_framedBingAffineCompression (scale : ℝ) :
    Continuous (framedBingAffineCompression scale) := by
  -- Both coordinates are continuous and multiplication by the fixed scale is continuous.
  unfold framedBingAffineCompression
  fun_prop

/-- Helper for Example 63.2: affine compression scales every distance in the framed block
by the absolute value of its scale. -/
lemma dist_framedBingAffineCompression (scale : ℝ)
    (p q : unitInterval × ℂ) :
    dist (framedBingAffineCompression scale p)
        (framedBingAffineCompression scale q) =
      |scale| * dist p q := by
  -- Regard both coordinates as one product norm and use the exact scalar-distance law.
  rw [framedBingAffineCompression, framedBingAffineCompression, dist_smul₀]
  simp only [Real.norm_eq_abs, Prod.dist_eq, Subtype.dist_eq]

/-- Helper for Example 63.2: affine compression by a nonzero scale is injective. -/
lemma framedBingAffineCompression_injective {scale : ℝ} (hscale : scale ≠ 0) :
    Function.Injective (framedBingAffineCompression scale) := by
  -- Equality of compressed points makes their scaled distance vanish; cancel the scale.
  intro p q hpq
  have hdist : |scale| * dist p q = 0 := by
    rw [← dist_framedBingAffineCompression, hpq, dist_self]
  have habs : |scale| ≠ 0 := abs_ne_zero.mpr hscale
  have hpqDist : dist p q = 0 := (mul_eq_zero.mp hdist).resolve_left habs
  exact dist_eq_zero.mp hpqDist

/-- Helper for Example 63.2: a nonzero affine compression has an explicit inverse
Lipschitz bound. -/
lemma framedBingAffineCompression_antilipschitz {scale : ℝ} (hscale : scale ≠ 0) :
    AntilipschitzWith
      (Real.toNNReal ((|scale|)⁻¹))
      (framedBingAffineCompression scale) := by
  -- The exact distance formula reduces the bound to cancellation of a nonzero scalar.
  apply AntilipschitzWith.of_le_mul_dist
  intro p q
  rw [dist_framedBingAffineCompression]
  rw [Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr (abs_nonneg scale))]
  rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hscale), one_mul]

/-- Helper for Example 63.2: compression at a nonzero scale embeds the whole framed block
in the affine three-dimensional model `ℝ × ℂ`. -/
lemma framedBingAffineCompression_isEmbedding {scale : ℝ} (hscale : scale ≠ 0) :
    Topology.IsEmbedding (framedBingAffineCompression scale) := by
  -- Combine the inverse Lipschitz estimate with continuity of the coordinate scaling.
  exact (framedBingAffineCompression_antilipschitz hscale).isEmbedding
    (continuous_framedBingAffineCompression scale)

/-- Helper for Example 63.2: a compressed framed tube has diameter at most its scale
times the model-tube diameter bound. -/
lemma framedBingAffineCompression_tube_diam_le (scale : ℝ) (i : Fin 3) :
    Metric.diam (framedBingAffineCompression scale '' framedBingTube i) ≤
      |scale| * (3 / 2 : ℝ) := by
  -- Compare two image points, pull them back to the compact model tube, and apply its bound.
  refine Metric.diam_le_of_forall_dist_le
    (mul_nonneg (abs_nonneg scale) (by norm_num)) ?_
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  rw [dist_framedBingAffineCompression]
  have hpq : dist p q ≤ Metric.diam (framedBingTube i) :=
    Metric.dist_le_diam_of_mem (isCompact_framedBingTube i).isBounded hp hq
  exact mul_le_mul_of_nonneg_left
    (hpq.trans (framedBingTube_diam_le i)) (abs_nonneg scale)

/-- Helper for Example 63.2: every positive target mesh admits one positive affine scale
at which all three framed tubes have smaller diameter. -/
lemma exists_framedBingAffineCompression_tube_diam_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ scale > 0, ∀ i : Fin 3,
      Metric.diam (framedBingAffineCompression scale '' framedBingTube i) < ε := by
  -- Scaling by half the requested mesh leaves room in the model bound `3 / 2`.
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro i
  calc
    Metric.diam (framedBingAffineCompression (ε / 2) '' framedBingTube i) ≤
        |ε / 2| * (3 / 2 : ℝ) :=
      framedBingAffineCompression_tube_diam_le (ε / 2) i
    _ = 3 * ε / 4 := by rw [abs_of_pos (half_pos hε)]; ring
    _ < ε := by linarith

/-- Helper for Example 63.2: the two outer framed tubes form the standard local child
obstacle. -/
def framedBingChildObstacle : Set (unitInterval × ℂ) :=
  framedBingTube 0 ∪ framedBingTube 2

/-- Helper for Example 63.2: the standard local child obstacle is compact. -/
lemma isCompact_framedBingChildObstacle : IsCompact framedBingChildObstacle := by
  -- The obstacle is a finite union of compact image tubes.
  exact (isCompact_framedBingTube 0).union (isCompact_framedBingTube 2)

/-- Helper for Example 63.2: the standard local child obstacle is closed. -/
lemma isClosed_framedBingChildObstacle : IsClosed framedBingChildObstacle := by
  -- Compactness closes the finite obstacle in the Hausdorff cylinder.
  exact isCompact_framedBingChildObstacle.isClosed

/-- Helper for Example 63.2: the planar pair of pants at the initial face of the framed
Bing block, bounded externally by the support disk and internally by the two child disks. -/
def framedBingBottomPairOfPants : Set (unitInterval × ℂ) :=
  ({0} : Set unitInterval) ×ˢ
    (Metric.closedBall 0 (3 / 4) \
      (Metric.ball (framedBingMarkedPoint 0) (1 / 16) ∪
        Metric.ball (framedBingMarkedPoint 2) (1 / 16)))

/-- Helper for Example 63.2: the bottom pair of pants is compact. -/
lemma isCompact_framedBingBottomPairOfPants :
    IsCompact framedBingBottomPairOfPants := by
  -- Remove the two open child disks from the compact support disk, then take the zero face.
  unfold framedBingBottomPairOfPants
  exact isCompact_singleton.prod
    ((isCompact_closedBall 0 (3 / 4)).diff
      (Metric.isOpen_ball.union Metric.isOpen_ball))

/-- Helper for Example 63.2: the lateral boundary of a seed cylinder before applying the
framed braid homeomorphism. -/
def framedBingSeedLateralBoundary (i : Fin 3) : Set (unitInterval × ℂ) :=
  Set.univ ×ˢ Metric.sphere (framedBingMarkedPoint i) (1 / 16)

/-- Helper for Example 63.2: a seed cylinder's lateral boundary is compact. -/
lemma isCompact_framedBingSeedLateralBoundary (i : Fin 3) :
    IsCompact (framedBingSeedLateralBoundary i) := by
  -- Both the unit interval and the boundary circle are compact.
  unfold framedBingSeedLateralBoundary
  exact isCompact_univ.prod (isCompact_sphere _ _)

/-- Helper for Example 63.2: the braided lateral boundary of the `i`th framed tube. -/
def framedBingTubeLateralBoundary (i : Fin 3) : Set (unitInterval × ℂ) :=
  framedBingBraidCylinderHomeomorph '' framedBingSeedLateralBoundary i

/-- Helper for Example 63.2: every braided lateral tube boundary is compact. -/
lemma isCompact_framedBingTubeLateralBoundary (i : Fin 3) :
    IsCompact (framedBingTubeLateralBoundary i) := by
  -- Transport compactness through the framed cylinder homeomorphism.
  exact framedBingBraidCylinderHomeomorph.isCompact_image.mpr
    (isCompact_framedBingSeedLateralBoundary i)

/-- Helper for Example 63.2: a braided lateral boundary lies in its corresponding closed
framed tube. -/
lemma framedBingTubeLateralBoundary_subset_tube (i : Fin 3) :
    framedBingTubeLateralBoundary i ⊆ framedBingTube i := by
  -- The seed boundary circle lies in the seed disk, and the same homeomorphism maps both.
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p, ⟨hp.1, Metric.sphere_subset_closedBall hp.2⟩, rfl⟩

/-- Helper for Example 63.2: the two lateral child boundaries of the horn patch are
disjoint. -/
lemma framedBingOuterTubeLateralBoundaries_disjoint :
    Disjoint (framedBingTubeLateralBoundary 0)
      (framedBingTubeLateralBoundary 2) := by
  -- Restrict the already proved disjointness of the two outer closed framed tubes.
  exact framedBingBraidCylinderHomeomorph_seedImages_disjoint.2.1.mono
    (framedBingTubeLateralBoundary_subset_tube 0)
    (framedBingTubeLateralBoundary_subset_tube 2)

/-- Helper for Example 63.2: each lateral tube meets both endpoint faces in exactly its
marked boundary circle. -/
lemma framedBingTubeLateralBoundary_boundarySlices (i : Fin 3) (z : ℂ) :
    ((0, z) ∈ framedBingTubeLateralBoundary i ↔
        z ∈ Metric.sphere (framedBingMarkedPoint i) (1 / 16)) ∧
      ((1, z) ∈ framedBingTubeLateralBoundary i ↔
        z ∈ Metric.sphere (framedBingMarkedPoint i) (1 / 16)) := by
  -- The initial face is fixed pointwise, while the framed endpoint disk is also fixed pointwise.
  constructor
  · constructor
    · rintro ⟨p, hp, himage⟩
      have hpEq : p = (0, z) :=
        framedBingBraidCylinderHomeomorph.injective
          (himage.trans (framedBingBraidCylinderHomeomorph_apply_zero z).symm)
      rw [hpEq] at hp
      exact hp.2
    · intro hz
      exact ⟨(0, z), ⟨Set.mem_univ _, hz⟩,
        framedBingBraidCylinderHomeomorph_apply_zero z⟩
  · constructor
    · rintro ⟨p, hp, himage⟩
      have htime : p.1 = 1 := by
        have htimeImage := congrArg Prod.fst himage
        simpa only [framedBingBraidCylinderHomeomorph_apply] using htimeImage
      have hpPair : p = (1, p.2) := by
        apply Prod.ext
        · exact htime
        · rfl
      have hfixed : framedBingBraidCylinderHomeomorph p = p := by
        rw [hpPair]
        exact framedBingBraidCylinderHomeomorph_apply_one_of_mem_framingDisk i
          (Metric.sphere_subset_closedBall hp.2)
      have hpEq : p = (1, z) := hfixed.symm.trans himage
      rw [hpEq] at hp
      exact hp.2
    · intro hz
      exact ⟨(1, z), ⟨Set.mem_univ _, hz⟩,
        framedBingBraidCylinderHomeomorph_apply_one_of_mem_framingDisk i
          (Metric.sphere_subset_closedBall hz)⟩

/-- Helper for Example 63.2: the inner radius used for a capped framed Bing annulus is
positive. -/
lemma framedBingCapInnerRadius_pos : (0 : ℝ) < 1 / 32 := by
  -- The chosen dyadic inner radius is strictly positive.
  norm_num

/-- Helper for Example 63.2: the capped framed Bing annulus has strictly ordered radii. -/
lemma framedBingCapInnerRadius_lt_outer : (1 / 32 : ℝ) < 1 / 16 := by
  -- The outer dyadic radius is twice the inner radius.
  norm_num

/-- Helper for Example 63.2: each capped radial annulus is homeomorphic to the braided lateral
boundary of its corresponding framed Bing tube. -/
noncomputable def framedBingLateralAnnulusHomeomorph (i : Fin 3) :
    closedRadialAnnulus (framedBingMarkedPoint i) (1 / 32) (1 / 16) ≃ₜ
      framedBingTubeLateralBoundary i :=
  -- First normalize the annulus onto the seed cylinder boundary, then transport that boundary
  -- through the framed braid homeomorphism.
  (radialAnnulusHomeomorph (framedBingMarkedPoint i) (1 / 32) (1 / 16)
      framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer).trans
    (framedBingBraidCylinderHomeomorph.image (framedBingSeedLateralBoundary i))

/-- Helper for Example 63.2: the braided annulus homeomorphism is the framed cylinder map applied
to radial collar coordinates. -/
lemma framedBingLateralAnnulusHomeomorph_apply (i : Fin 3)
    (z : closedRadialAnnulus (framedBingMarkedPoint i) (1 / 32) (1 / 16)) :
    ((framedBingLateralAnnulusHomeomorph i z : framedBingTubeLateralBoundary i) :
        unitInterval × ℂ) =
      framedBingBraidCylinderHomeomorph
        (radialAnnulusCollar (framedBingMarkedPoint i) (1 / 32) (1 / 16)
          framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z) := by
  -- First expose the image homeomorphism at the ambient level, then rewrite the annulus map.
  calc
    ((framedBingLateralAnnulusHomeomorph i z : framedBingTubeLateralBoundary i) :
        unitInterval × ℂ) =
        framedBingBraidCylinderHomeomorph
          ((radialAnnulusHomeomorph (framedBingMarkedPoint i) (1 / 32) (1 / 16)
            framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z :
              (Set.univ : Set unitInterval) ×ˢ
                Metric.sphere (framedBingMarkedPoint i) (1 / 16)) :
              unitInterval × ℂ) := by
      rfl
    _ = framedBingBraidCylinderHomeomorph
        (radialAnnulusCollar (framedBingMarkedPoint i) (1 / 32) (1 / 16)
          framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z) :=
      congrArg framedBingBraidCylinderHomeomorph
        (radialAnnulusHomeomorph_apply_coe (framedBingMarkedPoint i) (1 / 32) (1 / 16)
          framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z)

/-- Helper for Example 63.2: the braided annulus homeomorphism fixes the outer attaching circle
in the bottom face. -/
lemma framedBingLateralAnnulusHomeomorph_apply_outer (i : Fin 3)
    (z : closedRadialAnnulus (framedBingMarkedPoint i) (1 / 32) (1 / 16))
    (hz : dist (z : ℂ) (framedBingMarkedPoint i) = 1 / 16) :
    ((framedBingLateralAnnulusHomeomorph i z : framedBingTubeLateralBoundary i) :
        unitInterval × ℂ) = (0, (z : ℂ)) := by
  -- The radial collar has time zero on the outer circle, and the framed braid fixes that face.
  calc
    ((framedBingLateralAnnulusHomeomorph i z : framedBingTubeLateralBoundary i) :
        unitInterval × ℂ) =
        framedBingBraidCylinderHomeomorph
          (radialAnnulusCollar (framedBingMarkedPoint i) (1 / 32) (1 / 16)
            framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z) :=
      framedBingLateralAnnulusHomeomorph_apply i z
    _ = framedBingBraidCylinderHomeomorph (0, (z : ℂ)) :=
      congrArg framedBingBraidCylinderHomeomorph
        (radialAnnulusCollar_apply_of_dist_eq_outer (framedBingMarkedPoint i)
          framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z hz)
    _ = (0, (z : ℂ)) := framedBingBraidCylinderHomeomorph_apply_zero z

/-- Helper for Example 63.2: the braided annulus homeomorphism reaches the normalized inner
attaching circle in the top face. -/
lemma framedBingLateralAnnulusHomeomorph_apply_inner (i : Fin 3)
    (z : closedRadialAnnulus (framedBingMarkedPoint i) (1 / 32) (1 / 16))
    (hz : dist (z : ℂ) (framedBingMarkedPoint i) = 1 / 32) :
    ((framedBingLateralAnnulusHomeomorph i z : framedBingTubeLateralBoundary i) :
        unitInterval × ℂ) =
      (1, framedBingMarkedPoint i + (2 : ℝ) • ((z : ℂ) - framedBingMarkedPoint i)) := by
  -- Normalize the inner circle to the outer framing circle; the endpoint braid fixes the whole
  -- framing disk, so the normalized point is unchanged at time one.
  have hcollar :
      radialAnnulusCollar (framedBingMarkedPoint i) (1 / 32) (1 / 16)
          framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z =
        (1, framedBingMarkedPoint i + (2 : ℝ) •
          ((z : ℂ) - framedBingMarkedPoint i)) := by
    calc
      radialAnnulusCollar (framedBingMarkedPoint i) (1 / 32) (1 / 16)
          framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z =
          (1, framedBingMarkedPoint i + ((1 / 16 : ℝ) / (1 / 32)) •
            ((z : ℂ) - framedBingMarkedPoint i)) :=
        radialAnnulusCollar_apply_of_dist_eq_inner (framedBingMarkedPoint i)
          framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z hz
      _ = (1, framedBingMarkedPoint i + (2 : ℝ) •
          ((z : ℂ) - framedBingMarkedPoint i)) := by
        norm_num
  have hnormalized :
      framedBingMarkedPoint i + ((1 / 16 : ℝ) / (1 / 32)) •
          ((z : ℂ) - framedBingMarkedPoint i) =
        framedBingMarkedPoint i + (2 : ℝ) •
          ((z : ℂ) - framedBingMarkedPoint i) := by
    norm_num
  have hnormalizedSphere :=
    radialAnnulusProjection_mem_sphere (framedBingMarkedPoint i)
      framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z
  -- On the inner seam the radial denominator is exactly the chosen inner radius.
  rw [hz] at hnormalizedSphere
  have hnormalizedDisk :
      framedBingMarkedPoint i + (2 : ℝ) • ((z : ℂ) - framedBingMarkedPoint i) ∈
        Metric.closedBall (framedBingMarkedPoint i) (1 / 16) := by
    rw [← hnormalized]
    exact Metric.sphere_subset_closedBall hnormalizedSphere
  calc
    ((framedBingLateralAnnulusHomeomorph i z : framedBingTubeLateralBoundary i) :
        unitInterval × ℂ) =
        framedBingBraidCylinderHomeomorph
          (radialAnnulusCollar (framedBingMarkedPoint i) (1 / 32) (1 / 16)
            framedBingCapInnerRadius_pos framedBingCapInnerRadius_lt_outer z) :=
      framedBingLateralAnnulusHomeomorph_apply i z
    _ = framedBingBraidCylinderHomeomorph
        (1, framedBingMarkedPoint i + (2 : ℝ) •
          ((z : ℂ) - framedBingMarkedPoint i)) :=
      congrArg framedBingBraidCylinderHomeomorph hcollar
    _ = (1, framedBingMarkedPoint i + (2 : ℝ) •
        ((z : ℂ) - framedBingMarkedPoint i)) :=
      framedBingBraidCylinderHomeomorph_apply_one_of_mem_framingDisk i hnormalizedDisk

/-- Helper for Example 63.2: the exposed one-stage horn patch is the bottom pair of pants
together with the two outer lateral tube boundaries. -/
def framedBingHornPatch : Set (unitInterval × ℂ) :=
  framedBingBottomPairOfPants ∪ framedBingTubeLateralBoundary 0 ∪
    framedBingTubeLateralBoundary 2

/-- Helper for Example 63.2: the exposed framed horn patch is compact. -/
lemma isCompact_framedBingHornPatch : IsCompact framedBingHornPatch := by
  -- The patch is a finite union of the compact bottom and lateral pieces.
  exact (isCompact_framedBingBottomPairOfPants.union
    (isCompact_framedBingTubeLateralBoundary 0)).union
      (isCompact_framedBingTubeLateralBoundary 2)

/-- Helper for Example 63.2: the exposed framed horn patch is closed in the model
cylinder. -/
lemma isClosed_framedBingHornPatch : IsClosed framedBingHornPatch := by
  -- Compact subsets of the metric model cylinder are closed.
  exact isCompact_framedBingHornPatch.isClosed

/-- Helper for Example 63.2: at every positive mesh, an embedded affine copy of the
framed horn patch has compact image and pairwise disjoint child tubes of smaller diameter. -/
theorem exists_smallFramedBingBlock {ε : ℝ} (hε : 0 < ε) :
    ∃ scale > 0,
      Topology.IsEmbedding (framedBingAffineCompression scale) ∧
        IsCompact (framedBingAffineCompression scale '' framedBingHornPatch) ∧
          Disjoint
            (framedBingAffineCompression scale '' framedBingTube 0)
            (framedBingAffineCompression scale '' framedBingTube 2) ∧
            ∀ i : Fin 3,
              Metric.diam
                (framedBingAffineCompression scale '' framedBingTube i) < ε := by
  -- Choose the quantitative scale first, then transport compactness and child separation
  -- through the resulting embedding.
  obtain ⟨scale, hscale, hmesh⟩ :=
    exists_framedBingAffineCompression_tube_diam_lt hε
  have hscaleNe : scale ≠ 0 := ne_of_gt hscale
  have hinjective : Function.Injective (framedBingAffineCompression scale) :=
    framedBingAffineCompression_injective hscaleNe
  refine ⟨scale, hscale, framedBingAffineCompression_isEmbedding hscaleNe, ?_, ?_, hmesh⟩
  · exact isCompact_framedBingHornPatch.image
      (continuous_framedBingAffineCompression scale)
  · exact Set.disjoint_image_of_injective hinjective
      framedBingBraidCylinderHomeomorph_seedImages_disjoint.2.1

/-- Helper for Example 63.2: the two top boundary components of the exposed horn patch
are exactly the two outer child circles. -/
lemma framedBingHornPatch_topSlice (z : ℂ) :
    (1, z) ∈ framedBingHornPatch ↔
      z ∈ Metric.sphere (framedBingMarkedPoint 0) (1 / 16) ∨
        z ∈ Metric.sphere (framedBingMarkedPoint 2) (1 / 16) := by
  -- The bottom piece has no point on the top face, and the lateral slice equations finish.
  rw [framedBingHornPatch, Set.mem_union, Set.mem_union]
  simp only [framedBingBottomPairOfPants, Set.mem_prod, Set.mem_singleton_iff,
    one_ne_zero, false_and, false_or,
    (framedBingTubeLateralBoundary_boundarySlices 0 z).2,
    (framedBingTubeLateralBoundary_boundarySlices 2 z).2]

/-- Helper for Example 63.2: the punctured plane whose deleted points are the two outer
marked fibers of the framed Bing block. -/
abbrev FramedBingPuncturedPlane :=
  TwoPuncturePlane (framedBingMarkedPoint 0) (framedBingMarkedPoint 2)

/-- Helper for Example 63.2: the outer marked fibers are the two punctures of the
normalized doubly punctured plane. -/
lemma framedBingOuterMarkedPoints_eq_normalized :
    framedBingMarkedPoint 0 = DoublyPuncturedPlane.leftPuncture ∧
      framedBingMarkedPoint 2 = DoublyPuncturedPlane.rightPuncture := by
  -- Route correction: a direct implementation import exposes the two normalized coordinates.
  constructor
  · simp only [framedBingMarkedPoint, Matrix.cons_val_zero,
      DoublyPuncturedPlane.leftPuncture]
    norm_num
  · simp only [framedBingMarkedPoint, Matrix.cons_val_two,
      DoublyPuncturedPlane.rightPuncture]
    rfl

/-- Helper for Example 63.2: inverse framed-cylinder projection of a point outside the two
child tubes avoids both outer marked fibers. -/
lemma framedBingProjection_avoidsPunctures
    (p : {q : unitInterval × ℂ // q ∈ framedBingChildObstacleᶜ}) :
    (framedBingBraidCylinderHomeomorph.symm p).2 ≠
        framedBingMarkedPoint 0 ∧
      (framedBingBraidCylinderHomeomorph.symm p).2 ≠
        framedBingMarkedPoint 2 := by
  -- Route correction: the normalized puncture coordinates are opaque outside their owner
  -- module, so work first in the punctured plane at the actual marked fibers.
  -- If an inverse projection hit a puncture, its inverse-cylinder point would lie in the
  -- corresponding seed cylinder and the original point would lie in a forbidden child tube.
  constructor
  · intro hleft
    apply p.property
    apply Or.inl
    refine ⟨framedBingBraidCylinderHomeomorph.symm p, ?_, ?_⟩
    · refine ⟨Set.mem_univ _, ?_⟩
      rw [Metric.mem_closedBall, hleft]
      rw [dist_self]
      norm_num
    · exact framedBingBraidCylinderHomeomorph.apply_symm_apply p
  · intro hright
    apply p.property
    apply Or.inr
    refine ⟨framedBingBraidCylinderHomeomorph.symm p, ?_, ?_⟩
    · refine ⟨Set.mem_univ _, ?_⟩
      rw [Metric.mem_closedBall, hright]
      rw [dist_self]
      norm_num
    · exact framedBingBraidCylinderHomeomorph.apply_symm_apply p

/-- Helper for Example 63.2: the inverse framed-cylinder spatial coordinate defines a point
of the marked-fiber punctured plane. -/
noncomputable def framedBingComplementProjectionPoint
    (p : {q : unitInterval × ℂ // q ∈ framedBingChildObstacleᶜ}) :
    FramedBingPuncturedPlane :=
  ⟨(framedBingBraidCylinderHomeomorph.symm p).2,
    framedBingProjection_avoidsPunctures p⟩

/-- Helper for Example 63.2: inverse-cylinder spatial projection is continuous on the child
complement. -/
lemma continuous_framedBingComplementProjectionPoint :
    Continuous framedBingComplementProjectionPoint := by
  -- The ambient formula is the second coordinate of the continuous inverse homeomorphism.
  exact Continuous.subtype_mk
    (continuous_snd.comp
      (framedBingBraidCylinderHomeomorph.symm.continuous.comp continuous_subtype_val)) _

/-- Helper for Example 63.2: the canonical map from the local child complement to the
marked-fiber punctured plane. -/
noncomputable def framedBingComplementProjection :
    C({q : unitInterval × ℂ // q ∈ framedBingChildObstacleᶜ},
      FramedBingPuncturedPlane) :=
  ⟨framedBingComplementProjectionPoint,
    continuous_framedBingComplementProjectionPoint⟩

/-- Helper for Example 63.2: the middle framed tube is disjoint from the two child tubes. -/
lemma framedBingChildObstacle_disjoint_middle :
    Disjoint framedBingChildObstacle (framedBingTube 1) := by
  -- Repackage the already proved pairwise separation under the named tube interface.
  rcases framedBingBraidCylinderHomeomorph_seedImages_disjoint with ⟨h01, _, h12⟩
  rw [framedBingChildObstacle, Set.disjoint_union_left]
  exact ⟨h01, h12.symm⟩

/-- Helper for Example 63.2: the origin belongs to the framing disk of the middle marked
fiber. -/
lemma zero_mem_framedBingMiddleDisk :
    (0 : ℂ) ∈ Metric.closedBall (framedBingMarkedPoint 1) (1 / 16) := by
  -- The middle marked point is the origin itself.
  simp only [framedBingMarkedPoint, Matrix.cons_val_one, Matrix.cons_val_zero,
    Metric.mem_closedBall, dist_self]
  norm_num

/-- Helper for Example 63.2: the middle seed core, carried through the framed cylinder,
joins the two fixed boundary origins. -/
noncomputable def framedBingMiddleCore :
    Path ((0 : unitInterval), (0 : ℂ)) ((1 : unitInterval), (0 : ℂ)) :=
  (((unitInterval.path01.prod (Path.refl (0 : ℂ))).map
      framedBingBraidCylinderHomeomorph.continuous).cast
    (framedBingBraidCylinderHomeomorph_apply_zero 0).symm
    (framedBingBraidCylinderHomeomorph_apply_one_of_mem_framingDisk
      1 zero_mem_framedBingMiddleDisk).symm)

/-- Helper for Example 63.2: evaluation of the middle core is the cylinder image of its
seed core. -/
lemma framedBingMiddleCore_apply (t : unitInterval) :
    framedBingMiddleCore t = framedBingBraidCylinderHomeomorph (t, 0) := by
  -- Path mapping and endpoint casting do not alter pointwise values.
  rfl

/-- Helper for Example 63.2: every point of the middle core lies in the middle framed tube. -/
lemma framedBingMiddleCore_mem_middleTube (t : unitInterval) :
    framedBingMiddleCore t ∈ framedBingTube 1 := by
  -- Exhibit the corresponding point of the middle seed cylinder.
  refine ⟨(t, 0), ⟨Set.mem_univ _, zero_mem_framedBingMiddleDisk⟩, ?_⟩
  exact framedBingMiddleCore_apply t

/-- Helper for Example 63.2: the middle core avoids the two-child obstacle. -/
lemma framedBingMiddleCore_avoids_children (t : unitInterval) :
    framedBingMiddleCore t ∈ framedBingChildObstacleᶜ := by
  -- Disjointness converts membership in the middle tube into obstacle avoidance.
  intro hchild
  exact Set.disjoint_left.mp framedBingChildObstacle_disjoint_middle
    hchild (framedBingMiddleCore_mem_middleTube t)

/-- Helper for Example 63.2: a point whose spatial norm exceeds the support radius cannot
belong to any framed Bing tube. -/
lemma not_mem_framedBingTube_of_threeFour_lt_norm (i : Fin 3)
    (p : unitInterval × ℂ) (hp : (3 / 4 : ℝ) < ‖p.2‖) :
    p ∉ framedBingTube i := by
  -- The uniform tube-containment lemma would give the opposite norm bound.
  intro htube
  have hcylinder := framedBingTube_subset_closedBall i htube
  have hnorm : ‖p.2‖ ≤ (3 / 4 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hcylinder.2
  linarith

/-- Helper for Example 63.2: points on the imaginary axis avoid both outer framing disks. -/
lemma imaginaryAxis_not_mem_outerFramingDisks {z : ℂ} (hz : z.re = 0) :
    z ∉ Metric.closedBall (framedBingMarkedPoint 0) (1 / 16) ∧
      z ∉ Metric.closedBall (framedBingMarkedPoint 2) (1 / 16) := by
  -- Real parts alone give distance at least `1 / 2` from either outer center.
  constructor
  · intro hleft
    have hnorm : ‖z - framedBingMarkedPoint 0‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, Complex.dist_eq] using hleft
    have hlower : (1 / 2 : ℝ) ≤ ‖z - framedBingMarkedPoint 0‖ := by
      calc
        (1 / 2 : ℝ) = |(z - framedBingMarkedPoint 0).re| := by
          simp [framedBingMarkedPoint, hz]
        _ ≤ ‖z - framedBingMarkedPoint 0‖ := Complex.abs_re_le_norm _
    linarith
  · intro hright
    have hnorm : ‖z - framedBingMarkedPoint 2‖ ≤ (1 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, Complex.dist_eq] using hright
    have hlower : (1 / 2 : ℝ) ≤ ‖z - framedBingMarkedPoint 2‖ := by
      calc
        (1 / 2 : ℝ) = |(z - framedBingMarkedPoint 2).re| := by
          simp [framedBingMarkedPoint, hz]
        _ ≤ ‖z - framedBingMarkedPoint 2‖ := Complex.abs_re_le_norm _
    linarith

/-- Helper for Example 63.2: every point of the planar theta carrier avoids both outer
framing disks. -/
lemma planarTheta_not_mem_outerFramingDisks (z : PlanarTheta) :
    (z : ℂ) ∉ Metric.closedBall (framedBingMarkedPoint 0) (1 / 16) ∧
      (z : ℂ) ∉ Metric.closedBall (framedBingMarkedPoint 2) (1 / 16) := by
  -- The circle branch has norm one, whereas either framing disk lies inside radius `9 / 16`.
  rcases (PlanarTheta.mem_iff (z : ℂ)).mp z.property with hcircle | himaginary
  · constructor
    · intro hleft
      have hbound := norm_sub_le_radius_add_norm_sub_of_mem_closedBall
        (z := (z : ℂ)) (c := framedBingMarkedPoint 0) (a := 0)
        (r := (1 / 16 : ℝ)) hleft
      rw [sub_zero, hcircle] at hbound
      norm_num [framedBingMarkedPoint, Complex.norm_real] at hbound
    · intro hright
      have hbound := norm_sub_le_radius_add_norm_sub_of_mem_closedBall
        (z := (z : ℂ)) (c := framedBingMarkedPoint 2) (a := 0)
        (r := (1 / 16 : ℝ)) hright
      rw [sub_zero, hcircle] at hbound
      simp only [framedBingMarkedPoint, Matrix.cons_val_two] at hbound
      norm_num [Complex.norm_real] at hbound
  · exact imaginaryAxis_not_mem_outerFramingDisks himaginary.1

/-- Helper for Example 63.2: a subtype cut out inside a containing subtype is
homeomorphic to the same set viewed directly in the ambient space. -/
private def nestedSubtypeSetHomeomorph
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Subtype.ext rfl
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk fun x ↦ hSP x.2).subtype_mk fun x ↦ x.2 }

/-- Helper for Example 63.2: every point of the planar theta carrier avoids the two
normalized punctures. -/
private lemma planarTheta_avoidsNormalizedPunctures :
    PlanarTheta.carrier ⊆
      {z : ℂ | z ≠ DoublyPuncturedPlane.leftPuncture ∧
        z ≠ DoublyPuncturedPlane.rightPuncture} := by
  -- The two real half-points lie neither on the unit circle nor on the vertical diameter.
  intro z hz
  constructor
  · intro hleft
    subst z
    rcases (PlanarTheta.mem_iff _).mp hz with hcircle | hdiameter
    · norm_num [DoublyPuncturedPlane.leftPuncture, Complex.norm_def] at hcircle
    · norm_num [DoublyPuncturedPlane.leftPuncture] at hdiameter
  · intro hright
    subst z
    rcases (PlanarTheta.mem_iff _).mp hz with hcircle | hdiameter
    · norm_num [DoublyPuncturedPlane.rightPuncture, Complex.norm_def] at hcircle
    · norm_num [DoublyPuncturedPlane.rightPuncture] at hdiameter

/-- Helper for Example 63.2: the nested planar-theta retract is canonically homeomorphic
to the direct planar theta carrier without changing its complex coordinate. -/
lemma exists_planarThetaNestedHomeomorph_coe :
    ∃ e : PlanarTheta.inDoublyPuncturedPlane ≃ₜ PlanarTheta,
      ∀ z, ((e z : PlanarTheta) : ℂ) = ((z : DoublyPuncturedPlane) : ℂ) := by
  -- Identify the nested carrier with the direct carrier using its ambient complex coordinate.
  let e := nestedSubtypeSetHomeomorph
    {z : ℂ | z ≠ DoublyPuncturedPlane.leftPuncture ∧
      z ≠ DoublyPuncturedPlane.rightPuncture}
    PlanarTheta.carrier planarTheta_avoidsNormalizedPunctures
  refine ⟨e, ?_⟩
  intro z
  rfl

/-- Helper for Example 63.2: the standard child-complement contains a split copy of
`PlanarTheta`. -/
lemma exists_framedBingComplementSplit :
    ∃ s : C(PlanarTheta,
        {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}),
      ∃ q : C({p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ},
        PlanarTheta),
        ∀ z, q (s z) = z := by
  -- Route correction: use the initial face as a section and the deformation retraction as
  -- a left inverse, avoiding an explicit computation of the six-letter parent meridian.
  obtain ⟨e, hecoe⟩ := exists_planarThetaNestedHomeomorph_coe
  have hsectionMem (z : PlanarTheta) :
      ((0 : unitInterval), (z : ℂ)) ∈ framedBingChildObstacleᶜ := by
    have hz := planarTheta_not_mem_outerFramingDisks z
    intro hchild
    rw [framedBingChildObstacle, Set.mem_union] at hchild
    rcases hchild with hleft | hright
    · exact hz.1 ((framedBingTube_boundarySlices 0 (z : ℂ)).1.mp hleft)
    · exact hz.2 ((framedBingTube_boundarySlices 2 (z : ℂ)).1.mp hright)
  have hsectionContinuous : Continuous
      (fun z : PlanarTheta ↦
        (⟨((0 : unitInterval), (z : ℂ)), hsectionMem z⟩ :
          {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ})) := by
    -- The ambient initial-face inclusion is a product of a constant map and subtype coercion.
    exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  let s : C(PlanarTheta,
      {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}) :=
    ⟨fun z ↦ ⟨((0 : unitInterval), (z : ℂ)), hsectionMem z⟩,
      hsectionContinuous⟩
  have hnormalizedMem (z : FramedBingPuncturedPlane) :
      (z : ℂ) ≠ DoublyPuncturedPlane.leftPuncture ∧
        (z : ℂ) ≠ DoublyPuncturedPlane.rightPuncture := by
    -- Transport the two puncture inequalities through the paired coordinate bridge.
    rw [← framedBingOuterMarkedPoints_eq_normalized.1,
      ← framedBingOuterMarkedPoints_eq_normalized.2]
    exact z.property
  have hnormalizedContinuous : Continuous
      (fun z : FramedBingPuncturedPlane ↦
        (⟨(z : ℂ), hnormalizedMem z⟩ : DoublyPuncturedPlane)) := by
    exact continuous_subtype_val.subtype_mk _
  let normalizedProjection : C(FramedBingPuncturedPlane, DoublyPuncturedPlane) :=
    ⟨fun z ↦ ⟨(z : ℂ), hnormalizedMem z⟩, hnormalizedContinuous⟩
  obtain ⟨r, _⟩ :=
    (Set.isDeformationRetract_iff PlanarTheta.inDoublyPuncturedPlane).mp
      planarTheta_isDeformationRetract
  let eMap : C(PlanarTheta.inDoublyPuncturedPlane, PlanarTheta) :=
    ⟨e, e.continuous⟩
  let q : C({p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ},
      PlanarTheta) :=
    eMap.comp
      (r.toContinuousMap.comp
        (normalizedProjection.comp framedBingComplementProjection))
  refine ⟨s, q, ?_⟩
  intro z
  have heSymmCoe :
      (((e.symm z : PlanarTheta.inDoublyPuncturedPlane) :
          DoublyPuncturedPlane) : ℂ) = (z : ℂ) := by
    calc
      (((e.symm z : PlanarTheta.inDoublyPuncturedPlane) :
          DoublyPuncturedPlane) : ℂ) = ((e (e.symm z) : PlanarTheta) : ℂ) :=
        (hecoe (e.symm z)).symm
      _ = (z : ℂ) := congrArg Subtype.val (e.apply_symm_apply z)
  -- Initial-face fixation identifies the normalized projection with theta inclusion.
  have hprojection :
      normalizedProjection (framedBingComplementProjection (s z)) =
        (e.symm z : PlanarTheta.inDoublyPuncturedPlane) := by
    apply Subtype.ext
    have hfixed := framedBingBraidCylinderHomeomorph_apply_zero (z : ℂ)
    calc
      ((normalizedProjection (framedBingComplementProjection (s z)) :
          DoublyPuncturedPlane) : ℂ) =
          (framedBingBraidCylinderHomeomorph.symm
            ((0 : unitInterval), (z : ℂ))).2 := rfl
      _ = (framedBingBraidCylinderHomeomorph.symm
            (framedBingBraidCylinderHomeomorph
              ((0 : unitInterval), (z : ℂ)))).2 :=
        congrArg Prod.snd
          (congrArg framedBingBraidCylinderHomeomorph.symm hfixed.symm)
      _ = (z : ℂ) := congrArg Prod.snd
        (framedBingBraidCylinderHomeomorph.symm_apply_apply
          ((0 : unitInterval), (z : ℂ)))
      _ = (((e.symm z : PlanarTheta.inDoublyPuncturedPlane) :
          DoublyPuncturedPlane) : ℂ) := heSymmCoe.symm
  have hretract : r.toContinuousMap
      ((e.symm z : PlanarTheta.inDoublyPuncturedPlane) : DoublyPuncturedPlane) =
        e.symm z := by
    exact r.leftInverse (e.symm z)
  -- The retraction fixes nested theta and the coordinate homeomorphism cancels its inverse.
  change eMap (r.toContinuousMap
    (normalizedProjection (framedBingComplementProjection (s z)))) = z
  rw [hprojection, hretract]
  exact e.apply_symm_apply z

/-- Helper for Example 63.2: the full one-stage obstacle consists of the exposed horn
patch together with its two child tubes. -/
def framedBingRelativeObstacle : Set (unitInterval × ℂ) :=
  framedBingHornPatch ∪ framedBingChildObstacle

/-- Helper for Example 63.2: the complete one-stage relative obstacle is compact. -/
lemma isCompact_framedBingRelativeObstacle :
    IsCompact framedBingRelativeObstacle := by
  -- Both the exposed patch and the two closed child tubes are compact.
  exact isCompact_framedBingHornPatch.union isCompact_framedBingChildObstacle

/-- Helper for Example 63.2: the complete one-stage relative obstacle is closed. -/
lemma isClosed_framedBingRelativeObstacle :
    IsClosed framedBingRelativeObstacle := by
  -- Compactness closes the relative obstacle in the metric model cylinder.
  exact isCompact_framedBingRelativeObstacle.isClosed

/-- Helper for Example 63.2: the midpoint belongs to the unit interval. -/
lemma framedBingMidpoint_mem_unitInterval :
    (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Both endpoint inequalities are immediate numerical facts.
  norm_num

/-- Helper for Example 63.2: the distinguished interior time used for the relative
complement section. -/
noncomputable def framedBingMidpoint : unitInterval :=
  ⟨1 / 2, framedBingMidpoint_mem_unitInterval⟩

/-- Helper for Example 63.2: the distinguished midpoint is not the initial time. -/
lemma framedBingMidpoint_ne_zero : framedBingMidpoint ≠ 0 := by
  -- Equality in the interval would force the underlying real midpoint to vanish.
  intro hzero
  have hvalue := congrArg Subtype.val hzero
  norm_num [framedBingMidpoint] at hvalue

/-- Helper for Example 63.2: every framed slice of the planar theta carrier avoids both
child tubes. -/
lemma framedBingThetaSlice_avoids_children (t : unitInterval) (z : PlanarTheta) :
    framedBingBraidCylinderHomeomorph (t, (z : ℂ)) ∈
      framedBingChildObstacleᶜ := by
  -- Pull any alleged tube membership back through the cylinder homeomorphism.
  have hz := planarTheta_not_mem_outerFramingDisks z
  intro hchild
  rw [framedBingChildObstacle, Set.mem_union] at hchild
  rcases hchild with hleft | hright
  · rw [framedBingTube] at hleft
    obtain ⟨p, hp, himage⟩ := hleft
    have hpEq : p = (t, (z : ℂ)) :=
      framedBingBraidCylinderHomeomorph.injective himage
    rw [hpEq] at hp
    exact hz.1 hp.2
  · rw [framedBingTube] at hright
    obtain ⟨p, hp, himage⟩ := hright
    have hpEq : p = (t, (z : ℂ)) :=
      framedBingBraidCylinderHomeomorph.injective himage
    rw [hpEq] at hp
    exact hz.2 hp.2

/-- Helper for Example 63.2: the framed midpoint copy of `PlanarTheta` avoids the full
relative obstacle, including the exposed patch. -/
lemma framedBingMidpointThetaSlice_mem_relativeComplement (z : PlanarTheta) :
    framedBingBraidCylinderHomeomorph (framedBingMidpoint, (z : ℂ)) ∈
      framedBingRelativeObstacleᶜ := by
  -- Child avoidance also excludes the lateral pieces; the interior time excludes the bottom.
  have hchildren := framedBingThetaSlice_avoids_children framedBingMidpoint z
  intro hrelative
  rw [framedBingRelativeObstacle, Set.mem_union] at hrelative
  rcases hrelative with hpatch | hchild
  · rw [framedBingHornPatch, Set.mem_union, Set.mem_union] at hpatch
    rcases hpatch with (hbottom | hleftLateral) | hrightLateral
    · apply framedBingMidpoint_ne_zero
      have htime := hbottom.1
      simpa only [framedBingBraidCylinderHomeomorph_apply,
        Set.mem_singleton_iff] using htime
    · exact hchildren (Or.inl
        (framedBingTubeLateralBoundary_subset_tube 0 hleftLateral))
    · exact hchildren (Or.inr
        (framedBingTubeLateralBoundary_subset_tube 2 hrightLateral))
  · exact hchildren hchild

/-- Helper for Example 63.2: the full relative obstacle complement contains a split copy
of `PlanarTheta`. -/
lemma exists_framedBingRelativeComplementSplit :
    ∃ s : C(PlanarTheta,
        {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ}),
      ∃ q : C({p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ},
        PlanarTheta),
        ∀ z, q (s z) = z := by
  -- Use the interior framed slice as the section and the punctured-plane retraction as detector.
  obtain ⟨e, hecoe⟩ := exists_planarThetaNestedHomeomorph_coe
  have hsectionContinuous : Continuous
      (fun z : PlanarTheta ↦
        (⟨framedBingBraidCylinderHomeomorph (framedBingMidpoint, (z : ℂ)),
          framedBingMidpointThetaSlice_mem_relativeComplement z⟩ :
          {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ})) := by
    exact (framedBingBraidCylinderHomeomorph.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _
  let s : C(PlanarTheta,
      {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ}) :=
    ⟨fun z ↦ ⟨framedBingBraidCylinderHomeomorph
        (framedBingMidpoint, (z : ℂ)),
      framedBingMidpointThetaSlice_mem_relativeComplement z⟩,
      hsectionContinuous⟩
  have hrelativeAvoidsChildren
      (p : {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ}) :
      (p : unitInterval × ℂ) ∈ framedBingChildObstacleᶜ := by
    -- Avoiding the union in particular avoids its child-obstacle summand.
    intro hchild
    exact p.property (Or.inr hchild)
  have hinclusionContinuous : Continuous
      (fun p : {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ} ↦
        (⟨p, hrelativeAvoidsChildren p⟩ :
          {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ})) := by
    exact continuous_subtype_val.subtype_mk _
  let inclusion : C(
      {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ},
      {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}) :=
    ⟨fun p ↦ ⟨p, hrelativeAvoidsChildren p⟩, hinclusionContinuous⟩
  have hnormalizedMem (z : FramedBingPuncturedPlane) :
      (z : ℂ) ≠ DoublyPuncturedPlane.leftPuncture ∧
        (z : ℂ) ≠ DoublyPuncturedPlane.rightPuncture := by
    -- Transport the marked-fiber inequalities to the normalized puncture coordinates.
    rw [← framedBingOuterMarkedPoints_eq_normalized.1,
      ← framedBingOuterMarkedPoints_eq_normalized.2]
    exact z.property
  have hnormalizedContinuous : Continuous
      (fun z : FramedBingPuncturedPlane ↦
        (⟨(z : ℂ), hnormalizedMem z⟩ : DoublyPuncturedPlane)) := by
    exact continuous_subtype_val.subtype_mk _
  let normalizedProjection : C(FramedBingPuncturedPlane, DoublyPuncturedPlane) :=
    ⟨fun z ↦ ⟨(z : ℂ), hnormalizedMem z⟩, hnormalizedContinuous⟩
  obtain ⟨r, _⟩ :=
    (Set.isDeformationRetract_iff PlanarTheta.inDoublyPuncturedPlane).mp
      planarTheta_isDeformationRetract
  let eMap : C(PlanarTheta.inDoublyPuncturedPlane, PlanarTheta) :=
    ⟨e, e.continuous⟩
  let q : C({p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ},
      PlanarTheta) :=
    eMap.comp
      (r.toContinuousMap.comp
        (normalizedProjection.comp
          (framedBingComplementProjection.comp inclusion)))
  refine ⟨s, q, ?_⟩
  intro z
  have heSymmCoe :
      (((e.symm z : PlanarTheta.inDoublyPuncturedPlane) :
          DoublyPuncturedPlane) : ℂ) = (z : ℂ) := by
    calc
      (((e.symm z : PlanarTheta.inDoublyPuncturedPlane) :
          DoublyPuncturedPlane) : ℂ) = ((e (e.symm z) : PlanarTheta) : ℂ) :=
        (hecoe (e.symm z)).symm
      _ = (z : ℂ) := congrArg Subtype.val (e.apply_symm_apply z)
  -- Inverse cylinder projection sends the framed midpoint section back to `(1/2, z)`.
  have hprojection :
      normalizedProjection
          (framedBingComplementProjection (inclusion (s z))) =
        (e.symm z : PlanarTheta.inDoublyPuncturedPlane) := by
    apply Subtype.ext
    calc
      ((normalizedProjection
          (framedBingComplementProjection (inclusion (s z))) :
          DoublyPuncturedPlane) : ℂ) =
          (framedBingBraidCylinderHomeomorph.symm
            (framedBingBraidCylinderHomeomorph
              (framedBingMidpoint, (z : ℂ)))).2 := rfl
      _ = (z : ℂ) := congrArg Prod.snd
        (framedBingBraidCylinderHomeomorph.symm_apply_apply
          (framedBingMidpoint, (z : ℂ)))
      _ = (((e.symm z : PlanarTheta.inDoublyPuncturedPlane) :
          DoublyPuncturedPlane) : ℂ) := heSymmCoe.symm
  have hretract : r.toContinuousMap
      ((e.symm z : PlanarTheta.inDoublyPuncturedPlane) : DoublyPuncturedPlane) =
        e.symm z := by
    exact r.leftInverse (e.symm z)
  -- The retraction fixes nested theta and the coordinate homeomorphism cancels its inverse.
  change eMap (r.toContinuousMap
    (normalizedProjection
      (framedBingComplementProjection (inclusion (s z))))) = z
  rw [hprojection, hretract]
  exact e.apply_symm_apply z

/-- Helper for Example 63.2: the terminal-face segment from the origin to `I`. -/
noncomputable def framedBingTopReturn :
    Path ((1 : unitInterval), (0 : ℂ)) ((1 : unitInterval), Complex.I) :=
  (Path.refl (1 : unitInterval)).prod (Path.segment 0 Complex.I)

/-- Helper for Example 63.2: the outer-support segment returning from time one to time zero. -/
noncomputable def framedBingSupportReturn :
    Path ((1 : unitInterval), Complex.I) ((0 : unitInterval), Complex.I) :=
  unitInterval.path01.symm.prod (Path.refl Complex.I)

/-- Helper for Example 63.2: the initial-face segment from `I` back to the origin. -/
noncomputable def framedBingBottomReturn :
    Path ((0 : unitInterval), Complex.I) ((0 : unitInterval), (0 : ℂ)) :=
  (Path.refl (0 : unitInterval)).prod (Path.segment Complex.I 0)

/-- Helper for Example 63.2: the three outer segments forming the return half of the parent
meridian. -/
noncomputable def framedBingOuterReturn :
    Path ((1 : unitInterval), (0 : ℂ)) ((0 : unitInterval), (0 : ℂ)) :=
  framedBingTopReturn.trans (framedBingSupportReturn.trans framedBingBottomReturn)

/-- Helper for Example 63.2: the terminal-face return segment avoids both children. -/
lemma framedBingTopReturn_avoids_children (t : unitInterval) :
    framedBingTopReturn t ∈ framedBingChildObstacleᶜ := by
  -- Its spatial coordinate is imaginary, so the exact terminal-slice formulas exclude it.
  have hzRe : ((Path.segment (0 : ℂ) Complex.I) t).re = 0 := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  have houtside := imaginaryAxis_not_mem_outerFramingDisks hzRe
  intro hchild
  rw [framedBingChildObstacle, Set.mem_union] at hchild
  rcases hchild with hleft | hright
  · apply houtside.1
    apply (framedBingTube_boundarySlices 0 _).2.mp
    exact hleft
  · apply houtside.2
    apply (framedBingTube_boundarySlices 2 _).2.mp
    exact hright

/-- Helper for Example 63.2: the outer-support return segment avoids both children. -/
lemma framedBingSupportReturn_avoids_children (t : unitInterval) :
    framedBingSupportReturn t ∈ framedBingChildObstacleᶜ := by
  -- Its spatial coordinate has norm one, beyond the uniform tube support radius.
  have hnorm : ‖(framedBingSupportReturn t).2‖ = (1 : ℝ) := by
    simp [framedBingSupportReturn]
  have hstrict : (3 / 4 : ℝ) < ‖(framedBingSupportReturn t).2‖ := by
    rw [hnorm]
    norm_num
  intro hchild
  rw [framedBingChildObstacle, Set.mem_union] at hchild
  rcases hchild with hleft | hright
  · exact not_mem_framedBingTube_of_threeFour_lt_norm 0 _ hstrict hleft
  · exact not_mem_framedBingTube_of_threeFour_lt_norm 2 _ hstrict hright

/-- Helper for Example 63.2: the initial-face return segment avoids both children. -/
lemma framedBingBottomReturn_avoids_children (t : unitInterval) :
    framedBingBottomReturn t ∈ framedBingChildObstacleᶜ := by
  -- Reversing the imaginary segment preserves its zero real part; use the initial slice.
  have hzRe : ((Path.segment Complex.I (0 : ℂ)) t).re = 0 := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  have houtside := imaginaryAxis_not_mem_outerFramingDisks hzRe
  intro hchild
  rw [framedBingChildObstacle, Set.mem_union] at hchild
  rcases hchild with hleft | hright
  · apply houtside.1
    apply (framedBingTube_boundarySlices 0 _).1.mp
    exact hleft
  · apply houtside.2
    apply (framedBingTube_boundarySlices 2 _).1.mp
    exact hright

/-- Helper for Example 63.2: the entire three-segment outer return avoids the child
obstacle. -/
lemma framedBingOuterReturn_avoids_children (t : unitInterval) :
    framedBingOuterReturn t ∈ framedBingChildObstacleᶜ := by
  -- The range of a concatenation is the union of the ranges of its pieces.
  have htop : Set.range framedBingTopReturn ⊆ framedBingChildObstacleᶜ := by
    rintro _ ⟨u, rfl⟩
    exact framedBingTopReturn_avoids_children u
  have hsupport : Set.range framedBingSupportReturn ⊆ framedBingChildObstacleᶜ := by
    rintro _ ⟨u, rfl⟩
    exact framedBingSupportReturn_avoids_children u
  have hbottom : Set.range framedBingBottomReturn ⊆ framedBingChildObstacleᶜ := by
    rintro _ ⟨u, rfl⟩
    exact framedBingBottomReturn_avoids_children u
  have hrange : Set.range framedBingOuterReturn ⊆ framedBingChildObstacleᶜ := by
    rw [framedBingOuterReturn, Path.trans_range, Path.trans_range]
    exact Set.union_subset htop (Set.union_subset hsupport hbottom)
  exact hrange ⟨t, rfl⟩

/-- Helper for Example 63.2: the ambient parent meridian follows the middle core and then
returns through the outer support region. -/
noncomputable def framedBingParentMeridianAmbient :
    Path ((0 : unitInterval), (0 : ℂ)) ((0 : unitInterval), (0 : ℂ)) :=
  framedBingMiddleCore.trans framedBingOuterReturn

/-- Helper for Example 63.2: the ambient parent meridian avoids the two child tubes. -/
lemma framedBingParentMeridianAmbient_avoids_children (t : unitInterval) :
    framedBingParentMeridianAmbient t ∈ framedBingChildObstacleᶜ := by
  -- Both halves avoid the obstacle, so their concatenation does as well.
  have hcore : Set.range framedBingMiddleCore ⊆ framedBingChildObstacleᶜ := by
    rintro _ ⟨u, rfl⟩
    exact framedBingMiddleCore_avoids_children u
  have hreturn : Set.range framedBingOuterReturn ⊆ framedBingChildObstacleᶜ := by
    rintro _ ⟨u, rfl⟩
    exact framedBingOuterReturn_avoids_children u
  have hrange : Set.range framedBingParentMeridianAmbient ⊆
      framedBingChildObstacleᶜ := by
    rw [framedBingParentMeridianAmbient, Path.trans_range]
    exact Set.union_subset hcore hreturn
  exact hrange ⟨t, rfl⟩

/-- Helper for Example 63.2: the common meridian basepoint lies in the child-obstacle
complement. -/
lemma framedBingParentBase_mem :
    ((0 : unitInterval), (0 : ℂ)) ∈ framedBingChildObstacleᶜ := by
  -- Evaluate the already certified ambient avoidance at the loop endpoint.
  simpa using framedBingParentMeridianAmbient_avoids_children 0

/-- Helper for Example 63.2: the parent meridian's based point in the child-obstacle
complement. -/
def framedBingParentBase : {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ} :=
  ⟨((0 : unitInterval), (0 : ℂ)), framedBingParentBase_mem⟩

/-- Helper for Example 63.2: the obstacle-complement lift of the ambient meridian is
continuous. -/
lemma continuous_framedBingParentMeridianLift :
    Continuous (fun t ↦
      (⟨framedBingParentMeridianAmbient t,
        framedBingParentMeridianAmbient_avoids_children t⟩ :
        {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ})) := by
  -- Continuity into a subtype is inherited from the ambient path.
  exact framedBingParentMeridianAmbient.continuous.subtype_mk _

/-- Helper for Example 63.2: the lifted meridian begins at its named complement basepoint. -/
lemma framedBingParentMeridianLift_zero :
    (⟨framedBingParentMeridianAmbient 0,
      framedBingParentMeridianAmbient_avoids_children 0⟩ :
      {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}) =
        framedBingParentBase := by
  -- Subtype extensionality reduces the endpoint to the ambient path source law.
  apply Subtype.ext
  exact framedBingParentMeridianAmbient.source

/-- Helper for Example 63.2: the lifted meridian ends at its named complement basepoint. -/
lemma framedBingParentMeridianLift_one :
    (⟨framedBingParentMeridianAmbient 1,
      framedBingParentMeridianAmbient_avoids_children 1⟩ :
      {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}) =
        framedBingParentBase := by
  -- Subtype extensionality reduces the endpoint to the ambient path target law.
  apply Subtype.ext
  exact framedBingParentMeridianAmbient.target

/-- Helper for Example 63.2: the explicit parent meridian as a based path in the complement
of the two child tubes. -/
noncomputable def framedBingParentMeridian :
    Path framedBingParentBase framedBingParentBase :=
  {
    toFun := fun t ↦
      ⟨framedBingParentMeridianAmbient t,
        framedBingParentMeridianAmbient_avoids_children t⟩
    continuous_toFun := continuous_framedBingParentMeridianLift
    source' := framedBingParentMeridianLift_zero
    target' := framedBingParentMeridianLift_one
  }

/-- Helper for Example 63.2: forgetting the complement proof recovers the ambient parent
meridian pointwise. -/
lemma framedBingParentMeridian_coe (t : unitInterval) :
    (framedBingParentMeridian t : unitInterval × ℂ) =
      framedBingParentMeridianAmbient t := by
  -- The complement-valued path was defined by direct codomain restriction.
  rfl

/-- Helper for Example 63.2: the equation-defined round core is closed. -/
lemma isClosed_roundCore : IsClosed roundCore := by
  -- The core is the zero set of its continuous complex displacement signal.
  have hzeroSet : roundCore = {p | roundCoreSignal p = 0} := by
    ext p
    exact (roundCoreSignal_eq_zero_iff p).symm
  rw [hzeroSet]
  exact isClosed_eq continuous_roundCoreSignal continuous_const

/-- Helper for Example 63.2: the equation-defined round core is compact. -/
lemma isCompact_roundCore : IsCompact roundCore := by
  -- Closedness inside the compact Euclidean unit sphere gives compactness.
  exact (isCompact_sphere (0 : Space) 1).of_isClosed_subset
    isClosed_roundCore roundCore_subset_unitSphere

/-- Helper for Example 63.2: the complement of a closed thickening of the core lies in the
complement of the core itself. -/
lemma cthickeningCompl_subset_roundCoreCompl (r : ℝ) :
    (Metric.cthickening r roundCore)ᶜ ⊆ roundCoreᶜ := by
  -- A point of the core belongs to every closed thickening of the core.
  intro p hp hpcore
  exact hp (Metric.self_subset_cthickening roundCore hpcore)

/-- Helper for Example 63.2: restrict the round-core phase detector to the complement of a
closed thickening. -/
noncomputable def roundCorePhaseOnCthickeningComplement (r : ℝ) :
    C({p : Space // p ∈ (Metric.cthickening r roundCore)ᶜ}, Circle) :=
  ⟨fun p ↦
      ⟨roundCoreSignal p / ‖roundCoreSignal p‖,
        mem_sphere_zero_iff_norm.mpr
          (roundCorePhase_mem
            ⟨p, cthickeningCompl_subset_roundCoreCompl r p.property⟩)⟩,
    Continuous.subtype_mk
      ((continuous_roundCoreSignal.comp continuous_subtype_val).div
        (Complex.continuous_ofReal.comp
          (continuous_roundCoreSignal.comp continuous_subtype_val).norm)
        (fun p ↦ Complex.ofReal_ne_zero.mpr
          (norm_ne_zero_iff.mpr
            (roundCoreSignal_ne_zero
              (cthickeningCompl_subset_roundCoreCompl r p.property))))) _⟩

/-- Helper for Example 63.2: disjoint closed neighborhoods retain a meridian on which the
restricted phase detector is the identity. -/
lemma linkedCoreClosedNeighborhoodDetector_of_disjoint (r : ℝ)
    (hdisjoint : Disjoint (Metric.cthickening r roundCore)
      (Metric.cthickening r (Set.range roundCoreMeridian))) :
    ∃ m : C(Circle, {p : Space // p ∈ (Metric.cthickening r roundCore)ᶜ}),
      (∀ z, (m z : Space) = roundCoreMeridian z) ∧
      ∀ z, roundCorePhaseOnCthickeningComplement r (m z) = z := by
  -- Package the ambient meridian using disjointness of the two closed neighborhoods.
  have hmem (z : Circle) :
      roundCoreMeridian z ∈ (Metric.cthickening r roundCore)ᶜ := by
    -- The meridian lies in its own thickening, hence outside the disjoint core thickening.
    intro hzcore
    have hzmeridian : roundCoreMeridian z ∈
        Metric.cthickening r (Set.range roundCoreMeridian) :=
      Metric.self_subset_cthickening _ ⟨z, rfl⟩
    exact Set.disjoint_left.mp hdisjoint hzcore hzmeridian
  have hmcontinuous : Continuous
      (fun z : Circle ↦
        (⟨roundCoreMeridian z, hmem z⟩ :
          {p : Space // p ∈ (Metric.cthickening r roundCore)ᶜ})) := by
    -- Continuity into the complement subtype follows from ambient meridian continuity.
    exact continuous_roundCoreMeridian.subtype_mk _
  let m : C(Circle, {p : Space // p ∈ (Metric.cthickening r roundCore)ᶜ}) :=
    ⟨fun z ↦ ⟨roundCoreMeridian z, hmem z⟩, hmcontinuous⟩
  have hmval (z : Circle) : (m z : Space) = roundCoreMeridian z := by
    -- Record the ambient value before comparing subtype-valued detector inputs.
    rfl
  refine ⟨m, ?_, ?_⟩
  · -- The packaged meridian has the original ambient coordinates.
    exact hmval
  · -- Restriction does not alter the previously computed phase identity.
    intro z
    apply Circle.ext
    change roundCoreSignal (m z) / ‖roundCoreSignal (m z)‖ = (z : ℂ)
    rw [congrArg roundCoreSignal (hmval z), roundCoreSignal_roundCoreMeridian,
      norm_mul, Circle.norm_coe]
    norm_num

/-- Helper for Example 63.2: some disjoint closed core and meridian neighborhoods carry the
restricted degree-one phase detector. -/
theorem exists_linkedCoreClosedNeighborhoodDetector :
    ∃ r : ℝ, 0 < r ∧
      ∃ m : C(Circle, {p : Space // p ∈ (Metric.cthickening r roundCore)ᶜ}),
        (∀ z, (m z : Space) = roundCoreMeridian z) ∧
        ∀ z, roundCorePhaseOnCthickeningComplement r (m z) = z := by
  -- The equation-defined core and the explicit meridian range are disjoint.
  have hdisjoint : Disjoint roundCore (Set.range roundCoreMeridian) := by
    rw [Set.disjoint_left]
    rintro p hp ⟨w, rfl⟩
    exact roundCoreMeridian_mem_compl w hp
  have hmeridianCompact : IsCompact (Set.range roundCoreMeridian) :=
    isCompact_range continuous_roundCoreMeridian
  -- Compactness and closedness give a common positive thickening radius.
  obtain ⟨r, hr, hthickenings⟩ :=
    hdisjoint.exists_cthickenings isCompact_roundCore hmeridianCompact.isClosed
  obtain ⟨m, hmval, hphase⟩ :=
    linkedCoreClosedNeighborhoodDetector_of_disjoint r hthickenings
  exact ⟨r, hr, m, hmval, hphase⟩

/-- Helper for Example 63.2: the uniform limit in a linked-horn approximation is an
embedding. -/
lemma LinkedHornApproximation.limitEmbedding (A : LinkedHornApproximation) :
    Topology.IsEmbedding A.limitMap := by
  -- Uniform convergence transfers continuity from the finite embedded stages to the limit.
  have hcontinuous : Continuous A.limitMap :=
    A.stageMap_tendsto.continuous
      (Filter.Frequently.of_forall A.stageMap_continuous)
  -- Compactness of the source and Hausdorffness of the target upgrade injectivity to embedding.
  exact (hcontinuous.isClosedEmbedding A.limitMap_injective).isEmbedding

/-- Helper for Example 63.2: every finite-stage meridian in a linked-horn approximation is
not nullhomotopic. -/
lemma LinkedHornApproximation.stageMeridian_notNullhomotopic
    (A : LinkedHornApproximation) (n : ℕ) :
    ¬ Path.Homotopic (A.stageMeridian n) (Path.refl (A.stageBase n)) := by
  -- The stored circle detector sends this meridian to the positive degree-one generator.
  exact not_homotopic_refl_of_finiteStageDetector
    (A.stageDetector n) (A.stageDetector_base n) (A.stageMeridian n)
      (A.stageMeridian_degree n)

/-- Helper for Example 63.2: compact factorization through a finite horn stage makes the
limit meridian non-nullhomotopic. -/
lemma LinkedHornApproximation.limitMeridian_notNullhomotopic
    (A : LinkedHornApproximation) :
    ¬ Path.Homotopic A.limitMeridian
      (Path.refl
        (⟨A.limitBase, mem_connectedComponentIn A.limitBase_mem⟩ :
          {p // p ∈ connectedComponentIn (Set.range A.limitMap)ᶜ A.limitBase})) := by
  -- Any nullhomotopy has compact image and hence factors through one recorded finite stage.
  intro hnull
  obtain ⟨n, hn⟩ := A.nullhomotopy_factors hnull
  -- The degree-one detector at that stage contradicts the resulting finite nullhomotopy.
  exact A.stageMeridian_notNullhomotopic n hn

/-- Helper for Example 63.2: noncommutativity of the figure-eight fundamental group supplies
a nontrivial commutator class. -/
lemma exists_figureEight_commutator_ne_one :
    ∃ a b : FundamentalGroup FigureEight FigureEight.basepoint, ⁅a, b⁆ ≠ 1 := by
  -- Extract two noncommuting classes from the earlier computation of π₁ of the figure eight.
  classical
  have hnoncomm := figureEightFundamentalGroup_not_abelian
  rw [isMulCommutative_iff] at hnoncomm
  rw [not_forall] at hnoncomm
  obtain ⟨a, ha⟩ := hnoncomm
  rw [not_forall] at ha
  obtain ⟨b, hab⟩ := ha
  refine ⟨b.unop, a.unop, ?_⟩
  -- Commutation of the underlying classes would make the opposite-group classes commute.
  intro htrivial
  have hcomm := commutatorElement_eq_one_iff_mul_comm.mp htrivial
  apply hab
  apply MulOpposite.unop_injective
  simpa only [MulOpposite.unop_mul] using hcomm

/-- Helper for Example 63.2: the planar theta fundamental group contains a nonidentity
class transported from a figure-eight commutator. -/
lemma exists_planarTheta_class_ne_one :
    ∃ g : FundamentalGroup PlanarTheta PlanarTheta.basepoint, g ≠ 1 := by
  -- Transport the explicit noncommutative obstruction through the established group equivalence.
  obtain ⟨e⟩ := figureEightFundamentalGroup_mulEquiv_planarTheta
  obtain ⟨a, b, hab⟩ := exists_figureEight_commutator_ne_one
  refine ⟨e ⁅a, b⁆, ?_⟩
  intro htrivial
  apply hab
  apply e.injective
  rw [htrivial, map_one]

/-- Helper for Example 63.2: the complement of the complete one-stage relative obstacle
contains a based loop detected by a nonidentity `PlanarTheta` class. -/
lemma exists_framedBingRelativeComplementDetectedLoop :
    ∃ (b : {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ})
      (mu : Path b b)
      (q : C({p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ},
        PlanarTheta))
      (hq : q b = PlanarTheta.basepoint)
      (g : FundamentalGroup PlanarTheta PlanarTheta.basepoint),
        g ≠ 1 ∧
          FundamentalGroup.mapOfEq q hq
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk mu)) = g := by
  -- Represent a nonidentity theta class and carry its loop through the relative section.
  obtain ⟨s, q, hsplit⟩ := exists_framedBingRelativeComplementSplit
  obtain ⟨g, hg⟩ := exists_planarTheta_class_ne_one
  obtain ⟨nu, hnu⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  let b := s PlanarTheta.basepoint
  let mu : Path b b := nu.map s.continuous
  have hq : q b = PlanarTheta.basepoint := hsplit PlanarTheta.basepoint
  refine ⟨b, mu, q, hq, g, hg, ?_⟩
  -- The split equation reduces the detected mapped loop to its chosen representative.
  have hmapped : (mu.map q.continuous).cast hq.symm hq.symm = nu := by
    ext t
    exact congrArg (fun z : PlanarTheta ↦ (z : ℂ)) (hsplit (nu t))
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, hmapped, hnu]

/-- Helper for Example 63.2: the standard framed child complement contains a based loop
whose image in `PlanarTheta` represents a nonidentity class. -/
lemma exists_framedBingComplementDetectedLoop :
    ∃ (b : {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ})
      (mu : Path b b)
      (q : C({p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}, PlanarTheta))
      (hq : q b = PlanarTheta.basepoint)
      (g : FundamentalGroup PlanarTheta PlanarTheta.basepoint),
        g ≠ 1 ∧
          FundamentalGroup.mapOfEq q hq
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk mu)) = g := by
  -- Choose the split copy of theta and a nonidentity class detected on that copy.
  obtain ⟨s, q, hsplit⟩ := exists_framedBingComplementSplit
  obtain ⟨g, hg⟩ := exists_planarTheta_class_ne_one
  -- Represent the chosen class by a concrete loop before mapping it through the section.
  obtain ⟨nu, hnu⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  let b := s PlanarTheta.basepoint
  let mu : Path b b := nu.map s.continuous
  have hq : q b = PlanarTheta.basepoint := hsplit PlanarTheta.basepoint
  refine ⟨b, mu, q, hq, g, hg, ?_⟩
  -- The retraction equation identifies the mapped representative pointwise with `nu`.
  have hmapped : (mu.map q.continuous).cast hq.symm hq.symm = nu := by
    ext t
    exact congrArg (fun z : PlanarTheta ↦ (z : ℂ)) (hsplit (nu t))
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, hmapped, hnu]

/-- Helper for Example 63.2: one contracting framed Bing replacement packages the compact
horn patch, its disjoint small child tubes, and a meridian with nonidentity theta class. -/
structure ContractingBingReplacement where
  contraction : ℝ
  contraction_pos : 0 < contraction
  contraction_lt_one : contraction < 1
  scale : ℝ
  scale_pos : 0 < scale
  blockEmbedding : Topology.IsEmbedding (framedBingAffineCompression scale)
  patchCompact : IsCompact (framedBingAffineCompression scale '' framedBingHornPatch)
  childTubesDisjoint :
    Disjoint
      (framedBingAffineCompression scale '' framedBingTube 0)
      (framedBingAffineCompression scale '' framedBingTube 2)
  childTube_mesh : ∀ i : Fin 3,
    Metric.diam (framedBingAffineCompression scale '' framedBingTube i) < contraction
  base : {p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}
  meridian : Path base base
  detector : C({p : unitInterval × ℂ // p ∈ framedBingChildObstacleᶜ}, PlanarTheta)
  detector_base : detector base = PlanarTheta.basepoint
  detectedClass : FundamentalGroup PlanarTheta PlanarTheta.basepoint
  detectedClass_ne_one : detectedClass ≠ 1
  meridian_detected :
    FundamentalGroup.mapOfEq detector detector_base
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk meridian)) =
      detectedClass

/-- Helper for Example 63.2: a local replacement is accompanied by a fixed copy of
`PlanarTheta` in the full relative-obstacle complement and a continuous left inverse. -/
structure ThetaSplitBingReplacement (_replacement : ContractingBingReplacement) where
  thetaSection : C(PlanarTheta,
    {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ})
  retraction : C(
    {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ},
    PlanarTheta)
  retraction_thetaSection : ∀ z, retraction (thetaSection z) = z

/-- Helper for Example 63.2: the canonical relative-complement split equips every
contracting replacement with its theta-split companion. -/
theorem ContractingBingReplacement.toThetaSplit
    (R : ContractingBingReplacement) :
    Nonempty (ThetaSplitBingReplacement R) := by
  -- Package the midpoint theta section and its already verified punctured-plane retraction.
  obtain ⟨thetaSection, retraction, hsplit⟩ :=
    exists_framedBingRelativeComplementSplit
  exact ⟨{
    thetaSection := thetaSection
    retraction := retraction
    retraction_thetaSection := hsplit
  }⟩

/-- Helper for Example 63.2: a split theta section supplies a based loop representing a
nonidentity class in the full relative-obstacle complement. -/
lemma ThetaSplitBingReplacement.exists_meridianClass_ne_one
    {R : ContractingBingReplacement} (T : ThetaSplitBingReplacement R) :
    ∃ (b : {p : unitInterval × ℂ // p ∈ framedBingRelativeObstacleᶜ})
      (mu : Path b b),
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk mu) ≠ 1 := by
  -- Choose a nonidentity theta class and a path representative before applying the section.
  obtain ⟨g, hg⟩ := exists_planarTheta_class_ne_one
  obtain ⟨nu, hnu⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  let b := T.thetaSection PlanarTheta.basepoint
  let mu : Path b b := nu.map T.thetaSection.continuous
  have hbase : T.retraction b = PlanarTheta.basepoint :=
    T.retraction_thetaSection PlanarTheta.basepoint
  refine ⟨b, mu, fundamentalGroup_ne_one_of_map_eq_ne_one
    T.retraction hbase
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk mu)) g ?_ hg⟩
  -- Applying the left inverse to the section-valued path recovers its chosen representative.
  have hmapped :
      (mu.map T.retraction.continuous).cast hbase.symm hbase.symm = nu := by
    ext t
    exact congrArg (fun z : PlanarTheta ↦ (z : ℂ))
      (T.retraction_thetaSection (nu t))
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, hmapped, hnu]

/-- Helper for Example 63.2: the explicit framed block admits a contraction factor below
one together with a meridian detected by a nonidentity theta class. -/
theorem contractingFramedBingReplacement_nonempty :
    Nonempty ContractingBingReplacement := by
  -- Compress the complete local block below the fixed factor `1 / 2`.
  have hcontractionPos : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hcontractionLt : (1 / 2 : ℝ) < 1 := by
    norm_num
  obtain ⟨scale, hscale, hembedding, hcompact, hdisjoint, hmesh⟩ :=
    exists_smallFramedBingBlock hcontractionPos
  -- Independently choose the split theta loop carried by the child-obstacle complement.
  obtain ⟨base, meridian, detector, hdetectorBase, detectedClass,
      hdetectedClass, hdetected⟩ := exists_framedBingComplementDetectedLoop
  refine ⟨{
    contraction := 1 / 2
    contraction_pos := hcontractionPos
    contraction_lt_one := hcontractionLt
    scale := scale
    scale_pos := hscale
    blockEmbedding := hembedding
    patchCompact := hcompact
    childTubesDisjoint := hdisjoint
    childTube_mesh := hmesh
    base := base
    meridian := meridian
    detector := detector
    detector_base := hdetectorBase
    detectedClass := detectedClass
    detectedClass_ne_one := hdetectedClass
    meridian_detected := hdetected
  }⟩

/-- Helper for Example 63.2: the meridian stored in a contracting replacement represents a
nonidentity class in the complement of its child tubes. -/
lemma ContractingBingReplacement.meridianClass_ne_one
    (R : ContractingBingReplacement) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk R.meridian) ≠ 1 := by
  -- A trivial source class would map to the identity, contradicting the stored detector class.
  exact fundamentalGroup_ne_one_of_map_eq_ne_one
    R.detector R.detector_base
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk R.meridian))
    R.detectedClass R.meridian_detected R.detectedClass_ne_one

/-- Helper for Example 63.2: the contracting replacement's detected meridian is not
nullhomotopic in the child-tube complement. -/
lemma ContractingBingReplacement.meridian_notNullhomotopic
    (R : ContractingBingReplacement) :
    ¬ Path.Homotopic R.meridian (Path.refl R.base) := by
  -- Convert the nonidentity fundamental-group class into the required homotopy obstruction.
  exact not_homotopic_refl_of_fundamentalGroup_fromPath_ne_one
    R.meridian R.meridianClass_ne_one

/-- Helper for Example 63.2: uniformly convergent compact approximations with shrinking
closed nested neighborhoods have intersection equal to the limiting range. -/
lemma iInter_eq_range_of_uniform_nested_approximation
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (K : ℕ → Set Y)
    (hf : Continuous f) (hF : TendstoUniformly F f Filter.atTop)
    (hKclosed : ∀ n, IsClosed (K n)) (hKantitone : Antitone K)
    (hstage : ∀ n, Set.range (F n) ⊆ K n)
    (happrox : ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      ∀ y, y ∈ K n → ∃ x, dist y (F n x) < ε) :
    ⋂ n, K n = Set.range f := by
  -- First approximate each point of the nested intersection by a limiting range point.
  apply Set.Subset.antisymm
  · intro y hy
    have hlimitRangeClosed : IsClosed (Set.range f) :=
      (isCompact_range hf).isClosed
    rw [← hlimitRangeClosed.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hnear := Metric.tendstoUniformly_iff.mp hF (ε / 2) (half_pos hε)
    have hstageNear := happrox (ε / 2) (half_pos hε)
    obtain ⟨n, hnearAt, hstageNearAt⟩ := (hnear.and hstageNear).exists
    obtain ⟨x, hx⟩ := hstageNearAt y (Set.mem_iInter.mp hy n)
    refine ⟨f x, ⟨x, rfl⟩, ?_⟩
    calc
      dist y (f x) ≤ dist y (F n x) + dist (F n x) (f x) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 :=
        add_lt_add hx (by simpa only [dist_comm] using hnearAt x)
      _ = ε := by ring
  · rintro y ⟨x, rfl⟩
    rw [Set.mem_iInter]
    intro n
    -- Closedness retains the eventual membership of all finer antitone stages.
    apply (hKclosed n).mem_of_tendsto (hF.tendsto_at x)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact hKantitone hm (hstage m ⟨x, rfl⟩)

/-- Helper for Example 63.2: finite nonabelian horn stages converge to an embedded sphere and
carry one persistent meridian obstruction into a complementary component. -/
structure NonabelianLinkedHornApproximation where
  limitMap : StandardSphere 2 → StandardSphere 3
  limitMap_continuous : Continuous limitMap
  limitMap_injective : Function.Injective limitMap
  limitBase : StandardSphere 3
  limitBase_mem : limitBase ∈ (Set.range limitMap)ᶜ
  limitMeridian : Path
    (⟨limitBase, mem_connectedComponentIn limitBase_mem⟩ :
      {p // p ∈ connectedComponentIn (Set.range limitMap)ᶜ limitBase})
    ⟨limitBase, mem_connectedComponentIn limitBase_mem⟩
  obstacle : ℕ → Set (StandardSphere 3)
  obstacle_closed : ∀ n, IsClosed (obstacle n)
  obstacle_antitone : Antitone obstacle
  obstacle_iInter : ⋂ n, obstacle n = Set.range limitMap
  limitBase_mem_stage : ∀ n, limitBase ∈ (obstacle n)ᶜ
  stageMeridian : ∀ n,
    Path (⟨limitBase, limitBase_mem_stage n⟩ : {p // p ∈ (obstacle n)ᶜ})
      ⟨limitBase, limitBase_mem_stage n⟩
  stageMeridian_ambient : ∀ n t,
    (stageMeridian n t : StandardSphere 3) = limitMeridian t
  stageMeridian_class_ne_one : ∀ n,
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (stageMeridian n)) ≠ 1

/-- Helper for Example 63.2: the common ambient meridian basepoint regarded in a finite-stage
obstacle complement. -/
abbrev NonabelianLinkedHornApproximation.stageBase
    (A : NonabelianLinkedHornApproximation) (n : ℕ) :
    {p // p ∈ (A.obstacle n)ᶜ} :=
  ⟨A.limitBase, A.limitBase_mem_stage n⟩

/-- Helper for Example 63.2: the limit map of a nonabelian linked-horn approximation is an
embedding. -/
lemma NonabelianLinkedHornApproximation.limitEmbedding
    (A : NonabelianLinkedHornApproximation) : Topology.IsEmbedding A.limitMap := by
  -- Compactness of the source and Hausdorffness of the target upgrade the stored continuous
  -- injection to an embedding.
  exact (A.limitMap_continuous.isClosedEmbedding A.limitMap_injective).isEmbedding

/-- Helper for Example 63.2: the stored nonidentity class makes each finite-stage meridian
non-nullhomotopic. -/
lemma NonabelianLinkedHornApproximation.stageMeridian_notNullhomotopic
    (A : NonabelianLinkedHornApproximation) (n : ℕ) :
    ¬ Path.Homotopic (A.stageMeridian n) (Path.refl (A.stageBase n)) := by
  -- Apply the generic fundamental-group obstruction to the selected finite stage.
  exact not_homotopic_refl_of_fundamentalGroup_fromPath_ne_one
    (A.stageMeridian n) (A.stageMeridian_class_ne_one n)

/-- Helper for Example 63.2: a nullhomotopy in the limit complement restricts to the
complement of one finite closed obstacle. -/
lemma NonabelianLinkedHornApproximation.nullhomotopy_factors
    (A : NonabelianLinkedHornApproximation)
    (hnull : Path.Homotopic A.limitMeridian
      (Path.refl
        (⟨A.limitBase, mem_connectedComponentIn A.limitBase_mem⟩ :
          {p // p ∈ connectedComponentIn (Set.range A.limitMap)ᶜ A.limitBase}))) :
    ∃ n, Path.Homotopic (A.stageMeridian n) (Path.refl (A.stageBase n)) := by
  -- Choose a representative homotopy and map it from the component into the ambient sphere.
  obtain ⟨F⟩ := hnull
  let inclusion : C(
      {p // p ∈ connectedComponentIn (Set.range A.limitMap)ᶜ A.limitBase},
      StandardSphere 3) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let ambientHomotopy := F.map inclusion
  -- Its compact image avoids the limiting sphere, hence already avoids one finite obstacle.
  have hcompact : IsCompact (Set.range ambientHomotopy) :=
    isCompact_range ambientHomotopy.continuous
  have hdisjoint : Set.range ambientHomotopy ⊆ (⋂ n, A.obstacle n)ᶜ := by
    rintro _ ⟨z, rfl⟩
    rw [A.obstacle_iInter]
    exact connectedComponentIn_subset (Set.range A.limitMap)ᶜ A.limitBase (F z).property
  obtain ⟨n, hn⟩ := hcompact.subset_compl_iInter_of_antitone
    A.obstacle A.obstacle_closed A.obstacle_antitone hdisjoint
  refine ⟨n, ?_⟩
  -- Restrict the ambient square using the stored stage-base and meridian bridge laws.
  refine Path.Homotopy.codRestrictHomotopic
    (V := (A.obstacle n)ᶜ) (x₀ := A.stageBase n) (x₁ := A.stageBase n)
    (p₀ := A.limitMeridian.map inclusion.continuous)
    (p₁ := (Path.refl
      (⟨A.limitBase, mem_connectedComponentIn A.limitBase_mem⟩ :
        {p // p ∈ connectedComponentIn (Set.range A.limitMap)ᶜ A.limitBase})).map
          inclusion.continuous)
    (q₀ := A.stageMeridian n) (q₁ := Path.refl (A.stageBase n))
    ambientHomotopy (fun z ↦ hn ⟨z, rfl⟩) ?_ ?_
  · exact A.stageMeridian_ambient n
  · intro _
    rfl

/-- Helper for Example 63.2: compact factorization through a finite nonabelian horn stage
makes the limit meridian non-nullhomotopic. -/
lemma NonabelianLinkedHornApproximation.limitMeridian_notNullhomotopic
    (A : NonabelianLinkedHornApproximation) :
    ¬ Path.Homotopic A.limitMeridian
      (Path.refl
        (⟨A.limitBase, mem_connectedComponentIn A.limitBase_mem⟩ :
          {p // p ∈ connectedComponentIn (Set.range A.limitMap)ᶜ A.limitBase})) := by
  -- Factor a hypothetical nullhomotopy through a finite stage.
  intro hnull
  obtain ⟨n, hn⟩ := A.nullhomotopy_factors hnull
  -- The stored nonidentity stage class contradicts that finite nullhomotopy.
  exact A.stageMeridian_notNullhomotopic n hn

/-- Helper for Example 63.2: quantitative finite Bing stages, decreasing obstacles, and a
stagewise nonidentity meridian class package the recursive horn construction. -/
structure BingHornStageSystem where
  stageMap : ℕ → StandardSphere 2 → StandardSphere 3
  limitMap : StandardSphere 2 → StandardSphere 3
  stageMap_continuous : ∀ n, Continuous (stageMap n)
  stageMap_tendsto : TendstoUniformly stageMap limitMap Filter.atTop
  stageMap_eventually_separated : ∀ x y : StandardSphere 2, x ≠ y →
    ∃ ε > 0, ∀ᶠ n : ℕ in Filter.atTop, ε ≤ dist (stageMap n x) (stageMap n y)
  obstacle : ℕ → Set (StandardSphere 3)
  obstacle_closed : ∀ n, IsClosed (obstacle n)
  obstacle_antitone : Antitone obstacle
  obstacle_iInter : ⋂ n, obstacle n = Set.range limitMap
  limitBase : StandardSphere 3
  limitBase_mem : limitBase ∈ (Set.range limitMap)ᶜ
  limitBase_mem_stage : ∀ n, limitBase ∈ (obstacle n)ᶜ
  limitMeridian : Path
    (⟨limitBase, mem_connectedComponentIn limitBase_mem⟩ :
      {p // p ∈ connectedComponentIn (Set.range limitMap)ᶜ limitBase})
    ⟨limitBase, mem_connectedComponentIn limitBase_mem⟩
  stageMeridian : ∀ n,
    Path (⟨limitBase, limitBase_mem_stage n⟩ : {p // p ∈ (obstacle n)ᶜ})
      ⟨limitBase, limitBase_mem_stage n⟩
  stageMeridian_ambient : ∀ n t,
    (stageMeridian n t : StandardSphere 3) = limitMeridian t
  stageMeridian_class_ne_one : ∀ n,
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (stageMeridian n)) ≠ 1

/-- Helper for Example 63.2: the uniform limit recorded by a Bing stage system is
continuous. -/
lemma BingHornStageSystem.limitMap_continuous (S : BingHornStageSystem) :
    Continuous S.limitMap := by
  -- Uniform convergence transfers continuity from every finite stage to the limit.
  exact S.stageMap_tendsto.continuous
    (Filter.Frequently.of_forall S.stageMap_continuous)

/-- Helper for Example 63.2: persistent finite-stage separation makes the Bing limit map
injective. -/
lemma BingHornStageSystem.limitMap_injective (S : BingHornStageSystem) :
    Function.Injective S.limitMap := by
  -- Apply the quantitative separation criterion to the stored uniformly convergent stages.
  apply injectiveOfTendstoUniformlyOfEventuallyDistGe S.stageMap_tendsto
  intro x y hxy
  exact S.stageMap_eventually_separated x y hxy

/-- Helper for Example 63.2: a quantitative Bing stage system supplies the approximation
record consumed by the compact-factorization argument. -/
def BingHornStageSystem.toNonabelianLinkedHornApproximation
    (S : BingHornStageSystem) : NonabelianLinkedHornApproximation :=
  -- Assemble only from the verified stage-system projection lemmas and stored specifications.
  {
    limitMap := S.limitMap
    limitMap_continuous := S.limitMap_continuous
    limitMap_injective := S.limitMap_injective
    limitBase := S.limitBase
    limitBase_mem := S.limitBase_mem
    limitMeridian := S.limitMeridian
    obstacle := S.obstacle
    obstacle_closed := S.obstacle_closed
    obstacle_antitone := S.obstacle_antitone
    obstacle_iInter := S.obstacle_iInter
    limitBase_mem_stage := S.limitBase_mem_stage
    stageMeridian := S.stageMeridian
    stageMeridian_ambient := S.stageMeridian_ambient
    stageMeridian_class_ne_one := S.stageMeridian_class_ne_one
  }

/-- Helper for Example 63.2: convergent finite Bing stages store exactly the topological
data needed to identify the limiting sphere and retain stagewise meridian obstructions. -/
structure ConvergentBingHornStages where
  stageMap : ℕ → StandardSphere 2 → StandardSphere 3
  limitMap : StandardSphere 2 → StandardSphere 3
  stageMap_continuous : ∀ n, Continuous (stageMap n)
  stageMap_tendsto : TendstoUniformly stageMap limitMap Filter.atTop
  limitMap_injective : Function.Injective limitMap
  obstacle : ℕ → Set (StandardSphere 3)
  obstacle_closed : ∀ n, IsClosed (obstacle n)
  obstacle_antitone : Antitone obstacle
  stageMap_range : ∀ n, Set.range (stageMap n) ⊆ obstacle n
  obstacle_eventually_approximated : ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    ∀ y, y ∈ obstacle n → ∃ x, dist y (stageMap n x) < ε
  limitBase : StandardSphere 3
  limitBase_mem_stage : ∀ n, limitBase ∈ (obstacle n)ᶜ
  stageMeridian : ∀ n,
    Path (⟨limitBase, limitBase_mem_stage n⟩ : {p // p ∈ (obstacle n)ᶜ})
      ⟨limitBase, limitBase_mem_stage n⟩
  stageMeridian_ambient : ∀ n t,
    (stageMeridian n t : StandardSphere 3) = (stageMeridian 0 t : StandardSphere 3)
  stageMeridian_class_ne_one : ∀ n,
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (stageMeridian n)) ≠ 1

/-- Helper for Example 63.2: the common finite-stage meridian lies in the complementary
component of the limiting sphere once the obstacle intersection is identified. -/
lemma ConvergentBingHornStages.stageMeridian_zero_mem_limitComponent
    (S : ConvergentBingHornStages)
    (hintersection : ⋂ n, S.obstacle n = Set.range S.limitMap)
    (t : unitInterval) :
    (S.stageMeridian 0 t : StandardSphere 3) ∈
      connectedComponentIn (Set.range S.limitMap)ᶜ S.limitBase := by
  -- The ambient range of the stage-zero meridian is connected and contains the common base.
  have hrange : IsConnected
      (Set.range (fun u ↦ (S.stageMeridian 0 u : StandardSphere 3))) :=
    isConnected_range (continuous_subtype_val.comp (S.stageMeridian 0).continuous)
  apply hrange.isPreconnected.subset_connectedComponentIn
  · refine ⟨0, ?_⟩
    exact congrArg Subtype.val (S.stageMeridian 0).source
  · rintro _ ⟨u, rfl⟩
    -- Every point of the common ambient meridian avoids every nested obstacle.
    rw [← hintersection]
    intro hmem
    exact (S.stageMeridian 0 u).property (Set.mem_iInter.mp hmem 0)
  · exact Set.mem_range_self t

/-- Helper for Example 63.2: injectivity of the stored uniform limit gives persistent
positive separation of any two distinct source points. -/
lemma ConvergentBingHornStages.stageMap_eventually_separated
    (S : ConvergentBingHornStages) (x y : StandardSphere 2) (hxy : x ≠ y) :
    ∃ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
      ε ≤ dist (S.stageMap n x) (S.stageMap n y) := by
  -- Pointwise convergence makes the stage distances tend to the positive limit distance.
  have hlimitNe : S.limitMap x ≠ S.limitMap y := by
    intro heq
    exact hxy (S.limitMap_injective heq)
  have hlimitDist : 0 < dist (S.limitMap x) (S.limitMap y) := dist_pos.mpr hlimitNe
  have hdistTendsto : Filter.Tendsto
      (fun n ↦ dist (S.stageMap n x) (S.stageMap n y)) Filter.atTop
      (nhds (dist (S.limitMap x) (S.limitMap y))) :=
    (S.stageMap_tendsto.tendsto_at x).dist (S.stageMap_tendsto.tendsto_at y)
  refine ⟨dist (S.limitMap x) (S.limitMap y) / 2, half_pos hlimitDist, ?_⟩
  exact (hdistTendsto.eventually_const_lt (half_lt_self hlimitDist)).mono
    (fun _ hn ↦ hn.le)

/-- Helper for Example 63.2: directly convergent finite stages compile to the stage-system
interface used by the compact-factorization proof. -/
theorem ConvergentBingHornStages.toBingHornStageSystem
    (S : ConvergentBingHornStages) : Nonempty BingHornStageSystem := by
  -- Uniform convergence supplies continuity of the already selected injective limit.
  have hlimitContinuous : Continuous S.limitMap :=
    S.stageMap_tendsto.continuous
      (Filter.Frequently.of_forall S.stageMap_continuous)
  -- Eventual metric approximation identifies the nested obstacle intersection with that limit.
  have hintersection : ⋂ n, S.obstacle n = Set.range S.limitMap :=
    iInter_eq_range_of_uniform_nested_approximation
      S.stageMap S.limitMap S.obstacle hlimitContinuous S.stageMap_tendsto
      S.obstacle_closed S.obstacle_antitone S.stageMap_range
      S.obstacle_eventually_approximated
  have hbase : S.limitBase ∈ (Set.range S.limitMap)ᶜ := by
    rw [← hintersection]
    intro hmem
    exact S.limitBase_mem_stage 0 (Set.mem_iInter.mp hmem 0)
  -- Restrict the common ambient meridian to the limiting complementary component.
  let limitMeridian : Path
      (⟨S.limitBase, mem_connectedComponentIn hbase⟩ :
        {p // p ∈ connectedComponentIn (Set.range S.limitMap)ᶜ S.limitBase})
      ⟨S.limitBase, mem_connectedComponentIn hbase⟩ :=
    {
      toFun := fun t ↦
        ⟨S.stageMeridian 0 t,
          S.stageMeridian_zero_mem_limitComponent hintersection t⟩
      continuous_toFun :=
        (continuous_subtype_val.comp (S.stageMeridian 0).continuous).subtype_mk _
      source' := Subtype.ext (congrArg
        (fun z : {p // p ∈ (S.obstacle 0)ᶜ} ↦ (z : StandardSphere 3))
        (S.stageMeridian 0).source)
      target' := Subtype.ext (congrArg
        (fun z : {p // p ∈ (S.obstacle 0)ᶜ} ↦ (z : StandardSphere 3))
        (S.stageMeridian 0).target)
    }
  refine ⟨{
    stageMap := S.stageMap
    limitMap := S.limitMap
    stageMap_continuous := S.stageMap_continuous
    stageMap_tendsto := S.stageMap_tendsto
    stageMap_eventually_separated := S.stageMap_eventually_separated
    obstacle := S.obstacle
    obstacle_closed := S.obstacle_closed
    obstacle_antitone := S.obstacle_antitone
    obstacle_iInter := hintersection
    limitBase := S.limitBase
    limitBase_mem := hbase
    limitBase_mem_stage := S.limitBase_mem_stage
    limitMeridian := limitMeridian
    stageMeridian := S.stageMeridian
    stageMeridian_ambient := ?_
    stageMeridian_class_ne_one := S.stageMeridian_class_ne_one
  }⟩
  -- The limit-component restriction has the stage-zero meridian as its ambient path.
  intro n t
  exact S.stageMeridian_ambient n t

/-- Helper for Example 63.2: the distance to the nearer outer marked point controls the
two disjoint button supports in the affine seed plane. -/
noncomputable def framedBingButtonRadius (z : ℂ) : ℝ :=
  min (dist z (framedBingMarkedPoint 0)) (dist z (framedBingMarkedPoint 2))

/-- Helper for Example 63.2: the seed plane has height one on its two cap disks and
returns linearly to height zero before radius `1 / 8`. -/
noncomputable def framedBingButtonHeight (z : ℂ) : ℝ :=
  max 0 (min 1 (2 - 16 * framedBingButtonRadius z))

/-- Helper for Example 63.2: distance to the nearer outer marked point varies
continuously. -/
lemma continuous_framedBingButtonRadius : Continuous framedBingButtonRadius := by
  -- Both distance functions are continuous, and taking their pointwise minimum preserves
  -- continuity.
  unfold framedBingButtonRadius
  exact (continuous_id.dist continuous_const).min
    (continuous_id.dist continuous_const)

/-- Helper for Example 63.2: the two-button height profile is continuous. -/
lemma continuous_framedBingButtonHeight : Continuous framedBingButtonHeight := by
  -- The clipped affine profile is assembled from continuous arithmetic, minimum, and maximum.
  unfold framedBingButtonHeight
  exact continuous_const.max
    (continuous_const.min
      (continuous_const.sub
        (continuous_const.mul continuous_framedBingButtonRadius)))

/-- Helper for Example 63.2: each inner outer-marked disk is a flat terminal cap of the
two-button seed plane. -/
lemma framedBingButtonHeight_eq_one_of_mem_cap (i : Fin 3) (hi : i = 0 ∨ i = 2)
    {z : ℂ} (hz : z ∈ Metric.closedBall (framedBingMarkedPoint i) (1 / 16)) :
    framedBingButtonHeight z = 1 := by
  -- Membership in either cap bounds the nearer-center radius by `1 / 16`.
  have hnear : framedBingButtonRadius z ≤ (1 / 16 : ℝ) := by
    rcases hi with rfl | rfl
    · exact (min_le_left _ _).trans (by
        simpa only [Metric.mem_closedBall, dist_comm] using hz)
    · exact (min_le_right _ _).trans (by
        simpa only [Metric.mem_closedBall, dist_comm] using hz)
  have hprofile : (1 : ℝ) ≤ 2 - 16 * framedBingButtonRadius z := by
    linarith
  -- Both clipping operations are inactive at the constant top value.
  rw [framedBingButtonHeight, min_eq_left hprofile]
  norm_num

/-- Helper for Example 63.2: outside both radius-`1 / 8` support disks the button height
vanishes. -/
lemma framedBingButtonHeight_eq_zero_of_outerSupports_le {z : ℂ}
    (hleft : (1 / 8 : ℝ) ≤ dist z (framedBingMarkedPoint 0))
    (hright : (1 / 8 : ℝ) ≤ dist z (framedBingMarkedPoint 2)) :
    framedBingButtonHeight z = 0 := by
  -- The nearer-center radius is still at least `1 / 8`, so the unclipped profile is
  -- nonpositive.
  have hnear : (1 / 8 : ℝ) ≤ framedBingButtonRadius z := by
    exact le_min hleft hright
  have hprofile : 2 - 16 * framedBingButtonRadius z ≤ (0 : ℝ) := by
    linarith
  rw [framedBingButtonHeight, max_eq_left]
  exact (min_le_right 1 (2 - 16 * framedBingButtonRadius z)).trans hprofile

/-- Helper for Example 63.2: the explicit affine seed plane is the graph of the
two-button height profile. -/
noncomputable def framedBingButtonPlane (z : ℂ) : ℝ × ℂ :=
  (framedBingButtonHeight z, z)

/-- Helper for Example 63.2: the explicit two-button plane varies continuously. -/
lemma continuous_framedBingButtonPlane : Continuous framedBingButtonPlane := by
  -- Pair the continuous height coordinate with the unchanged complex coordinate.
  unfold framedBingButtonPlane
  exact continuous_framedBingButtonHeight.prodMk continuous_id

/-- Helper for Example 63.2: the two flat inner disks map exactly to the terminal cap
disks at height one. -/
lemma framedBingButtonPlane_apply_of_mem_cap (i : Fin 3) (hi : i = 0 ∨ i = 2)
    {z : ℂ} (hz : z ∈ Metric.closedBall (framedBingMarkedPoint i) (1 / 16)) :
    framedBingButtonPlane z = (1, z) := by
  -- Substitute the cap computation into the graph parameterization.
  rw [framedBingButtonPlane, framedBingButtonHeight_eq_one_of_mem_cap i hi hz]

/-- Helper for Example 63.2: the seed plane agrees with the bottom coordinate plane away
from its two compact supports. -/
lemma framedBingButtonPlane_apply_of_outerSupports_le {z : ℂ}
    (hleft : (1 / 8 : ℝ) ≤ dist z (framedBingMarkedPoint 0))
    (hright : (1 / 8 : ℝ) ≤ dist z (framedBingMarkedPoint 2)) :
    framedBingButtonPlane z = (0, z) := by
  -- Substitute the outside-support computation into the graph parameterization.
  rw [framedBingButtonPlane,
    framedBingButtonHeight_eq_zero_of_outerSupports_le hleft hright]

/-- Helper for Example 63.2: the explicit two-button seed plane is a closed embedding in
the affine three-dimensional model. -/
lemma framedBingButtonPlane_isClosedEmbedding :
    Topology.IsClosedEmbedding framedBingButtonPlane := by
  -- Projection to the complex coordinate is a continuous left inverse, hence the graph map
  -- is an embedding.
  have hleftInverse : Function.LeftInverse Prod.snd framedBingButtonPlane := by
    intro z
    rfl
  have hembedding : Topology.IsEmbedding framedBingButtonPlane :=
    hleftInverse.isEmbedding continuous_snd continuous_framedBingButtonPlane
  -- Identify the graph range with a closed equality locus in `ℝ × ℂ`.
  have hrange : Set.range framedBingButtonPlane =
      {p : ℝ × ℂ | p.1 = framedBingButtonHeight p.2} := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      rfl
    · intro hp
      refine ⟨p.2, ?_⟩
      apply Prod.ext
      · exact hp.symm
      · rfl
  refine ⟨hembedding, ?_⟩
  rw [hrange]
  exact isClosed_eq continuous_fst
    (continuous_framedBingButtonHeight.comp continuous_snd)

/-- Helper for Example 63.2: the proper two-button plane map extends continuously over
the one-point compactifications. -/
lemma continuous_onePointMap_framedBingButtonPlane :
    Continuous (OnePoint.map framedBingButtonPlane) := by
  -- Closed embeddings are proper, and proper maps tend to infinity in the cocompact filters.
  have hproper : IsProperMap framedBingButtonPlane :=
    framedBingButtonPlane_isClosedEmbedding.isProperMap
  have hcocompact : Filter.Tendsto framedBingButtonPlane
      (Filter.cocompact ℂ) (Filter.cocompact (ℝ × ℂ)) :=
    (isProperMap_iff_tendsto_cocompact.mp hproper).2
  apply OnePoint.continuous_map continuous_framedBingButtonPlane
  rw [Filter.coclosedCompact_eq_cocompact,
    Filter.coclosedCompact_eq_cocompact]
  exact hcocompact

/-- Helper for Example 63.2: compactifying the two-button plane preserves injectivity. -/
lemma injective_onePointMap_framedBingButtonPlane :
    Function.Injective (OnePoint.map framedBingButtonPlane) := by
  -- `OnePoint.map` is `Option.map`, so injectivity follows from the affine embedding.
  exact Option.map_injective framedBingButtonPlane_isClosedEmbedding.injective

/-- Helper for Example 63.2: conjugating the compactified two-button plane by the fixed
sphere charts gives the capped seed sphere. -/
noncomputable def framedBingButtonSphere : StandardSphere 2 → StandardSphere 3 :=
  fun x ↦ realProdComplexOnePointSphereHomeomorph
    (OnePoint.map framedBingButtonPlane (complexOnePointSphereHomeomorph.symm x))

/-- Helper for Example 63.2: the capped seed sphere is a closed embedding. -/
lemma framedBingButtonSphere_isClosedEmbedding :
    Topology.IsClosedEmbedding framedBingButtonSphere := by
  -- Continuity and injectivity are preserved by both compactification charts; compactness of
  -- the source then upgrades the map to a closed embedding.
  have hcontinuous : Continuous framedBingButtonSphere := by
    unfold framedBingButtonSphere
    exact realProdComplexOnePointSphereHomeomorph.continuous.comp
      (continuous_onePointMap_framedBingButtonPlane.comp
        complexOnePointSphereHomeomorph.symm.continuous)
  have hinjective : Function.Injective framedBingButtonSphere := by
    unfold framedBingButtonSphere
    exact realProdComplexOnePointSphereHomeomorph.injective.comp
      (injective_onePointMap_framedBingButtonPlane.comp
        complexOnePointSphereHomeomorph.symm.injective)
  exact hcontinuous.isClosedEmbedding hinjective

/-- Helper for Example 63.2: on affine source points the capped seed sphere is exactly
the chart image of the explicit button plane. -/
lemma framedBingButtonSphere_apply_affine (z : ℂ) :
    framedBingButtonSphere
        (complexOnePointSphereHomeomorph (z : OnePoint ℂ)) =
      realProdComplexOnePointSphereHomeomorph
        (framedBingButtonPlane z : OnePoint (ℝ × ℂ)) := by
  -- Cancel the source chart and evaluate `OnePoint.map` on an affine point.
  simp only [framedBingButtonSphere, Homeomorph.symm_apply_apply, OnePoint.map_some]

/-- Helper for Example 63.2: the capped seed sphere sends the compactification point to
the ambient compactification point. -/
lemma framedBingButtonSphere_apply_infinity :
    framedBingButtonSphere
        (complexOnePointSphereHomeomorph (OnePoint.infty : OnePoint ℂ)) =
      realProdComplexOnePointSphereHomeomorph
        (OnePoint.infty : OnePoint (ℝ × ℂ)) := by
  -- Cancel the source chart and use that `OnePoint.map` fixes infinity.
  simp only [framedBingButtonSphere, Homeomorph.symm_apply_apply, OnePoint.map_infty]

/-- Helper for Example 63.2: the braided annulus parameterization viewed in the affine
three-dimensional model. -/
noncomputable def framedBingLateralAnnulusPoint (i : Fin 3)
    (z : closedRadialAnnulus (framedBingMarkedPoint i) (1 / 32) (1 / 16)) :
    ℝ × ℂ :=
  let p : unitInterval × ℂ := framedBingLateralAnnulusHomeomorph i z
  ((p.1 : ℝ), p.2)

/-- Helper for Example 63.2: the affine braided-annulus parameterization agrees with the
bottom plane on its outer attaching circle. -/
lemma framedBingLateralAnnulusPoint_apply_outer (i : Fin 3)
    (z : closedRadialAnnulus (framedBingMarkedPoint i) (1 / 32) (1 / 16))
    (hz : dist (z : ℂ) (framedBingMarkedPoint i) = 1 / 16) :
    framedBingLateralAnnulusPoint i z = (0, (z : ℂ)) := by
  -- Project the already normalized cylinder equation to the affine product.
  change
    ((((framedBingLateralAnnulusHomeomorph i z :
      framedBingTubeLateralBoundary i) : unitInterval × ℂ).1 : ℝ),
      ((framedBingLateralAnnulusHomeomorph i z :
        framedBingTubeLateralBoundary i) : unitInterval × ℂ).2) =
      (0, (z : ℂ))
  rw [framedBingLateralAnnulusHomeomorph_apply_outer i z hz]
  rfl

/-- Helper for Example 63.2: the affine braided-annulus parameterization agrees with the
normalized flat cap on its inner attaching circle. -/
lemma framedBingLateralAnnulusPoint_apply_inner (i : Fin 3)
    (z : closedRadialAnnulus (framedBingMarkedPoint i) (1 / 32) (1 / 16))
    (hz : dist (z : ℂ) (framedBingMarkedPoint i) = 1 / 32) :
    framedBingLateralAnnulusPoint i z =
      (1, framedBingMarkedPoint i + (2 : ℝ) •
        ((z : ℂ) - framedBingMarkedPoint i)) := by
  -- Project the terminal cylinder equation to the affine product.
  change
    ((((framedBingLateralAnnulusHomeomorph i z :
      framedBingTubeLateralBoundary i) : unitInterval × ℂ).1 : ℝ),
      ((framedBingLateralAnnulusHomeomorph i z :
        framedBingTubeLateralBoundary i) : unitInterval × ℂ).2) =
      (1, framedBingMarkedPoint i + (2 : ℝ) •
        ((z : ℂ) - framedBingMarkedPoint i))
  rw [framedBingLateralAnnulusHomeomorph_apply_inner i z hz]
  rfl

/-- Helper for Example 63.2: the boundary-normalized capped Bing patch replaces the two
outer marked disks by their braided lateral annuli and flat terminal caps. -/
noncomputable def framedBingCappedPatch (z : ℂ) : ℝ × ℂ :=
  @dite (ℝ × ℂ)
    (z ∈ Metric.closedBall (framedBingMarkedPoint 0) (1 / 32))
    (Classical.propDecidable _)
    (fun _ ↦
      (1, framedBingMarkedPoint 0 + (2 : ℝ) • (z - framedBingMarkedPoint 0)))
    (fun _ ↦
      @dite (ℝ × ℂ)
        (z ∈ Metric.closedBall (framedBingMarkedPoint 2) (1 / 32))
        (Classical.propDecidable _)
        (fun _ ↦
          (1, framedBingMarkedPoint 2 + (2 : ℝ) • (z - framedBingMarkedPoint 2)))
        (fun _ ↦
          @dite (ℝ × ℂ)
            (z ∈ closedRadialAnnulus
              (framedBingMarkedPoint 0) (1 / 32) (1 / 16))
            (Classical.propDecidable _)
            (fun h₀a ↦ framedBingLateralAnnulusPoint 0 ⟨z, h₀a⟩)
            (fun _ ↦
              @dite (ℝ × ℂ)
                (z ∈ closedRadialAnnulus
                  (framedBingMarkedPoint 2) (1 / 32) (1 / 16))
                (Classical.propDecidable _)
                (fun h₂a ↦ framedBingLateralAnnulusPoint 2 ⟨z, h₂a⟩)
                (fun _ ↦ (0, z)))))

/-- Helper for Example 63.2: the capped Bing patch has the normalized flat left cap on
the inner left disk. -/
lemma framedBingCappedPatch_apply_leftCap {z : ℂ}
    (hz : z ∈ Metric.closedBall (framedBingMarkedPoint 0) (1 / 32)) :
    framedBingCappedPatch z =
      (1, framedBingMarkedPoint 0 + (2 : ℝ) • (z - framedBingMarkedPoint 0)) := by
  -- The left cap is the first branch of the normalized finite gluing.
  simp only [framedBingCappedPatch, dif_pos hz]

/-- Helper for Example 63.2: the capped Bing patch has the normalized flat right cap on
the inner right disk. -/
lemma framedBingCappedPatch_apply_rightCap {z : ℂ}
    (hz : z ∈ Metric.closedBall (framedBingMarkedPoint 2) (1 / 32)) :
    framedBingCappedPatch z =
      (1, framedBingMarkedPoint 2 + (2 : ℝ) • (z - framedBingMarkedPoint 2)) := by
  -- The two inner cap disks are disjoint, so the preceding left branch is inactive.
  have hdisjoint : Disjoint
      (Metric.closedBall (framedBingMarkedPoint 0) (1 / 32))
      (Metric.closedBall (framedBingMarkedPoint 2) (1 / 32)) := by
    apply Metric.closedBall_disjoint_closedBall
    simp only [framedBingMarkedPoint, Matrix.cons_val_zero, Matrix.cons_val_two]
    norm_num [Complex.dist_eq, Complex.norm_real]
  have hnotLeft : z ∉ Metric.closedBall (framedBingMarkedPoint 0) (1 / 32) := by
    intro hleft
    exact Set.disjoint_left.mp hdisjoint hleft hz
  simp only [framedBingCappedPatch, dif_neg hnotLeft, dif_pos hz]

/-- Helper for Example 63.2: away from the two outer attaching disks, the capped Bing
patch is the unchanged bottom plane. -/
lemma framedBingCappedPatch_apply_of_outside_outerDisks {z : ℂ}
    (hleft : z ∉ Metric.closedBall (framedBingMarkedPoint 0) (1 / 16))
    (hright : z ∉ Metric.closedBall (framedBingMarkedPoint 2) (1 / 16)) :
    framedBingCappedPatch z = (0, z) := by
  -- Inner caps lie in the outer disks, while each annulus stores outer-disk membership.
  have hinnerLeft : z ∉ Metric.closedBall (framedBingMarkedPoint 0) (1 / 32) := by
    intro hz
    apply hleft
    rw [Metric.mem_closedBall] at hz ⊢
    exact hz.trans (by norm_num)
  have hinnerRight : z ∉ Metric.closedBall (framedBingMarkedPoint 2) (1 / 32) := by
    intro hz
    apply hright
    rw [Metric.mem_closedBall] at hz ⊢
    exact hz.trans (by norm_num)
  have hannulusLeft : z ∉
      closedRadialAnnulus (framedBingMarkedPoint 0) (1 / 32) (1 / 16) := by
    intro hz
    exact hleft (closedRadialAnnulus_subset_closedBall
      (framedBingMarkedPoint 0) (1 / 32) (1 / 16) hz)
  have hannulusRight : z ∉
      closedRadialAnnulus (framedBingMarkedPoint 2) (1 / 32) (1 / 16) := by
    intro hz
    exact hright (closedRadialAnnulus_subset_closedBall
      (framedBingMarkedPoint 2) (1 / 32) (1 / 16) hz)
  rw [framedBingCappedPatch, dif_neg hinnerLeft, dif_neg hinnerRight,
    dif_neg hannulusLeft, dif_neg hannulusRight]

/-- Helper for Example 63.2: retaining the frontier of a closed obstacle makes its old
complement a clopen region inside the refined complement. -/
lemma isClopen_complPreimage_of_frontier_subset
    {X : Type*} [TopologicalSpace X] {K K' : Set X}
    (hK : IsClosed K) (hfrontier : frontier K ⊆ K') :
    IsClopen {x : ↑(K'ᶜ) | (x : X) ∈ Kᶜ} := by
  -- Apply the induced-topology criterion to the open old complement.
  apply isClopen_preimage_val hK.isOpen_compl
  rw [frontier_compl]
  -- A retained frontier cannot meet the refined complement.
  exact Set.disjoint_left.mpr (fun _ hx hx' ↦ hx' (hfrontier hx))

/-- Helper for Example 63.2: a split copy in an obstacle complement extends across any
refinement that retains the old frontier, without changing the ambient section. -/
lemma thetaSplitComplement_of_frontier_subset
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {K K' : Set X} (hK : IsClosed K) (hsub : K' ⊆ K)
    (hfrontier : frontier K ⊆ K') (z₀ : Z)
    (s : C(Z, ↑(Kᶜ))) (q : C(↑(Kᶜ), Z))
    (hq : ∀ z, q (s z) = z) :
    ∃ (s' : C(Z, ↑(K'ᶜ))) (q' : C(↑(K'ᶜ), Z)),
      (∀ z, (s' z : X) = s z) ∧ ∀ z, q' (s' z) = z := by
  classical
  -- The old complement includes continuously into the larger refined complement.
  let inclusion : C(↑(Kᶜ), ↑(K'ᶜ)) :=
    ContinuousMap.inclusion (Set.compl_subset_compl.mpr hsub)
  let s' : C(Z, ↑(K'ᶜ)) := inclusion.comp s
  let oldRegion : Set ↑(K'ᶜ) := {x | (x : X) ∈ Kᶜ}
  have hOldRegion : IsClopen oldRegion :=
    isClopen_complPreimage_of_frontier_subset hK hfrontier
  -- On the clopen old region use the original detector, and use a constant elsewhere.
  let q'Fun : ↑(K'ᶜ) → Z := fun x ↦
    if hx : (x : X) ∈ Kᶜ then q ⟨x, hx⟩ else z₀
  have hqOld : ContinuousOn q'Fun oldRegion := by
    rw [continuousOn_iff_continuous_restrict]
    let toOld : C(oldRegion, ↑(Kᶜ)) :=
      ⟨fun x ↦ ⟨(x : X), x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    have hcontinuous : Continuous (q.comp toOld) := (q.comp toOld).continuous
    have hrestricted : oldRegion.restrict q'Fun = q.comp toOld := by
      funext x
      have hxOld : (x : X) ∈ Kᶜ := x.property
      simp only [Set.restrict_apply, q'Fun, dif_pos hxOld,
        ContinuousMap.comp_apply]
      apply congrArg q
      exact Subtype.ext (congrArg Subtype.val rfl)
    rw [hrestricted]
    exact hcontinuous
  have hqNew : ContinuousOn q'Fun oldRegionᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    have hconstant : Continuous (fun _ : ↑(oldRegionᶜ) ↦ z₀) := continuous_const
    have hrestricted : oldRegionᶜ.restrict q'Fun = fun _ : ↑(oldRegionᶜ) ↦ z₀ := by
      funext x
      have hxNew : (x : X) ∉ Kᶜ := by
        intro hxOld
        exact x.property hxOld
      simp only [Set.restrict_apply, q'Fun, dif_neg hxNew]
    rw [hrestricted]
    exact hconstant
  have hq'Continuous : Continuous q'Fun := by
    rw [← continuousOn_univ]
    rw [← Set.union_compl_self oldRegion]
    exact hqOld.union_of_isClosed hqNew hOldRegion.isClosed
      hOldRegion.isOpen.isClosed_compl
  let q' : C(↑(K'ᶜ), Z) := ⟨q'Fun, hq'Continuous⟩
  refine ⟨s', q', ?_, ?_⟩
  · -- The inclusion changes only the subtype proof, never the ambient point.
    intro z
    rfl
  · -- Every section value lies in the old clopen region, so the old left inverse applies.
    intro z
    have hsMem : ((s' z : ↑(K'ᶜ)) : X) ∈ Kᶜ := (s z).property
    change (if hx : ((s' z : ↑(K'ᶜ)) : X) ∈ Kᶜ then
      q ⟨s' z, hx⟩ else z₀) = z
    rw [dif_pos hsMem]
    have hsectionValue : (⟨s' z, hsMem⟩ : ↑(Kᶜ)) = s z := by
      apply Subtype.ext
      exact congrArg Subtype.val rfl
    rw [hsectionValue]
    exact hq z

/-- Helper for Example 63.2: a recursively refined framed Bing sphere sequence records the
geometric estimates and persistent meridian needed before taking its uniform limit. -/
structure FramedBingSphereStageSequence (replacement : ContractingBingReplacement) where
  geometricConstant : ℝ
  stageMap : ℕ → StandardSphere 2 → StandardSphere 3
  stageMap_continuous : ∀ n, Continuous (stageMap n)
  stageMap_step : ∀ n x,
    dist (stageMap n x) (stageMap (n + 1) x) ≤
      geometricConstant * replacement.contraction ^ n
  stageMap_eventually_separated : ∀ x y : StandardSphere 2, x ≠ y →
    ∃ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
      ε ≤ dist (stageMap n x) (stageMap n y)
  obstacle : ℕ → Set (StandardSphere 3)
  obstacle_closed : ∀ n, IsClosed (obstacle n)
  obstacle_antitone : Antitone obstacle
  stageMap_range : ∀ n, Set.range (stageMap n) ⊆ obstacle n
  obstacle_eventually_approximated : ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    ∀ y, y ∈ obstacle n → ∃ x, dist y (stageMap n x) < ε
  limitBase : StandardSphere 3
  limitBase_mem_stage : ∀ n, limitBase ∈ (obstacle n)ᶜ
  stageMeridian : ∀ n,
    Path (⟨limitBase, limitBase_mem_stage n⟩ : {p // p ∈ (obstacle n)ᶜ})
      ⟨limitBase, limitBase_mem_stage n⟩
  stageMeridian_ambient : ∀ n t,
    (stageMeridian n t : StandardSphere 3) = (stageMeridian 0 t : StandardSphere 3)
  stageMeridian_class_ne_one : ∀ n,
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (stageMeridian n)) ≠ 1

/-- Helper for Example 63.2: geometric displacement and first-divergence separation give a
continuous injective uniform limit of a framed Bing sphere stage sequence. -/
lemma FramedBingSphereStageSequence.exists_limit
    {replacement : ContractingBingReplacement}
    (S : FramedBingSphereStageSequence replacement) :
    ∃ f : StandardSphere 2 → StandardSphere 3,
      Continuous f ∧ Function.Injective f ∧
        TendstoUniformly S.stageMap f Filter.atTop := by
  -- Apply the generic geometric-step limit theorem with the replacement's contraction ratio.
  exact existsContinuousInjectiveTendstoUniformlyOfGeometricStep
    S.stageMap S.geometricConstant replacement.contraction
    replacement.contraction_pos.le replacement.contraction_lt_one
    S.stageMap_continuous S.stageMap_step
    S.stageMap_eventually_separated

/-- Helper for Example 63.2: a quantitative framed Bing sphere sequence supplies all fields
of the directly convergent horn-stage interface. -/
lemma FramedBingSphereStageSequence.toConvergentBingHornStages
    {replacement : ContractingBingReplacement}
    (S : FramedBingSphereStageSequence replacement) :
    Nonempty ConvergentBingHornStages := by
  -- First take the uniform limit; its continuity and injectivity have already been isolated.
  obtain ⟨limitMap, _limitMapContinuous, limitMapInjective, stageMapTendsto⟩ :=
    S.exists_limit
  -- The remaining fields are stable projections of the finite-stage construction.
  exact ⟨{
    stageMap := S.stageMap
    limitMap := limitMap
    stageMap_continuous := S.stageMap_continuous
    stageMap_tendsto := stageMapTendsto
    limitMap_injective := limitMapInjective
    obstacle := S.obstacle
    obstacle_closed := S.obstacle_closed
    obstacle_antitone := S.obstacle_antitone
    stageMap_range := S.stageMap_range
    obstacle_eventually_approximated := S.obstacle_eventually_approximated
    limitBase := S.limitBase
    limitBase_mem_stage := S.limitBase_mem_stage
    stageMeridian := S.stageMeridian
    stageMeridian_ambient := S.stageMeridian_ambient
    stageMeridian_class_ne_one := S.stageMeridian_class_ne_one
  }⟩

/-- Helper for Example 63.2: iterated boundary-normalized Bing replacements produce the
quantitative framed sphere stage sequence. -/
theorem ContractingBingReplacement.framedBingSphereStageSequence_nonempty
    (replacement : ContractingBingReplacement) :
    Nonempty (FramedBingSphereStageSequence replacement) :=
  -- Route correction: the prior set-level horn patch had no parameterization suitable for
  -- gluing.  The capped patch and retained-frontier detector extension above now provide that
  -- owner interface; what remains is the address-indexed closed-embedding refinement itself.
  -- TODO: recursively glue the relative horn patch into every active flat cap.  The missing
  -- geometric step must prove seam agreement, nested closed obstacles, geometric mesh bounds,
  -- first-divergence separation, and persistence of the fixed theta-bearing complement region.
  sorry

/-- Helper for Example 63.2: a contracting local replacement compiles, by relative binary
refinement and compactification, to directly convergent Bing horn stages. -/
theorem ContractingBingReplacement.toConvergentBingHornStages
    (replacement : ContractingBingReplacement) :
    Nonempty ConvergentBingHornStages := by
  -- Route correction: isolate the recursive cap geometry in a quantitative sequence and let
  -- the generic geometric-step theorem construct the limit instead of assembling it here.
  obtain ⟨stages⟩ := replacement.framedBingSphereStageSequence_nonempty
  -- Compile the verified finite-stage projections into the existing convergence interface.
  exact stages.toConvergentBingHornStages

/-- Helper for Example 63.2: recursively scaled Euclidean framed Bing blocks, compactified
at infinity, supply the directly convergent stage data. -/
theorem convergentBingHornStages_nonempty : Nonempty ConvergentBingHornStages := by
  -- Compile the proved local replacement through the isolated relative-refinement interface.
  obtain ⟨replacement⟩ := contractingFramedBingReplacement_nonempty
  exact replacement.toConvergentBingHornStages

/-- Helper for Example 63.2: the compactified convergent Bing blocks form a stage system
with one persistent nonabelian detector class. -/
theorem bingHornStageSystem_nonempty : Nonempty BingHornStageSystem := by
  -- Compile the direct convergence data; all limit and component plumbing is isolated above.
  obtain ⟨S⟩ := convergentBingHornStages_nonempty
  exact S.toBingHornStageSystem

/-- Helper for Example 63.2: the recursive Bing-double construction produces a nonabelian
linked-horn approximation. -/
theorem nonabelianLinkedHornApproximation_exists :
    Nonempty NonabelianLinkedHornApproximation := by
  -- Route correction: the round-core circle phase is only an abelian local-clearance tool;
  -- it cannot certify a persistent meridian in a sphere complement. The geometric-step API now
  -- supplies the continuous injective uniform limit once a genuinely nonabelian Bing-stage
  -- family provides displacement and first-divergence estimates.
  -- The strict-collar construction above now upgrades pointwise braid closure to an explicit
  -- product-cylinder homeomorphism: it fixes the initial face, fixes uniform endpoint disks,
  -- has compact support, and carries the three seed cylinders to pairwise disjoint tubes.
  -- The named tube API now also supplies exact boundary slices, a `3 / 2` diameter bound, a
  -- closed two-child obstacle, and an explicit parent meridian in its complement.
  -- The recursive geometry is isolated in the stage-system constructor; the conversion above
  -- derives continuity, injectivity, and every finite nonidentity obstruction uniformly.
  obtain ⟨S⟩ := bingHornStageSystem_nonempty
  exact ⟨S.toNonabelianLinkedHornApproximation⟩

end AlexanderHornGeometry

/-- Helper for Example 63.2: the geometric Alexander construction supplies an embedded
sphere and a non-nullhomotopic meridian in one complementary component. -/
theorem alexanderHornedSphere_meridianCertificate :
    ∃ (f : StandardSphere 2 → StandardSphere 3) (x : StandardSphere 3)
      (hx : x ∈ (Set.range f)ᶜ), Topology.IsEmbedding f ∧
        ∃ μ : Path
            (⟨x, mem_connectedComponentIn hx⟩ :
              {y // y ∈ connectedComponentIn (Set.range f)ᶜ x})
            ⟨x, mem_connectedComponentIn hx⟩,
          ¬ Path.Homotopic μ
            (Path.refl (⟨x, mem_connectedComponentIn hx⟩ :
              {y // y ∈ connectedComponentIn (Set.range f)ᶜ x})) := by
  -- Route correction: isolate the recursive geometry in a stable approximation interface;
  -- the certificate itself now uses only its embedding and compact-factorization consequences.
  obtain ⟨A⟩ := AlexanderHornGeometry.nonabelianLinkedHornApproximation_exists
  refine ⟨A.limitMap, A.limitBase, A.limitBase_mem, A.limitEmbedding,
    A.limitMeridian, ?_⟩
  exact A.limitMeridian_notNullhomotopic

/-- Helper for Example 63.2: the Alexander construction supplies an embedded sphere and a
complementary component with a nontrivial based fundamental group. -/
theorem alexanderHornedSphere_piOneCertificate :
    ∃ (f : StandardSphere 2 → StandardSphere 3) (x : StandardSphere 3)
      (hx : x ∈ (Set.range f)ᶜ), Topology.IsEmbedding f ∧
        ∃ g h : FundamentalGroup (connectedComponentIn (Set.range f)ᶜ x)
          ⟨x, mem_connectedComponentIn hx⟩, g ≠ h := by
  -- Convert the geometric meridian obstruction into two distinct fundamental-group elements.
  obtain ⟨f, x, hx, hf, μ, hμ⟩ := alexanderHornedSphere_meridianCertificate
  refine ⟨f, x, hx, hf,
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk μ), 1, ?_⟩
  exact fundamentalGroup_fromPath_ne_one_of_not_homotopic μ hμ

/-- Helper for Example 63.2: the certified complement component is not simply connected. -/
lemma hornedSphereComplementComponent_notSimplyConnected
    (f : StandardSphere 2 → StandardSphere 3) (x : StandardSphere 3)
    (hx : x ∈ (Set.range f)ᶜ)
    (g h : FundamentalGroup (connectedComponentIn (Set.range f)ᶜ x)
      ⟨x, mem_connectedComponentIn hx⟩) (hgh : g ≠ h) :
    ¬ IsSimplyConnected (connectedComponentIn (Set.range f)ᶜ x) := by
  -- Apply the generic obstruction at the canonical component basepoint.
  exact not_isSimplyConnected_of_fundamentalGroup_ne
    (connectedComponentIn (Set.range f)ᶜ x) ⟨x, mem_connectedComponentIn hx⟩ g h hgh

/-- Example 63.2: There is a homeomorphic image of the standard two-sphere in
the standard three-sphere with a complementary domain that is not simply connected. -/
theorem alexanderHornedSphere_exists :
    ∃ C U : Set (StandardSphere 3), Nonempty (C ≃ₜ StandardSphere 2) ∧
      IsConnectedComponentIn Cᶜ U ∧ ¬ IsSimplyConnected U := by
  -- Unpack the geometric construction through its stable embedding and π₁ interface.
  obtain ⟨f, x, hx, hf, g, h, hgh⟩ := alexanderHornedSphere_piOneCertificate
  refine ⟨Set.range f, connectedComponentIn (Set.range f)ᶜ x, ?_, ?_, ?_⟩
  · exact hornedSphereRange_homeomorph f hf
  · exact IsConnectedComponentIn.of_mem hx
  · exact hornedSphereComplementComponent_notSimplyConnected f x hx g h hgh
