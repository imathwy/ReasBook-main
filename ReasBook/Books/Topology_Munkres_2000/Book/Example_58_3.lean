module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Example_58_3.PlaneModels
public import Topology_Munkres_2000.Book.Theorem_58_3
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import Topology_Munkres_2000.Book.Example_58_2
import Topology_Munkres_2000.Book.Proposition_58_2.HomotopyEquiv
import all Topology_Munkres_2000.Book.Definition_53_5.FigureEight
import all Topology_Munkres_2000.Book.Example_58_2.PlanarFigureEight
import all Topology_Munkres_2000.Book.Example_58_3.PlaneModels
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Euclidean.Sphere.Basic

public section

noncomputable section

open scoped Pointwise

/-- Helper for Example 58.3: the figure-eight carrier is closed in the torus. -/
private theorem isClosed_figureEightCarrier : IsClosed FigureEight.carrier := by
  -- Write the two coordinate circles as closed equality loci.
  have hcarrier : FigureEight.carrier =
      {z : Torus | z.2 = 1} ∪ {z : Torus | z.1 = 1} := by
    ext z
    rw [FigureEight.mem_iff]
    simp only [Set.mem_union, Set.mem_setOf_eq]
  rw [hcarrier]
  exact (isClosed_eq continuous_snd continuous_const).union
    (isClosed_eq continuous_fst continuous_const)

/-- Helper for Example 58.3: the figure eight inherits compactness from the compact torus. -/
private theorem figureEightCompactSpace : CompactSpace FigureEight := by
  -- A closed subspace of a compact space is compact.
  exact isCompact_iff_compactSpace.mp isClosed_figureEightCarrier.isCompact

/-- Helper for Example 58.3: the coordinate difference realizes the abstract figure eight
as two tangent circles in the complex plane. -/
private def figureEightPlanarMap (x : FigureEight) : ℂ :=
  (x.1.1 - x.1.2) / 2

/-- Helper for Example 58.3: the planar realization of the figure eight is continuous. -/
private theorem continuous_figureEightPlanarMap : Continuous figureEightPlanarMap := by
  -- Continuity follows from the two coordinate projections and complex arithmetic.
  unfold figureEightPlanarMap
  fun_prop

/-- Helper for Example 58.3: two unit complex numbers whose sum is `2` are both `1`. -/
private theorem circle_eq_one_of_add_eq_two (z w : Circle)
    (hzw : (z : ℂ) + w = 2) : z = 1 ∧ w = 1 := by
  -- Real parts of unit complex numbers are at most one, so equality of their sum is rigid.
  have hRe : (z : ℂ).re + (w : ℂ).re = 2 := by
    simpa using congrArg Complex.re hzw
  have hzReLe : z.1.re ≤ 1 := by
    rw [← Circle.norm_coe z]
    exact Complex.re_le_norm z
  have hwReLe : w.1.re ≤ 1 := by
    rw [← Circle.norm_coe w]
    exact Complex.re_le_norm w
  have hzRe : z.1.re = 1 := by
    nlinarith
  have hwRe : w.1.re = 1 := by
    nlinarith
  have hzComplex : (z : ℂ) = 1 := by
    have hzNormSq : z.1.re * z.1.re + z.1.im * z.1.im = 1 := by
      simpa [Complex.normSq_apply] using Circle.normSq_coe z
    apply Complex.ext
    · simpa using hzRe
    · simp only [Complex.one_im]
      nlinarith [sq_nonneg z.1.im]
  have hwComplex : (w : ℂ) = 1 := by
    have hwNormSq : w.1.re * w.1.re + w.1.im * w.1.im = 1 := by
      simpa [Complex.normSq_apply] using Circle.normSq_coe w
    apply Complex.ext
    · simpa using hwRe
    · simp only [Complex.one_im]
      nlinarith [sq_nonneg w.1.im]
  constructor
  · exact Circle.ext hzComplex
  · exact Circle.ext hwComplex

/-- Helper for Example 58.3: the planar coordinate realization separates points of the
abstract figure eight. -/
private theorem injective_figureEightPlanarMap :
    Function.Injective figureEightPlanarMap := by
  -- On equal branches cancellation is immediate; across branches the two unit coordinates
  -- can meet only at their common basepoint.
  intro x y hxy
  have htwo : (2 : ℂ) ≠ 0 := by
    norm_num
  have hdiff : (x.1.1 : ℂ) - x.1.2 = (y.1.1 : ℂ) - y.1.2 := by
    exact (div_left_inj' htwo).mp hxy
  rcases (FigureEight.mem_iff x.1).mp x.2 with hx | hx
  · rcases (FigureEight.mem_iff y.1).mp y.2 with hy | hy
    · apply Subtype.ext
      apply Prod.ext
      · apply Circle.ext
        rw [hx, hy] at hdiff
        exact sub_left_inj.mp hdiff
      · exact hx.trans hy.symm
    · have hsum : (x.1.1 : ℂ) + y.1.2 = 2 := by
        calc
          (x.1.1 : ℂ) + y.1.2 = ((x.1.1 : ℂ) - 1) + (1 + y.1.2) := by ring
          _ = (1 - (y.1.2 : ℂ)) + (1 + y.1.2) := by
            simpa [hx, hy] using congrArg (fun z : ℂ ↦ z + (1 + y.1.2)) hdiff
          _ = 2 := by ring
      obtain ⟨hxOne, hyOne⟩ := circle_eq_one_of_add_eq_two x.1.1 y.1.2 hsum
      apply Subtype.ext
      apply Prod.ext
      · exact hxOne.trans hy.symm
      · exact hx.trans hyOne.symm
  · rcases (FigureEight.mem_iff y.1).mp y.2 with hy | hy
    · have hdiff' : (1 : ℂ) - x.1.2 = (y.1.1 : ℂ) - 1 := by
        simpa [hx, hy] using hdiff
      have hsum : (x.1.2 : ℂ) + y.1.1 = 2 := by
        calc
          (x.1.2 : ℂ) + y.1.1 = (1 - (1 - (x.1.2 : ℂ))) + y.1.1 := by ring
          _ = (1 - ((y.1.1 : ℂ) - 1)) + y.1.1 := by rw [hdiff']
          _ = 2 := by ring
      obtain ⟨hxOne, hyOne⟩ := circle_eq_one_of_add_eq_two x.1.2 y.1.1 hsum
      apply Subtype.ext
      apply Prod.ext
      · exact hx.trans hyOne.symm
      · exact hxOne.trans hy.symm
    · apply Subtype.ext
      apply Prod.ext
      · exact hx.trans hy.symm
      · apply Circle.ext
        rw [hx, hy] at hdiff
        exact sub_right_inj.mp hdiff

/-- Helper for Example 58.3: the planar coordinate realization is a topological embedding. -/
private theorem isEmbedding_figureEightPlanarMap :
    Topology.IsEmbedding figureEightPlanarMap := by
  -- Compactness of the domain upgrades the continuous injection to a closed embedding.
  letI : CompactSpace FigureEight := figureEightCompactSpace
  exact (continuous_figureEightPlanarMap.isClosedEmbedding
    injective_figureEightPlanarMap).isEmbedding

/-- Helper for Example 58.3: the two normalized punctures are distinct. -/
private theorem normalizedPunctures_ne :
    DoublyPuncturedPlane.leftPuncture ≠ DoublyPuncturedPlane.rightPuncture := by
  -- The chosen punctures are the distinct real points `-1 / 2` and `1 / 2`.
  unfold DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture
  norm_num

/-- Helper for Example 58.3: the normalized punctures are distance one apart. -/
private theorem normalizedPunctures_dist :
    dist DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture = 1 := by
  -- Compute the distance between the two real points directly in `ℂ`.
  unfold DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture
  rw [Complex.dist_eq]
  norm_num

/-- Helper for Example 58.3: the reversed distance between the normalized punctures is one. -/
private theorem normalizedPunctures_dist_rev :
    dist DoublyPuncturedPlane.rightPuncture DoublyPuncturedPlane.leftPuncture = 1 := by
  -- Symmetry reduces the reversed distance to the preceding computation.
  calc
    dist DoublyPuncturedPlane.rightPuncture DoublyPuncturedPlane.leftPuncture =
        dist DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture :=
      dist_comm _ _
    _ = 1 := normalizedPunctures_dist

/-- Helper for Example 58.3: the coordinate realization has precisely the normalized planar
figure-eight carrier as its range. -/
private theorem range_figureEightPlanarMap :
    Set.range figureEightPlanarMap =
      PlanarFigureEight.carrier DoublyPuncturedPlane.leftPuncture
        DoublyPuncturedPlane.rightPuncture := by
  -- Each coordinate-circle branch maps to one of the two normalized Euclidean circles.
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [PlanarFigureEight.mem_carrier_iff]
    rcases (FigureEight.mem_iff x.1).mp x.2 with hx | hx
    · left
      calc
        dist (figureEightPlanarMap x) DoublyPuncturedPlane.leftPuncture =
            ‖(x.1.1 : ℂ) / 2‖ := by
              rw [Complex.dist_eq]
              unfold figureEightPlanarMap DoublyPuncturedPlane.leftPuncture
              rw [hx]
              simp only [Circle.coe_one]
              congr 1
              ring
        _ = ‖(x.1.1 : ℂ)‖ / ‖(2 : ℂ)‖ := norm_div _ _
        _ = dist DoublyPuncturedPlane.leftPuncture
              DoublyPuncturedPlane.rightPuncture / 2 := by
                rw [Circle.norm_coe, normalizedPunctures_dist]
                norm_num
    · right
      calc
        dist (figureEightPlanarMap x) DoublyPuncturedPlane.rightPuncture =
            ‖-(x.1.2 : ℂ) / 2‖ := by
              rw [Complex.dist_eq]
              unfold figureEightPlanarMap DoublyPuncturedPlane.rightPuncture
              rw [hx]
              simp only [Circle.coe_one]
              congr 1
              ring
        _ = ‖(x.1.2 : ℂ)‖ / ‖(2 : ℂ)‖ := by rw [norm_div, norm_neg]
        _ = dist DoublyPuncturedPlane.leftPuncture
              DoublyPuncturedPlane.rightPuncture / 2 := by
                rw [Circle.norm_coe, normalizedPunctures_dist]
                norm_num
  · intro hz
    rw [PlanarFigureEight.mem_carrier_iff] at hz
    rcases hz with hz | hz
    · have hzNorm : ‖(2 : ℂ) * z + 1‖ = 1 := by
        have hcenter : ‖z + 1 / 2‖ = 1 / 2 := by
          rw [← normalizedPunctures_dist, ← hz]
          rw [Complex.dist_eq]
          unfold DoublyPuncturedPlane.leftPuncture
          congr 1
          ring
        calc
          ‖(2 : ℂ) * z + 1‖ = ‖(2 : ℂ) * (z + 1 / 2)‖ := by
            congr 1
            ring
          _ = ‖(2 : ℂ)‖ * ‖z + 1 / 2‖ := norm_mul _ _
          _ = 1 := by rw [hcenter]; norm_num
      let u : Circle := ⟨(2 : ℂ) * z + 1, mem_sphere_zero_iff_norm.mpr hzNorm⟩
      have hxMem : ((u, 1) : Torus) ∈ FigureEight.carrier := by
        exact (FigureEight.mem_iff _).mpr (Or.inl rfl)
      let x : FigureEight := ⟨(u, 1), hxMem⟩
      refine ⟨x, ?_⟩
      unfold figureEightPlanarMap x u
      simp only [Circle.coe_one]
      ring
    · have hzNorm : ‖1 - (2 : ℂ) * z‖ = 1 := by
        have hcenter : ‖z - 1 / 2‖ = 1 / 2 := by
          rw [← normalizedPunctures_dist, ← hz]
          rw [Complex.dist_eq]
          unfold DoublyPuncturedPlane.rightPuncture
          congr 1
        calc
          ‖1 - (2 : ℂ) * z‖ = ‖-(2 : ℂ) * (z - 1 / 2)‖ := by
            congr 1
            ring
          _ = ‖(2 : ℂ)‖ * ‖z - 1 / 2‖ := by rw [norm_mul, norm_neg]
          _ = 1 := by rw [hcenter]; norm_num
      let v : Circle := ⟨1 - (2 : ℂ) * z, mem_sphere_zero_iff_norm.mpr hzNorm⟩
      have hxMem : (((1 : Circle), v) : Torus) ∈ FigureEight.carrier := by
        exact (FigureEight.mem_iff _).mpr (Or.inr rfl)
      let x : FigureEight := ⟨(1, v), hxMem⟩
      refine ⟨x, ?_⟩
      unfold figureEightPlanarMap x v
      simp only [Circle.coe_one]
      ring

/-- Helper for Example 58.3: every point of the normalized planar figure eight avoids both
punctures. -/
private theorem normalizedPlanarFigureEight_avoidsPunctures {z : ℂ}
    (hz : z ∈ PlanarFigureEight.carrier DoublyPuncturedPlane.leftPuncture
      DoublyPuncturedPlane.rightPuncture) :
    z ≠ DoublyPuncturedPlane.leftPuncture ∧
      z ≠ DoublyPuncturedPlane.rightPuncture := by
  -- At either center the two required sphere radii are respectively zero or one, never one half.
  rw [PlanarFigureEight.mem_carrier_iff] at hz
  constructor
  · intro hleft
    subst z
    rcases hz with hz | hz
    · rw [dist_self, normalizedPunctures_dist] at hz
      norm_num at hz
    · rw [normalizedPunctures_dist] at hz
      norm_num at hz
  · intro hright
    subst z
    rcases hz with hz | hz
    · rw [normalizedPunctures_dist_rev, normalizedPunctures_dist] at hz
      norm_num at hz
    · rw [dist_self, normalizedPunctures_dist] at hz
      norm_num at hz

/-- Helper for Example 58.3: the coordinate realization regarded as a map into the normalized
doubly punctured plane. -/
private def figureEightDoublyPuncturedMap (x : FigureEight) : DoublyPuncturedPlane :=
  ⟨figureEightPlanarMap x,
    normalizedPlanarFigureEight_avoidsPunctures
      (range_figureEightPlanarMap ▸ Set.mem_range_self x)⟩

/-- Helper for Example 58.3: coercing the punctured-plane realization recovers its planar
coordinate value. -/
private theorem coe_figureEightDoublyPuncturedMap (x : FigureEight) :
    (figureEightDoublyPuncturedMap x : ℂ) = figureEightPlanarMap x := by
  -- The codomain restriction changes only the stored puncture-avoidance proof.
  rfl

/-- Helper for Example 58.3: composing the punctured-plane realization with its subtype
projection is the original planar coordinate map. -/
private theorem subtypeVal_comp_figureEightDoublyPuncturedMap :
    Subtype.val ∘ figureEightDoublyPuncturedMap = figureEightPlanarMap := by
  -- Extensionality exposes the preceding pointwise coercion formula.
  funext x
  exact coe_figureEightDoublyPuncturedMap x

/-- Helper for Example 58.3: the punctured-plane coordinate realization remains an embedding. -/
private theorem isEmbedding_figureEightDoublyPuncturedMap :
    Topology.IsEmbedding figureEightDoublyPuncturedMap := by
  -- Composing with the ambient subtype inclusion recovers the verified planar embedding.
  have hcontinuous : Continuous figureEightDoublyPuncturedMap :=
    continuous_figureEightPlanarMap.subtype_mk _
  apply Topology.IsEmbedding.of_comp hcontinuous continuous_subtype_val
  rw [subtypeVal_comp_figureEightDoublyPuncturedMap]
  exact isEmbedding_figureEightPlanarMap

/-- Helper for Example 58.3: the punctured-plane realization has exactly the normalized planar
figure-eight retract as its range. -/
private theorem range_figureEightDoublyPuncturedMap :
    Set.range figureEightDoublyPuncturedMap =
      PlanarFigureEight.inComplement DoublyPuncturedPlane.leftPuncture
        DoublyPuncturedPlane.rightPuncture := by
  -- Compare both subtypes after projecting to the complex plane and use the planar range theorem.
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [PlanarFigureEight.mem_inComplement_iff]
    exact range_figureEightPlanarMap ▸ Set.mem_range_self x
  · intro hz
    have hzCarrier : (z : ℂ) ∈
        PlanarFigureEight.carrier DoublyPuncturedPlane.leftPuncture
          DoublyPuncturedPlane.rightPuncture :=
      (PlanarFigureEight.mem_inComplement_iff _ _ z).mp hz
    rw [← range_figureEightPlanarMap] at hzCarrier
    obtain ⟨x, hx⟩ := hzCarrier
    refine ⟨x, ?_⟩
    exact Subtype.ext hx

/-- Helper for Example 58.3: the abstract figure eight is homeomorphic to the normalized planar
figure-eight deformation retract. -/
private theorem figureEightHomeomorphNormalizedPlanarFigureEight :
    Nonempty
      (FigureEight ≃ₜ
        PlanarFigureEight.inComplement DoublyPuncturedPlane.leftPuncture
          DoublyPuncturedPlane.rightPuncture) := by
  -- Restrict the punctured-plane embedding to its computed range.
  exact ⟨isEmbedding_figureEightDoublyPuncturedMap.toHomeomorph.trans
    (Homeomorph.setCongr range_figureEightDoublyPuncturedMap)⟩

/-- Helper for Example 58.3: a subtype cut out inside a containing subtype is homeomorphic to
the same set viewed directly in the ambient space. -/
private def nestedSubtypeHomeomorph
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

/-- Helper for Example 58.3: every point of the planar theta carrier avoids the two normalized
punctures. -/
private theorem planarTheta_avoidsPunctures :
    PlanarTheta.carrier ⊆
      {z : ℂ | z ≠ DoublyPuncturedPlane.leftPuncture ∧
        z ≠ DoublyPuncturedPlane.rightPuncture} := by
  -- Neither real puncture lies on the unit circle or on the vertical diameter.
  intro z hz
  constructor
  · intro hleft
    subst z
    rw [PlanarTheta.mem_iff] at hz
    rcases hz with hz | hz
    · norm_num [DoublyPuncturedPlane.leftPuncture, Complex.norm_def] at hz
    · norm_num [DoublyPuncturedPlane.leftPuncture] at hz
  · intro hright
    subst z
    rw [PlanarTheta.mem_iff] at hz
    rcases hz with hz | hz
    · norm_num [DoublyPuncturedPlane.rightPuncture, Complex.norm_def] at hz
    · norm_num [DoublyPuncturedPlane.rightPuncture] at hz

/-- Helper for Example 58.3: the nested planar-theta retract is homeomorphic to the direct
planar theta carrier. -/
private def planarThetaRetractHomeomorph :
    PlanarTheta.inDoublyPuncturedPlane ≃ₜ PlanarTheta :=
  nestedSubtypeHomeomorph
    {z : ℂ | z ≠ DoublyPuncturedPlane.leftPuncture ∧
      z ≠ DoublyPuncturedPlane.rightPuncture}
    PlanarTheta.carrier planarTheta_avoidsPunctures

/-- Helper for Example 58.3: `HasNProngsAt n x` records `n` embedded arcs beginning at
`x` whose pairwise intersections consist only of `x`. -/
private def HasNProngsAt {X : Type*} [TopologicalSpace X] (n : ℕ) (x : X) : Prop :=
  ∃ γ : Fin n → C(unitInterval, X),
    (∀ i, γ i 0 = x) ∧
      (∀ i, Topology.IsEmbedding (γ i)) ∧
        ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {x}

/-- Helper for Example 58.3: an embedding preserves every finite embedded-prong
configuration. -/
private theorem HasNProngsAt.map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {x : X} {f : X → Y} (hf : Topology.IsEmbedding f)
    (hx : HasNProngsAt n x) : HasNProngsAt n (f x) := by
  -- Compose every prong with the embedding, retaining its initial point and injectivity.
  obtain ⟨γ, hstart, hembed, hmeet⟩ := hx
  let cf : C(X, Y) := ⟨f, hf.continuous⟩
  let δ : Fin n → C(unitInterval, Y) := fun i ↦ cf.comp (γ i)
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro i
    exact congrArg f (hstart i)
  · intro i
    exact hf.comp (hembed i)
  · intro i j hij
    -- Injectivity reflects a common image point back to the original pairwise intersection.
    ext y
    constructor
    · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have hst : γ i s = γ j t := by
        apply hf.injective
        exact hs.trans ht.symm
      have hsource : γ i s ∈ Set.range (γ i) ∩ Set.range (γ j) := by
        constructor
        · exact ⟨s, rfl⟩
        · exact ⟨t, hst.symm⟩
      rw [hmeet i j hij] at hsource
      have hbase : γ i s = x := Set.mem_singleton_iff.mp hsource
      exact Set.mem_singleton_iff.mpr (hs ▸ congrArg f hbase)
    · intro hy
      have hyBase : y = f x := Set.mem_singleton_iff.mp hy
      constructor
      · refine ⟨0, ?_⟩
        change f (γ i 0) = y
        rw [hstart i, hyBase]
      · refine ⟨0, ?_⟩
        change f (γ j 0) = y
        rw [hstart j, hyBase]

/-- Helper for Example 58.3: discarding prongs preserves a finite prong configuration. -/
private theorem HasNProngsAt.mono {X : Type*} [TopologicalSpace X] {m n : ℕ} {x : X}
    (hx : HasNProngsAt n x) (hmn : m ≤ n) : HasNProngsAt m x := by
  -- Restrict the indexed family along the canonical embedding `Fin m ↪ Fin n`.
  obtain ⟨γ, hstart, hembed, hmeet⟩ := hx
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  refine ⟨fun i ↦ γ (e i), ?_, ?_, ?_⟩
  · intro i
    exact hstart (e i)
  · intro i
    exact hembed (e i)
  · intro i j hij
    exact hmeet (e i) (e j) (fun heq ↦ hij (e.injective heq))

/-- Helper for Example 58.3: finitely many pairwise disjoint embedded prongs meet some
arbitrarily small metric sphere in pairwise distinct points. -/
private theorem HasNProngsAt.exists_injective_sphere_hits
    {X : Type*} [MetricSpace X] {n : ℕ} [NeZero n] {x : X}
    (hx : HasNProngsAt n x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧
      ∃ p : Fin n → X, Function.Injective p ∧ ∀ i, dist (p i) x = r := by
  -- Use the minimum endpoint distance to choose a radius reached by every prong.
  classical
  obtain ⟨γ, hstart, hembed, hmeet⟩ := hx
  let endpointDistance : Fin n → ℝ := fun i ↦ dist (γ i 1) x
  have hendpointDistance_pos (i : Fin n) : 0 < endpointDistance i := by
    dsimp only [endpointDistance]
    apply dist_pos.mpr
    intro hendpoint
    have hparameters : (1 : unitInterval) = 0 := by
      apply (hembed i).injective
      exact hendpoint.trans (hstart i).symm
    exact one_ne_zero hparameters
  let endpointDistances : Finset ℝ := Finset.univ.image endpointDistance
  have hdistances_nonempty : endpointDistances.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let minimumEndpointDistance : ℝ := endpointDistances.min' hdistances_nonempty
  have hminimum_pos : 0 < minimumEndpointDistance := by
    have hminimum_mem : minimumEndpointDistance ∈ endpointDistances :=
      endpointDistances.min'_mem hdistances_nonempty
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hminimum_mem
    rw [← hi]
    exact hendpointDistance_pos i
  let r : ℝ := min ε minimumEndpointDistance / 2
  have hr_pos : 0 < r := by
    dsimp only [r]
    positivity
  have hr_lt_ε : r < ε := by
    dsimp only [r]
    nlinarith [min_le_left ε minimumEndpointDistance]
  have hr_lt_endpoint (i : Fin n) : r < endpointDistance i := by
    have hiMem : endpointDistance i ∈ endpointDistances := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hminimum_le : minimumEndpointDistance ≤ endpointDistance i :=
      endpointDistances.min'_le _ hiMem
    dsimp only [r]
    nlinarith [min_le_right ε minimumEndpointDistance]
  have hexistsHit (i : Fin n) :
      ∃ t : unitInterval, dist (γ i t) x = r := by
    have hcontinuous : Continuous (fun t : unitInterval ↦ dist (γ i t) x) := by
      fun_prop
    have hrInterval : r ∈ Set.Icc (dist (γ i 0) x) (dist (γ i 1) x) := by
      rw [hstart i, dist_self]
      exact ⟨hr_pos.le, (hr_lt_endpoint i).le⟩
    exact intermediate_value_univ (0 : unitInterval) 1 hcontinuous hrInterval
  let hitParameter : Fin n → unitInterval := fun i ↦ Classical.choose (hexistsHit i)
  let hitPoint : Fin n → X := fun i ↦ γ i (hitParameter i)
  have hhitDistance (i : Fin n) : dist (hitPoint i) x = r := by
    exact Classical.choose_spec (hexistsHit i)
  have hhitInjective : Function.Injective hitPoint := by
    intro i j hp
    by_contra hij
    have hpointMem : hitPoint i ∈ Set.range (γ i) ∩ Set.range (γ j) := by
      constructor
      · exact ⟨hitParameter i, rfl⟩
      · exact ⟨hitParameter j, hp.symm⟩
    rw [hmeet i j hij] at hpointMem
    have hpointBase : hitPoint i = x := Set.mem_singleton_iff.mp hpointMem
    have hrZero : r = 0 := by
      rw [← hhitDistance i, hpointBase, dist_self]
    exact hr_pos.ne' hrZero
  exact ⟨r, hr_pos, hr_lt_ε, hitPoint, hhitInjective, hhitDistance⟩

/-- Helper for Example 58.3: three points common to the unit circle and a second nonconcentric
circle cannot be pairwise distinct. -/
private theorem eq_of_three_unitCircle_sphere_points
    {c p₀ p₁ p₂ : ℂ} {r : ℝ} (hc : (0 : ℂ) ≠ c) (hp₀p₁ : p₀ ≠ p₁)
    (hp₀norm : ‖p₀‖ = 1) (hp₁norm : ‖p₁‖ = 1) (hp₂norm : ‖p₂‖ = 1)
    (hp₀dist : dist p₀ c = r) (hp₁dist : dist p₁ c = r)
    (hp₂dist : dist p₂ c = r) : p₂ = p₀ ∨ p₂ = p₁ := by
  -- Apply the two-dimensional theorem that two distinct Euclidean circles meet at most twice.
  have hp₀zero : dist p₀ (0 : ℂ) = 1 := by
    simpa only [dist_zero_right] using hp₀norm
  have hp₁zero : dist p₁ (0 : ℂ) = 1 := by
    simpa only [dist_zero_right] using hp₁norm
  have hp₂zero : dist p₂ (0 : ℂ) = 1 := by
    simpa only [dist_zero_right] using hp₂norm
  exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    Complex.finrank_real_complex hc hp₀p₁ hp₀zero hp₁zero hp₂zero hp₀dist hp₁dist
      hp₂dist

/-- Helper for Example 58.3: distance between two points on the imaginary axis is the absolute
difference of their imaginary coordinates. -/
private theorem dist_eq_abs_im_sub_of_re_eq_zero {z w : ℂ}
    (hz : z.re = 0) (hw : w.re = 0) : dist z w = |z.im - w.im| := by
  -- Expand the complex norm; the real-coordinate contribution vanishes.
  rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, hz, hw]
  simp only [sub_self, zero_mul, zero_add]
  rw [← pow_two, Real.sqrt_sq_eq_abs]

/-- Helper for Example 58.3: three points of the imaginary axis on one metric sphere cannot be
pairwise distinct. -/
private theorem eq_of_three_vertical_sphere_points
    {c p₀ p₁ p₂ : ℂ} {r : ℝ}
    (hc : c.re = 0) (hp₀re : p₀.re = 0) (hp₁re : p₁.re = 0)
    (hp₂re : p₂.re = 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp₀dist : dist p₀ c = r) (hp₁dist : dist p₁ c = r)
    (hp₂dist : dist p₂ c = r) : p₂ = p₀ ∨ p₂ = p₁ := by
  -- Project to the real line, where a metric sphere is the pair `c.im ± r`.
  have hr : 0 ≤ r := by
    rw [← hp₀dist]
    exact dist_nonneg
  have hp₀sphere : p₀.im ∈ Metric.sphere c.im r := by
    rw [Metric.mem_sphere, Real.dist_eq]
    exact (dist_eq_abs_im_sub_of_re_eq_zero hp₀re hc).symm.trans hp₀dist
  have hp₁sphere : p₁.im ∈ Metric.sphere c.im r := by
    rw [Metric.mem_sphere, Real.dist_eq]
    exact (dist_eq_abs_im_sub_of_re_eq_zero hp₁re hc).symm.trans hp₁dist
  have hp₂sphere : p₂.im ∈ Metric.sphere c.im r := by
    rw [Metric.mem_sphere, Real.dist_eq]
    exact (dist_eq_abs_im_sub_of_re_eq_zero hp₂re hc).symm.trans hp₂dist
  rw [Real.sphere_eq_pair c.im hr] at hp₀sphere hp₁sphere hp₂sphere
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp₀sphere hp₁sphere hp₂sphere
  rcases hp₀sphere with hp₀minus | hp₀plus
  · rcases hp₁sphere with hp₁minus | hp₁plus
    · exfalso
      apply hp₀p₁
      apply Complex.ext
      · exact hp₀re.trans hp₁re.symm
      · exact hp₀minus.trans hp₁minus.symm
    · rcases hp₂sphere with hp₂minus | hp₂plus
      · left
        apply Complex.ext
        · exact hp₂re.trans hp₀re.symm
        · exact hp₂minus.trans hp₀minus.symm
      · right
        apply Complex.ext
        · exact hp₂re.trans hp₁re.symm
        · exact hp₂plus.trans hp₁plus.symm
  · rcases hp₁sphere with hp₁minus | hp₁plus
    · rcases hp₂sphere with hp₂minus | hp₂plus
      · right
        apply Complex.ext
        · exact hp₂re.trans hp₁re.symm
        · exact hp₂minus.trans hp₁minus.symm
      · left
        apply Complex.ext
        · exact hp₂re.trans hp₀re.symm
        · exact hp₂plus.trans hp₀plus.symm
    · exfalso
      apply hp₀p₁
      apply Complex.ext
      · exact hp₀re.trans hp₁re.symm
      · exact hp₀plus.trans hp₁plus.symm

/-- Helper for Example 58.3: on the bounded imaginary diameter, a sphere centered at either
unit endpoint contains at most one point. -/
private theorem eq_of_two_verticalSegment_sphere_points_at_unit_endpoint
    {c p q : ℂ} {r : ℝ} (hcnorm : ‖c‖ = 1) (hcre : c.re = 0)
    (hpre : p.re = 0) (hpim : p.im ∈ Set.Icc (-1 : ℝ) 1)
    (hqre : q.re = 0) (hqim : q.im ∈ Set.Icc (-1 : ℝ) 1)
    (hpdist : dist p c = r) (hqdist : dist q c = r) : p = q := by
  -- The center is `Complex.I` or `-Complex.I`; within the segment all displacement has one sign.
  have hzeroRe : (0 : ℂ).re = 0 := by
    norm_num
  have hcabs : |c.im| = 1 := by
    calc
      |c.im| = dist c (0 : ℂ) := by
        rw [dist_eq_abs_im_sub_of_re_eq_zero hcre hzeroRe]
        norm_num
      _ = ‖c‖ := dist_zero_right c
      _ = 1 := hcnorm
  have hone : (0 : ℝ) ≤ 1 := by
    norm_num
  rcases (abs_eq hone).mp hcabs with hcim | hcim
  · have hpabs : |p.im - c.im| = r :=
      (dist_eq_abs_im_sub_of_re_eq_zero hpre hcre).symm.trans hpdist
    have hqabs : |q.im - c.im| = r :=
      (dist_eq_abs_im_sub_of_re_eq_zero hqre hcre).symm.trans hqdist
    rw [hcim, abs_of_nonpos (sub_nonpos.mpr hpim.2)] at hpabs
    rw [hcim, abs_of_nonpos (sub_nonpos.mpr hqim.2)] at hqabs
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · linarith
  · have hpabs : |p.im - c.im| = r :=
      (dist_eq_abs_im_sub_of_re_eq_zero hpre hcre).symm.trans hpdist
    have hqabs : |q.im - c.im| = r :=
      (dist_eq_abs_im_sub_of_re_eq_zero hqre hcre).symm.trans hqdist
    rw [hcim, abs_of_nonneg] at hpabs
    · rw [hcim, abs_of_nonneg] at hqabs
      · apply Complex.ext
        · exact hpre.trans hqre.symm
        · linarith
      · linarith [hqim.1]
    · linarith [hpim.1]

/-- Helper for Example 58.3: the positive quarter-circle parameterization is continuous. -/
private theorem continuous_positiveQuarterCircleArc :
    Continuous (fun t : unitInterval ↦ Circle.exp ((Real.pi / 2) * (t : ℝ))) := by
  -- This is the circle exponential composed with a linear parameter map.
  fun_prop

/-- Helper for Example 58.3: the positive quarter-circle arc starts at the circle basepoint. -/
private theorem positiveQuarterCircleArc_zero :
    Circle.exp ((Real.pi / 2) * ((0 : unitInterval) : ℝ)) = 1 := by
  -- At parameter zero the exponential angle is zero.
  simp

/-- Helper for Example 58.3: the positive quarter-circle arc from the circle basepoint. -/
private def positiveQuarterCircleArc : C(unitInterval, Circle) :=
  ⟨fun t ↦ Circle.exp ((Real.pi / 2) * (t : ℝ)), continuous_positiveQuarterCircleArc⟩

/-- Helper for Example 58.3: the negative quarter-circle parameterization is continuous. -/
private theorem continuous_negativeQuarterCircleArc :
    Continuous (fun t : unitInterval ↦ Circle.exp (-(Real.pi / 2) * (t : ℝ))) := by
  -- This is again the circle exponential composed with a linear parameter map.
  fun_prop

/-- Helper for Example 58.3: the negative quarter-circle arc starts at the circle basepoint. -/
private theorem negativeQuarterCircleArc_zero :
    Circle.exp (-(Real.pi / 2) * ((0 : unitInterval) : ℝ)) = 1 := by
  -- At parameter zero the exponential angle is zero.
  simp

/-- Helper for Example 58.3: the negative quarter-circle arc from the circle basepoint. -/
private def negativeQuarterCircleArc : C(unitInterval, Circle) :=
  ⟨fun t ↦ Circle.exp (-(Real.pi / 2) * (t : ℝ)), continuous_negativeQuarterCircleArc⟩

/-- Helper for Example 58.3: the positive quarter-circle parameterization is injective. -/
private theorem positiveQuarterCircleArc_injective :
    Function.Injective positiveQuarterCircleArc := by
  -- The relevant angles lie in an interval shorter than one full turn.
  intro s t hst
  have hsMem : (Real.pi / 2) * (s : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · nlinarith [s.property.1, Real.pi_pos]
    · nlinarith [s.property.2, Real.pi_pos]
  have htMem : (Real.pi / 2) * (t : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · nlinarith [t.property.1, Real.pi_pos]
    · nlinarith [t.property.2, Real.pi_pos]
  have hangle : (Real.pi / 2) * (s : ℝ) = (Real.pi / 2) * (t : ℝ) := by
    have hwidth : Real.pi / 2 - (0 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_pos]
    exact Circle.exp_injOn_Icc (a := (0 : ℝ)) (b := Real.pi / 2)
      hwidth hsMem htMem hst
  apply Subtype.ext
  nlinarith [Real.pi_pos]

/-- Helper for Example 58.3: the negative quarter-circle parameterization is injective. -/
private theorem negativeQuarterCircleArc_injective :
    Function.Injective negativeQuarterCircleArc := by
  -- Its angles likewise lie in an interval shorter than one full turn.
  intro s t hst
  have hsMem : -(Real.pi / 2) * (s : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (0 : ℝ) := by
    constructor
    · nlinarith [s.property.2, Real.pi_pos]
    · nlinarith [s.property.1, Real.pi_pos]
  have htMem : -(Real.pi / 2) * (t : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (0 : ℝ) := by
    constructor
    · nlinarith [t.property.2, Real.pi_pos]
    · nlinarith [t.property.1, Real.pi_pos]
  have hangle : -(Real.pi / 2) * (s : ℝ) = -(Real.pi / 2) * (t : ℝ) := by
    have hwidth : (0 : ℝ) - (-(Real.pi / 2)) < 2 * Real.pi := by
      nlinarith [Real.pi_pos]
    exact Circle.exp_injOn_Icc (a := -(Real.pi / 2)) (b := (0 : ℝ))
      hwidth hsMem htMem hst
  apply Subtype.ext
  nlinarith [Real.pi_pos]

/-- Helper for Example 58.3: the positive quarter-circle arc is a topological embedding. -/
private theorem isEmbedding_positiveQuarterCircleArc :
    Topology.IsEmbedding positiveQuarterCircleArc := by
  -- Compactness of `unitInterval` upgrades the continuous injection to an embedding.
  exact (positiveQuarterCircleArc.continuous.isClosedEmbedding
    positiveQuarterCircleArc_injective).isEmbedding

/-- Helper for Example 58.3: the negative quarter-circle arc is a topological embedding. -/
private theorem isEmbedding_negativeQuarterCircleArc :
    Topology.IsEmbedding negativeQuarterCircleArc := by
  -- Compactness of `unitInterval` upgrades the continuous injection to an embedding.
  exact (negativeQuarterCircleArc.continuous.isClosedEmbedding
    negativeQuarterCircleArc_injective).isEmbedding

/-- Helper for Example 58.3: the positive and negative quarter-circle arcs meet only at their
common initial point. -/
private theorem range_positiveQuarterCircleArc_inter_negativeQuarterCircleArc :
    Set.range positiveQuarterCircleArc ∩ Set.range negativeQuarterCircleArc =
      {(1 : Circle)} := by
  -- Injectivity of the exponential on `[-π/2, π/2]` forces both parameters to be zero.
  ext y
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hsMem : (Real.pi / 2) * (s : ℝ) ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith [s.property.1, Real.pi_pos]
      · nlinarith [s.property.2, Real.pi_pos]
    have htMem : -(Real.pi / 2) * (t : ℝ) ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith [t.property.2, Real.pi_pos]
      · nlinarith [t.property.1, Real.pi_pos]
    have hangle : (Real.pi / 2) * (s : ℝ) = -(Real.pi / 2) * (t : ℝ) := by
      have hwidth : Real.pi / 2 - (-(Real.pi / 2)) < 2 * Real.pi := by
        nlinarith [Real.pi_pos]
      exact Circle.exp_injOn_Icc (a := -(Real.pi / 2)) (b := Real.pi / 2)
        hwidth hsMem htMem (hs.trans ht.symm)
    have hsZero : (s : ℝ) = 0 := by
      nlinarith [s.property.1, t.property.1, Real.pi_pos]
    apply Set.mem_singleton_iff.mpr
    calc
      y = positiveQuarterCircleArc s := hs.symm
      _ = positiveQuarterCircleArc 0 :=
        congrArg positiveQuarterCircleArc (Subtype.ext hsZero)
      _ = 1 := positiveQuarterCircleArc_zero
  · intro hy
    have hyOne : y = (1 : Circle) := Set.mem_singleton_iff.mp hy
    constructor
    · exact ⟨0, positiveQuarterCircleArc_zero.trans hyOne.symm⟩
    · exact ⟨0, negativeQuarterCircleArc_zero.trans hyOne.symm⟩

/-- Helper for Example 58.3: points on the first coordinate circle lie in the figure eight. -/
private theorem firstFigureEightCircle_mem (z : Circle) :
    (z, (1 : Circle)) ∈ FigureEight.carrier := by
  -- The second coordinate is the circle basepoint.
  exact (FigureEight.mem_iff _).mpr (Or.inl rfl)

/-- Helper for Example 58.3: inclusion of the first coordinate circle into the figure eight. -/
private def firstFigureEightCircle (z : Circle) : FigureEight :=
  ⟨(z, 1), firstFigureEightCircle_mem z⟩

/-- Helper for Example 58.3: the first coordinate-circle inclusion is continuous. -/
private theorem continuous_firstFigureEightCircle : Continuous firstFigureEightCircle := by
  -- It is the product inclusion with a constant second coordinate, restricted to the carrier.
  exact (continuous_id.prodMk continuous_const).subtype_mk _

/-- Helper for Example 58.3: the first coordinate-circle inclusion as a continuous map. -/
private def firstFigureEightCircleMap : C(Circle, FigureEight) :=
  ⟨firstFigureEightCircle, continuous_firstFigureEightCircle⟩

/-- Helper for Example 58.3: the bundled first-circle inclusion evaluates as its underlying
subtype map. -/
private theorem firstFigureEightCircleMap_apply (z : Circle) :
    firstFigureEightCircleMap z = firstFigureEightCircle z := by
  -- Bundling continuity does not change pointwise values.
  rfl

/-- Helper for Example 58.3: the first coordinate-circle inclusion sends `1` to the
figure-eight basepoint. -/
private theorem firstFigureEightCircle_one :
    firstFigureEightCircle 1 = FigureEight.basepoint := by
  -- Both subtype points have the same pair of circle coordinates.
  apply Subtype.ext
  rfl

/-- Helper for Example 58.3: inclusion of the first coordinate circle is an embedding. -/
private theorem isEmbedding_firstFigureEightCircle :
    Topology.IsEmbedding firstFigureEightCircle := by
  -- Codomain restriction of the standard product inclusion preserves embedding.
  exact (isEmbedding_prodMkLeft (1 : Circle)).codRestrict _ _

/-- Helper for Example 58.3: points on the second coordinate circle lie in the figure eight. -/
private theorem secondFigureEightCircle_mem (z : Circle) :
    ((1 : Circle), z) ∈ FigureEight.carrier := by
  -- The first coordinate is the circle basepoint.
  exact (FigureEight.mem_iff _).mpr (Or.inr rfl)

/-- Helper for Example 58.3: inclusion of the second coordinate circle into the figure eight. -/
private def secondFigureEightCircle (z : Circle) : FigureEight :=
  ⟨(1, z), secondFigureEightCircle_mem z⟩

/-- Helper for Example 58.3: the second coordinate-circle inclusion is continuous. -/
private theorem continuous_secondFigureEightCircle : Continuous secondFigureEightCircle := by
  -- It is the product inclusion with a constant first coordinate, restricted to the carrier.
  exact (continuous_const.prodMk continuous_id).subtype_mk _

/-- Helper for Example 58.3: the second coordinate-circle inclusion as a continuous map. -/
private def secondFigureEightCircleMap : C(Circle, FigureEight) :=
  ⟨secondFigureEightCircle, continuous_secondFigureEightCircle⟩

/-- Helper for Example 58.3: the bundled second-circle inclusion evaluates as its underlying
subtype map. -/
private theorem secondFigureEightCircleMap_apply (z : Circle) :
    secondFigureEightCircleMap z = secondFigureEightCircle z := by
  -- Bundling continuity does not change pointwise values.
  rfl

/-- Helper for Example 58.3: composing the bundled first-circle inclusion agrees pointwise with
ordinary function composition. -/
private theorem coe_firstFigureEightCircleMap_comp (γ : C(unitInterval, Circle)) :
    ⇑(firstFigureEightCircleMap.comp γ) = firstFigureEightCircle ∘ γ := by
  -- Compare the two functions at each parameter.
  funext t
  exact firstFigureEightCircleMap_apply (γ t)

/-- Helper for Example 58.3: composing the bundled second-circle inclusion agrees pointwise with
ordinary function composition. -/
private theorem coe_secondFigureEightCircleMap_comp (γ : C(unitInterval, Circle)) :
    ⇑(secondFigureEightCircleMap.comp γ) = secondFigureEightCircle ∘ γ := by
  -- Compare the two functions at each parameter.
  funext t
  exact secondFigureEightCircleMap_apply (γ t)

/-- Helper for Example 58.3: the second coordinate-circle inclusion sends `1` to the
figure-eight basepoint. -/
private theorem secondFigureEightCircle_one :
    secondFigureEightCircle 1 = FigureEight.basepoint := by
  -- Both subtype points have the same pair of circle coordinates.
  apply Subtype.ext
  rfl

/-- Helper for Example 58.3: inclusion of the second coordinate circle is an embedding. -/
private theorem isEmbedding_secondFigureEightCircle :
    Topology.IsEmbedding secondFigureEightCircle := by
  -- Codomain restriction of the other standard product inclusion preserves embedding.
  exact (isEmbedding_prodMkRight (1 : Circle)).codRestrict _ _

/-- Helper for Example 58.3: injective postcomposition transports a computed intersection of
two ranges. -/
private theorem range_comp_inter_range_comp_of_injective
    {X Y Z : Type*} {f : X → Y} {γ δ : Z → X} {x : X}
    (hf : Function.Injective f)
    (hinter : Set.range γ ∩ Set.range δ = {x}) :
    Set.range (f ∘ γ) ∩ Set.range (f ∘ δ) = {f x} := by
  -- Injectivity reflects common image points to the computed source intersection.
  ext y
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hsource : γ s = δ t := by
      apply hf
      exact hs.trans ht.symm
    have hmem : γ s ∈ Set.range γ ∩ Set.range δ := by
      exact ⟨⟨s, rfl⟩, ⟨t, hsource.symm⟩⟩
    rw [hinter] at hmem
    exact Set.mem_singleton_iff.mpr (hs ▸ congrArg f (Set.mem_singleton_iff.mp hmem))
  · intro hy
    have hyFx : y = f x := Set.mem_singleton_iff.mp hy
    have hxMem : x ∈ Set.range γ ∩ Set.range δ := by
      rw [hinter]
      exact Set.mem_singleton x
    obtain ⟨s, hs⟩ := hxMem.1
    obtain ⟨t, ht⟩ := hxMem.2
    constructor
    · exact ⟨s, congrArg f hs |>.trans hyFx.symm⟩
    · exact ⟨t, congrArg f ht |>.trans hyFx.symm⟩

/-- Helper for Example 58.3: arcs in the two coordinate circles starting at `1` meet in the
figure eight only at its basepoint. -/
private theorem range_firstCircleArc_inter_secondCircleArc
    {γ δ : unitInterval → Circle} (hγ : γ 0 = 1) (hδ : δ 0 = 1) :
    Set.range (firstFigureEightCircle ∘ γ) ∩
      Set.range (secondFigureEightCircle ∘ δ) = {FigureEight.basepoint} := by
  -- Equality of a first-circle point and a second-circle point forces both coordinates to be `1`.
  ext y
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hmaps : firstFigureEightCircle (γ s) = secondFigureEightCircle (δ t) :=
      hs.trans ht.symm
    have hcoords : (γ s, (1 : Circle)) = ((1 : Circle), δ t) :=
      congrArg Subtype.val hmaps
    have hfirst : γ s = 1 := congrArg Prod.fst hcoords
    apply Set.mem_singleton_iff.mpr
    calc
      y = firstFigureEightCircle (γ s) := hs.symm
      _ = FigureEight.basepoint := by
        apply Subtype.ext
        apply Prod.ext
        · exact hfirst
        · rfl
  · intro hy
    have hyBase : y = FigureEight.basepoint := Set.mem_singleton_iff.mp hy
    constructor
    · refine ⟨0, ?_⟩
      change firstFigureEightCircle (γ 0) = y
      rw [hγ, hyBase]
      rfl
    · refine ⟨0, ?_⟩
      change secondFigureEightCircle (δ 0) = y
      rw [hδ, hyBase]
      rfl

/-- Helper for Example 58.3: the four canonical quarter-circle prongs at the figure-eight
basepoint. -/
private def figureEightBasepointProng : Fin 4 → C(unitInterval, FigureEight) :=
  ![firstFigureEightCircleMap.comp positiveQuarterCircleArc,
    firstFigureEightCircleMap.comp negativeQuarterCircleArc,
    secondFigureEightCircleMap.comp positiveQuarterCircleArc,
    secondFigureEightCircleMap.comp negativeQuarterCircleArc]

/-- Helper for Example 58.3: the zeroth canonical prong is the positive first-circle arc. -/
private theorem figureEightBasepointProng_zero :
    figureEightBasepointProng 0 =
      firstFigureEightCircleMap.comp positiveQuarterCircleArc := by
  -- This is the zeroth entry of the defining four-vector.
  rfl

/-- Helper for Example 58.3: the first canonical prong is the negative first-circle arc. -/
private theorem figureEightBasepointProng_one :
    figureEightBasepointProng 1 =
      firstFigureEightCircleMap.comp negativeQuarterCircleArc := by
  -- This is the first entry of the defining four-vector.
  rfl

/-- Helper for Example 58.3: the second canonical prong is the positive second-circle arc. -/
private theorem figureEightBasepointProng_two :
    figureEightBasepointProng 2 =
      secondFigureEightCircleMap.comp positiveQuarterCircleArc := by
  -- This is the second entry of the defining four-vector.
  rfl

/-- Helper for Example 58.3: the third canonical prong is the negative second-circle arc. -/
private theorem figureEightBasepointProng_three :
    figureEightBasepointProng 3 =
      secondFigureEightCircleMap.comp negativeQuarterCircleArc := by
  -- This is the third entry of the defining four-vector.
  rfl

/-- Helper for Example 58.3: the two bundled quarter-arcs in the first coordinate circle meet
only at the figure-eight basepoint. -/
private theorem range_firstFigureEightQuarterArcs_inter :
    Set.range (firstFigureEightCircleMap.comp positiveQuarterCircleArc) ∩
      Set.range (firstFigureEightCircleMap.comp negativeQuarterCircleArc) =
        {FigureEight.basepoint} := by
  -- Rewrite the bundled maps pointwise and transport the circle intersection through inclusion.
  rw [coe_firstFigureEightCircleMap_comp, coe_firstFigureEightCircleMap_comp]
  simpa only [firstFigureEightCircle_one] using
    range_comp_inter_range_comp_of_injective isEmbedding_firstFigureEightCircle.injective
      range_positiveQuarterCircleArc_inter_negativeQuarterCircleArc

/-- Helper for Example 58.3: the two bundled quarter-arcs in the second coordinate circle meet
only at the figure-eight basepoint. -/
private theorem range_secondFigureEightQuarterArcs_inter :
    Set.range (secondFigureEightCircleMap.comp positiveQuarterCircleArc) ∩
      Set.range (secondFigureEightCircleMap.comp negativeQuarterCircleArc) =
        {FigureEight.basepoint} := by
  -- Rewrite the bundled maps pointwise and transport the circle intersection through inclusion.
  rw [coe_secondFigureEightCircleMap_comp, coe_secondFigureEightCircleMap_comp]
  simpa only [secondFigureEightCircle_one] using
    range_comp_inter_range_comp_of_injective isEmbedding_secondFigureEightCircle.injective
      range_positiveQuarterCircleArc_inter_negativeQuarterCircleArc

/-- Helper for Example 58.3: bundled arcs in the two coordinate circles starting at `1` meet
only at the figure-eight basepoint. -/
private theorem range_firstCircleMapArc_inter_secondCircleMapArc
    {γ δ : C(unitInterval, Circle)} (hγ : γ 0 = 1) (hδ : δ 0 = 1) :
    Set.range (firstFigureEightCircleMap.comp γ) ∩
      Set.range (secondFigureEightCircleMap.comp δ) = {FigureEight.basepoint} := by
  -- The continuous-map wrappers have the same pointwise values as the underlying inclusions.
  rw [coe_firstFigureEightCircleMap_comp, coe_secondFigureEightCircleMap_comp]
  exact range_firstCircleArc_inter_secondCircleArc hγ hδ

/-- Helper for Example 58.3: the figure-eight basepoint supports four embedded prongs. -/
private theorem figureEight_hasFourProngsAtBasepoint :
    HasNProngsAt 4 FigureEight.basepoint := by
  -- Use the positive and negative quarter-arcs in each of the two coordinate circles.
  refine ⟨figureEightBasepointProng, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [figureEightBasepointProng, positiveQuarterCircleArc,
        negativeQuarterCircleArc, firstFigureEightCircleMap,
        secondFigureEightCircleMap, firstFigureEightCircle,
        secondFigureEightCircle, FigureEight.basepoint]
  · intro i
    fin_cases i
    · exact isEmbedding_firstFigureEightCircle.comp isEmbedding_positiveQuarterCircleArc
    · exact isEmbedding_firstFigureEightCircle.comp isEmbedding_negativeQuarterCircleArc
    · exact isEmbedding_secondFigureEightCircle.comp isEmbedding_positiveQuarterCircleArc
    · exact isEmbedding_secondFigureEightCircle.comp isEmbedding_negativeQuarterCircleArc
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals
      simp only [figureEightBasepointProng, Matrix.cons_val_zero',
        Matrix.cons_val_succ'] at hij ⊢
    all_goals try { exact (hij rfl).elim }
    · exact range_firstFigureEightQuarterArcs_inter
    · exact range_firstCircleMapArc_inter_secondCircleMapArc
        positiveQuarterCircleArc_zero positiveQuarterCircleArc_zero
    · exact range_firstCircleMapArc_inter_secondCircleMapArc
        positiveQuarterCircleArc_zero negativeQuarterCircleArc_zero
    · simpa only [Set.inter_comm] using range_firstFigureEightQuarterArcs_inter
    · exact range_firstCircleMapArc_inter_secondCircleMapArc
        negativeQuarterCircleArc_zero positiveQuarterCircleArc_zero
    · exact range_firstCircleMapArc_inter_secondCircleMapArc
        negativeQuarterCircleArc_zero negativeQuarterCircleArc_zero
    · simpa only [Set.inter_comm] using range_firstCircleMapArc_inter_secondCircleMapArc
        positiveQuarterCircleArc_zero positiveQuarterCircleArc_zero
    · simpa only [Set.inter_comm] using range_firstCircleMapArc_inter_secondCircleMapArc
        negativeQuarterCircleArc_zero positiveQuarterCircleArc_zero
    · exact range_secondFigureEightQuarterArcs_inter
    · simpa only [Set.inter_comm] using range_firstCircleMapArc_inter_secondCircleMapArc
        positiveQuarterCircleArc_zero negativeQuarterCircleArc_zero
    · simpa only [Set.inter_comm] using range_firstCircleMapArc_inter_secondCircleMapArc
        negativeQuarterCircleArc_zero negativeQuarterCircleArc_zero
    · simpa only [Set.inter_comm] using range_secondFigureEightQuarterArcs_inter

/-- Helper for Example 58.3: `-Complex.I` lies on the unit circle. -/
private theorem negI_mem_unitCircle :
    (-Complex.I : ℂ) ∈ (Submonoid.unitSphere ℂ : Set ℂ) := by
  -- Its complex norm is one.
  have hnorm : ‖(-Complex.I : ℂ)‖ = 1 := by
    norm_num
  exact mem_sphere_zero_iff_norm.mpr hnorm

/-- Helper for Example 58.3: the lower imaginary unit as a point of `Circle`. -/
private def circleNegI : Circle :=
  ⟨-Complex.I, negI_mem_unitCircle⟩

/-- Helper for Example 58.3: the lower imaginary unit lies in the planar theta carrier. -/
private theorem planarThetaLowerVertex_mem :
    (-Complex.I : ℂ) ∈ PlanarTheta.carrier := by
  -- It lies on the unit-circle branch of the theta carrier.
  have hnorm : ‖(-Complex.I : ℂ)‖ = 1 := by
    norm_num
  exact (PlanarTheta.mem_iff _).mpr (Or.inl hnorm)

/-- Helper for Example 58.3: the lower branch vertex of the planar theta space. -/
private def planarThetaLowerVertex : PlanarTheta :=
  ⟨-Complex.I, planarThetaLowerVertex_mem⟩

/-- Helper for Example 58.3: every unit-circle point lies in the planar theta carrier. -/
private theorem planarThetaCircle_mem (z : Circle) : (z : ℂ) ∈ PlanarTheta.carrier := by
  -- The circle norm supplies the first disjunct in the carrier description.
  exact (PlanarTheta.mem_iff _).mpr (Or.inl (Circle.norm_coe z))

/-- Helper for Example 58.3: inclusion of the unit-circle branch into the planar theta space. -/
private def planarThetaCircle (z : Circle) : PlanarTheta :=
  ⟨z, planarThetaCircle_mem z⟩

/-- Helper for Example 58.3: the circle-branch inclusion sends the lower imaginary unit to
the lower theta vertex. -/
private theorem planarThetaCircle_circleNegI :
    planarThetaCircle circleNegI = planarThetaLowerVertex := by
  -- Both subtype points have the same ambient complex coordinate.
  apply Subtype.ext
  rfl

/-- Helper for Example 58.3: the unit-circle branch inclusion into planar theta is continuous. -/
private theorem continuous_planarThetaCircle : Continuous planarThetaCircle := by
  -- It is the circle subtype inclusion, restricted to the theta carrier.
  exact continuous_subtype_val.subtype_mk _

/-- Helper for Example 58.3: the unit-circle branch inclusion as a continuous map. -/
private def planarThetaCircleMap : C(Circle, PlanarTheta) :=
  ⟨planarThetaCircle, continuous_planarThetaCircle⟩

/-- Helper for Example 58.3: the unit-circle branch inclusion into planar theta is an embedding. -/
private theorem isEmbedding_planarThetaCircle : Topology.IsEmbedding planarThetaCircle := by
  -- Codomain restriction of the circle subtype inclusion preserves embedding.
  exact Topology.IsEmbedding.subtypeVal.codRestrict _ _

/-- Helper for Example 58.3: bundled composition with the theta circle inclusion is ordinary
function composition pointwise. -/
private theorem coe_planarThetaCircleMap_comp (γ : C(unitInterval, Circle)) :
    ⇑(planarThetaCircleMap.comp γ) = planarThetaCircle ∘ γ := by
  -- Compare the two functions at each interval parameter.
  rfl

/-- Helper for Example 58.3: rotating the positive quarter-circle arc by a circle point. -/
private theorem continuous_circleMulLeft (v : Circle) :
    Continuous (fun z : Circle ↦ v * z) := by
  -- Left multiplication is continuous in the circle topological group.
  fun_prop

/-- Helper for Example 58.3: left multiplication by a fixed circle point as a continuous map. -/
private def circleMulLeftMap (v : Circle) : C(Circle, Circle) :=
  ⟨fun z ↦ v * z, continuous_circleMulLeft v⟩

/-- Helper for Example 58.3: the bundled circle rotation has the expected underlying
function. -/
private theorem coe_circleMulLeftMap (v : Circle) :
    ⇑(circleMulLeftMap v) = fun z ↦ v * z := by
  -- Bundling continuity does not alter pointwise multiplication.
  rfl

/-- Helper for Example 58.3: bundled composition with a circle rotation is ordinary function
composition pointwise. -/
private theorem coe_circleMulLeftMap_comp (v : Circle) (γ : C(unitInterval, Circle)) :
    ⇑((circleMulLeftMap v).comp γ) = ⇑(circleMulLeftMap v) ∘ γ := by
  -- Compare the two functions at each interval parameter.
  rfl

/-- Helper for Example 58.3: left multiplication by a circle point sends `1` to that point. -/
private theorem circleMulLeftMap_one (v : Circle) : circleMulLeftMap v 1 = v := by
  -- This is the multiplicative identity law.
  exact mul_one v

/-- Helper for Example 58.3: left multiplication by a fixed circle point is an embedding. -/
private theorem isEmbedding_circleMulLeftMap (v : Circle) :
    Topology.IsEmbedding (circleMulLeftMap v) := by
  -- Its underlying function is the standard left-multiplication homeomorphism.
  rw [coe_circleMulLeftMap]
  exact (Homeomorph.mulLeft v).isEmbedding

/-- Helper for Example 58.3: rotating the positive quarter-circle arc by a circle point. -/
private def rotatedPositiveQuarterCircleArc (v : Circle) : C(unitInterval, Circle) :=
  (circleMulLeftMap v).comp positiveQuarterCircleArc

/-- Helper for Example 58.3: rotating the negative quarter-circle arc by a circle point. -/
private def rotatedNegativeQuarterCircleArc (v : Circle) : C(unitInterval, Circle) :=
  (circleMulLeftMap v).comp negativeQuarterCircleArc

/-- Helper for Example 58.3: the rotated positive quarter-circle arc starts at its rotation
point. -/
private theorem rotatedPositiveQuarterCircleArc_zero (v : Circle) :
    rotatedPositiveQuarterCircleArc v 0 = v := by
  -- The unrotated arc starts at `1`.
  calc
    rotatedPositiveQuarterCircleArc v 0 =
        circleMulLeftMap v (positiveQuarterCircleArc 0) := rfl
    _ = circleMulLeftMap v 1 :=
      congrArg (circleMulLeftMap v) positiveQuarterCircleArc_zero
    _ = v := circleMulLeftMap_one v

/-- Helper for Example 58.3: the rotated negative quarter-circle arc starts at its rotation
point. -/
private theorem rotatedNegativeQuarterCircleArc_zero (v : Circle) :
    rotatedNegativeQuarterCircleArc v 0 = v := by
  -- The unrotated arc starts at `1`.
  calc
    rotatedNegativeQuarterCircleArc v 0 =
        circleMulLeftMap v (negativeQuarterCircleArc 0) := rfl
    _ = circleMulLeftMap v 1 :=
      congrArg (circleMulLeftMap v) negativeQuarterCircleArc_zero
    _ = v := circleMulLeftMap_one v

/-- Helper for Example 58.3: the rotated positive quarter-circle arc is an embedding. -/
private theorem isEmbedding_rotatedPositiveQuarterCircleArc (v : Circle) :
    Topology.IsEmbedding (rotatedPositiveQuarterCircleArc v) := by
  -- Compose the quarter-arc embedding with rotation by a homeomorphism.
  exact (isEmbedding_circleMulLeftMap v).comp isEmbedding_positiveQuarterCircleArc

/-- Helper for Example 58.3: the rotated negative quarter-circle arc is an embedding. -/
private theorem isEmbedding_rotatedNegativeQuarterCircleArc (v : Circle) :
    Topology.IsEmbedding (rotatedNegativeQuarterCircleArc v) := by
  -- Compose the quarter-arc embedding with rotation by a homeomorphism.
  exact (isEmbedding_circleMulLeftMap v).comp isEmbedding_negativeQuarterCircleArc

/-- Helper for Example 58.3: the two rotated quarter-circle arcs meet only at their rotation
point. -/
private theorem range_rotatedQuarterCircleArcs_inter (v : Circle) :
    Set.range (rotatedPositiveQuarterCircleArc v) ∩
      Set.range (rotatedNegativeQuarterCircleArc v) = {v} := by
  -- Rotation is injective, so it transports the computed unrotated intersection.
  rw [rotatedPositiveQuarterCircleArc, rotatedNegativeQuarterCircleArc,
    coe_circleMulLeftMap_comp, coe_circleMulLeftMap_comp]
  simpa only [circleMulLeftMap_one] using
    range_comp_inter_range_comp_of_injective
      (isEmbedding_circleMulLeftMap v).injective
      range_positiveQuarterCircleArc_inter_negativeQuarterCircleArc

/-- Helper for Example 58.3: the two rotated circle arcs, included into planar theta, meet only
at their common vertex. -/
private theorem range_planarThetaRotatedQuarterArcs_inter (v : Circle) :
    Set.range (planarThetaCircleMap.comp (rotatedPositiveQuarterCircleArc v)) ∩
      Set.range (planarThetaCircleMap.comp (rotatedNegativeQuarterCircleArc v)) =
        {planarThetaCircle v} := by
  -- Injectivity of the circle-branch inclusion transports the rotated-circle intersection.
  rw [coe_planarThetaCircleMap_comp, coe_planarThetaCircleMap_comp]
  exact range_comp_inter_range_comp_of_injective isEmbedding_planarThetaCircle.injective
    (range_rotatedQuarterCircleArcs_inter v)

/-- Helper for Example 58.3: the lower vertical-diameter parameter lies in the theta carrier. -/
private theorem planarThetaLowerVertical_mem (t : unitInterval) :
    (((t : ℂ) - 1) * Complex.I) ∈ PlanarTheta.carrier := by
  -- Its real part is zero and its imaginary coordinate runs from `-1` to `0`.
  have honeLeTwo : (1 : ℝ) ≤ 2 := by
    norm_num
  rw [PlanarTheta.mem_iff]
  right
  constructor
  · simp
  · constructor
    · norm_num
      exact t.property.1
    · norm_num
      exact t.property.2.trans honeLeTwo

/-- Helper for Example 58.3: the lower half of the vertical theta diameter. -/
private def planarThetaLowerVertical (t : unitInterval) : PlanarTheta :=
  ⟨((t : ℂ) - 1) * Complex.I, planarThetaLowerVertical_mem t⟩

/-- Helper for Example 58.3: the lower vertical-diameter arc is continuous. -/
private theorem continuous_planarThetaLowerVertical : Continuous planarThetaLowerVertical := by
  -- The ambient complex formula is polynomial in the real interval coordinate.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Example 58.3: the lower vertical-diameter arc as a continuous map. -/
private def planarThetaLowerVerticalMap : C(unitInterval, PlanarTheta) :=
  ⟨planarThetaLowerVertical, continuous_planarThetaLowerVertical⟩

/-- Helper for Example 58.3: the lower vertical-diameter arc starts at the lower theta vertex. -/
private theorem planarThetaLowerVertical_zero :
    planarThetaLowerVerticalMap 0 = planarThetaLowerVertex := by
  -- Evaluate the ambient affine formula at zero.
  apply Subtype.ext
  norm_num [planarThetaLowerVerticalMap, planarThetaLowerVertical,
    planarThetaLowerVertex]

/-- Helper for Example 58.3: the norm of a unit-interval coordinate minus one is its distance
from the right endpoint. -/
private theorem norm_unitInterval_coe_sub_one (t : unitInterval) :
    ‖(t : ℂ) - 1‖ = 1 - (t : ℝ) := by
  -- Reduce the complex norm of a real number to its absolute value.
  have hnonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have hneg : (t : ℂ) - 1 = -(((1 - (t : ℝ) : ℝ)) : ℂ) := by
    norm_num
  rw [hneg, norm_neg]
  exact Complex.norm_of_nonneg hnonneg

/-- Helper for Example 58.3: the lower vertical-diameter arc is injective. -/
private theorem planarThetaLowerVertical_injective :
    Function.Injective planarThetaLowerVerticalMap := by
  -- Equality of imaginary coordinates recovers the interval parameter.
  intro s t hst
  have him : ((((s : ℂ) - 1) * Complex.I).im) =
      ((((t : ℂ) - 1) * Complex.I).im) := by
    exact congrArg (fun z : PlanarTheta ↦ (z : ℂ).im) hst
  apply Subtype.ext
  norm_num at him ⊢
  exact him

/-- Helper for Example 58.3: the lower vertical-diameter arc is an embedding. -/
private theorem isEmbedding_planarThetaLowerVertical :
    Topology.IsEmbedding planarThetaLowerVerticalMap := by
  -- Compactness of the interval upgrades the continuous injection to an embedding.
  exact (planarThetaLowerVerticalMap.continuous.isClosedEmbedding
    planarThetaLowerVertical_injective).isEmbedding

/-- Helper for Example 58.3: a circle arc beginning at the lower theta vertex meets the lower
vertical diameter only at that vertex. -/
private theorem range_planarThetaCircleArc_inter_lowerVertical
    {γ : C(unitInterval, Circle)} (hγ : γ 0 = circleNegI) :
    Set.range (planarThetaCircleMap.comp γ) ∩ Set.range planarThetaLowerVerticalMap =
      {planarThetaLowerVertex} := by
  -- A vertical-diameter point lying on the unit circle has parameter zero.
  ext y
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hcomplex : (γ s : ℂ) = ((t : ℂ) - 1) * Complex.I := by
      exact congrArg Subtype.val (hs.trans ht.symm)
    have hnorm : (1 : ℝ) = ‖((t : ℂ) - 1) * Complex.I‖ := by
      rw [← Circle.norm_coe (γ s), hcomplex]
    have htZero : (t : ℝ) = 0 := by
      rw [norm_mul, Complex.norm_I, mul_one] at hnorm
      rw [norm_unitInterval_coe_sub_one] at hnorm
      nlinarith
    apply Set.mem_singleton_iff.mpr
    calc
      y = planarThetaLowerVerticalMap t := ht.symm
      _ = planarThetaLowerVerticalMap 0 :=
        congrArg planarThetaLowerVerticalMap (Subtype.ext htZero)
      _ = planarThetaLowerVertex := planarThetaLowerVertical_zero
  · intro hy
    have hyVertex : y = planarThetaLowerVertex := Set.mem_singleton_iff.mp hy
    constructor
    · refine ⟨0, ?_⟩
      rw [ContinuousMap.comp_apply, hγ, hyVertex]
      apply Subtype.ext
      rfl
    · exact ⟨0, planarThetaLowerVertical_zero.trans hyVertex.symm⟩

/-- Helper for Example 58.3: the three canonical prongs issuing from the lower theta vertex. -/
private def planarThetaLowerProng : Fin 3 → C(unitInterval, PlanarTheta) :=
  ![planarThetaCircleMap.comp (rotatedPositiveQuarterCircleArc circleNegI),
    planarThetaCircleMap.comp (rotatedNegativeQuarterCircleArc circleNegI),
    planarThetaLowerVerticalMap]

/-- Helper for Example 58.3: the lower theta vertex supports three embedded prongs. -/
private theorem planarThetaLowerVertex_hasThreeProngs :
    HasNProngsAt 3 planarThetaLowerVertex := by
  -- The two circle quarters and the vertical half-diameter have only the lower vertex in common.
  refine ⟨planarThetaLowerProng, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [planarThetaLowerProng, rotatedPositiveQuarterCircleArc_zero,
        rotatedNegativeQuarterCircleArc_zero, circleNegI, planarThetaCircleMap,
        planarThetaCircle, planarThetaLowerVertex, planarThetaLowerVertical_zero]
  · intro i
    fin_cases i
    · exact isEmbedding_planarThetaCircle.comp
        (isEmbedding_rotatedPositiveQuarterCircleArc circleNegI)
    · exact isEmbedding_planarThetaCircle.comp
        (isEmbedding_rotatedNegativeQuarterCircleArc circleNegI)
    · exact isEmbedding_planarThetaLowerVertical
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals
      simp only [planarThetaLowerProng, Matrix.cons_val_zero', Matrix.cons_val_succ'] at hij ⊢
    all_goals try { exact (hij rfl).elim }
    · simpa only [planarThetaCircle_circleNegI] using
        range_planarThetaRotatedQuarterArcs_inter circleNegI
    · exact range_planarThetaCircleArc_inter_lowerVertical
        (rotatedPositiveQuarterCircleArc_zero circleNegI)
    · simpa only [Set.inter_comm, planarThetaCircle_circleNegI] using
        range_planarThetaRotatedQuarterArcs_inter circleNegI
    · exact range_planarThetaCircleArc_inter_lowerVertical
        (rotatedNegativeQuarterCircleArc_zero circleNegI)
    · simpa only [Set.inter_comm] using range_planarThetaCircleArc_inter_lowerVertical
        (rotatedPositiveQuarterCircleArc_zero circleNegI)
    · simpa only [Set.inter_comm] using range_planarThetaCircleArc_inter_lowerVertical
        (rotatedNegativeQuarterCircleArc_zero circleNegI)

/-- Helper for Example 58.3: complex negation preserves the planar theta carrier. -/
private theorem planarTheta_neg_mem (z : PlanarTheta) :
    -(z : ℂ) ∈ PlanarTheta.carrier := by
  -- Negation preserves the circle and reflects the vertical diameter across the origin.
  have hz := z.property
  rw [PlanarTheta.mem_iff] at hz ⊢
  rcases hz with hcircle | hdiameter
  · left
    simpa only [norm_neg] using hcircle
  · right
    constructor
    · simpa only [map_neg, Complex.neg_re, neg_eq_zero] using hdiameter.1
    · rw [Complex.neg_im]
      constructor
      · linarith [hdiameter.2.2]
      · linarith [hdiameter.2.1]

/-- Helper for Example 58.3: reflection through the origin acts on the planar theta space. -/
private def planarThetaNeg (z : PlanarTheta) : PlanarTheta :=
  ⟨-(z : ℂ), planarTheta_neg_mem z⟩

/-- Helper for Example 58.3: reflection through the origin embeds the planar theta space in
itself. -/
private theorem isEmbedding_planarThetaNeg : Topology.IsEmbedding planarThetaNeg := by
  -- Restrict the ambient negation homeomorphism to the invariant theta carrier.
  exact ((Homeomorph.neg ℂ).isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict
    PlanarTheta.carrier planarTheta_neg_mem

/-- Helper for Example 58.3: the lower theta vertex differs from its reflection through the
origin. -/
private theorem planarThetaLowerVertex_ne_neg :
    planarThetaLowerVertex ≠ planarThetaNeg planarThetaLowerVertex := by
  -- Their imaginary coordinates are respectively `-1` and `1`.
  intro hvertices
  have him := congrArg (fun z : PlanarTheta ↦ (z : ℂ).im) hvertices
  norm_num [planarThetaLowerVertex, planarThetaNeg] at him

/-- Helper for Example 58.3: no point of the planar theta space supports more than three
pairwise disjoint embedded prongs. -/
private theorem planarTheta_prongCard_le_three {n : ℕ} {x : PlanarTheta}
    (hx : HasNProngsAt n x) : n ≤ 3 := by
  -- Four prongs would give four distinct hits on every sufficiently small sphere.
  by_contra hn
  have hfourLe : 4 ≤ n := by
    omega
  have hfour : HasNProngsAt 4 x := hx.mono hfourLe
  by_cases hxnorm : ‖(x : ℂ)‖ = 1
  · by_cases hxre : (x : ℂ).re = 0
    · -- At a vertex, a small sphere has at most two circle hits and one diameter hit.
      have honePositive : (0 : ℝ) < 1 := by
        norm_num
      obtain ⟨r, -, -, p, hpInjective, hpDistance⟩ :=
        hfour.exists_injective_sphere_hits honePositive
      have hpComplexDistance (i : Fin 4) :
          dist (p i : ℂ) (x : ℂ) = r := hpDistance i
      have hxzero : (0 : ℂ) ≠ (x : ℂ) := by
        intro hzero
        rw [← hzero] at hxnorm
        norm_num at hxnorm
      have hpMem (i : Fin 4) :
          ‖(p i : ℂ)‖ = 1 ∨
            ((p i : ℂ).re = 0 ∧ (p i : ℂ).im ∈ Set.Icc (-1 : ℝ) 1) := by
        exact (PlanarTheta.mem_iff _).mp (p i).property
      have circleTripleImpossible (i j k : Fin 4)
          (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
          (hi : ‖(p i : ℂ)‖ = 1) (hj : ‖(p j : ℂ)‖ = 1)
          (hk : ‖(p k : ℂ)‖ = 1) : False := by
        have hpij : (p i : ℂ) ≠ (p j : ℂ) := by
          intro hpval
          exact hij (hpInjective (Subtype.ext hpval))
        rcases eq_of_three_unitCircle_sphere_points hxzero hpij hi hj hk
            (hpComplexDistance i) (hpComplexDistance j) (hpComplexDistance k) with
          hpki | hpkj
        · exact hki (hpInjective (Subtype.ext hpki))
        · exact hkj (hpInjective (Subtype.ext hpkj))
      have verticalPairImpossible (i j : Fin 4) (hij : i ≠ j)
          (hi : (p i : ℂ).re = 0 ∧ (p i : ℂ).im ∈ Set.Icc (-1 : ℝ) 1)
          (hj : (p j : ℂ).re = 0 ∧ (p j : ℂ).im ∈ Set.Icc (-1 : ℝ) 1) :
          False := by
        have hpval := eq_of_two_verticalSegment_sphere_points_at_unit_endpoint
          hxnorm hxre hi.1 hi.2 hj.1 hj.2 (hpComplexDistance i) (hpComplexDistance j)
        exact hij (hpInjective (Subtype.ext hpval))
      have h₀₁ : (0 : Fin 4) ≠ 1 := by decide
      have h₀₂ : (0 : Fin 4) ≠ 2 := by decide
      have h₀₃ : (0 : Fin 4) ≠ 3 := by decide
      have h₁₂ : (1 : Fin 4) ≠ 2 := by decide
      have h₁₃ : (1 : Fin 4) ≠ 3 := by decide
      have h₂₃ : (2 : Fin 4) ≠ 3 := by decide
      rcases hpMem 0 with h₀circle | h₀diameter
      · rcases hpMem 1 with h₁circle | h₁diameter
        · rcases hpMem 2 with h₂circle | h₂diameter
          · exact circleTripleImpossible 0 1 2 h₀₁ h₀₂.symm h₁₂.symm
              h₀circle h₁circle h₂circle
          · rcases hpMem 3 with h₃circle | h₃diameter
            · exact circleTripleImpossible 0 1 3 h₀₁ h₀₃.symm h₁₃.symm
                h₀circle h₁circle h₃circle
            · exact verticalPairImpossible 2 3 h₂₃ h₂diameter h₃diameter
        · rcases hpMem 2 with h₂circle | h₂diameter
          · rcases hpMem 3 with h₃circle | h₃diameter
            · exact circleTripleImpossible 0 2 3 h₀₂ h₀₃.symm h₂₃.symm
                h₀circle h₂circle h₃circle
            · exact verticalPairImpossible 1 3 h₁₃ h₁diameter h₃diameter
          · exact verticalPairImpossible 1 2 h₁₂ h₁diameter h₂diameter
      · rcases hpMem 1 with h₁circle | h₁diameter
        · rcases hpMem 2 with h₂circle | h₂diameter
          · rcases hpMem 3 with h₃circle | h₃diameter
            · exact circleTripleImpossible 1 2 3 h₁₂ h₁₃.symm h₂₃.symm
                h₁circle h₂circle h₃circle
            · exact verticalPairImpossible 0 3 h₀₃ h₀diameter h₃diameter
          · exact verticalPairImpossible 0 2 h₀₂ h₀diameter h₂diameter
        · exact verticalPairImpossible 0 1 h₀₁ h₀diameter h₁diameter
    · -- Away from the imaginary axis, a small sphere meets only the circle branch.
      have hε : 0 < |(x : ℂ).re| := abs_pos.mpr hxre
      obtain ⟨r, -, hrε, p, hpInjective, hpDistance⟩ :=
        hfour.exists_injective_sphere_hits hε
      have hpComplexDistance (i : Fin 4) :
          dist (p i : ℂ) (x : ℂ) = r := hpDistance i
      have hpCircle (i : Fin 4) : ‖(p i : ℂ)‖ = 1 := by
        have hmem := (PlanarTheta.mem_iff _).mp (p i).property
        rcases hmem with hcircle | hdiameter
        · exact hcircle
        · exfalso
          have hreBound : |(x : ℂ).re| ≤ dist (p i : ℂ) (x : ℂ) := by
            rw [Complex.dist_eq]
            calc
              |(x : ℂ).re| = |((p i : ℂ) - x).re| := by
                rw [Complex.sub_re, hdiameter.1, zero_sub, abs_neg]
              _ ≤ ‖(p i : ℂ) - x‖ := Complex.abs_re_le_norm _
          rw [hpComplexDistance i] at hreBound
          linarith
      have hxzero : (0 : ℂ) ≠ (x : ℂ) := by
        intro hzero
        rw [← hzero] at hxnorm
        norm_num at hxnorm
      have hp₀p₁ : (p 0 : ℂ) ≠ (p 1 : ℂ) := by
        intro hpval
        have hindices := hpInjective (Subtype.ext hpval)
        norm_num at hindices
      rcases eq_of_three_unitCircle_sphere_points hxzero hp₀p₁
          (hpCircle 0) (hpCircle 1) (hpCircle 2)
          (hpComplexDistance 0) (hpComplexDistance 1) (hpComplexDistance 2) with
        hp₂p₀ | hp₂p₁
      · have hindices := hpInjective (Subtype.ext hp₂p₀)
        omega
      · have hindices := hpInjective (Subtype.ext hp₂p₁)
        omega
  · -- Off the unit circle, a small sphere meets only the vertical-diameter branch.
    have hxDiameter : (x : ℂ).re = 0 ∧ (x : ℂ).im ∈ Set.Icc (-1 : ℝ) 1 := by
      rcases (PlanarTheta.mem_iff _).mp x.property with hcircle | hdiameter
      · exact (hxnorm hcircle).elim
      · exact hdiameter
    have hnormDifference : 1 - ‖(x : ℂ)‖ ≠ 0 := sub_ne_zero.mpr (Ne.symm hxnorm)
    have hε : 0 < |1 - ‖(x : ℂ)‖| := abs_pos.mpr hnormDifference
    obtain ⟨r, -, hrε, p, hpInjective, hpDistance⟩ :=
      hfour.exists_injective_sphere_hits hε
    have hpComplexDistance (i : Fin 4) :
        dist (p i : ℂ) (x : ℂ) = r := hpDistance i
    have hpDiameter (i : Fin 4) :
        (p i : ℂ).re = 0 ∧ (p i : ℂ).im ∈ Set.Icc (-1 : ℝ) 1 := by
      rcases (PlanarTheta.mem_iff _).mp (p i).property with hcircle | hdiameter
      · exfalso
        have hnormBound : |1 - ‖(x : ℂ)‖| ≤ dist (p i : ℂ) (x : ℂ) := by
          rw [Complex.dist_eq]
          simpa only [hcircle] using abs_norm_sub_norm_le (p i : ℂ) (x : ℂ)
        rw [hpComplexDistance i] at hnormBound
        linarith
      · exact hdiameter
    have hp₀p₁ : (p 0 : ℂ) ≠ (p 1 : ℂ) := by
      intro hpval
      have hindices := hpInjective (Subtype.ext hpval)
      norm_num at hindices
    rcases eq_of_three_vertical_sphere_points hxDiameter.1 (hpDiameter 0).1
        (hpDiameter 1).1 (hpDiameter 2).1 hp₀p₁ (hpComplexDistance 0)
        (hpComplexDistance 1) (hpComplexDistance 2) with hp₂p₀ | hp₂p₁
    · have hindices := hpInjective (Subtype.ext hp₂p₀)
      omega
    · have hindices := hpInjective (Subtype.ext hp₂p₁)
      omega

/-- Helper for Example 58.3: the planar theta space has two distinct points that each support
three pairwise disjoint embedded prongs. -/
private theorem planarTheta_exists_two_tripleProngPoints :
    ∃ p q : PlanarTheta, p ≠ q ∧ HasNProngsAt 3 p ∧ HasNProngsAt 3 q := by
  -- Reflect the verified lower-vertex prongs to the distinct upper vertex.
  refine ⟨planarThetaLowerVertex, planarThetaNeg planarThetaLowerVertex,
    planarThetaLowerVertex_ne_neg, planarThetaLowerVertex_hasThreeProngs, ?_⟩
  exact planarThetaLowerVertex_hasThreeProngs.map isEmbedding_planarThetaNeg

/-- Helper for Example 58.3: a figure-eight point supporting three pairwise disjoint embedded
prongs is necessarily the common basepoint of its two circles. -/
private theorem figureEight_eq_basepoint_of_threeProngs {x : FigureEight}
    (hx : HasNProngsAt 3 x) : x = FigureEight.basepoint := by
  -- Away from the common point, a small sphere sees only one coordinate circle and hence
  -- cannot contain the three distinct hits supplied by three prongs.
  by_contra hxBase
  rcases (FigureEight.mem_iff x.1).mp x.2 with hxSecondOne | hxFirstOne
  · have hxFirstNe : x.1.1 ≠ 1 := by
      intro hxFirstOne
      apply hxBase
      apply Subtype.ext
      apply Prod.ext
      · exact hxFirstOne
      · exact hxSecondOne
    have hε : 0 < dist x.1.1 1 := dist_pos.mpr hxFirstNe
    obtain ⟨r, -, hrε, p, hpInjective, hpDistance⟩ :=
      hx.exists_injective_sphere_hits hε
    have hpSecondOne (i : Fin 3) : (p i).1.2 = 1 := by
      rcases (FigureEight.mem_iff (p i).1).mp (p i).2 with hsecond | hfirst
      · exact hsecond
      · exfalso
        have hcoordinateBound : dist x.1.1 1 ≤ dist (p i) x := by
          calc
            dist x.1.1 1 = dist (p i).1.1 x.1.1 := by
              rw [hfirst, dist_comm]
            _ ≤ max (dist (p i).1.1 x.1.1) (dist (p i).1.2 x.1.2) :=
              le_max_left _ _
            _ = dist (p i) x := rfl
        rw [hpDistance i] at hcoordinateBound
        linarith
    have hpFirstDistance (i : Fin 3) :
        dist ((p i).1.1 : ℂ) (x.1.1 : ℂ) = r := by
      have hdistance := hpDistance i
      change dist (p i).1 x.1 = r at hdistance
      rw [Prod.dist_eq, hpSecondOne i, hxSecondOne, dist_self,
        max_eq_left dist_nonneg] at hdistance
      exact hdistance
    have hxFirstZero : (0 : ℂ) ≠ (x.1.1 : ℂ) := by
      intro hzero
      have hxnorm := Circle.norm_coe x.1.1
      rw [← hzero] at hxnorm
      norm_num at hxnorm
    have hp₀p₁ : ((p 0).1.1 : ℂ) ≠ ((p 1).1.1 : ℂ) := by
      intro hfirst
      have hcircle : (p 0).1.1 = (p 1).1.1 := Circle.ext hfirst
      have htorus : (p 0).1 = (p 1).1 := by
        apply Prod.ext
        · exact hcircle
        · exact (hpSecondOne 0).trans (hpSecondOne 1).symm
      have hindices := hpInjective (Subtype.ext htorus)
      omega
    rcases eq_of_three_unitCircle_sphere_points hxFirstZero hp₀p₁
        (Circle.norm_coe (p 0).1.1) (Circle.norm_coe (p 1).1.1)
        (Circle.norm_coe (p 2).1.1) (hpFirstDistance 0) (hpFirstDistance 1)
        (hpFirstDistance 2) with hp₂p₀ | hp₂p₁
    · have hcircle : (p 2).1.1 = (p 0).1.1 := Circle.ext hp₂p₀
      have htorus : (p 2).1 = (p 0).1 := by
        apply Prod.ext
        · exact hcircle
        · exact (hpSecondOne 2).trans (hpSecondOne 0).symm
      have hindices := hpInjective (Subtype.ext htorus)
      omega
    · have hcircle : (p 2).1.1 = (p 1).1.1 := Circle.ext hp₂p₁
      have htorus : (p 2).1 = (p 1).1 := by
        apply Prod.ext
        · exact hcircle
        · exact (hpSecondOne 2).trans (hpSecondOne 1).symm
      have hindices := hpInjective (Subtype.ext htorus)
      omega
  · have hxSecondNe : x.1.2 ≠ 1 := by
      intro hxSecondOne
      apply hxBase
      apply Subtype.ext
      apply Prod.ext
      · exact hxFirstOne
      · exact hxSecondOne
    have hε : 0 < dist x.1.2 1 := dist_pos.mpr hxSecondNe
    obtain ⟨r, -, hrε, p, hpInjective, hpDistance⟩ :=
      hx.exists_injective_sphere_hits hε
    have hpFirstOne (i : Fin 3) : (p i).1.1 = 1 := by
      rcases (FigureEight.mem_iff (p i).1).mp (p i).2 with hsecond | hfirst
      · exfalso
        have hcoordinateBound : dist x.1.2 1 ≤ dist (p i) x := by
          calc
            dist x.1.2 1 = dist (p i).1.2 x.1.2 := by
              rw [hsecond, dist_comm]
            _ ≤ max (dist (p i).1.1 x.1.1) (dist (p i).1.2 x.1.2) :=
              le_max_right _ _
            _ = dist (p i) x := rfl
        rw [hpDistance i] at hcoordinateBound
        linarith
      · exact hfirst
    have hpSecondDistance (i : Fin 3) :
        dist ((p i).1.2 : ℂ) (x.1.2 : ℂ) = r := by
      have hdistance := hpDistance i
      change dist (p i).1 x.1 = r at hdistance
      rw [Prod.dist_eq, hpFirstOne i, hxFirstOne, dist_self,
        max_eq_right dist_nonneg] at hdistance
      exact hdistance
    have hxSecondZero : (0 : ℂ) ≠ (x.1.2 : ℂ) := by
      intro hzero
      have hxnorm := Circle.norm_coe x.1.2
      rw [← hzero] at hxnorm
      norm_num at hxnorm
    have hp₀p₁ : ((p 0).1.2 : ℂ) ≠ ((p 1).1.2 : ℂ) := by
      intro hsecond
      have hcircle : (p 0).1.2 = (p 1).1.2 := Circle.ext hsecond
      have htorus : (p 0).1 = (p 1).1 := by
        apply Prod.ext
        · exact (hpFirstOne 0).trans (hpFirstOne 1).symm
        · exact hcircle
      have hindices := hpInjective (Subtype.ext htorus)
      omega
    rcases eq_of_three_unitCircle_sphere_points hxSecondZero hp₀p₁
        (Circle.norm_coe (p 0).1.2) (Circle.norm_coe (p 1).1.2)
        (Circle.norm_coe (p 2).1.2) (hpSecondDistance 0) (hpSecondDistance 1)
        (hpSecondDistance 2) with hp₂p₀ | hp₂p₁
    · have hcircle : (p 2).1.2 = (p 0).1.2 := Circle.ext hp₂p₀
      have htorus : (p 2).1 = (p 0).1 := by
        apply Prod.ext
        · exact (hpFirstOne 2).trans (hpFirstOne 0).symm
        · exact hcircle
      have hindices := hpInjective (Subtype.ext htorus)
      omega
    · have hcircle : (p 2).1.2 = (p 1).1.2 := Circle.ext hp₂p₁
      have htorus : (p 2).1 = (p 1).1 := by
        apply Prod.ext
        · exact (hpFirstOne 2).trans (hpFirstOne 1).symm
        · exact hcircle
      have hindices := hpInjective (Subtype.ext htorus)
      omega

/-- Helper for Example 58.3: the interpolation coefficient that radially clips the plane to
the closed unit disk. -/
private def outerDiskClipScale (t : unitInterval) (z : ℂ) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) / max 1 ‖z‖

/-- Helper for Example 58.3: radial interpolation from a planar point to its unit-disk clip. -/
private def outerDiskClipValue (t : unitInterval) (z : ℂ) : ℂ :=
  outerDiskClipScale t z • z

/-- Helper for Example 58.3: outer clipping starts at the original planar point. -/
private theorem outerDiskClipValue_zero (z : ℂ) :
    outerDiskClipValue 0 z = z := by
  -- At time zero the interpolation coefficient is one.
  simp [outerDiskClipValue, outerDiskClipScale]

/-- Helper for Example 58.3: outer clipping fixes every point of the closed unit disk. -/
private theorem outerDiskClipValue_eq_of_norm_le (t : unitInterval) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : outerDiskClipValue t z = z := by
  -- Inside the disk the maximum denominator is one, so the coefficient stays one.
  rw [outerDiskClipValue, outerDiskClipScale, max_eq_left hz]
  simp

/-- Helper for Example 58.3: a point starting outside the unit disk remains outside it during
outer clipping. -/
private theorem one_le_norm_outerDiskClipValue_of_one_lt (t : unitInterval) {z : ℂ}
    (hz : 1 < ‖z‖) : 1 ≤ ‖outerDiskClipValue t z‖ := by
  -- The output norm is the affine interpolation between `‖z‖` and one.
  have hnormPos : 0 < ‖z‖ := zero_lt_one.trans hz
  have hscaleNonneg : 0 ≤ outerDiskClipScale t z := by
    unfold outerDiskClipScale
    exact add_nonneg (sub_nonneg.mpr t.2.2)
      (div_nonneg t.2.1 (zero_le_one.trans (le_max_left 1 ‖z‖)))
  rw [outerDiskClipValue, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hscaleNonneg, outerDiskClipScale, max_eq_right hz.le]
  rw [add_mul, div_mul_cancel₀ _ hnormPos.ne']
  nlinarith [t.2.1, t.2.2]

/-- Helper for Example 58.3: the endpoint of outer clipping lies in the closed unit disk. -/
private theorem norm_outerDiskClipValue_one_le (z : ℂ) :
    ‖outerDiskClipValue 1 z‖ ≤ 1 := by
  -- At time one the norm is `‖z‖ / max 1 ‖z‖`.
  have hdenomPos : 0 < max 1 ‖z‖ :=
    zero_lt_one.trans_le (le_max_left 1 ‖z‖)
  rw [outerDiskClipValue, outerDiskClipScale, norm_smul, Real.norm_eq_abs]
  rw [Set.Icc.coe_one, sub_self, zero_add, one_div]
  rw [abs_of_pos (inv_pos.mpr hdenomPos), inv_mul_eq_div]
  exact (div_le_one hdenomPos).2 (le_max_right 1 ‖z‖)

/-- Helper for Example 58.3: outer clipping never reaches either normalized puncture. -/
private theorem outerDiskClipValue_avoidsPunctures (t : unitInterval)
    (z : DoublyPuncturedPlane) :
    outerDiskClipValue t z ≠ DoublyPuncturedPlane.leftPuncture ∧
      outerDiskClipValue t z ≠ DoublyPuncturedPlane.rightPuncture := by
  -- Points in the disk are fixed; points outside retain norm at least one.
  by_cases hz : ‖(z : ℂ)‖ ≤ 1
  · rw [outerDiskClipValue_eq_of_norm_le t hz]
    exact z.2
  · have hout := one_le_norm_outerDiskClipValue_of_one_lt t (lt_of_not_ge hz)
    constructor
    · intro hleft
      rw [hleft] at hout
      norm_num [DoublyPuncturedPlane.leftPuncture, Complex.norm_def] at hout
    · intro hright
      rw [hright] at hout
      norm_num [DoublyPuncturedPlane.rightPuncture, Complex.norm_def] at hout

/-- Helper for Example 58.3: the outer clipping formula is continuous in time and point. -/
private theorem continuous_outerDiskClipValue :
    Continuous (fun p : unitInterval × DoublyPuncturedPlane ↦
      outerDiskClipValue p.1 p.2) := by
  -- The maximum denominator is bounded below by one, so division is continuous globally.
  have htime : Continuous (fun p : unitInterval × DoublyPuncturedPlane ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hpoint : Continuous (fun p : unitInterval × DoublyPuncturedPlane ↦ (p.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hdenom : Continuous (fun p : unitInterval × DoublyPuncturedPlane ↦
      max 1 ‖(p.2 : ℂ)‖) :=
    continuous_const.max (continuous_norm.comp hpoint)
  have hdenomNe : ∀ p : unitInterval × DoublyPuncturedPlane,
      max 1 ‖(p.2 : ℂ)‖ ≠ 0 := fun p ↦
    ne_of_gt (zero_lt_one.trans_le (le_max_left 1 ‖(p.2 : ℂ)‖))
  unfold outerDiskClipValue outerDiskClipScale
  exact ((continuous_const.sub htime).add (htime.div hdenom hdenomNe)).smul hpoint

/-- Helper for Example 58.3: outer clipping as a point of the doubly punctured plane. -/
private def outerDiskClipPoint (p : unitInterval × DoublyPuncturedPlane) :
    DoublyPuncturedPlane :=
  ⟨outerDiskClipValue p.1 p.2, outerDiskClipValue_avoidsPunctures p.1 p.2⟩

/-- Helper for Example 58.3: the punctured-plane-valued outer clipping is continuous. -/
private theorem continuous_outerDiskClipPoint : Continuous outerDiskClipPoint := by
  -- Restrict the verified planar formula to the punctured-plane codomain.
  exact continuous_outerDiskClipValue.subtype_mk _

/-- Helper for Example 58.3: the bundled outer clipping homotopy map. -/
private def outerDiskClipMap :
    C(unitInterval × DoublyPuncturedPlane, DoublyPuncturedPlane) :=
  ⟨outerDiskClipPoint, continuous_outerDiskClipPoint⟩

/-- Helper for Example 58.3: the endpoint map of outer clipping. -/
private def outerDiskClipEndpoint : C(DoublyPuncturedPlane, DoublyPuncturedPlane) :=
  ⟨fun z ↦ outerDiskClipPoint (1, z),
    continuous_outerDiskClipPoint.comp (continuous_const.prodMk continuous_id)⟩

/-- Helper for Example 58.3: the bundled clipping map starts at the identity. -/
private theorem outerDiskClipMap_zero (z : DoublyPuncturedPlane) :
    outerDiskClipMap (0, z) = z := by
  -- Subtype equality reduces to the planar time-zero computation.
  apply Subtype.ext
  exact outerDiskClipValue_zero z

/-- Helper for Example 58.3: every theta point has norm at most one. -/
private theorem norm_le_one_of_mem_planarTheta {z : ℂ} (hz : z ∈ PlanarTheta.carrier) :
    ‖z‖ ≤ 1 := by
  -- The circle has norm one, while the vertical diameter has absolute imaginary part at most one.
  rcases (PlanarTheta.mem_iff z).mp hz with hcircle | hdiameter
  · exact hcircle.le
  · rw [Complex.norm_def, Complex.normSq_apply, hdiameter.1, zero_mul, zero_add]
    rw [← pow_two, Real.sqrt_sq_eq_abs]
    exact abs_le.mpr hdiameter.2

/-- Helper for Example 58.3: outer clipping fixes the theta carrier pointwise. -/
private theorem outerDiskClipMap_fixed (t : unitInterval) {z : DoublyPuncturedPlane}
    (hz : z ∈ PlanarTheta.inDoublyPuncturedPlane) : outerDiskClipMap (t, z) = z := by
  -- Theta lies in the closed unit disk, where the clipping formula is the identity.
  apply Subtype.ext
  exact outerDiskClipValue_eq_of_norm_le t (norm_le_one_of_mem_planarTheta hz)

/-- Helper for Example 58.3: outer clipping is a homotopy relative to the theta carrier. -/
private def outerDiskClipHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id DoublyPuncturedPlane)
      outerDiskClipEndpoint PlanarTheta.inDoublyPuncturedPlane :=
  { toHomotopy :=
      { toContinuousMap := outerDiskClipMap
        map_zero_left := outerDiskClipMap_zero
        map_one_left := fun _ ↦ rfl }
    prop' := outerDiskClipMap_fixed }

/-- Helper for Example 58.3: the closed unit half-disk on the nonpositive-real side. -/
private def leftClosedHalfDisk : Set ℂ :=
  Metric.closedBall 0 1 ∩ {z | z.re ≤ 0}

/-- Helper for Example 58.3: the closed unit half-disk on the nonnegative-real side. -/
private def rightClosedHalfDisk : Set ℂ :=
  Metric.closedBall 0 1 ∩ {z | 0 ≤ z.re}

/-- Helper for Example 58.3: the left closed half-disk is closed. -/
private theorem isClosed_leftClosedHalfDisk : IsClosed leftClosedHalfDisk := by
  -- Intersect the closed disk with the closed real-coordinate half-space.
  exact Metric.isClosed_closedBall.inter
    (isClosed_le Complex.continuous_re continuous_const)

/-- Helper for Example 58.3: the right closed half-disk is closed. -/
private theorem isClosed_rightClosedHalfDisk : IsClosed rightClosedHalfDisk := by
  -- Intersect the closed disk with the opposite closed real-coordinate half-space.
  exact Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const Complex.continuous_re)

/-- Helper for Example 58.3: the left closed half-disk is convex. -/
private theorem convex_leftClosedHalfDisk : Convex ℝ leftClosedHalfDisk := by
  -- Both the disk and its real-coordinate half-space are convex.
  exact (convex_closedBall (0 : ℂ) 1).inter (convex_halfSpace_re_le 0)

/-- Helper for Example 58.3: the right closed half-disk is convex. -/
private theorem convex_rightClosedHalfDisk : Convex ℝ rightClosedHalfDisk := by
  -- Both the disk and its opposite real-coordinate half-space are convex.
  exact (convex_closedBall (0 : ℂ) 1).inter (convex_halfSpace_re_ge 0)

/-- Helper for Example 58.3: the left closed half-disk is bounded. -/
private theorem isBounded_leftClosedHalfDisk : Bornology.IsBounded leftClosedHalfDisk := by
  -- The half-disk is contained in the bounded closed unit disk.
  exact Metric.isBounded_closedBall.subset Set.inter_subset_left

/-- Helper for Example 58.3: the right closed half-disk is bounded. -/
private theorem isBounded_rightClosedHalfDisk : Bornology.IsBounded rightClosedHalfDisk := by
  -- The half-disk is contained in the bounded closed unit disk.
  exact Metric.isBounded_closedBall.subset Set.inter_subset_left

/-- Helper for Example 58.3: the normalized left puncture lies in the interior of the left
closed half-disk. -/
private theorem leftPuncture_mem_interior_leftClosedHalfDisk :
    DoublyPuncturedPlane.leftPuncture ∈ interior leftClosedHalfDisk := by
  -- Its norm is one half and its real part is strictly negative.
  rw [leftClosedHalfDisk, interior_inter, interior_closedBall (0 : ℂ) one_ne_zero,
    Complex.interior_setOf_re_le]
  constructor
  · rw [Metric.mem_ball, dist_zero_right]
    norm_num [DoublyPuncturedPlane.leftPuncture, Complex.norm_def]
  · norm_num [DoublyPuncturedPlane.leftPuncture]

/-- Helper for Example 58.3: the normalized right puncture lies in the interior of the right
closed half-disk. -/
private theorem rightPuncture_mem_interior_rightClosedHalfDisk :
    DoublyPuncturedPlane.rightPuncture ∈ interior rightClosedHalfDisk := by
  -- Its norm is one half and its real part is strictly positive.
  rw [rightClosedHalfDisk, interior_inter, interior_closedBall (0 : ℂ) one_ne_zero,
    Complex.interior_setOf_le_re]
  constructor
  · rw [Metric.mem_ball, dist_zero_right]
    norm_num [DoublyPuncturedPlane.rightPuncture, Complex.norm_def]
  · norm_num [DoublyPuncturedPlane.rightPuncture]

/-- Helper for Example 58.3: translating an interior point to the origin makes the translated
convex body a neighborhood of zero. -/
private theorem centeredConvexBody_mem_nhds_zero {K : Set ℂ} {p : ℂ}
    (hp : p ∈ interior K) : -p +ᵥ K ∈ nhds (0 : ℂ) := by
  -- Translation carries the chosen interior point to the origin.
  rw [← mem_interior_iff_mem_nhds, interior_vadd]
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hp

/-- Helper for Example 58.3: gauge rescaling after translation sends a chosen interior point
to the origin and its convex body to the closed unit disk. -/
private def centeredConvexBodyGauge (K : Set ℂ) (p : ℂ)
    (hKconvex : Convex ℝ K) (hp : p ∈ interior K)
    (hKbounded : Bornology.IsBounded K) : ℂ ≃ₜ ℂ :=
  (Homeomorph.addLeft (-p)).trans
    (gaugeRescaleHomeomorph (-p +ᵥ K) (Metric.closedBall 0 1)
      (hKconvex.vadd (-p)) (centeredConvexBody_mem_nhds_zero hp)
      ((NormedSpace.isVonNBounded_of_isBounded ℝ hKbounded).vadd (-p))
      (convex_closedBall (0 : ℂ) 1) (Metric.closedBall_mem_nhds 0 zero_lt_one)
      (NormedSpace.isVonNBounded_closedBall ℝ ℂ 1))

/-- Helper for Example 58.3: the centered gauge sends its distinguished point to zero. -/
private theorem centeredConvexBodyGauge_apply_center (K : Set ℂ) (p : ℂ)
    (hKconvex : Convex ℝ K) (hp : p ∈ interior K)
    (hKbounded : Bornology.IsBounded K) :
    centeredConvexBodyGauge K p hKconvex hp hKbounded p = 0 := by
  -- Translation gives zero, which gauge rescaling fixes.
  rw [centeredConvexBodyGauge, Homeomorph.trans_apply]
  change gaugeRescale (-p +ᵥ K) (Metric.closedBall 0 1) (-p + p) = 0
  rw [neg_add_cancel, gaugeRescale_zero]

/-- Helper for Example 58.3: the centered gauge maps a closed convex body onto the closed
unit disk. -/
private theorem image_centeredConvexBodyGauge_eq_closedBall (K : Set ℂ) (p : ℂ)
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (hp : p ∈ interior K)
    (hKbounded : Bornology.IsBounded K) :
    centeredConvexBodyGauge K p hKconvex hp hKbounded '' K =
      Metric.closedBall 0 1 := by
  -- Translate first, then use the closure computation supplied by gauge rescaling.
  let g : ℂ ≃ₜ ℂ :=
    gaugeRescaleHomeomorph (-p +ᵥ K) (Metric.closedBall 0 1)
      (hKconvex.vadd (-p)) (centeredConvexBody_mem_nhds_zero hp)
      ((NormedSpace.isVonNBounded_of_isBounded ℝ hKbounded).vadd (-p))
      (convex_closedBall (0 : ℂ) 1) (Metric.closedBall_mem_nhds 0 zero_lt_one)
      (NormedSpace.isVonNBounded_closedBall ℝ ℂ 1)
  have hgauge : g '' (-p +ᵥ K) = Metric.closedBall (0 : ℂ) 1 := by
    calc
      g '' (-p +ᵥ K) = g '' closure (-p +ᵥ K) := by
        rw [closure_vadd, hKclosed.closure_eq]
      _ = closure (Metric.closedBall (0 : ℂ) 1) := by
        exact image_gaugeRescaleHomeomorph_closure
          (hKconvex.vadd (-p)) (centeredConvexBody_mem_nhds_zero hp)
          ((NormedSpace.isVonNBounded_of_isBounded ℝ hKbounded).vadd (-p))
          (convex_closedBall (0 : ℂ) 1) (Metric.closedBall_mem_nhds 0 zero_lt_one)
          (NormedSpace.isVonNBounded_closedBall ℝ ℂ 1)
      _ = Metric.closedBall 0 1 := Metric.isClosed_closedBall.closure_eq
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hgauge]
    refine ⟨-p + x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · rfl
  · intro hy
    rw [← hgauge] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    obtain ⟨x, hx, hwx⟩ := hw
    refine ⟨x, hx, ?_⟩
    rw [← hwy, ← hwx]
    rfl

/-- Helper for Example 58.3: membership in a closed convex body is detected by the norm of
its centered gauge coordinate. -/
private theorem centeredConvexBodyGauge_mem_iff (K : Set ℂ) (p : ℂ)
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (hp : p ∈ interior K)
    (hKbounded : Bornology.IsBounded K) (z : ℂ) :
    z ∈ K ↔ ‖centeredConvexBodyGauge K p hKconvex hp hKbounded z‖ ≤ 1 := by
  -- Use bijectivity to turn the image equality into a pointwise membership equivalence.
  let e := centeredConvexBodyGauge K p hKconvex hp hKbounded
  have himage : e '' K = Metric.closedBall (0 : ℂ) 1 :=
    image_centeredConvexBodyGauge_eq_closedBall K p hKclosed hKconvex hp hKbounded
  constructor
  · intro hz
    have hez : e z ∈ Metric.closedBall (0 : ℂ) 1 := himage ▸ ⟨z, hz, rfl⟩
    change ‖e z‖ ≤ 1
    simpa only [Metric.mem_closedBall, dist_zero_right] using hez
  · intro hz
    change ‖e z‖ ≤ 1 at hz
    have hez : e z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [← himage] at hez
    obtain ⟨w, hw, hwz⟩ := hez
    exact (e.injective hwz).symm ▸ hw

/-- Helper for Example 58.3: the centered gauge maps the frontier of a closed convex body
onto the unit sphere. -/
private theorem image_frontier_centeredConvexBodyGauge_eq_sphere (K : Set ℂ) (p : ℂ)
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (hp : p ∈ interior K)
    (hKbounded : Bornology.IsBounded K) :
    centeredConvexBodyGauge K p hKconvex hp hKbounded '' frontier K =
      Metric.sphere 0 1 := by
  -- Homeomorphisms preserve frontiers, and the closed unit disk has unit sphere frontier.
  rw [(centeredConvexBodyGauge K p hKconvex hp hKbounded).image_frontier,
    image_centeredConvexBodyGauge_eq_closedBall K p hKclosed hKconvex hp hKbounded,
    frontier_closedBall (0 : ℂ) one_ne_zero]

/-- Helper for Example 58.3: frontier membership is detected by unit norm in centered gauge
coordinates. -/
private theorem centeredConvexBodyGauge_frontier_iff (K : Set ℂ) (p : ℂ)
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (hp : p ∈ interior K)
    (hKbounded : Bornology.IsBounded K) (z : ℂ) :
    z ∈ frontier K ↔ ‖centeredConvexBodyGauge K p hKconvex hp hKbounded z‖ = 1 := by
  -- As above, use injectivity to read the frontier image equality pointwise.
  let e := centeredConvexBodyGauge K p hKconvex hp hKbounded
  have himage : e '' frontier K = Metric.sphere (0 : ℂ) 1 :=
    image_frontier_centeredConvexBodyGauge_eq_sphere K p hKclosed hKconvex hp hKbounded
  constructor
  · intro hz
    have hez : e z ∈ Metric.sphere (0 : ℂ) 1 := himage ▸ ⟨z, hz, rfl⟩
    change ‖e z‖ = 1
    simpa only [Metric.mem_sphere, dist_zero_right] using hez
  · intro hz
    change ‖e z‖ = 1 at hz
    have hez : e z ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [← himage] at hez
    obtain ⟨w, hw, hwz⟩ := hez
    exact (e.injective hwz).symm ▸ hw

/-- Helper for Example 58.3: the gauge homeomorphism for the left punctured half-disk. -/
private def leftHalfDiskGauge : ℂ ≃ₜ ℂ :=
  centeredConvexBodyGauge leftClosedHalfDisk DoublyPuncturedPlane.leftPuncture
    convex_leftClosedHalfDisk leftPuncture_mem_interior_leftClosedHalfDisk
    isBounded_leftClosedHalfDisk

/-- Helper for Example 58.3: the gauge homeomorphism for the right punctured half-disk. -/
private def rightHalfDiskGauge : ℂ ≃ₜ ℂ :=
  centeredConvexBodyGauge rightClosedHalfDisk DoublyPuncturedPlane.rightPuncture
    convex_rightClosedHalfDisk rightPuncture_mem_interior_rightClosedHalfDisk
    isBounded_rightClosedHalfDisk

/-- Helper for Example 58.3: the frontier of the left closed half-disk consists of its
semicircle and vertical diameter. -/
private theorem mem_frontier_leftClosedHalfDisk_iff (z : ℂ) :
    z ∈ frontier leftClosedHalfDisk ↔
      (‖z‖ = 1 ∧ z.re ≤ 0) ∨ (z.re = 0 ∧ ‖z‖ ≤ 1) := by
  -- For a closed intersection, leave the interior through either active inequality.
  have hinterior : interior leftClosedHalfDisk =
      Metric.ball (0 : ℂ) 1 ∩ {z | z.re < 0} := by
    rw [leftClosedHalfDisk, interior_inter, interior_closedBall (0 : ℂ) one_ne_zero,
      Complex.interior_setOf_re_le]
  rw [isClosed_leftClosedHalfDisk.frontier_eq, hinterior]
  simp only [leftClosedHalfDisk, Set.mem_sdiff, Set.mem_inter_iff, Metric.mem_closedBall,
    Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hnorm, hre⟩, hnotInterior⟩
    by_cases hnormEq : ‖z‖ = 1
    · exact Or.inl ⟨hnormEq, hre⟩
    · right
      have hnormLt : ‖z‖ < 1 := lt_of_le_of_ne hnorm hnormEq
      have hreNotLt : ¬z.re < 0 := fun hreLt ↦ hnotInterior ⟨hnormLt, hreLt⟩
      exact ⟨le_antisymm hre (le_of_not_gt hreNotLt), hnorm⟩
  · rintro (⟨hnorm, hre⟩ | ⟨hre, hnorm⟩)
    · refine ⟨⟨hnorm.le, hre⟩, ?_⟩
      exact fun hInterior ↦ (ne_of_lt hInterior.1) hnorm
    · refine ⟨⟨hnorm, hre.le⟩, ?_⟩
      exact fun hInterior ↦ (ne_of_lt hInterior.2) hre

/-- Helper for Example 58.3: the frontier of the right closed half-disk consists of its
semicircle and vertical diameter. -/
private theorem mem_frontier_rightClosedHalfDisk_iff (z : ℂ) :
    z ∈ frontier rightClosedHalfDisk ↔
      (‖z‖ = 1 ∧ 0 ≤ z.re) ∨ (z.re = 0 ∧ ‖z‖ ≤ 1) := by
  -- The proof is the reflected version of the left-half-disk calculation.
  have hinterior : interior rightClosedHalfDisk =
      Metric.ball (0 : ℂ) 1 ∩ {z | 0 < z.re} := by
    rw [rightClosedHalfDisk, interior_inter, interior_closedBall (0 : ℂ) one_ne_zero,
      Complex.interior_setOf_le_re]
  rw [isClosed_rightClosedHalfDisk.frontier_eq, hinterior]
  simp only [rightClosedHalfDisk, Set.mem_sdiff, Set.mem_inter_iff, Metric.mem_closedBall,
    Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hnorm, hre⟩, hnotInterior⟩
    by_cases hnormEq : ‖z‖ = 1
    · exact Or.inl ⟨hnormEq, hre⟩
    · right
      have hnormLt : ‖z‖ < 1 := lt_of_le_of_ne hnorm hnormEq
      have hreNotLt : ¬0 < z.re := fun hreLt ↦ hnotInterior ⟨hnormLt, hreLt⟩
      exact ⟨le_antisymm (le_of_not_gt hreNotLt) hre, hnorm⟩
  · rintro (⟨hnorm, hre⟩ | ⟨hre, hnorm⟩)
    · refine ⟨⟨hnorm.le, hre⟩, ?_⟩
      exact fun hInterior ↦ (ne_of_lt hInterior.1) hnorm
    · refine ⟨⟨hnorm, hre.ge⟩, ?_⟩
      exact fun hInterior ↦ (ne_of_lt hInterior.2) hre.symm

/-- Helper for Example 58.3: each half-disk frontier lies in the planar theta carrier. -/
private theorem frontier_halfDisk_subset_planarTheta (z : ℂ)
    (hz : z ∈ frontier leftClosedHalfDisk ∨ z ∈ frontier rightClosedHalfDisk) :
    z ∈ PlanarTheta.carrier := by
  -- Semicircle points use the circle branch; diameter points use the imaginary-axis branch.
  rw [PlanarTheta.mem_iff]
  rcases hz with hz | hz
  · rcases (mem_frontier_leftClosedHalfDisk_iff z).mp hz with hcircle | hdiameter
    · exact Or.inl hcircle.1
    · right
      refine ⟨hdiameter.1, ?_⟩
      exact abs_le.mp ((Complex.abs_im_le_norm z).trans hdiameter.2)
  · rcases (mem_frontier_rightClosedHalfDisk_iff z).mp hz with hcircle | hdiameter
    · exact Or.inl hcircle.1
    · right
      refine ⟨hdiameter.1, ?_⟩
      exact abs_le.mp ((Complex.abs_im_le_norm z).trans hdiameter.2)

/-- Helper for Example 58.3: a theta point belongs to the frontier selected by the sign of
its real coordinate. -/
private theorem planarTheta_mem_selected_halfDisk_frontier {z : ℂ}
    (hz : z ∈ PlanarTheta.carrier) :
    (z.re ≤ 0 → z ∈ frontier leftClosedHalfDisk) ∧
      (0 ≤ z.re → z ∈ frontier rightClosedHalfDisk) := by
  -- Circle points lie on the matching semicircle; diameter points lie on both frontiers.
  rcases (PlanarTheta.mem_iff z).mp hz with hcircle | hdiameter
  · constructor
    · intro hre
      exact (mem_frontier_leftClosedHalfDisk_iff z).mpr (Or.inl ⟨hcircle, hre⟩)
    · intro hre
      exact (mem_frontier_rightClosedHalfDisk_iff z).mpr (Or.inl ⟨hcircle, hre⟩)
  · have hnorm : ‖z‖ ≤ 1 := norm_le_one_of_mem_planarTheta hz
    constructor
    · intro _
      exact (mem_frontier_leftClosedHalfDisk_iff z).mpr
        (Or.inr ⟨hdiameter.1, hnorm⟩)
    · intro _
      exact (mem_frontier_rightClosedHalfDisk_iff z).mpr
        (Or.inr ⟨hdiameter.1, hnorm⟩)

/-- Helper for Example 58.3: the positive coefficient used to radially move a nonzero vector
to the unit sphere. -/
private def radialInterpolationScale (t : unitInterval) (u : ℂ) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) / ‖u‖

/-- Helper for Example 58.3: inverse-norm radial interpolation in a gauge coordinate. -/
private def radialInterpolation (t : unitInterval) (u : ℂ) : ℂ :=
  radialInterpolationScale t u • u

/-- Helper for Example 58.3: the radial coefficient is positive away from the origin. -/
private theorem radialInterpolationScale_pos (t : unitInterval) {u : ℂ} (hu : u ≠ 0) :
    0 < radialInterpolationScale t u := by
  -- It is a convex combination of one and the positive inverse norm.
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  unfold radialInterpolationScale
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.2.2)
      (div_pos (lt_of_le_of_ne t.2.1 (Ne.symm ht)) huNorm)

/-- Helper for Example 58.3: the norm under radial interpolation is affine in time. -/
private theorem norm_radialInterpolation (t : unitInterval) {u : ℂ} (hu : u ≠ 0) :
    ‖radialInterpolation t u‖ = (1 - (t : ℝ)) * ‖u‖ + (t : ℝ) := by
  -- Positivity removes the scalar absolute value, after which the norm cancels.
  rw [radialInterpolation, norm_smul, Real.norm_eq_abs,
    abs_of_pos (radialInterpolationScale_pos t hu)]
  unfold radialInterpolationScale
  field_simp

/-- Helper for Example 58.3: radial interpolation starts at its input. -/
private theorem radialInterpolation_zero (u : ℂ) : radialInterpolation 0 u = u := by
  -- At time zero the interpolation scalar is one.
  simp [radialInterpolation, radialInterpolationScale]

/-- Helper for Example 58.3: radial interpolation fixes unit vectors. -/
private theorem radialInterpolation_of_norm_eq_one (t : unitInterval) {u : ℂ}
    (hu : ‖u‖ = 1) : radialInterpolation t u = u := by
  -- Unit norm makes the interpolation scalar identically one.
  simp [radialInterpolation, radialInterpolationScale, hu]

/-- Helper for Example 58.3: radial interpolation reaches the unit sphere at time one. -/
private theorem norm_radialInterpolation_one {u : ℂ} (hu : u ≠ 0) :
    ‖radialInterpolation 1 u‖ = 1 := by
  -- Substitute time one in the affine norm formula.
  rw [norm_radialInterpolation 1 hu, Set.Icc.coe_one]
  ring

/-- Helper for Example 58.3: radial interpolation of a nonzero vector stays nonzero. -/
private theorem radialInterpolation_ne_zero (t : unitInterval) {u : ℂ} (hu : u ≠ 0) :
    radialInterpolation t u ≠ 0 := by
  -- A positive scalar multiple of a nonzero vector cannot vanish.
  exact smul_ne_zero (radialInterpolationScale_pos t hu).ne' hu

/-- Helper for Example 58.3: radial interpolation is continuous after substitution of a
continuous nonvanishing vector field. -/
private theorem continuous_radialInterpolation_comp {X : Type*} [TopologicalSpace X]
    {t : X → unitInterval} {u : X → ℂ} (ht : Continuous t) (hu : Continuous u)
    (huNe : ∀ x, u x ≠ 0) : Continuous (fun x ↦ radialInterpolation (t x) (u x)) := by
  -- The only denominator is the norm of the vector field, nonzero by hypothesis.
  have htime : Continuous (fun x ↦ ((t x : unitInterval) : ℝ)) :=
    continuous_subtype_val.comp ht
  have hnorm : Continuous (fun x ↦ ‖u x‖) := continuous_norm.comp hu
  have hnormNe : ∀ x, ‖u x‖ ≠ 0 := fun x ↦ norm_ne_zero_iff.mpr (huNe x)
  unfold radialInterpolation radialInterpolationScale
  exact ((continuous_const.sub htime).add (htime.div hnorm hnormNe)).smul hu

/-- Helper for Example 58.3: the left half-disk gauge sends the left puncture to zero. -/
private theorem leftHalfDiskGauge_apply_puncture :
    leftHalfDiskGauge DoublyPuncturedPlane.leftPuncture = 0 := by
  -- This is the distinguished-center property of the centered gauge.
  exact centeredConvexBodyGauge_apply_center leftClosedHalfDisk
    DoublyPuncturedPlane.leftPuncture convex_leftClosedHalfDisk
    leftPuncture_mem_interior_leftClosedHalfDisk isBounded_leftClosedHalfDisk

/-- Helper for Example 58.3: the right half-disk gauge sends the right puncture to zero. -/
private theorem rightHalfDiskGauge_apply_puncture :
    rightHalfDiskGauge DoublyPuncturedPlane.rightPuncture = 0 := by
  -- This is the corresponding distinguished-center property on the right.
  exact centeredConvexBodyGauge_apply_center rightClosedHalfDisk
    DoublyPuncturedPlane.rightPuncture convex_rightClosedHalfDisk
    rightPuncture_mem_interior_rightClosedHalfDisk isBounded_rightClosedHalfDisk

/-- Helper for Example 58.3: the left half-disk is the inverse image of the closed unit disk
under its gauge. -/
private theorem leftHalfDiskGauge_mem_iff (z : ℂ) :
    z ∈ leftClosedHalfDisk ↔ ‖leftHalfDiskGauge z‖ ≤ 1 := by
  -- Specialize the generic gauge membership interface.
  exact centeredConvexBodyGauge_mem_iff leftClosedHalfDisk
    DoublyPuncturedPlane.leftPuncture isClosed_leftClosedHalfDisk convex_leftClosedHalfDisk
    leftPuncture_mem_interior_leftClosedHalfDisk isBounded_leftClosedHalfDisk z

/-- Helper for Example 58.3: the right half-disk is the inverse image of the closed unit disk
under its gauge. -/
private theorem rightHalfDiskGauge_mem_iff (z : ℂ) :
    z ∈ rightClosedHalfDisk ↔ ‖rightHalfDiskGauge z‖ ≤ 1 := by
  -- Specialize the generic gauge membership interface.
  exact centeredConvexBodyGauge_mem_iff rightClosedHalfDisk
    DoublyPuncturedPlane.rightPuncture isClosed_rightClosedHalfDisk convex_rightClosedHalfDisk
    rightPuncture_mem_interior_rightClosedHalfDisk isBounded_rightClosedHalfDisk z

/-- Helper for Example 58.3: the left half-disk frontier is detected by unit gauge norm. -/
private theorem leftHalfDiskGauge_frontier_iff (z : ℂ) :
    z ∈ frontier leftClosedHalfDisk ↔ ‖leftHalfDiskGauge z‖ = 1 := by
  -- Specialize the generic gauge frontier interface.
  exact centeredConvexBodyGauge_frontier_iff leftClosedHalfDisk
    DoublyPuncturedPlane.leftPuncture isClosed_leftClosedHalfDisk convex_leftClosedHalfDisk
    leftPuncture_mem_interior_leftClosedHalfDisk isBounded_leftClosedHalfDisk z

/-- Helper for Example 58.3: the right half-disk frontier is detected by unit gauge norm. -/
private theorem rightHalfDiskGauge_frontier_iff (z : ℂ) :
    z ∈ frontier rightClosedHalfDisk ↔ ‖rightHalfDiskGauge z‖ = 1 := by
  -- Specialize the generic gauge frontier interface.
  exact centeredConvexBodyGauge_frontier_iff rightClosedHalfDisk
    DoublyPuncturedPlane.rightPuncture isClosed_rightClosedHalfDisk convex_rightClosedHalfDisk
    rightPuncture_mem_interior_rightClosedHalfDisk isBounded_rightClosedHalfDisk z

/-- Helper for Example 58.3: radial interpolation transported through a homeomorphism. -/
private def gaugeRadialValue (e : ℂ ≃ₜ ℂ) (t : unitInterval) (z : ℂ) : ℂ :=
  e.symm (radialInterpolation t (e z))

/-- Helper for Example 58.3: a transported radial interpolation starts at its input. -/
private theorem gaugeRadialValue_zero (e : ℂ ≃ₜ ℂ) (z : ℂ) :
    gaugeRadialValue e 0 z = z := by
  -- Radial time zero and the inverse law of the homeomorphism cancel successively.
  rw [gaugeRadialValue, radialInterpolation_zero, e.symm_apply_apply]

/-- Helper for Example 58.3: transported radial interpolation fixes points whose gauge norm
is one. -/
private theorem gaugeRadialValue_of_norm_eq_one (e : ℂ ≃ₜ ℂ) (t : unitInterval) {z : ℂ}
    (hz : ‖e z‖ = 1) : gaugeRadialValue e t z = z := by
  -- Unit gauge norm fixes the radial core, then the homeomorphism cancels.
  rw [gaugeRadialValue, radialInterpolation_of_norm_eq_one t hz, e.symm_apply_apply]

/-- Helper for Example 58.3: transported radial interpolation remains in a gauge unit disk. -/
private theorem gaugeRadialValue_mem_of_norm_le (e : ℂ ≃ₜ ℂ) (t : unitInterval) {z : ℂ}
    (hz : ‖e z‖ ≤ 1) (hzCenter : e z ≠ 0) : ‖e (gaugeRadialValue e t z)‖ ≤ 1 := by
  -- The affine norm formula stays below one because both endpoint norms do.
  rw [gaugeRadialValue, e.apply_symm_apply, norm_radialInterpolation t hzCenter]
  nlinarith [t.2.1, t.2.2]

/-- Helper for Example 58.3: the transported radial endpoint has unit gauge norm. -/
private theorem gaugeRadialValue_norm_one (e : ℂ ≃ₜ ℂ) {z : ℂ} (hzCenter : e z ≠ 0) :
    ‖e (gaugeRadialValue e 1 z)‖ = 1 := by
  -- At time one, the radial core lies on the unit sphere.
  rw [gaugeRadialValue, e.apply_symm_apply, norm_radialInterpolation_one hzCenter]

/-- Helper for Example 58.3: transported radial interpolation never reaches the point mapped
to the gauge origin. -/
private theorem gaugeRadialValue_ne_center (e : ℂ ≃ₜ ℂ) (p : ℂ) (t : unitInterval) {z : ℂ}
    (hp : e p = 0) (hzCenter : e z ≠ 0) : gaugeRadialValue e t z ≠ p := by
  -- Applying the gauge would identify a nonzero radial value with zero.
  intro heq
  have hzero : radialInterpolation t (e z) = 0 := by
    calc
      radialInterpolation t (e z) = e (gaugeRadialValue e t z) := by
        rw [gaugeRadialValue, e.apply_symm_apply]
      _ = e p := congrArg e heq
      _ = 0 := hp
  exact radialInterpolation_ne_zero t hzCenter hzero

/-- Helper for Example 58.3: transported radial interpolation is continuous for a continuous
field avoiding the gauge center. -/
private theorem continuous_gaugeRadialValue_comp {X : Type*} [TopologicalSpace X]
    (e : ℂ ≃ₜ ℂ) {t : X → unitInterval} {z : X → ℂ} (ht : Continuous t)
    (hz : Continuous z) (hzCenter : ∀ x, e (z x) ≠ 0) :
    Continuous (fun x ↦ gaugeRadialValue e (t x) (z x)) := by
  -- Compose the continuous radial core with the inverse homeomorphism.
  exact e.symm.continuous.comp
    (continuous_radialInterpolation_comp ht (e.continuous.comp hz) hzCenter)

/-- Helper for Example 58.3: the endpoint value of the preliminary outer-disk clipping. -/
private def clippedDiskValue (z : DoublyPuncturedPlane) : ℂ :=
  outerDiskClipValue 1 z

/-- Helper for Example 58.3: the clipped endpoint depends continuously on its input. -/
private theorem continuous_clippedDiskValue : Continuous clippedDiskValue := by
  -- Restrict the already-continuous clipping formula to time one.
  exact continuous_outerDiskClipValue.comp (continuous_const.prodMk continuous_id)

/-- Helper for Example 58.3: the clipped endpoint avoids both normalized punctures. -/
private theorem clippedDiskValue_avoidsPunctures (z : DoublyPuncturedPlane) :
    clippedDiskValue z ≠ DoublyPuncturedPlane.leftPuncture ∧
      clippedDiskValue z ≠ DoublyPuncturedPlane.rightPuncture := by
  -- This is the time-one instance of puncture avoidance for outer clipping.
  exact outerDiskClipValue_avoidsPunctures 1 z

/-- Helper for Example 58.3: the clipped endpoint lies in the closed unit disk. -/
private theorem norm_clippedDiskValue_le_one (z : DoublyPuncturedPlane) :
    ‖clippedDiskValue z‖ ≤ 1 := by
  -- This is the endpoint norm estimate for outer clipping.
  exact norm_outerDiskClipValue_one_le z

/-- Helper for Example 58.3: the clipped endpoint has nonzero left gauge coordinate. -/
private theorem leftHalfDiskGauge_clippedDiskValue_ne_zero (z : DoublyPuncturedPlane) :
    leftHalfDiskGauge (clippedDiskValue z) ≠ 0 := by
  -- Injectivity would otherwise identify the clipped point with the left puncture.
  rw [← leftHalfDiskGauge_apply_puncture]
  exact leftHalfDiskGauge.injective.ne (clippedDiskValue_avoidsPunctures z).1

/-- Helper for Example 58.3: the clipped endpoint has nonzero right gauge coordinate. -/
private theorem rightHalfDiskGauge_clippedDiskValue_ne_zero (z : DoublyPuncturedPlane) :
    rightHalfDiskGauge (clippedDiskValue z) ≠ 0 := by
  -- Injectivity would otherwise identify the clipped point with the right puncture.
  rw [← rightHalfDiskGauge_apply_puncture]
  exact rightHalfDiskGauge.injective.ne (clippedDiskValue_avoidsPunctures z).2

/-- Helper for Example 58.3: the radial branch through the left half-disk. -/
private def leftThetaCollapseBranch (t : unitInterval) (z : DoublyPuncturedPlane) : ℂ :=
  gaugeRadialValue leftHalfDiskGauge t (clippedDiskValue z)

/-- Helper for Example 58.3: the radial branch through the right half-disk. -/
private def rightThetaCollapseBranch (t : unitInterval) (z : DoublyPuncturedPlane) : ℂ :=
  gaugeRadialValue rightHalfDiskGauge t (clippedDiskValue z)

/-- Helper for Example 58.3: the left collapse branch is jointly continuous. -/
private theorem continuous_leftThetaCollapseBranch :
    Continuous (fun p : unitInterval × DoublyPuncturedPlane ↦
      leftThetaCollapseBranch p.1 p.2) := by
  -- Apply the transported-radial continuity interface to the clipped endpoint field.
  exact continuous_gaugeRadialValue_comp leftHalfDiskGauge continuous_fst
    (continuous_clippedDiskValue.comp continuous_snd)
    (fun p ↦ leftHalfDiskGauge_clippedDiskValue_ne_zero p.2)

/-- Helper for Example 58.3: the right collapse branch is jointly continuous. -/
private theorem continuous_rightThetaCollapseBranch :
    Continuous (fun p : unitInterval × DoublyPuncturedPlane ↦
      rightThetaCollapseBranch p.1 p.2) := by
  -- Apply the same interface to the right gauge.
  exact continuous_gaugeRadialValue_comp rightHalfDiskGauge continuous_fst
    (continuous_clippedDiskValue.comp continuous_snd)
    (fun p ↦ rightHalfDiskGauge_clippedDiskValue_ne_zero p.2)

/-- Helper for Example 58.3: the left branch starts at the clipped endpoint. -/
private theorem leftThetaCollapseBranch_zero (z : DoublyPuncturedPlane) :
    leftThetaCollapseBranch 0 z = clippedDiskValue z := by
  -- Use the time-zero computation for transported radial interpolation.
  exact gaugeRadialValue_zero leftHalfDiskGauge (clippedDiskValue z)

/-- Helper for Example 58.3: the right branch starts at the clipped endpoint. -/
private theorem rightThetaCollapseBranch_zero (z : DoublyPuncturedPlane) :
    rightThetaCollapseBranch 0 z = clippedDiskValue z := by
  -- Use the corresponding time-zero computation for the right gauge.
  exact gaugeRadialValue_zero rightHalfDiskGauge (clippedDiskValue z)

/-- Helper for Example 58.3: when selected by a nonpositive real part, the left branch stays
inside the left closed half-disk. -/
private theorem leftThetaCollapseBranch_mem (t : unitInterval) (z : DoublyPuncturedPlane)
    (hzRe : (clippedDiskValue z).re ≤ 0) :
    leftThetaCollapseBranch t z ∈ leftClosedHalfDisk := by
  -- Translate half-disk membership into the gauge norm bound and use radial convexity.
  apply (leftHalfDiskGauge_mem_iff _).mpr
  apply gaugeRadialValue_mem_of_norm_le
  · apply (leftHalfDiskGauge_mem_iff _).mp
    refine ⟨?_, hzRe⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_clippedDiskValue_le_one z
  · exact leftHalfDiskGauge_clippedDiskValue_ne_zero z

/-- Helper for Example 58.3: when selected by a nonnegative real part, the right branch stays
inside the right closed half-disk. -/
private theorem rightThetaCollapseBranch_mem (t : unitInterval) (z : DoublyPuncturedPlane)
    (hzRe : 0 ≤ (clippedDiskValue z).re) :
    rightThetaCollapseBranch t z ∈ rightClosedHalfDisk := by
  -- Translate half-disk membership into the right gauge norm bound.
  apply (rightHalfDiskGauge_mem_iff _).mpr
  apply gaugeRadialValue_mem_of_norm_le
  · apply (rightHalfDiskGauge_mem_iff _).mp
    refine ⟨?_, hzRe⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_clippedDiskValue_le_one z
  · exact rightHalfDiskGauge_clippedDiskValue_ne_zero z

/-- Helper for Example 58.3: the left branch endpoint lies on the left half-disk frontier. -/
private theorem leftThetaCollapseBranch_one_mem_frontier (z : DoublyPuncturedPlane) :
    leftThetaCollapseBranch 1 z ∈ frontier leftClosedHalfDisk := by
  -- At time one the transported radial coordinate has norm one.
  apply (leftHalfDiskGauge_frontier_iff _).mpr
  exact gaugeRadialValue_norm_one leftHalfDiskGauge
    (leftHalfDiskGauge_clippedDiskValue_ne_zero z)

/-- Helper for Example 58.3: the right branch endpoint lies on the right half-disk frontier. -/
private theorem rightThetaCollapseBranch_one_mem_frontier (z : DoublyPuncturedPlane) :
    rightThetaCollapseBranch 1 z ∈ frontier rightClosedHalfDisk := by
  -- At time one the corresponding right gauge coordinate has norm one.
  apply (rightHalfDiskGauge_frontier_iff _).mpr
  exact gaugeRadialValue_norm_one rightHalfDiskGauge
    (rightHalfDiskGauge_clippedDiskValue_ne_zero z)

/-- Helper for Example 58.3: the left branch fixes a clipped endpoint on its frontier. -/
private theorem leftThetaCollapseBranch_fixed (t : unitInterval) (z : DoublyPuncturedPlane)
    (hz : clippedDiskValue z ∈ frontier leftClosedHalfDisk) :
    leftThetaCollapseBranch t z = clippedDiskValue z := by
  -- Frontier membership is precisely unit gauge norm, which the radial core fixes.
  exact gaugeRadialValue_of_norm_eq_one leftHalfDiskGauge t
    ((leftHalfDiskGauge_frontier_iff _).mp hz)

/-- Helper for Example 58.3: the right branch fixes a clipped endpoint on its frontier. -/
private theorem rightThetaCollapseBranch_fixed (t : unitInterval) (z : DoublyPuncturedPlane)
    (hz : clippedDiskValue z ∈ frontier rightClosedHalfDisk) :
    rightThetaCollapseBranch t z = clippedDiskValue z := by
  -- Frontier membership is again unit gauge norm.
  exact gaugeRadialValue_of_norm_eq_one rightHalfDiskGauge t
    ((rightHalfDiskGauge_frontier_iff _).mp hz)

/-- Helper for Example 58.3: the selected left branch avoids both normalized punctures. -/
private theorem leftThetaCollapseBranch_avoidsPunctures (t : unitInterval)
    (z : DoublyPuncturedPlane) (hzRe : (clippedDiskValue z).re ≤ 0) :
    leftThetaCollapseBranch t z ≠ DoublyPuncturedPlane.leftPuncture ∧
      leftThetaCollapseBranch t z ≠ DoublyPuncturedPlane.rightPuncture := by
  -- Nonvanishing excludes the left center; the half-disk sign excludes the right center.
  constructor
  · exact gaugeRadialValue_ne_center leftHalfDiskGauge
      DoublyPuncturedPlane.leftPuncture t leftHalfDiskGauge_apply_puncture
      (leftHalfDiskGauge_clippedDiskValue_ne_zero z)
  · intro hright
    have hmem := leftThetaCollapseBranch_mem t z hzRe
    rw [leftClosedHalfDisk] at hmem
    have hre := hmem.2
    rw [hright] at hre
    norm_num [DoublyPuncturedPlane.rightPuncture] at hre

/-- Helper for Example 58.3: the selected right branch avoids both normalized punctures. -/
private theorem rightThetaCollapseBranch_avoidsPunctures (t : unitInterval)
    (z : DoublyPuncturedPlane) (hzRe : 0 ≤ (clippedDiskValue z).re) :
    rightThetaCollapseBranch t z ≠ DoublyPuncturedPlane.leftPuncture ∧
      rightThetaCollapseBranch t z ≠ DoublyPuncturedPlane.rightPuncture := by
  -- The half-disk sign excludes the left center; nonvanishing excludes the right center.
  constructor
  · intro hleft
    have hmem := rightThetaCollapseBranch_mem t z hzRe
    rw [rightClosedHalfDisk] at hmem
    have hre := hmem.2
    rw [hleft] at hre
    norm_num [DoublyPuncturedPlane.leftPuncture] at hre
  · exact gaugeRadialValue_ne_center rightHalfDiskGauge
      DoublyPuncturedPlane.rightPuncture t rightHalfDiskGauge_apply_puncture
      (rightHalfDiskGauge_clippedDiskValue_ne_zero z)

/-- Helper for Example 58.3: paste the two gauge-radial branches according to the real sign
of the clipped endpoint. -/
private def thetaCollapseValue (p : unitInterval × DoublyPuncturedPlane) : ℂ :=
  if (clippedDiskValue p.2).re ≤ 0 then
    leftThetaCollapseBranch p.1 p.2
  else
    rightThetaCollapseBranch p.1 p.2

/-- Helper for Example 58.3: the two collapse branches agree on their vertical overlap. -/
private theorem thetaCollapseBranches_eq_of_re_eq_zero
    (p : unitInterval × DoublyPuncturedPlane) (hpRe : (clippedDiskValue p.2).re = 0) :
    leftThetaCollapseBranch p.1 p.2 = rightThetaCollapseBranch p.1 p.2 := by
  -- The clipped point lies on both vertical frontiers, so both branches fix it.
  have hnorm := norm_clippedDiskValue_le_one p.2
  have hleft : clippedDiskValue p.2 ∈ frontier leftClosedHalfDisk :=
    (mem_frontier_leftClosedHalfDisk_iff _).mpr (Or.inr ⟨hpRe, hnorm⟩)
  have hright : clippedDiskValue p.2 ∈ frontier rightClosedHalfDisk :=
    (mem_frontier_rightClosedHalfDisk_iff _).mpr (Or.inr ⟨hpRe, hnorm⟩)
  calc
    leftThetaCollapseBranch p.1 p.2 = clippedDiskValue p.2 :=
      leftThetaCollapseBranch_fixed p.1 p.2 hleft
    _ = rightThetaCollapseBranch p.1 p.2 :=
      (rightThetaCollapseBranch_fixed p.1 p.2 hright).symm

/-- Helper for Example 58.3: the pasted theta-collapse value is continuous. -/
private theorem continuous_thetaCollapseValue : Continuous thetaCollapseValue := by
  -- The ordered closed-cover pasting theorem uses branch agreement at real part zero.
  exact Continuous.if_le continuous_leftThetaCollapseBranch
    continuous_rightThetaCollapseBranch
    (Complex.continuous_re.comp (continuous_clippedDiskValue.comp continuous_snd))
    continuous_const thetaCollapseBranches_eq_of_re_eq_zero

/-- Helper for Example 58.3: the pasted collapse starts at the clipped endpoint map. -/
private theorem thetaCollapseValue_zero (z : DoublyPuncturedPlane) :
    thetaCollapseValue (0, z) = clippedDiskValue z := by
  -- Either branch has the same verified time-zero value.
  rw [thetaCollapseValue]
  split_ifs
  · exact leftThetaCollapseBranch_zero z
  · exact rightThetaCollapseBranch_zero z

/-- Helper for Example 58.3: the pasted collapse avoids both punctures at every time. -/
private theorem thetaCollapseValue_avoidsPunctures (p : unitInterval × DoublyPuncturedPlane) :
    thetaCollapseValue p ≠ DoublyPuncturedPlane.leftPuncture ∧
      thetaCollapseValue p ≠ DoublyPuncturedPlane.rightPuncture := by
  -- Dispatch to the avoidance theorem for the branch selected by the real sign.
  rw [thetaCollapseValue]
  split_ifs with hsign
  · exact leftThetaCollapseBranch_avoidsPunctures p.1 p.2 hsign
  · exact rightThetaCollapseBranch_avoidsPunctures p.1 p.2
      (le_of_lt (lt_of_not_ge hsign))

/-- Helper for Example 58.3: the pasted endpoint lies in the planar theta carrier. -/
private theorem thetaCollapseValue_one_mem (z : DoublyPuncturedPlane) :
    thetaCollapseValue (1, z) ∈ PlanarTheta.carrier := by
  -- Each selected branch ends on one of the two half-disk frontiers.
  rw [thetaCollapseValue]
  split_ifs
  · exact frontier_halfDisk_subset_planarTheta _
      (Or.inl (leftThetaCollapseBranch_one_mem_frontier z))
  · exact frontier_halfDisk_subset_planarTheta _
      (Or.inr (rightThetaCollapseBranch_one_mem_frontier z))

/-- Helper for Example 58.3: outer clipping is the identity on the theta carrier. -/
private theorem clippedDiskValue_eq_of_mem_planarTheta {z : DoublyPuncturedPlane}
    (hz : z ∈ PlanarTheta.inDoublyPuncturedPlane) : clippedDiskValue z = z := by
  -- Project the subtype equality supplied by the preliminary relative homotopy.
  exact congrArg Subtype.val (outerDiskClipMap_fixed 1 hz)

/-- Helper for Example 58.3: the pasted collapse fixes the planar theta carrier pointwise. -/
private theorem thetaCollapseValue_fixed (t : unitInterval) {z : DoublyPuncturedPlane}
    (hz : z ∈ PlanarTheta.inDoublyPuncturedPlane) : thetaCollapseValue (t, z) = z := by
  -- After clipping fixes `z`, the real sign selects a half-disk frontier containing `z`.
  have hclip := clippedDiskValue_eq_of_mem_planarTheta hz
  rw [thetaCollapseValue]
  split_ifs with hsign
  · have hzRe : (z : ℂ).re ≤ 0 := by
      rw [← hclip]
      exact hsign
    have hzFrontier : (z : ℂ) ∈ frontier leftClosedHalfDisk :=
      (planarTheta_mem_selected_halfDisk_frontier hz).1 hzRe
    have hclipFrontier : clippedDiskValue z ∈ frontier leftClosedHalfDisk := by
      rwa [hclip]
    calc
      leftThetaCollapseBranch t z = clippedDiskValue z :=
        leftThetaCollapseBranch_fixed t z hclipFrontier
      _ = z := hclip
  · have hzRe : 0 ≤ (z : ℂ).re := by
      rw [← hclip]
      exact le_of_lt (lt_of_not_ge hsign)
    have hzFrontier : (z : ℂ) ∈ frontier rightClosedHalfDisk :=
      (planarTheta_mem_selected_halfDisk_frontier hz).2 hzRe
    have hclipFrontier : clippedDiskValue z ∈ frontier rightClosedHalfDisk := by
      rwa [hclip]
    calc
      rightThetaCollapseBranch t z = clippedDiskValue z :=
        rightThetaCollapseBranch_fixed t z hclipFrontier
      _ = z := hclip

/-- Helper for Example 58.3: the pasted collapse packaged as a point of the doubly punctured
plane. -/
private def thetaCollapsePoint
    (p : unitInterval × DoublyPuncturedPlane) : DoublyPuncturedPlane :=
  ⟨thetaCollapseValue p, thetaCollapseValue_avoidsPunctures p⟩

/-- Helper for Example 58.3: coercing the packaged collapse point recovers its planar value. -/
private theorem coe_thetaCollapsePoint (p : unitInterval × DoublyPuncturedPlane) :
    (thetaCollapsePoint p : ℂ) = thetaCollapseValue p := by
  -- Packaging changes only the stored puncture-avoidance proof.
  rfl

/-- Helper for Example 58.3: the punctured-plane-valued theta collapse is continuous. -/
private theorem continuous_thetaCollapsePoint : Continuous thetaCollapsePoint := by
  -- Restrict the verified planar formula to the punctured-plane codomain.
  exact continuous_thetaCollapseValue.subtype_mk _

/-- Helper for Example 58.3: the bundled punctured-plane-valued theta collapse. -/
private def thetaCollapseMap :
    C(unitInterval × DoublyPuncturedPlane, DoublyPuncturedPlane) :=
  ⟨thetaCollapsePoint, continuous_thetaCollapsePoint⟩

/-- Helper for Example 58.3: the theta-collapse map starts at the outer-clipping endpoint. -/
private theorem thetaCollapseMap_zero (z : DoublyPuncturedPlane) :
    thetaCollapseMap (0, z) = outerDiskClipEndpoint z := by
  -- Compare ambient complex values using the planar time-zero formula.
  apply Subtype.ext
  exact (coe_thetaCollapsePoint (0, z)).trans (thetaCollapseValue_zero z)

/-- Helper for Example 58.3: the time-one collapse point belongs to the nested theta carrier. -/
private theorem thetaCollapsePoint_one_mem (z : DoublyPuncturedPlane) :
    thetaCollapsePoint (1, z) ∈ PlanarTheta.inDoublyPuncturedPlane := by
  -- Membership reduces to the verified planar endpoint statement.
  exact thetaCollapseValue_one_mem z

/-- Helper for Example 58.3: the theta-valued endpoint of the collapse. -/
private def thetaRetractionPoint
    (z : DoublyPuncturedPlane) : PlanarTheta.inDoublyPuncturedPlane :=
  ⟨thetaCollapsePoint (1, z), thetaCollapsePoint_one_mem z⟩

/-- Helper for Example 58.3: coercing the theta-valued endpoint to the plane recovers the
planar collapse endpoint. -/
private theorem coe_thetaRetractionPoint (z : DoublyPuncturedPlane) :
    ((thetaRetractionPoint z : DoublyPuncturedPlane) : ℂ) =
      thetaCollapseValue (1, z) := by
  -- Both subtype layers store the same planar endpoint value.
  exact coe_thetaCollapsePoint (1, z)

/-- Helper for Example 58.3: the theta-valued endpoint map is continuous. -/
private theorem continuous_thetaRetractionPoint : Continuous thetaRetractionPoint := by
  -- Restrict the time-one punctured-plane map to its theta-valued endpoint.
  exact (continuous_thetaCollapsePoint.comp (continuous_const.prodMk continuous_id)).subtype_mk _

/-- Helper for Example 58.3: the bundled endpoint map into the nested theta carrier. -/
private def thetaRetractionMap :
    C(DoublyPuncturedPlane, PlanarTheta.inDoublyPuncturedPlane) :=
  ⟨thetaRetractionPoint, continuous_thetaRetractionPoint⟩

/-- Helper for Example 58.3: the endpoint map is a left inverse to theta inclusion. -/
private theorem thetaRetractionMap_leftInverse :
    Function.LeftInverse thetaRetractionMap
      (Subtype.val : PlanarTheta.inDoublyPuncturedPlane → DoublyPuncturedPlane) := by
  -- Theta fixation at time one supplies the left-inverse equation through both subtype layers.
  intro z
  apply Subtype.ext
  apply Subtype.ext
  exact (coe_thetaRetractionPoint z).trans (thetaCollapseValue_fixed 1 z.2)

/-- Helper for Example 58.3: the endpoint theta retraction. -/
private def thetaRetraction : Set.Retraction PlanarTheta.inDoublyPuncturedPlane :=
  Set.Retraction.ofContinuousMap thetaRetractionMap thetaRetractionMap_leftInverse

/-- Helper for Example 58.3: the collapse endpoint is the ambient map of the theta retraction. -/
private theorem thetaCollapseMap_one (z : DoublyPuncturedPlane) :
    thetaCollapseMap (1, z) = thetaRetraction.toAmbient z := by
  -- Compare the common planar endpoint through the named coercion formulas.
  apply Subtype.ext
  exact (coe_thetaCollapsePoint (1, z)).trans (coe_thetaRetractionPoint z).symm

/-- Helper for Example 58.3: the packaged collapse fixes the nested theta carrier. -/
private theorem thetaCollapseMap_fixed (t : unitInterval) {z : DoublyPuncturedPlane}
    (hz : z ∈ PlanarTheta.inDoublyPuncturedPlane) : thetaCollapseMap (t, z) = z := by
  -- Reduce subtype equality to the verified planar fixation statement.
  apply Subtype.ext
  exact (coe_thetaCollapsePoint (t, z)).trans (thetaCollapseValue_fixed t hz)

/-- Helper for Example 58.3: on theta, the packaged collapse equals its outer-clipping
initial map throughout the homotopy. -/
private theorem thetaCollapseMap_eq_outerDiskClipEndpoint (t : unitInterval)
    {z : DoublyPuncturedPlane} (hz : z ∈ PlanarTheta.inDoublyPuncturedPlane) :
    thetaCollapseMap (t, z) = outerDiskClipEndpoint z := by
  -- Both maps equal the unchanged theta point.
  calc
    thetaCollapseMap (t, z) = z := thetaCollapseMap_fixed t hz
    _ = outerDiskClipEndpoint z := (outerDiskClipMap_fixed 1 hz).symm

/-- Helper for Example 58.3: the gauge-radial collapse is a homotopy relative to theta. -/
private def thetaCollapseHomotopyRel :
    ContinuousMap.HomotopyRel outerDiskClipEndpoint thetaRetraction.toAmbient
      PlanarTheta.inDoublyPuncturedPlane :=
  { toHomotopy :=
      { toContinuousMap := thetaCollapseMap
        map_zero_left := thetaCollapseMap_zero
        map_one_left := thetaCollapseMap_one }
    prop' := thetaCollapseMap_eq_outerDiskClipEndpoint }

/-- Helper for Example 58.3: after outer clipping, the two punctured closed half-disks
deform relative to their frontiers onto the planar theta carrier. -/
private theorem exists_thetaRetraction_homotopicRel_outerDiskClip :
    ∃ r : Set.Retraction PlanarTheta.inDoublyPuncturedPlane,
      ContinuousMap.HomotopicRel outerDiskClipEndpoint r.toAmbient
        PlanarTheta.inDoublyPuncturedPlane := by
  -- Package the constructed endpoint retraction and its relative gauge-radial homotopy.
  exact ⟨thetaRetraction, ⟨thetaCollapseHomotopyRel⟩⟩


/-- Example 58.3 (1): with punctures normalized to `-1 / 2` and `1 / 2`, one in each
bounded component of the complement of the planar theta carrier, the planar theta space is
a deformation retract of the resulting doubly punctured plane. -/
theorem planarTheta_isDeformationRetract :
    Set.IsDeformationRetract PlanarTheta.inDoublyPuncturedPlane := by
  -- Concatenate outer clipping with the relative collapse of the two punctured half-disks.
  obtain ⟨r, ⟨H⟩⟩ := exists_thetaRetraction_homotopicRel_outerDiskClip
  apply (Set.isDeformationRetract_iff PlanarTheta.inDoublyPuncturedPlane).2
  exact ⟨r, ⟨outerDiskClipHomotopyRel.trans H⟩⟩

/-- Example 58.3 (2): the figure eight and the planar theta space have isomorphic
fundamental groups. -/
theorem figureEightFundamentalGroup_mulEquiv_planarTheta :
    Nonempty
      (FundamentalGroup FigureEight FigureEight.basepoint ≃*
        FundamentalGroup PlanarTheta PlanarTheta.basepoint) := by
  -- Realize the abstract figure eight as the normalized planar retract.
  obtain ⟨eFigure⟩ := figureEightHomeomorphNormalizedPlanarFigureEight
  let figurePoint := eFigure FigureEight.basepoint
  let figureInclusion : C(
      PlanarFigureEight.inComplement DoublyPuncturedPlane.leftPuncture
        DoublyPuncturedPlane.rightPuncture,
      DoublyPuncturedPlane) := ⟨Subtype.val, continuous_subtype_val⟩
  let figureInclusionOpposite := MulEquiv.ofBijective
    (FundamentalGroup.LeftToRight.map figureInclusion figurePoint)
    (Set.IsDeformationRetract.fundamentalGroupMap_bijective
      (PlanarFigureEight.isDeformationRetract _ _ normalizedPunctures_ne) figurePoint)
  let figureInclusionEquiv := MulEquiv.unop figureInclusionOpposite
  -- Choose the nested theta point whose direct planar image is the stated basepoint.
  let thetaPoint : PlanarTheta.inDoublyPuncturedPlane :=
    ⟨⟨PlanarTheta.basepoint.1,
      planarTheta_avoidsPunctures PlanarTheta.basepoint.2⟩,
      PlanarTheta.basepoint.2⟩
  let thetaInclusion : C(PlanarTheta.inDoublyPuncturedPlane,
      DoublyPuncturedPlane) := ⟨Subtype.val, continuous_subtype_val⟩
  let thetaInclusionOpposite := MulEquiv.ofBijective
    (FundamentalGroup.LeftToRight.map thetaInclusion thetaPoint)
    (planarTheta_isDeformationRetract.fundamentalGroupMap_bijective thetaPoint)
  let thetaInclusionEquiv := MulEquiv.unop thetaInclusionOpposite
  -- The complement of two points in the complex plane is path connected.
  letI : PathConnectedSpace DoublyPuncturedPlane :=
    isPathConnected_iff_pathConnectedSpace.mp (by
      have hrank : 1 < Module.rank ℝ ℂ := by
        rw [Complex.rank_real_complex]
        norm_num
      have hcount : ({DoublyPuncturedPlane.leftPuncture,
          DoublyPuncturedPlane.rightPuncture} : Set ℂ).Countable :=
        (Set.countable_singleton DoublyPuncturedPlane.rightPuncture).insert
          DoublyPuncturedPlane.leftPuncture
      have hpath := hcount.isPathConnected_compl_of_one_lt_rank hrank
      have hcarrier :
          ({DoublyPuncturedPlane.leftPuncture,
            DoublyPuncturedPlane.rightPuncture} : Set ℂ)ᶜ =
            {z | z ≠ DoublyPuncturedPlane.leftPuncture ∧
              z ≠ DoublyPuncturedPlane.rightPuncture} := by
        ext z
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_setOf_eq, not_or]
      rw [hcarrier] at hpath
      exact hpath)
  -- Pass through the common punctured plane, changing its basepoint once.
  let result :=
    (eFigure.fundamentalGroupMulEquiv FigureEight.basepoint).trans
      (figureInclusionEquiv.trans
        ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
          (figurePoint : DoublyPuncturedPlane) (thetaPoint : DoublyPuncturedPlane)).trans
          (thetaInclusionEquiv.symm.trans
            (planarThetaRetractHomeomorph.fundamentalGroupMulEquiv thetaPoint))))
  exact ⟨result⟩

/-- Example 58.3 (3): the figure eight is not homeomorphic to a deformation retract of
the planar theta space. -/
theorem figureEight_not_homeomorphic_deformationRetract_planarTheta :
    ¬ ∃ A : Set PlanarTheta, Set.IsDeformationRetract A ∧ Nonempty (FigureEight ≃ₜ A) := by
  -- A homeomorphism onto any subspace would give an embedding into the whole theta space.
  rintro ⟨A, _, ⟨e⟩⟩
  let f : FigureEight → PlanarTheta := fun x ↦ (e x : PlanarTheta)
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  -- Four basepoint prongs cannot fit at a theta point, whose valence is at most three.
  have hprongs : HasNProngsAt 4 (f FigureEight.basepoint) :=
    figureEight_hasFourProngsAtBasepoint.map hf
  have hcard : 4 ≤ 3 := planarTheta_prongCard_le_three hprongs
  omega

/-- Example 58.3 (4): the planar theta space is not homeomorphic to a deformation retract
of the figure eight. -/
theorem planarTheta_not_homeomorphic_deformationRetract_figureEight :
    ¬ ∃ A : Set FigureEight, Set.IsDeformationRetract A ∧ Nonempty (PlanarTheta ≃ₜ A) := by
  -- Again forget the alleged retract and retain the induced embedding into the ambient graph.
  rintro ⟨A, _, ⟨e⟩⟩
  let f : PlanarTheta → FigureEight := fun x ↦ (e x : FigureEight)
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  -- The two theta vertices would both map to the unique triple-prong figure-eight point.
  obtain ⟨p, q, hpq, hp, hq⟩ := planarTheta_exists_two_tripleProngPoints
  have hpImage : HasNProngsAt 3 (f p) := hp.map hf
  have hqImage : HasNProngsAt 3 (f q) := hq.map hf
  have hfp : f p = FigureEight.basepoint :=
    figureEight_eq_basepoint_of_threeProngs hpImage
  have hfq : f q = FigureEight.basepoint :=
    figureEight_eq_basepoint_of_threeProngs hqImage
  exact hpq (hf.injective (hfp.trans hfq.symm))
