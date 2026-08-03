module

public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Definition_58_3.HomotopyType
public import Topology_Munkres_2000.Book.Example_58_3.PlaneModels

import Topology_Munkres_2000.Book.Exercise_58_4
import all Topology_Munkres_2000.Book.Definition_53_5.FigureEight
import all Topology_Munkres_2000.Book.Example_58_2.PlanarFigureEight
import all Topology_Munkres_2000.Book.Example_58_3.PlaneModels
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Euclidean.Sphere.Basic

public section

noncomputable section

/-- Helper for Example 58.4: the figure-eight carrier is closed in the torus. -/
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

/-- Helper for Example 58.4: the figure eight inherits compactness from the compact torus. -/
private theorem figureEightCompactSpace : CompactSpace FigureEight := by
  -- A closed subspace of a compact space is compact.
  exact isCompact_iff_compactSpace.mp isClosed_figureEightCarrier.isCompact

/-- Helper for Example 58.4: the coordinate difference realizes the abstract figure eight
as two tangent circles in the complex plane. -/
private def figureEightPlanarMap (x : FigureEight) : ℂ :=
  (x.1.1 - x.1.2) / 2

/-- Helper for Example 58.4: the planar realization of the figure eight is continuous. -/
private theorem continuous_figureEightPlanarMap : Continuous figureEightPlanarMap := by
  -- Continuity follows from the two coordinate projections and complex arithmetic.
  unfold figureEightPlanarMap
  fun_prop

/-- Helper for Example 58.4: two unit complex numbers whose sum is `2` are both `1`. -/
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

/-- Helper for Example 58.4: the planar coordinate realization separates points of the
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

/-- Helper for Example 58.4: the planar coordinate realization is a topological embedding. -/
private theorem isEmbedding_figureEightPlanarMap :
    Topology.IsEmbedding figureEightPlanarMap := by
  -- Compactness of the domain upgrades the continuous injection to a closed embedding.
  letI : CompactSpace FigureEight := figureEightCompactSpace
  exact (continuous_figureEightPlanarMap.isClosedEmbedding
    injective_figureEightPlanarMap).isEmbedding

/-- Helper for Example 58.4: the two normalized punctures are distinct. -/
private theorem normalizedPunctures_ne :
    DoublyPuncturedPlane.leftPuncture ≠ DoublyPuncturedPlane.rightPuncture := by
  -- The chosen punctures are the distinct real points `-1 / 2` and `1 / 2`.
  unfold DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture
  norm_num

/-- Helper for Example 58.4: the normalized punctures are distance one apart. -/
private theorem normalizedPunctures_dist :
    dist DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture = 1 := by
  -- Compute the distance between the two real points directly in `ℂ`.
  unfold DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture
  rw [Complex.dist_eq]
  norm_num

/-- Helper for Example 58.4: the reversed distance between the normalized punctures is one. -/
private theorem normalizedPunctures_dist_rev :
    dist DoublyPuncturedPlane.rightPuncture DoublyPuncturedPlane.leftPuncture = 1 := by
  -- Symmetry reduces the reversed distance to the preceding computation.
  calc
    dist DoublyPuncturedPlane.rightPuncture DoublyPuncturedPlane.leftPuncture =
        dist DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture :=
      dist_comm _ _
    _ = 1 := normalizedPunctures_dist

/-- Helper for Example 58.4: the coordinate realization has precisely the normalized planar
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

/-- Helper for Example 58.4: every point of the normalized planar figure eight avoids both
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

/-- Helper for Example 58.4: the coordinate realization regarded as a map into the normalized
doubly punctured plane. -/
private def figureEightDoublyPuncturedMap (x : FigureEight) : DoublyPuncturedPlane :=
  ⟨figureEightPlanarMap x,
    normalizedPlanarFigureEight_avoidsPunctures
      (range_figureEightPlanarMap ▸ Set.mem_range_self x)⟩

/-- Helper for Example 58.4: coercing the punctured-plane realization recovers its planar
coordinate value. -/
private theorem coe_figureEightDoublyPuncturedMap (x : FigureEight) :
    (figureEightDoublyPuncturedMap x : ℂ) = figureEightPlanarMap x := by
  -- The codomain restriction changes only the stored puncture-avoidance proof.
  rfl

/-- Helper for Example 58.4: composing the punctured-plane realization with its subtype
projection is the original planar coordinate map. -/
private theorem subtypeVal_comp_figureEightDoublyPuncturedMap :
    Subtype.val ∘ figureEightDoublyPuncturedMap = figureEightPlanarMap := by
  -- Extensionality exposes the preceding pointwise coercion formula.
  funext x
  exact coe_figureEightDoublyPuncturedMap x

/-- Helper for Example 58.4: the punctured-plane coordinate realization remains an embedding. -/
private theorem isEmbedding_figureEightDoublyPuncturedMap :
    Topology.IsEmbedding figureEightDoublyPuncturedMap := by
  -- Composing with the ambient subtype inclusion recovers the verified planar embedding.
  have hcontinuous : Continuous figureEightDoublyPuncturedMap :=
    continuous_figureEightPlanarMap.subtype_mk _
  apply Topology.IsEmbedding.of_comp hcontinuous continuous_subtype_val
  rw [subtypeVal_comp_figureEightDoublyPuncturedMap]
  exact isEmbedding_figureEightPlanarMap

/-- Helper for Example 58.4: the punctured-plane realization has exactly the normalized planar
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

/-- Helper for Example 58.4: the abstract figure eight is homeomorphic to the normalized planar
figure-eight deformation retract. -/
private theorem figureEightHomeomorphNormalizedPlanarFigureEight :
    Nonempty
      (FigureEight ≃ₜ
        PlanarFigureEight.inComplement DoublyPuncturedPlane.leftPuncture
          DoublyPuncturedPlane.rightPuncture) := by
  -- Restrict the punctured-plane embedding to its computed range.
  exact ⟨isEmbedding_figureEightDoublyPuncturedMap.toHomeomorph.trans
    (Homeomorph.setCongr range_figureEightDoublyPuncturedMap)⟩

/-- Helper for Example 58.4: a subtype cut out inside a containing subtype is homeomorphic to
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

/-- Helper for Example 58.4: every point of the planar theta carrier avoids the two normalized
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

/-- Helper for Example 58.4: the nested planar-theta retract is homeomorphic to the direct
planar theta carrier. -/
private def planarThetaRetractHomeomorph :
    PlanarTheta.inDoublyPuncturedPlane ≃ₜ PlanarTheta :=
  nestedSubtypeHomeomorph
    {z : ℂ | z ≠ DoublyPuncturedPlane.leftPuncture ∧
      z ≠ DoublyPuncturedPlane.rightPuncture}
    PlanarTheta.carrier planarTheta_avoidsPunctures

/-- Helper for Example 58.4: `HasNProngsAt n x` records `n` embedded arcs beginning at
`x` whose pairwise intersections consist only of `x`. -/
private def HasNProngsAt {X : Type*} [TopologicalSpace X] (n : ℕ) (x : X) : Prop :=
  ∃ γ : Fin n → C(unitInterval, X),
    (∀ i, γ i 0 = x) ∧
      (∀ i, Topology.IsEmbedding (γ i)) ∧
        ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {x}

/-- Helper for Example 58.4: an embedding preserves every finite embedded-prong
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

/-- Helper for Example 58.4: discarding prongs preserves a finite prong configuration. -/
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

/-- Helper for Example 58.4: finitely many pairwise disjoint embedded prongs meet some
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

/-- Helper for Example 58.4: three points common to the unit circle and a second nonconcentric
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

/-- Helper for Example 58.4: distance between two points on the imaginary axis is the absolute
difference of their imaginary coordinates. -/
private theorem dist_eq_abs_im_sub_of_re_eq_zero {z w : ℂ}
    (hz : z.re = 0) (hw : w.re = 0) : dist z w = |z.im - w.im| := by
  -- Expand the complex norm; the real-coordinate contribution vanishes.
  rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, hz, hw]
  simp only [sub_self, zero_mul, zero_add]
  rw [← pow_two, Real.sqrt_sq_eq_abs]

/-- Helper for Example 58.4: three points of the imaginary axis on one metric sphere cannot be
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

/-- Helper for Example 58.4: on the bounded imaginary diameter, a sphere centered at either
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

/-- Helper for Example 58.4: the positive quarter-circle parameterization is continuous. -/
private theorem continuous_positiveQuarterCircleArc :
    Continuous (fun t : unitInterval ↦ Circle.exp ((Real.pi / 2) * (t : ℝ))) := by
  -- This is the circle exponential composed with a linear parameter map.
  fun_prop

/-- Helper for Example 58.4: the positive quarter-circle arc starts at the circle basepoint. -/
private theorem positiveQuarterCircleArc_zero :
    Circle.exp ((Real.pi / 2) * ((0 : unitInterval) : ℝ)) = 1 := by
  -- At parameter zero the exponential angle is zero.
  simp

/-- Helper for Example 58.4: the positive quarter-circle arc from the circle basepoint. -/
private def positiveQuarterCircleArc : C(unitInterval, Circle) :=
  ⟨fun t ↦ Circle.exp ((Real.pi / 2) * (t : ℝ)), continuous_positiveQuarterCircleArc⟩

/-- Helper for Example 58.4: the negative quarter-circle parameterization is continuous. -/
private theorem continuous_negativeQuarterCircleArc :
    Continuous (fun t : unitInterval ↦ Circle.exp (-(Real.pi / 2) * (t : ℝ))) := by
  -- This is again the circle exponential composed with a linear parameter map.
  fun_prop

/-- Helper for Example 58.4: the negative quarter-circle arc starts at the circle basepoint. -/
private theorem negativeQuarterCircleArc_zero :
    Circle.exp (-(Real.pi / 2) * ((0 : unitInterval) : ℝ)) = 1 := by
  -- At parameter zero the exponential angle is zero.
  simp

/-- Helper for Example 58.4: the negative quarter-circle arc from the circle basepoint. -/
private def negativeQuarterCircleArc : C(unitInterval, Circle) :=
  ⟨fun t ↦ Circle.exp (-(Real.pi / 2) * (t : ℝ)), continuous_negativeQuarterCircleArc⟩

/-- Helper for Example 58.4: the positive quarter-circle parameterization is injective. -/
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

/-- Helper for Example 58.4: the negative quarter-circle parameterization is injective. -/
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

/-- Helper for Example 58.4: the positive quarter-circle arc is a topological embedding. -/
private theorem isEmbedding_positiveQuarterCircleArc :
    Topology.IsEmbedding positiveQuarterCircleArc := by
  -- Compactness of `unitInterval` upgrades the continuous injection to an embedding.
  exact (positiveQuarterCircleArc.continuous.isClosedEmbedding
    positiveQuarterCircleArc_injective).isEmbedding

/-- Helper for Example 58.4: the negative quarter-circle arc is a topological embedding. -/
private theorem isEmbedding_negativeQuarterCircleArc :
    Topology.IsEmbedding negativeQuarterCircleArc := by
  -- Compactness of `unitInterval` upgrades the continuous injection to an embedding.
  exact (negativeQuarterCircleArc.continuous.isClosedEmbedding
    negativeQuarterCircleArc_injective).isEmbedding

/-- Helper for Example 58.4: the positive and negative quarter-circle arcs meet only at their
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

/-- Helper for Example 58.4: points on the first coordinate circle lie in the figure eight. -/
private theorem firstFigureEightCircle_mem (z : Circle) :
    (z, (1 : Circle)) ∈ FigureEight.carrier := by
  -- The second coordinate is the circle basepoint.
  exact (FigureEight.mem_iff _).mpr (Or.inl rfl)

/-- Helper for Example 58.4: inclusion of the first coordinate circle into the figure eight. -/
private def firstFigureEightCircle (z : Circle) : FigureEight :=
  ⟨(z, 1), firstFigureEightCircle_mem z⟩

/-- Helper for Example 58.4: the first coordinate-circle inclusion is continuous. -/
private theorem continuous_firstFigureEightCircle : Continuous firstFigureEightCircle := by
  -- It is the product inclusion with a constant second coordinate, restricted to the carrier.
  exact (continuous_id.prodMk continuous_const).subtype_mk _

/-- Helper for Example 58.4: the first coordinate-circle inclusion as a continuous map. -/
private def firstFigureEightCircleMap : C(Circle, FigureEight) :=
  ⟨firstFigureEightCircle, continuous_firstFigureEightCircle⟩

/-- Helper for Example 58.4: the bundled first-circle inclusion evaluates as its underlying
subtype map. -/
private theorem firstFigureEightCircleMap_apply (z : Circle) :
    firstFigureEightCircleMap z = firstFigureEightCircle z := by
  -- Bundling continuity does not change pointwise values.
  rfl

/-- Helper for Example 58.4: the first coordinate-circle inclusion sends `1` to the
figure-eight basepoint. -/
private theorem firstFigureEightCircle_one :
    firstFigureEightCircle 1 = FigureEight.basepoint := by
  -- Both subtype points have the same pair of circle coordinates.
  apply Subtype.ext
  rfl

/-- Helper for Example 58.4: inclusion of the first coordinate circle is an embedding. -/
private theorem isEmbedding_firstFigureEightCircle :
    Topology.IsEmbedding firstFigureEightCircle := by
  -- Codomain restriction of the standard product inclusion preserves embedding.
  exact (isEmbedding_prodMkLeft (1 : Circle)).codRestrict _ _

/-- Helper for Example 58.4: points on the second coordinate circle lie in the figure eight. -/
private theorem secondFigureEightCircle_mem (z : Circle) :
    ((1 : Circle), z) ∈ FigureEight.carrier := by
  -- The first coordinate is the circle basepoint.
  exact (FigureEight.mem_iff _).mpr (Or.inr rfl)

/-- Helper for Example 58.4: inclusion of the second coordinate circle into the figure eight. -/
private def secondFigureEightCircle (z : Circle) : FigureEight :=
  ⟨(1, z), secondFigureEightCircle_mem z⟩

/-- Helper for Example 58.4: the second coordinate-circle inclusion is continuous. -/
private theorem continuous_secondFigureEightCircle : Continuous secondFigureEightCircle := by
  -- It is the product inclusion with a constant first coordinate, restricted to the carrier.
  exact (continuous_const.prodMk continuous_id).subtype_mk _

/-- Helper for Example 58.4: the second coordinate-circle inclusion as a continuous map. -/
private def secondFigureEightCircleMap : C(Circle, FigureEight) :=
  ⟨secondFigureEightCircle, continuous_secondFigureEightCircle⟩

/-- Helper for Example 58.4: the bundled second-circle inclusion evaluates as its underlying
subtype map. -/
private theorem secondFigureEightCircleMap_apply (z : Circle) :
    secondFigureEightCircleMap z = secondFigureEightCircle z := by
  -- Bundling continuity does not change pointwise values.
  rfl

/-- Helper for Example 58.4: composing the bundled first-circle inclusion agrees pointwise with
ordinary function composition. -/
private theorem coe_firstFigureEightCircleMap_comp (γ : C(unitInterval, Circle)) :
    ⇑(firstFigureEightCircleMap.comp γ) = firstFigureEightCircle ∘ γ := by
  -- Compare the two functions at each parameter.
  funext t
  exact firstFigureEightCircleMap_apply (γ t)

/-- Helper for Example 58.4: composing the bundled second-circle inclusion agrees pointwise with
ordinary function composition. -/
private theorem coe_secondFigureEightCircleMap_comp (γ : C(unitInterval, Circle)) :
    ⇑(secondFigureEightCircleMap.comp γ) = secondFigureEightCircle ∘ γ := by
  -- Compare the two functions at each parameter.
  funext t
  exact secondFigureEightCircleMap_apply (γ t)

/-- Helper for Example 58.4: the second coordinate-circle inclusion sends `1` to the
figure-eight basepoint. -/
private theorem secondFigureEightCircle_one :
    secondFigureEightCircle 1 = FigureEight.basepoint := by
  -- Both subtype points have the same pair of circle coordinates.
  apply Subtype.ext
  rfl

/-- Helper for Example 58.4: inclusion of the second coordinate circle is an embedding. -/
private theorem isEmbedding_secondFigureEightCircle :
    Topology.IsEmbedding secondFigureEightCircle := by
  -- Codomain restriction of the other standard product inclusion preserves embedding.
  exact (isEmbedding_prodMkRight (1 : Circle)).codRestrict _ _

/-- Helper for Example 58.4: injective postcomposition transports a computed intersection of
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

/-- Helper for Example 58.4: arcs in the two coordinate circles starting at `1` meet in the
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

/-- Helper for Example 58.4: the four canonical quarter-circle prongs at the figure-eight
basepoint. -/
private def figureEightBasepointProng : Fin 4 → C(unitInterval, FigureEight) :=
  ![firstFigureEightCircleMap.comp positiveQuarterCircleArc,
    firstFigureEightCircleMap.comp negativeQuarterCircleArc,
    secondFigureEightCircleMap.comp positiveQuarterCircleArc,
    secondFigureEightCircleMap.comp negativeQuarterCircleArc]

/-- Helper for Example 58.4: the zeroth canonical prong is the positive first-circle arc. -/
private theorem figureEightBasepointProng_zero :
    figureEightBasepointProng 0 =
      firstFigureEightCircleMap.comp positiveQuarterCircleArc := by
  -- This is the zeroth entry of the defining four-vector.
  rfl

/-- Helper for Example 58.4: the first canonical prong is the negative first-circle arc. -/
private theorem figureEightBasepointProng_one :
    figureEightBasepointProng 1 =
      firstFigureEightCircleMap.comp negativeQuarterCircleArc := by
  -- This is the first entry of the defining four-vector.
  rfl

/-- Helper for Example 58.4: the second canonical prong is the positive second-circle arc. -/
private theorem figureEightBasepointProng_two :
    figureEightBasepointProng 2 =
      secondFigureEightCircleMap.comp positiveQuarterCircleArc := by
  -- This is the second entry of the defining four-vector.
  rfl

/-- Helper for Example 58.4: the third canonical prong is the negative second-circle arc. -/
private theorem figureEightBasepointProng_three :
    figureEightBasepointProng 3 =
      secondFigureEightCircleMap.comp negativeQuarterCircleArc := by
  -- This is the third entry of the defining four-vector.
  rfl

/-- Helper for Example 58.4: the two bundled quarter-arcs in the first coordinate circle meet
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

/-- Helper for Example 58.4: the two bundled quarter-arcs in the second coordinate circle meet
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

/-- Helper for Example 58.4: bundled arcs in the two coordinate circles starting at `1` meet
only at the figure-eight basepoint. -/
private theorem range_firstCircleMapArc_inter_secondCircleMapArc
    {γ δ : C(unitInterval, Circle)} (hγ : γ 0 = 1) (hδ : δ 0 = 1) :
    Set.range (firstFigureEightCircleMap.comp γ) ∩
      Set.range (secondFigureEightCircleMap.comp δ) = {FigureEight.basepoint} := by
  -- The continuous-map wrappers have the same pointwise values as the underlying inclusions.
  rw [coe_firstFigureEightCircleMap_comp, coe_secondFigureEightCircleMap_comp]
  exact range_firstCircleArc_inter_secondCircleArc hγ hδ

/-- Helper for Example 58.4: the figure-eight basepoint supports four embedded prongs. -/
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

/-- Helper for Example 58.4: `-Complex.I` lies on the unit circle. -/
private theorem negI_mem_unitCircle :
    (-Complex.I : ℂ) ∈ (Submonoid.unitSphere ℂ : Set ℂ) := by
  -- Its complex norm is one.
  have hnorm : ‖(-Complex.I : ℂ)‖ = 1 := by
    norm_num
  exact mem_sphere_zero_iff_norm.mpr hnorm

/-- Helper for Example 58.4: the lower imaginary unit as a point of `Circle`. -/
private def circleNegI : Circle :=
  ⟨-Complex.I, negI_mem_unitCircle⟩

/-- Helper for Example 58.4: the lower imaginary unit lies in the planar theta carrier. -/
private theorem planarThetaLowerVertex_mem :
    (-Complex.I : ℂ) ∈ PlanarTheta.carrier := by
  -- It lies on the unit-circle branch of the theta carrier.
  have hnorm : ‖(-Complex.I : ℂ)‖ = 1 := by
    norm_num
  exact (PlanarTheta.mem_iff _).mpr (Or.inl hnorm)

/-- Helper for Example 58.4: the lower branch vertex of the planar theta space. -/
private def planarThetaLowerVertex : PlanarTheta :=
  ⟨-Complex.I, planarThetaLowerVertex_mem⟩

/-- Helper for Example 58.4: every unit-circle point lies in the planar theta carrier. -/
private theorem planarThetaCircle_mem (z : Circle) : (z : ℂ) ∈ PlanarTheta.carrier := by
  -- The circle norm supplies the first disjunct in the carrier description.
  exact (PlanarTheta.mem_iff _).mpr (Or.inl (Circle.norm_coe z))

/-- Helper for Example 58.4: inclusion of the unit-circle branch into the planar theta space. -/
private def planarThetaCircle (z : Circle) : PlanarTheta :=
  ⟨z, planarThetaCircle_mem z⟩

/-- Helper for Example 58.4: the circle-branch inclusion sends the lower imaginary unit to
the lower theta vertex. -/
private theorem planarThetaCircle_circleNegI :
    planarThetaCircle circleNegI = planarThetaLowerVertex := by
  -- Both subtype points have the same ambient complex coordinate.
  apply Subtype.ext
  rfl

/-- Helper for Example 58.4: the unit-circle branch inclusion into planar theta is continuous. -/
private theorem continuous_planarThetaCircle : Continuous planarThetaCircle := by
  -- It is the circle subtype inclusion, restricted to the theta carrier.
  exact continuous_subtype_val.subtype_mk _

/-- Helper for Example 58.4: the unit-circle branch inclusion as a continuous map. -/
private def planarThetaCircleMap : C(Circle, PlanarTheta) :=
  ⟨planarThetaCircle, continuous_planarThetaCircle⟩

/-- Helper for Example 58.4: the unit-circle branch inclusion into planar theta is an embedding. -/
private theorem isEmbedding_planarThetaCircle : Topology.IsEmbedding planarThetaCircle := by
  -- Codomain restriction of the circle subtype inclusion preserves embedding.
  exact Topology.IsEmbedding.subtypeVal.codRestrict _ _

/-- Helper for Example 58.4: bundled composition with the theta circle inclusion is ordinary
function composition pointwise. -/
private theorem coe_planarThetaCircleMap_comp (γ : C(unitInterval, Circle)) :
    ⇑(planarThetaCircleMap.comp γ) = planarThetaCircle ∘ γ := by
  -- Compare the two functions at each interval parameter.
  rfl

/-- Helper for Example 58.4: rotating the positive quarter-circle arc by a circle point. -/
private theorem continuous_circleMulLeft (v : Circle) :
    Continuous (fun z : Circle ↦ v * z) := by
  -- Left multiplication is continuous in the circle topological group.
  fun_prop

/-- Helper for Example 58.4: left multiplication by a fixed circle point as a continuous map. -/
private def circleMulLeftMap (v : Circle) : C(Circle, Circle) :=
  ⟨fun z ↦ v * z, continuous_circleMulLeft v⟩

/-- Helper for Example 58.4: the bundled circle rotation has the expected underlying
function. -/
private theorem coe_circleMulLeftMap (v : Circle) :
    ⇑(circleMulLeftMap v) = fun z ↦ v * z := by
  -- Bundling continuity does not alter pointwise multiplication.
  rfl

/-- Helper for Example 58.4: bundled composition with a circle rotation is ordinary function
composition pointwise. -/
private theorem coe_circleMulLeftMap_comp (v : Circle) (γ : C(unitInterval, Circle)) :
    ⇑((circleMulLeftMap v).comp γ) = ⇑(circleMulLeftMap v) ∘ γ := by
  -- Compare the two functions at each interval parameter.
  rfl

/-- Helper for Example 58.4: left multiplication by a circle point sends `1` to that point. -/
private theorem circleMulLeftMap_one (v : Circle) : circleMulLeftMap v 1 = v := by
  -- This is the multiplicative identity law.
  exact mul_one v

/-- Helper for Example 58.4: left multiplication by a fixed circle point is an embedding. -/
private theorem isEmbedding_circleMulLeftMap (v : Circle) :
    Topology.IsEmbedding (circleMulLeftMap v) := by
  -- Its underlying function is the standard left-multiplication homeomorphism.
  rw [coe_circleMulLeftMap]
  exact (Homeomorph.mulLeft v).isEmbedding

/-- Helper for Example 58.4: rotating the positive quarter-circle arc by a circle point. -/
private def rotatedPositiveQuarterCircleArc (v : Circle) : C(unitInterval, Circle) :=
  (circleMulLeftMap v).comp positiveQuarterCircleArc

/-- Helper for Example 58.4: rotating the negative quarter-circle arc by a circle point. -/
private def rotatedNegativeQuarterCircleArc (v : Circle) : C(unitInterval, Circle) :=
  (circleMulLeftMap v).comp negativeQuarterCircleArc

/-- Helper for Example 58.4: the rotated positive quarter-circle arc starts at its rotation
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

/-- Helper for Example 58.4: the rotated negative quarter-circle arc starts at its rotation
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

/-- Helper for Example 58.4: the rotated positive quarter-circle arc is an embedding. -/
private theorem isEmbedding_rotatedPositiveQuarterCircleArc (v : Circle) :
    Topology.IsEmbedding (rotatedPositiveQuarterCircleArc v) := by
  -- Compose the quarter-arc embedding with rotation by a homeomorphism.
  exact (isEmbedding_circleMulLeftMap v).comp isEmbedding_positiveQuarterCircleArc

/-- Helper for Example 58.4: the rotated negative quarter-circle arc is an embedding. -/
private theorem isEmbedding_rotatedNegativeQuarterCircleArc (v : Circle) :
    Topology.IsEmbedding (rotatedNegativeQuarterCircleArc v) := by
  -- Compose the quarter-arc embedding with rotation by a homeomorphism.
  exact (isEmbedding_circleMulLeftMap v).comp isEmbedding_negativeQuarterCircleArc

/-- Helper for Example 58.4: the two rotated quarter-circle arcs meet only at their rotation
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

/-- Helper for Example 58.4: the two rotated circle arcs, included into planar theta, meet only
at their common vertex. -/
private theorem range_planarThetaRotatedQuarterArcs_inter (v : Circle) :
    Set.range (planarThetaCircleMap.comp (rotatedPositiveQuarterCircleArc v)) ∩
      Set.range (planarThetaCircleMap.comp (rotatedNegativeQuarterCircleArc v)) =
        {planarThetaCircle v} := by
  -- Injectivity of the circle-branch inclusion transports the rotated-circle intersection.
  rw [coe_planarThetaCircleMap_comp, coe_planarThetaCircleMap_comp]
  exact range_comp_inter_range_comp_of_injective isEmbedding_planarThetaCircle.injective
    (range_rotatedQuarterCircleArcs_inter v)

/-- Helper for Example 58.4: the lower vertical-diameter parameter lies in the theta carrier. -/
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

/-- Helper for Example 58.4: the lower half of the vertical theta diameter. -/
private def planarThetaLowerVertical (t : unitInterval) : PlanarTheta :=
  ⟨((t : ℂ) - 1) * Complex.I, planarThetaLowerVertical_mem t⟩

/-- Helper for Example 58.4: the lower vertical-diameter arc is continuous. -/
private theorem continuous_planarThetaLowerVertical : Continuous planarThetaLowerVertical := by
  -- The ambient complex formula is polynomial in the real interval coordinate.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Example 58.4: the lower vertical-diameter arc as a continuous map. -/
private def planarThetaLowerVerticalMap : C(unitInterval, PlanarTheta) :=
  ⟨planarThetaLowerVertical, continuous_planarThetaLowerVertical⟩

/-- Helper for Example 58.4: the lower vertical-diameter arc starts at the lower theta vertex. -/
private theorem planarThetaLowerVertical_zero :
    planarThetaLowerVerticalMap 0 = planarThetaLowerVertex := by
  -- Evaluate the ambient affine formula at zero.
  apply Subtype.ext
  norm_num [planarThetaLowerVerticalMap, planarThetaLowerVertical,
    planarThetaLowerVertex]

/-- Helper for Example 58.4: the norm of a unit-interval coordinate minus one is its distance
from the right endpoint. -/
private theorem norm_unitInterval_coe_sub_one (t : unitInterval) :
    ‖(t : ℂ) - 1‖ = 1 - (t : ℝ) := by
  -- Reduce the complex norm of a real number to its absolute value.
  have hnonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have hneg : (t : ℂ) - 1 = -(((1 - (t : ℝ) : ℝ)) : ℂ) := by
    norm_num
  rw [hneg, norm_neg]
  exact Complex.norm_of_nonneg hnonneg

/-- Helper for Example 58.4: the lower vertical-diameter arc is injective. -/
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

/-- Helper for Example 58.4: the lower vertical-diameter arc is an embedding. -/
private theorem isEmbedding_planarThetaLowerVertical :
    Topology.IsEmbedding planarThetaLowerVerticalMap := by
  -- Compactness of the interval upgrades the continuous injection to an embedding.
  exact (planarThetaLowerVerticalMap.continuous.isClosedEmbedding
    planarThetaLowerVertical_injective).isEmbedding

/-- Helper for Example 58.4: a circle arc beginning at the lower theta vertex meets the lower
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

/-- Helper for Example 58.4: the three canonical prongs issuing from the lower theta vertex. -/
private def planarThetaLowerProng : Fin 3 → C(unitInterval, PlanarTheta) :=
  ![planarThetaCircleMap.comp (rotatedPositiveQuarterCircleArc circleNegI),
    planarThetaCircleMap.comp (rotatedNegativeQuarterCircleArc circleNegI),
    planarThetaLowerVerticalMap]

/-- Helper for Example 58.4: the lower theta vertex supports three embedded prongs. -/
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

/-- Helper for Example 58.4: complex negation preserves the planar theta carrier. -/
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

/-- Helper for Example 58.4: reflection through the origin acts on the planar theta space. -/
private def planarThetaNeg (z : PlanarTheta) : PlanarTheta :=
  ⟨-(z : ℂ), planarTheta_neg_mem z⟩

/-- Helper for Example 58.4: reflection through the origin embeds the planar theta space in
itself. -/
private theorem isEmbedding_planarThetaNeg : Topology.IsEmbedding planarThetaNeg := by
  -- Restrict the ambient negation homeomorphism to the invariant theta carrier.
  exact ((Homeomorph.neg ℂ).isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict
    PlanarTheta.carrier planarTheta_neg_mem

/-- Helper for Example 58.4: the lower theta vertex differs from its reflection through the
origin. -/
private theorem planarThetaLowerVertex_ne_neg :
    planarThetaLowerVertex ≠ planarThetaNeg planarThetaLowerVertex := by
  -- Their imaginary coordinates are respectively `-1` and `1`.
  intro hvertices
  have him := congrArg (fun z : PlanarTheta ↦ (z : ℂ).im) hvertices
  norm_num [planarThetaLowerVertex, planarThetaNeg] at him

/-- Helper for Example 58.4: no point of the planar theta space supports more than three
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

/-- Helper for Example 58.4: the planar theta space has two distinct points that each support
three pairwise disjoint embedded prongs. -/
private theorem planarTheta_exists_two_tripleProngPoints :
    ∃ p q : PlanarTheta, p ≠ q ∧ HasNProngsAt 3 p ∧ HasNProngsAt 3 q := by
  -- Reflect the verified lower-vertex prongs to the distinct upper vertex.
  refine ⟨planarThetaLowerVertex, planarThetaNeg planarThetaLowerVertex,
    planarThetaLowerVertex_ne_neg, planarThetaLowerVertex_hasThreeProngs, ?_⟩
  exact planarThetaLowerVertex_hasThreeProngs.map isEmbedding_planarThetaNeg

/-- Helper for Example 58.4: a figure-eight point supporting three pairwise disjoint embedded
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

/-- Example 58.4: the figure eight and the planar theta space are homotopy equivalent. -/
theorem figureEight_sameHomotopyType_planarTheta :
    SameHomotopyType FigureEight PlanarTheta := by
  -- Use the explicit folding equivalence between the two graph models.
  exact SameHomotopyType.ofHomotopyEquiv figureEightHomotopyEquiv

/-- Example 58.4: the figure eight cannot be embedded in the planar theta space. -/
theorem figureEight_not_embeddableIn_planarTheta :
    ¬ ∃ f : FigureEight → PlanarTheta, Topology.IsEmbedding f := by
  -- Transport the four verified basepoint prongs; the theta valence bound gives `4 ≤ 3`.
  rintro ⟨f, hf⟩
  have hprongs : HasNProngsAt 4 (f FigureEight.basepoint) :=
    figureEight_hasFourProngsAtBasepoint.map hf
  have hcard : 4 ≤ 3 := planarTheta_prongCard_le_three hprongs
  omega

/-- Example 58.4: the planar theta space cannot be embedded in the figure eight. -/
theorem planarTheta_not_embeddableIn_figureEight :
    ¬ ∃ f : PlanarTheta → FigureEight, Topology.IsEmbedding f := by
  -- Both triple-prong theta vertices would map to the unique triple-prong figure-eight point,
  -- contradicting injectivity of the alleged embedding.
  rintro ⟨f, hf⟩
  obtain ⟨p, q, hpq, hp, hq⟩ := planarTheta_exists_two_tripleProngPoints
  have hpImage : HasNProngsAt 3 (f p) := hp.map hf
  have hqImage : HasNProngsAt 3 (f q) := hq.map hf
  have hfp : f p = FigureEight.basepoint :=
    figureEight_eq_basepoint_of_threeProngs hpImage
  have hfq : f q = FigureEight.basepoint :=
    figureEight_eq_basepoint_of_threeProngs hqImage
  exact hpq (hf.injective (hfp.trans hfq.symm))
