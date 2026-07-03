

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_4_1 (from Chap02) -/
section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Set

/-- If `z` is an interior point of `C`, then every direction `y` admits a nonzero scalar step
from `z` that remains in `C`. This primitive bridge only uses the scalar norm, not an order on the
scalar field. -/
theorem forall_exists_ne_zero_add_smul_mem_of_mem_interior
    {C : Set E} {z : E} (hz : z ∈ interior C) :
    ∀ y : E, ∃ ε : 𝕜, ε ≠ 0 ∧ z + ε • y ∈ C := by
  intro y
  by_cases hy : y = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    simpa [hy] using interior_subset hz
  · rcases (Metric.mem_interior_iff_exists_pos_closedBall_subset).1 hz with ⟨δ, hδ, hball⟩
    let r : ℝ := δ / (2 * ‖y‖)
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hr : 0 < r := by
      dsimp [r]
      positivity
    obtain ⟨c, hc0, hcr⟩ := NormedField.exists_norm_lt 𝕜 (lt_min zero_lt_one hr)
    let ε : 𝕜 := c ^ 2
    have hε : 0 < ‖ε‖ := by
      dsimp [ε]
      exact norm_pos_iff.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mp hc0.ne'))
    have hεnorm : ‖ε‖ < r := by
      have hcr' : ‖c‖ < r := lt_of_lt_of_le hcr (min_le_right _ _)
      calc
        ‖ε‖ = ‖c‖ * ‖c‖ := by
          dsimp [ε]
          rw [pow_two, norm_mul]
        _ < ‖c‖ := by
          nlinarith [lt_of_lt_of_le hcr (min_le_left _ _)]
        _ < r := hcr'
    refine ⟨ε, norm_ne_zero_iff.mp hε.ne', ?_⟩
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show z + ε • y - z = ε • y by abel_nf, norm_smul]
    have hbound : ‖ε‖ * ‖y‖ < δ / 2 := by
      have hεnorm' : ‖ε‖ < δ / (2 * ‖y‖) := by
        simpa [r] using hεnorm
      have htmp : ‖ε‖ * (2 * ‖y‖) < δ := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖y‖)).mp hεnorm'
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      nlinarith
    linarith

end Set

end

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.4.1 characterizes ordinary interior points of a convex subset of
  a finite-dimensional ordered normed-field space by the existence of a positive
  step in every direction from the point.
- `core/canonical`: the owner notions are `Convex 𝕜`, `interior`, and the chapter owner theorem
  `Convex.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem` for relative interior,
  together with the full-dimensional bridge
  `intrinsicInterior_eq_interior_of_affineSpan_eq_top`.
- `bridge/view`: this item upgrades the relative-interior segment-prolongation criterion to the
  ordinary interior criterion by using the full-dimensionality forced by directional extension in
  every ambient direction.
- Domain-style sampling used here: `Metric.mem_interior_iff_exists_pos_closedBall_subset`,
  `Convex.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem`,
  `intrinsicInterior_eq_interior_of_affineSpan_eq_top`, and the algebraic bridge
  `Set.affineSpan_eq_top_of_forall_exists_ne_zero_lineMap_mem`.
- Primitive data vs derived API: the full-dimensionality bridge is stated from the primitive
  nonzero-step data, while the source-facing positive-step criterion is derived API over ordered
  scalars; the public criterion therefore belongs under the `Convex` owner abstraction rather than
  as a parallel global theorem.
- Layer target: this item stays `source-facing`, refined to owner-style `Convex` API.
-/

namespace Set

/-- If `z` is an interior point of `C`, then every direction `y` admits a positive scalar step
from `z` that remains in `C`. -/
theorem forall_exists_pos_add_smul_mem_of_mem_interior
    {C : Set E} {z : E} (hz : z ∈ interior C) :
    ∀ y : E, ∃ ε > (0 : 𝕜), z + ε • y ∈ C := by
  intro y
  by_cases hy : y = 0
  · refine ⟨1, by positivity, ?_⟩
    simpa [hy] using interior_subset hz
  · rcases (Metric.mem_interior_iff_exists_pos_closedBall_subset).1 hz with ⟨δ, hδ, hball⟩
    let r : ℝ := δ / (2 * ‖y‖)
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hr : 0 < r := by
      dsimp [r]
      positivity
    obtain ⟨c, hc0, hcr⟩ := NormedField.exists_norm_lt 𝕜 (lt_min zero_lt_one hr)
    let ε : 𝕜 := c ^ 2
    have hε : 0 < ε := by
      dsimp [ε]
      exact sq_pos_iff.mpr (norm_ne_zero_iff.mp hc0.ne')
    have hεnorm : ‖ε‖ < r := by
      have hcr' : ‖c‖ < r := lt_of_lt_of_le hcr (min_le_right _ _)
      calc
        ‖ε‖ = ‖c‖ * ‖c‖ := by
          dsimp [ε]
          rw [pow_two, norm_mul]
        _ < ‖c‖ := by
          nlinarith [lt_of_lt_of_le hcr (min_le_left _ _)]
        _ < r := hcr'
    refine ⟨ε, hε, ?_⟩
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show z + ε • y - z = ε • y by abel_nf, norm_smul]
    have hbound : ‖ε‖ * ‖y‖ < δ / 2 := by
      have hεnorm' : ‖ε‖ < δ / (2 * ‖y‖) := by
        simpa [r] using hεnorm
      have htmp : ‖ε‖ * (2 * ‖y‖) < δ := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖y‖)).mp hεnorm'
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      nlinarith
    linarith

end Set

end

section

variable {𝕜 V P : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [AddTorsor V P]

namespace Set

open AffineMap

/-- If every ambient direction from `z` admits a nonzero scalar step that stays in `C`, then
`C` is full-dimensional in the ambient affine space. -/
theorem affineSpan_eq_top_of_forall_exists_ne_zero_lineMap_mem
    (C : Set P) (z : P) (hz : ∀ x : P, ∃ μ : 𝕜, μ ≠ 0 ∧ lineMap z x μ ∈ C) :
    affineSpan 𝕜 C = ⊤ := by
  have hzC : z ∈ C := by
    rcases hz z with ⟨μ, hμ, hmem⟩
    simpa using hmem
  apply top_unique
  intro x _
  rcases hz x with ⟨μ, hμ, hp⟩
  have hzA : z ∈ affineSpan 𝕜 C := subset_affineSpan 𝕜 C hzC
  have hpA : lineMap z x μ ∈ affineSpan 𝕜 C := subset_affineSpan 𝕜 C hp
  have hxA : lineMap z (lineMap z x μ) μ⁻¹ ∈ affineSpan 𝕜 C :=
    AffineMap.lineMap_mem μ⁻¹ hzA hpA
  simpa [lineMap_lineMap_right, inv_mul_cancel₀ hμ] using hxA

end Set

end

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

namespace Convex

open AffineMap

/-- If every direction from `z` can be prolonged by a positive scalar while staying in a convex
set `C`, then `z` lies in `interior C`. -/
private theorem mem_interior_of_forall_exists_pos_add_smul_mem
    {C : Set E} {z : E} (hC : Convex 𝕜 C)
    (hz : ∀ y : E, ∃ ε > (0 : 𝕜), z + ε • y ∈ C) :
    z ∈ interior C := by
  have hzC : z ∈ C := by
    rcases hz 0 with ⟨ε, hε, hmem⟩
    simpa using hmem
  have hseg : ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C := by
    intro x hx
    rcases hz (z - x) with ⟨ε, hε, hmem⟩
    refine ⟨ε + 1, by linarith, ?_⟩
    rw [lineMap_apply_module']
    have hline : (ε + 1) • (z - x) + x = z + ε • (z - x) := by
      rw [sub_eq_add_neg, add_smul, one_smul]
      abel_nf
    simpa [hline] using hmem
  have hzri : z ∈ intrinsicInterior 𝕜 C :=
    (hC.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem).2 ⟨⟨z, hzC⟩, hseg⟩
  have hspan : affineSpan 𝕜 C = ⊤ := by
    refine Set.affineSpan_eq_top_of_forall_exists_ne_zero_lineMap_mem C z ?_
    intro x
    rcases hz (x - z) with ⟨ε, hε, hmem⟩
    refine ⟨ε, hε.ne', ?_⟩
    simpa [lineMap_apply_module', add_comm, add_left_comm, add_assoc] using hmem
  simpa [intrinsicInterior_eq_interior_of_affineSpan_eq_top hspan] using hzri

/-- Corollary 6.4.1: a point `z` of a convex set `C` lies in `interior C` if and only if, for
every direction `y`, some positive field-valued step `z + ε • y` still lies in `C`. -/
theorem mem_interior_iff_forall_exists_pos_add_smul_mem
    {C : Set E} {z : E} (hC : Convex 𝕜 C) :
    z ∈ interior C ↔ ∀ y : E, ∃ ε > (0 : 𝕜), z + ε • y ∈ C := by
  constructor
  · exact Set.forall_exists_pos_add_smul_mem_of_mem_interior
  · exact hC.mem_interior_of_forall_exists_pos_add_smul_mem

end Convex

end

/-! ### Text_6_4 (from Chap02) -/
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 6.4 records that the chapter unit ball `B` is closed and convex.
- `core/canonical`: the owner object is `closedBall (0 : E) 1`, with derived owner facts
  `Metric.isClosed_closedBall`; convexity is a derived property from the norm inequality at the
  primitive real-scalar action layer.
- `bridge/view`: Text 6.3 already provides the source-facing chapter notation `B` directly for the
  canonical owner `closedBall (0 : E) 1`, so this file states the textbook facts in that notation.
- Primitive data vs derived API: `B` is the only primitive object here; closedness and convexity
  are derived properties and should remain theorem-level API.
- Domain-style sampling used here: the source-facing chapter notation `B` from Text 6.3, the
  canonical owner `closedBall`, `Metric.isClosed_closedBall`, and the primitive norm inequalities
  `norm_add_le` and `norm_smul`.
- Owner choice: keep `closedBall` as the canonical owner and expose source-facing theorem surfaces
  through the chapter notation `B`.
- Layer target: source-facing theorem API over the canonical owner.
-/

section

variable {E : Type*} [PseudoMetricSpace E] [Zero E]

/- Owner-level closedness for Text 6.4: the canonical unit closed ball `closedBall (0 : E) 1`
is closed at the primitive pseudometric layer. -/
private theorem isClosed_unitClosedBall : IsClosed (Metric.closedBall (0 : E) (1 : ℝ)) := by
  simpa using (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : E) (1 : ℝ)))

/- Text 6.4 source-facing bridge: the chapter notation `B` for the unit closed ball is closed. -/
theorem isClosed_B : IsClosed (B : Set E) := by
  simpa [B_eq_closedBall] using (isClosed_unitClosedBall (E := E))

end

section

variable {E : Type*} [SeminormedAddCommGroup E] [SMul ℝ E] [NormSMulClass ℝ E]

/- Owner-level convexity for Text 6.4: the canonical unit closed ball `closedBall (0 : E) 1`
is convex. This only needs real scalar action and `norm_smul`. -/
private theorem convex_unitClosedBall : Convex ℝ (Metric.closedBall (0 : E) (1 : ℝ)) := by
  intro x hx y hy a b ha hb hab
  have hx' : ‖x‖ ≤ (1 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖y‖ ≤ (1 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  have hnorm : ‖a • x + b • y‖ ≤ (1 : ℝ) := by
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ := by rw [norm_smul, norm_smul]
      _ = a * ‖x‖ + b * ‖y‖ := by rw [Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by linarith [hab]
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/- Text 6.4 source-facing bridge: the chapter notation `B` for the unit closed ball is convex. -/
theorem convex_B : Convex ℝ (B : Set E) := by
  simpa [B_eq_closedBall] using (convex_unitClosedBall (E := E))

end

/-! ### Theorem_6_4 (from Chap02) -/
section

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.4 characterizes relative interior points of a nonempty convex set in
  a finite-dimensional ambient space by the ability to prolong every segment in the set past the
  candidate endpoint.
- `core/canonical`: the owner notions are `Convex 𝕜`, mathlib's canonical relative interior
  `intrinsicInterior 𝕜`, and the canonical affine-combination owner `AffineMap.lineMap`, with the
  owner-style chapter API organized under `namespace Convex`.
- `bridge/view`: Rockafellar's `ri C` is represented by `ri[𝕜](C)`.
- Domain-style sampling used here: `intrinsicInterior`, `AffineMap.lineMap`,
  `Convex.openSegment_intrinsicInterior_closure_subset_intrinsicInterior`, and the affine-basis
  bridge from convex hulls to nonempty interior in the affine span.
- Primitive data vs derived API: the primitive owner data is the convex set `C` together with
  `hC : Convex 𝕜 C`; the prolongation criterion is derived API and should therefore live on the
  `Convex` owner abstraction rather than as a parallel global theorem.
- Layer target: this item is a source-facing theorem stated directly in the canonical
  `intrinsicInterior` language.
-/

namespace Convex

open AffineMap

section Forward

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Theorem 6.4, forward direction: a point of `ri[𝕜](C)` admits a prolongation of
every segment in `C` past that point while staying in `C`. -/
-- Proof sketch: choose a closed ball in the affine span around `z` contained in `C`. For `x ≠ z`,
-- pick a very small scalar `δ > 0` and move from `z` a distance `δ • (z - x)`; the resulting
-- point is `lineMap x z (1 + δ)`, remains in the affine span of `C`, and lies inside the chosen
-- ball, hence in `C`.
theorem forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior
    {C : Set E} {z : E} (hz : z ∈ ri[𝕜](C)) :
    ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C := by
  intro x hx
  rcases (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).1 hz with
    ⟨hzA, ε, hε, hball⟩
  by_cases hxz : x = z
  · refine ⟨2, by norm_num, ?_⟩
    simpa [hxz] using hx
  · let r : ℝ := ε / (2 * ‖z - x‖)
    have hzx : 0 < ‖z - x‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr (by simpa [eq_comm] using hxz)
    have hr : 0 < r := by
      dsimp [r]
      positivity
    obtain ⟨c, hc0, hcr⟩ := NormedField.exists_norm_lt 𝕜 (lt_min zero_lt_one hr)
    let δ : 𝕜 := c ^ 2
    have hδ : 0 < δ := by
      dsimp [δ]
      exact sq_pos_iff.mpr (norm_ne_zero_iff.mp hc0.ne')
    have hδr : ‖δ‖ < r := by
      have hcr' : ‖c‖ < r := lt_of_lt_of_le hcr (min_le_right _ _)
      calc
        ‖δ‖ = ‖c‖ * ‖c‖ := by
          dsimp [δ]
          rw [pow_two, norm_mul]
        _ < ‖c‖ := by
          nlinarith [lt_of_lt_of_le hcr (min_le_left _ _)]
        _ < r := hcr'
    let w : E := lineMap x z (1 + δ)
    have hw : w = z + δ • (z - x) := by
      dsimp [w]
      rw [lineMap_apply_module', add_smul, one_smul]
      abel_nf
    have hwspan : w ∈ affineSpan 𝕜 C := by
      dsimp [w]
      exact AffineMap.lineMap_mem (1 + δ) (subset_affineSpan 𝕜 C hx) hzA
    have hdist : dist w z < ε := by
      rw [hw, dist_eq_norm]
      have hsub : z + δ • (z - x) - z = δ • (z - x) := by
        abel_nf
      rw [hsub, norm_smul]
      calc
        ‖δ‖ * ‖z - x‖ < r * ‖z - x‖ := by
          exact mul_lt_mul_of_pos_right hδr hzx
        _ = ε / 2 := by
          dsimp [r]
          field_simp [hzx.ne']
        _ < ε := by
          linarith
    have hwmem : w ∈ C :=
      hball <| by
        refine ⟨?_, hwspan⟩
        exact Metric.mem_closedBall.2 (le_of_lt hdist)
    exact ⟨1 + δ, by linarith, hwmem⟩

end Forward

section Reverse

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

private theorem homeomorph_interior_nonempty_iff {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (φ : α ≃ₜ β) (s : Set β) :
    (interior s).Nonempty ↔ (interior (φ ⁻¹' s)).Nonempty := by
  rw [← φ.image_symm, ← φ.symm.image_interior, Set.image_nonempty]

private theorem AffineBasis.centroid_mem_interior_convexHull {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (b : AffineBasis ι 𝕜 F) :
    Finset.univ.centroid 𝕜 b ∈ interior (convexHull 𝕜 (Set.range b)) := by
  haveI := b.nonempty
  haveI : FiniteDimensional 𝕜 F := b.finiteDimensional
  have hconv : convexHull 𝕜 (Set.range b) = ⋂ i, b.coord i ⁻¹' Set.Ici 0 := by
    ext x
    simp [b.convexHull_eq_nonneg_coord]
  rw [hconv, interior_iInter_of_finite]
  refine Set.mem_iInter.2 fun i ↦ ?_
  have hcont : Continuous (b.coord i) := continuous_barycentric_coord b i
  have hopen : IsOpen (b.coord i ⁻¹' Set.Ioi (0 : 𝕜)) :=
    hcont.isOpen_preimage _ isOpen_Ioi
  have hcoord :
      (b.coord i) ((Finset.univ : Finset ι).centroid 𝕜 b) =
        (↑((Finset.univ : Finset ι).card) : 𝕜)⁻¹ := by
    simpa using b.coord_apply_centroid (show i ∈ (Finset.univ : Finset ι) by simp)
  have hcoord_pos : 0 < (b.coord i) (Finset.univ.centroid 𝕜 b) := by
    rw [hcoord]
    refine inv_pos.mpr ?_
    have hcard_nat : 0 < (Finset.univ : Finset ι).card := Finset.card_pos.mpr Finset.univ_nonempty
    exact_mod_cast hcard_nat
  have hmem : Finset.univ.centroid 𝕜 b ∈ b.coord i ⁻¹' Set.Ioi (0 : 𝕜) := by
    simpa [Set.mem_preimage, Set.mem_Ioi] using hcoord_pos
  exact mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (hopen.mem_nhds hmem) (Set.preimage_mono Set.Ioi_subset_Ici_self)

section AffineSpanOpen

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem isOpen_affineSpan_eq_top {u : Set E} (hu : IsOpen u) (hne : u.Nonempty) :
    affineSpan 𝕜 u = ⊤ := by
  rcases hne with ⟨x, hx⟩
  refine top_unique ?_
  intro y hy
  by_cases hxy : y = x
  · subst y
    exact subset_affineSpan 𝕜 u hx
  · rcases Metric.isOpen_iff.mp hu x hx with ⟨ε, hε, hball⟩
    let r : ℝ := ε / (2 * ‖y - x‖)
    have hyx : 0 < ‖y - x‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr hxy
    have hr : 0 < r := by
      dsimp [r]
      positivity
    obtain ⟨c, hc0, hcr⟩ := NormedField.exists_norm_lt 𝕜 hr
    let z : E := lineMap x y c
    have hz_eq : z = x + c • (y - x) := by
      dsimp [z]
      rw [lineMap_apply_module']
      simp [add_comm]
    have hdist : dist z x < ε := by
      rw [hz_eq, dist_eq_norm]
      have hsub : x + c • (y - x) - x = c • (y - x) := by
        abel_nf
      rw [hsub, norm_smul]
      calc
        ‖c‖ * ‖y - x‖ < r * ‖y - x‖ := by
          exact mul_lt_mul_of_pos_right hcr hyx
        _ = ε / 2 := by
          dsimp [r]
          field_simp [hyx.ne']
        _ < ε := by
          linarith
    have hz : z ∈ u := hball <| Metric.mem_ball.2 hdist
    have hxA : x ∈ affineSpan 𝕜 u := subset_affineSpan 𝕜 u hx
    have hzA : z ∈ affineSpan 𝕜 u := subset_affineSpan 𝕜 u hz
    have hc : c ≠ 0 := norm_ne_zero_iff.mp hc0.ne'
    have hy_eq : y = lineMap x z c⁻¹ := by
      symm
      calc
        lineMap x z c⁻¹ = x + c⁻¹ • (z - x) := by
          rw [lineMap_apply_module']
          simp [add_comm]
        _ = x + c⁻¹ • (c • (y - x)) := by
          rw [hz_eq]
          congr 1
          abel_nf
        _ = x + (c⁻¹ * c) • (y - x) := by
          rw [smul_smul]
        _ = x + (y - x) := by
          rw [inv_mul_cancel₀ hc, one_smul]
        _ = y := by
          abel_nf
    simpa [hy_eq] using AffineMap.lineMap_mem c⁻¹ hxA hzA

end AffineSpanOpen

private theorem interior_convexHull_nonempty_iff_affineSpan_eq_top {s : Set E} :
    (interior (convexHull 𝕜 s)).Nonempty ↔ affineSpan 𝕜 s = ⊤ := by
  refine ⟨?_, ?_⟩
  · intro hs
    have htop :
        affineSpan 𝕜 (interior (convexHull 𝕜 s)) = ⊤ :=
      isOpen_affineSpan_eq_top isOpen_interior hs
    have hmono :
        affineSpan 𝕜 (interior (convexHull 𝕜 s)) ≤ affineSpan 𝕜 (convexHull 𝕜 s) :=
      affineSpan_mono 𝕜 interior_subset
    refine top_unique ?_
    rw [← htop]
    exact hmono.trans_eq (affineSpan_convexHull s)
  · intro h
    obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis h
    suffices (interior (convexHull 𝕜 (Set.range b))).Nonempty by
      rw [hb, Subtype.range_coe_subtype] at this
      exact this.mono <| interior_mono <| convexHull_mono hts
    lift t to Finset E using b.finite_set
    exact ⟨_, AffineBasis.centroid_mem_interior_convexHull b⟩

private theorem convex_interior_nonempty_iff_affineSpan_eq_top {s : Set E} (hs : Convex 𝕜 s) :
    (interior s).Nonempty ↔ affineSpan 𝕜 s = ⊤ := by
  rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top, hs.convexHull_eq]

theorem intrinsicInterior_nonempty {C : Set E} (hC : Convex 𝕜 C) (hCne : C.Nonempty) :
    (ri[𝕜](C)).Nonempty := by
  haveI := hCne.coe_sort
  obtain ⟨p, hp⟩ := hCne
  let p' : _root_.affineSpan 𝕜 C := ⟨p, subset_affineSpan 𝕜 C hp⟩
  let s : Set (_root_.affineSpan 𝕜 C) := ((↑) : _root_.affineSpan 𝕜 C → E) ⁻¹' C
  let t : Set (_root_.affineSpan 𝕜 C).direction :=
    (AffineIsometryEquiv.constVSub 𝕜 p').symm ⁻¹' s
  have ht : Convex 𝕜 t := by
    simpa [s, t] using hC.affine_preimage
      ((_root_.affineSpan 𝕜 C).subtype.comp
        (AffineIsometryEquiv.constVSub 𝕜 p').symm.toAffineEquiv.toAffineMap)
  rw [intrinsicInterior, Set.image_nonempty]
  have hs_top : affineSpan 𝕜 s = ⊤ := by
    change affineSpan 𝕜 (Subtype.val ⁻¹' C) = ⊤
    exact affineSpan_coe_preimage_eq_top C
  have ht_top : affineSpan 𝕜 t = ⊤ := by
    change affineSpan 𝕜 (((AffineIsometryEquiv.constVSub 𝕜 p').symm.toAffineEquiv) ⁻¹' s) = ⊤
    rw [← AffineSubspace.comap_span (AffineIsometryEquiv.constVSub 𝕜 p').symm.toAffineEquiv s,
      hs_top, AffineSubspace.comap_top]
  have ht_nonempty : (interior t).Nonempty :=
    (convex_interior_nonempty_iff_affineSpan_eq_top ht).2 ht_top
  exact (homeomorph_interior_nonempty_iff
    (AffineIsometryEquiv.constVSub 𝕜 p').symm.toHomeomorph s).2 ht_nonempty

/-- Theorem 6.4, reverse direction: if every segment in a nonempty convex set `C` can be
prolonged past `z` while staying in `C`, then `z ∈ ri[𝕜](C)`. -/
-- Proof sketch: first produce some point `x ∈ ri[𝕜](C)` by passing to the affine
-- span of `C` and using the general affine-basis interior-nonempty bridge above. The assumed
-- prolongation gives `lineMap x z μ ∈ C` for some `μ > 1`, so
-- `z = lineMap x (lineMap x z μ) μ⁻¹` with `0 < μ⁻¹ < 1`. Theorem 6.1 then puts `z` back in
-- `ri[𝕜](C)`.
theorem mem_intrinsicInterior_of_forall_exists_gt_one_lineMap_mem
    {C : Set E} (hC : Convex 𝕜 C) (hCne : C.Nonempty) {z : E}
    (hz : ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C) :
    z ∈ ri[𝕜](C) := by
  rcases hC.intrinsicInterior_nonempty hCne with ⟨x, hxri⟩
  rcases hz x (intrinsicInterior_subset hxri) with ⟨μ, hμ, hy⟩
  have hμInv : μ⁻¹ ∈ Set.Ioo (0 : 𝕜) 1 := by
    constructor
    · exact inv_pos.mpr (lt_trans zero_lt_one hμ)
    · rw [inv_lt_one₀]
      · linarith
      · linarith
  have hzseg : z ∈ openSegment 𝕜 x (lineMap x z μ) := by
    have hμ0 : μ ≠ 0 := (lt_trans zero_lt_one hμ).ne'
    simpa [hμ0] using
      (lineMap_mem_openSegment 𝕜 x (lineMap x z μ) hμInv :
        lineMap x (lineMap x z μ) μ⁻¹ ∈ openSegment 𝕜 x (lineMap x z μ))
  exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hxri
    (subset_intrinsicClosure hy) hzseg

/-- Theorem 6.4: a point `z` lies in `ri[𝕜](C)` iff `C` is nonempty and every segment in `C`
with endpoint `z` can be prolonged past `z` while staying in `C`. -/
theorem mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem
    {C : Set E} (hC : Convex 𝕜 C) {z : E} :
    z ∈ ri[𝕜](C) ↔
      C.Nonempty ∧ ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C := by
  constructor
  · intro hzri
    refine ⟨⟨z, intrinsicInterior_subset hzri⟩, ?_⟩
    exact Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hzri
  · rintro ⟨hCne, hz⟩
    exact hC.mem_intrinsicInterior_of_forall_exists_gt_one_lineMap_mem hCne hz

end Reverse

end Convex

end
