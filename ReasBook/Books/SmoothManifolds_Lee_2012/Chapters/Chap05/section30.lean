import Mathlib
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sets.Opens

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_30_extra_1 (from Chap05/Sec05_30) -/
universe uM uN

variable {M : Type uM} {N : Type uN}

/- The canonical owner for level sets and zero sets is `Set.preimage`. -/
recall Set.preimage (Φ : M → N) (s : Set N) : Set M

variable (Φ : M → N) (c : N)

/- Definition 5.30-extra-1: a level set of a map `Φ : M → N` at a point `c : N` is the singleton
fiber `Φ ⁻¹' {c}`. In the special case `c = 0`, this is the zero set of `Φ`. -/
#check (Φ ⁻¹' {c} : Set M)

variable [Zero N]

#check (Φ ⁻¹' ({0} : Set N) : Set M)

/-! ### Definition_5_30_extra_2 (from Chap05/Sec05_30) -/
open Set
open scoped ContDiff Manifold

universe uE uE' uH uH' uM uN

-- Semantic search note: `lean_leansearch` was unavailable in this environment; local project
-- precedent was checked against the nearby regular-value and submersion files.

namespace Manifold

section RegularPoints

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}

/-- Definition 5.30-extra-2 (1): a point `p` is a regular point of `Φ : M → N` when the manifold
derivative `mfderiv I J Φ p` is surjective. -/
def IsRegularPoint (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (p : M) : Prop :=
  Function.Surjective (mfderiv I J Φ p)

/-- `IsRegularPoint` means surjectivity of the manifold derivative at the given point. -/
theorem isRegularPoint_iff_surjective_mfderiv (Φ : M → N) (p : M) :
    IsRegularPoint I J Φ p ↔ Function.Surjective (mfderiv I J Φ p) := sorry

/-- Definition 5.30-extra-2 (2): a point `p` is a critical point of `Φ : M → N` when `p` is not a
regular point of `Φ`. -/
def IsCriticalPoint (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (p : M) : Prop :=
  ¬ IsRegularPoint I J Φ p

/-- A point is critical exactly when it is not regular. -/
theorem isCriticalPoint_iff_not_isRegularPoint (Φ : M → N) (p : M) :
    IsCriticalPoint I J Φ p ↔ ¬ IsRegularPoint I J Φ p := sorry

/-- Definition 5.30-extra-2 (3): a value `c` is regular exactly when every point of the level set
`Φ⁻¹({c})` is a regular point of `Φ`. This uses the canonical local definition
`Manifold.IsRegularValue`. -/
theorem isRegularValue_iff_forall_isRegularPoint (Φ : M → N) (c : N) :
    IsRegularValue I J Φ c ↔ ∀ p : M, Φ p = c → IsRegularPoint I J Φ p := sorry

/-- A value with empty fiber is a regular value. -/
theorem isRegularValue_of_preimage_eq_empty {Φ : M → N} {c : N}
    (h : Φ ⁻¹' ({c} : Set N) = ∅) :
    IsRegularValue I J Φ c := sorry

/-- Definition 5.30-extra-2 (4): a value `c` is a critical value of `Φ : M → N` when `c` is not a
regular value of `Φ`. -/
def IsCriticalValue (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (c : N) : Prop :=
  ¬ IsRegularValue I J Φ c

/-- A value is critical exactly when some point of its level set is a critical point. -/
theorem isCriticalValue_iff_exists_critical_point (Φ : M → N) (c : N) :
    IsCriticalValue I J Φ c ↔ ∃ p : M, Φ p = c ∧ IsCriticalPoint I J Φ p := sorry

/-- Definition 5.30-extra-2 (5): the level set `Φ⁻¹({c})` is a regular level set when `c` is a
regular value of `Φ`. -/
def IsRegularLevelSet (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (c : N) : Prop :=
  IsRegularValue I J Φ c

/-- A level set is regular exactly when every point of that level set is a regular point. -/
theorem isRegularLevelSet_iff_forall_mem_preimage_isRegularPoint (Φ : M → N) (c : N) :
    IsRegularLevelSet I J Φ c ↔
      ∀ p : M, p ∈ Φ ⁻¹' ({c} : Set N) → IsRegularPoint I J Φ p := sorry

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- If the source manifold dimension is smaller than the target manifold dimension, then every
point is critical. -/
theorem isCriticalPoint_of_model_finrank_lt {Φ : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') (p : M) :
    IsCriticalPoint I J Φ p := sorry

/-- A smooth map is a smooth submersion exactly when every point of the source is a regular
point. -/
theorem isSmoothSubmersion_iff_forall_isRegularPoint {Φ : M → N} (hΦ : ContMDiff I J ∞ Φ) :
    IsSmoothSubmersion I J Φ ↔ ∀ p : M, IsRegularPoint I J Φ p := sorry

/-- The regular points of a smooth map form an open subset of the source manifold. -/
theorem isOpen_setOf_isRegularPoint {Φ : M → N} (hΦ : ContMDiff I J ∞ Φ) :
    IsOpen {p : M | IsRegularPoint I J Φ p} := sorry

end FiniteDimensional

end RegularPoints

end Manifold

/-! ### Definition_5_30_extra_3 (from Chap05/Sec05_30) -/
open scoped ContDiff Manifold

section DefiningMaps

universe uE uE' uH uH' uM uN

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

namespace Set

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was matched against local project precedent for regular-value and local-open-subset APIs.
/-- Definition 5.30-extra-3 (1): a smooth map `Φ : M → N` is a defining map for `S ⊆ M` if `S` is
the level set of some value `c : N` and the manifold derivative of `Φ` is surjective at every
point of `S`. -/
class IsDefiningMap (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (S : Set M) (Φ : M → N) where
  level : N
  contMDiff : ContMDiff I J ∞ Φ
  isLevelSet : S = Φ ⁻¹' {level}
  surj_mfderiv : ∀ x : M, x ∈ S → Function.Surjective (mfderiv I J Φ x)

/-- A defining map canonically provides the smoothness hypothesis as a `Fact`. -/
instance instFactContMDiffIsDefiningMap (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ E' H') (S : Set M) (Φ : M → N) (h : IsDefiningMap I J S Φ) :
    Fact (ContMDiff I J ∞ Φ) where
  out := h.contMDiff

/-- A defining function is a defining map whose codomain is a finite-dimensional real vector
space `ℝ^k`, represented in Lean as `Fin k → ℝ`. -/
abbrev IsDefiningFunction (I : ModelWithCorners ℝ E H) (S : Set M) {k : ℕ}
    (f : M → Fin k → ℝ) :=
  IsDefiningMap I 𝓘(ℝ, Fin k → ℝ) S f

/-- Definition 5.30-extra-3 (2): a smooth map `Φ : U → N` on an open subset `U ⊆ M` is a local
defining map for `S ⊆ M` if the points of `S` lying in `U` are exactly one level set of `Φ` and
the manifold derivative of `Φ` is surjective at each such point. -/
class IsLocalDefiningMapOn (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (S : Set M) (U : TopologicalSpace.Opens M) (Φ : U → N) where
  level : N
  contMDiff : ContMDiff I J ∞ Φ
  isLevelSet : {x : U | (x : M) ∈ S} = Φ ⁻¹' {level}
  surj_mfderiv : ∀ x : U, (x : M) ∈ S → Function.Surjective (mfderiv I J Φ x)

/-- A local defining map canonically provides the smoothness hypothesis as a `Fact`. -/
instance instFactContMDiffIsLocalDefiningMapOn (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ E' H') (S : Set M) (U : TopologicalSpace.Opens M) (Φ : U → N)
    (h : IsLocalDefiningMapOn I J S U Φ) :
    Fact (ContMDiff I J ∞ Φ) where
  out := h.contMDiff

/-- A local defining function is a local defining map whose codomain is `ℝ^k`, represented as
`Fin k → ℝ`. -/
abbrev IsLocalDefiningFunctionOn (I : ModelWithCorners ℝ E H) (S : Set M)
    (U : TopologicalSpace.Opens M) {k : ℕ} (f : U → Fin k → ℝ) :=
  IsLocalDefiningMapOn I 𝓘(ℝ, Fin k → ℝ) S U f

/-- Existence of a `Set.IsDefiningMap` structure is equivalent to specifying the chosen level
value, smoothness, level-set equation, and surjective derivative condition. -/
theorem isDefiningMap_iff (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (S : Set M) (Φ : M → N) :
    Nonempty (IsDefiningMap I J S Φ) ↔
      ∃ c : N,
        ContMDiff I J ∞ Φ ∧
          S = Φ ⁻¹' {c} ∧
          ∀ x : M, x ∈ S → Function.Surjective (mfderiv I J Φ x) := sorry

/-- Existence of a `Set.IsDefiningFunction` structure is equivalent to the corresponding explicit
`ℝ^k`-valued defining-map conditions. -/
theorem isDefiningFunction_iff (I : ModelWithCorners ℝ E H) (S : Set M) {k : ℕ}
    (f : M → Fin k → ℝ) :
    Nonempty (IsDefiningFunction I S f) ↔
      ∃ c : Fin k → ℝ,
        ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ f ∧
          S = f ⁻¹' {c} ∧
          ∀ x : M, x ∈ S → Function.Surjective (mfderiv I 𝓘(ℝ, Fin k → ℝ) f x) := sorry

/-- Existence of a `Set.IsLocalDefiningMapOn` structure is equivalent to specifying the chosen
level value on the open subset, the smoothness of `Φ`, the level-set equation, and surjectivity of
the derivative along `S ∩ U`. -/
theorem isLocalDefiningMapOn_iff (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ E' H') (S : Set M) (U : TopologicalSpace.Opens M) (Φ : U → N) :
    Nonempty (IsLocalDefiningMapOn I J S U Φ) ↔
      ∃ c : N,
        ContMDiff I J ∞ Φ ∧
          {x : U | (x : M) ∈ S} = Φ ⁻¹' {c} ∧
          ∀ x : U, (x : M) ∈ S → Function.Surjective (mfderiv I J Φ x) := sorry

/-- Existence of a `Set.IsLocalDefiningFunctionOn` structure is equivalent to the corresponding
explicit `ℝ^k`-valued local defining-map conditions. -/
theorem isLocalDefiningFunctionOn_iff (I : ModelWithCorners ℝ E H) (S : Set M)
    (U : TopologicalSpace.Opens M) {k : ℕ} (f : U → Fin k → ℝ) :
    Nonempty (IsLocalDefiningFunctionOn I S U f) ↔
      ∃ c : Fin k → ℝ,
        ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ f ∧
          {x : U | (x : M) ∈ S} = f ⁻¹' {c} ∧
          ∀ x : U, (x : M) ∈ S → Function.Surjective (mfderiv I 𝓘(ℝ, Fin k → ℝ) f x) := sorry

end Set

end DefiningMaps

/-! ### Corollary_5_30 (from Chap05/Sec05_32) -/
open scoped Manifold Topology

section RestrictingMapsToEmbeddedSubmanifolds

universe u𝕜 uE uH uM uE' uH' uE'' uH'' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H'' N]
variable {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ⊤ N]

namespace Manifold.IsSmoothEmbedding

/-- Helper for Corollary 5.30: the codomain-restricted map is continuous because the embedded
submanifold carries the induced subspace topology. -/
lemma continuous_codRestrict
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    Continuous (Set.codRestrict F S hFS) := by
  -- The embedding part of `hS` identifies continuity into `S` with continuity after composing
  -- with the inclusion `Subtype.val : S → M`.
  refine hS.isEmbedding.isInducing.continuous_iff.2 ?_
  simpa [Function.comp] using hF.continuous

/-- Helper for Corollary 5.30: in immersion charts for the inclusion `S ↪ M`, the restricted map
to `S` is recovered from the ambient chart expression by the projected inverse equivalence. -/
lemma writtenInCharts_codRestrict_eqOn
    {F : N → M} (hFS : ∀ x, F x ∈ S) {y : S}
    (hImm : IsImmersionAt J I ⊤ (Subtype.val : S → M) y) :
    Set.EqOn ((hImm.domChart.extend J) ∘ Set.codRestrict F S hFS)
      ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
      ((Set.codRestrict F S hFS) ⁻¹' hImm.domChart.source) := by
  -- Apply the immersion normal form to the point `Set.codRestrict F S hFS z` and solve for its
  -- domain-chart coordinates by postcomposing with `Prod.fst ∘ hImm.equiv.symm`.
  intro z hz
  have hz_target :
      hImm.domChart.extend J (Set.codRestrict F S hFS z) ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hz
  simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz] using
    (congrArg (fun v => Prod.fst (hImm.equiv.symm v)) (hImm.writtenInCharts hz_target)).symm

/-- Helper for Corollary 5.30: each pointwise codomain restriction is smooth in the embedded
manifold structure. -/
lemma contMDiffAt_toSubtype
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) (x : N) :
    ContMDiffAt K J ⊤ (Set.codRestrict F S hFS) x := by
  let fS : N → S := Set.codRestrict F S hFS
  let y : S := fS x
  let hImm : IsImmersionAt J I ⊤ (Subtype.val : S → M) y := hS.isImmersion.isImmersionAt y
  let e : OpenPartialHomeomorph N H'' := chartAt H'' x
  let x' : E'' := e.extend K x
  have hcont : ContinuousAt fS x := (continuous_codRestrict hS hF hFS).continuousAt
  have hx : x ∈ e.source := mem_chart_source H'' x
  have hy : fS x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hy' : F x ∈ hImm.codChart.source := hImm.mem_codChart_source
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ) (e := e)
    (e' := hImm.domChart) (IsManifold.chart_mem_maximalAtlas x) hImm.domChart_mem_maximalAtlas
    hx hy,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨hcont, ?_⟩
  have hambient :
      ContDiffWithinAt 𝕜 ⊤ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) (Set.range K) x' := by
    -- Rewrite the ambient smoothness in the chart pair `(e, hImm.codChart)`.
    simpa [Set.preimage_univ] using
      ((contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ) (e := e)
        (e' := hImm.codChart) (IsManifold.chart_mem_maximalAtlas x)
        hImm.codChart_mem_maximalAtlas hx hy').1 (hF.contMDiffAt.contMDiffWithinAt)).2
  have hproj :
      ContDiff 𝕜 ⊤ (fun v ↦ (hImm.equiv.symm v).1) := by
    simpa using contDiff_fst.comp hImm.equiv.symm.contDiff
  have hprojWithin :
      ContDiffWithinAt 𝕜 ⊤ (fun v ↦ (hImm.equiv.symm v).1) Set.univ
        (((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) x') :=
    hproj.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt 𝕜 ⊤
        ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm))
        (Set.range K) x' := by
    -- Postcompose the ambient chart expression with the smooth linear projection onto the
    -- `S`-coordinates in the immersion normal form.
    exact hprojWithin.comp x' hambient (by intro z hz; simp)
  have hsource_mem : fS ⁻¹' hImm.domChart.source ∈ 𝓝 x := by
    -- The chosen immersion chart is open around `y = fS x`, so continuity of `fS` pulls it back
    -- to a neighborhood of `x`.
    have : hImm.domChart.source ∈ 𝓝 (fS x) :=
      hImm.domChart.open_source.mem_nhds hy
    exact hcont.preimage_mem_nhds this
  have hset_mem :
      (e.extend K).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈ 𝓝[Set.range K] x' := by
    -- Transport that neighborhood through the source chart on `N`.
    simpa [e, x', nhdsWithin_univ] using
      e.extend_preimage_mem_nhdsWithin (I := K) (s := Set.univ) (t := fS ⁻¹' hImm.domChart.source)
        hx (by simpa [nhdsWithin_univ] using hsource_mem)
  have heq :
      ((hImm.domChart.extend J) ∘ fS ∘ (e.extend K).symm)
        =ᶠ[𝓝[Set.range K] x']
          ((fun v ↦ (hImm.equiv.symm v).1) ∘
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm)) := by
    -- On the neighborhood where `fS` lands in the immersion domain chart, the two chart
    -- expressions agree by the previous `EqOn` lemma.
    refine Filter.eventuallyEq_of_mem hset_mem ?_
    intro z hz
    have hchartEq := writtenInCharts_codRestrict_eqOn (F := F) (hFS := hFS) (hImm := hImm)
    simpa [Function.comp] using hchartEq hz
  have hx'_target : x' ∈ (e.extend K).target := (e.extend K).map_source <| by
    simpa [OpenPartialHomeomorph.extend_source] using hx
  have hx'_range : x' ∈ Set.range K :=
    e.extend_target_subset_range hx'_target
  exact hcomp.congr_of_eventuallyEq_of_mem heq hx'_range

/-- If `Subtype.val : S → M` is a smooth embedding and a smooth map `F : N → M` has image in `S`,
then `F` is smooth as a map to `S`. This owner-based restriction-to-subtype bridge is the
canonical input for Corollary 5.30 and its boundary-ambient variant. -/
theorem contMDiff_toSubtype
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  -- Smoothness is verified pointwise using the immersion normal form of the embedding.
  intro x
  exact contMDiffAt_toSubtype hS hF hFS x

end Manifold.IsSmoothEmbedding

/-- Corollary 5.30 (Embedded Case): every smooth map `F : N → M` whose image is contained in an
embedded submanifold `S ⊆ M` is smooth as a map from `N` to `S`. -/
theorem contMDiff_toSubtype_of_isEmbeddedSubmanifold {F : N → M}
    [IsEmbeddedSubmanifold I J S]
    (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  simpa using
    IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val.contMDiff_toSubtype hF hFS

end RestrictingMapsToEmbeddedSubmanifolds
