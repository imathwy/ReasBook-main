import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_38.Definition_6_38_extra_2
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.Jacobian

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Manifold
open Set
open scoped ContDiff Manifold

universe uα uE uH uM

-- Semantic Lean search tool `lean_leansearch` was unavailable in this environment; the statement
-- below was matched against the local `has_measure_zero_in_manifold` owner from Section 6.38,
-- mathlib's canonical chart-change owner `ModelWithCorners.extendCoordChange`, and the standard
-- null-image theorem `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`.

section

variable {α : Type uα}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [(volume : Measure E).IsAddHaarMeasure] [BorelSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- Lemma 6.6: if a subset `A` of a smooth finite-dimensional real manifold is covered by domains
of smooth charts whose extended chart images of `A` have measure zero in the model space, then `A`
has measure zero in the manifold. -/
theorem has_measure_zero_in_manifold_of_chart_cover
    {A : Set M} (e : α → OpenPartialHomeomorph M H)
    (he : ∀ a : α, e a ∈ IsManifold.maximalAtlas I ∞ M)
    (hcover : A ⊆ ⋃ a : α, (e a).source)
    (hzero : ∀ a : α, volume (((e a).extend I) '' (A ∩ (e a).source)) = 0) :
    has_measure_zero_in_manifold I A := by
  classical
  intro μ hμ k hk
  let _ : μ.IsAddHaarMeasure := hμ
  have hzeroμ : ∀ a : α, μ (((e a).extend I) '' (A ∩ (e a).source)) = 0 := by
    intro a
    rw [Measure.isAddLeftInvariant_eq_smul μ volume, Measure.smul_apply, hzero a]
    simp
  let s : Set (range I) := fun z ↦ (z : E) ∈ (k.extend I) '' (A ∩ k.source)
  have hs : IsLindelof s := HereditarilyLindelofSpace.isLindelof s
  have hs_ex : ∀ z : s, ∃ x ∈ A ∩ k.source, k.extend I x = z.1 := by
    intro z
    have hz : ((z : range I) : E) ∈ (k.extend I) '' (A ∩ k.source) := z.2
    simpa using hz
  choose x hxA hxk using hs_ex
  have hxcover : ∀ z : s, ∃ a : α, x z ∈ (e a).source := by
    intro z
    simpa using hcover (hxA z).1
  choose a hxa using hxcover
  let U : ∀ z : range I, z ∈ s → Set (range I) := fun z hz ↦
    Subtype.val ⁻¹' (I.extendCoordChange k (e (a ⟨z, hz⟩))).source
  have hU : ∀ z (hz : z ∈ s), U z hz ∈ nhds z := by
    intro z hz
    let z' : s := ⟨z, hz⟩
    exact preimage_coe_mem_nhds_subtype.2 <|
      hxk z' ▸ I.extendCoordChange_source_mem_nhdsWithin' (hxA z').2 (hxa z')
  obtain ⟨t, ht_count, hs_subcover⟩ := hs.elim_nhds_subcover' U hU
  let r : Set α := a '' t
  have hr_count : r.Countable := ht_count.image a
  let piece : α → Set E := fun a ↦
    (k.extend I) '' (A ∩ k.source ∩ (e a).source)
  have hsource_subset_piece : ∀ a : α,
      ((k.extend I) '' (A ∩ k.source)) ∩ (I.extendCoordChange k (e a)).source ⊆ piece a := by
    intro a y hy
    rcases hy.1 with ⟨x₁, hx₁, rfl⟩
    rw [← OpenPartialHomeomorph.extend_image_source_inter] at hy
    rcases hy.2 with ⟨x₂, hx₂, hx₂eq⟩
    have hx₁k : x₁ ∈ (k.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hx₁.2
    have hx₂k : x₂ ∈ (k.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hx₂.1
    have hx₁eq : x₁ = x₂ := by
      calc
        x₁ = (k.extend I).symm ((k.extend I) x₁) := by
          symm
          exact (k.extend I).left_inv hx₁k
        _ = (k.extend I).symm ((k.extend I) x₂) := by rw [hx₂eq]
        _ = x₂ := by
          exact (k.extend I).left_inv hx₂k
    exact ⟨x₁, ⟨hx₁, hx₁eq ▸ hx₂.2⟩, rfl⟩
  have hpiece_zero : ∀ a : α, μ (piece a) = 0 := by
    intro a
    let piece' : Set E := ((e a).extend I) '' (A ∩ k.source ∩ (e a).source)
    have hpiece'_zero : μ piece' = 0 := by
      apply measure_mono_null ?_ (hzeroμ a)
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx.1.1, hx.2⟩, rfl⟩
    have hpiece'_subset :
        piece' ⊆ (I.extendCoordChange (e a) k).source := by
      intro y hy
      rw [← OpenPartialHomeomorph.extend_image_source_inter]
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx.2, hx.1.2⟩, rfl⟩
    have hdiff :
        DifferentiableOn ℝ (I.extendCoordChange (e a) k) piece' :=
      ((I.contDiffOn_extendCoordChange (he a) hk).differentiableOn (by simp)).mono hpiece'_subset
    have himage_zero :
        μ ((I.extendCoordChange (e a) k) '' piece') = 0 :=
      MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hdiff
        hpiece'_zero
    suffices (I.extendCoordChange (e a) k) '' piece' = piece a by
      rw [← this]
      exact himage_zero
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨x, hx, rfl⟩
      refine ⟨x, ⟨hx.1, hx.2⟩, ?_⟩
      simp [ModelWithCorners.extendCoordChange, (e a).left_inv hx.2]
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      refine ⟨(e a).extend I x, ?_, ?_⟩
      · exact ⟨x, ⟨hx.1, hx.2⟩, rfl⟩
      · simp [ModelWithCorners.extendCoordChange, (e a).left_inv hx.2]
  have hsubset :
      (k.extend I) '' (A ∩ k.source) ⊆ ⋃ a ∈ r, piece a := by
    intro y hy
    have hy_range : y ∈ range I := by
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨k x, by simp⟩
    have hy_subcover :
        (⟨y, hy_range⟩ : range I) ∈ ⋃ z ∈ t, U z z.2 :=
      hs_subcover hy
    rcases mem_iUnion₂.1 hy_subcover with ⟨z, hz, hyz⟩
    have hy_source : y ∈ (I.extendCoordChange k (e (a z))).source := hyz
    exact mem_iUnion₂.2 ⟨a z, mem_image_of_mem a hz, hsource_subset_piece (a z) ⟨hy, hy_source⟩⟩
  exact measure_mono_null hsubset <|
    (measure_biUnion_null_iff hr_count).2 fun a ha ↦ hpiece_zero a

end
