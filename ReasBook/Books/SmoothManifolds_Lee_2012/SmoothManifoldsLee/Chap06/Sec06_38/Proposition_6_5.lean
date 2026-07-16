import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Definition_2_11_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open TopologicalSpace
open scoped ContDiff Manifold

-- Domain sampling pass: the source-facing owner is `Function.IsSmoothOn`, while the canonical
-- ambient null-image theorem is
-- `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`.
-- Proposition 6.5 is the bridge from local smooth extensions on the subtype `A` to that
-- differentiable-on theorem on ambient Euclidean space.

/-- Proposition 6.5: if `A ⊆ ℝ^n` has measure zero and `F : A → ℝ^n` is smooth in the local
extension sense, then the image `F(A)` has measure zero. Since the domain of `F` is the subtype
`A`, its image is represented by `Set.range F`. -/
theorem volume_range_eq_zero_of_isSmoothOn_of_volume_eq_zero
    {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : volume A = 0)
    (F : A → EuclideanSpace ℝ (Fin n))
    (hF : F.IsSmoothOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) :
    volume (Set.range F) = 0 := by
  classical
  rw [Function.isSmoothOn_iff_exists_local_extension] at hF
  choose U hU using hF
  have hU_open (p : A) : IsOpen (U p) := (hU p).1
  have hpU (p : A) : (p : EuclideanSpace ℝ (Fin n)) ∈ U p := (hU p).2.1
  choose Fext hFext using fun p ↦ (hU p).2.2
  have hFext_smooth (p : A) :
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (∞ : ℕ∞ω) (Fext p) (U p) := (hFext p).1
  have hFext_eq (p : A) :
      ∀ q : A, (q : EuclideanSpace ℝ (Fin n)) ∈ U p → Fext p q = F q := (hFext p).2
  let V : A → Set A := fun p ↦ (↑) ⁻¹' U p
  have hV_nhds : ∀ p : A, V p ∈ nhds p := fun p ↦
    preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds ((hU_open p).mem_nhds (hpU p))
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  have hpiece_zero : ∀ p ∈ t, volume (F '' V p) = 0 := by
    intro p hp
    have hdiff_on_U : DifferentiableOn ℝ (Fext p) (U p) :=
      (hFext_smooth p).contDiffOn.differentiableOn (by simp)
    have hdiff_on_piece : DifferentiableOn ℝ (Fext p) (A ∩ U p) :=
      hdiff_on_U.mono fun _ hx ↦ hx.2
    have hA_piece : volume (A ∩ U p) = 0 :=
      measure_mono_null Set.inter_subset_left hA
    have himage_piece : volume (Fext p '' (A ∩ U p)) = 0 :=
      by
        simpa using
          addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
            volume hdiff_on_piece hA_piece
    refine measure_mono_null ?_ himage_piece
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    exact ⟨(q : EuclideanSpace ℝ (Fin n)), ⟨q.2, hq⟩, hFext_eq p q hq⟩
  have hrange_subset : Set.range F ⊆ ⋃ p ∈ t, F '' V p := by
    intro y hy
    rcases hy with ⟨q, rfl⟩
    have hq_cover : q ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hq_cover with ⟨p, hp, hq⟩
    exact Set.mem_iUnion₂.2 ⟨p, hp, ⟨q, hq, rfl⟩⟩
  exact measure_mono_null hrange_subset <|
    (measure_biUnion_null_iff ht_countable).2 hpiece_zero
