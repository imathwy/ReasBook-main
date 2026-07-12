import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Measure.Prod
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_3
import SmoothManifolds_Lee_2012.Chap04.Sec04_27.Problem_4_1
import SmoothManifolds_Lee_2012.Chap06.Sec06_38.Lemma_6_2

open MeasureTheory
open EuclideanSpace

-- Domain sampling pass: Proposition 6.3 lies in the Euclidean graph / measure-zero domain.
-- The source-facing owner is the canonical graph parametrization `graphMap`, realized in the
-- ambient product as `Set.range (fun x ↦ (x, f x))`. The measure-theoretic core abstraction is
-- the product graph in `ℝ^n × ℝ`, where every vertical slice is either empty or a singleton. The
-- ambient realization in `ℝ^(n + 1)` is only a bridge/view, provided by the canonical measurable
-- equivalence `lastCoordinateMeasurableEquiv : ℝ^n × ℝ ≃ ℝ^(n + 1)`.
-- Primitive data are the subset `A`, the continuous map `f : A → ℝ`, and, in the half-space
-- variant, the canonical inclusion into the ambient Euclidean space.

namespace EuclideanSpace

/-- The canonical measurable identification `ℝ^n × ℝ ≃ ℝ^(n + 1)` obtained by adjoining the last
coordinate. This is the bridge/view that realizes graphs in `ℝ^(n + 1)`. -/
noncomputable def lastCoordinateMeasurableEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) × ℝ ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
  MeasurableEquiv.prodComm.trans (firstCoordinateMeasurableEquiv n).symm

/-- The last-coordinate identification preserves Lebesgue measure. -/
theorem lastCoordinateMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (lastCoordinateMeasurableEquiv n) := by
  exact
    (firstCoordinateMeasurableEquiv_measurePreserving n).symm.comp
      (Measure.measurePreserving_swap :
        MeasurePreserving
          (Prod.swap : EuclideanSpace ℝ (Fin n) × ℝ → ℝ × EuclideanSpace ℝ (Fin n))
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
          ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))))

end EuclideanSpace

section

theorem measurableSet_range_graph_of_measurableEmbedding
    {α X : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [MeasurableSpace X]
    (i : α → X) (hi : MeasurableEmbedding i) (f : α → ℝ) (hf : Continuous f) :
    MeasurableSet (Set.range fun a : α ↦ (i a, f a) : Set (X × ℝ)) := by
  let g : α → X × ℝ := fun a ↦ (i a, f a)
  have hgraph_meas : MeasurableSet (Set.range (graphMap (Set.univ : Set α) f)) := by
    have hgraph_eq :
        Set.range (graphMap (Set.univ : Set α) f) = {p : α × ℝ | f p.1 = p.2} := by
      rw [range_graphMap_eq_graphOn]
      ext p
      simp [Set.mem_graphOn]
    rw [hgraph_eq]
    exact (isClosed_eq (hf.comp continuous_fst) continuous_snd).measurableSet
  have hi_prod : MeasurableEmbedding (Prod.map i (id : ℝ → ℝ)) :=
    hi.prodMap MeasurableEmbedding.id
  have hgraph_range :
      Set.range g =
        ((Prod.map i (id : ℝ → ℝ)) '' Set.range (graphMap (Set.univ : Set α) f) :
          Set (X × ℝ)) := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨graphMap (Set.univ : Set α) f ⟨a, by simp⟩, ?_, rfl⟩
      exact ⟨⟨a, by simp⟩, rfl⟩
    · rintro ⟨q, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  simpa [g, hgraph_range] using hi_prod.measurableSet_image.2 hgraph_meas

theorem volume_range_graph_eq_zero_of_measurableEmbedding
    {α X : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [MeasureSpace X]
    (i : α → X) (hi : MeasurableEmbedding i) (f : α → ℝ) (hf : Continuous f) :
    volume (Set.range fun a : α ↦ (i a, f a) : Set (X × ℝ)) = 0 := by
  let g : α → X × ℝ := fun a ↦ (i a, f a)
  have hmeas : MeasurableSet (Set.range g) := by
    simpa [g] using measurableSet_range_graph_of_measurableEmbedding i hi f hf
  have hslice :
      ∀ x : X, volume (Prod.mk x ⁻¹' Set.range g) = 0 := by
    intro x
    by_cases hx : x ∈ Set.range i
    · rcases hx with ⟨a, rfl⟩
      have hs : Prod.mk (i a) ⁻¹' Set.range g = {f a} := by
        ext t
        constructor
        · intro ht
          rcases ht with ⟨b, hb⟩
          have hab : a = b := hi.injective <| by simpa [g] using (congrArg Prod.fst hb).symm
          exact Set.mem_singleton_iff.2 <| by simpa [g, hab] using (congrArg Prod.snd hb).symm
        · intro ht
          rcases Set.mem_singleton_iff.1 ht with rfl
          exact ⟨a, by simp [g]⟩
      rw [hs]
      simp
    · have hs : Prod.mk x ⁻¹' Set.range g = ∅ := by
        ext t
        constructor
        · intro ht
          rcases ht with ⟨a, ha⟩
          exact (hx ⟨a, by simpa using congrArg Prod.fst ha⟩).elim
        · simp
      rw [hs]
      simp
  have hzero : volume (Set.range g) = 0 := by
    rw [Measure.volume_eq_prod X ℝ]
    exact Measure.measure_prod_null_of_ae_null hmeas <| Filter.Eventually.of_forall hslice
  simpa [g] using hzero

end

private theorem volume_image_lastCoordinateMeasurableEquiv_eq_zero
    {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n) × ℝ)} (hzero : volume s = 0) :
    volume (lastCoordinateMeasurableEquiv n '' s) = 0 := by
  let e : EuclideanSpace ℝ (Fin n) × ℝ ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
    lastCoordinateMeasurableEquiv n
  have he : MeasurePreserving e := lastCoordinateMeasurableEquiv_measurePreserving n
  calc
    volume (e '' s) = (Measure.map e volume) (e '' s) := by rw [he.map_eq]
    _ = volume (e ⁻¹' (e '' s)) := e.map_apply (e '' s)
    _ = volume s := by simp
    _ = 0 := hzero

/-- Proposition 6.3 (1): if `A ⊆ ℝ^n` is measurable and `f : A → ℝ` is continuous, then the
graph of `f`, viewed in `ℝ^(n+1)` through the canonical product identification, has measure zero. -/
theorem volume_graph_eq_zero_of_measurableSet_of_continuous
    {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A) (f : A → ℝ) (hf : Continuous f) :
    volume
        (lastCoordinateMeasurableEquiv n ''
          Set.range fun x : A ↦ ((x : EuclideanSpace ℝ (Fin n)), f x)) = 0 := by
  have hgraph_zero :
      volume
        (Set.range fun x : A ↦ ((x : EuclideanSpace ℝ (Fin n)), f x) :
          Set (EuclideanSpace ℝ (Fin n) × ℝ)) = 0 := by
    simpa using
      volume_range_graph_eq_zero_of_measurableEmbedding
        ((↑) : A → EuclideanSpace ℝ (Fin n)) (MeasurableEmbedding.subtype_coe hA) f hf
  exact volume_image_lastCoordinateMeasurableEquiv_eq_zero hgraph_zero

/-- Proposition 6.3 (2): if `A ⊆ ℍ^n` is measurable and `f : A → ℝ` is continuous, then the
graph of `f`, viewed in `ℝ^(n+1)` through the canonical half-space inclusion and product
identification, has measure zero. -/
theorem volume_halfSpace_graph_eq_zero_of_measurableSet_of_continuous
    {n : ℕ} [NeZero n] {A : Set (EuclideanHalfSpace n)}
    (hA : MeasurableSet (EuclideanHalfSpace.inclusion n '' A)) (f : A → ℝ) (hf : Continuous f) :
    volume
        (lastCoordinateMeasurableEquiv n ''
          Set.range fun x : A ↦ (EuclideanHalfSpace.inclusion n x, f x)) = 0 :=
  by
  let _ : MeasurableSpace (EuclideanHalfSpace n) := Subtype.instMeasurableSpace
  let _ : BorelSpace (EuclideanHalfSpace n) :=
    inferInstanceAs (BorelSpace {x : EuclideanSpace ℝ (Fin n) // 0 ≤ x.ofLp 0})
  have hhalf_meas : MeasurableSet ({x : EuclideanSpace ℝ (Fin n) | 0 ≤ x.ofLp 0}) := by
    have hcoord : Continuous fun x : EuclideanSpace ℝ (Fin n) ↦ x.ofLp 0 :=
      PiLp.continuous_apply 2 _ 0
    exact (isClosed_le continuous_const hcoord).measurableSet
  have hhalf_embed :
      MeasurableEmbedding (EuclideanHalfSpace.inclusion n : EuclideanHalfSpace n →
        EuclideanSpace ℝ (Fin n)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      exact Subtype.ext hxy
    · simpa [EuclideanHalfSpace.inclusion] using
        (MeasurableEmbedding.subtype_coe hhalf_meas).measurable
    · intro s hs
      simpa [EuclideanHalfSpace.inclusion] using
        (MeasurableEmbedding.subtype_coe hhalf_meas).measurableSet_image.2 hs
  have hA_subtype : MeasurableSet A := by
    simpa using hhalf_embed.measurableSet_image.mp hA
  have hi :
      MeasurableEmbedding (EuclideanHalfSpace.inclusion n ∘ ((↑) : A → EuclideanHalfSpace n)) :=
    hhalf_embed.comp (MeasurableEmbedding.subtype_coe hA_subtype)
  have hgraph_zero :
      volume
        (Set.range fun x : A ↦ (EuclideanHalfSpace.inclusion n x, f x) :
          Set (EuclideanSpace ℝ (Fin n) × ℝ)) = 0 := by
    simpa using volume_range_graph_eq_zero_of_measurableEmbedding
      (EuclideanHalfSpace.inclusion n ∘ ((↑) : A → EuclideanHalfSpace n)) hi f hf
  exact volume_image_lastCoordinateMeasurableEquiv_eq_zero hgraph_zero
