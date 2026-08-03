module

import Topology_Munkres_2000.Book.Theorem_45_4
import Topology_Munkres_2000.Book.Exercise_47_2.ProperTarget
import Mathlib.Topology.ContinuousMap.Compact

universe u

/- Exercise 47.3. When `X` is compact Hausdorff, the general Ascoli theorem implies both
finite-dimensional cases of Theorem 45.4 through the compact-domain isometry between `C(X, Y)`
and `BoundedContinuousFunction X Y`. -/
#check fun {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ} ↦
  let transfer : ∀ {Y : Type} [MetricSpace Y] [ProperSpace Y]
      (𝓕 : Set (BoundedContinuousFunction X Y)),
      IsCompact (closure 𝓕) ↔
        Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) ∧
          PointwiseBounded (fun f : 𝓕 ↦ (f : X → Y)) := fun {Y} _ _ 𝓕 ↦ by
    have h_compact :
        IsCompact (closure ((ContinuousMap.isometryEquivBoundedOfCompact X Y) ⁻¹' 𝓕)) ↔
          IsCompact (closure 𝓕) := by
      change IsCompact
          (closure ((ContinuousMap.isometryEquivBoundedOfCompact X Y).toHomeomorph ⁻¹' 𝓕)) ↔
        IsCompact (closure 𝓕)
      rw [← (ContinuousMap.isometryEquivBoundedOfCompact X Y).toHomeomorph.preimage_closure]
      exact (ContinuousMap.isometryEquivBoundedOfCompact X Y).toHomeomorph.isCompact_preimage
    have h_equicontinuous :
        Equicontinuous
            (fun f : (ContinuousMap.isometryEquivBoundedOfCompact X Y) ⁻¹' 𝓕 ↦
              (f : X → Y)) ↔
          Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) := by
      constructor
      · intro h
        convert h.comp (fun (⟨f, hf⟩ : 𝓕) ↦
          ⟨(ContinuousMap.isometryEquivBoundedOfCompact X Y).symm f,
            by
              change ContinuousMap.isometryEquivBoundedOfCompact X Y
                ((ContinuousMap.isometryEquivBoundedOfCompact X Y).symm f) ∈ 𝓕
              rw [(ContinuousMap.isometryEquivBoundedOfCompact X Y).apply_symm_apply]
              exact hf⟩) using 1
        ext f x
        simp only [Function.comp_apply, ContinuousMap.isometryEquivBoundedOfCompact_symm_apply,
          BoundedContinuousFunction.coe_toContinuousMap]
      · intro h
        convert h.comp
          (fun (⟨f, hf⟩ : (ContinuousMap.isometryEquivBoundedOfCompact X Y) ⁻¹' 𝓕) ↦
            ⟨ContinuousMap.isometryEquivBoundedOfCompact X Y f, hf⟩) using 1
        ext f x
        simp only [Function.comp_apply, ContinuousMap.isometryEquivBoundedOfCompact_apply,
          BoundedContinuousFunction.mkOfCompact_apply]
    have h_pointwise :
        PointwiseBounded
            (fun f : (ContinuousMap.isometryEquivBoundedOfCompact X Y) ⁻¹' 𝓕 ↦
              (f : X → Y)) ↔
          PointwiseBounded (fun f : 𝓕 ↦ (f : X → Y)) := by
      constructor
      · intro h
        rw [pointwiseBounded_iff] at h ⊢
        intro x
        apply (h x).subset
        rintro y ⟨⟨f, hf⟩, rfl⟩
        refine ⟨⟨(ContinuousMap.isometryEquivBoundedOfCompact X Y).symm f, ?_⟩, ?_⟩
        · change ContinuousMap.isometryEquivBoundedOfCompact X Y
            ((ContinuousMap.isometryEquivBoundedOfCompact X Y).symm f) ∈ 𝓕
          rw [(ContinuousMap.isometryEquivBoundedOfCompact X Y).apply_symm_apply]
          exact hf
        simp
      · intro h
        rw [pointwiseBounded_iff] at h ⊢
        intro x
        apply (h x).subset
        rintro y ⟨⟨f, hf⟩, rfl⟩
        exact ⟨⟨ContinuousMap.isometryEquivBoundedOfCompact X Y f, hf⟩, by simp⟩
    rw [← h_compact, ContinuousMap.isCompact_closure_iff_equicontinuous_and_pointwiseBounded,
      h_equicontinuous, h_pointwise]
  show
    (∀ 𝓕 : Set (BoundedContinuousFunction X (Fin n → ℝ)),
      IsCompact (closure 𝓕) ↔
        Equicontinuous (fun f : 𝓕 ↦ (f : X → Fin n → ℝ)) ∧
          PointwiseBounded (fun f : 𝓕 ↦ (f : X → Fin n → ℝ))) ∧
    (∀ 𝓕 : Set (BoundedContinuousFunction X (EuclideanSpace ℝ (Fin n))),
      IsCompact (closure 𝓕) ↔
        Equicontinuous (fun f : 𝓕 ↦ (f : X → EuclideanSpace ℝ (Fin n))) ∧
          PointwiseBounded (fun f : 𝓕 ↦ (f : X → EuclideanSpace ℝ (Fin n)))) from
    ⟨fun 𝓕 ↦ transfer 𝓕, fun 𝓕 ↦ transfer 𝓕⟩

/- Theorem 45.4 records these two conclusions as the canonical public API. -/
#check isCompact_closure_iff_equicontinuous_and_pointwiseBounded_sup
#check isCompact_closure_iff_equicontinuous_and_pointwiseBounded_euclidean
