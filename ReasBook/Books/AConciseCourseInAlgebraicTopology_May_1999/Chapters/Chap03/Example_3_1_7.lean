import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Constructions.SumProd
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v u₁ v₁ u₂ v₂

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {E₁ : Type u₁} {B₁ : Type v₁} {E₂ : Type u₂} {B₂ : Type v₂}
variable [TopologicalSpace E₁] [TopologicalSpace B₁] [TopologicalSpace E₂] [TopologicalSpace B₂]

private theorem prod_discreteTopology
    {A : Type u₁} {B : Type u₂} [TopologicalSpace A] [TopologicalSpace B]
    (hA : DiscreteTopology A) (hB : DiscreteTopology B) :
    DiscreteTopology (A × B) :=
  @instDiscreteTopologyProd A B _ _ hA hB

namespace IsEvenlyCovered

/-- The product of two evenly covered neighborhoods is evenly covered for the product map. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂} {b₁ : B₁} {b₂ : B₂}
    (hp : IsEvenlyCovered p b₁ (p ⁻¹' ({b₁} : Set B₁)))
    (hq : IsEvenlyCovered q b₂ (q ⁻¹' ({b₂} : Set B₂))) :
    IsEvenlyCovered (Prod.map p q) (b₁, b₂)
      (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
  rcases hp with ⟨hpdisc, U₁, hb₁U₁, hU₁, hpU₁, H₁, hH₁⟩
  rcases hq with ⟨hqdisc, U₂, hb₂U₂, hU₂, hqU₂, H₂, hH₂⟩
  have hpre :
      Prod.map p q ⁻¹' (U₁ ×ˢ U₂) = (p ⁻¹' U₁) ×ˢ (q ⁻¹' U₂) := by
    ext x
    simp [Prod.map]
  have hfiber :
      Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂)) =
        (p ⁻¹' ({b₁} : Set B₁)) ×ˢ (q ⁻¹' ({b₂} : Set B₂)) := by
    ext x
    simp [Prod.map]
  let hFiber :
      ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) ≃ₜ
        (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.Set.prod (p ⁻¹' ({b₁} : Set B₁)) (q ⁻¹' ({b₂} : Set B₂))).symm.trans
      (Homeomorph.setCongr hfiber.symm)
  have hdisc : DiscreteTopology (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
    exact @Homeomorph.discreteTopology _ _ _ _ (prod_discreteTopology hpdisc hqdisc) hFiber
  let H :
      ↑(Prod.map p q ⁻¹' (U₁ ×ˢ U₂)) ≃ₜ
        ↑(U₁ ×ˢ U₂) × (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.setCongr hpre).trans <|
      (Homeomorph.Set.prod (p ⁻¹' U₁) (q ⁻¹' U₂)).trans <|
        (H₁.prodCongr H₂).trans <|
          (Homeomorph.prodProdProdComm U₁ (p ⁻¹' ({b₁} : Set B₁)) U₂
            (q ⁻¹' ({b₂} : Set B₂))).trans <|
            Homeomorph.prodCongr
              (Homeomorph.Set.prod U₁ U₂).symm
              hFiber
  refine ⟨hdisc, U₁ ×ˢ U₂, ⟨hb₁U₁, hb₂U₂⟩, hU₁.prod hU₂, ?_, H, ?_⟩
  · simpa [Prod.map] using hpU₁.prod hqU₂
  · intro x
    have hx₁ : p x.1.1 ∈ U₁ := by
      simpa [Prod.map] using x.2.1
    have hx₂ : q x.1.2 ∈ U₂ := by
      simpa [Prod.map] using x.2.2
    ext
    · simpa [H, Prod.map] using hH₁ ⟨x.1.1, hx₁⟩
    · simpa [H, Prod.map] using hH₂ ⟨x.1.2, hx₂⟩

end IsEvenlyCovered

namespace IsPathConnectedEvenlyCovered

/-- Path-connected evenly covered neighborhoods are stable under products. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂} {b₁ : B₁} {b₂ : B₂}
    (hp : IsPathConnectedEvenlyCovered p b₁)
    (hq : IsPathConnectedEvenlyCovered q b₂) :
    IsPathConnectedEvenlyCovered (Prod.map p q) (b₁, b₂) := by
  rcases hp with ⟨hpdisc, U₁, hb₁U₁, hU₁, hU₁Path, hpU₁, H₁, hH₁⟩
  rcases hq with ⟨hqdisc, U₂, hb₂U₂, hU₂, hU₂Path, hqU₂, H₂, hH₂⟩
  have hUProd : IsPathConnected (U₁ ×ˢ U₂) := by
    rw [isPathConnected_iff]
    refine ⟨hU₁Path.nonempty.prod hU₂Path.nonempty, ?_⟩
    intro x hx y hy
    let hx₁ := (isPathConnected_iff.mp hU₁Path).2 x.1 hx.1 y.1 hy.1
    let hx₂ := (isPathConnected_iff.mp hU₂Path).2 x.2 hx.2 y.2 hy.2
    exact ⟨hx₁.somePath.prod hx₂.somePath, fun t ↦ ⟨hx₁.somePath_mem t, hx₂.somePath_mem t⟩⟩
  have hpre :
      Prod.map p q ⁻¹' (U₁ ×ˢ U₂) = (p ⁻¹' U₁) ×ˢ (q ⁻¹' U₂) := by
    ext x
    simp [Prod.map]
  have hfiber :
      Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂)) =
        (p ⁻¹' ({b₁} : Set B₁)) ×ˢ (q ⁻¹' ({b₂} : Set B₂)) := by
    ext x
    simp [Prod.map]
  let hFiber :
      ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) ≃ₜ
        (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.Set.prod (p ⁻¹' ({b₁} : Set B₁)) (q ⁻¹' ({b₂} : Set B₂))).symm.trans
      (Homeomorph.setCongr hfiber.symm)
  have hdisc : DiscreteTopology (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
    exact @Homeomorph.discreteTopology _ _ _ _ (prod_discreteTopology hpdisc hqdisc) hFiber
  refine ⟨hdisc, U₁ ×ˢ U₂, ⟨hb₁U₁, hb₂U₂⟩, hU₁.prod hU₂, hUProd, ?_, ?_, ?_⟩
  · simpa [Prod.map] using hpU₁.prod hqU₂
  · exact
      (Homeomorph.setCongr hpre).trans <|
        (Homeomorph.Set.prod (p ⁻¹' U₁) (q ⁻¹' U₂)).trans <|
          (H₁.prodCongr H₂).trans <|
            (Homeomorph.prodProdProdComm U₁ (p ⁻¹' ({b₁} : Set B₁)) U₂
              (q ⁻¹' ({b₂} : Set B₂))).trans <|
              Homeomorph.prodCongr
                (Homeomorph.Set.prod U₁ U₂).symm
                hFiber
  · intro x
    have hx₁ : p x.1.1 ∈ U₁ := by
      simpa [Prod.map] using x.2.1
    have hx₂ : q x.1.2 ∈ U₂ := by
      simpa [Prod.map] using x.2.2
    ext
    · simpa [Prod.map] using hH₁ ⟨x.1.1, hx₁⟩
    · simpa [Prod.map] using hH₂ ⟨x.1.2, hx₂⟩

end IsPathConnectedEvenlyCovered

namespace Homeomorph

/-- Example 3.1.7 (1): every homeomorphism is a covering map. -/
-- Proof sketch: a homeomorphism identifies the source with the target, so every point has an open
-- neighborhood over which the map is trivial with singleton fiber.
theorem isCoveringMap (h : X ≃ₜ Y) : IsCoveringMap h := by
  have hf : Continuous (fun x : X ↦ ((h x, ()) : Y × Unit)) := by
    simpa using
      h.continuous.prodMk (continuous_const : Continuous fun _ : X ↦ (() : Unit))
  have hg : Continuous (fun yp : Y × Unit ↦ h.symm yp.1) := by
    fun_prop
  let t : Bundle.Trivialization Unit h := by
    refine
      { toFun := fun x ↦ (h x, ())
        invFun := fun yp : Y × Unit ↦ h.symm yp.1
        source := (_root_.Set.univ : Set X)
        target := (_root_.Set.univ : Set Y) ×ˢ (_root_.Set.univ : Set Unit)
        map_source' := ?_
        map_target' := ?_
        left_inv' := ?_
        right_inv' := ?_
        open_source := isOpen_univ
        open_target := isOpen_univ.prod isOpen_univ
        continuousOn_toFun := Continuous.continuousOn hf
        continuousOn_invFun := Continuous.continuousOn hg
        baseSet := (_root_.Set.univ : Set Y)
        open_baseSet := isOpen_univ
        source_eq := rfl
        target_eq := rfl
        proj_toFun := by intro x hx; rfl }
    · intro x hx
      simp [Set.mem_univ]
    · intro yp hyp
      simp [Set.mem_univ]
    · intro x hx
      simp
    · rintro ⟨y, u⟩ hyp
      cases u
      simp
  exact IsCoveringMap.mk h (fun _ ↦ Unit) (fun _ ↦ t) fun _ ↦ by simp [t]

/-- Example 3.1.7 (1), source-facing form: on a locally path-connected target, every
homeomorphism is a covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap [LocPathConnectedSpace Y] (h : X ≃ₜ Y) :
    IsPathConnectedCoveringMap h :=
  h.isCoveringMap.isPathConnectedCoveringMap h.surjective

end Homeomorph

namespace IsCoveringMap

/-- Example 3.1.7 (2): the product of two covering maps is again a covering map. -/
-- Proof sketch: take evenly covered neighborhoods for the two factors and use the product of the
-- corresponding local trivializations to trivialize the product map.
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) :
    IsCoveringMap (Prod.map p q) := by
  rintro ⟨b₁, b₂⟩
  simpa using (hp b₁).prodMap (hq b₂)

end IsCoveringMap

namespace IsPathConnectedCoveringMap

/-- Example 3.1.7 (2), source-facing form: the product of two path-connected covering maps is
again a path-connected covering map. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂}
    (hp : IsPathConnectedCoveringMap p) (hq : IsPathConnectedCoveringMap q) :
    IsPathConnectedCoveringMap (Prod.map p q) := by
  refine ⟨?_, fun b ↦ ?_⟩
  · simpa using hp.surjective.prodMap hq.surjective
  · rcases b with ⟨b₁, b₂⟩
    simpa using (hp.2 b₁).prodMap (hq.2 b₂)

end IsPathConnectedCoveringMap

/- Example 3.1.7 (3): the map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by
`Real.fourierChar`, is a covering map. -/
#check (real_fourierChar_isCoveringMap : IsCoveringMap Real.fourierChar)

namespace Circle

instance instLocPathConnectedSpace : LocPathConnectedSpace Circle :=
  ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle

end Circle

/- The map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by `Real.fourierChar`, is a
path-connected covering map in the sense of Definition 3.1.5. -/
theorem real_fourierChar_isPathConnectedCoveringMap :
    IsPathConnectedCoveringMap Real.fourierChar := by
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  have hsurjExp : Function.Surjective Circle.exp := by
    intro z
    rcases Circle.surjOn_exp_neg_pi_pi (by simp : z ∈ (Set.univ : Set Circle)) with ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hsurj : Function.Surjective Real.fourierChar := by
    simpa [Real.fourierChar_apply', Function.comp_def, smul_eq_mul] using
      hsurjExp.comp (Homeomorph.smulOfNeZero (2 * Real.pi) h2pi).surjective
  exact real_fourierChar_isCoveringMap.isPathConnectedCoveringMap hsurj

namespace Circle

private theorem isCoveringMap_npow_of_neZero (n : ℕ) [NeZero n] :
    IsCoveringMap ((· ^ n) : Circle → Circle) :=
  (isQuotientCoveringMap_npow n).isCoveringMap

private theorem isPathConnectedCoveringMap_npow_of_neZero (n : ℕ) [NeZero n] :
    IsPathConnectedCoveringMap ((· ^ n) : Circle → Circle) :=
  (isCoveringMap_npow_of_neZero n).isPathConnectedCoveringMap
    (isQuotientCoveringMap_npow n).surjective

/-- Example 3.1.7 (4): for `n ≠ 0`, the power map `z ↦ z ^ n` on `S¹` is a covering map. -/
-- Proof sketch: `Circle.isQuotientCoveringMap_npow n` gives the stronger quotient-covering
-- statement, and `IsQuotientCoveringMap.isCoveringMap` forgets the quotient-action data.
theorem isCoveringMap_npow (n : ℕ) (hn : n ≠ 0) :
    IsCoveringMap ((· ^ n) : Circle → Circle) := by
  exact @isCoveringMap_npow_of_neZero n ⟨hn⟩

/-- Example 3.1.7 (4), source-facing form: for `n ≠ 0`, the power map `z ↦ z ^ n` on `S¹` is a
path-connected covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap_npow (n : ℕ) (hn : n ≠ 0) :
    IsPathConnectedCoveringMap ((· ^ n) : Circle → Circle) := by
  exact @isPathConnectedCoveringMap_npow_of_neZero n ⟨hn⟩

end Circle
