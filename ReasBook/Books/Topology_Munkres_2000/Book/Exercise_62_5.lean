module

public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
import Topology_Munkres_2000.Book.Exercise_62_4
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

public section

open Set

universe u

namespace Topology.IsSimpleClosedCurve

/-- Helper for Exercise 62.5: an ambient homeomorphism carries a simple closed curve
to a simple closed curve. -/
theorem homeomorphImage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) [Topology.IsSimpleClosedCurve A] :
    Topology.IsSimpleClosedCurve (e '' A) := by
  -- Restrict the ambient homeomorphism to `A` and compose with its circle model.
  obtain ⟨hA⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := A)
  exact ⟨⟨(e.image A).symm.trans hA⟩⟩

end Topology.IsSimpleClosedCurve

/-- Helper for Exercise 62.5: inclusion through a simply connected intermediate
subspace induces the trivial map on fundamental groups. -/
lemma fundamentalGroupMapOfSubset_eq_one_of_isSimplyConnected
    {X : Type u} [TopologicalSpace X] {A U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) (hU : IsSimplyConnected U) (a : A) :
    FundamentalGroup.mapOfSubset (hAU.trans hUV) a = 1 := by
  letI : SimplyConnectedSpace U := hU.simplyConnectedSpace
  -- Factor the direct inclusion path map through `U`.
  unfold FundamentalGroup.mapOfSubset
  ext p
  rw [FundamentalGroup.map_apply]
  have mapThroughU :
      Path.Homotopic.Quotient.map p (ContinuousMap.inclusion (hAU.trans hUV)) =
        Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map p (ContinuousMap.inclusion hAU))
          (ContinuousMap.inclusion hUV) := by
    exact Path.Homotopic.Quotient.map_comp
      (p := p) (f := ContinuousMap.inclusion hAU) (g := ContinuousMap.inclusion hUV)
  rw [mapThroughU]
  -- The intermediate fundamental group is a subsingleton, so its loop is constant.
  rw [Subsingleton.elim
    (Path.Homotopic.Quotient.map p (ContinuousMap.inclusion hAU))
    (Path.Homotopic.Quotient.refl (ContinuousMap.inclusion hAU a))]
  rfl

/-- Helper for Exercise 62.5: translating a point in a bounded complementary component
to the origin preserves boundedness of that component. -/
private lemma isBounded_connectedComponentIn_compl_image_subRight
    {E : Type*} [NormedAddCommGroup E] (C : Set E) (x y : E)
    (hy : y ∈ connectedComponentIn Cᶜ x)
    (h_bounded : Bornology.IsBounded (connectedComponentIn Cᶜ x)) :
    Bornology.IsBounded
      (connectedComponentIn (((Homeomorph.subRight y) '' C)ᶜ) 0) := by
  -- Rebase the original component at `y`, then transport it through translation.
  let e : E ≃ₜ E := Homeomorph.subRight y
  have hyC : y ∈ Cᶜ := connectedComponentIn_subset Cᶜ x hy
  have hey : e y = 0 := by
    simp [e]
  rw [← e.image_compl C, ← hey, ← e.image_connectedComponentIn hyC,
    ← connectedComponentIn_eq hy]
  -- Translation preserves all pairwise distances, hence preserves boundedness.
  rw [Metric.isBounded_image_iff]
  obtain ⟨K, hK⟩ := Metric.isBounded_iff.mp h_bounded
  refine ⟨K, fun z hz w hw ↦ ?_⟩
  simpa only [e, Homeomorph.subRight_apply, dist_sub_right] using hK hz hw

/-- Helper for Exercise 62.5: the punctured-plane obstruction for bounded complementary
components forces such components to stay inside every simply connected intermediate set. -/
private lemma boundedComponent_compl_subset_of_fundamentalGroupObstruction
    (curveObstruction :
      ∀ (D : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve D]
        (hD : D ⊆ EuclideanPlane.punctured) (d : D),
        Bornology.IsBounded (connectedComponentIn Dᶜ 0) →
          FundamentalGroup.mapOfSubset hD d ≠ 1)
    (U C : Set (EuclideanSpace ℝ (Fin 2))) (hU_sc : IsSimplyConnected U)
    [Topology.IsSimpleClosedCurve C] (hCU : C ⊆ U)
    (x : EuclideanSpace ℝ (Fin 2))
    (h_bounded : Bornology.IsBounded (connectedComponentIn Cᶜ x)) :
    connectedComponentIn Cᶜ x ⊆ U := by
  -- Translate a hypothetical point outside `U` to the puncture at the origin.
  intro y hy
  by_contra hyU
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Homeomorph.subRight y
  have hCurveSubset : e '' C ⊆ e '' U := image_mono hCU
  have hTranslatedSimplyConnected : IsSimplyConnected (e '' U) :=
    e.isSimplyConnected_image.mpr hU_sc
  have hTranslatedAvoidsOrigin : e '' U ⊆ EuclideanPlane.punctured := by
    -- Injectivity of translation identifies a preimage of zero with the excluded point.
    rintro z ⟨u, hu, rfl⟩
    simp only [EuclideanPlane.punctured, mem_compl_iff, mem_singleton_iff]
    intro heu
    have heuy : e u = e y := by
      simpa [e] using heu
    have huy : u = y := e.injective heuy
    exact hyU (huy ▸ hu)
  have hCurvePunctured : e '' C ⊆ EuclideanPlane.punctured :=
    hCurveSubset.trans hTranslatedAvoidsOrigin
  letI : Topology.IsSimpleClosedCurve (e '' C) :=
    Topology.IsSimpleClosedCurve.homeomorphImage e C
  have hTranslatedBounded : Bornology.IsBounded
      (connectedComponentIn ((e '' C)ᶜ) 0) :=
    isBounded_connectedComponentIn_compl_image_subRight C x y hy h_bounded
  -- Evaluate both the obstruction and the simply connected factorization at one basepoint.
  obtain ⟨circleEquiv⟩ :=
    Topology.IsSimpleClosedCurve.homeomorphic_circle (X := e '' C)
  let c : e '' C := circleEquiv.symm 1
  have hNontrivial : FundamentalGroup.mapOfSubset hCurvePunctured c ≠ 1 :=
    curveObstruction (e '' C) hCurvePunctured c hTranslatedBounded
  have hTrivial : FundamentalGroup.mapOfSubset hCurvePunctured c = 1 :=
    fundamentalGroupMapOfSubset_eq_one_of_isSimplyConnected
      hCurveSubset hTranslatedAvoidsOrigin hTranslatedSimplyConnected c
  exact hNontrivial hTrivial

/-- Exercise 62.5: If a simple closed curve lies in a simply connected open subset of
`EuclideanSpace ℝ (Fin 2)`, then every bounded component of its complement lies in that set. -/
theorem boundedComponent_compl_subset_of_isSimplyConnected
    (U C : Set (EuclideanSpace ℝ (Fin 2))) (hU_open : IsOpen U)
    (hU_sc : IsSimplyConnected U) [Topology.IsSimpleClosedCurve C] (hCU : C ⊆ U)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Cᶜ)
    (h_bounded : Bornology.IsBounded (connectedComponentIn Cᶜ x)) :
    connectedComponentIn Cᶜ x ⊆ U := by
  -- Route correction: the repaired Exercise 62.4 obstruction now closes the translated
  -- punctured-plane frontier directly.
  refine boundedComponent_compl_subset_of_fundamentalGroupObstruction
    ?_ U C hU_sc hCU x h_bounded
  -- Exercise 62.4 rules out triviality whenever the origin component is bounded.
  exact fun D _ hD d hBounded ↦
    fundamentalGroupMap_ne_one_of_originComponent_bounded D hD d hBounded
