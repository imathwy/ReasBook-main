module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Theorem_62_1.AlexanderDuality
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Theorem_63_8.SphereModTwoCohomology
public import Topology_Munkres_2000.Book.Theorem_63_8.SingularAlexanderDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.SetTheory.Cardinal.Basic

import Topology_Munkres_2000.Book.Exercise_62_6
import Topology_Munkres_2000.Book.Theorem_57_6

public section

open Set
open scoped Topology

/-- Helper for Theorem 63.8: the difference of two mod-two component generators
has coefficient sum zero. -/
private lemma componentDifferenceModTwo_mem_ker
    {ι : Type*} (i j : ι) :
    Finsupp.single i (1 : ZMod 2) - Finsupp.single j 1 ∈
      LinearMap.ker (InvarianceOfDomainSupport.componentAugmentationModTwo ι) := by
  -- Both generators have augmentation one, so their difference has augmentation zero.
  classical
  change (Finsupp.single i (1 : ZMod 2) - Finsupp.single j 1).sum
      (fun _ z ↦ z) = 0
  rw [Finsupp.sum_sub_index]
  · simp
  · simp

/-- Helper for Theorem 63.8: the reduced mod-two component chain represented by
the difference of two component generators. -/
private noncomputable def componentDifferenceModTwo
    {ι : Type*} (i j : ι) :
    LinearMap.ker (InvarianceOfDomainSupport.componentAugmentationModTwo ι) :=
  ⟨Finsupp.single i (1 : ZMod 2) - Finsupp.single j 1,
    componentDifferenceModTwo_mem_ker i j⟩

/-- Helper for Theorem 63.8: differences from three distinct component indices
give two linearly independent reduced mod-two component chains. -/
private lemma componentDifferencesModTwo_linearIndependent
    {ι : Type*} {a b c : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent (ZMod 2)
      (fun i : Fin 2 ↦ if i = 0 then componentDifferenceModTwo a b
        else componentDifferenceModTwo c b) := by
  -- Evaluation at `a` and `c` recovers the two coefficients of any relation.
  apply Fintype.linearIndependent_iff.mpr
  intro g hsum
  have hsumValue := congrArg Subtype.val hsum
  have ha := congrArg (fun w : ι →₀ ZMod 2 ↦ w a) hsumValue
  have hc := congrArg (fun w : ι →₀ ZMod 2 ↦ w c) hsumValue
  have hg0 : g 0 = 0 := by
    simpa [componentDifferenceModTwo, hab, hac] using ha
  have hg1 : g 1 = 0 := by
    simpa [componentDifferenceModTwo, hac.symm, hbc.symm] using hc
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

/-- Helper for Theorem 63.8: a space covered by two nonempty preconnected sets has
at most two connected components. -/
private lemma cardinalMk_connectedComponents_le_two_of_preconnected_cover
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hUnonempty : U.Nonempty) (hVnonempty : V.Nonempty)
    (hcover : U ∪ V = Set.univ) :
    Cardinal.mk (ConnectedComponents X) ≤ 2 := by
  -- Representatives from the two preconnected pieces surject onto the component quotient.
  classical
  obtain ⟨u, hu⟩ := hUnonempty
  obtain ⟨v, hv⟩ := hVnonempty
  let representative : Bool → X := fun b ↦ bif b then v else u
  have hsurjective : Function.Surjective
      (fun b ↦ ConnectedComponents.mk (representative b)) := by
    intro q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    have hx : x ∈ U ∨ x ∈ V := by
      have hxUnion : x ∈ U ∪ V := by
        rw [hcover]
        exact Set.mem_univ x
      exact hxUnion
    rcases hx with hxU | hxV
    · refine ⟨false, ?_⟩
      simp only [representative, Bool.cond_false]
      exact ConnectedComponents.coe_eq_coe'.mpr
        (hU.subset_connectedComponent hxU hu)
    · refine ⟨true, ?_⟩
      simp only [representative, Bool.cond_true]
      exact ConnectedComponents.coe_eq_coe'.mpr
        (hV.subset_connectedComponent hxV hv)
  -- The quotient therefore has cardinality bounded by the two-element Boolean type.
  calc
    Cardinal.mk (ConnectedComponents X) ≤ Cardinal.mk Bool :=
      Cardinal.mk_le_of_surjective hsurjective
    _ = 2 := by simp

/-- Helper for Theorem 63.8: the two open arcs between distinct circle points cover
their complement and bound its component count by two. -/
private lemma cardinalMk_connectedComponents_circle_compl_pair_le_two
    (a b : Circle) (hab : a ≠ b) :
    Cardinal.mk (ConnectedComponents ({a, b}ᶜ : Set Circle)) ≤ 2 := by
  -- Use the interiors of the two canonical directed arcs as the two pieces.
  let U : Set Circle := Circle.path a b '' Set.Ioo 0 1
  let V : Set Circle := Circle.path b a '' Set.Ioo 0 1
  have hUsubset : U ⊆ ({a, b}ᶜ : Set Circle) := by
    rintro z ⟨t, ht, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hta
      have hpathEq : Circle.path a b t = Circle.path a b 0 := by
        simpa using hta
      have ht0 : t = 0 := (Circle.path_injective_of_ne hab) hpathEq
      exact (ne_of_gt ht.1) ht0
    · intro htb
      have hpathEq : Circle.path a b t = Circle.path a b 1 := by
        simpa using htb
      have ht1 : t = 1 := (Circle.path_injective_of_ne hab) hpathEq
      exact (ne_of_lt ht.2) ht1
  have hVsubset : V ⊆ ({a, b}ᶜ : Set Circle) := by
    rintro z ⟨t, ht, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hta
      have hpathEq : Circle.path b a t = Circle.path b a 1 := by
        simpa using hta
      have ht1 : t = 1 := (Circle.path_injective_of_ne hab.symm) hpathEq
      exact (ne_of_lt ht.2) ht1
    · intro htb
      have hpathEq : Circle.path b a t = Circle.path b a 0 := by
        simpa using htb
      have ht0 : t = 0 := (Circle.path_injective_of_ne hab.symm) hpathEq
      exact (ne_of_gt ht.1) ht0
  have hUV : U ∪ V = ({a, b}ᶜ : Set Circle) := by
    apply Set.Subset.antisymm
    · exact Set.union_subset hUsubset hVsubset
    · intro z hz
      have hzRange : z ∈ Set.range (Circle.path a b) ∪
          Set.range (Circle.path b a) := by
        rw [Circle.range_path_union_range_path hab]
        exact Set.mem_univ z
      rcases hzRange with ⟨t, hzt⟩ | ⟨t, hzt⟩
      · left
        have ht0 : t ≠ 0 := by
          intro ht0
          apply hz
          left
          simpa [ht0] using hzt.symm
        have ht1 : t ≠ 1 := by
          intro ht1
          apply hz
          right
          simpa [ht1] using hzt.symm
        refine ⟨t, ⟨lt_of_le_of_ne bot_le ht0.symm,
          lt_of_le_of_ne le_top ht1⟩, hzt⟩
      · right
        have ht0 : t ≠ 0 := by
          intro ht0
          apply hz
          right
          simpa [ht0] using hzt.symm
        have ht1 : t ≠ 1 := by
          intro ht1
          apply hz
          left
          simpa [ht1] using hzt.symm
        refine ⟨t, ⟨lt_of_le_of_ne bot_le ht0.symm,
          lt_of_le_of_ne le_top ht1⟩, hzt⟩
  let U' : Set ({a, b}ᶜ : Set Circle) := Subtype.val ⁻¹' U
  let V' : Set ({a, b}ᶜ : Set Circle) := Subtype.val ⁻¹' V
  have hUpreconnected : IsPreconnected U := by
    exact isPreconnected_Ioo.image (Circle.path a b)
      (Circle.path a b).continuous.continuousOn
  have hVpreconnected : IsPreconnected V := by
    exact isPreconnected_Ioo.image (Circle.path b a)
      (Circle.path b a).continuous.continuousOn
  have hU'preconnected : IsPreconnected U' := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [U', Subtype.image_preimage_coe, Set.inter_eq_right.mpr hUsubset] using
      hUpreconnected
  have hV'preconnected : IsPreconnected V' := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [V', Subtype.image_preimage_coe, Set.inter_eq_right.mpr hVsubset] using
      hVpreconnected
  have hhalfMem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
    norm_num
  let t : unitInterval := ⟨1 / 2, hhalfMem⟩
  have ht : t ∈ Set.Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  have hU'nonempty : U'.Nonempty := by
    have hz : Circle.path a b t ∈ U := ⟨t, ht, rfl⟩
    exact ⟨⟨Circle.path a b t, hUsubset hz⟩, hz⟩
  have hV'nonempty : V'.Nonempty := by
    have hz : Circle.path b a t ∈ V := ⟨t, ht, rfl⟩
    exact ⟨⟨Circle.path b a t, hVsubset hz⟩, hz⟩
  have hU'V' : U' ∪ V' = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hz : (z : Circle) ∈ U ∪ V := by
      rw [hUV]
      exact z.property
    exact hz
  -- Passing to the complement subtype preserves the two preconnected arc pieces.
  exact cardinalMk_connectedComponents_le_two_of_preconnected_cover U' V'
    hU'preconnected hV'preconnected hU'nonempty hV'nonempty hU'V'

/-- Helper for Theorem 63.8: canonical complex coordinates preserve the Euclidean
unit-circle predicate. -/
private lemma euclideanPlaneCoordinates_mem_unitSphere
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both predicates say that the norm is one, and the coordinate map is an isometry.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Theorem 63.8: complex coordinates identify the standard one-sphere
with the complex unit circle. -/
private noncomputable def standardSphereOneHomeomorphCircle :
    StandardSphere 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneCoordinates_mem_unitSphere

/-- Helper for Theorem 63.8: a subspace homeomorphic to the standard one-sphere
is a simple closed curve. -/
private lemma isSimpleClosedCurve_of_homeomorphic_standardSphereOne
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ StandardSphere 1)) :
    Topology.IsSimpleClosedCurve C := by
  -- Compose the given homeomorphism with canonical complex coordinates on `S¹`.
  rw [Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle]
  exact hC.map (fun e ↦ e.trans standardSphereOneHomeomorphCircle)

/-- Helper for Theorem 63.8: a homeomorphism preserves avoidance of a specified
pair of points. -/
private lemma homeomorph_mem_compl_pair_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a b x : X) :
    x ∈ ({a, b}ᶜ : Set X) ↔ e x ∈ ({e a, e b}ᶜ : Set Y) := by
  -- Injectivity of the homeomorphism reflects both excluded equalities.
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    e.injective.eq_iff]

/-- Helper for Theorem 63.8: a homeomorphism restricts to the complements of a
specified pair. -/
private def pairComplementHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a b : X) :
    ({a, b}ᶜ : Set X) ≃ₜ ({e a, e b}ᶜ : Set Y) :=
  e.subtype (homeomorph_mem_compl_pair_iff e a b)

/-- Helper for Theorem 63.8: homeomorphic spaces have equally many connected
components. -/
private lemma cardinalMk_connectedComponents_eq_of_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Cardinal.mk (ConnectedComponents X) = Cardinal.mk (ConnectedComponents Y) := by
  -- The homeomorphism descends to a homeomorphism of component quotients.
  let eComponents := e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y ↦ e.isConnected_preimage.mpr (isConnected_singleton : IsConnected ({y} : Set Y)))
  exact Cardinal.mk_congr eComponents.toEquiv

/-- Helper for Theorem 63.8: deleting two distinct points from the standard
one-sphere leaves at most two connected components. -/
private lemma cardinalMk_connectedComponents_standardSphereOne_compl_pair_le_two
    (a b : StandardSphere 1) (hab : a ≠ b) :
    Cardinal.mk (ConnectedComponents ({a, b}ᶜ : Set (StandardSphere 1))) ≤ 2 := by
  -- Transport the circle arc bound through canonical complex coordinates.
  let e := standardSphereOneHomeomorphCircle
  have habCircle : e a ≠ e b := e.injective.ne hab
  have hcard := cardinalMk_connectedComponents_eq_of_homeomorph
    (pairComplementHomeomorph e a b)
  rw [hcard]
  exact cardinalMk_connectedComponents_circle_compl_pair_le_two (e a) (e b) habCircle

/-- Helper for Theorem 63.8: every point of the standard zero-sphere is a chosen
point or its antipode. -/
private lemma standardSphereZero_eq_or_eq_neg (x y : StandardSphere 0) :
    y = x ∨ y = -x := by
  -- The unique coordinate of a point of `S⁰` has square one.
  have hx : x.1 0 ^ 2 = (1 : ℝ) := by
    have hx' :=
      (Set.ext_iff.mp (EuclideanSpace.sphere_zero_eq 1 zero_le_one) x.1).mp x.property
    simpa using hx'
  have hy : y.1 0 ^ 2 = (1 : ℝ) := by
    have hy' :=
      (Set.ext_iff.mp (EuclideanSpace.sphere_zero_eq 1 zero_le_one) y.1).mp y.property
    simpa using hy'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hx.symm) with hxy | hxy
  · left
    apply Subtype.ext
    ext i
    simpa only [Fin.eq_zero i] using hxy
  · right
    apply Subtype.ext
    ext i
    simpa [Fin.eq_zero i] using hxy

/-- Helper for Theorem 63.8: separation together with an upper bound of two
complementary components forces exactly two components. -/
private lemma separatesInto_two_of_separates_of_components_le_two
    {X : Type} [TopologicalSpace X] (A : Set X) (hseparates : A.Separates)
    (hle : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 2) :
    A.SeparatesInto 2 := by
  -- Separation excludes zero or one component, so the upper bound is sharp.
  rw [Set.separatesInto_iff]
  apply le_antisymm hle
  by_contra hnot
  have hlt : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) < (2 : Cardinal) :=
    lt_of_not_ge hnot
  have hone : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 1 := by
    apply Cardinal.lt_natCast_add_one_iff.mp
    norm_num at hlt ⊢
    exact hlt
  have hsubsingleton : Subsingleton (ConnectedComponents (Aᶜ : Set X)) :=
    Cardinal.le_one_iff_subsingleton.mp hone
  have hcomponentUniv :
      ∀ x : (Aᶜ : Set X), connectedComponent x = Set.univ := by
    intro x
    apply Set.eq_univ_of_forall
    intro y
    rw [← connectedComponent_eq_iff_mem]
    exact ConnectedComponents.coe_eq_coe.mp
      (@Subsingleton.elim _ hsubsingleton
        (y : ConnectedComponents _) (x : ConnectedComponents _))
  have hpreconnected : PreconnectedSpace (Aᶜ : Set X) :=
    preconnectedSpace_iff_connectedComponent.mpr hcomponentUniv
  exact (Set.separates_iff.mp hseparates) hpreconnected

/-- Helper for Theorem 63.8: failure of a two-component bound yields three
points whose connected-component classes are pairwise distinct. -/
private lemma exists_three_componentRepresentatives_of_not_le_two
    {W : Type*} [TopologicalSpace W]
    (hnot : ¬ Cardinal.mk (ConnectedComponents W) ≤ 2) :
    ∃ a a' b : W,
      (a : ConnectedComponents W) ≠ a' ∧
      (a : ConnectedComponents W) ≠ b ∧
      (a' : ConnectedComponents W) ≠ b := by
  -- Embed `Fin 3` in the component quotient, then lift its three values.
  have hthree : (3 : Cardinal) ≤ Cardinal.mk (ConnectedComponents W) := by
    convert Cardinal.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot) using 1
    norm_num
  obtain ⟨componentEmbedding⟩ : Nonempty (Fin 3 ↪ ConnectedComponents W) := by
    apply Cardinal.lift_mk_le'.mp
    simpa using hthree
  obtain ⟨a, ha⟩ := ConnectedComponents.surjective_coe (componentEmbedding 0)
  obtain ⟨a', ha'⟩ := ConnectedComponents.surjective_coe (componentEmbedding 1)
  obtain ⟨b, hb⟩ := ConnectedComponents.surjective_coe (componentEmbedding 2)
  have hzeroNeOne : (0 : Fin 3) ≠ 1 := by
    decide
  have hzeroNeTwo : (0 : Fin 3) ≠ 2 := by
    decide
  have honeNeTwo : (1 : Fin 3) ≠ 2 := by
    decide
  refine ⟨a, a', b, ?_, ?_, ?_⟩
  · rw [ha, ha']
    exact componentEmbedding.injective.ne hzeroNeOne
  · rw [ha, hb]
    exact componentEmbedding.injective.ne hzeroNeTwo
  · rw [ha', hb]
    exact componentEmbedding.injective.ne honeNeTwo

-- Route correction: reduced homology is normalized to component chains only
-- after the global singular-duality rank bound has been established.
/-- Helper for Theorem 63.8: if reduced mod-two `H₀` contains no independent
pair, then a locally path-connected space has at most two components. -/
private lemma cardinalMk_connectedComponents_le_two_of_noIndependentPair
    {X : Type} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    (noIndependentPair : ∀ v : Fin 2 →
        InvarianceOfDomainSupport.reducedHomologyZeroModTwo (TopCat.of X),
      ¬ LinearIndependent (ZMod 2) v) :
    Cardinal.mk (ConnectedComponents X) ≤ 2 := by
  -- Three components would provide two independent augmentation-kernel classes.
  by_contra hnot
  obtain ⟨a, a', b, haa', hab, ha'b⟩ :=
    exists_three_componentRepresentatives_of_not_le_two hnot
  let componentsToPaths := connectedComponentsEquivZerothHomotopy (X := X)
  let aPath := componentsToPaths (a : ConnectedComponents X)
  let a'Path := componentsToPaths (a' : ConnectedComponents X)
  let bPath := componentsToPaths (b : ConnectedComponents X)
  have haa'Path : aPath ≠ a'Path := componentsToPaths.injective.ne haa'
  have habPath : aPath ≠ bPath := componentsToPaths.injective.ne hab
  have ha'bPath : a'Path ≠ bPath := componentsToPaths.injective.ne ha'b
  let componentChains := fun i : Fin 2 ↦ if i = 0 then
    componentDifferenceModTwo aPath a'Path
  else componentDifferenceModTwo bPath a'Path
  have hcomponentChains :
      LinearIndependent (ZMod 2) componentChains := by
    -- The connected-to-path-component equivalence preserves all three inequalities.
    exact componentDifferencesModTwo_linearIndependent
      haa'Path habPath ha'bPath
  obtain ⟨eKernel⟩ :=
    InvarianceOfDomainSupport.nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel
      (TopCat.of X)
  let reducedChains := eKernel.symm.toLinearMap ∘ componentChains
  have hReducedChains :
      LinearIndependent (ZMod 2) reducedChains := by
    -- Normalize the component chains to reduced singular homology.
    exact hcomponentChains.map' eKernel.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr eKernel.symm.injective)
  -- The resulting pair contradicts the assumed rank obstruction in reduced `H₀`.
  exact noIndependentPair reducedChains hReducedChains

/-- Helper for Theorem 63.8: normed vector spaces have bases of contractible
metric neighborhoods. -/
private lemma stronglyLocallyContractibleSpace_normedModel
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    StronglyLocallyContractibleSpace E := by
  -- Positive-radius metric balls form the required contractible neighborhood basis.
  exact StronglyLocallyContractibleSpace.of_bases
    (fun _ ↦ Metric.nhds_basis_ball)
    (fun _ _ hr ↦ Metric.contractibleSpace_ball hr)

/-- Helper for Theorem 63.8: a charted space modeled on a strongly locally
contractible space is strongly locally contractible. -/
private lemma stronglyLocallyContractibleSpace_of_chartedModel
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [StronglyLocallyContractibleSpace H] :
    StronglyLocallyContractibleSpace M := by
  -- Pull a contractible basis inside each chart target back through the chart.
  refine StronglyLocallyContractibleSpace.of_bases
    (p := fun x s ↦
      s ∈ nhds (chartAt H x x) ∧ ContractibleSpace s ∧
        s ⊆ (chartAt H x).target)
    (s := fun x s ↦ (chartAt H x).symm '' s) ?_ ?_
  · intro x
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((contractible_basis (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  · rintro x s ⟨_, hsContractible, hsTarget⟩
    -- Local instance justification (contractibility): the chosen basis member's
    -- witness is needed to transport contractibility through this chart restriction.
    letI : ContractibleSpace s := hsContractible
    exact
      ((chartAt H x).symm.homeomorphOfImageSubsetSource hsTarget rfl).symm.contractibleSpace

/-- Helper for Theorem 63.8: a subspace homeomorphic to a standard sphere is
locally contractible. -/
private lemma locallyContractibleSpace_of_homeomorphic_standardSphere
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    LocallyContractibleSpace C := by
  -- First obtain strong local contractibility from the standard sphere charts.
  -- Local instance justification (regularity): the model-space instance is supplied
  -- by the preceding generic lemma and is not available through typeclass search.
  letI : StronglyLocallyContractibleSpace (EuclideanSpace ℝ (Fin n)) :=
    stronglyLocallyContractibleSpace_normedModel _
  have hSphereStrong : StronglyLocallyContractibleSpace (StandardSphere n) :=
    stronglyLocallyContractibleSpace_of_chartedModel
      (EuclideanSpace ℝ (Fin n)) (StandardSphere n)
  obtain ⟨e⟩ := hC
  -- Local instance justification (regularity): this witness records the chart proof
  -- for the standard sphere so the homeomorphism can transport it to `C`.
  letI : StronglyLocallyContractibleSpace (StandardSphere n) := hSphereStrong
  have hCStrong : StronglyLocallyContractibleSpace C :=
    e.isOpenEmbedding.stronglyLocallyContractibleSpace
  -- Local instance justification (regularity): the transported structure depends on
  -- the chosen homeomorphism and therefore is kept proof-local.
  letI : StronglyLocallyContractibleSpace C := hCStrong
  -- Forget the stronger neighborhood-basis property at the final step.
  exact StronglyLocallyContractibleSpace.locallyContractible (X := C)

/-- Helper for Theorem 63.8: top mod-two cohomology is transported through a
homeomorphism with the standard sphere. -/
private lemma nonempty_topModTwoCohomologyLinearEquiv_of_homeomorphic_standardSphere
    (n : ℕ) (hn : 0 < n) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    Nonempty
      (AlgebraicTopology.ModTwoSingularCohomology (TopCat.of C) n ≃ₗ[ZMod 2]
        ZMod 2) := by
  -- Compose homeomorphism invariance with the standard-sphere computation.
  obtain ⟨e⟩ := hC
  obtain ⟨eSphere⟩ :=
    AlgebraicTopology.standardSphereTopModTwoCohomologyLinearEquiv n hn
  exact ⟨(AlgebraicTopology.modTwoSingularCohomologyMapIso
    (TopCat.isoOfHomeo e) n).toLinearEquiv.trans eSphere⟩

/-- Helper for Theorem 63.8: Alexander duality identifies the complement's
reduced mod-two `H₀` with the one-dimensional coefficient field. -/
private lemma nonempty_reducedHomologyZeroModTwoEquivZModTwo_sphereComplement
    (n : ℕ) (hn : 0 < n) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    Nonempty
      (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
          (TopCat.of (Cᶜ : Set (StandardSphere (n + 1)))) ≃ₗ[ZMod 2]
        ZMod 2) := by
  -- Install compactness and local contractibility for singular Alexander duality.
  obtain ⟨e⟩ := hC
  -- Local instance justification (transported compactness): compactness of `C`
  -- depends on the chosen homeomorphism with the standard sphere.
  letI : CompactSpace C := e.symm.compactSpace
  have hCLocallyContractible : LocallyContractibleSpace C :=
    locallyContractibleSpace_of_homeomorphic_standardSphere n C ⟨e⟩
  obtain ⟨eCohomology⟩ :=
    nonempty_topModTwoCohomologyLinearEquiv_of_homeomorphic_standardSphere
      n hn C ⟨e⟩
  obtain ⟨eAlexander⟩ :=
    InvarianceOfDomainSupport.nonempty_topModTwoAlexanderDuality
      n hn C hCLocallyContractible
  -- Reverse duality and then apply the sphere cohomology computation.
  exact ⟨eAlexander.symm.trans eCohomology⟩

/-- Helper for Theorem 63.8: rank-one reduced mod-two `H₀` permits at most
two connected components in a locally path-connected space. -/
private lemma cardinalMk_connectedComponents_le_two_of_rankOneReducedHomologyZeroModTwo
    {X : Type} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    (hRankOne : Nonempty
      (InvarianceOfDomainSupport.reducedHomologyZeroModTwo (TopCat.of X) ≃ₗ[ZMod 2]
        ZMod 2)) :
    Cardinal.mk (ConnectedComponents X) ≤ 2 := by
  -- Transport any hypothetical independent pair to the one-dimensional field.
  obtain ⟨eRankOne⟩ := hRankOne
  apply cardinalMk_connectedComponents_le_two_of_noIndependentPair
  intro v hv
  have hRankOneIndependent :
      LinearIndependent (ZMod 2) (fun i ↦ eRankOne (v i)) := by
    -- Injectivity of the equivalence preserves linear independence.
    exact hv.map' eRankOne.toLinearMap
      (LinearMap.ker_eq_bot.mpr eRankOne.injective)
  have htwo : 2 ≤ Module.finrank (ZMod 2) (ZMod 2) := by
    simpa using hRankOneIndependent.fintype_card_le_finrank
  -- The coefficient field has rank one over itself, contradicting the pair bound.
  have htwoOne : (2 : ℕ) ≤ 1 := by
    simpa only [Module.finrank_self] using htwo
  omega

/-- Helper for Theorem 63.8: nonzero rank-one reduced mod-two `H₀` of an
open complement forces that complement to be non-preconnected. -/
private lemma separates_of_rankOneReducedHomologyZeroModTwo
    {X : Type} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    (A : Set X) (hA : IsClosed A)
    (hRankOne : Nonempty
      (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
          (TopCat.of (Aᶜ : Set X)) ≃ₗ[ZMod 2]
        ZMod 2)) :
    A.Separates := by
  -- Preconnectedness would make reduced `H₀` a zero object.
  rw [Set.separates_iff]
  intro hPreconnectedSpace
  have hPreconnected : IsPreconnected Aᶜ :=
    isPreconnected_iff_preconnectedSpace.mpr hPreconnectedSpace
  have hZero :=
    (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
      Aᶜ hA.isOpen_compl).mp hPreconnected
  obtain ⟨eRankOne⟩ := hRankOne
  have hSourceSubsingleton : Subsingleton
      (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
        (TopCat.of (Aᶜ : Set X))) :=
    ModuleCat.isZero_iff_subsingleton.mp hZero
  have hTargetSubsingleton : Subsingleton (ZMod 2) :=
    eRankOne.toEquiv.subsingleton_congr.mp hSourceSubsingleton
  -- The coefficient field is nontrivial, contradicting the transported zero object.
  have honeEqZero : (1 : ZMod 2) = 0 :=
    @Subsingleton.elim (ZMod 2) hTargetSubsingleton 1 0
  exact one_ne_zero honeEqZero

/-- Helper for Theorem 63.8: an embedded standard sphere is closed in the
ambient standard sphere. -/
private lemma isClosed_of_homeomorphic_standardSphere
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) : IsClosed C := by
  -- Transfer compactness across the homeomorphism and use the Hausdorff ambient sphere.
  obtain ⟨e⟩ := hC
  -- Local instance justification (transported compactness): the compact structure on
  -- `C` is transported through the chosen homeomorphism witness.
  letI : CompactSpace C := e.symm.compactSpace
  exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed

/-- Theorem 63.8 (1): A subspace of the standard `(n + 1)`-sphere homeomorphic to
the standard `n`-sphere separates it into exactly two components. -/
theorem jordanBrouwer_separatesInto (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    C.SeparatesInto 2 := by
  -- Separate the zero-sphere and Jordan-curve cases from higher-dimensional duality.
  rcases n.eq_zero_or_pos with rfl | hn
  · obtain ⟨e⟩ := hC
    have hnonnegativeRadius : (0 : ℝ) ≤ 1 := by
      norm_num
    have hSphereNonempty : Nonempty (StandardSphere 0) :=
      (NormedSpace.sphere_nonempty.mpr hnonnegativeRadius).coe_sort
    obtain ⟨x⟩ := hSphereNonempty
    let a : C := e.symm x
    let b : C := e.symm (-x)
    have hab : a ≠ b := by
      intro hab
      apply ne_neg_of_mem_unit_sphere ℝ x
      simpa only [a, b, e.apply_symm_apply] using congrArg e hab
    have hCpair : C = {(a : StandardSphere 1), (b : StandardSphere 1)} := by
      ext z
      constructor
      · intro hz
        let zC : C := ⟨z, hz⟩
        rcases standardSphereZero_eq_or_eq_neg x (e zC) with heq | heq
        · have himage : e zC = e a := by
            simpa only [a, e.apply_symm_apply] using heq
          have hza : zC = a := e.injective himage
          exact Set.mem_insert_iff.mpr (Or.inl (congrArg Subtype.val hza))
        · have himage : e zC = e b := by
            simpa only [b, e.apply_symm_apply] using heq
          have hzb : zC = b := e.injective himage
          exact Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton_iff.mpr (congrArg Subtype.val hzb)))
      · intro hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact a.property
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact b.property
    have habVal : (a : StandardSphere 1) ≠ (b : StandardSphere 1) :=
      fun h ↦ hab (Subtype.ext h)
    have hNotPreconnected : ¬ IsPreconnected Cᶜ := by
      -- Transport the explicit two-point complement to the complex unit circle.
      rw [hCpair]
      intro hPreconnected
      have habCircle : standardSphereOneHomeomorphCircle a ≠
          standardSphereOneHomeomorphCircle b :=
        standardSphereOneHomeomorphCircle.injective.ne habVal
      apply Circle.not_isPreconnected_compl_pair habCircle
      apply (standardSphereOneHomeomorphCircle.isPreconnected_preimage).mp
      have hPreimage : standardSphereOneHomeomorphCircle ⁻¹'
          ({standardSphereOneHomeomorphCircle a,
            standardSphereOneHomeomorphCircle b}ᶜ : Set Circle) =
          ({(a : StandardSphere 1), (b : StandardSphere 1)}ᶜ :
            Set (StandardSphere 1)) := by
        ext z
        simp
      rw [hPreimage]
      exact hPreconnected
    have hseparates : C.Separates := by
      -- The set-level obstruction is the complement subtype obstruction.
      rw [Set.separates_iff]
      intro hPreconnectedSpace
      exact hNotPreconnected
        (isPreconnected_iff_preconnectedSpace.mpr hPreconnectedSpace)
    have hle : Cardinal.mk
        (ConnectedComponents (Cᶜ : Set (StandardSphere 1))) ≤ 2 := by
      rw [hCpair]
      exact cardinalMk_connectedComponents_standardSphereOne_compl_pair_le_two
        (a : StandardSphere 1) (b : StandardSphere 1) habVal
    -- The explicit circle argument supplies the lower bound without Theorem 63.7.
    exact separatesInto_two_of_separates_of_components_le_two C
      hseparates hle
  · by_cases hnOne : n = 1
    · subst n
      -- The ordinary Jordan curve theorem already gives the exact count in dimension one.
      -- Local instance justification (simple closed curve): the structure is transported
      -- from the supplied homeomorphism with the standard one-sphere.
      letI : Topology.IsSimpleClosedCurve C :=
        isSimpleClosedCurve_of_homeomorphic_standardSphereOne C hC
      exact jordanCurveSphere_separatesInto C
    · have hCclosed : IsClosed C :=
        isClosed_of_homeomorphic_standardSphere n C hC
      -- Local instance justification (ambient regularity): sphere charts provide the
      -- local path-connectedness used by reduced `H₀` detection.
      letI : LocallyPathConnectedSpace (StandardSphere (n + 1)) :=
        ChartedSpace.locallyPathConnectedSpace
          (EuclideanSpace ℝ (Fin (n + 1))) _
      -- Local instance justification (complement regularity): the complement is open.
      letI : LocallyPathConnectedSpace
          (Cᶜ : Set (StandardSphere (n + 1))) :=
        hCclosed.isOpen_compl.locallyPathConnectedSpace
      have hRankOne :=
        nonempty_reducedHomologyZeroModTwoEquivZModTwo_sphereComplement
          n hn C hC
      have hseparates : C.Separates :=
        separates_of_rankOneReducedHomologyZeroModTwo C hCclosed hRankOne
      have hle : Cardinal.mk
          (ConnectedComponents (Cᶜ : Set (StandardSphere (n + 1)))) ≤ 2 :=
        cardinalMk_connectedComponents_le_two_of_rankOneReducedHomologyZeroModTwo
          hRankOne
      -- The one rank computation gives both the lower and upper component bounds.
      exact separatesInto_two_of_separates_of_components_le_two C hseparates hle

/-- Helper for Theorem 63.8: exactly two complementary components imply
separation. -/
private lemma separates_of_separatesInto_two
    {X : Type*} [TopologicalSpace X] (A : Set X) (hA : A.SeparatesInto 2) :
    A.Separates := by
  -- A preconnected complement has at most one connected component, contradicting two.
  rw [Set.separates_iff]
  intro hPreconnected
  letI : PreconnectedSpace (Aᶜ : Set X) := hPreconnected
  have hle : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 1 :=
    Cardinal.le_one_iff_subsingleton.mpr inferInstance
  rw [Set.separatesInto_iff] at hA
  rw [hA] at hle
  norm_num at hle

/-- Helper for Theorem 63.8: the frontier of a complementary component of a
closed set in a locally connected space lies in that set. -/
private lemma frontier_connectedComponentIn_compl_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (A : Set X) (hA : IsClosed A) (x : (Aᶜ : Set X)) :
    frontier (connectedComponentIn Aᶜ x) ⊆ A := by
  -- Complementary components are open in a locally connected space.
  intro z hz
  have hcomponentOpen : IsOpen (connectedComponentIn Aᶜ x) :=
    hA.isOpen_compl.connectedComponentIn
  have hzNotMem : z ∉ connectedComponentIn Aᶜ x := by
    intro hzMem
    have hzInterior : z ∈ interior (connectedComponentIn Aᶜ x) :=
      hcomponentOpen.interior_eq.symm ▸ hzMem
    exact (mem_frontier_iff_notMem_interior hzMem).mp hz hzInterior
  -- A frontier point outside `A` would belong to another open component that
  -- meets the original component, forcing the two components to coincide.
  by_contra hzA
  have hzCompl : z ∈ Aᶜ := hzA
  have hzOwnComponent : z ∈ connectedComponentIn Aᶜ z :=
    mem_connectedComponentIn hzCompl
  have hownOpen : IsOpen (connectedComponentIn Aᶜ z) :=
    hA.isOpen_compl.connectedComponentIn
  have hzClosure : z ∈ closure (connectedComponentIn Aᶜ x) :=
    frontier_subset_closure hz
  rcases mem_closure_iff.mp hzClosure (connectedComponentIn Aᶜ z) hownOpen hzOwnComponent with
    ⟨y, hyOwn, hyComponent⟩
  have heq : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ z :=
    (connectedComponentIn_eq hyComponent).trans (connectedComponentIn_eq hyOwn).symm
  exact hzNotMem (heq ▸ hzOwnComponent)

-- Route correction: separation already supplies a second complementary
-- component, so the frontier argument does not need the exact component count.
/-- Helper for Theorem 63.8: a separating closed set has a complementary point
outside the closure of the component containing a prescribed point. -/
private lemma exists_complementPoint_not_mem_componentClosure_of_separates
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (A : Set X) (hA : IsClosed A)
    (hseparates : A.Separates)
    (x : (Aᶜ : Set X)) :
    ∃ b : (Aᶜ : Set X), (b : X) ∉ closure (connectedComponentIn Aᶜ x) := by
  -- Separation prevents the component quotient of the complement from being a singleton.
  classical
  have hnotPreconnected : ¬ PreconnectedSpace (Aᶜ : Set X) :=
    Set.separates_iff.mp hseparates
  have hnotSubsingleton : ¬ Subsingleton (ConnectedComponents (Aᶜ : Set X)) := by
    intro hsubsingleton
    apply hnotPreconnected
    rw [preconnectedSpace_iff_connectedComponent]
    intro y
    apply Set.eq_univ_of_forall
    intro z
    rw [← connectedComponent_eq_iff_mem]
    exact ConnectedComponents.coe_eq_coe.mp
      (@Subsingleton.elim _ hsubsingleton
        (z : ConnectedComponents _) (y : ConnectedComponents _))
  have hotherComponent :
      ∃ q : ConnectedComponents (Aᶜ : Set X), q ≠ (x : ConnectedComponents _) := by
    by_contra hnot
    apply hnotSubsingleton
    constructor
    intro q r
    have hq : q = (x : ConnectedComponents _) := by
      by_contra hqx
      exact hnot ⟨q, hqx⟩
    have hr : r = (x : ConnectedComponents _) := by
      by_contra hrx
      exact hnot ⟨r, hrx⟩
    exact hq.trans hr.symm
  obtain ⟨q, hqx⟩ := hotherComponent
  obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe q
  have hbNotMem : (b : X) ∉ connectedComponentIn Aᶜ x := by
    intro hb
    rw [connectedComponentIn_eq_image x.property] at hb
    obtain ⟨z, hz, hzb⟩ := hb
    have hzx : b ∈ connectedComponent x := by
      have hzb' : z = b := Subtype.ext hzb
      exact hzb' ▸ hz
    exact hqx (ConnectedComponents.coe_eq_coe'.mpr hzx)
  refine ⟨b, ?_⟩
  -- The other component is an open neighborhood of `b` disjoint from the
  -- component of `x`, hence also disjoint from its closure at `b`.
  intro hbClosure
  have hbOwn : (b : X) ∈ connectedComponentIn Aᶜ b :=
    mem_connectedComponentIn b.property
  have hbOwnOpen : IsOpen (connectedComponentIn Aᶜ b) :=
    hA.isOpen_compl.connectedComponentIn
  rcases mem_closure_iff.mp hbClosure (connectedComponentIn Aᶜ b) hbOwnOpen hbOwn with
    ⟨y, hyOwn, hyComponent⟩
  have heq : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ b :=
    (connectedComponentIn_eq hyComponent).trans (connectedComponentIn_eq hyOwn).symm
  exact hbNotMem (heq ▸ hbOwn)

/-- Helper for Theorem 63.8: a preconnected set meeting a set and the
complement of its closure also meets its frontier. -/
private lemma IsPreconnected.inter_frontier_nonempty_of_mem_of_mem_compl_closure
    {X : Type*} [TopologicalSpace X] {S W : Set X} (hS : IsPreconnected S)
    (hSW : (S ∩ W).Nonempty) (hSclosure : (S ∩ (closure W)ᶜ).Nonempty) :
    (S ∩ frontier W).Nonempty := by
  -- A point outside the closure is in particular outside the original set.
  have hScompl : (S ∩ Wᶜ).Nonempty := by
    obtain ⟨x, hxS, hxClosure⟩ := hSclosure
    exact ⟨x, hxS, fun hxW ↦ hxClosure (subset_closure hxW)⟩
  -- Avoiding the frontier would force the preconnected set into one of the
  -- two disjoint interiors, contradicting one of the two witnesses.
  by_contra hfrontier
  rw [Set.not_nonempty_iff_eq_empty] at hfrontier
  have hdisjoint : Disjoint S (frontier W) :=
    Set.disjoint_iff_inter_eq_empty.mpr hfrontier
  have hcover : S ⊆ interior W ∪ interior Wᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact hdisjoint.subset_compl_right
  have hinteriors : Disjoint (interior W) (interior Wᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  obtain hSin | hSin :=
    hS.subset_or_subset isOpen_interior isOpen_interior hinteriors hcover
  · obtain ⟨x, hxS, hxCompl⟩ := hScompl
    exact hxCompl (interior_subset (hSin hxS))
  · obtain ⟨x, hxS, hxW⟩ := hSW
    exact (interior_subset (hSin hxS)) hxW

/-- Helper for Theorem 63.8: the complement of a subspace homeomorphic to a
closed `n`-ball has vanishing reduced mod-two `H₀`. -/
private lemma isZero_reducedHomologyZeroModTwo_closedBallComplement
    (n : ℕ) (B : Set (StandardSphere (n + 1)))
    (hB : Nonempty
      (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    CategoryTheory.Limits.IsZero
      (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
        (TopCat.of (Bᶜ : Set (StandardSphere (n + 1))))) := by
  -- Transfer compactness and contractibility from the standard closed ball to `B`.
  classical
  obtain ⟨e⟩ := hB
  -- Local instance justification (transported compactness): compactness of `B`
  -- depends on its chosen homeomorphism with the closed ball.
  letI : CompactSpace B := e.symm.compactSpace
  -- Local instance justification (contractibility): the closed-ball instance needs
  -- the explicit nonnegative-radius witness used in this proof.
  letI : ContractibleSpace
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Metric.contractibleSpace_closedBall zero_le_one
  -- Local instance justification (transported contractibility): contractibility of
  -- `B` depends on the chosen homeomorphism and is not canonical globally.
  letI : ContractibleSpace B := e.contractibleSpace
  -- The odd-map obstruction supplies the no-retraction input to the generalized
  -- Borsuk lemma, which makes the complement preconnected.
  have hOdd : StandardSphere.OddSelfMapsNotNullhomotopic n :=
    StandardSphere.OddSelfMapsNotNullhomotopic.of_forall n
      (StandardSphere.oddSelfMap_not_nullhomotopic n)
  have hNoRetract : ¬ Set.IsRetract (StandardSphere.boundary n) :=
    sphereNotRetractOfBall n hOdd
  have hNoRetractPrevious :
      ¬ Set.IsRetract (StandardSphere.boundary ((n + 1) - 1)) := by
    rw [Nat.add_sub_cancel_right]
    exact hNoRetract
  have hNotSeparates : ¬ B.Separates :=
    compactContractible_not_separates_sphere (n + 1) (Nat.succ_pos n)
      hNoRetractPrevious B
  have hPreconnectedSpace : PreconnectedSpace (Bᶜ : Set (StandardSphere (n + 1))) := by
    rw [Set.separates_iff] at hNotSeparates
    exact Classical.byContradiction hNotSeparates
  have hPreconnected : IsPreconnected Bᶜ :=
    isPreconnected_iff_preconnectedSpace.mpr hPreconnectedSpace
  -- On the open complement, preconnectedness is exactly vanishing reduced `H₀`.
  -- Local instance justification (regularity): the charted-sphere structure provides
  -- local path-connectedness for the reduced-homology characterization.
  letI : LocallyPathConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  have hBopen : IsOpen Bᶜ :=
    (isCompact_iff_compactSpace.mpr inferInstance).isClosed.isOpen_compl
  exact
    (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
      Bᶜ hBopen).mp hPreconnected

/-- Helper for Theorem 63.8: the complement of a subspace homeomorphic to a
closed `n`-ball in the standard `(n + 1)`-sphere is preconnected. -/
private lemma isPreconnected_compl_of_homeomorphic_closedBall
    (n : ℕ) (B : Set (StandardSphere (n + 1)))
    (hB : Nonempty
      (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    IsPreconnected Bᶜ := by
  -- Closedness makes the complement open, so reduced `H₀` detects preconnectedness.
  -- Local instance justification (regularity): the charted-sphere structure provides
  -- local path-connectedness for the reduced-homology characterization.
  letI : LocallyPathConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  have hBzero :=
    isZero_reducedHomologyZeroModTwo_closedBallComplement n B hB
  obtain ⟨e⟩ := hB
  -- Local instance justification (transported compactness): compactness of `B`
  -- depends on the selected homeomorphism with the closed ball.
  letI : CompactSpace B := e.symm.compactSpace
  have hBopen : IsOpen Bᶜ :=
    (isCompact_iff_compactSpace.mpr inferInstance).isClosed.isOpen_compl
  exact
    (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
      Bᶜ hBopen).mpr
        hBzero

/-- Helper for Theorem 63.8: the ambient Euclidean space defining
`StandardSphere n` has dimension `n + 1`. -/
private lemma finrank_standardSphereAmbient (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
  -- Euclidean coordinates are indexed by `Fin (n + 1)`.
  simp

/-- Helper for Theorem 63.8: the dimension fact needed by the generic
stereographic chart on `StandardSphere n`. -/
private instance standardSphereAmbientFinrankFact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_standardSphereAmbient n⟩

/-- Helper for Theorem 63.8: stereographic projection identifies a punctured
standard `n`-sphere with `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def puncturedStandardSphereHomeomorphEuclidean
    (n : ℕ) (p : StandardSphere n) :
    ({p}ᶜ : Set (StandardSphere n)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  ((Homeomorph.setCongr (stereographic'_source p).symm).trans
    (stereographic' n p).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target p)).trans (Homeomorph.Set.univ _))

/-- Helper for Theorem 63.8: the punctured-sphere homeomorphism agrees pointwise
with `stereographic'`. -/
@[simp] private lemma puncturedStandardSphereHomeomorphEuclidean_apply
    (n : ℕ) (p : StandardSphere n) (x : ({p}ᶜ : Set (StandardSphere n))) :
    puncturedStandardSphereHomeomorphEuclidean n p x = stereographic' n p x := by
  -- The set-congruence maps only adjust the source and target subtype spellings.
  rfl

/-- Helper for Theorem 63.8: positive scalar dilation carries the unit closed
ball onto the closed ball of that radius. -/
private lemma smulTorsor_mem_closedBall_iff
    {n : ℕ} {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ Metric.closedBall 0 1 ↔
      DilationEquiv.smulTorsor (0 : EuclideanSpace ℝ (Fin n)) hr.ne' x ∈
        Metric.closedBall 0 r := by
  -- Norm scaling reduces membership in both centered balls to the same inequality.
  simp only [Metric.mem_closedBall, DilationEquiv.smulTorsor_apply, vadd_eq_add,
    add_zero, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rw [mul_comm r ‖x‖, mul_le_iff_le_one_left hr]

/-- Helper for Theorem 63.8: a positive-radius Euclidean closed ball is
homeomorphic to the unit closed ball. -/
private noncomputable def closedBallHomeomorphUnitBall
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ((DilationEquiv.smulTorsor (0 : EuclideanSpace ℝ (Fin n)) hr.ne').toHomeomorph.subtype
    (smulTorsor_mem_closedBall_iff hr)).symm

/-- Helper for Theorem 63.8: every neighborhood of a point on an embedded
`n`-sphere contains the complement of a closed `n`-ball core. -/
private lemma exists_closedBallCore_of_mem_nhds
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n))
    (c : C) {U : Set (StandardSphere (n + 1))} (hU : U ∈ 𝓝 (c : StandardSphere (n + 1))) :
    ∃ B : Set (StandardSphere (n + 1)),
      B ⊆ C ∧
        Nonempty (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        C \ B ⊆ U := by
  -- Choose an open ambient neighborhood so its complement on the compact sphere
  -- remains compact after transport through the embedding homeomorphism.
  classical
  obtain ⟨e⟩ := hC
  obtain ⟨O, hOU, hOopen, hcO⟩ := mem_nhds_iff.mp hU
  let p : StandardSphere n := e c
  let V : Set (StandardSphere n) :=
    (fun q ↦ ((e.symm q : C) : StandardSphere (n + 1))) ⁻¹' O
  have hVopen : IsOpen V := by
    exact hOopen.preimage (continuous_subtype_val.comp e.symm.continuous)
  have hpV : p ∈ V := by
    simpa [p, V] using hcO
  have hKcompact : IsCompact Vᶜ :=
    hVopen.isClosed_compl.isCompact
  have hKpunct : Vᶜ ⊆ ({p}ᶜ : Set (StandardSphere n)) := by
    intro q hqK hqp
    exact hqK (Set.mem_singleton_iff.mp hqp ▸ hpV)
  -- Local instance justification (compact core): compactness of this complement
  -- subtype comes from the particular neighborhood `V` chosen above.
  letI : CompactSpace (Vᶜ : Set (StandardSphere n)) :=
    isCompact_iff_compactSpace.mp hKcompact
  -- Send the compact complement through the punctured-sphere chart and enclose
  -- its Euclidean image in a positive-radius closed ball.
  let punctured := puncturedStandardSphereHomeomorphEuclidean n p
  let kToPunct : (Vᶜ : Set (StandardSphere n)) →
      ({p}ᶜ : Set (StandardSphere n)) :=
    fun q ↦ ⟨q, hKpunct q.property⟩
  have hkToPunctContinuous : Continuous kToPunct := by
    exact continuous_subtype_val.subtype_mk _
  let chartOnK : (Vᶜ : Set (StandardSphere n)) → EuclideanSpace ℝ (Fin n) :=
    fun q ↦ punctured (kToPunct q)
  have hchartOnKContinuous : Continuous chartOnK := by
    exact punctured.continuous.comp hkToPunctContinuous
  have hchartRangeCompact : IsCompact (Set.range chartOnK) :=
    isCompact_range hchartOnKContinuous
  obtain ⟨r, hr, hchartRange⟩ :=
    hchartRangeCompact.isBounded.subset_closedBall_lt 0
      (0 : EuclideanSpace ℝ (Fin n))
  -- Pull this closed ball back through the chart and then through the embedded
  -- copy of the sphere in the ambient sphere.
  let D : Set ({p}ᶜ : Set (StandardSphere n)) :=
    punctured ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  let embeddedPuncture : ({p}ᶜ : Set (StandardSphere n)) →
      StandardSphere (n + 1) :=
    fun q ↦ (e.symm q : StandardSphere (n + 1))
  have hembeddedPuncture : Topology.IsEmbedding embeddedPuncture := by
    exact Topology.IsEmbedding.subtypeVal.comp
      (e.symm.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  let B : Set (StandardSphere (n + 1)) := embeddedPuncture '' D
  let DHomeomorphBall :
      D ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r :=
    punctured.subtype (fun _ ↦ Iff.rfl)
  let DHomeomorphB : D ≃ₜ B :=
    hembeddedPuncture.homeomorphImage D
  have hBball : Nonempty
      (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ⟨DHomeomorphB.symm.trans
      (DHomeomorphBall.trans (closedBallHomeomorphUnitBall n r hr))⟩
  refine ⟨B, ?_, hBball, ?_⟩
  · -- Every point of the pulled-back ball lies in the embedded sphere `C`.
    rintro y ⟨q, hqD, rfl⟩
    exact (e.symm q).property
  · -- A point of `C` outside the core maps into `V`, hence lies in `O ⊆ U`.
    rintro y ⟨hyC, hyB⟩
    apply hOU
    by_contra hyO
    let q : StandardSphere n := e ⟨y, hyC⟩
    have hqK : q ∈ Vᶜ := by
      intro hqV
      apply hyO
      simpa [q, V] using hqV
    let qK : (Vᶜ : Set (StandardSphere n)) := ⟨q, hqK⟩
    let qPunct : ({p}ᶜ : Set (StandardSphere n)) := kToPunct qK
    have hqBall : punctured qPunct ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
      apply hchartRange
      exact ⟨qK, rfl⟩
    apply hyB
    refine ⟨qPunct, hqBall, ?_⟩
    have hrecover := congrArg Subtype.val (e.symm_apply_apply ⟨y, hyC⟩)
    simpa only [embeddedPuncture, qPunct, kToPunct, qK, q] using hrecover

/-- Helper for Theorem 63.8: every point of an embedded sphere lies in the
frontier of every complementary component. -/
private lemma homeomorphic_standardSphere_subset_frontier_component
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n))
    (x : (Cᶜ : Set (StandardSphere (n + 1)))) :
    C ⊆ frontier (connectedComponentIn Cᶜ x) := by
  -- Use local connectedness to keep complementary components open.
  -- Local instance justification (regularity): the charted-sphere API supplies the
  -- ambient local connectedness needed for openness of complementary components.
  letI : LocallyConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  have hCclosed : IsClosed C := isClosed_of_homeomorphic_standardSphere n C hC
  have hseparates : C.Separates :=
    separates_of_separatesInto_two C (jordanBrouwer_separatesInto n C hC)
  have hfrontierSubset : frontier (connectedComponentIn Cᶜ x) ⊆ C :=
    frontier_connectedComponentIn_compl_subset_of_isClosed C hCclosed x
  -- It suffices to produce a frontier point in each neighborhood of `c`.
  intro c hc
  apply isClosed_frontier.closure_subset
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨B, hBC, hBball, hCBU⟩ :=
    exists_closedBallCore_of_mem_nhds n C hC ⟨c, hc⟩ hU
  obtain ⟨b, hbClosure⟩ :=
    exists_complementPoint_not_mem_componentClosure_of_separates
      C hCclosed hseparates x
  have hxB : (x : StandardSphere (n + 1)) ∈ Bᶜ := by
    intro hx
    exact x.property (hBC hx)
  have hbB : (b : StandardSphere (n + 1)) ∈ Bᶜ := by
    intro hb
    exact b.property (hBC hb)
  have hBpre : IsPreconnected Bᶜ :=
    isPreconnected_compl_of_homeomorphic_closedBall n B hBball
  have hBcomponent : (Bᶜ ∩ connectedComponentIn Cᶜ x).Nonempty :=
    ⟨x, hxB, mem_connectedComponentIn x.property⟩
  have hBoutside :
      (Bᶜ ∩ (closure (connectedComponentIn Cᶜ x))ᶜ).Nonempty :=
    ⟨b, hbB, hbClosure⟩
  obtain ⟨y, hyB, hyFrontier⟩ :=
    IsPreconnected.inter_frontier_nonempty_of_mem_of_mem_compl_closure
      hBpre hBcomponent hBoutside
  have hyCB : y ∈ C \ B := ⟨hfrontierSubset hyFrontier, hyB⟩
  exact ⟨y, hCBU hyCB, hyFrontier⟩

/-- Theorem 63.8 (2): Each component of the complement has the embedded
subspace `C` as its frontier in the standard `(n + 1)`-sphere. -/
theorem jordanBrouwer_frontier_component (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n))
    (x : (Cᶜ : Set (StandardSphere (n + 1)))) :
    frontier (connectedComponentIn Cᶜ x) = C := by
  -- Combine the general closed-set inclusion with the neighborhood crossing argument.
  -- Local instance justification (regularity): the charted-sphere API supplies the
  -- ambient local connectedness required by the closed-set frontier lemma.
  letI : LocallyConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  apply Set.Subset.antisymm
  · exact frontier_connectedComponentIn_compl_subset_of_isClosed C
      (isClosed_of_homeomorphic_standardSphere n C hC) x
  · exact homeomorphic_standardSphere_subset_frontier_component n C hC x
