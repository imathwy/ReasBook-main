module

public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Exercise_71_2
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_59_3.Sphere
public import Topology_Munkres_2000.Book.Theorem_68_4
public import Mathlib.Geometry.Manifold.Instances.Sphere

public section

noncomputable section

open Metric Set

universe u v

/-- Helper for Exercise 71.3: stereographic projection from the antipode identifies a
neighborhood of a unit-sphere point with an orthogonal-complement vector space. -/
private def antipodalStereographicChart
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : sphere (0 : E) 1) :
    (stereographic (norm_eq_of_mem_sphere (-q))).source ≃ₜ
      Submodule.orthogonal (ℝ ∙ (-(q : E))) :=
  (stereographic (norm_eq_of_mem_sphere (-q))).toHomeomorphSourceTarget |>.trans
    (Homeomorph.Set.univ _)

/-- Helper for Exercise 71.3: a unit-sphere point belongs to the stereographic chart
centered at its antipode. -/
private lemma mem_antipodalStereographicChart_source
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : sphere (0 : E) 1) :
    q ∈ (stereographic (norm_eq_of_mem_sphere (-q))).source := by
  -- The chart omits only its center, and a unit vector is distinct from its antipode.
  rw [stereographic_source]
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
    ne_neg_of_mem_unit_sphere ℝ q

/-- Helper for Exercise 71.3: the inverse image of an antipodal stereographic chart is
the chosen local neighborhood in a homeomorphic copy of a unit sphere. -/
private def antipodalStereographicNeighborhood
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : X ≃ₜ sphere (0 : E) 1) (x : X) : Set X :=
  e ⁻¹' (stereographic (norm_eq_of_mem_sphere (-(e x)))).source

/-- Helper for Exercise 71.3: an antipodal stereographic neighborhood is homeomorphic
to a real normed vector space. -/
private def antipodalStereographicNeighborhoodHomeomorph
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : X ≃ₜ sphere (0 : E) 1) (x : X) :
    antipodalStereographicNeighborhood e x ≃ₜ
      Submodule.orthogonal (ℝ ∙ (-((e x : sphere (0 : E) 1) : E))) :=
  (e.sets rfl).trans (antipodalStereographicChart (e x))

/-- Helper for Exercise 71.3: the center point lies in its antipodal stereographic
neighborhood. -/
private lemma mem_antipodalStereographicNeighborhood
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : X ≃ₜ sphere (0 : E) 1) (x : X) :
    x ∈ antipodalStereographicNeighborhood e x := by
  -- Evaluation under the homeomorphism reduces membership to the chart-source fact.
  exact mem_antipodalStereographicChart_source (e x)

/-- Helper for Exercise 71.3: every antipodal stereographic neighborhood is open. -/
private lemma isOpen_antipodalStereographicNeighborhood
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : X ≃ₜ sphere (0 : E) 1) (x : X) :
    IsOpen (antipodalStereographicNeighborhood e x) := by
  -- Pull back the open source of the partial homeomorphism.
  exact e.isOpen_preimage.mpr
    (stereographic (norm_eq_of_mem_sphere (-(e x)))).open_source

/-- Helper for Exercise 71.3: the constant map to `x` is the endpoint map of the
singleton retraction. -/
private def singletonRetractionMap
    {X : Type u} [TopologicalSpace X] (x : X) : C(X, ({x} : Set X)) :=
  ContinuousMap.const X ⟨x, Set.mem_singleton x⟩

/-- Helper for Exercise 71.3: the constant map to `x` is a left inverse to inclusion of
the singleton. -/
private lemma singletonRetractionMap_leftInverse
    {X : Type u} [TopologicalSpace X] (x : X) :
    Function.LeftInverse (singletonRetractionMap x) Subtype.val := by
  -- Every point of the singleton has underlying value `x`.
  intro y
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp y.property).symm

/-- Helper for Exercise 71.3: the canonical retraction onto a singleton. -/
private def singletonRetraction
    {X : Type u} [TopologicalSpace X] (x : X) : Set.Retraction ({x} : Set X) :=
  Set.Retraction.ofContinuousMap (singletonRetractionMap x)
    (singletonRetractionMap_leftInverse x)

/-- Helper for Exercise 71.3: affine contraction in coordinates supplied by a
homeomorphism to a real normed vector space. -/
private def normedSpaceContraction
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : unitInterval × X → X :=
  fun z ↦ e.symm (((1 - (z.1 : ℝ)) • e z.2) + ((z.1 : ℝ) • e x))

/-- Helper for Exercise 71.3: affine contraction in homeomorphic vector-space
coordinates is continuous. -/
private lemma continuous_normedSpaceContraction
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : Continuous (normedSpaceContraction e x) := by
  -- Continuity follows from the coordinate homeomorphism and continuous affine operations.
  unfold normedSpaceContraction
  fun_prop

/-- Helper for Exercise 71.3: affine contraction starts at the identity. -/
private lemma normedSpaceContraction_zero
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x y : X) :
    normedSpaceContraction e x (0, y) = ContinuousMap.id X y := by
  -- At time zero only the original point remains.
  simp [normedSpaceContraction]

/-- Helper for Exercise 71.3: affine contraction ends at the singleton retraction. -/
private lemma normedSpaceContraction_one
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x y : X) :
    normedSpaceContraction e x (1, y) = (singletonRetraction x).toAmbient y := by
  -- At time one only the chosen center remains.
  unfold normedSpaceContraction singletonRetraction Set.Retraction.toAmbient
    singletonRetractionMap Set.Retraction.ofContinuousMap
  simp

/-- Helper for Exercise 71.3: affine contraction fixes its center throughout. -/
private lemma normedSpaceContraction_fixed
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) (t : unitInterval) {y : X} (hy : y ∈ ({x} : Set X)) :
    normedSpaceContraction e x (t, y) = ContinuousMap.id X y := by
  -- Substitute the singleton point and combine the complementary affine coefficients.
  rw [Set.mem_singleton_iff.mp hy]
  simp only [normedSpaceContraction, ContinuousMap.id_apply]
  rw [← add_smul]
  simp

/-- Helper for Exercise 71.3: affine contraction gives a relative homotopy from the
identity to the singleton retraction. -/
private def normedSpaceSingletonHomotopy
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) :
    ContinuousMap.HomotopyRel (ContinuousMap.id X) (singletonRetraction x).toAmbient {x} where
  toFun := normedSpaceContraction e x
  continuous_toFun := continuous_normedSpaceContraction e x
  map_zero_left := normedSpaceContraction_zero e x
  map_one_left := normedSpaceContraction_one e x
  prop' := normedSpaceContraction_fixed e x

/-- Helper for Exercise 71.3: a point in a space homeomorphic to a real normed vector
space is a deformation retract. -/
private lemma isDeformationRetract_singleton_of_homeomorph_normedSpace
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : Set.IsDeformationRetract ({x} : Set X) := by
  -- Package the canonical retraction together with the affine relative homotopy.
  rw [Set.isDeformationRetract_iff]
  refine ⟨singletonRetraction x, ?_⟩
  exact ⟨normedSpaceSingletonHomotopy e x⟩

/-- Helper for Exercise 71.3: collapse the indexed free product of a group and a
subsingleton group onto its first factor. -/
private def finTwoCoprodCollapse
    (G : Fin 2 → Type u) [∀ i, Group (G i)] :
    Monoid.CoprodI G →* G 0 :=
  Monoid.CoprodI.lift
    (Fin.cases (MonoidHom.id (G 0)) (Fin.cases 1 (fun i ↦ Fin.elim0 i)))

/-- Helper for Exercise 71.3: including the first factor after collapsing the binary
coproduct is the identity. -/
private lemma finTwoCoprodOf_comp_collapse
    (G : Fin 2 → Type u) [∀ i, Group (G i)]
    (htrivial : Subsingleton (G (Fin.succ 0))) :
    (Monoid.CoprodI.of : G 0 →* Monoid.CoprodI G).comp (finTwoCoprodCollapse G) =
      MonoidHom.id (Monoid.CoprodI G) := by
  -- Check the equality on the canonical generators of the indexed coproduct.
  apply Monoid.CoprodI.ext_hom
  intro i
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) i
  · ext g
    simp only [MonoidHom.comp_apply, Monoid.CoprodI.lift_of,
      finTwoCoprodCollapse, Fin.cases_zero, MonoidHom.id_apply]
  · ext g
    rw [@Subsingleton.elim _ htrivial g 1]
    simp only [map_one]

/-- Helper for Exercise 71.3: collapse of a binary coproduct with trivial second factor
is bijective. -/
private lemma finTwoCoprodCollapse_bijective
    (G : Fin 2 → Type u) [∀ i, Group (G i)]
    (htrivial : Subsingleton (G (Fin.succ 0))) :
    Function.Bijective (finTwoCoprodCollapse G) := by
  -- The first-factor inclusion is both a left and a right inverse to collapse.
  constructor
  · intro a b hab
    calc
      a = Monoid.CoprodI.of (finTwoCoprodCollapse G a) := by
        simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using
          (DFunLike.congr_fun (finTwoCoprodOf_comp_collapse G htrivial) a).symm
      _ = Monoid.CoprodI.of (finTwoCoprodCollapse G b) := congrArg Monoid.CoprodI.of hab
      _ = b := by
        simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using
          DFunLike.congr_fun (finTwoCoprodOf_comp_collapse G htrivial) b
  · intro g
    refine ⟨Monoid.CoprodI.of g, ?_⟩
    simp [finTwoCoprodCollapse]

/-- Helper for Exercise 71.3: the indexed free product of a group and a subsingleton
group is multiplicatively equivalent to the first group. -/
private def finTwoCoprodMulEquiv
    (G : Fin 2 → Type u) [∀ i, Group (G i)]
    (htrivial : Subsingleton (G (Fin.succ 0))) :
    Monoid.CoprodI G ≃* G 0 :=
  MulEquiv.ofBijective (finTwoCoprodCollapse G) (finTwoCoprodCollapse_bijective G htrivial)

/-- Exercise 71.3: The fundamental group of a finite wedge whose first component is a
circle and whose second component is a two-sphere is infinite cyclic. -/
theorem fundamentalGroup_wedge_circle_twoSphere
    {Z : Type u} [TopologicalSpace Z] (S : Fin 2 → Set Z) (p : Z)
    [Topology.IsFiniteWedge S p]
    (h_circle : Nonempty (S 0 ≃ₜ Circle))
    (h_twoSphere : Nonempty (S 1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Nonempty (FundamentalGroup Z p ≃* Multiplicative ℤ) := by
  -- Choose the two supplied models and the common wedge point in each component.
  obtain ⟨circleHomeomorph⟩ := h_circle
  obtain ⟨sphereHomeomorph⟩ := h_twoSphere
  let p₀ : S 0 := ⟨p, Topology.IsFiniteWedge.point_mem 0⟩
  let p₁ : S 1 := ⟨p, Topology.IsFiniteWedge.point_mem 1⟩
  let W₀ : Set (S 0) := antipodalStereographicNeighborhood circleHomeomorph p₀
  let W₁ : Set (S 1) := antipodalStereographicNeighborhood sphereHomeomorph p₁
  let W : ∀ i, Set (S i) := Fin.cases W₀ (Fin.cases W₁ (fun i ↦ Fin.elim0 i))
  have hW_open : ∀ i, IsOpen (W i) := by
    -- Each of the two neighborhoods is the pullback of an open chart source.
    intro i
    fin_cases i
    · exact isOpen_antipodalStereographicNeighborhood circleHomeomorph p₀
    · exact isOpen_antipodalStereographicNeighborhood sphereHomeomorph p₁
  have hpW : ∀ i, (⟨p, Topology.IsFiniteWedge.point_mem i⟩ : S i) ∈ W i := by
    -- The chart at each component is centered at the antipode of the wedge point.
    intro i
    fin_cases i
    · exact mem_antipodalStereographicNeighborhood circleHomeomorph p₀
    · exact mem_antipodalStereographicNeighborhood sphereHomeomorph p₁
  have hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, Topology.IsFiniteWedge.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)) := by
    -- Contract each chart neighborhood by its vector-space coordinates.
    intro i
    fin_cases i
    · exact isDeformationRetract_singleton_of_homeomorph_normedSpace
        (antipodalStereographicNeighborhoodHomeomorph circleHomeomorph p₀)
        ⟨p₀, hpW 0⟩
    · exact isDeformationRetract_singleton_of_homeomorph_normedSpace
        (antipodalStereographicNeighborhoodHomeomorph sphereHomeomorph p₁)
        ⟨p₁, hpW 1⟩
  -- Van Kampen identifies the ambient group as the external free product of the factors.
  let G : Fin 2 → Type u := fun i ↦
    FundamentalGroup (S i) ⟨p, Topology.IsFiniteWedge.point_mem i⟩
  let j : ∀ i, G i →* FundamentalGroup Z p := fun i ↦
    FundamentalGroup.mapOfEq
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, Z)) rfl
  have h_free : MonoidHom.IsExternalFreeProduct j :=
    fundamentalGroup_isExternalFreeProduct_of_finiteWedge S p W hW_open hpW hW_retract
  -- Normalize the circle factor to integers, allowing for its transported basepoint.
  let circleCoordinates : G 0 ≃* Multiplicative ℤ :=
    (circleHomeomorph.fundamentalGroupMulEquiv p₀).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        (circleHomeomorph p₀) 1).trans Circle.fundamentalGroupEquivInt)
  have sphereFactorSubsingleton : Subsingleton (G (Fin.succ 0)) := by
    -- Simple connectedness of the standard two-sphere trivializes its fundamental group.
    exact (sphereHomeomorph.fundamentalGroupMulEquiv p₁).toEquiv.subsingleton
  -- Compare with the canonical coproduct, then collapse its trivial sphere factor.
  obtain ⟨equiv, _, _⟩ := MonoidHom.HasFreeProductExtension.uniqueMulEquiv
    G j (fun _ ↦ Monoid.CoprodI.of) h_free.hasExtension
      (Monoid.CoprodI.instIsExternalFreeProduct G).hasExtension
  exact ⟨equiv.trans ((finTwoCoprodMulEquiv G sphereFactorSubsingleton).trans
    circleCoordinates)⟩

end
