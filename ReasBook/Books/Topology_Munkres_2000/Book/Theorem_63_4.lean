module

public import Topology_Munkres_2000.Book.Theorem_61_4
public import Topology_Munkres_2000.Book.Theorem_63_2
public import Topology_Munkres_2000.Book.Theorem_9_0_1.CrossingComponents
public import Topology_Munkres_2000.Book.Exercise_23_6
public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Example_53_6.Polar
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.SetTheory.Cardinal.Basic

public section

open Set
open scoped Topology

/-- Helper for Theorem 63.4: the two points in an intersection equal to
`{p, q}` belong to both intersecting sets. -/
private lemma pair_mem_of_inter_eq_pair
    {X : Type*} {A₁ A₂ : Set X} {p q : X} (hinter : A₁ ∩ A₂ = {p, q}) :
    p ∈ A₁ ∧ p ∈ A₂ ∧ q ∈ A₁ ∧ q ∈ A₂ := by
  -- Rewrite each endpoint through the stated intersection equation.
  have hp : p ∈ A₁ ∩ A₂ := by
    rw [hinter]
    simp
  have hq : q ∈ A₁ ∩ A₂ := by
    rw [hinter]
    simp
  exact ⟨hp.1, hp.2, hq.1, hq.2⟩

/-- Helper for Theorem 63.4: inside the twice-punctured space, the complements
of two sets meeting exactly at the punctures cover the whole space. -/
private lemma pairComplement_preimage_compl_union_eq_univ
    {X : Type*} (A₁ A₂ : Set X) (p q : X) (hinter : A₁ ∩ A₂ = {p, q}) :
    (Subtype.val ⁻¹' A₁ᶜ : Set ({p, q}ᶜ : Set X)) ∪
        Subtype.val ⁻¹' A₂ᶜ = Set.univ := by
  -- A point outside `{p, q}` cannot belong to both sets.
  ext x
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_contra h
  push Not at h
  have hx : x.1 ∈ A₁ ∩ A₂ := ⟨h.1, h.2⟩
  rw [hinter] at hx
  exact x.2 hx

/-- Helper for Theorem 63.4: the overlap of the two complement preimages is
the preimage of the complement of their union. -/
private lemma pairComplement_preimage_compl_inter
    {X : Type*} (A₁ A₂ : Set X) (p q : X) :
    (Subtype.val ⁻¹' A₁ᶜ : Set ({p, q}ᶜ : Set X)) ∩
        Subtype.val ⁻¹' A₂ᶜ = Subtype.val ⁻¹' (A₁ ∪ A₂)ᶜ := by
  -- Membership on both sides is the same pair of negated membership statements.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_union,
    not_or]

/-- Helper for Theorem 63.4: separation and an upper bound of two complementary
components force exactly two complementary components. -/
private lemma separatesInto_two_of_separates_of_components_le_two
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hsep : A.Separates)
    (hle : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 2) :
    A.SeparatesInto 2 := by
  -- Separation rules out the only cardinals strictly below two.
  rw [Set.separatesInto_iff]
  apply le_antisymm hle
  by_contra hnot
  have hlt : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) < (2 : Cardinal) :=
    lt_of_not_ge hnot
  have hone : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 1 := by
    apply Cardinal.lt_natCast_add_one_iff.mp
    norm_num at hlt ⊢
    exact hlt
  have hsub : Subsingleton (ConnectedComponents (Aᶜ : Set X)) :=
    Cardinal.le_one_iff_subsingleton.mp hone
  have hallComponents : ∀ x : (Aᶜ : Set X), connectedComponent x = Set.univ := by
    intro x
    apply eq_univ_of_forall
    intro y
    rw [← connectedComponent_eq_iff_mem]
    exact ConnectedComponents.coe_eq_coe.mp
      (@Subsingleton.elim _ hsub (y : ConnectedComponents _) (x : ConnectedComponents _))
  have hpre : PreconnectedSpace (Aᶜ : Set X) :=
    preconnectedSpace_iff_connectedComponent.mpr hallComponents
  exact (Set.separates_iff.mp hsep) hpre

/-- Helper for Theorem 63.4: a spherical arc is a closed connected subset of
the standard two-sphere. -/
private lemma isClosed_and_isConnected_of_isArc
    (A : Set (StandardSphere 2)) [Topology.IsArc A] :
    IsClosed A ∧ IsConnected A := by
  -- Transport compactness and connectedness from the unit interval model.
  classical
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := e.symm.compactSpace
  letI : ConnectedSpace A := e.symm.surjective.connectedSpace e.symm.continuous
  have hcompact : IsCompact A := isCompact_iff_compactSpace.mpr inferInstance
  exact ⟨hcompact.isClosed, isConnected_iff_connectedSpace.mpr inferInstance⟩

/-- Helper for Theorem 63.4: an arc contains a point distinct from any
prescribed pair of its points. -/
private lemma exists_mem_arc_ne_pair
    (A : Set (StandardSphere 2)) [Topology.IsArc A]
    (p q : StandardSphere 2) (hp : p ∈ A) (hq : q ∈ A) :
    ∃ r ∈ A, r ≠ p ∧ r ≠ q := by
  -- Transfer infinitude from the unit interval and avoid the selected endpoints.
  classical
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  have hzeroOne : (0 : ℝ) < 1 := by
    norm_num
  letI : Infinite unitInterval := Set.Icc.infinite hzeroOne
  letI : Infinite A := e.toEquiv.infinite_iff.mpr inferInstance
  let pA : A := ⟨p, hp⟩
  let qA : A := ⟨q, hq⟩
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({pA, qA} : Finset A)
  refine ⟨r, r.2, ?_, ?_⟩
  · intro hrp
    apply hr
    exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hrp))
  · intro hrq
    apply hr
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr (Subtype.ext hrq)))

/-- Helper for Theorem 63.4: a nonseparating closed complement remains
path-joinable after deleting two points of the closed set. -/
private lemma joinedIn_preimage_compl_pairComplement
    (D : Set (StandardSphere 2)) (hDclosed : IsClosed D)
    (p q : StandardSphere 2) (hp : p ∈ D) (hq : q ∈ D)
    (hDnonseparating : ¬ D.Separates)
    (a b : ({p, q}ᶜ : Set (StandardSphere 2)))
    (ha : a.1 ∈ Dᶜ) (hb : b.1 ∈ Dᶜ) :
    JoinedIn (Subtype.val ⁻¹' Dᶜ) a b := by
  -- First join the points in a stereographic chart on the full complement.
  have hDcompl_subset_puncture : Dᶜ ⊆ ({p}ᶜ : Set (StandardSphere 2)) := by
    intro x hxD hxp
    exact hxD (hxp ▸ hp)
  let chart := StandardSphere.puncturedHomeomorphPlane p
  let chartDomain : Set ({p}ᶜ : Set (StandardSphere 2)) := Subtype.val ⁻¹' Dᶜ
  have hchartDomain_image : ((fun x ↦ x.1) '' chartDomain) = Dᶜ := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hDcompl_subset_puncture]
  have hchartDomain_open : IsOpen chartDomain :=
    hDclosed.isOpen_compl.preimage continuous_subtype_val
  have hchartDomain_nonempty : chartDomain.Nonempty :=
    ⟨⟨a.1, hDcompl_subset_puncture ha⟩, ha⟩
  have hDcompl_preconnected : IsPreconnected Dᶜ := by
    apply isPreconnected_iff_preconnectedSpace.mpr
    by_contra hpre
    exact hDnonseparating (Set.separates_iff.mpr hpre)
  have hchartDomain_preconnected : IsPreconnected chartDomain := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hchartDomain_image]
    exact hDcompl_preconnected
  have hchartDomain_connected : IsConnected chartDomain :=
    ⟨hchartDomain_nonempty, hchartDomain_preconnected⟩
  have hchartImage_open : IsOpen (chart '' chartDomain) :=
    chart.isOpenMap chartDomain hchartDomain_open
  have hchartImage_connected : IsConnected (chart '' chartDomain) :=
    chart.isConnected_image.mpr hchartDomain_connected
  have hchartImage_pathConnected : IsPathConnected (chart '' chartDomain) :=
    (hchartImage_open.isConnected_iff_isPathConnected).mp hchartImage_connected
  have hchartDomain_pathConnected : IsPathConnected chartDomain :=
    chart.isPathConnected_image.mp hchartImage_pathConnected
  have hab_punctured : JoinedIn chartDomain
      (⟨a.1, hDcompl_subset_puncture ha⟩ : ({p}ᶜ : Set (StandardSphere 2)))
      (⟨b.1, hDcompl_subset_puncture hb⟩ : ({p}ᶜ : Set (StandardSphere 2))) := by
    exact hchartDomain_pathConnected.joinedIn _ ha _ hb
  have hab_sphere : JoinedIn Dᶜ a.1 b.1 := by
    have himage := hab_punctured.map continuous_subtype_val
    rw [hchartDomain_image] at himage
    exact himage
  -- The path avoids both punctures because both lie in `D`.
  have hpair_subset : Dᶜ ⊆ ({p, q}ᶜ : Set (StandardSphere 2)) := by
    intro x hxD hxpair
    rcases hxpair with hxp | hxq
    · exact hxD (hxp ▸ hp)
    · exact hxD (hxq ▸ hq)
  have hpair_image :
      ((fun x ↦ x.1) '' (Subtype.val ⁻¹' Dᶜ : Set ({p, q}ᶜ : Set (StandardSphere 2)))) =
        Dᶜ := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hpair_subset]
  apply (Topology.IsInducing.subtypeVal.joinedIn_image
    (F := Subtype.val ⁻¹' Dᶜ) ha hb).mp
  rwa [hpair_image]

/-- Helper for Theorem 63.4: forgetting the second puncture gives the nested
punctured-sphere point used by stereographic projection. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Theorem 63.4: flattening the nested puncture recovers a point
outside the two-point set. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Theorem 63.4: the nesting map between punctured spheres is
continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build continuity through the two successive subtype constructors.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩ : ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Theorem 63.4: flattening the nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- Both subtype projections are continuous; membership proofs are propositional.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Theorem 63.4: flattening after nesting fixes each point of the
pair complement. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Equality of the underlying sphere points determines the subtype values.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 63.4: nesting after flattening fixes each nested
punctured-sphere point. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Equality of the underlying sphere points determines the subtype values.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Theorem 63.4: the two-point complement is canonically the
one-point complement inside a punctured sphere. -/
private def pairComplementHomeomorphNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  { toFun := pairComplementToNestedPuncture p q
    invFun := nestedPunctureToPairComplement p q
    left_inv := nestedPunctureToPairComplement_leftInverse p q
    right_inv := nestedPunctureToPairComplement_rightInverse p q
    continuous_toFun := continuous_pairComplementToNestedPuncture p q
    continuous_invFun := continuous_nestedPunctureToPairComplement p q }

/-- Helper for Theorem 63.4: the second puncture belongs to the chart centered
at the first puncture. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Membership is exactly the reversed distinctness assumption.
  simpa using hpq.symm

/-- Helper for Theorem 63.4: stereographic coordinates followed by the
standard Euclidean-complex identification. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (StandardSphere.puncturedHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Theorem 63.4: translate stereographic coordinates so the
second puncture is sent to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Theorem 63.4: the translated chart is nonzero exactly away
from the second puncture. -/
private lemma translatedPuncturedSphereChart_ne_zero_iff
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p}ᶜ : Set (StandardSphere 2))) :
    x.1 ≠ q ↔ translatedPuncturedSphereChart p q hpq x ≠ 0 := by
  -- Translation turns nonvanishing into inequality with the chart image of `q`.
  simp only [translatedPuncturedSphereChart, Homeomorph.trans_apply,
    Homeomorph.subRight_apply, sub_ne_zero]
  rw [(puncturedSphereHomeomorphComplex p).injective.ne_iff]
  simpa using (Subtype.coe_ne_coe (a := x)
    (b := (⟨q, secondPoint_mem_firstPointComplement p q hpq⟩ :
      ({p}ᶜ : Set (StandardSphere 2)))))

/-- Helper for Theorem 63.4: stereographic projection and translation identify
the twice-punctured sphere with the punctured complex plane. -/
private noncomputable def twicePuncturedSphereHomeomorphPuncturedComplexPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Helper for Theorem 63.4: the nested-subtype inclusion and reconstruction
are inverse in the forward direction. -/
private lemma nestedSubtypeToAmbient_leftInverse
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    Function.LeftInverse
      (fun x : S ↦ (⟨⟨x.1, hSP x.2⟩, x.2⟩ :
        (Subtype.val ⁻¹' S : Set P)))
      (fun x : (Subtype.val ⁻¹' S : Set P) ↦ (⟨x.1.1, x.2⟩ : S)) := by
  -- Extensionality reduces the nested carrier equality to the ambient value.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Theorem 63.4: the nested-subtype inclusion and reconstruction
are inverse in the backward direction. -/
private lemma nestedSubtypeToAmbient_rightInverse
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    Function.RightInverse
      (fun x : S ↦ (⟨⟨x.1, hSP x.2⟩, x.2⟩ :
        (Subtype.val ⁻¹' S : Set P)))
      (fun x : (Subtype.val ⁻¹' S : Set P) ↦ (⟨x.1.1, x.2⟩ : S)) := by
  -- Extensionality reduces the carrier equality to the ambient value.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 63.4: a set cut out inside a larger subtype is
homeomorphic to the same set viewed in the ambient space. -/
private def nestedSubtypeHomeomorph
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := nestedSubtypeToAmbient_leftInverse P S hSP
    right_inv := nestedSubtypeToAmbient_rightInverse P S hSP
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun x ↦ x.2)
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk (fun x ↦ hSP x.2)).subtype_mk (fun x ↦ x.2) }

/-- Helper for Theorem 63.4: a homeomorphism induces a homeomorphism of
connected-component quotients. -/
private noncomputable def connectedComponentsHomeomorphOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y :=
  e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y ↦ e.isConnected_preimage.mpr (isConnected_singleton : IsConnected ({y} : Set Y)))

/-- Helper for Theorem 63.4: polar and exponential coordinates identify the
punctured complex plane with the infinite cylinder. -/
private noncomputable def puncturedComplexPlaneHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- Helper for Theorem 63.4: the infinite cylinder has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroupInfiniteCylinderEquivInt (p : Circle × ℝ) :
    Nonempty (FundamentalGroup (Circle × ℝ) p ≃* Multiplicative ℤ) := by
  -- Contractibility removes the real factor, leaving the circle calculation.
  exact ⟨(FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2 inferInstance).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt)⟩

/-- Helper for Theorem 63.4: the punctured complex plane has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroup_puncturedComplexPlane_equiv_int
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Transport the cylinder calculation through polar and logarithmic coordinates.
  let e := puncturedComplexPlaneHomeomorphInfiniteCylinder
  exact ⟨(e.fundamentalGroupMulEquiv z).trans
    (fundamentalGroupInfiniteCylinderEquivInt (e z)).some⟩

/-- Helper for Theorem 63.4: the twice-punctured sphere has infinite-cyclic
fundamental group at every basepoint. -/
private lemma pairComplementFundamentalGroupEquivInt
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- Transport first to the punctured plane, then use the cylinder calculation.
  let e := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  exact ⟨(e.fundamentalGroupMulEquiv x).trans
    (fundamentalGroup_puncturedComplexPlane_equiv_int (e x)).some⟩

/-- Helper for Theorem 63.4: the complement of two spherical arcs meeting at
exactly two distinct endpoints has at most two connected components. -/
private lemma arcPairComplementComponents_le_two
    (A₁ A₂ : Set (StandardSphere 2)) [Topology.IsArc A₁] [Topology.IsArc A₂]
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : A₁ ∩ A₂ = {p, q}) :
    Cardinal.mk (ConnectedComponents ((A₁ ∪ A₂)ᶜ : Set (StandardSphere 2))) ≤ 2 := by
  -- Normalize the arc-pair complement as an overlap in the twice-punctured sphere.
  have hA₁geometry := isClosed_and_isConnected_of_isArc A₁
  have hA₂geometry := isClosed_and_isConnected_of_isArc A₂
  have hpqMem := pair_mem_of_inter_eq_pair hinter
  let P : Set (StandardSphere 2) := {p, q}ᶜ
  let U : Set P := Subtype.val ⁻¹' A₁ᶜ
  let V : Set P := Subtype.val ⁻¹' A₂ᶜ
  let W : Set (StandardSphere 2) := (A₁ ∪ A₂)ᶜ
  have hUopen : IsOpen U :=
    hA₁geometry.1.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V :=
    hA₂geometry.1.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ :=
    pairComplement_preimage_compl_union_eq_univ A₁ A₂ p q hinter
  have hWinter : U ∩ V = Subtype.val ⁻¹' W :=
    pairComplement_preimage_compl_inter A₁ A₂ p q
  have hWsubset : W ⊆ P := by
    intro x hxW hxPair
    rcases hxPair with hxp | hxq
    · exact hxW (Or.inl (hxp ▸ hpqMem.1))
    · exact hxW (Or.inl (hxq ▸ hpqMem.2.2.1))
  let overlapHomeomorph : (U ∩ V : Set P) ≃ₜ W :=
    (Homeomorph.setCongr hWinter).trans (nestedSubtypeHomeomorph P W hWsubset)
  -- Each cover complement contains an interior point of its corresponding arc.
  have hUcompl : Uᶜ.Nonempty := by
    obtain ⟨r, hrA₁, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₁ p q hpqMem.1 hpqMem.2.2.1
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    let rP : P := ⟨r, hrP⟩
    refine ⟨rP, ?_⟩
    simpa only [U, mem_compl_iff, mem_preimage, not_not] using hrA₁
  have hVcompl : Vᶜ.Nonempty := by
    obtain ⟨r, hrA₂, hrp, hrq⟩ :=
      exists_mem_arc_ne_pair A₂ p q hpqMem.2.1 hpqMem.2.2.2
    have hrP : r ∈ P := by
      simpa only [P, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        ⟨hrp, hrq⟩
    let rP : P := ⟨r, hrP⟩
    refine ⟨rP, ?_⟩
    simpa only [V, mem_compl_iff, mem_preimage, not_not] using hrA₂
  have hWopen : IsOpen W :=
    (hA₁geometry.1.union hA₂geometry.1).isOpen_compl
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  letI : LocallyConnectedSpace W := hWopen.locallyConnectedSpace
  letI : LocallyConnectedSpace (U ∩ V : Set P) :=
    overlapHomeomorph.locallyConnectedSpace
  have hjoinedU : ∀ x y : (U ∩ V : Set P), JoinedIn U x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement A₁ hA₁geometry.1 p q
      hpqMem.1 hpqMem.2.2.1 (arc_not_separates A₁)
      x.1 y.1 x.2.1 y.2.1
  have hjoinedV : ∀ x y : (U ∩ V : Set P), JoinedIn V x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement A₂ hA₂geometry.1 p q
      hpqMem.2.1 hpqMem.2.2.2 (arc_not_separates A₂)
      x.1 y.1 x.2.2 y.2.2
  have hfundamental : ∀ x : (U ∩ V : Set P),
      Nonempty (FundamentalGroup P x.1 ≃* Multiplicative ℤ) := by
    intro x
    exact pairComplementFundamentalGroupEquivInt p q hpq x.1
  have hoverlapBound :
      Cardinal.mk (ConnectedComponents (U ∩ V : Set P)) ≤ 2 :=
    Theorem901.mk_connectedComponents_inter_le_two_of_windingCover
      U V hUopen hVopen hUcompl hVcompl hcover hjoinedU hjoinedV hfundamental
  -- Transport the overlap bound back to the ambient complementary set.
  rw [← Cardinal.mk_congr
    (connectedComponentsHomeomorphOfHomeomorph overlapHomeomorph).toEquiv]
  exact hoverlapBound

/-- Helper for Theorem 63.4: two spherical arcs meeting exactly at two
distinct endpoints have exactly two complementary components. -/
private lemma sphereArcPair_separatesInto_two
    (A₁ A₂ : Set (StandardSphere 2)) [Topology.IsArc A₁] [Topology.IsArc A₂]
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : A₁ ∩ A₂ = {p, q}) :
    (A₁ ∪ A₂).SeparatesInto 2 := by
  -- Combine the general separation theorem with the component upper bound.
  have hA₁geometry := isClosed_and_isConnected_of_isArc A₁
  have hA₂geometry := isClosed_and_isConnected_of_isArc A₂
  have hseparates : (A₁ ∪ A₂).Separates :=
    union_separates_of_inter_pair A₁ A₂ p q hpq hinter
      hA₁geometry.1 hA₂geometry.1 hA₁geometry.2 hA₂geometry.2
  exact separatesInto_two_of_separates_of_components_le_two
    (A₁ ∪ A₂) hseparates
      (arcPairComplementComponents_le_two A₁ A₂ p q hpq hinter)

/-- Helper for Theorem 63.4: every circle-like subset of a Hausdorff space is
the union of two closed connected arcs meeting at distinct endpoints. -/
private lemma existsTwoArcDecomposition
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (D : Set X) [Topology.IsSimpleClosedCurve D] :
    ∃ D₁ D₂ : Set X, ∃ p q : X,
      p ≠ q ∧ D = D₁ ∪ D₂ ∧ D₁ ∩ D₂ = {p, q} ∧
        IsClosed D₁ ∧ IsClosed D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧
        Topology.IsArc D₁ ∧ Topology.IsArc D₂ := by
  classical
  -- Transport the two canonical circle paths between antipodal points into `D`.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := D)
  let f : Circle → X := fun z ↦ (e.symm z : X)
  let p : X := f 1
  let q : X := f (-1)
  let D₁ : Set X := Set.range (f ∘ Circle.path 1 (-1))
  let D₂ : Set X := Set.range (f ∘ Circle.path (-1) 1)
  have hfContinuous : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hpq : p ≠ q := by
    intro hpq
    exact (Circle.neg_ne_self 1).symm (hfInjective hpq)
  have hRange : Set.range f = D := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, rfl⟩
      exact (e.symm y).property
    · intro x hx
      have hfx : f (e ⟨x, hx⟩) = x := by
        simp [f]
      exact ⟨e ⟨x, hx⟩, hfx⟩
  have hpath₁Continuous : Continuous (f ∘ Circle.path 1 (-1)) :=
    hfContinuous.comp (Circle.path 1 (-1)).continuous
  have hpath₂Continuous : Continuous (f ∘ Circle.path (-1) 1) :=
    hfContinuous.comp (Circle.path (-1) 1).continuous
  have hpath₁Injective : Function.Injective (f ∘ Circle.path 1 (-1)) :=
    hfInjective.comp (Circle.path_injective_of_ne (Circle.neg_ne_self 1).symm)
  have hpath₂Injective : Function.Injective (f ∘ Circle.path (-1) 1) :=
    hfInjective.comp (Circle.path_injective_of_ne (Circle.neg_ne_self 1))
  -- Compact-domain embeddings identify both path ranges with the unit interval.
  have hD₁Arc : Topology.IsArc D₁ := by
    let hEmbedding : Topology.IsEmbedding (f ∘ Circle.path 1 (-1)) :=
      hpath₁Continuous.isClosedEmbedding hpath₁Injective |>.isEmbedding
    exact ⟨⟨hEmbedding.toHomeomorph.symm⟩⟩
  have hD₂Arc : Topology.IsArc D₂ := by
    let hEmbedding : Topology.IsEmbedding (f ∘ Circle.path (-1) 1) :=
      hpath₂Continuous.isClosedEmbedding hpath₂Injective |>.isEmbedding
    exact ⟨⟨hEmbedding.toHomeomorph.symm⟩⟩
  have hD₁image : D₁ = f '' Set.range (Circle.path 1 (-1)) := by
    simp [D₁, Set.range_comp]
  have hD₂image : D₂ = f '' Set.range (Circle.path (-1) 1) := by
    simp [D₂, Set.range_comp]
  -- The complementary circle paths cover the circle and meet only at endpoints.
  have hUnion : D = D₁ ∪ D₂ := by
    rw [hD₁image, hD₂image, ← Set.image_union,
      Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm, Set.image_univ]
    exact hRange.symm
  have hInter : D₁ ∩ D₂ = {p, q} := by
    rw [hD₁image, hD₂image, ← Set.image_inter hfInjective,
      Circle.range_path_inter_range_path (Circle.neg_ne_self 1).symm, Set.image_pair]
  -- Continuity from the compact interval supplies closedness and connectedness.
  refine ⟨D₁, D₂, p, q, hpq, hUnion, hInter, ?_, ?_, ?_, ?_, hD₁Arc, hD₂Arc⟩
  · exact (isCompact_range hpath₁Continuous).isClosed
  · exact (isCompact_range hpath₂Continuous).isClosed
  · exact isConnected_range hpath₁Continuous
  · exact isConnected_range hpath₂Continuous

/-- Theorem 63.4 (1): A simple closed curve in the standard two-sphere
separates the sphere into exactly two components. -/
theorem jordanCurveSphere_separatesInto
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C] :
    C.SeparatesInto 2 := by
  -- Decompose the curve into two canonical arcs and apply the global component bound.
  obtain ⟨C₁, C₂, p, q, hpq, hUnion, hInter, -, -, -, -, hC₁Arc, hC₂Arc⟩ :=
    existsTwoArcDecomposition C
  letI : Topology.IsArc C₁ := hC₁Arc
  letI : Topology.IsArc C₂ := hC₂Arc
  rw [hUnion]
  exact sphereArcPair_separatesInto_two C₁ C₂ p q hpq hInter

/-- Helper for Theorem 63.4: a simple closed curve in the standard sphere is
compact, hence closed. -/
private lemma isCompact_of_isSimpleClosedCurve_standardSphere
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C] : IsCompact C := by
  -- Transfer compactness from the circle across the defining homeomorphism.
  classical
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := e.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- Helper for Theorem 63.4: in a locally connected space, the frontier of a
complementary component of a closed set lies in that set. -/
private lemma frontierConnectedComponentInComplement_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (A : Set X) (hA : IsClosed A) (x : (Aᶜ : Set X)) :
    frontier (connectedComponentIn Aᶜ x) ⊆ A := by
  -- Openness of complementary components excludes their own points from the frontier.
  intro z hz
  have hcomponentOpen : IsOpen (connectedComponentIn Aᶜ x) :=
    hA.isOpen_compl.connectedComponentIn
  have hzNotMem : z ∉ connectedComponentIn Aᶜ x := by
    intro hzMem
    have hzInterior : z ∈ interior (connectedComponentIn Aᶜ x) :=
      hcomponentOpen.interior_eq.symm ▸ hzMem
    exact (mem_frontier_iff_notMem_interior hzMem).mp hz hzInterior
  -- A frontier point outside `A` lies in another open complementary component.
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
  -- Intersecting connected components coincide, contradicting exclusion above.
  have heq : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ z :=
    (connectedComponentIn_eq hyComponent).trans (connectedComponentIn_eq hyOwn).symm
  exact hzNotMem (heq ▸ hzOwnComponent)

/-- Helper for Theorem 63.4: there is a complement point outside the component
of any prescribed complement point. -/
private lemma exists_complementPoint_not_mem_component
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (StandardSphere 2))) :
    ∃ b : (Cᶜ : Set (StandardSphere 2)),
      (b : StandardSphere 2) ∉ connectedComponentIn Cᶜ x := by
  -- Exact cardinality two supplies a second connected-component class.
  classical
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set (StandardSphere 2))) = 2 :=
    separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
  obtain ⟨q, hqx, _⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x)).mp hcomponents
  obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe q
  refine ⟨b, ?_⟩
  intro hb
  rw [connectedComponentIn_eq_image x.property] at hb
  obtain ⟨z, hz, hzb⟩ := hb
  have hzx : b ∈ connectedComponent x := by
    have hzb' : z = b := Subtype.ext hzb
    exact hzb' ▸ hz
  exact hqx (ConnectedComponents.coe_eq_coe'.mpr hzx)

/-- Helper for Theorem 63.4: every neighborhood of a point on a simple closed
curve contains one arc in a two-arc decomposition of the curve. -/
private lemma existsTwoArcDecomposition_first_subset_nhds
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.IsSimpleClosedCurve C]
    {z : X} (hzC : z ∈ C) {N : Set X} (hN : N ∈ 𝓝 z) :
    ∃ A₁ A₂ : Set X, Topology.IsArc A₁ ∧ Topology.IsArc A₂ ∧
      C = A₁ ∪ A₂ ∧ A₁ ⊆ N := by
  classical
  -- Center circle coordinates at `z` and pull the prescribed neighborhood back.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  let zC : C := ⟨z, hzC⟩
  let w : Circle := e zC
  let f : Circle → X := fun v ↦ (e.symm v : X)
  let rotation : Circle ≃ₜ Circle := Homeomorph.mulLeft w
  let g : Circle → X := f ∘ rotation
  have hfContinuous : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hgContinuous : Continuous g := hfContinuous.comp rotation.continuous
  have hgInjective : Function.Injective g := hfInjective.comp rotation.injective
  have hgOne : g 1 = z := by
    simp [g, rotation, f, w, zC]
  have hpreimageN : g ⁻¹' N ∈ 𝓝 (1 : Circle) := by
    rw [← hgOne] at hN
    exact hgContinuous.continuousAt hN
  obtain ⟨n, -, hn⟩ :=
    Circle.hasBasis_centeredArc_div_two_pow.mem_iff.mp hpreimageN
  let R : ℝ := Real.pi / (2 : ℝ) ^ (n + 1)
  let r : ℝ := R / 2
  have hcentered : Circle.centeredArc R ⊆ g ⁻¹' N := by
    simpa only [R] using hn
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRlepi : R ≤ Real.pi := by
    dsimp [R]
    exact div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two)
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hrltR : r < R := by
    dsimp [r]
    linarith
  have hrltpi : r < Real.pi := lt_of_lt_of_le hrltR hRlepi
  let a : Circle := Circle.exp (-r)
  let b : Circle := Circle.exp r
  have hnegRlower : -Real.pi < -r := by
    linarith
  have hnegRupper : -r ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hposRlower : -Real.pi < r := by
    linarith [Real.pi_pos]
  have harga : a.val.arg = -r := by
    dsimp [a]
    exact Circle.arg_exp hnegRlower hnegRupper
  have hargb : b.val.arg = r := by
    dsimp [b]
    exact Circle.arg_exp hposRlower hrltpi.le
  have habArg : a.val.arg ≤ b.val.arg := by
    rw [harga, hargb]
    linarith
  have hab : a ≠ b := by
    intro hab
    have hargs := congrArg (fun v : Circle ↦ v.val.arg) hab
    rw [harga, hargb] at hargs
    linarith
  have hangle : Circle.angleDiff a b = 2 * r := by
    rw [Circle.angleDiff, if_pos habArg, harga, hargb]
    ring
  have hsmallPath : Set.range (Circle.path a b) ⊆ Circle.centeredArc R := by
    rw [Circle.range_path]
    rintro y ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    rw [harga, hangle] at ht
    rcases ht with ⟨htl, htr⟩
    have htAbs : |t| < R := by
      rw [abs_lt]
      constructor
      · linarith
      · linarith
    exact htAbs
  let A₁ : Set X := Set.range (g ∘ Circle.path a b)
  let A₂ : Set X := Set.range (g ∘ Circle.path b a)
  have hpath₁Continuous : Continuous (g ∘ Circle.path a b) :=
    hgContinuous.comp (Circle.path a b).continuous
  have hpath₂Continuous : Continuous (g ∘ Circle.path b a) :=
    hgContinuous.comp (Circle.path b a).continuous
  have hpath₁Injective : Function.Injective (g ∘ Circle.path a b) :=
    hgInjective.comp (Circle.path_injective_of_ne hab)
  have hpath₂Injective : Function.Injective (g ∘ Circle.path b a) :=
    hgInjective.comp (Circle.path_injective_of_ne hab.symm)
  have hA₁Arc : Topology.IsArc A₁ := by
    let embedding : Topology.IsEmbedding (g ∘ Circle.path a b) :=
      hpath₁Continuous.isClosedEmbedding hpath₁Injective |>.isEmbedding
    exact ⟨⟨embedding.toHomeomorph.symm⟩⟩
  have hA₂Arc : Topology.IsArc A₂ := by
    let embedding : Topology.IsEmbedding (g ∘ Circle.path b a) :=
      hpath₂Continuous.isClosedEmbedding hpath₂Injective |>.isEmbedding
    exact ⟨⟨embedding.toHomeomorph.symm⟩⟩
  have hRange : Set.range g = C := by
    apply Set.Subset.antisymm
    · rintro y ⟨v, rfl⟩
      exact (e.symm (rotation v)).property
    · intro y hy
      let yC : C := ⟨y, hy⟩
      refine ⟨rotation.symm (e yC), ?_⟩
      simp [g, f, yC]
  have hA₁image : A₁ = g '' Set.range (Circle.path a b) := by
    simp [A₁, Set.range_comp]
  have hA₂image : A₂ = g '' Set.range (Circle.path b a) := by
    simp [A₂, Set.range_comp]
  have hUnion : C = A₁ ∪ A₂ := by
    rw [hA₁image, hA₂image, ← Set.image_union,
      Circle.range_path_union_range_path hab, Set.image_univ]
    exact hRange.symm
  have hA₁N : A₁ ⊆ N := by
    rintro y ⟨t, rfl⟩
    exact hcentered (hsmallPath ⟨t, rfl⟩)
  exact ⟨A₁, A₂, hA₁Arc, hA₂Arc, hUnion, hA₁N⟩

/-- Helper for Theorem 63.4: the complement of a spherical arc is
path-connected. -/
private lemma isPathConnected_compl_of_isArc
    (A : Set (StandardSphere 2)) [Topology.IsArc A]
    (a : StandardSphere 2) (ha : a ∈ Aᶜ) : IsPathConnected Aᶜ := by
  -- Arc nonseparation gives preconnectedness, and openness upgrades it to paths.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hgeometry := isClosed_and_isConnected_of_isArc A
  have hpreconnectedSpace : PreconnectedSpace (Aᶜ : Set (StandardSphere 2)) := by
    have hnonseparating := arc_not_separates A
    rw [Set.separates_iff] at hnonseparating
    exact not_not.mp hnonseparating
  have hpreconnected : IsPreconnected Aᶜ :=
    isPreconnected_iff_preconnectedSpace.mpr hpreconnectedSpace
  have hconnected : IsConnected Aᶜ := ⟨⟨a, ha⟩, hpreconnected⟩
  exact (hgeometry.1.isOpen_compl.isConnected_iff_isPathConnected).mp hconnected

/-- Theorem 63.4 (2): Every component of the complement of a simple
closed curve in the standard two-sphere has the curve as its frontier. -/
theorem jordanCurveSphere_frontier_component
    (C : Set (StandardSphere 2))
    [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (StandardSphere 2))) :
    frontier (connectedComponentIn Cᶜ x) = C := by
  classical
  let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ x
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  -- The easy inclusion follows because complementary components are open.
  have hCclosed : IsClosed C :=
    (isCompact_of_isSimpleClosedCurve_standardSphere C).isClosed
  apply Set.Subset.antisymm
  · exact frontierConnectedComponentInComplement_subset C hCclosed x
  -- For the reverse inclusion, connect the two components while avoiding a
  -- large arc; the crossing point must lie in the prescribed small arc.
  obtain ⟨b, hbU⟩ := exists_complementPoint_not_mem_component C x
  intro z hzC
  apply isClosed_frontier.closure_subset
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨A₁, A₂, hA₁Arc, hA₂Arc, hUnion, hA₁N⟩ :=
    existsTwoArcDecomposition_first_subset_nhds C hzC hN
  letI : Topology.IsArc A₁ := hA₁Arc
  letI : Topology.IsArc A₂ := hA₂Arc
  have hA₂C : A₂ ⊆ C := by
    rw [hUnion]
    exact subset_union_right
  have hxA₂ : (x : StandardSphere 2) ∈ A₂ᶜ := by
    intro hxA₂
    exact x.property (hA₂C hxA₂)
  have hbA₂ : (b : StandardSphere 2) ∈ A₂ᶜ := by
    intro hbA₂
    exact b.property (hA₂C hbA₂)
  have hpathConnected := isPathConnected_compl_of_isArc A₂ x hxA₂
  have hjoined : JoinedIn A₂ᶜ (x : StandardSphere 2) (b : StandardSphere 2) :=
    hpathConnected.joinedIn x hxA₂ b hbA₂
  let gamma : Path (x : StandardSphere 2) (b : StandardSphere 2) := hjoined.somePath
  let S : Set (StandardSphere 2) := Set.range gamma
  have hSconnected : IsConnected S := isConnected_range gamma.continuous
  have hSU : (S ∩ U).Nonempty :=
    ⟨x, gamma.source_mem_range, mem_connectedComponentIn x.property⟩
  have hSUcompl : (S ∩ Uᶜ).Nonempty :=
    ⟨b, gamma.target_mem_range, hbU⟩
  obtain ⟨y, hyS, hyFrontier⟩ :=
    hSconnected.inter_frontier_nonempty hSU hSUcompl
  have hyA₂ : y ∈ A₂ᶜ := by
    obtain ⟨t, rfl⟩ := hyS
    exact hjoined.somePath_mem t
  have hyC : y ∈ C :=
    frontierConnectedComponentInComplement_subset C hCclosed x hyFrontier
  have hyA₁ : y ∈ A₁ := by
    rw [hUnion] at hyC
    exact hyC.resolve_right hyA₂
  exact ⟨y, hA₁N hyA₁, hyFrontier⟩
