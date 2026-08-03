module

public import Topology_Munkres_2000.Book.Theorem_61_4
public import Topology_Munkres_2000.Book.Theorem_63_1
public import Topology_Munkres_2000.Book.Exercise_58_2
public import Topology_Munkres_2000.Book.Example_53_6.Polar
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Mathlib.SetTheory.Cardinal.Basic

public section

open Set

/-- Helper for Theorem 63.5: the two points in an intersection equal to `{p, q}`
belong to each of the intersecting sets. -/
private lemma pair_mem_of_inter_eq_pair
    {X : Type*} {C₁ C₂ : Set X} {p q : X} (hinter : C₁ ∩ C₂ = {p, q}) :
    p ∈ C₁ ∧ p ∈ C₂ ∧ q ∈ C₁ ∧ q ∈ C₂ := by
  -- Rewrite membership in the two-point set through the stated intersection equality.
  have hp : p ∈ C₁ ∩ C₂ := by
    rw [hinter]
    simp
  have hq : q ∈ C₁ ∩ C₂ := by
    rw [hinter]
    simp
  exact ⟨hp.1, hp.2, hq.1, hq.2⟩

/-- Helper for Theorem 63.5: inside the twice-punctured space, the complements
of two sets meeting in exactly the punctures cover the whole space. -/
private lemma pairComplement_preimage_compl_union_eq_univ
    {X : Type*} (C₁ C₂ : Set X) (p q : X) (hinter : C₁ ∩ C₂ = {p, q}) :
    (Subtype.val ⁻¹' C₁ᶜ : Set ({p, q}ᶜ : Set X)) ∪
        Subtype.val ⁻¹' C₂ᶜ = Set.univ := by
  -- A point outside `{p, q}` cannot belong to both sets.
  ext x
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_contra h
  push Not at h
  have hx : x.1 ∈ C₁ ∩ C₂ := ⟨h.1, h.2⟩
  rw [hinter] at hx
  exact x.2 hx

/-- Helper for Theorem 63.5: the overlap of the two complement preimages is
the preimage of the complement of their union. -/
private lemma pairComplement_preimage_compl_inter
    {X : Type*} (C₁ C₂ : Set X) (p q : X) :
    (Subtype.val ⁻¹' C₁ᶜ : Set ({p, q}ᶜ : Set X)) ∩
        Subtype.val ⁻¹' C₂ᶜ = Subtype.val ⁻¹' (C₁ ∪ C₂)ᶜ := by
  -- Membership on both sides is the same pair of negated membership statements.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_union,
    not_or]

/-- Helper for Theorem 63.5: separation and an upper bound of two complementary
components force exactly two complementary components. -/
private lemma separatesInto_two_of_separates_of_components_le_two
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hsep : A.Separates)
    (hle : Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) ≤ 2) :
    A.SeparatesInto 2 := by
  -- The upper bound is an equality because separation rules out at most one component.
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
  have hpre : PreconnectedSpace (Aᶜ : Set X) :=
    preconnectedSpace_iff_connectedComponent.mpr (fun x ↦ by
      apply eq_univ_of_forall
      intro y
      rw [← connectedComponent_eq_iff_mem]
      exact ConnectedComponents.coe_eq_coe.mp
        (@Subsingleton.elim _ hsub (y : ConnectedComponents _) (x : ConnectedComponents _)))
  exact (Set.separates_iff.mp hsep) hpre

/-- Helper for Theorem 63.5: a nonseparating closed complement remains path-joinable
after restricting to a sphere with two points removed from the closed set. -/
private lemma joinedIn_preimage_compl_pairComplement
    (D : Set (StandardSphere 2)) (hDclosed : IsClosed D)
    (p q : StandardSphere 2) (hp : p ∈ D) (hq : q ∈ D)
    (hDnonseparating : ¬ D.Separates)
    (a b : ({p, q}ᶜ : Set (StandardSphere 2)))
    (ha : a.1 ∈ Dᶜ) (hb : b.1 ∈ Dᶜ) :
    JoinedIn (Subtype.val ⁻¹' Dᶜ) a b := by
  -- Place the complement in the stereographic chart centered at a point of `D`.
  have hDcompl_subset_puncture : Dᶜ ⊆ ({p}ᶜ : Set (StandardSphere 2)) := by
    intro x hxD hxp
    exact hxD (hxp ▸ hp)
  let chart := StandardSphere.puncturedHomeomorphPlane p
  let chartDomain : Set ({p}ᶜ : Set (StandardSphere 2)) := Subtype.val ⁻¹' Dᶜ
  have hchartDomain_image : ((fun x ↦ x.1) '' chartDomain) = Dᶜ := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hDcompl_subset_puncture]
  have hchartDomain_open : IsOpen chartDomain := by
    exact hDclosed.isOpen_compl.preimage continuous_subtype_val
  have hchartDomain_nonempty : chartDomain.Nonempty := by
    refine ⟨⟨a.1, hDcompl_subset_puncture ha⟩, ha⟩
  -- Nonseparation supplies connectedness, and the Euclidean chart upgrades it to paths.
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
  -- Lift the resulting sphere path to the twice-punctured subtype using `p, q ∈ D`.
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

/-- Helper for Theorem 63.5: more than two connected components admit three
representatives whose component classes are pairwise distinct. -/
private lemma exists_three_componentRepresentatives_of_not_le_two
    {W : Type*} [TopologicalSpace W]
    (hnot : ¬ Cardinal.mk (ConnectedComponents W) ≤ 2) :
    ∃ a a' b : W,
      (a : ConnectedComponents W) ≠ a' ∧
      (a : ConnectedComponents W) ≠ b ∧
      (a' : ConnectedComponents W) ≠ b := by
  -- Convert failure of the upper bound into an embedding of `Fin 3` into the quotient.
  have hthree : (3 : Cardinal) ≤ Cardinal.mk (ConnectedComponents W) := by
    convert Cardinal.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot) using 1 <;> norm_num
  obtain ⟨componentEmbedding⟩ : Nonempty (Fin 3 ↪ ConnectedComponents W) := by
    apply Cardinal.lift_mk_le'.mp
    simpa using hthree
  -- Lift the three embedded quotient points to representatives in the original space.
  obtain ⟨a, ha⟩ := ConnectedComponents.surjective_coe (componentEmbedding 0)
  obtain ⟨a', ha'⟩ := ConnectedComponents.surjective_coe (componentEmbedding 1)
  obtain ⟨b, hb⟩ := ConnectedComponents.surjective_coe (componentEmbedding 2)
  refine ⟨a, a', b, ?_, ?_, ?_⟩
  · rw [ha, ha']
    exact componentEmbedding.injective.ne (by decide)
  · rw [ha, hb]
    exact componentEmbedding.injective.ne (by decide)
  · rw [ha', hb]
    exact componentEmbedding.injective.ne (by decide)

/-- Helper for Theorem 63.5: an open cover with path access through both sets and
infinite-cyclic fundamental group has at most two overlap components. -/
private lemma mk_connectedComponents_inter_le_two_of_crossingCover
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [LocallyConnectedSpace (U ∩ V : Set X)]
    (hjoinedU : ∀ x y : (U ∩ V : Set X), JoinedIn U x.1 y.1)
    (hjoinedV : ∀ x y : (U ∩ V : Set X), JoinedIn V x.1 y.1)
    (hfundamental : ∀ x : (U ∩ V : Set X),
      Nonempty (FundamentalGroup X x.1 ≃* Multiplicative ℤ)) :
    Cardinal.mk (ConnectedComponents (U ∩ V : Set X)) ≤ 2 := by
  -- Three overlap components would supply the two incompatible crossing generators.
  by_contra hnot
  obtain ⟨a, a', b, haa', hab, ha'b⟩ :=
    exists_three_componentRepresentatives_of_not_le_two hnot
  let A₀ : Set (U ∩ V : Set X) := connectedComponent a ∪ connectedComponent a'
  let B₀ : Set (U ∩ V : Set X) := A₀ᶜ
  let A₁ : Set (U ∩ V : Set X) := connectedComponent a
  let B₁ : Set (U ∩ V : Set X) := A₁ᶜ
  let A : Set X := Subtype.val '' A₀
  let B : Set X := Subtype.val '' B₀
  let A' : Set X := Subtype.val '' A₁
  let B' : Set X := Subtype.val '' B₁
  -- Local connectedness makes all selected component pieces open in the ambient cover.
  have hA₀open : IsOpen A₀ :=
    (isOpen_connectedComponent.union isOpen_connectedComponent)
  have hB₀open : IsOpen B₀ :=
    (isClosed_connectedComponent.union isClosed_connectedComponent).isOpen_compl
  have hA₁open : IsOpen A₁ := isOpen_connectedComponent
  have hB₁open : IsOpen B₁ := isClosed_connectedComponent.isOpen_compl
  have hAopen : IsOpen A := hU.inter hV |>.isOpenMap_subtype_val A₀ hA₀open
  have hBopen : IsOpen B := hU.inter hV |>.isOpenMap_subtype_val B₀ hB₀open
  have hA'open : IsOpen A' := hU.inter hV |>.isOpenMap_subtype_val A₁ hA₁open
  have hB'open : IsOpen B' := hU.inter hV |>.isOpenMap_subtype_val B₁ hB₁open
  have hoverlap : U ∩ V = A ∪ B := by
    ext x
    constructor
    · intro hx
      let y : (U ∩ V : Set X) := ⟨x, hx⟩
      by_cases hy : y ∈ A₀
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
    · rintro (⟨y, -, rfl⟩ | ⟨y, -, rfl⟩) <;> exact y.2
  have hoverlap' : U ∩ V = A' ∪ B' := by
    ext x
    constructor
    · intro hx
      let y : (U ∩ V : Set X) := ⟨x, hx⟩
      by_cases hy : y ∈ A₁
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
    · rintro (⟨y, -, rfl⟩ | ⟨y, -, rfl⟩) <;> exact y.2
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.2
    rintro x ⟨y, hyA, rfl⟩ ⟨z, hzB, hzy⟩
    have hyz : y = z := Subtype.ext hzy.symm
    exact hzB (hyz ▸ hyA)
  have hA'B' : Disjoint A' B' := by
    apply Set.disjoint_left.2
    rintro x ⟨y, hyA, rfl⟩ ⟨z, hzB, hzy⟩
    have hyz : y = z := Subtype.ext hzy.symm
    exact hzB (hyz ▸ hyA)
  -- The three representatives occupy the required sides of both partitions.
  have haA : a.1 ∈ A := ⟨a, Or.inl mem_connectedComponent, rfl⟩
  have ha'A : a'.1 ∈ A := ⟨a', Or.inr mem_connectedComponent, rfl⟩
  have hbB : b.1 ∈ B := by
    refine ⟨b, ?_, rfl⟩
    intro hbA
    rcases hbA with hbca | hbca'
    · exact hab (ConnectedComponents.coe_eq_coe.mpr
        ((connectedComponent_eq_iff_mem.mpr hbca).symm))
    · exact ha'b (ConnectedComponents.coe_eq_coe.mpr
        ((connectedComponent_eq_iff_mem.mpr hbca').symm))
  have haA' : a.1 ∈ A' := ⟨a, mem_connectedComponent, rfl⟩
  have ha'B' : a'.1 ∈ B' := by
    refine ⟨a', ?_, rfl⟩
    intro ha'ca
    exact haa' (ConnectedComponents.coe_eq_coe.mpr
      ((connectedComponent_eq_iff_mem.mpr ha'ca).symm))
  -- Choose the four paths supplied by the two path-access hypotheses.
  let α : Path a.1 b.1 := (hjoinedU a b).somePath
  let β : Path b.1 a.1 := (hjoinedV b a).somePath
  let γ : Path a.1 a'.1 := (hjoinedU a a').somePath
  let δ : Path a'.1 a.1 := (hjoinedV a' a).somePath
  obtain ⟨fundamentalEquiv⟩ := hfundamental a
  letI : Infinite (FundamentalGroup X a.1) :=
    fundamentalEquiv.toEquiv.infinite_iff.mpr inferInstance
  letI : IsCyclic (FundamentalGroup X a.1) :=
    fundamentalEquiv.isCyclic.mpr inferInstance
  have hαtop :
      Subgroup.zpowers (FundamentalGroup.fromPath (.mk (α.trans β))) = ⊤ := by
    exact crossingLoopClass_zpowers_eq_top U V A B α β hU hV hAopen hBopen
      hcover hoverlap hAB haA hbB
      (fun t ↦ (hjoinedU a b).somePath_mem t)
      (fun t ↦ (hjoinedV b a).somePath_mem t)
  have hγtop :
      Subgroup.zpowers (FundamentalGroup.fromPath (.mk (γ.trans δ))) = ⊤ := by
    exact crossingLoopClass_zpowers_eq_top U V A' B' γ δ hU hV hA'open hB'open
      hcover hoverlap' hA'B' haA' ha'B'
      (fun t ↦ (hjoinedU a a').somePath_mem t)
      (fun t ↦ (hjoinedV a' a).somePath_mem t)
  have hdisjoint := crossingLoopClasses_disjoint U V A B α β γ δ hU hV hAopen hBopen
    hcover hoverlap hAB haA hbB ha'A
    (fun t ↦ (hjoinedU a b).somePath_mem t)
    (fun t ↦ (hjoinedV b a).somePath_mem t)
    (fun t ↦ (hjoinedU a a').somePath_mem t)
    (fun t ↦ (hjoinedV a' a).somePath_mem t)
  -- Both generated subgroups are top, contradicting their disjointness in an infinite group.
  rw [hαtop, hγtop] at hdisjoint
  simpa using hdisjoint

/-- Helper for Theorem 63.5: forgetting the second puncture gives the nested
punctured-sphere point used by the stereographic chart. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Theorem 63.5: flattening the nested puncture recovers a point
outside the two-point set. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Theorem 63.5: the nested-puncture map is continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Build continuity through the two successive subtype constructors.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩ : ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Theorem 63.5: flattening the nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- Both subtype projections are continuous, and the membership proof is propositional.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Theorem 63.5: flattening after nesting fixes each pair-complement point. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Equality of subtype values suffices because membership proofs are irrelevant.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 63.5: nesting after flattening fixes each nested point. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Equality of the underlying sphere points determines the nested subtype value.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 63.5: the two-point complement is canonically the
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

/-- Helper for Theorem 63.5: the second puncture belongs to the chart centered
at the first puncture. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Membership is exactly the reversed distinctness assumption.
  simpa using hpq.symm

/-- Helper for Theorem 63.5: stereographic coordinates followed by the standard
Euclidean-complex identification. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (StandardSphere.puncturedHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Theorem 63.5: translate stereographic coordinates so the second
puncture is sent to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Theorem 63.5: the translated chart is nonzero exactly away from
the second puncture. -/
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

/-- Helper for Theorem 63.5: stereographic projection and translation identify
the twice-punctured sphere with the punctured complex plane. -/
private noncomputable def twicePuncturedSphereHomeomorphPuncturedComplexPlane
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Helper for Theorem 63.5: a homeomorphism maps each connected component onto
the connected component of the image point. -/
private lemma image_connectedComponent_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    e '' connectedComponent x = connectedComponent (e x) := by
  -- Continuity gives one inclusion; apply the inverse homeomorphism for the other.
  apply Set.Subset.antisymm
  · exact e.continuous.image_connectedComponent_subset x
  · intro y hy
    have hmem : e.symm y ∈ connectedComponent (e.symm (e x)) :=
      e.symm.continuous.image_connectedComponent_subset (e x) ⟨y, hy, rfl⟩
    exact ⟨e.symm y, by simpa using hmem, e.apply_symm_apply y⟩

/-- Helper for Theorem 63.5: homeomorphic spaces have equivalent connected-component
quotients. -/
private noncomputable def connectedComponentsEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y :=
  { toFun := Quotient.map e fun x y hxy ↦ by
      change connectedComponent x = connectedComponent y at hxy
      change connectedComponent (e x) = connectedComponent (e y)
      rw [← image_connectedComponent_eq e x, ← image_connectedComponent_eq e y, hxy]
    invFun := Quotient.map e.symm fun x y hxy ↦ by
      change connectedComponent x = connectedComponent y at hxy
      change connectedComponent (e.symm x) = connectedComponent (e.symm y)
      rw [← image_connectedComponent_eq e.symm x,
        ← image_connectedComponent_eq e.symm y, hxy]
    left_inv := fun q ↦ Quotient.inductionOn q fun x ↦ Quotient.sound (by
      change connectedComponent (e.symm (e x)) = connectedComponent x
      simp)
    right_inv := fun q ↦ Quotient.inductionOn q fun x ↦ Quotient.sound (by
      change connectedComponent (e (e.symm x)) = connectedComponent x
      simp) }

/-- Helper for Theorem 63.5: an included subtype cut out inside a larger subtype
is homeomorphic to the same set viewed in the ambient space. -/
private def nestedSubtypeHomeomorph
    {X : Type*} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := fun x ↦ Subtype.ext rfl
    right_inv := fun x ↦ Subtype.ext rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2
    continuous_invFun := (continuous_subtype_val.subtype_mk fun x ↦ hSP x.2).subtype_mk fun x ↦ x.2 }

/-- Helper for Theorem 63.5: polar and exponential coordinates identify the
punctured complex plane with the infinite cylinder. -/
private noncomputable def puncturedComplexPlaneHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- Helper for Theorem 63.5: the punctured complex plane has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroup_puncturedComplexPlane_equiv_int
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Transport the known cylinder calculation through polar and logarithmic coordinates.
  let e := puncturedComplexPlaneHomeomorphInfiniteCylinder
  exact ⟨(e.fundamentalGroupMulEquiv z).trans
    (fundamentalGroup_infiniteCylinder (e z)).some⟩

/-- Helper for Theorem 63.5: the twice-punctured sphere has infinite-cyclic
fundamental group at every basepoint. -/
private lemma fundamentalGroup_twicePuncturedSphere_equiv_int
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- Transport first to the punctured plane, then use the cylinder calculation.
  let e := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  exact ⟨(e.fundamentalGroupMulEquiv x).trans
    (fundamentalGroup_puncturedComplexPlane_equiv_int (e x)).some⟩

/-- Helper for Theorem 63.5: the complement of the union has at most two
connected components under the theorem's nonseparation hypotheses. -/
private lemma mk_connectedComponents_compl_union_le_two
    (C₁ C₂ : Set (StandardSphere 2))
    (hC₁closed : IsClosed C₁) (hC₂closed : IsClosed C₂)
    (p q : StandardSphere 2) (hpq : p ≠ q) (hinter : C₁ ∩ C₂ = {p, q})
    (hC₁nonseparating : ¬ C₁.Separates)
    (hC₂nonseparating : ¬ C₂.Separates) :
    Cardinal.mk (ConnectedComponents ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) ≤ 2 := by
  -- Work in the twice-punctured sphere and use the two complement preimages as the cover.
  have hpq_mem := pair_mem_of_inter_eq_pair hinter
  let P : Set (StandardSphere 2) := {p, q}ᶜ
  let U : Set P := Subtype.val ⁻¹' C₁ᶜ
  let V : Set P := Subtype.val ⁻¹' C₂ᶜ
  let W : Set (StandardSphere 2) := (C₁ ∪ C₂)ᶜ
  have hUopen : IsOpen U := hC₁closed.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen V := hC₂closed.isOpen_compl.preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ := by
    exact pairComplement_preimage_compl_union_eq_univ C₁ C₂ p q hinter
  have hWinter : U ∩ V = Subtype.val ⁻¹' W := by
    exact pairComplement_preimage_compl_inter C₁ C₂ p q
  have hWsubset : W ⊆ P := by
    intro x hxW hxpair
    rcases hxpair with hxp | hxq
    · exact hxW (Or.inl (hxp ▸ hpq_mem.1))
    · exact hxW (Or.inl (hxq ▸ hpq_mem.2.2.1))
  let overlapHomeomorph : (U ∩ V : Set P) ≃ₜ W :=
    (Homeomorph.setCongr hWinter).trans (nestedSubtypeHomeomorph P W hWsubset)
  let pairPlane := twicePuncturedSphereHomeomorphPuncturedComplexPlane p q hpq
  let overlapPlane : (U ∩ V : Set P) ≃ₜ
      {z : {z : ℂ // z ≠ 0} // pairPlane.symm z ∈ U ∩ V} :=
    pairPlane.subtype fun x ↦ by simp
  letI : LocallyConnectedSpace {z : ℂ // z ≠ 0} :=
    isClosed_singleton.isOpen_compl.locallyConnectedSpace
  have hoverlapPlaneOpen : IsOpen
      {z : {z : ℂ // z ≠ 0} | pairPlane.symm z ∈ U ∩ V} := by
    exact (hUopen.inter hVopen).preimage pairPlane.symm.continuous
  letI : LocallyConnectedSpace
      {z : {z : ℂ // z ≠ 0} // pairPlane.symm z ∈ U ∩ V} :=
    hoverlapPlaneOpen.locallyConnectedSpace
  letI : LocallyConnectedSpace (U ∩ V : Set P) :=
    overlapPlane.locallyConnectedSpace
  have hjoinedU : ∀ x y : (U ∩ V : Set P), JoinedIn U x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement C₁ hC₁closed p q hpq_mem.1 hpq_mem.2.2.1
      hC₁nonseparating x.1 y.1 x.2.1 y.2.1
  have hjoinedV : ∀ x y : (U ∩ V : Set P), JoinedIn V x.1 y.1 := by
    intro x y
    exact joinedIn_preimage_compl_pairComplement C₂ hC₂closed p q hpq_mem.2.1 hpq_mem.2.2.2
      hC₂nonseparating x.1 y.1 x.2.2 y.2.2
  have hfundamental : ∀ x : (U ∩ V : Set P),
      Nonempty (FundamentalGroup P x.1 ≃* Multiplicative ℤ) := by
    intro x
    exact fundamentalGroup_twicePuncturedSphere_equiv_int p q hpq x.1
  have hinterComponents : Cardinal.mk (ConnectedComponents (U ∩ V : Set P)) ≤ 2 :=
    mk_connectedComponents_inter_le_two_of_crossingCover U V hUopen hVopen hcover
      hjoinedU hjoinedV hfundamental
  -- Transport the component bound from the overlap subtype back to the original complement.
  rw [← Cardinal.mk_congr (connectedComponentsEquivOfHomeomorph overlapHomeomorph)]
  exact hinterComponents

/-- Theorem 63.5: Two closed connected subsets of the standard two-sphere that
meet in exactly two distinct points and are individually nonseparating have a
union that separates the sphere into exactly two components. -/
theorem union_separatesInto_two_of_inter_pair
    (C₁ C₂ : Set (StandardSphere 2))
    (hC₁closed : IsClosed C₁) (hC₂closed : IsClosed C₂)
    (hC₁connected : IsConnected C₁) (hC₂connected : IsConnected C₂)
    (hinter : ∃ p q, p ≠ q ∧ C₁ ∩ C₂ = {p, q})
    (hC₁nonseparating : ¬ C₁.Separates)
    (hC₂nonseparating : ¬ C₂.Separates) :
    (C₁ ∪ C₂).SeparatesInto 2 := by
  -- Choose the two intersection points and separate the lower and upper component bounds.
  obtain ⟨p, q, hpq, hinter⟩ := hinter
  have hpq_mem := pair_mem_of_inter_eq_pair hinter
  have hseparates : (C₁ ∪ C₂).Separates := by
    exact union_separates_of_inter_pair C₁ C₂ p q hpq hinter hC₁closed hC₂closed
      hC₁connected hC₂connected
  have hcomponents :
      Cardinal.mk (ConnectedComponents ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) ≤ 2 := by
    exact mk_connectedComponents_compl_union_le_two C₁ C₂ hC₁closed hC₂closed p q hpq
      hinter hC₁nonseparating hC₂nonseparating
  -- The intersection membership facts record the endpoint side conditions for the crossing proof.
  clear hpq_mem
  exact separatesInto_two_of_separates_of_components_le_two (C₁ ∪ C₂) hseparates hcomponents
