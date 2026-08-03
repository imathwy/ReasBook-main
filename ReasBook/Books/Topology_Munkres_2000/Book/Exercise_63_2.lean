module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_2.Arc
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Definition_55_2.Instances
public import Topology_Munkres_2000.Book.Theorem_63_2
public import Topology_Munkres_2000.Book.Theorem_63_3
public import Topology_Munkres_2000.Book.Theorem_63_5

public section

open Set

universe u

/-- Helper for Exercise 63.2: an arc in a Hausdorff space is closed and connected. -/
private lemma isClosed_isConnected_of_isArc
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (A : Set X) [Topology.IsArc A] : IsClosed A ∧ IsConnected A := by
  classical
  -- Transfer compactness and connectedness from the unit interval model.
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := e.symm.compactSpace
  letI : ConnectedSpace A := e.connectedSpace_iff.mpr inferInstance
  have hcompact : IsCompact A := isCompact_iff_compactSpace.mpr inferInstance
  exact ⟨hcompact.isClosed, isConnected_iff_connectedSpace.mpr inferInstance⟩

/-- Helper for Exercise 63.2: the interior-point set of an arc is connected. -/
private lemma isConnected_arcInteriorPoints
    {X : Type u} [TopologicalSpace X] (A : Set X) [Topology.IsArc A] :
    IsConnected {x : A | Topology.IsArc.IsInteriorPoint x} := by
  -- Arc coordinates identify the interior-point set with the open unit interval.
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  have hinterior : {x : A | Topology.IsArc.IsInteriorPoint x} =
      e ⁻¹' Ioo (0 : unitInterval) 1 := by
    ext x
    rw [mem_setOf_eq, mem_preimage, Topology.IsArc.isInteriorPoint_iff e]
    constructor
    · intro h
      have hzero : e x ≠ 0 := by
        intro hx
        exact h.1 (e.toEquiv.apply_eq_iff_eq_symm_apply.mp hx)
      have hone : e x ≠ 1 := by
        intro hx
        exact h.2 (e.toEquiv.apply_eq_iff_eq_symm_apply.mp hx)
      exact ⟨unitInterval.pos_iff_ne_zero.mpr hzero,
        unitInterval.lt_one_iff_ne_one.mpr hone⟩
    · intro h
      constructor
      · intro hx
        have hzero : e x = 0 := by
          simpa only [e.apply_symm_apply] using congrArg e hx
        exact (unitInterval.pos_iff_ne_zero.mp h.1) hzero
      · intro hx
        have hone : e x = 1 := by
          simpa only [e.apply_symm_apply] using congrArg e hx
        exact (unitInterval.lt_one_iff_ne_one.mp h.2) hone
  rw [hinterior]
  exact e.isConnected_preimage.mpr (isConnected_Ioo zero_lt_one)

/-- Helper for Exercise 63.2: arc coordinates identify the ambient endpoint image
with the pair of coordinate endpoints. -/
private lemma endpointImage_eq_pair
    {X : Type u} [TopologicalSpace X] (A : Set X) [Topology.IsArc A]
    (e : A ≃ₜ unitInterval) :
    Subtype.val '' {x : A | Topology.IsArc.IsEndpoint x} =
      {(e.symm 0 : A).1, (e.symm 1 : A).1} := by
  -- Rewrite intrinsic endpoint membership through the chosen arc coordinates.
  ext x
  simp only [mem_image, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Topology.IsArc.isEndpoint_iff e] at hy
    exact hy.imp (congrArg Subtype.val) (congrArg Subtype.val)
  · rintro (hx | hx)
    · refine ⟨e.symm 0, ?_, hx.symm⟩
      rw [Topology.IsArc.isEndpoint_iff e]
      exact Or.inl rfl
    · refine ⟨e.symm 1, ?_, hx.symm⟩
      rw [Topology.IsArc.isEndpoint_iff e]
      exact Or.inr rfl

/-- Helper for Exercise 63.2: a subset viewed inside a containing subtype is
homeomorphic to the same subset in the ambient space. -/
private def nestedSubtypeHomeomorph
    {X : Type u} [TopologicalSpace X] (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Subtype.ext rfl
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk fun x ↦ hSP x.2).subtype_mk fun x ↦ x.2 }

/-- Helper for Exercise 63.2: homeomorphic spaces have equally many connected components. -/
private lemma mk_connectedComponents_eq_of_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Cardinal.mk (ConnectedComponents X) = Cardinal.mk (ConnectedComponents Y) := by
  -- Pass the homeomorphism through the connected-component quotient.
  let eComponents := e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y ↦ e.isConnected_preimage.mpr (isConnected_singleton : IsConnected ({y} : Set Y)))
  exact Cardinal.mk_congr eComponents.toEquiv

/-- Helper for Exercise 63.2: a clopen subset splits the connected-component
cardinal into the contributions from it and its complement. -/
private lemma mk_connectedComponents_eq_add_compl_of_isClopen
    {X : Type u} [TopologicalSpace X] (U : Set X) (hU : IsClopen U) :
    Cardinal.mk (ConnectedComponents X) =
      Cardinal.mk (ConnectedComponents U) + Cardinal.mk (ConnectedComponents (Uᶜ : Set X)) := by
  classical
  -- Use the canonical Bool-indexed clopen partition and flatten its sigma type.
  let P : Bool → Set X := fun b ↦ bif b then Uᶜ else U
  have hPclopen : ∀ b, IsClopen (P b) := by
    intro b
    cases b with
    | false =>
      simpa only [P, Bool.cond_false] using hU
    | true =>
      simpa only [P, Bool.cond_true] using hU.compl
  have hPdisjoint : Pairwise (fun b c ↦ Disjoint (P b) (P c)) := by
    intro b c hbc
    cases b with
    | false =>
      cases c with
      | false => exact (hbc rfl).elim
      | true => exact disjoint_compl_right
    | true =>
      cases c with
      | false => exact disjoint_compl_left
      | true => exact (hbc rfl).elim
  have hPcover : ⋃ b, P b = Set.univ := by
    ext x
    by_cases hx : x ∈ U
    · simp [P, hx]
    · simp [P, hx]
  have eFiber (b : Bool) : ConnectedComponents (P b) ≃
      bif b then ConnectedComponents (Uᶜ : Set X) else ConnectedComponents U := by
    cases b with
    | false => exact Equiv.refl _
    | true => exact Equiv.refl _
  let eBool : (Σ b, ConnectedComponents (P b)) ≃
      ConnectedComponents U ⊕ ConnectedComponents (Uᶜ : Set X) := by
    exact (Equiv.sigmaCongrRight eFiber).trans
      (Equiv.sumEquivSigmaBool
        (ConnectedComponents U) (ConnectedComponents (Uᶜ : Set X))).symm
  let e : ConnectedComponents X ≃
      ConnectedComponents U ⊕ ConnectedComponents (Uᶜ : Set X) :=
    (ConnectedComponents.equivOfIsClopen hPclopen hPdisjoint hPcover).trans eBool
  simpa only [Cardinal.mk_sum, Cardinal.lift_id] using Cardinal.mk_congr e

/-- Helper for Exercise 63.2: a nonempty connected space has one connected component. -/
private lemma mk_connectedComponents_eq_one_of_isConnected
    {X : Type u} [TopologicalSpace X] (U : Set X) (hU : IsConnected U) :
    Cardinal.mk (ConnectedComponents U) = 1 := by
  -- Connectedness supplies the canonical subsingleton and nonempty quotient instances.
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU
  exact Cardinal.mk_eq_one (ConnectedComponents U)

/-- Helper for Exercise 63.2: the exterior of a complementary domain of a
closed connected set in a connected locally connected space is connected. -/
private lemma isConnected_complementaryDomainExterior
    {X : Type u} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    (D : Set X) (hDclosed : IsClosed D) (hDconnected : IsConnected D)
    (a : X) (ha : a ∈ Dᶜ) :
    IsConnected ((connectedComponentIn Dᶜ a)ᶜ) := by
  let W := connectedComponentIn Dᶜ a
  let K := Wᶜ
  have hDopen : IsOpen Dᶜ := hDclosed.isOpen_compl
  have hWopen : IsOpen W := hDopen.connectedComponentIn
  have hKclosed : IsClosed K := hWopen.isClosed_compl
  have hDsubK : D ⊆ K := by
    intro x hxD hxW
    exact (connectedComponentIn_subset Dᶜ a hxW) hxD
  have hforceSide : ∀ {s t : Set X}, IsOpen s → IsOpen t →
      K ⊆ s ∪ t → K ∩ (s ∩ t) = ∅ → D ⊆ s → K ⊆ s := by
    intro s t hsopen htopen hcover hdisjoint hDsub
    by_contra hKsub
    obtain ⟨x, hxK, hxs⟩ := not_subset.mp hKsub
    have hxt : x ∈ t := (hcover hxK).resolve_left hxs
    let S := K ∩ t
    have hSnonempty : S.Nonempty := ⟨x, hxK, hxt⟩
    have hSdisjointD : Disjoint S D := by
      rw [Set.disjoint_left]
      intro z hzS hzD
      have hzInter : z ∈ K ∩ (s ∩ t) := ⟨hzS.1, hDsub hzD, hzS.2⟩
      rw [hdisjoint] at hzInter
      exact hzInter
    have hSeq : S = K ∩ sᶜ := by
      ext z
      constructor
      · intro hz
        refine ⟨hz.1, ?_⟩
        intro hzs
        have hzInter : z ∈ K ∩ (s ∩ t) := ⟨hz.1, hzs, hz.2⟩
        rw [hdisjoint] at hzInter
        exact hzInter
      · intro hz
        exact ⟨hz.1, (hcover hz.1).resolve_left hz.2⟩
    have hSclosed : IsClosed S := by
      rw [hSeq]
      exact hKclosed.inter hsopen.isClosed_compl
    let P : Set (Dᶜ : Set X) := Subtype.val ⁻¹' W
    have hPeq : P = connectedComponent (⟨a, ha⟩ : (Dᶜ : Set X)) := by
      ext z
      simp only [P, W, mem_preimage]
      rw [connectedComponentIn_eq_image ha]
      constructor
      · rintro ⟨y, hy, hyz⟩
        have hyz' : y = z := Subtype.ext hyz
        exact hyz' ▸ hy
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hPclopen : IsClopen P := by
      constructor
      · rw [hPeq]
        exact isClosed_connectedComponent
      · exact hWopen.preimage continuous_subtype_val
    let T : Set (Dᶜ : Set X) := Pᶜ ∩ Subtype.val ⁻¹' t
    have hTopen : IsOpen T :=
      hPclopen.compl.isOpen.inter (htopen.preimage continuous_subtype_val)
    have hTimage : Subtype.val '' T = S := by
      ext z
      constructor
      · rintro ⟨y, hyT, rfl⟩
        exact ⟨hyT.1, hyT.2⟩
      · intro hzS
        have hzDcompl : z ∈ Dᶜ := by
          intro hzD
          exact Set.disjoint_left.mp hSdisjointD hzS hzD
        let zD : (Dᶜ : Set X) := ⟨z, hzDcompl⟩
        have hzP : zD ∉ P := hzS.1
        exact ⟨zD, ⟨hzP, hzS.2⟩, rfl⟩
    have hSopen : IsOpen S := by
      rw [← hTimage]
      exact hDopen.isOpenMap_subtype_val T hTopen
    have hSuniv : S = Set.univ :=
      IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSnonempty
    obtain ⟨d, hdD⟩ := hDconnected.nonempty
    have hdS : d ∈ S := hSuniv.symm ▸ Set.mem_univ d
    exact Set.disjoint_left.mp hSdisjointD hdS hdD
  -- Any relative separation of `K` would put `D` on one side, which the claim
  -- upgrades to all of `K`.
  refine ⟨hDconnected.nonempty.mono hDsubK, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro s t hsopen htopen hcover hdisjoint
  have hDcover : D ⊆ s ∪ t := hDsubK.trans hcover
  have hDdisjoint : D ∩ (s ∩ t) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzInter : z ∈ K ∩ (s ∩ t) := ⟨hDsubK hz.1, hz.2⟩
    rw [hdisjoint] at hzInter
    exact hzInter
  obtain hDs | hDt := (isPreconnected_iff_subset_of_disjoint.mp
    hDconnected.isPreconnected) s t hsopen htopen hDcover hDdisjoint
  · exact Or.inl (hforceSide hsopen htopen hcover hdisjoint hDs)
  · apply Or.inr
    apply hforceSide htopen hsopen
    · simpa only [union_comm] using hcover
    · simpa only [inter_comm s] using hdisjoint
    · exact hDt

/-- Helper for Exercise 63.2: adjoining a set contained, off `D`, in one
complementary domain replaces only that domain's component contribution. -/
private lemma mk_connectedComponents_compl_union_eq_add_remainder
    {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X]
    (D A : Set X) (hDclosed : IsClosed D) (a : X) (ha : a ∈ Dᶜ)
    (hAD : A \ D ⊆ connectedComponentIn Dᶜ a) :
    ∃ κ : Cardinal,
      Cardinal.mk (ConnectedComponents (Dᶜ : Set X)) = 1 + κ ∧
      Cardinal.mk (ConnectedComponents ((D ∪ A)ᶜ : Set X)) =
        Cardinal.mk (ConnectedComponents
          ((((connectedComponentIn Dᶜ a)ᶜ ∪ A)ᶜ : Set X))) + κ := by
  classical
  let W := connectedComponentIn Dᶜ a
  let XD := (Dᶜ : Set X)
  let XY := ((D ∪ A)ᶜ : Set X)
  let U : Set XD := Subtype.val ⁻¹' W
  let V : Set XY := Subtype.val ⁻¹' W
  have hDopen : IsOpen Dᶜ := hDclosed.isOpen_compl
  have hWopen : IsOpen W := hDopen.connectedComponentIn
  have hUeq : U = connectedComponent (⟨a, ha⟩ : XD) := by
    ext z
    simp only [U, W, mem_preimage]
    rw [connectedComponentIn_eq_image ha]
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hyz' : y = z := Subtype.ext hyz
      exact hyz' ▸ hy
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hUclopen : IsClopen U := by
    constructor
    · rw [hUeq]
      exact isClosed_connectedComponent
    · exact hWopen.preimage continuous_subtype_val
  have hXYsubXD : (D ∪ A)ᶜ ⊆ Dᶜ :=
    compl_subset_compl.mpr Set.subset_union_left
  let j : XY → XD := Set.inclusion hXYsubXD
  have hjcontinuous : Continuous j := continuous_inclusion hXYsubXD
  have hVeq : V = j ⁻¹' U := by
    ext z
    rfl
  have hVclopen : IsClopen V := by
    rw [hVeq]
    exact hUclopen.preimage hjcontinuous
  have hWconnected : IsConnected W :=
    isConnected_connectedComponentIn_iff.mpr ha
  have hUconnected : IsConnected U := by
    apply hWconnected.preimage_of_isOpenMap Subtype.val_injective
      hDopen.isOpenMap_subtype_val
    intro x hxW
    exact ⟨⟨x, connectedComponentIn_subset Dᶜ a hxW⟩, rfl⟩
  have hUone : Cardinal.mk (ConnectedComponents U) = 1 :=
    mk_connectedComponents_eq_one_of_isConnected U hUconnected
  have hDsplit : Cardinal.mk (ConnectedComponents XD) =
      Cardinal.mk (ConnectedComponents U) +
        Cardinal.mk (ConnectedComponents (Uᶜ : Set XD)) :=
    mk_connectedComponents_eq_add_compl_of_isClopen U hUclopen
  have hYsplit : Cardinal.mk (ConnectedComponents XY) =
      Cardinal.mk (ConnectedComponents V) +
        Cardinal.mk (ConnectedComponents (Vᶜ : Set XY)) :=
    mk_connectedComponents_eq_add_compl_of_isClopen V hVclopen
  let L := ((Wᶜ ∪ A)ᶜ : Set X)
  have hLsubY : L ⊆ (D ∪ A)ᶜ := by
    intro x hxL hxUnion
    rcases hxUnion with hxD | hxA
    · exact hxL (Or.inl (fun hxW ↦ (connectedComponentIn_subset Dᶜ a hxW) hxD))
    · exact hxL (Or.inr hxA)
  have hVset : V = Subtype.val ⁻¹' L := by
    ext z
    constructor
    · intro hzW hzL
      rcases hzL with hzWc | hzA
      · exact hzWc hzW
      · exact z.2 (Or.inr hzA)
    · intro hzL
      by_contra hzW
      exact hzL (Or.inl hzW)
  let eLocal : V ≃ₜ L :=
    (Homeomorph.setCongr hVset).trans
      (nestedSubtypeHomeomorph (D ∪ A)ᶜ L hLsubY)
  have hLocal : Cardinal.mk (ConnectedComponents V) =
      Cardinal.mk (ConnectedComponents L) :=
    mk_connectedComponents_eq_of_homeomorph eLocal
  let R := (Dᶜ ∩ Wᶜ : Set X)
  have hRsubD : R ⊆ Dᶜ := fun _ hx ↦ hx.1
  have hRsubY : R ⊆ (D ∪ A)ᶜ := by
    intro x hxR hxUnion
    rcases hxUnion with hxD | hxA
    · exact hxR.1 hxD
    · exact hxR.2 (hAD ⟨hxA, hxR.1⟩)
  have hUcomplSet : Uᶜ = Subtype.val ⁻¹' R := by
    ext z
    exact ⟨fun hz ↦ ⟨z.2, hz⟩, fun hz ↦ hz.2⟩
  have hVcomplSet : Vᶜ = Subtype.val ⁻¹' R := by
    ext z
    exact ⟨fun hz ↦ ⟨fun hzD ↦ z.2 (Or.inl hzD), hz⟩,
      fun hz ↦ hz.2⟩
  let eRestD : (Uᶜ : Set XD) ≃ₜ R :=
    (Homeomorph.setCongr hUcomplSet).trans (nestedSubtypeHomeomorph Dᶜ R hRsubD)
  let eRestY : (Vᶜ : Set XY) ≃ₜ R :=
    (Homeomorph.setCongr hVcomplSet).trans
      (nestedSubtypeHomeomorph (D ∪ A)ᶜ R hRsubY)
  have hRestD : Cardinal.mk (ConnectedComponents (Uᶜ : Set XD)) =
      Cardinal.mk (ConnectedComponents R) :=
    mk_connectedComponents_eq_of_homeomorph eRestD
  have hRestY : Cardinal.mk (ConnectedComponents (Vᶜ : Set XY)) =
      Cardinal.mk (ConnectedComponents R) :=
    mk_connectedComponents_eq_of_homeomorph eRestY
  refine ⟨Cardinal.mk (ConnectedComponents (Uᶜ : Set XD)), ?_, ?_⟩
  · calc
      Cardinal.mk (ConnectedComponents (Dᶜ : Set X)) =
          Cardinal.mk (ConnectedComponents U) +
            Cardinal.mk (ConnectedComponents (Uᶜ : Set XD)) :=
        hDsplit
      _ = 1 + Cardinal.mk (ConnectedComponents (Uᶜ : Set XD)) := congrArg
        (fun κ ↦ κ + Cardinal.mk (ConnectedComponents (Uᶜ : Set XD))) hUone
  · calc
      Cardinal.mk (ConnectedComponents ((D ∪ A)ᶜ : Set X)) =
          Cardinal.mk (ConnectedComponents V) +
            Cardinal.mk (ConnectedComponents (Vᶜ : Set XY)) :=
        hYsplit
      _ = Cardinal.mk (ConnectedComponents L) + Cardinal.mk (ConnectedComponents R) :=
        congrArg₂ (fun κ μ : Cardinal ↦ κ + μ) hLocal hRestY
      _ = Cardinal.mk (ConnectedComponents L) +
          Cardinal.mk (ConnectedComponents (Uᶜ : Set XD)) :=
        congrArg (fun κ ↦ Cardinal.mk (ConnectedComponents L) + κ) hRestD.symm

/-- Helper for Exercise 63.2: a set with connected complement does not separate. -/
private lemma compl_not_separates_of_isConnected
    {X : Type u} [TopologicalSpace X] (U : Set X) (hU : IsConnected U) :
    ¬ Uᶜ.Separates := by
  -- Separation would negate the preconnected-space structure supplied by `hU`.
  intro hseparates
  rw [Set.separates_iff, compl_compl] at hseparates
  exact hseparates (isPreconnected_iff_preconnectedSpace.mp hU.isPreconnected)

/-- Helper for Exercise 63.2: a once-punctured standard two-sphere is simply connected. -/
private lemma puncturedStandardSphere_isSimplyConnected (p : StandardSphere 2) :
    IsSimplyConnected (({p} : Set (StandardSphere 2))ᶜ) := by
  -- Stereographic projection transports the simply connected Euclidean plane.
  let chart := StandardSphere.puncturedHomeomorphPlane p
  exact chart.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance

/-- Helper for Exercise 63.2: `1 / 2` lies in `unitInterval`. -/
private lemma half_mem_unitInterval : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
  -- The midpoint satisfies the two defining inequalities.
  norm_num

/-- Helper for Exercise 63.2: the midpoint of the unit interval. -/
private noncomputable def unitIntervalMidpoint : unitInterval :=
  ⟨1 / 2, half_mem_unitInterval⟩

/-- Helper for Exercise 63.2: the unit-interval midpoint is not the left endpoint. -/
private lemma unitIntervalMidpoint_ne_zero : unitIntervalMidpoint ≠ 0 := by
  -- Equality of subtype values would say `1 / 2 = 0` in `ℝ`.
  intro h
  have hval := congrArg Subtype.val h
  norm_num [unitIntervalMidpoint] at hval

/-- Helper for Exercise 63.2: the unit-interval midpoint is not the right endpoint. -/
private lemma unitIntervalMidpoint_ne_one : unitIntervalMidpoint ≠ 1 := by
  -- Equality of subtype values would say `1 / 2 = 1` in `ℝ`.
  intro h
  have hval := congrArg Subtype.val h
  norm_num [unitIntervalMidpoint] at hval

/-- Helper for Exercise 63.2: an arc cannot be the whole standard two-sphere. -/
private lemma isArc_ne_univ_standardSphere
    (A : Set (StandardSphere 2)) [Topology.IsArc A] : A ≠ Set.univ := by
  -- If the arc filled the sphere, its coordinate midpoint would become an endpoint
  -- because the punctured sphere is connected, contradicting interval coordinates.
  intro hA
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  let hAuniv : A ≃ₜ (Set.univ : Set (StandardSphere 2)) := Homeomorph.setCongr hA
  let hSphere : A ≃ₜ StandardSphere 2 :=
    hAuniv.trans (Homeomorph.Set.univ (StandardSphere 2))
  let m : A := e.symm unitIntervalMidpoint
  have hmConnected : IsConnected (({m} : Set A)ᶜ) := by
    rw [← hSphere.isConnected_image,
      hSphere.image_compl, Set.image_singleton]
    exact (puncturedStandardSphere_isSimplyConnected (hSphere m)).isPathConnected.isConnected
  rw [← e.isConnected_image, e.image_compl, Set.image_singleton,
    unitInterval.isConnected_compl_singleton_iff] at hmConnected
  rcases hmConnected with hm | hm
  · have hmidpoint : unitIntervalMidpoint = 0 := by
      simpa only [m, e.apply_symm_apply] using hm
    exact unitIntervalMidpoint_ne_zero hmidpoint
  · have hmidpoint : unitIntervalMidpoint = 1 := by
      simpa only [m, e.apply_symm_apply] using hm
    exact unitIntervalMidpoint_ne_one hmidpoint

/-- Helper for Exercise 63.2: a circle-like subset splits at a prescribed point
into two arcs whose common points are exactly their endpoint pair. -/
private lemma existsTwoArcDecompositionAt
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.IsSimpleClosedCurve C] (x : X) (hxC : x ∈ C) :
    ∃ A₁ A₂ : Set X, ∃ hA₁Arc : Topology.IsArc A₁,
      ∃ hA₂Arc : Topology.IsArc A₂, ∃ q : X,
      x ≠ q ∧ C = A₁ ∪ A₂ ∧ A₁ ∩ A₂ = {x, q} ∧
      Subtype.val '' {z : A₁ | @Topology.IsArc.IsEndpoint A₁ _ hA₁Arc z} = {x, q} ∧
      Subtype.val '' {z : A₂ | @Topology.IsArc.IsEndpoint A₂ _ hA₂Arc z} = {x, q} := by
  classical
  -- Use the two complementary circle paths from the chosen point to its antipode.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  let xC : C := ⟨x, hxC⟩
  let z : Circle := e xC
  let f : Circle → X := fun w ↦ (e.symm w : X)
  let q : X := f (-z)
  let A₁ : Set X := Set.range (f ∘ Circle.path z (-z))
  let A₂ : Set X := Set.range (f ∘ Circle.path (-z) z)
  have hfContinuous : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hzx : f z = x := by
    simp [f, z, xC]
  have hzneg : z ≠ -z := (Circle.neg_ne_self z).symm
  have hxq : x ≠ q := by
    intro hxq
    exact hzneg (hfInjective (hzx.trans hxq))
  have hpath₁Continuous : Continuous (f ∘ Circle.path z (-z)) :=
    hfContinuous.comp (Circle.path z (-z)).continuous
  have hpath₂Continuous : Continuous (f ∘ Circle.path (-z) z) :=
    hfContinuous.comp (Circle.path (-z) z).continuous
  have hpath₁Injective : Function.Injective (f ∘ Circle.path z (-z)) :=
    hfInjective.comp (Circle.path_injective_of_ne hzneg)
  have hpath₂Injective : Function.Injective (f ∘ Circle.path (-z) z) :=
    hfInjective.comp (Circle.path_injective_of_ne hzneg.symm)
  let embedding₁ : Topology.IsEmbedding (f ∘ Circle.path z (-z)) :=
    hpath₁Continuous.isClosedEmbedding hpath₁Injective |>.isEmbedding
  let embedding₂ : Topology.IsEmbedding (f ∘ Circle.path (-z) z) :=
    hpath₂Continuous.isClosedEmbedding hpath₂Injective |>.isEmbedding
  have hA₁Arc : Topology.IsArc A₁ :=
    ⟨⟨embedding₁.toHomeomorph.symm⟩⟩
  have hA₂Arc : Topology.IsArc A₂ :=
    ⟨⟨embedding₂.toHomeomorph.symm⟩⟩
  have hA₁image : A₁ = f '' Set.range (Circle.path z (-z)) := by
    simp [A₁, Set.range_comp]
  have hA₂image : A₂ = f '' Set.range (Circle.path (-z) z) := by
    simp [A₂, Set.range_comp]
  have hRange : Set.range f = C := by
    apply Set.Subset.antisymm
    · rintro y ⟨w, rfl⟩
      exact (e.symm w).property
    · intro y hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simp [f]
  have hUnion : C = A₁ ∪ A₂ := by
    rw [hA₁image, hA₂image, ← Set.image_union,
      Circle.range_path_union_range_path hzneg, Set.image_univ]
    exact hRange.symm
  have hInter : A₁ ∩ A₂ = {x, q} := by
    rw [hA₁image, hA₂image, ← Set.image_inter hfInjective,
      Circle.range_path_inter_range_path hzneg, Set.image_pair]
    simp only [hzx, q]
  letI : Topology.IsArc A₁ := hA₁Arc
  letI : Topology.IsArc A₂ := hA₂Arc
  have hEndpoints₁ :
      Subtype.val '' {w : A₁ | Topology.IsArc.IsEndpoint w} = {x, q} := by
    have h := endpointImage_eq_pair A₁ embedding₁.toHomeomorph.symm
    rw [Homeomorph.symm_symm, Topology.IsEmbedding.toHomeomorph_apply_coe,
      Topology.IsEmbedding.toHomeomorph_apply_coe, Function.comp_apply,
      Function.comp_apply, Path.source, Path.target] at h
    simpa only [hzx, q] using h
  have hEndpoints₂ :
      Subtype.val '' {w : A₂ | Topology.IsArc.IsEndpoint w} = {x, q} := by
    have h := endpointImage_eq_pair A₂ embedding₂.toHomeomorph.symm
    rw [Homeomorph.symm_symm, Topology.IsEmbedding.toHomeomorph_apply_coe,
      Topology.IsEmbedding.toHomeomorph_apply_coe, Function.comp_apply,
      Function.comp_apply, Path.source, Path.target] at h
    simpa only [hzx, q, pair_comm] using h
  exact ⟨A₁, A₂, hA₁Arc, hA₂Arc, q, hxq, hUnion, hInter,
    hEndpoints₁, hEndpoints₂⟩

/-- Exercise 63.2 (1): Adjoining an arc that meets `D` in one endpoint does not
change the number of complementary components. -/
theorem arcUnion_separatesInto_of_inter_endpoint (n : ℕ)
    (D A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    [Topology.IsArc A]
    (hDclosed : IsClosed D) (hDconnected : IsConnected D)
    (hDseparates : D.SeparatesInto n)
    (hinter : ∃ x : A, Topology.IsArc.IsEndpoint x ∧ D ∩ A = {x.1}) :
    (D ∪ A).SeparatesInto n := by
  classical
  -- The manifold structure supplies local connectedness for complementary domains.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  obtain ⟨x, hxEndpoint, hinter⟩ := hinter
  have hxInter : (x : StandardSphere 2) ∈ D ∩ A := by
    rw [hinter]
    exact Set.mem_singleton x.1
  have hxD : (x : StandardSphere 2) ∈ D := hxInter.1
  have hAgeometry := isClosed_isConnected_of_isArc A
  have hremEq : A \ D =
      Subtype.val '' (({x} : Set A)ᶜ) := by
    ext y
    constructor
    · intro hy
      let yA : A := ⟨y, hy.1⟩
      have hyx : yA ≠ x := by
        intro hyx
        have hyval : y = (x : StandardSphere 2) := congrArg Subtype.val hyx
        exact hy.2 (hyval.symm ▸ hxD)
      exact ⟨yA, hyx, rfl⟩
    · rintro ⟨y, hyx, rfl⟩
      refine ⟨y.2, ?_⟩
      intro hyD
      have hyInter : (y : StandardSphere 2) ∈ D ∩ A := ⟨hyD, y.2⟩
      rw [hinter] at hyInter
      exact hyx (Subtype.ext hyInter)
  have hremConnected : IsConnected (A \ D) := by
    rw [hremEq]
    obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
    have hpuncturedArc : IsConnected (({x} : Set A)ᶜ) := by
      rw [← e.isConnected_image, e.image_compl, Set.image_singleton,
        unitInterval.isConnected_compl_singleton_iff]
      rw [Topology.IsArc.isEndpoint_iff e] at hxEndpoint
      rcases hxEndpoint with hx | hx
      · left
        simp only [hx, e.apply_symm_apply]
      · right
        simp only [hx, e.apply_symm_apply]
    exact hpuncturedArc.image Subtype.val continuous_subtype_val.continuousOn
  obtain ⟨a, haRem⟩ := hremConnected.nonempty
  have haD : a ∈ Dᶜ := haRem.2
  let W := connectedComponentIn Dᶜ a
  let K := Wᶜ
  have hremSubW : A \ D ⊆ W := by
    exact hremConnected.isPreconnected.subset_connectedComponentIn
      haRem (fun _ hy ↦ hy.2)
  have hWconnected : IsConnected W :=
    isConnected_connectedComponentIn_iff.mpr haD
  have hWopen : IsOpen W := hDclosed.isOpen_compl.connectedComponentIn
  have hKclosed : IsClosed K := hWopen.isClosed_compl
  have hKconnected : IsConnected K :=
    isConnected_complementaryDomainExterior D hDclosed hDconnected a haD
  have hKnonseparating : ¬ K.Separates :=
    compl_not_separates_of_isConnected W hWconnected
  have hAnonseparating : ¬ A.Separates := arc_not_separates A
  have hxK : (x : StandardSphere 2) ∈ K := by
    intro hxW
    exact (connectedComponentIn_subset Dᶜ a hxW) hxD
  have hKinterA : K ∩ A = {(x : StandardSphere 2)} := by
    ext y
    constructor
    · intro hy
      have hyD : y ∈ D := by
        by_contra hyD
        exact hy.1 (hremSubW ⟨hy.2, hyD⟩)
      have hyInter : y ∈ D ∩ A := ⟨hyD, hy.2⟩
      rwa [hinter] at hyInter
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ ⟨hxK, x.2⟩
  have hinterSimplyConnected : IsSimplyConnected ((K ∩ A)ᶜ) := by
    rw [hKinterA]
    exact puncturedStandardSphere_isSimplyConnected x
  have hUnionNonseparating : ¬ (K ∪ A).Separates :=
    union_not_separates_of_compl_inter_simplyConnected K A hKclosed hAgeometry.1
      hinterSimplyConnected hKnonseparating hAnonseparating
  have hWdiffNonempty : (W \ A).Nonempty := by
    by_contra hWdiff
    rw [Set.not_nonempty_iff_eq_empty] at hWdiff
    have hWsubA : W ⊆ A := by
      intro y hyW
      by_contra hyA
      have hyDiff : y ∈ W \ A := ⟨hyW, hyA⟩
      rw [hWdiff] at hyDiff
      exact hyDiff
    have hAeq : A = W ∪ {(x : StandardSphere 2)} := by
      ext y
      constructor
      · intro hyA
        by_cases hyx : y = x
        · exact Or.inr (Set.mem_singleton_iff.mpr hyx)
        · apply Or.inl
          apply hremSubW
          refine ⟨hyA, ?_⟩
          intro hyD
          have hyInter : y ∈ D ∩ A := ⟨hyD, hyA⟩
          rw [hinter] at hyInter
          exact hyx hyInter
      · rintro (hyW | hyx)
        · exact hWsubA hyW
        · rw [Set.mem_singleton_iff] at hyx
          exact hyx ▸ x.2
    obtain ⟨z, hzA⟩ := Set.nonempty_compl.mpr (isArc_ne_univ_standardSphere A)
    have hpunctureCover : ({(x : StandardSphere 2)} : Set (StandardSphere 2))ᶜ ⊆
        W ∪ Aᶜ := by
      intro y hyx
      by_cases hyA : y ∈ A
      · rw [hAeq] at hyA
        exact Or.inl (hyA.resolve_right hyx)
      · exact Or.inr hyA
    have hpunctureConnected :=
      (puncturedStandardSphere_isSimplyConnected (x : StandardSphere 2)).isPathConnected.isConnected
    obtain hpunctureSubW | hpunctureSubA :=
      hpunctureConnected.isPreconnected.subset_or_subset hWopen hAgeometry.1.isOpen_compl
        (LE.le.disjoint_compl_right hWsubA) hpunctureCover
    · have hzx : z ∈ ({(x : StandardSphere 2)} : Set (StandardSphere 2))ᶜ := by
        intro hzx
        exact hzA (hzx ▸ x.2)
      exact hzA (hWsubA (hpunctureSubW hzx))
    · have hax : a ∈ ({(x : StandardSphere 2)} : Set (StandardSphere 2))ᶜ := by
        intro hax
        exact haD (hax ▸ hxD)
      exact (hpunctureSubA hax) (hWsubA (mem_connectedComponentIn haD))
  have hLocalSet : (K ∪ A)ᶜ = W \ A := by
    ext y
    simp [K]
  have hLocalConnected : IsConnected ((K ∪ A)ᶜ) := by
    have hpreconnectedSpace : PreconnectedSpace ((K ∪ A)ᶜ : Set (StandardSphere 2)) := by
      by_contra hpre
      exact hUnionNonseparating (Set.separates_iff.mpr hpre)
    refine ⟨?_, isPreconnected_iff_preconnectedSpace.mpr hpreconnectedSpace⟩
    rw [hLocalSet]
    exact hWdiffNonempty
  have hLocalOne : Cardinal.mk (ConnectedComponents ((K ∪ A)ᶜ :
      Set (StandardSphere 2))) = 1 :=
    mk_connectedComponents_eq_one_of_isConnected (K ∪ A)ᶜ hLocalConnected
  obtain ⟨κ, hDlocal, hUnionLocal⟩ :=
    mk_connectedComponents_compl_union_eq_add_remainder D A hDclosed a haD hremSubW
  -- The affected domain still contributes one component, so the global count is unchanged.
  rw [Set.separatesInto_iff] at hDseparates ⊢
  calc
    Cardinal.mk (ConnectedComponents ((D ∪ A)ᶜ : Set (StandardSphere 2))) =
        Cardinal.mk (ConnectedComponents ((K ∪ A)ᶜ : Set (StandardSphere 2))) + κ :=
      hUnionLocal
    _ = 1 + κ := congrArg (fun μ ↦ μ + κ) hLocalOne
    _ = Cardinal.mk (ConnectedComponents (Dᶜ : Set (StandardSphere 2))) := hDlocal.symm
    _ = n := hDseparates

/-- Exercise 63.2 (2): Adjoining an arc that meets `D` in both endpoints
increases the number of complementary components by one. -/
theorem arcUnion_separatesInto_succ_of_inter_endpoints (n : ℕ)
    (D A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    [Topology.IsArc A]
    (hDclosed : IsClosed D) (hDconnected : IsConnected D)
    (hDseparates : D.SeparatesInto n)
    (hinter : D ∩ A = Subtype.val '' {x : A | Topology.IsArc.IsEndpoint x}) :
    (D ∪ A).SeparatesInto (n + 1) := by
  classical
  -- As in part (a), work inside the unique complementary domain containing the
  -- connected arc interior.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  have hAgeometry := isClosed_isConnected_of_isArc A
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  let I : Set A := {x : A | Topology.IsArc.IsInteriorPoint x}
  have hremEq : A \ D = Subtype.val '' I := by
    ext y
    constructor
    · intro hy
      let yA : A := ⟨y, hy.1⟩
      have hyInterior : Topology.IsArc.IsInteriorPoint yA := by
        rw [Topology.IsArc.isInteriorPoint_iff e]
        constructor
        · intro hy0
          have hyEndpoint : Topology.IsArc.IsEndpoint yA :=
            (Topology.IsArc.isEndpoint_iff e yA).mpr (Or.inl hy0)
          have hyImage : y ∈ Subtype.val '' {z : A | Topology.IsArc.IsEndpoint z} :=
            ⟨yA, hyEndpoint, rfl⟩
          exact hy.2 (hinter.symm ▸ hyImage).1
        · intro hy1
          have hyEndpoint : Topology.IsArc.IsEndpoint yA :=
            (Topology.IsArc.isEndpoint_iff e yA).mpr (Or.inr hy1)
          have hyImage : y ∈ Subtype.val '' {z : A | Topology.IsArc.IsEndpoint z} :=
            ⟨yA, hyEndpoint, rfl⟩
          exact hy.2 (hinter.symm ▸ hyImage).1
      exact ⟨yA, hyInterior, rfl⟩
    · rintro ⟨y, hyInterior, rfl⟩
      refine ⟨y.2, ?_⟩
      intro hyD
      have hyInter : (y : StandardSphere 2) ∈ D ∩ A := ⟨hyD, y.2⟩
      rw [hinter] at hyInter
      obtain ⟨z, hzEndpoint, hzy⟩ := hyInter
      have hzy' : z = y := Subtype.ext hzy
      have hyInterior' : Topology.IsArc.IsInteriorPoint y := by
        simpa only [I, mem_setOf_eq] using hyInterior
      have hyInteriorCoords := (Topology.IsArc.isInteriorPoint_iff e y).mp hyInterior'
      have hzEndpointCoords := (Topology.IsArc.isEndpoint_iff e z).mp hzEndpoint
      rw [hzy'] at hzEndpointCoords
      exact hzEndpointCoords.elim hyInteriorCoords.1 hyInteriorCoords.2
  have hremConnected : IsConnected (A \ D) := by
    rw [hremEq]
    exact (isConnected_arcInteriorPoints A).image Subtype.val
      continuous_subtype_val.continuousOn
  obtain ⟨a, haRem⟩ := hremConnected.nonempty
  have haD : a ∈ Dᶜ := haRem.2
  let W := connectedComponentIn Dᶜ a
  let K := Wᶜ
  have hremSubW : A \ D ⊆ W :=
    hremConnected.isPreconnected.subset_connectedComponentIn
      haRem (fun _ hy ↦ hy.2)
  have hWconnected : IsConnected W :=
    isConnected_connectedComponentIn_iff.mpr haD
  have hWopen : IsOpen W := hDclosed.isOpen_compl.connectedComponentIn
  have hKclosed : IsClosed K := hWopen.isClosed_compl
  have hKconnected : IsConnected K :=
    isConnected_complementaryDomainExterior D hDclosed hDconnected a haD
  have hKnonseparating : ¬ K.Separates :=
    compl_not_separates_of_isConnected W hWconnected
  have hAnonseparating : ¬ A.Separates := arc_not_separates A
  have hKinterA : K ∩ A = D ∩ A := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, hy.2⟩
      by_contra hyD
      exact hy.1 (hremSubW ⟨hy.2, hyD⟩)
    · intro hy
      refine ⟨?_, hy.2⟩
      intro hyW
      exact (connectedComponentIn_subset Dᶜ a hyW) hy.1
  let p : StandardSphere 2 := (e.symm 0 : A).1
  let q : StandardSphere 2 := (e.symm 1 : A).1
  have hpq : p ≠ q := by
    intro hpq
    have hsubtype : e.symm 0 = e.symm 1 := Subtype.ext hpq
    exact zero_ne_one (e.symm.injective hsubtype)
  have hendpointPair :
      Subtype.val '' {x : A | Topology.IsArc.IsEndpoint x} = {p, q} := by
    exact endpointImage_eq_pair A e
  have hKinterPair : K ∩ A = {p, q} :=
    hKinterA.trans (hinter.trans hendpointPair)
  have hLocalTwo : (K ∪ A).SeparatesInto 2 :=
    union_separatesInto_two_of_inter_pair K A hKclosed hAgeometry.1
      hKconnected hAgeometry.2 ⟨p, q, hpq, hKinterPair⟩
      hKnonseparating hAnonseparating
  obtain ⟨κ, hDlocal, hUnionLocal⟩ :=
    mk_connectedComponents_compl_union_eq_add_remainder D A hDclosed a haD hremSubW
  have hLocalCount : Cardinal.mk
      (ConnectedComponents ((K ∪ A)ᶜ : Set (StandardSphere 2))) = 2 :=
    Set.separatesInto_iff.mp hLocalTwo
  have htwo : (2 : Cardinal) = 1 + 1 := by
    norm_num
  -- Replacing one old domain by two local domains adds exactly one globally.
  rw [Set.separatesInto_iff] at hDseparates ⊢
  calc
    Cardinal.mk (ConnectedComponents ((D ∪ A)ᶜ : Set (StandardSphere 2))) =
        Cardinal.mk (ConnectedComponents ((K ∪ A)ᶜ : Set (StandardSphere 2))) + κ :=
      hUnionLocal
    _ = 2 + κ := congrArg (fun μ ↦ μ + κ) hLocalCount
    _ = (1 + κ) + 1 := by
      rw [htwo]
      ac_rfl
    _ = Cardinal.mk (ConnectedComponents (Dᶜ : Set (StandardSphere 2))) + 1 :=
      congrArg (fun μ ↦ μ + 1) hDlocal.symm
    _ = (n : Cardinal) + 1 := congrArg (fun μ ↦ μ + 1) hDseparates
    _ = ((n + 1 : ℕ) : Cardinal) := (Nat.cast_add n 1).symm

/-- Exercise 63.2 (3): Adjoining a simple closed curve that meets `D` in one
point increases the number of complementary components by one. -/
theorem simpleClosedCurveUnion_separatesInto_succ (n : ℕ)
    (D C : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    [Topology.IsSimpleClosedCurve C]
    (hDclosed : IsClosed D) (hDconnected : IsConnected D)
    (hDseparates : D.SeparatesInto n)
    (hinter : ∃ x, D ∩ C = {x}) :
    (D ∪ C).SeparatesInto (n + 1) := by
  classical
  obtain ⟨x, hinter⟩ := hinter
  have hxInter : x ∈ D ∩ C := by
    rw [hinter]
    exact Set.mem_singleton x
  have hxD : x ∈ D := hxInter.1
  have hxC : x ∈ C := hxInter.2
  obtain ⟨A₁, A₂, hA₁Arc, hA₂Arc, q, hxq, hCunion, hAinter,
      hEndpoints₁, hEndpoints₂⟩ := existsTwoArcDecompositionAt C x hxC
  letI : Topology.IsArc A₁ := hA₁Arc
  letI : Topology.IsArc A₂ := hA₂Arc
  have hA₁geometry := isClosed_isConnected_of_isArc A₁
  have hA₂geometry := isClosed_isConnected_of_isArc A₂
  have hxAinter : x ∈ A₁ ∩ A₂ := by
    rw [hAinter]
    exact Set.mem_insert x {q}
  have hA₁subC : A₁ ⊆ C := by
    rw [hCunion]
    exact Set.subset_union_left
  have hA₂subC : A₂ ⊆ C := by
    rw [hCunion]
    exact Set.subset_union_right
  have hDinterA₁ : D ∩ A₁ = {x} := by
    ext y
    constructor
    · intro hy
      have hyDC : y ∈ D ∩ C := ⟨hy.1, hA₁subC hy.2⟩
      rwa [hinter] at hyDC
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ ⟨hxD, hxAinter.1⟩
  have hxEndpointImage₁ :
      x ∈ Subtype.val '' {z : A₁ | Topology.IsArc.IsEndpoint z} := by
    rw [hEndpoints₁]
    exact Set.mem_insert x {q}
  obtain ⟨x₁, hx₁Endpoint, hx₁val⟩ := hxEndpointImage₁
  have hFirstArc : (D ∪ A₁).SeparatesInto n := by
    -- The first arc meets `D` only at the prescribed endpoint, so part (a) applies.
    apply arcUnion_separatesInto_of_inter_endpoint n D A₁ hDclosed hDconnected
      hDseparates
    refine ⟨x₁, hx₁Endpoint, ?_⟩
    simpa only [hx₁val] using hDinterA₁
  have hDunionA₁closed : IsClosed (D ∪ A₁) :=
    hDclosed.union hA₁geometry.1
  have hDunionA₁connected : IsConnected (D ∪ A₁) := by
    exact IsConnected.union ⟨x, hxD, hxAinter.1⟩ hDconnected hA₁geometry.2
  have hSecondInterPair : (D ∪ A₁) ∩ A₂ = {x, q} := by
    ext y
    constructor
    · intro hy
      rcases hy.1 with hyD | hyA₁
      · have hyDC : y ∈ D ∩ C := ⟨hyD, hA₂subC hy.2⟩
        rw [hinter] at hyDC
        exact Or.inl hyDC
      · rw [← hAinter]
        exact ⟨hyA₁, hy.2⟩
    · intro hy
      have hyInter : y ∈ A₁ ∩ A₂ := by
        rwa [hAinter]
      exact ⟨Or.inr hyInter.1, hyInter.2⟩
  have hSecondInter : (D ∪ A₁) ∩ A₂ =
      Subtype.val '' {z : A₂ | Topology.IsArc.IsEndpoint z} :=
    hSecondInterPair.trans hEndpoints₂.symm
  have hSecondArc : ((D ∪ A₁) ∪ A₂).SeparatesInto (n + 1) := by
    -- The second arc meets the enlarged connected set in both endpoints, so part (b)
    -- supplies the single additional component.
    exact arcUnion_separatesInto_succ_of_inter_endpoints n (D ∪ A₁) A₂
      hDunionA₁closed hDunionA₁connected hFirstArc hSecondInter
  rw [hCunion, ← union_assoc]
  exact hSecondArc
