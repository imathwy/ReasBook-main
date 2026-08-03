module

public import Topology_Munkres_2000.Book.Theorem_9_0_1.OpenCoverWinding

public section

open Set

universe u

namespace Theorem901

/-- Helper for Theorem 9.0.1: a metric two-set cover with path access through
both members and infinite-cyclic fundamental group has at most two overlap
components. -/
lemma mk_connectedComponents_inter_le_two_of_windingCover
    {X : Type u} [PseudoMetricSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUcompl : Uᶜ.Nonempty) (hVcompl : Vᶜ.Nonempty)
    (hcover : U ∪ V = Set.univ)
    [LocallyConnectedSpace (U ∩ V : Set X)]
    (hjoinedU : ∀ x y : (U ∩ V : Set X), JoinedIn U x.1 y.1)
    (hjoinedV : ∀ x y : (U ∩ V : Set X), JoinedIn V x.1 y.1)
    (hfundamental : ∀ x : (U ∩ V : Set X),
      Nonempty (FundamentalGroup X x.1 ≃* Multiplicative ℤ)) :
    Cardinal.mk (ConnectedComponents (U ∩ V : Set X)) ≤ 2 := by
  -- Three overlap components provide the two component partitions used by the
  -- winding-coordinate contradiction.
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
  have hA₀open : IsOpen A₀ :=
    isOpen_connectedComponent.union isOpen_connectedComponent
  have hB₀open : IsOpen B₀ :=
    (isClosed_connectedComponent.union isClosed_connectedComponent).isOpen_compl
  have hA₁open : IsOpen A₁ := isOpen_connectedComponent
  have hB₁open : IsOpen B₁ := isClosed_connectedComponent.isOpen_compl
  have hAopen : IsOpen A :=
    (hU.inter hV).isOpenMap_subtype_val A₀ hA₀open
  have hBopen : IsOpen B :=
    (hU.inter hV).isOpenMap_subtype_val B₀ hB₀open
  have hA'open : IsOpen A' :=
    (hU.inter hV).isOpenMap_subtype_val A₁ hA₁open
  have hB'open : IsOpen B' :=
    (hU.inter hV).isOpenMap_subtype_val B₁ hB₁open
  have hoverlap : U ∩ V = A ∪ B := by
    ext x
    constructor
    · intro hx
      let y : (U ∩ V : Set X) := ⟨x, hx⟩
      by_cases hy : y ∈ A₀
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
    · rintro (⟨y, -, rfl⟩ | ⟨y, -, rfl⟩)
      · exact y.2
      · exact y.2
  have hoverlap' : U ∩ V = A' ∪ B' := by
    ext x
    constructor
    · intro hx
      let y : (U ∩ V : Set X) := ⟨x, hx⟩
      by_cases hy : y ∈ A₁
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
    · rintro (⟨y, -, rfl⟩ | ⟨y, -, rfl⟩)
      · exact y.2
      · exact y.2
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
  -- Record which side of each partition contains the three representatives.
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
  obtain ⟨w₀⟩ := exists_openCoverWindingCoordinate hU hV hAopen hBopen
    hUcompl hVcompl hcover hoverlap hAB
  obtain ⟨w₁⟩ := exists_openCoverWindingCoordinate hU hV hA'open hB'open
    hUcompl hVcompl hcover hoverlap' hA'B'
  -- Lift the four cover-contained paths to paths in the cover subtypes.
  have habU : Joined (⟨a.1, a.2.1⟩ : U) ⟨b.1, b.2.1⟩ :=
    (joinedIn_iff_joined a.2.1 b.2.1).mp (hjoinedU a b)
  have hbaV : Joined (⟨b.1, b.2.2⟩ : V) ⟨a.1, a.2.2⟩ :=
    (joinedIn_iff_joined b.2.2 a.2.2).mp (hjoinedV b a)
  have haa'U : Joined (⟨a.1, a.2.1⟩ : U) ⟨a'.1, a'.2.1⟩ :=
    (joinedIn_iff_joined a.2.1 a'.2.1).mp (hjoinedU a a')
  have ha'aV : Joined (⟨a'.1, a'.2.2⟩ : V) ⟨a.1, a.2.2⟩ :=
    (joinedIn_iff_joined a'.2.2 a.2.2).mp (hjoinedV a' a)
  let alpha : Path (⟨a.1, a.2.1⟩ : U) ⟨b.1, b.2.1⟩ := habU.somePath
  let beta : Path (⟨b.1, b.2.2⟩ : V) ⟨a.1, a.2.2⟩ := hbaV.somePath
  let gamma : Path (⟨a.1, a.2.1⟩ : U) ⟨a'.1, a'.2.1⟩ := haa'U.somePath
  let delta : Path (⟨a'.1, a'.2.2⟩ : V) ⟨a.1, a.2.2⟩ := ha'aV.somePath
  let f : FundamentalGroup X a.1 := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      ((alpha.map continuous_subtype_val).trans (beta.map continuous_subtype_val)))
  let g : FundamentalGroup X a.1 := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      ((gamma.map continuous_subtype_val).trans (delta.map continuous_subtype_val)))
  have hfCoordinate : w₀.fundamentalGroupCoordinate a f =
      Multiplicative.ofAdd (-1) := by
    exact w₀.pathPairCoordinate_eq_neg_one a b alpha beta haA hbB
  have hgCoordinateZero : w₀.fundamentalGroupCoordinate a g =
      Multiplicative.ofAdd 0 := by
    exact w₀.pathPairCoordinate_eq_zero a a' gamma delta haA ha'A
  have hgCoordinateNeg : w₁.fundamentalGroupCoordinate a g =
      Multiplicative.ofAdd (-1) := by
    exact w₁.pathPairCoordinate_eq_neg_one a a' gamma delta haA' ha'B'
  have hfNe : f ≠ 1 := by
    intro hf
    have h := congrArg (w₀.fundamentalGroupCoordinate a) hf
    rw [hfCoordinate, map_one] at h
    norm_num at h
  have hgNe : g ≠ 1 := by
    intro hg
    have h := congrArg (w₁.fundamentalGroupCoordinate a) hg
    rw [hgCoordinateNeg, map_one] at h
    norm_num at h
  -- Infinite cyclicity equates nonzero powers, while the first winding
  -- coordinate sends those powers to incompatible integers.
  obtain ⟨fundamentalEquiv⟩ := hfundamental a
  obtain ⟨m, k, hm, hk, hpower⟩ :=
    exists_zpow_eq_zpow_of_equiv_int fundamentalEquiv hfNe hgNe
  have hcoordinatePower :=
    congrArg (w₀.fundamentalGroupCoordinate a) hpower
  rw [map_zpow, map_zpow, hfCoordinate, hgCoordinateZero] at hcoordinatePower
  have hadditive := congrArg Multiplicative.toAdd hcoordinatePower
  simp only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_zero] at hadditive
  have hmzero : m = 0 := by
    have hneg : -m = 0 := by
      simpa only [Int.cast_id, mul_neg, mul_one] using hadditive
    exact neg_eq_zero.mp hneg
  exact hm hmzero

end Theorem901

end
