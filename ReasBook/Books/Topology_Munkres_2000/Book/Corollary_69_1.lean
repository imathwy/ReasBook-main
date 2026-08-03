module

public import Mathlib.GroupTheory.FiniteAbelian.Basic

public section

universe uG uH uι uκ

namespace AddGroup

/-- Helper for Corollary 69.1: the minimal number of additive generators of a finitely generated
torsion-free abelian group is its `ℤ`-module finrank. -/
lemma rank_eq_finrank_of_isAddTorsionFree
    {A : Type*} [AddCommGroup A] [AddGroup.FG A] [IsAddTorsionFree A] :
    AddGroup.rank A = Module.finrank ℤ A := by
  classical
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := A)
  -- The basis is an additive generating set, giving the upper bound on group rank.
  have hBasisClosure :
      AddSubgroup.closure ((Finset.univ.image b : Finset A) : Set A) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Finset.coe_image, Finset.coe_univ,
      Set.image_univ]
    have hTopToAddSubgroup : (⊤ : Submodule ℤ A).toAddSubgroup = ⊤ := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, Submodule.mem_top, AddSubgroup.mem_top]
    exact (congrArg Submodule.toAddSubgroup b.span_eq).trans hTopToAddSubgroup
  have hRankLe : AddGroup.rank A ≤ n := by
    refine (AddGroup.rank_le hBasisClosure).trans_eq ?_
    simp only [Finset.card_image_of_injective Finset.univ b.injective, Finset.card_univ,
      Fintype.card_fin]
  -- A smallest additive generating set also spans the `ℤ`-module, giving the reverse bound.
  obtain ⟨s, hsCard, hsClosure⟩ := AddGroup.rank_spec A
  have hSpan : Submodule.span ℤ (s : Set A) = ⊤ := by
    apply Submodule.toAddSubgroup_injective
    rw [Submodule.span_int_eq_addSubgroupClosure, hsClosure]
    rfl
  have hFinrankLe : Module.finrank ℤ A ≤ s.card := by
    have hSpanFinrank := finrank_span_finset_le_card (R := ℤ) s
    rwa [Set.finrank, hSpan, finrank_top] at hSpanFinrank
  have hFinrankEq : Module.finrank ℤ A = n := by
    simp only [Module.finrank_eq_card_basis b, Fintype.card_fin]
  omega

/-- Helper for Corollary 69.1: finitely generated torsion-free abelian groups of equal additive
rank are additively equivalent. -/
lemma nonemptyAddEquivOfRankEqOfIsAddTorsionFree
    {A : Type uG} {B : Type uH}
    [AddCommGroup A] [AddCommGroup B] [AddGroup.FG A] [AddGroup.FG B]
    [IsAddTorsionFree A] [IsAddTorsionFree B]
    (hRank : AddGroup.rank A = AddGroup.rank B) : Nonempty (A ≃+ B) := by
  classical
  -- Replace group rank by module finrank and identify the canonical finite bases.
  have hFinrank : Module.finrank ℤ A = Module.finrank ℤ B := by
    rw [← rank_eq_finrank_of_isAddTorsionFree,
      ← rank_eq_finrank_of_isAddTorsionFree, hRank]
  obtain ⟨n, basisA⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := A)
  obtain ⟨m, basisB⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := B)
  have hBasisAFinrank : n = Module.finrank ℤ A := by
    simp only [Module.finrank_eq_card_basis basisA, Fintype.card_fin]
  have hBasisBFinrank : Module.finrank ℤ B = m := by
    simp only [Module.finrank_eq_card_basis basisB, Fintype.card_fin]
  have hIndex : n = m := hBasisAFinrank.trans (hFinrank.trans hBasisBFinrank)
  let indexEquiv := finCongr hIndex
  -- A basis equivalence is in particular an additive equivalence.
  exact ⟨(basisA.equiv basisB indexEquiv).toAddEquiv⟩

end AddGroup

namespace AddCommGroup

/-- Helper for Corollary 69.1: a finitely generated abelian group splits additively as its
torsion subgroup times its torsion-free quotient. -/
theorem nonemptyAddEquivTorsionProdQuotient
    (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    Nonempty (A ≃+ AddCommGroup.torsion A × (A ⧸ AddCommGroup.torsion A)) := by
  let torsionSubmodule := Submodule.torsion ℤ A
  -- Projectivity of the finite torsion-free quotient supplies a section of the quotient map.
  obtain ⟨sectionMap, hSection⟩ := Module.projective_lifting_property
    torsionSubmodule.mkQ LinearMap.id torsionSubmodule.mkQ_surjective
  have hExact : LinearMap.range torsionSubmodule.subtype = LinearMap.ker torsionSubmodule.mkQ := by
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  let splitEquiv := lequivProdOfRightSplitExact torsionSubmodule.injective_subtype hExact hSection
  -- Forget linearity and orient the split equivalence from the original group to the product.
  rw [← Submodule.torsion_int]
  exact ⟨splitEquiv.symm.toAddEquiv⟩

end AddCommGroup

/-- Corollary 69.1. Two finitely generated abelian groups are additively isomorphic when their
Betti numbers agree and their torsion subgroups are additively isomorphic. -/
theorem addEquivOfFreeRankEqOfTorsionAddEquiv
    {G : Type uG} {H : Type uH}
    [AddCommGroup G] [AddCommGroup H] [AddGroup.FG G] [AddGroup.FG H]
    (hRank : AddCommGroup.freeRank G = AddCommGroup.freeRank H)
    (torsionEquiv : AddCommGroup.torsion G ≃+ AddCommGroup.torsion H) :
    Nonempty (G ≃+ H) := by
  -- Split both groups into their torsion and torsion-free components.
  obtain ⟨splitG⟩ := AddCommGroup.nonemptyAddEquivTorsionProdQuotient G
  obtain ⟨splitH⟩ := AddCommGroup.nonemptyAddEquivTorsionProdQuotient H
  have hQuotientRank :
      AddGroup.rank (G ⧸ AddCommGroup.torsion G) =
        AddGroup.rank (H ⧸ AddCommGroup.torsion H) := by
    simpa only [AddCommGroup.freeRank_def] using hRank
  obtain ⟨quotientEquiv⟩ :=
    AddGroup.nonemptyAddEquivOfRankEqOfIsAddTorsionFree hQuotientRank
  -- Combine the supplied torsion equivalence with the classified free quotients.
  exact ⟨splitG.trans ((torsionEquiv.prodCongr quotientEquiv).trans splitH.symm)⟩

/-- Helper for Corollary 69.1: matching explicit elementary-divisor decompositions and equal
Betti numbers give an additive equivalence of finitely generated abelian groups. -/
theorem addEquivOfFreeRankEqOfElementaryDivisors
    {G : Type uG} {H : Type uH} {ι : Type uι} {κ : Type uκ}
    [AddCommGroup G] [AddCommGroup H] [AddGroup.FG G] [AddGroup.FG H]
    (pG : ι → ℕ) (eG : ι → ℕ) (pH : κ → ℕ) (eH : κ → ℕ)
    (torsionG : AddCommGroup.torsion G ≃+ DirectSum ι (fun i ↦ ZMod (pG i ^ eG i)))
    (torsionH : AddCommGroup.torsion H ≃+ DirectSum κ (fun j ↦ ZMod (pH j ^ eH j)))
    (hRank : AddCommGroup.freeRank G = AddCommGroup.freeRank H)
    (σ : ι ≃ κ) (hOrders : ∀ i, pG i ^ eG i = pH (σ i) ^ eH (σ i)) :
    Nonempty (G ≃+ H) := by
  -- Reindexing preserves each cyclic factor's order.
  have hReindexedOrders : ∀ j, pG (σ.symm j) ^ eG (σ.symm j) = pH j ^ eH j := by
    intro j
    simpa only [Equiv.apply_symm_apply] using hOrders (σ.symm j)
  -- Transport the direct-sum factors and invoke the intrinsic classification theorem.
  apply addEquivOfFreeRankEqOfTorsionAddEquiv hRank
  exact torsionG |>.trans (DirectSum.equivCongrLeft σ) |>.trans
    (DirectSum.congrAddEquiv fun j ↦
      (ZMod.ringEquivCongr (hReindexedOrders j)).toAddEquiv) |>.trans torsionH.symm
