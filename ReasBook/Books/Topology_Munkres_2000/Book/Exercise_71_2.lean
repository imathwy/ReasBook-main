module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Definition_68_5
public import Topology_Munkres_2000.Book.Exercise_71_2.FiniteWedge
public import Topology_Munkres_2000.Book.Lemma_68_5
public import Topology_Munkres_2000.Book.Theorem_58_3
public import Topology_Munkres_2000.Book.Theorem_70_1.Pushout
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Proposition_58_2.HomotopyEquiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.Topology.LocallyFinite

public section

open Set CategoryTheory CategoryTheory.Limits

universe u

/-- Helper for Exercise 71.2: the partial wedge supported on the finite set `J`. -/
private def finiteWedgeCore {X : Type u} {ι : Type*}
    (S : ι → Set X) (p : X) (J : Finset ι) : Set X :=
  {p} ∪ ⋃ i ∈ J, S i

/-- Helper for Exercise 71.2: the partial wedge in which summands outside `J` are
replaced by their chosen neighborhoods. -/
private def finiteWedgeThickening {X : Type u} {ι : Type*} [DecidableEq ι]
    (S : ι → Set X) (p : X) (W : ∀ i, Set (S i)) (J K : Finset ι) : Set X :=
  finiteWedgeCore S p J ∪ ⋃ i ∈ K \ J, Subtype.val '' W i

/-- Helper for Exercise 71.2: the wedge point belongs to every partial wedge core. -/
private lemma point_mem_finiteWedgeCore {X : Type u} {ι : Type*}
    (S : ι → Set X) (p : X) (J : Finset ι) :
    p ∈ finiteWedgeCore S p J := by
  -- The explicit singleton in the core handles the empty-index base case uniformly.
  exact Set.mem_union_left _ (Set.mem_singleton p)

/-- Helper for Exercise 71.2: the wedge point as a point of a partial core. -/
private def finiteWedgeCorePoint {X : Type u} {ι : Type*}
    (S : ι → Set X) (p : X) (J : Finset ι) : finiteWedgeCore S p J :=
  ⟨p, point_mem_finiteWedgeCore S p J⟩

/-- Helper for Exercise 71.2: each selected summand lies in its partial wedge core. -/
private lemma summand_subset_finiteWedgeCore {X : Type u} {ι : Type*}
    (S : ι → Set X) (p : X) (J : Finset ι) {i : ι} (hi : i ∈ J) :
    S i ⊆ finiteWedgeCore S p J := by
  -- Insert the summand into the finite union occurring on the right of the core.
  intro x hx
  exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hx⟩⟩)

/-- Helper for Exercise 71.2: enlarging the index set enlarges the partial wedge core. -/
private lemma finiteWedgeCore_mono {X : Type u} {ι : Type*}
    (S : ι → Set X) (p : X) {J K : Finset ι} (hJK : J ⊆ K) :
    finiteWedgeCore S p J ⊆ finiteWedgeCore S p K := by
  -- Preserve the wedge point and send every indexed summand along `J ⊆ K`.
  rintro x (hx | hx)
  · exact Set.mem_union_left _ hx
  · rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hiJ, hxS⟩ := hx
    exact Set.mem_union_right _
      (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hJK hiJ, hxS⟩⟩)

/-- Helper for Exercise 71.2: the partial core indexed by every summand is the
whole ambient space. -/
private lemma finiteWedgeCore_univ {X : Type u} [TopologicalSpace X]
    {ι : Type*} [Fintype ι] (S : ι → Set X) (p : X)
    [h : Topology.IsFiniteWedge S p] :
    finiteWedgeCore S p Finset.univ = Set.univ := by
  -- The finite union over `univ` is the given wedge cover; adjoining `p` changes nothing.
  simp only [finiteWedgeCore, Finset.mem_univ, Set.iUnion_true, h.covers,
    Set.union_univ]

/-- Helper for Exercise 71.2: the core retained on a singleton index is exactly
that summand. -/
private lemma finiteWedgeCore_singleton
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p] (i : k) :
    finiteWedgeCore S p {i} = S i := by
  -- The wedge point already belongs to the selected summand.
  ext x
  constructor
  · rintro (hxp | hxi)
    · rw [Set.mem_singleton_iff.mp hxp]
      exact h.point_mem i
    · rw [Set.mem_iUnion₂] at hxi
      obtain ⟨j, hj, hxj⟩ := hxi
      simpa only [Finset.mem_singleton.mp hj] using hxj
  · intro hxi
    exact Set.mem_union_right _
      (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_singleton_self i, hxi⟩⟩)

/-- Helper for Exercise 71.2: the retained core is contained in its thickening. -/
private lemma finiteWedgeCore_subset_thickening {X : Type u} {ι : Type*} [DecidableEq ι]
    (S : ι → Set X) (p : X) (W : ∀ i, Set (S i)) (J K : Finset ι) :
    finiteWedgeCore S p J ⊆ finiteWedgeThickening S p W J K := by
  -- This is the left summand in the defining union of the thickening.
  exact Set.subset_union_left

/-- Helper for Exercise 71.2: a subset is canonically homeomorphic to its preimage
inside any containing subspace. -/
private def setSubsetPreimageHomeomorph
    {X : Type*} [TopologicalSpace X] {U V : Set X} (hUV : U ⊆ V) :
    U ≃ₜ (Subtype.val ⁻¹' U : Set V) where
  toFun x := ⟨⟨x, hUV x.property⟩, x.property⟩
  invFun x := ⟨x.1.1, x.property⟩
  left_inv x := by
    -- Both composites retain the same ambient point; the named eta law avoids
    -- reducing nested subtype membership witnesses.
    exact Subtype.coe_eta x _
  right_inv x := by
    change (⟨⟨x.1.1, hUV x.property⟩, x.property⟩ :
      (Subtype.val ⁻¹' U : Set V)) = x
    have hinner : (⟨x.1.1, hUV x.property⟩ : V) = x.1 :=
      Subtype.coe_eta x.1 _
    exact Subtype.ext hinner
  continuous_toFun := by
    -- Continuity is inherited twice from the two subtype inclusions.
    exact (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := by
    -- Forget both membership proofs, then repackage the ambient point.
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Helper for Exercise 71.2: induced fundamental-group maps respect composition
of continuous maps. -/
private lemma fundamentalGroupMap_comp
    {A : Type*} {B : Type*} {C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (g : C(B, C)) (f : C(A, B)) (a : A) :
    (FundamentalGroup.map g (f a)).comp (FundamentalGroup.map f a) =
      FundamentalGroup.map (g.comp f) a := by
  ext q
  simp only [MonoidHom.comp_apply]
  have innerMap :
      FundamentalGroup.map f a q = Path.Homotopic.Quotient.map q f :=
    FundamentalGroup.map_apply f a q
  have nestedMap :
      Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map q f) g =
        Path.Homotopic.Quotient.map q (g.comp f) := by
    exact (Path.Homotopic.Quotient.map_comp (p := q) (f := f) (g := g)).symm
  have outerToComposite :
      FundamentalGroup.map g (f a) (Path.Homotopic.Quotient.map q f) =
        FundamentalGroup.map (g.comp f) a q := by
    rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply]
    exact nestedMap
  exact (congrArg (fun z ↦ FundamentalGroup.map g (f a) z) innerMap).trans
    outerToComposite

/-- Helper for Exercise 71.2: `mapOfSubtype` is the map induced by the canonical
subtype inclusion. -/
private lemma FundamentalGroup.mapOfSubtype_eq_map_subtypeVal
    {X : Type*} [TopologicalSpace X] (U : Set X) (x : U) :
    FundamentalGroup.mapOfSubtype U x =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x := by
  -- Expose the owner definition once for transport-stable composition rewrites.
  unfold FundamentalGroup.mapOfSubtype
  ext q
  rw [FundamentalGroup.map_apply]

/-- Helper for Exercise 71.2: inclusion of a deformation retract induces a
bijective map on the ordinary mathlib fundamental group. -/
private lemma fundamentalGroupMapOfSubtype_bijective_of_isDeformationRetract
    {Y : Type*} [TopologicalSpace Y] {A : Set Y}
    (hA : Set.IsDeformationRetract A) (a : A) :
    Function.Bijective (FundamentalGroup.mapOfSubtype A a) := by
  rw [Set.isDeformationRetract_iff] at hA
  obtain ⟨r, ⟨H⟩⟩ := hA
  -- The forward map of the deformation-retraction equivalence is definitionally
  -- the subtype inclusion used by `mapOfSubtype`.
  exact ContinuousMap.HomotopyEquiv.fundamentalGroupMap_bijective
    (Set.DeformationRetraction.toHomotopyEquiv ⟨r, H⟩) a

/-- Helper for Exercise 71.2: if a subset is a deformation retract after viewing it
inside a containing subspace, its direct inclusion induces a bijection on fundamental groups. -/
private lemma fundamentalGroupMapOfSubset_bijective_of_isDeformationRetract
    {X : Type*} [TopologicalSpace X] {U V : Set X} (hUV : U ⊆ V) (x₀ : U)
    (hU : Set.IsDeformationRetract (Subtype.val ⁻¹' U : Set V)) :
    Function.Bijective (FundamentalGroup.mapOfSubset hUV x₀) := by
  let e := setSubsetPreimageHomeomorph hUV
  have heBij : Function.Bijective
      (FundamentalGroup.map (e : C(U, (Subtype.val ⁻¹' U : Set V))) x₀) := by
    exact e.toHomotopyEquiv.fundamentalGroupMap_bijective x₀
  have hincBij : Function.Bijective
      (FundamentalGroup.mapOfSubtype (Subtype.val ⁻¹' U : Set V) (e x₀)) :=
    fundamentalGroupMapOfSubtype_bijective_of_isDeformationRetract hU (e x₀)
  have hcontinuous :
      (ContinuousMap.comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C((Subtype.val ⁻¹' U : Set V), V))
        (e : C(U, (Subtype.val ⁻¹' U : Set V)))) =
        ContinuousMap.inclusion hUV := by
    ext x
    exact congrArg Subtype.val (Subtype.coe_eta (ContinuousMap.inclusion hUV x) _)
  have hmap :
      (FundamentalGroup.mapOfSubtype (Subtype.val ⁻¹' U : Set V) (e x₀)).comp
          (FundamentalGroup.map (e : C(U, (Subtype.val ⁻¹' U : Set V))) x₀) =
        FundamentalGroup.mapOfSubset hUV x₀ := by
    rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
    rw [FundamentalGroup.mapOfSubtype_eq_map_subtypeVal]
    calc
      _ = FundamentalGroup.map
          ((⟨Subtype.val, continuous_subtype_val⟩ :
            C((Subtype.val ⁻¹' U : Set V), V)).comp
              (e : C(U, (Subtype.val ⁻¹' U : Set V)))) x₀ :=
        fundamentalGroupMap_comp _ _ x₀
      _ = FundamentalGroup.map (ContinuousMap.inclusion hUV) x₀ :=
        by
          cases hcontinuous
          rfl
  -- Compose the two bijections and normalize the composite to direct inclusion.
  have hcomp := hincBij.comp heBij
  change Function.Bijective
    ⇑((FundamentalGroup.mapOfSubtype (Subtype.val ⁻¹' U : Set V) (e x₀)).comp
      (FundamentalGroup.map (e : C(U, (Subtype.val ⁻¹' U : Set V))) x₀)) at hcomp
  rw [hmap] at hcomp
  exact hcomp

/-- Helper for Exercise 71.2: map a subspace into a larger subspace represented
as a preimage inside a common ambient subspace. -/
private noncomputable def fundamentalGroupNestedSubsetMap
    {X : Type*} [TopologicalSpace X] {A U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) (a : A) :
    FundamentalGroup A a →*
      FundamentalGroup (Subtype.val ⁻¹' U : Set V)
        ⟨⟨a, hUV (hAU a.property)⟩, hAU a.property⟩ :=
  FundamentalGroup.map
    ((setSubsetPreimageHomeomorph hUV :
        C(U, (Subtype.val ⁻¹' U : Set V))).comp
      (ContinuousMap.inclusion hAU)) a

/-- Helper for Exercise 71.2: if `A` deformation retracts from `U`, the nested
inclusion of `A` into the copy of `U` inside `V` induces a bijection on fundamental groups. -/
private lemma fundamentalGroupNestedSubsetMap_bijective_of_isDeformationRetract
    {X : Type*} [TopologicalSpace X] {A U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) (a : A)
    (hA : Set.IsDeformationRetract (Subtype.val ⁻¹' A : Set U)) :
    Function.Bijective (fundamentalGroupNestedSubsetMap hAU hUV a) := by
  have hinclusion : Function.Bijective (FundamentalGroup.mapOfSubset hAU a) :=
    fundamentalGroupMapOfSubset_bijective_of_isDeformationRetract hAU a hA
  have hhomeomorph : Function.Bijective
      (FundamentalGroup.map
        (setSubsetPreimageHomeomorph hUV :
          C(U, (Subtype.val ⁻¹' U : Set V)))
        ⟨a, hAU a.property⟩) :=
    (setSubsetPreimageHomeomorph hUV).toHomotopyEquiv.fundamentalGroupMap_bijective
      ⟨a, hAU a.property⟩
  have hcomp := hhomeomorph.comp hinclusion
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion] at hcomp
  change Function.Bijective
    ⇑((FundamentalGroup.map
        (setSubsetPreimageHomeomorph hUV :
          C(U, (Subtype.val ⁻¹' U : Set V)))
        ⟨a, hAU a.property⟩).comp
      (FundamentalGroup.map (ContinuousMap.inclusion hAU) a)) at hcomp
  have hmap :
      (FundamentalGroup.map
        (setSubsetPreimageHomeomorph hUV :
          C(U, (Subtype.val ⁻¹' U : Set V)))
        ⟨a, hAU a.property⟩).comp
          (FundamentalGroup.map (ContinuousMap.inclusion hAU) a) =
        fundamentalGroupNestedSubsetMap hAU hUV a := by
    exact fundamentalGroupMap_comp _ _ a
  exact hmap ▸ hcomp

/-- Helper for Exercise 71.2: inclusion through a nested subspace agrees with
direct inclusion into the containing subspace. -/
private lemma fundamentalGroupMapOfSubtype_comp_nestedSubsetMap
    {X : Type*} [TopologicalSpace X] {A U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) (a : A) :
    (FundamentalGroup.mapOfSubtype (Subtype.val ⁻¹' U : Set V)
      ⟨⟨a, hUV (hAU a.property)⟩, hAU a.property⟩).comp
        (fundamentalGroupNestedSubsetMap hAU hUV a) =
      FundamentalGroup.mapOfSubset (hAU.trans hUV) a := by
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  rw [FundamentalGroup.mapOfSubtype_eq_map_subtypeVal]
  unfold fundamentalGroupNestedSubsetMap
  calc
    _ = FundamentalGroup.map
        ((⟨Subtype.val, continuous_subtype_val⟩ :
            C((Subtype.val ⁻¹' U : Set V), V)).comp
          ((setSubsetPreimageHomeomorph hUV :
              C(U, (Subtype.val ⁻¹' U : Set V))).comp
            (ContinuousMap.inclusion hAU))) a :=
      fundamentalGroupMap_comp _ _ a
    _ = FundamentalGroup.map (ContinuousMap.inclusion (hAU.trans hUV)) a := by
      congr 1

/-- Helper for Exercise 71.2: fundamental-group maps induced by two nested
subset inclusions compose to the map induced by the direct inclusion. -/
private lemma fundamentalGroupMapOfSubset_comp
    {X : Type*} [TopologicalSpace X] {A U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) (a : A) :
    (FundamentalGroup.mapOfSubset hUV ⟨a, hAU a.property⟩).comp
        (FundamentalGroup.mapOfSubset hAU a) =
      FundamentalGroup.mapOfSubset (hAU.trans hUV) a := by
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion,
    FundamentalGroup.mapOfSubset_eq_map_inclusion,
    FundamentalGroup.mapOfSubset_eq_map_inclusion]
  calc
    _ = FundamentalGroup.map
        ((ContinuousMap.inclusion hUV).comp
          (ContinuousMap.inclusion hAU)) a :=
      fundamentalGroupMap_comp _ _ a
    _ = FundamentalGroup.map (ContinuousMap.inclusion (hAU.trans hUV)) a := by
      congr 1

/-- Helper for Exercise 71.2: inclusion through a subspace and then into the
ambient space induces the direct ambient inclusion on fundamental groups. -/
private lemma FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hAU : A ⊆ U) (a : A) :
    (FundamentalGroup.mapOfSubtype U ⟨a, hAU a.property⟩).comp
        (FundamentalGroup.mapOfSubset hAU a) =
      FundamentalGroup.mapOfSubtype A a := by
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  rw [FundamentalGroup.mapOfSubtype_eq_map_subtypeVal,
    FundamentalGroup.mapOfSubtype_eq_map_subtypeVal]
  calc
    _ = FundamentalGroup.map
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp
          (ContinuousMap.inclusion hAU)) a :=
      fundamentalGroupMap_comp _ _ a
    _ = FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) a := by
      congr 1

/-- Helper for Exercise 71.2: a reflexive endpoint equality in `mapOfEq`
recovers the ordinary induced fundamental-group map. -/
private lemma FundamentalGroup.mapOfEq_refl_eq_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) =
      FundamentalGroup.map f x := by
  ext q
  simp only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Helper for Exercise 71.2: a thickening indexed inside `K` lies in the `K`-core. -/
private lemma finiteWedgeThickening_subset_core {X : Type u} {ι : Type*} [DecidableEq ι]
    (S : ι → Set X) (p : X) (W : ∀ i, Set (S i)) {J K : Finset ι}
    (hJK : J ⊆ K) :
    finiteWedgeThickening S p W J K ⊆ finiteWedgeCore S p K := by
  -- Core points use monotonicity; neighborhood points lie in their ambient summands.
  rintro x (hx | hx)
  · exact finiteWedgeCore_mono S p hJK hx
  · rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hi, xW, hxW, rfl⟩ := hx
    exact summand_subset_finiteWedgeCore S p K (Finset.mem_sdiff.mp hi).1 xW.property

/-- Helper for Exercise 71.2: outside the retained core, a point of a thickening comes
from one of the discarded neighborhoods. -/
private lemma exists_neighborhood_of_mem_thickening_not_core
    {X : Type u} {ι : Type*} [DecidableEq ι]
    (S : ι → Set X) (p : X) (W : ∀ i, Set (S i))
    (J K : Finset ι) {x : X}
    (hxT : x ∈ finiteWedgeThickening S p W J K)
    (hxJ : x ∉ finiteWedgeCore S p J) :
    ∃ i, i ∈ K \ J ∧ ∃ w : W i, (w : X) = x := by
  -- Eliminate the retained-core branch of the defining union and unpack an image witness.
  rcases hxT with hxT | hxT
  · exact False.elim (hxJ hxT)
  · rw [Set.mem_iUnion₂] at hxT
    obtain ⟨i, hi, w, hw, hwx⟩ := hxT
    exact ⟨i, hi, ⟨⟨w, w.property⟩, hw⟩, hwx⟩

/-- Helper for Exercise 71.2: away from the retained core, the discarded neighborhood
containing a point is unique. -/
private lemma neighborhood_index_unique_of_not_mem_core
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (S : ι → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (J : Finset ι) {x : X} (hxJ : x ∉ finiteWedgeCore S p J)
    {i k : ι} (xi : S i) (xk : S k) (hxi : (xi : X) = x) (hxk : (xk : X) = x) :
    i = k := by
  -- Distinct summands meet only at `p`, which is already in every core.
  by_contra hik
  have hxInter : x ∈ S i ∩ S k := by
    constructor
    · simpa only [← hxi] using xi.property
    · simpa only [← hxk] using xk.property
  have hxp : x = p := Set.mem_singleton_iff.mp ((h.inter_eq hik) ▸ hxInter)
  apply hxJ
  rw [hxp]
  exact point_mem_finiteWedgeCore S p J

/-- Helper for Exercise 71.2: a point lying in two distinct wedge summands is the
wedge point. -/
private lemma eq_point_of_mem_distinct_summands
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (S : ι → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    {i j : ι} (hij : i ≠ j) {x : X} (hxi : x ∈ S i) (hxj : x ∈ S j) :
    x = p := by
  -- Apply the defining pairwise-intersection equation of a finite wedge.
  exact Set.mem_singleton_iff.mp ((h.inter_eq hij) ▸ ⟨hxi, hxj⟩)

/-- Helper for Exercise 71.2: the closed tails removed from a partial thickening. -/
private def finiteWedgeExcluded {X : Type u} {ι : Type*} [DecidableEq ι]
    (S : ι → Set X) (W : ∀ i, Set (S i)) (J K : Finset ι) : Set X :=
  ⋃ i ∈ K \ J, Subtype.val '' (W i)ᶜ

/-- Helper for Exercise 71.2: the union of the finitely many discarded closed tails is
closed in the ambient space. -/
private lemma finiteWedgeExcluded_isClosed
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i)) (hW_open : ∀ i, IsOpen (W i)) (J K : Finset ι) :
    IsClosed (finiteWedgeExcluded S W J K) := by
  -- Each tail is the closed image of the complement of `W i` in the closed summand `S i`.
  apply isClosed_biUnion_finset
  intro i hi
  exact (h.isClosed i).isClosedMap_subtype_val _ (hW_open i).isClosed_compl

/-- Helper for Exercise 71.2: inside the `K`-core, membership in a thickening is exactly
avoidance of all discarded closed tails. -/
private lemma mem_finiteWedgeThickening_iff_not_mem_excluded
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (J K : Finset ι) (x : finiteWedgeCore S p K) :
    (x : X) ∈ finiteWedgeThickening S p W J K ↔
      (x : X) ∉ finiteWedgeExcluded S W J K := by
  constructor
  · intro hxT hxE
    -- A point in an excluded tail cannot lie in any retained summand or neighborhood.
    rw [finiteWedgeExcluded, Set.mem_iUnion₂] at hxE
    obtain ⟨i, hi, wi, hwiCompl, hwi⟩ := hxE
    have hxi : (x : X) ∈ S i := by
      rw [← hwi]
      exact wi.property
    have hxp_not : (x : X) ≠ p := by
      intro hxp
      apply hwiCompl
      have hsubtype : wi = (⟨p, h.point_mem i⟩ : S i) := by
        apply Subtype.ext
        exact hwi.trans hxp
      rw [hsubtype]
      exact hpW i
    rcases hxT with hxJ | hxN
    · rcases hxJ with hxp | hxJ
      · exact hxp_not (Set.mem_singleton_iff.mp hxp)
      · rw [Set.mem_iUnion₂] at hxJ
        obtain ⟨j, hj, hxj⟩ := hxJ
        have hij : i ≠ j := by
          intro hij
          subst j
          exact (Finset.mem_sdiff.mp hi).2 hj
        exact hxp_not (eq_point_of_mem_distinct_summands S p hij hxi hxj)
    · rw [Set.mem_iUnion₂] at hxN
      obtain ⟨j, hj, wj, hwj, hwjx⟩ := hxN
      by_cases hij : i = j
      · subst j
        apply hwiCompl
        have hsubtype : wi = wj := by
          apply Subtype.ext
          exact hwi.trans hwjx.symm
        rw [hsubtype]
        exact hwj
      · have hxj : (x : X) ∈ S j := by
          simpa only [← hwjx] using wj.property
        exact hxp_not (eq_point_of_mem_distinct_summands S p hij hxi hxj)
  · intro hxE
    -- A core point is either retained already or lies in a discarded summand; in the latter
    -- case avoidance of its tail forces membership in the chosen neighborhood.
    rcases x.property with hxp | hxK
    · exact Set.mem_union_left _ (Set.mem_union_left _ hxp)
    · rw [Set.mem_iUnion₂] at hxK
      obtain ⟨i, hiK, hxi⟩ := hxK
      by_cases hiJ : i ∈ J
      · exact Set.mem_union_left _
          (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiJ, hxi⟩⟩))
      · have hxW : (⟨x, hxi⟩ : S i) ∈ W i := by
          by_contra hxW
          apply hxE
          rw [finiteWedgeExcluded]
          exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
            ⟨Finset.mem_sdiff.mpr ⟨hiK, hiJ⟩, ⟨⟨x, hxi⟩, hxW, rfl⟩⟩⟩
        exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
          ⟨Finset.mem_sdiff.mpr ⟨hiK, hiJ⟩, ⟨⟨x, hxi⟩, hxW, rfl⟩⟩⟩)

/-- Helper for Exercise 71.2: every thickening is open relative to its containing
partial wedge core. -/
private lemma finiteWedgeThickening_isOpen
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i)) (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (J K : Finset ι) :
    IsOpen (Subtype.val ⁻¹' finiteWedgeThickening S p W J K :
      Set (finiteWedgeCore S p K)) := by
  -- Rewrite the relative thickening as the preimage of the open complement of the tails.
  have hopen : IsOpen (finiteWedgeExcluded S W J K)ᶜ :=
    (finiteWedgeExcluded_isClosed S p W hW_open J K).isOpen_compl
  have heq :
      (Subtype.val ⁻¹' finiteWedgeThickening S p W J K :
          Set (finiteWedgeCore S p K)) =
        Subtype.val ⁻¹' (finiteWedgeExcluded S W J K)ᶜ := by
    ext x
    exact mem_finiteWedgeThickening_iff_not_mem_excluded S p W hpW J K x
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- Helper for Exercise 71.2: the two successor thickenings cover the enlarged partial
wedge core. -/
private lemma finiteWedgeThickening_insert_union
    {X : Type u} {ι : Type*} [DecidableEq ι]
    (S : ι → Set X) (p : X) (W : ∀ i, Set (S i))
    (J : Finset ι) (i : ι) :
    finiteWedgeThickening S p W {i} (insert i J) ∪
        finiteWedgeThickening S p W J (insert i J) =
      finiteWedgeCore S p (insert i J) := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact finiteWedgeThickening_subset_core S p W
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i J)) hx
    · exact finiteWedgeThickening_subset_core S p W (Finset.subset_insert i J) hx
  · intro hx
    rcases hx with hxp | hx
    · exact Or.inl (Set.mem_union_left _ (Set.mem_union_left _ hxp))
    · rw [Set.mem_iUnion₂] at hx
      obtain ⟨j, hj, hxS⟩ := hx
      rcases Finset.mem_insert.mp hj with hji | hjJ
      · subst j
        exact Or.inl (Set.mem_union_left _
          (summand_subset_finiteWedgeCore S p {i} (Finset.mem_singleton_self i) hxS))
      · exact Or.inr (Set.mem_union_left _
          (summand_subset_finiteWedgeCore S p J hjJ hxS))

/-- Helper for Exercise 71.2: the intersection of the two successor thickenings is the
all-neighborhood thickening. -/
private lemma finiteWedgeThickening_insert_inter
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (J : Finset ι) {i : ι} (hi : i ∉ J) :
    finiteWedgeThickening S p W {i} (insert i J) ∩
        finiteWedgeThickening S p W J (insert i J) =
      finiteWedgeThickening S p W ∅ (insert i J) := by
  ext x
  constructor
  · rintro ⟨hxU, hxV⟩
    rcases hxU with hxCore | hxNeighborhood
    · rcases hxCore with hxp | hxiUnion
      · exact Set.mem_union_left _ (Set.mem_union_left _ hxp)
      · rw [Set.mem_iUnion₂] at hxiUnion
        obtain ⟨k, hkSingleton, hxSk⟩ := hxiUnion
        have hki : k = i := Finset.mem_singleton.mp hkSingleton
        subst k
        rcases hxV with hxCoreJ | hxNeighborhoodI
        · rcases hxCoreJ with hxp | hxJ
          · exact Set.mem_union_left _ (Set.mem_union_left _ hxp)
          · rw [Set.mem_iUnion₂] at hxJ
            obtain ⟨j, hjJ, hxSj⟩ := hxJ
            have hij : i ≠ j := by
              intro hij
              subst j
              exact hi hjJ
            have hxp : x = p :=
              eq_point_of_mem_distinct_summands S p hij hxSk hxSj
            rw [hxp]
            exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton p))
        · rw [Set.mem_iUnion₂] at hxNeighborhoodI
          obtain ⟨j, hj, wj, hwj, hwjx⟩ := hxNeighborhoodI
          have hji : j = i := by
            rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hj).1 with hji | hjJ
            · exact hji
            · exact False.elim ((Finset.mem_sdiff.mp hj).2 hjJ)
          subst j
          exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
            ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self i J, Finset.notMem_empty i⟩,
              ⟨wj, hwj, hwjx⟩⟩⟩)
    · rw [Set.mem_iUnion₂] at hxNeighborhood
      obtain ⟨j, hj, wj, hwj, hwjx⟩ := hxNeighborhood
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2
        ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hj).1, Finset.notMem_empty j⟩,
          ⟨wj, hwj, hwjx⟩⟩⟩)
  · intro hxC
    rcases hxC with hxp | hxNeighborhood
    · constructor
      · exact Set.mem_union_left _
          (finiteWedgeCore_mono S p (Finset.empty_subset {i}) hxp)
      · exact Set.mem_union_left _
          (finiteWedgeCore_mono S p (Finset.empty_subset J) hxp)
    · rw [Set.mem_iUnion₂] at hxNeighborhood
      obtain ⟨j, hj, wj, hwj, hwjx⟩ := hxNeighborhood
      have hjK : j ∈ insert i J := (Finset.mem_sdiff.mp hj).1
      by_cases hji : j = i
      · subst j
        have hxi : x ∈ S i := by
          simpa only [← hwjx] using wj.property
        constructor
        · exact Set.mem_union_left _ (Set.mem_union_right _
            (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
              ⟨Finset.mem_singleton_self i, hxi⟩⟩))
        · exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
            ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self i J, hi⟩, ⟨wj, hwj, hwjx⟩⟩⟩)
      · have hjJ : j ∈ J := (Finset.mem_insert.mp hjK).resolve_left hji
        have hjSingleton : j ∉ ({i} : Finset ι) := by
          simpa only [Finset.mem_singleton] using hji
        have hxj : x ∈ S j := by
          simpa only [← hwjx] using wj.property
        constructor
        · exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2
            ⟨Finset.mem_sdiff.mpr ⟨hjK, hjSingleton⟩,
              ⟨wj, hwj, hwjx⟩⟩⟩)
        · exact Set.mem_union_left _ (Set.mem_union_right _
            (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2
              ⟨hjJ, hxj⟩⟩))

/-- Helper for Exercise 71.2: the open successor piece retaining the newly inserted
summand. -/
private def finiteWedgeSuccessorLeft
    {X : Type u} [TopologicalSpace X] {k : Type*} [DecidableEq k]
    (S : k → Set X) (p : X) (W : ∀ i, Set (S i)) (J : Finset k) (i : k) :
    Set (finiteWedgeCore S p (insert i J)) :=
  Subtype.val ⁻¹' finiteWedgeThickening S p W {i} (insert i J)

/-- Helper for Exercise 71.2: the open successor piece retaining the previously
constructed partial core. -/
private def finiteWedgeSuccessorRight
    {X : Type u} [TopologicalSpace X] {k : Type*} [DecidableEq k]
    (S : k → Set X) (p : X) (W : ∀ i, Set (S i)) (J : Finset k) (i : k) :
    Set (finiteWedgeCore S p (insert i J)) :=
  Subtype.val ⁻¹' finiteWedgeThickening S p W J (insert i J)

/-- Helper for Exercise 71.2: the canonical partial-core point lies in the left
successor piece. -/
private lemma finiteWedgeCorePoint_mem_successorLeft
    {X : Type u} [TopologicalSpace X] {k : Type*} [DecidableEq k]
    (S : k → Set X) (p : X) (W : ∀ i, Set (S i)) (J : Finset k) (i : k) :
    finiteWedgeCorePoint S p (insert i J) ∈
      finiteWedgeSuccessorLeft S p W J i := by
  -- The wedge point lies in the retained singleton core of the left thickening.
  exact finiteWedgeCore_subset_thickening S p W {i} (insert i J)
    (point_mem_finiteWedgeCore S p {i})

/-- Helper for Exercise 71.2: the canonical partial-core point lies in the right
successor piece. -/
private lemma finiteWedgeCorePoint_mem_successorRight
    {X : Type u} [TopologicalSpace X] {k : Type*} [DecidableEq k]
    (S : k → Set X) (p : X) (W : ∀ i, Set (S i)) (J : Finset k) (i : k) :
    finiteWedgeCorePoint S p (insert i J) ∈
      finiteWedgeSuccessorRight S p W J i := by
  -- The wedge point also lies in the retained old core of the right thickening.
  exact finiteWedgeCore_subset_thickening S p W J (insert i J)
    (point_mem_finiteWedgeCore S p J)

/-- Helper for Exercise 71.2: the canonical partial-core point lies in the
intersection of the successor pieces. -/
private lemma finiteWedgeCorePoint_mem_successorIntersection
    {X : Type u} [TopologicalSpace X] {k : Type*} [DecidableEq k]
    (S : k → Set X) (p : X) (W : ∀ i, Set (S i)) (J : Finset k) (i : k) :
    finiteWedgeCorePoint S p (insert i J) ∈
      finiteWedgeSuccessorLeft S p W J i ∩
        finiteWedgeSuccessorRight S p W J i := by
  -- Pair the two canonical membership proofs at the common wedge point.
  exact ⟨finiteWedgeCorePoint_mem_successorLeft S p W J i,
    finiteWedgeCorePoint_mem_successorRight S p W J i⟩

/-- Helper for Exercise 71.2: the two successor pieces cover the enlarged partial
core. -/
private lemma finiteWedgeSuccessor_union
    {X : Type u} [TopologicalSpace X] {k : Type*} [DecidableEq k]
    (S : k → Set X) (p : X) (W : ∀ i, Set (S i)) (J : Finset k) (i : k) :
    finiteWedgeSuccessorLeft S p W J i ∪
        finiteWedgeSuccessorRight S p W J i = Set.univ := by
  ext x
  constructor
  · intro
    exact Set.mem_univ x
  · intro
    change x.1 ∈ finiteWedgeThickening S p W {i} (insert i J) ∪
      finiteWedgeThickening S p W J (insert i J)
    rw [finiteWedgeThickening_insert_union]
    exact x.property

/-- Helper for Exercise 71.2: the left successor piece is open in the enlarged
partial core. -/
private lemma finiteWedgeSuccessorLeft_isOpen
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i)) (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (J : Finset k) (i : k) : IsOpen (finiteWedgeSuccessorLeft S p W J i) := by
  -- This is the relative-openness theorem for the singleton-retaining thickening.
  exact finiteWedgeThickening_isOpen S p W hW_open hpW {i} (insert i J)

/-- Helper for Exercise 71.2: the right successor piece is open in the enlarged
partial core. -/
private lemma finiteWedgeSuccessorRight_isOpen
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i)) (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (J : Finset k) (i : k) : IsOpen (finiteWedgeSuccessorRight S p W J i) := by
  -- This is the relative-openness theorem for the old-core-retaining thickening.
  exact finiteWedgeThickening_isOpen S p W hW_open hpW J (insert i J)

/-- Helper for Exercise 71.2: a point of a thickening that lies in an unretained
summand belongs to that summand's chosen neighborhood. -/
private lemma mem_neighborhood_of_mem_thickening_summand
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (J K : Finset k) {i : k} (hiJ : i ∉ J) {x : X}
    (hxT : x ∈ finiteWedgeThickening S p W J K) (hxi : x ∈ S i) :
    (⟨x, hxi⟩ : S i) ∈ W i := by
  rcases hxT with hxCore | hxNeighborhood
  · -- On the retained core, an unretained summand can meet it only at the wedge point.
    rcases hxCore with hxp | hxSelected
    · have hxp' : x = p := Set.mem_singleton_iff.mp hxp
      subst x
      exact hpW i
    · rw [Set.mem_iUnion₂] at hxSelected
      obtain ⟨j, hjJ, hxj⟩ := hxSelected
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hiJ hjJ
      have hxp : x = p := eq_point_of_mem_distinct_summands S p hij hxi hxj
      have heq : (⟨x, hxi⟩ : S i) = ⟨p, h.point_mem i⟩ := by
        apply Subtype.ext
        exact hxp
      rw [heq]
      exact hpW i
  · -- On a neighborhood piece, either it is the same piece or the point is again `p`.
    rw [Set.mem_iUnion₂] at hxNeighborhood
    obtain ⟨j, hj, w, hwW, hwx⟩ := hxNeighborhood
    by_cases hij : i = j
    · subst j
      have heq : (⟨x, hxi⟩ : S i) = w := by
        apply Subtype.ext
        exact hwx.symm
      rw [heq]
      exact hwW
    · have hxj : x ∈ S j := by
        simpa only [← hwx] using w.property
      have hxp : x = p := eq_point_of_mem_distinct_summands S p hij hxi hxj
      have heq : (⟨x, hxi⟩ : S i) = ⟨p, h.point_mem i⟩ := by
        apply Subtype.ext
        exact hxp
      rw [heq]
      exact hpW i

/-- Helper for Exercise 71.2: a point of a relative thickening lying in a summand
outside the containing core is the wedge point. -/
private lemma eq_point_of_mem_thickening_summand_not_mem
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i)) (J K : Finset k) (hJK : J ⊆ K)
    {i : k} (hiK : i ∉ K)
    {x : X} (hxT : x ∈ finiteWedgeThickening S p W J K) (hxi : x ∈ S i) :
    x = p := by
  -- The thickening lies in the `K`-core, whose summands are all distinct from `i`.
  have hxK : x ∈ finiteWedgeCore S p K :=
    finiteWedgeThickening_subset_core S p W hJK hxT
  rcases hxK with hxp | hxSelected
  · exact Set.mem_singleton_iff.mp hxp
  · rw [Set.mem_iUnion₂] at hxSelected
    obtain ⟨j, hjK, hxj⟩ := hxSelected
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hiK hjK
    exact eq_point_of_mem_distinct_summands S p hij hxi hxj

/-- Helper for Exercise 71.2: an unselected summand meets a partial core only at
the wedge point. -/
private lemma eq_point_of_mem_core_summand_not_mem
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (J : Finset k) {i : k} (hiJ : i ∉ J) {x : X}
    (hxJ : x ∈ finiteWedgeCore S p J) (hxi : x ∈ S i) : x = p := by
  rcases hxJ with hxp | hxSelected
  · exact Set.mem_singleton_iff.mp hxp
  · rw [Set.mem_iUnion₂] at hxSelected
    obtain ⟨j, hjJ, hxj⟩ := hxSelected
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hiJ hjJ
    exact eq_point_of_mem_distinct_summands S p hij hxi hxj

/-- Helper for Exercise 71.2: every ambient point belongs to some summand of the
finite wedge cover. -/
private lemma exists_summand_mem
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p] (x : X) :
    ∃ i, x ∈ S i := by
  have hx : x ∈ ⋃ i, S i := by
    rw [h.covers]
    trivial
  exact Set.mem_iUnion.mp hx

/-- Helper for Exercise 71.2: expose concrete deformation-retraction data from the
propositional deformation-retract predicate. -/
private lemma nonemptyDeformationRetraction_of_isDeformationRetract
    {Y : Type*} [TopologicalSpace Y] {A : Set Y}
    (hA : Set.IsDeformationRetract A) :
    Nonempty (Set.DeformationRetraction A) := by
  -- Use the public characterization instead of unfolding the opaque predicate.
  rw [Set.isDeformationRetract_iff] at hA
  obtain ⟨r, ⟨H⟩⟩ := hA
  exact ⟨Set.DeformationRetraction.ofHomotopyRel r H⟩

/-- Helper for Exercise 71.2: choose concrete deformation-retraction data from each
neighborhood contraction hypothesis. -/
private noncomputable def chosenNeighborhoodDeformationRetraction
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (i : k) :
    Set.DeformationRetraction
      ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)) :=
  Classical.choice
    (nonemptyDeformationRetraction_of_isDeformationRetract (hW_retract i))

/-- Helper for Exercise 71.2: the closed summand piece on which one local pasted
homotopy is defined. -/
private def finiteWedgeHomotopyPiece
    {X : Type u} {k : Type*} [DecidableEq k]
    (S : k → Set X) (p : X) (W : ∀ i, Set (S i))
    (J K : Finset k) (i : k) :
    Set (unitInterval × finiteWedgeThickening S p W J K) :=
  {z | (z.2 : X) ∈ S i}

/-- Helper for Exercise 71.2: on a retained summand use the identity, and on an
unretained summand use its chosen contraction. -/
private noncomputable def finiteWedgeLocalHomotopy
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (i : k)
    (z : finiteWedgeHomotopyPiece S p W J K i) : X :=
  if hiJ : i ∈ J then z.1.2 else
    let xi : S i := ⟨z.1.2, z.2⟩
    let wi : W i := ⟨xi,
      mem_neighborhood_of_mem_thickening_summand S p W hpW J K hiJ
        z.1.2.property z.2⟩
    chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i |>.toHomotopyRel
      (z.1.1, wi)

/-- Helper for Exercise 71.2: expose the contraction formula on an unretained
summand without relying on definitional equality between subtype proofs. -/
private lemma finiteWedgeLocalHomotopy_of_not_mem
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (i : k) (hiJ : i ∉ J)
    (z : finiteWedgeHomotopyPiece S p W J K i) :
    finiteWedgeLocalHomotopy S p W hpW hW_retract J K i z =
      ((chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel
        (z.1.1, ⟨⟨z.1.2, z.2⟩,
          mem_neighborhood_of_mem_thickening_summand S p W hpW J K hiJ
            z.1.2.property z.2⟩)).1.1 := by
  -- Unfold once here so later rewrites remain insensitive to proof fields.
  simp only [finiteWedgeLocalHomotopy, dif_neg hiJ]

/-- Helper for Exercise 71.2: every local summand homotopy starts at its input
point. -/
private lemma finiteWedgeLocalHomotopy_zero
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (i : k)
    (x : finiteWedgeThickening S p W J K) (hxi : (x : X) ∈ S i) :
    finiteWedgeLocalHomotopy S p W hpW hW_retract J K i
      ⟨(0, x), hxi⟩ = x := by
  -- Retained pieces are stationary; every supplied contraction starts at the identity.
  by_cases hiJ : i ∈ J
  · simp only [finiteWedgeLocalHomotopy, dif_pos hiJ]
  · rw [finiteWedgeLocalHomotopy_of_not_mem S p W hpW hW_retract J K i hiJ]
    let input : W i :=
      ⟨⟨x, hxi⟩,
        mem_neighborhood_of_mem_thickening_summand S p W hpW J K hiJ
          x.property hxi⟩
    have hzero :=
      (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel.apply_zero
        input
    exact congrArg (fun y : W i ↦ y.1.1) hzero

/-- Helper for Exercise 71.2: every local summand homotopy remains in the relative
thickening. -/
private lemma finiteWedgeLocalHomotopy_mem_thickening
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) (i : k)
    (z : finiteWedgeHomotopyPiece S p W J K i) :
    finiteWedgeLocalHomotopy S p W hpW hW_retract J K i z ∈
      finiteWedgeThickening S p W J K := by
  by_cases hiJ : i ∈ J
  · -- Retained summands are fixed, so membership is inherited from the input.
    simpa only [finiteWedgeLocalHomotopy, dif_pos hiJ] using z.1.2.property
  · by_cases hiK : i ∈ K
    · -- A contracted point stays in `W i`, one of the neighborhood pieces of the thickening.
      apply Set.mem_union_right
      refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
        ⟨Finset.mem_sdiff.mpr ⟨hiK, hiJ⟩, ?_⟩⟩
      let moved : W i :=
        chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i |>.toHomotopyRel
          (z.1.1, ⟨⟨z.1.2, z.2⟩,
            mem_neighborhood_of_mem_thickening_summand S p W hpW J K hiJ
              z.1.2.property z.2⟩)
      refine ⟨moved, moved.property, ?_⟩
      exact (finiteWedgeLocalHomotopy_of_not_mem
        S p W hpW hW_retract J K i hiJ z).symm
    · -- A summand outside `K` meets the thickening only at `p`, which every
      -- neighborhood contraction fixes.
      have hxp : (z.1.2 : X) = p :=
        eq_point_of_mem_thickening_summand_not_mem S p W J K hJK hiK
          z.1.2.property z.2
      let q : W i := ⟨⟨p, h.point_mem i⟩, hpW i⟩
      let input : W i :=
        ⟨⟨z.1.2, z.2⟩,
          mem_neighborhood_of_mem_thickening_summand S p W hpW J K hiJ
            z.1.2.property z.2⟩
      have hinput : input = q := by
        apply Subtype.ext
        apply Subtype.ext
        exact hxp
      have hfixed :
          (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel
              (z.1.1, q) = q := by
        simpa only [ContinuousMap.id_apply] using
          (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel.eq_fst
            z.1.1 (Set.mem_singleton q)
      have hout : finiteWedgeLocalHomotopy S p W hpW hW_retract J K i z = p := by
        calc
          finiteWedgeLocalHomotopy S p W hpW hW_retract J K i z =
              (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i |>.toHomotopyRel
                (z.1.1, input)).1.1 :=
            finiteWedgeLocalHomotopy_of_not_mem
              S p W hpW hW_retract J K i hiJ z
          _ = q.1.1 := congrArg (fun y : W i ↦ y.1.1) <| by
            have hmoved :
                (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel
                  (z.1.1, input) = q := by
              rw [hinput]
              exact hfixed
            exact hmoved
          _ = p := rfl
      rw [hout]
      exact finiteWedgeCore_subset_thickening S p W J K
        (point_mem_finiteWedgeCore S p J)

/-- Helper for Exercise 71.2: each summandwise homotopy is continuous on its
closed summand piece. -/
private lemma continuous_finiteWedgeLocalHomotopy
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (i : k) :
    Continuous (finiteWedgeLocalHomotopy S p W hpW hW_retract J K i) := by
  unfold finiteWedgeLocalHomotopy
  split
  · fun_prop
  · let input : finiteWedgeHomotopyPiece S p W J K i → W i :=
      fun z ↦ ⟨⟨z.1.2, z.2⟩,
        mem_neighborhood_of_mem_thickening_summand S p W hpW J K ‹i ∉ J›
          z.1.2.property z.2⟩
    have hinput : Continuous input := by
      apply continuous_induced_rng.2
      apply continuous_induced_rng.2
      fun_prop
    have hpair : Continuous (fun z : finiteWedgeHomotopyPiece S p W J K i ↦
        (z.1.1, input z)) := by
      fun_prop
    have hmoved : Continuous (fun z : finiteWedgeHomotopyPiece S p W J K i ↦
        (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel
          (z.1.1, input z)) := by
      exact map_continuous
        (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel |>.comp
          hpair
    exact continuous_subtype_val.comp (continuous_subtype_val.comp hmoved)

/-- Helper for Exercise 71.2: a local summand homotopy based at the wedge point
stays at the wedge point. -/
private lemma finiteWedgeLocalHomotopy_eq_point
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (i : k)
    (z : finiteWedgeHomotopyPiece S p W J K i) (hzp : (z.1.2 : X) = p) :
    finiteWedgeLocalHomotopy S p W hpW hW_retract J K i z = p := by
  by_cases hiJ : i ∈ J
  · simpa only [finiteWedgeLocalHomotopy, dif_pos hiJ] using hzp
  · rw [finiteWedgeLocalHomotopy_of_not_mem S p W hpW hW_retract J K i hiJ]
    let q : W i := ⟨⟨p, h.point_mem i⟩, hpW i⟩
    let input : W i :=
      ⟨⟨z.1.2, z.2⟩,
        mem_neighborhood_of_mem_thickening_summand S p W hpW J K hiJ
          z.1.2.property z.2⟩
    have hinput : input = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hzp
    have hfixed :
        (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel
            (z.1.1, q) = q := by
      simpa only [ContinuousMap.id_apply] using
        (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel.eq_fst
          z.1.1 (Set.mem_singleton q)
    have hmoved :
        (chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i).toHomotopyRel
            (z.1.1, input) = q := by
      rw [hinput]
      exact hfixed
    exact (congrArg (fun y : W i ↦ y.1.1) hmoved).trans rfl

/-- Helper for Exercise 71.2: package a summandwise homotopy as a continuous map
into the relative thickening. -/
private noncomputable def finiteWedgeLocalHomotopyMap
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) (i : k) :
    C(finiteWedgeHomotopyPiece S p W J K i,
      finiteWedgeThickening S p W J K) :=
  { toFun := fun z ↦
      ⟨finiteWedgeLocalHomotopy S p W hpW hW_retract J K i z,
        finiteWedgeLocalHomotopy_mem_thickening
          S p W hpW hW_retract J K hJK i z⟩
    continuous_toFun := continuous_induced_rng.2
      (continuous_finiteWedgeLocalHomotopy S p W hpW hW_retract J K i) }

/-- Helper for Exercise 71.2: coercing a packaged local homotopy exposes its
underlying ambient-space formula. -/
private lemma finiteWedgeLocalHomotopyMap_coe
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) (i : k)
    (z : finiteWedgeHomotopyPiece S p W J K i) :
    (finiteWedgeLocalHomotopyMap S p W hpW hW_retract J K hJK i z : X) =
      finiteWedgeLocalHomotopy S p W hpW hW_retract J K i z := by
  -- Both sides are the same ambient value; membership proofs are deliberately hidden here.
  rfl

/-- Helper for Exercise 71.2: every summand piece in the homotopy domain is
closed. -/
private lemma finiteWedgeHomotopyPiece_isClosed
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i)) (J K : Finset k) (i : k) :
    IsClosed (finiteWedgeHomotopyPiece S p W J K i) := by
  -- It is the preimage of the closed summand under the spatial projection.
  exact (h.isClosed i).preimage <| by fun_prop

/-- Helper for Exercise 71.2: the summand pieces cover the complete homotopy
domain. -/
private lemma finiteWedgeHomotopyPiece_iUnion
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i)) (J K : Finset k) :
    ⋃ i, finiteWedgeHomotopyPiece S p W J K i = Set.univ := by
  ext z
  simp only [finiteWedgeHomotopyPiece, Set.mem_iUnion, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  have hz : (z.2 : X) ∈ ⋃ i, S i := by
    rw [h.covers]
    trivial
  exact Set.mem_iUnion.mp hz

/-- Helper for Exercise 71.2: local summand homotopies agree on pairwise
intersections. -/
private lemma finiteWedgeLocalHomotopyMap_compatible
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K)
    (i j : k) (z : unitInterval × finiteWedgeThickening S p W J K)
    (hzi : z ∈ finiteWedgeHomotopyPiece S p W J K i)
    (hzj : z ∈ finiteWedgeHomotopyPiece S p W J K j) :
    finiteWedgeLocalHomotopyMap S p W hpW hW_retract J K hJK i ⟨z, hzi⟩ =
      finiteWedgeLocalHomotopyMap S p W hpW hW_retract J K hJK j ⟨z, hzj⟩ := by
  apply Subtype.ext
  by_cases hij : i = j
  · subst j
    rfl
  · -- Distinct summands meet only at `p`, and each local contraction fixes `p`.
    have hzp : (z.2 : X) = p :=
      eq_point_of_mem_distinct_summands S p hij hzi hzj
    exact (finiteWedgeLocalHomotopy_eq_point
      S p W hpW hW_retract J K i ⟨z, hzi⟩ hzp).trans
        (finiteWedgeLocalHomotopy_eq_point
          S p W hpW hW_retract J K j ⟨z, hzj⟩ hzp).symm

/-- Helper for Exercise 71.2: glue the compatible local contractions over the
finite closed summand cover. -/
private noncomputable def finiteWedgePastedHomotopy
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    unitInterval × finiteWedgeThickening S p W J K →
      finiteWedgeThickening S p W J K :=
  Set.liftCover (finiteWedgeHomotopyPiece S p W J K)
    (fun i ↦ finiteWedgeLocalHomotopyMap S p W hpW hW_retract J K hJK i)
    (finiteWedgeLocalHomotopyMap_compatible S p W hpW hW_retract J K hJK)
    (finiteWedgeHomotopyPiece_iUnion S p W J K)

/-- Helper for Exercise 71.2: the pasted homotopy is continuous by finite closed
pasting. -/
private lemma continuous_finiteWedgePastedHomotopy
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    Continuous (finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK) := by
  -- Restriction to each closed piece is its already-continuous local map.
  refine (locallyFinite_of_finite (finiteWedgeHomotopyPiece S p W J K)).continuous
    (finiteWedgeHomotopyPiece_iUnion S p W J K)
    (finiteWedgeHomotopyPiece_isClosed S p W J K) ?_
  intro i
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict :
      (finiteWedgeHomotopyPiece S p W J K i).restrict
          (finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK) =
        finiteWedgeLocalHomotopyMap S p W hpW hW_retract J K hJK i := by
    funext z
    change finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK z =
      finiteWedgeLocalHomotopyMap S p W hpW hW_retract J K hJK i z
    unfold finiteWedgePastedHomotopy
    exact Set.liftCover_coe z
  rw [hrestrict]
  exact map_continuous _

/-- Helper for Exercise 71.2: on any summand piece, the pasted homotopy computes
as the corresponding local homotopy. -/
private lemma finiteWedgePastedHomotopy_of_mem
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) (i : k)
    (z : unitInterval × finiteWedgeThickening S p W J K)
    (hzi : z ∈ finiteWedgeHomotopyPiece S p W J K i) :
    finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK z =
      finiteWedgeLocalHomotopyMap S p W hpW hW_retract J K hJK i ⟨z, hzi⟩ := by
  -- This is the computation rule of `Set.liftCover`.
  unfold finiteWedgePastedHomotopy
  exact Set.liftCover_of_mem hzi

/-- Helper for Exercise 71.2: the pasted homotopy starts at the identity. -/
private lemma finiteWedgePastedHomotopy_zero
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K)
    (x : finiteWedgeThickening S p W J K) :
    finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK (0, x) = x := by
  obtain ⟨i, hxi⟩ := exists_summand_mem S p (x : X)
  have hpaste := finiteWedgePastedHomotopy_of_mem
    S p W hpW hW_retract J K hJK i (0, x) hxi
  apply Subtype.ext
  exact (congrArg (fun y : finiteWedgeThickening S p W J K ↦ (y : X)) hpaste).trans
    (finiteWedgeLocalHomotopy_zero S p W hpW hW_retract J K i x hxi)

/-- Helper for Exercise 71.2: the endpoint of an unretained local contraction is
the wedge point. -/
private lemma finiteWedgeLocalHomotopy_one_eq_point
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (i : k) (hiJ : i ∉ J)
    (x : finiteWedgeThickening S p W J K) (hxi : (x : X) ∈ S i) :
    finiteWedgeLocalHomotopy S p W hpW hW_retract J K i
      ⟨(1, x), hxi⟩ = p := by
  rw [finiteWedgeLocalHomotopy_of_not_mem S p W hpW hW_retract J K i hiJ]
  let H := chosenNeighborhoodDeformationRetraction S p W hpW hW_retract i
  let q : W i := ⟨⟨p, h.point_mem i⟩, hpW i⟩
  let input : W i :=
    ⟨⟨x, hxi⟩,
      mem_neighborhood_of_mem_thickening_summand S p W hpW J K hiJ
        x.property hxi⟩
  have hret : (H.toRetraction.apply input : W i) = q :=
    Set.mem_singleton_iff.mp (H.toRetraction.apply input).property
  have hend : H.toHomotopyRel (1, input) = q := by
    calc
      H.toHomotopyRel (1, input) = H.toRetraction.toAmbient input :=
        H.toHomotopyRel.apply_one input
      _ = (H.toRetraction.apply input : W i) :=
        Set.Retraction.toAmbient_apply H.toRetraction input
      _ = q := hret
  exact (congrArg (fun y : W i ↦ y.1.1) hend).trans rfl

/-- Helper for Exercise 71.2: the pasted homotopy fixes every point of the
retained partial core throughout. -/
private lemma finiteWedgePastedHomotopy_fixed
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) (t : unitInterval)
    (x : finiteWedgeThickening S p W J K)
    (hxJ : (x : X) ∈ finiteWedgeCore S p J) :
    finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK (t, x) = x := by
  obtain ⟨i, hxi⟩ := exists_summand_mem S p (x : X)
  have hpaste := finiteWedgePastedHomotopy_of_mem
    S p W hpW hW_retract J K hJK i (t, x) hxi
  apply Subtype.ext
  rw [congrArg (fun y : finiteWedgeThickening S p W J K ↦ (y : X)) hpaste,
    finiteWedgeLocalHomotopyMap_coe]
  by_cases hiJ : i ∈ J
  · simp only [finiteWedgeLocalHomotopy, dif_pos hiJ]
  · have hxp := eq_point_of_mem_core_summand_not_mem S p J hiJ hxJ hxi
    exact (finiteWedgeLocalHomotopy_eq_point
      S p W hpW hW_retract J K i ⟨(t, x), hxi⟩ hxp).trans hxp.symm

/-- Helper for Exercise 71.2: at time one, the pasted homotopy lands in the
retained partial core. -/
private lemma finiteWedgePastedHomotopy_one_mem_core
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K)
    (x : finiteWedgeThickening S p W J K) :
    (finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK (1, x) : X) ∈
      finiteWedgeCore S p J := by
  obtain ⟨i, hxi⟩ := exists_summand_mem S p (x : X)
  have hpaste := finiteWedgePastedHomotopy_of_mem
    S p W hpW hW_retract J K hJK i (1, x) hxi
  rw [congrArg (fun y : finiteWedgeThickening S p W J K ↦ (y : X)) hpaste,
    finiteWedgeLocalHomotopyMap_coe]
  by_cases hiJ : i ∈ J
  · simpa only [finiteWedgeLocalHomotopyMap, finiteWedgeLocalHomotopy, dif_pos hiJ] using
      summand_subset_finiteWedgeCore S p J hiJ hxi
  · rw [finiteWedgeLocalHomotopy_one_eq_point S p W hpW hW_retract J K i hiJ x hxi]
    exact point_mem_finiteWedgeCore S p J

/-- Helper for Exercise 71.2: the time-one map of the pasted homotopy is
continuous. -/
private lemma continuous_finiteWedgePastedEndpoint
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    Continuous (fun x : finiteWedgeThickening S p W J K ↦
      finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK (1, x)) := by
  -- Restrict the continuous two-variable homotopy to the time-one slice.
  exact (continuous_finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK).comp <| by
    fun_prop

/-- Helper for Exercise 71.2: the pasted endpoint, bundled as a map into the
retained partial core. -/
private noncomputable def finiteWedgePastedRetractionMap
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    C(finiteWedgeThickening S p W J K,
      (Subtype.val ⁻¹' finiteWedgeCore S p J :
        Set (finiteWedgeThickening S p W J K))) :=
  { toFun := fun x ↦
      ⟨finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK (1, x),
        finiteWedgePastedHomotopy_one_mem_core
          S p W hpW hW_retract J K hJK x⟩
    continuous_toFun := continuous_induced_rng.2
      (continuous_finiteWedgePastedEndpoint S p W hpW hW_retract J K hJK) }

/-- Helper for Exercise 71.2: the pasted endpoint map is a left inverse to the
partial-core inclusion. -/
private lemma finiteWedgePastedRetractionMap_leftInverse
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    Function.LeftInverse
      (finiteWedgePastedRetractionMap S p W hpW hW_retract J K hJK)
      Subtype.val := by
  intro x
  apply Subtype.ext
  exact finiteWedgePastedHomotopy_fixed
    S p W hpW hW_retract J K hJK 1 x.1 x.2

/-- Helper for Exercise 71.2: the endpoint of the pasted homotopy defines a
retraction onto the retained partial core. -/
private noncomputable def finiteWedgePastedRetraction
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    Set.Retraction
      (Subtype.val ⁻¹' finiteWedgeCore S p J :
        Set (finiteWedgeThickening S p W J K)) :=
  Set.Retraction.ofContinuousMap
    (finiteWedgePastedRetractionMap S p W hpW hW_retract J K hJK)
    (finiteWedgePastedRetractionMap_leftInverse S p W hpW hW_retract J K hJK)

/-- Helper for Exercise 71.2: the ambient endpoint of the pasted retraction is
the time-one slice of the pasted homotopy. -/
private lemma finiteWedgePastedRetraction_toAmbient
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K)
    (x : finiteWedgeThickening S p W J K) :
    (finiteWedgePastedRetraction S p W hpW hW_retract J K hJK).toAmbient x =
      finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK (1, x) := by
  -- Push the comparison to the ambient carrier before exposing the short endpoint map.
  rw [Set.Retraction.toAmbient_apply]
  rfl

/-- Helper for Exercise 71.2: the pasted contraction is a relative homotopy from
the identity to its endpoint retraction. -/
private noncomputable def finiteWedgePastedHomotopyRel
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (finiteWedgeThickening S p W J K))
      (finiteWedgePastedRetraction S p W hpW hW_retract J K hJK).toAmbient
      (Subtype.val ⁻¹' finiteWedgeCore S p J :
        Set (finiteWedgeThickening S p W J K)) :=
  { toFun := finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK
    continuous_toFun :=
      continuous_finiteWedgePastedHomotopy S p W hpW hW_retract J K hJK
    map_zero_left := finiteWedgePastedHomotopy_zero S p W hpW hW_retract J K hJK
    map_one_left := fun x ↦
      (finiteWedgePastedRetraction_toAmbient S p W hpW hW_retract J K hJK x).symm
    prop' := finiteWedgePastedHomotopy_fixed S p W hpW hW_retract J K hJK }

/-- Helper for Exercise 71.2: every relative thickening deformation retracts
onto its retained partial core. -/
private lemma finiteWedgeThickening_deformationRetractsToCore
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J K : Finset k) (hJK : J ⊆ K) :
    Set.IsDeformationRetract
      (Subtype.val ⁻¹' finiteWedgeCore S p J :
        Set (finiteWedgeThickening S p W J K)) := by
  -- Package the retraction and the pasted relative homotopy through the public criterion.
  rw [Set.isDeformationRetract_iff]
  exact ⟨finiteWedgePastedRetraction S p W hpW hW_retract J K hJK,
    ⟨finiteWedgePastedHomotopyRel S p W hpW hW_retract J K hJK⟩⟩

/-- Helper for Exercise 71.2: reduced words with the same underlying list are equal. -/
private lemma reducedWord_eq_of_toList_eq
    {G : Type*} {k : Type*} [Group G] {H : k → Subgroup G}
    {w₁ w₂ : Subgroup.ReducedWord H} (hlist : w₁.toList = w₂.toList) :
    w₁ = w₂ := by
  -- All remaining fields in the two word structures are proof-valued.
  cases w₁ with
  | mk toWord₁ neOne₁ chain₁ =>
      cases w₂ with
      | mk toWord₂ neOne₂ chain₂ =>
          cases toWord₁ with
          | mk list₁ mem₁ =>
              cases toWord₂ with
              | mk list₂ mem₂ =>
                  dsimp only at hlist
                  subst list₂
                  rfl

/-
/-- Helper for Exercise 71.2: a multiplicative equivalence transports an internal
free-product decomposition to the images of its factors. -/
private lemma Subgroup.IsFreeProduct.mapMulEquiv
    {G G' : Type*} {k : Type*} [Group G] [Group G']
    {H : k → Subgroup G} (hfree : Subgroup.IsFreeProduct H) (e : G ≃* G') :
    Subgroup.IsFreeProduct (fun i ↦ (H i).map e.toMonoidHom) := by
  rw [Subgroup.isFreeProduct_iff] at hfree ⊢
  refine ⟨?_, ?_⟩
  · -- Equivalences preserve trivial intersections of distinct factors.
    intro i j hij
    rw [Subgroup.disjoint_def]
    rintro y ⟨x, hxi, hxy⟩ ⟨z, hzj, hzy⟩
    have hxz' : x = z := e.injective (hxy.trans hzy.symm)
    subst z
    have hxbot : x ∈ (⊥ : Subgroup G) := (hfree.1 hij).le_bot ⟨hxi, hzj⟩
    have hxone : x = 1 := by
      simpa only [Subgroup.mem_bot] using hxbot
    rw [← hxy, hxone, map_one]
  · intro y
    -- Map the unique reduced representative of `e.symm y` letter by letter.
    obtain ⟨w, hwprod, hwunique⟩ := hfree.2 (e.symm y)
    have hmem : ∀ x ∈ w.toList.map e, ∃ i, x ∈ (H i).map e.toMonoidHom := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨i, hzi⟩ := w.toWord.mem_subgroup z hz
      exact ⟨i, Subgroup.mem_map_of_mem e.toMonoidHom hzi⟩
    have hne : ∀ x ∈ w.toList.map e, x ≠ 1 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact e.map_ne_one_iff.mpr (w.ne_one z hz)
    have hchain :
        (w.toList.map e).IsChain (fun x z ↦
          ∀ i, ¬ (x ∈ (H i).map e.toMonoidHom ∧ z ∈ (H i).map e.toMonoidHom)) := by
      rw [List.isChain_map]
      exact w.chain_separated.imp fun x z hxz i hi ↦ hxz i
        ⟨(Subgroup.mem_map_iff_mem e.injective).mp hi.1,
          (Subgroup.mem_map_iff_mem e.injective).mp hi.2⟩
    let mapped := Subgroup.ReducedWord.ofList
      (fun i ↦ (H i).map e.toMonoidHom) (w.toList.map e) hmem hne hchain
    have hmappedProd : mapped.prod = y := by
      rw [Subgroup.ReducedWord.prod_def, Subgroup.ReducedWord.toList_ofList,
        ← map_list_prod, ← Subgroup.ReducedWord.prod_def H w, hwprod,
        e.apply_symm_apply]
    refine ⟨mapped, hmappedProd, ?_⟩
    intro other hotherProd
    -- Pull any competing target word back through the inverse equivalence.
    have hbackMem : ∀ x ∈ other.toList.map e.symm, ∃ i, x ∈ H i := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨i, hzi⟩ := other.toWord.mem_subgroup z hz
      exact ⟨i, (Subgroup.mem_map_equiv.mp hzi)⟩
    have hbackNe : ∀ x ∈ other.toList.map e.symm, x ≠ 1 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact e.symm.map_ne_one_iff.mpr (other.ne_one z hz)
    have hbackChain :
        (other.toList.map e.symm).IsChain
          (fun x z ↦ ∀ i, ¬ (x ∈ H i ∧ z ∈ H i)) := by
      rw [List.isChain_map]
      apply other.chain_separated.imp
      intro x z hxz i hi
      apply hxz i
      have hxmem : e (e.symm x) ∈ (H i).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hi.1
      have hzmem : e (e.symm z) ∈ (H i).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hi.2
      simpa only [e.apply_symm_apply] using And.intro hxmem hzmem
    let back := Subgroup.ReducedWord.ofList H (other.toList.map e.symm)
      hbackMem hbackNe hbackChain
    have hbackProd : back.prod = e.symm y := by
      rw [Subgroup.ReducedWord.prod_def, Subgroup.ReducedWord.toList_ofList,
        ← map_list_prod,
        ← Subgroup.ReducedWord.prod_def (fun i ↦ (H i).map e.toMonoidHom) other,
        hotherProd]
    have hbackEq : back = w := hwunique back hbackProd
    have hlistBack : other.toList.map e.symm = w.toList := by
      simpa only [back, Subgroup.ReducedWord.toList_ofList] using
        congrArg (fun q : Subgroup.ReducedWord H ↦ q.toList) hbackEq
    have hlist : other.toList = w.toList.map e := by
      have hmappedLists := congrArg (List.map e) hlistBack
      have hroundtrip : (other.toList.map e.symm).map e = other.toList := by
        have hmapComp :
            other.toList.map (e ∘ e.symm) = other.toList.map id := by
          apply List.map_congr_left
          intro z hz
          exact e.apply_symm_apply z
        have hmapMap :
            (other.toList.map e.symm).map e = other.toList.map (e ∘ e.symm) :=
          List.map_map
        have hmapId : other.toList.map id = other.toList := List.map_id other.toList
        calc
          (other.toList.map e.symm).map e = other.toList.map (e ∘ e.symm) := hmapMap
          _ = other.toList.map id := hmapComp
          _ = other.toList := hmapId
      calc
        other.toList = (other.toList.map e.symm).map e := hroundtrip.symm
        _ = w.toList.map e := hmappedLists
    exact reducedWord_eq_of_toList_eq hlist
-/

/-- Helper for Exercise 71.2: reindexing a family by an equivalence preserves an internal
free-product decomposition. -/
private lemma Subgroup.IsFreeProduct.reindex
    {G : Type*} {k l : Type*} [Group G] {H : k → Subgroup G}
    (hfree : Subgroup.IsFreeProduct H) (e : l ≃ k) :
    Subgroup.IsFreeProduct (fun j ↦ H (e j)) := by
  rw [Subgroup.isFreeProduct_iff] at hfree ⊢
  refine ⟨?_, ?_⟩
  · -- Pairwise disjointness is unchanged after relabeling by an injection.
    intro i j hij
    exact hfree.1 (e.injective.ne hij)
  · intro x
    obtain ⟨w, hwprod, hwunique⟩ := hfree.2 x
    have hmem : ∀ y ∈ w.toList, ∃ j, y ∈ H (e j) := by
      intro y hy
      obtain ⟨i, hyi⟩ := w.toWord.mem_subgroup y hy
      have hyi' : y ∈ H (e (e.symm i)) := by
        simpa only [e.apply_symm_apply] using hyi
      exact ⟨e.symm i, hyi'⟩
    have hchain :
        w.toList.IsChain (fun y z ↦ ∀ j, ¬ (y ∈ H (e j) ∧ z ∈ H (e j))) := by
      exact w.chain_separated.imp fun y z hyz j ↦ hyz (e j)
    let reindexed := Subgroup.ReducedWord.ofList (fun j ↦ H (e j)) w.toList
      hmem w.ne_one hchain
    have hreindexedProd : reindexed.prod = x := by
      simpa only [reindexed, Subgroup.ReducedWord.prod_def,
        Subgroup.ReducedWord.toList_ofList] using hwprod
    refine ⟨reindexed, hreindexedProd, ?_⟩
    intro other hother
    have hotherMem : ∀ y ∈ other.toList, ∃ i, y ∈ H i := by
      intro y hy
      obtain ⟨j, hyj⟩ := other.toWord.mem_subgroup y hy
      exact ⟨e j, hyj⟩
    have hotherChain :
        other.toList.IsChain (fun y z ↦ ∀ i, ¬ (y ∈ H i ∧ z ∈ H i)) := by
      apply other.chain_separated.imp
      intro y z hyz i hi
      apply hyz (e.symm i)
      simpa only [e.apply_symm_apply] using hi
    let original := Subgroup.ReducedWord.ofList H other.toList
      hotherMem other.ne_one hotherChain
    have horiginalProd : original.prod = x := by
      simpa only [original, Subgroup.ReducedWord.prod_def,
        Subgroup.ReducedWord.toList_ofList] using hother
    have horiginal : original = w := hwunique original horiginalProd
    have hlist : other.toList = w.toList := by
      simpa only [original, Subgroup.ReducedWord.toList_ofList] using
        congrArg (fun q : Subgroup.ReducedWord H ↦ q.toList) horiginal
    exact reducedWord_eq_of_toList_eq hlist

/-- Helper for Exercise 71.2: postcomposition by a multiplicative equivalence preserves
an external free-product decomposition. -/
private lemma MonoidHom.IsExternalFreeProduct.compMulEquiv
    {k : Type*} {G : k → Type*} {H H' : Type*}
    [∀ i, Group (G i)] [Group H] [Group H']
    {f : ∀ i, G i →* H} (hfree : MonoidHom.IsExternalFreeProduct f)
    (e : H ≃* H') :
    MonoidHom.IsExternalFreeProduct (fun i ↦ e.toMonoidHom.comp (f i)) := by
  refine ⟨fun i ↦ e.injective.comp (hfree.injective i), ?_⟩
  -- The new ranges are precisely the images of the old factor ranges.
  simpa only [MonoidHom.range_comp] using hfree.isFreeProduct.mapMulEquiv e

/-- Helper for Exercise 71.2: relabeling the factors by an equivalence preserves an
external free-product decomposition. -/
private lemma MonoidHom.IsExternalFreeProduct.reindex
    {k l : Type*} {G : k → Type*} {H : Type*}
    [∀ i, Group (G i)] [Group H] {f : ∀ i, G i →* H}
    (hfree : MonoidHom.IsExternalFreeProduct f) (e : l ≃ k) :
    MonoidHom.IsExternalFreeProduct (fun j ↦ f (e j)) := by
  refine ⟨fun j ↦ hfree.injective (e j), ?_⟩
  exact hfree.isFreeProduct.reindex e

/-- Helper for Exercise 71.2: relabeling the factors and precomposing each factor map
with a multiplicative equivalence preserves an external free-product decomposition. -/
private lemma MonoidHom.IsExternalFreeProduct.reindexCompMulEquiv
    {k l : Type*} {G : k → Type*} {G' : l → Type*} {H : Type*}
    [∀ i, Group (G i)] [∀ j, Group (G' j)] [Group H]
    {f : ∀ i, G i →* H} (hfree : MonoidHom.IsExternalFreeProduct f)
    (e : l ≃ k) (φ : ∀ j, G' j ≃* G (e j)) :
    MonoidHom.IsExternalFreeProduct
      (fun j ↦ (f (e j)).comp (φ j).toMonoidHom) := by
  refine ⟨fun j ↦ (hfree.injective (e j)).comp (φ j).injective, ?_⟩
  -- Surjectivity of each equivalence leaves the factor range unchanged, so only the
  -- already-proved index relabeling remains.
  have hrange (j : l) :
      ((f (e j)).comp (φ j).toMonoidHom).range = (f (e j)).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Set.mem_range_self (φ j y)
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (φ j).surjective y
      exact Set.mem_range_self x
  simpa only [hrange] using hfree.isFreeProduct.reindex e

/-- Helper for Exercise 71.2: bijectivity of the canonical indexed-coproduct map
exhibits its target as the external free product. -/
private lemma MonoidHom.isExternalFreeProduct_of_coprodLift_bijective
    {k : Type*} {G : k → Type*} {H : Type*}
    [∀ i, Group (G i)] [Group H] (f : ∀ i, G i →* H)
    (hbij : Function.Bijective (Monoid.CoprodI.lift f)) :
    MonoidHom.IsExternalFreeProduct f := by
  let e : Monoid.CoprodI G ≃* H := MulEquiv.ofBijective (Monoid.CoprodI.lift f) hbij
  have hcanonical := (Monoid.CoprodI.canonicalIsExternalFreeProduct G).compMulEquiv e
  have hgenerators : (fun i ↦ e.toMonoidHom.comp
      (Monoid.CoprodI.of : G i →* Monoid.CoprodI G)) = f := by
    funext i
    exact Monoid.CoprodI.lift_comp_of f i
  -- The transported canonical inclusions agree with `f` on every factor.
  rw [hgenerators] at hcanonical
  exact hcanonical

/-- Helper for Exercise 71.2: a pushout of two groups over a subsingleton group is
realized by the canonical binary free-product lift. -/
private lemma Monoid.Coprod.lift_bijective_of_isPushout_of_subsingleton
    {Z A B P : Type u} [Group Z] [Group A] [Group B] [Group P] [Subsingleton Z]
    (f : Z →* A) (g : Z →* B) (inl : A →* P) (inr : B →* P)
    (hpush : IsPushout (GrpCat.ofHom f) (GrpCat.ofHom g)
      (GrpCat.ofHom inl) (GrpCat.ofHom inr)) :
    Function.Bijective (Monoid.Coprod.lift inl inr) := by
  have hcomm :
      GrpCat.ofHom f ≫
          GrpCat.ofHom (Monoid.Coprod.inl : A →* Monoid.Coprod A B) =
        GrpCat.ofHom g ≫
          GrpCat.ofHom (Monoid.Coprod.inr : B →* Monoid.Coprod A B) := by
    apply GrpCat.hom_ext
    ext z
    rw [Subsingleton.elim z 1]
    simp only [map_one]
  let inv : GrpCat.of P ⟶ GrpCat.of (Monoid.Coprod A B) :=
    hpush.desc (GrpCat.ofHom Monoid.Coprod.inl)
      (GrpCat.ofHom Monoid.Coprod.inr) hcomm
  have hinl : GrpCat.ofHom inl ≫ inv = GrpCat.ofHom Monoid.Coprod.inl := by
    exact hpush.inl_desc _ _ hcomm
  have hinr : GrpCat.ofHom inr ≫ inv = GrpCat.ofHom Monoid.Coprod.inr := by
    exact hpush.inr_desc _ _ hcomm
  have hlift_inv :
      (inv.hom.comp (Monoid.Coprod.lift inl inr)) =
        MonoidHom.id (Monoid.Coprod A B) := by
    apply Monoid.Coprod.hom_ext
    · simpa only [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inl,
        MonoidHom.id_comp, GrpCat.hom_comp, GrpCat.hom_ofHom] using
        congrArg GrpCat.Hom.hom hinl
    · simpa only [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inr,
        MonoidHom.id_comp, GrpCat.hom_comp, GrpCat.hom_ofHom] using
        congrArg GrpCat.Hom.hom hinr
  have hinv_lift :
      GrpCat.ofHom (Monoid.Coprod.lift inl inr) ≫ inv =
        𝟙 (GrpCat.of (Monoid.Coprod A B)) := by
    apply GrpCat.hom_ext
    simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom, GrpCat.hom_id] using hlift_inv
  have hinv_lift' :
      inv ≫ GrpCat.ofHom (Monoid.Coprod.lift inl inr) = 𝟙 (GrpCat.of P) := by
    apply hpush.hom_ext
    · rw [← Category.assoc, hinl, ← GrpCat.ofHom_comp,
        Monoid.Coprod.lift_comp_inl, Category.comp_id]
    · rw [← Category.assoc, hinr, ← GrpCat.ofHom_comp,
        Monoid.Coprod.lift_comp_inr, Category.comp_id]
  have hinv_lift_hom :
      (Monoid.Coprod.lift inl inr).comp inv.hom = MonoidHom.id P := by
    simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom, GrpCat.hom_id] using
      congrArg GrpCat.Hom.hom hinv_lift'
  -- The pushout comparison has an explicit two-sided inverse, hence its underlying
  -- canonical free-product lift is bijective.
  have hleft : Function.LeftInverse inv.hom (Monoid.Coprod.lift inl inr) := by
    intro x
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using
      congrArg (fun q ↦ q x) hlift_inv
  have hright : Function.RightInverse inv.hom (Monoid.Coprod.lift inl inr) := by
    intro x
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using
      congrArg (fun q ↦ q x) hinv_lift_hom
  refine ⟨?_, ?_⟩
  · exact hleft.injective
  · exact hright.surjective

/-- Helper for Exercise 71.2: the indexed coproduct over `insert i J` is generated by
the new factor and the indexed coproduct over `J`. -/
private def coprodIInsertComparison
    {k : Type*} (G : k → Type*) [∀ i, Group (G i)] [DecidableEq k]
    (J : Finset k) (i : k) :
    Monoid.Coprod (G i) (Monoid.CoprodI (fun j : J ↦ G j)) →*
      Monoid.CoprodI (fun j : ↥(insert i J) ↦ G j) :=
  Monoid.Coprod.lift
    (@Monoid.CoprodI.of ↥(insert i J) (fun j : ↥(insert i J) ↦ G j) _
      ⟨i, Finset.mem_insert_self i J⟩)
    (Monoid.CoprodI.lift (fun j : J ↦
      @Monoid.CoprodI.of ↥(insert i J) (fun q : ↥(insert i J) ↦ G q) _
        ⟨j, Finset.mem_insert_of_mem j.property⟩))

/-- Helper for Exercise 71.2: an element of `insert i J` different from `i`
belongs to `J`. -/
private lemma mem_finset_of_mem_insert_ne
    {k : Type*} [DecidableEq k] (J : Finset k) (i : k)
    (j : ↥(insert i J)) (hji : j.1 ≠ i) : j.1 ∈ J := by
  -- Remove the new-index alternative from membership in the inserted finset.
  exact (Finset.mem_insert.mp j.property).resolve_left hji

/-- Helper for Exercise 71.2: split an indexed-coproduct factor over `insert i J`
according to whether it is the newly inserted factor. -/
private def coprodIInsertComparisonInv
    {k : Type*} (G : k → Type*) [∀ i, Group (G i)] [DecidableEq k]
    (J : Finset k) (i : k) :
    Monoid.CoprodI (fun j : ↥(insert i J) ↦ G j) →*
      Monoid.Coprod (G i) (Monoid.CoprodI (fun j : J ↦ G j)) :=
  Monoid.CoprodI.lift (fun j ↦
    if hji : j.1 = i then
      Monoid.Coprod.inl.comp (MulEquiv.cast hji).toMonoidHom
    else
      Monoid.Coprod.inr.comp
        (@Monoid.CoprodI.of J (fun q : J ↦ G q) _
          ⟨j.1, mem_finset_of_mem_insert_ne J i j hji⟩))

/-- Helper for Exercise 71.2: the comparison from the binary coproduct to the
indexed coproduct over an inserted finset is bijective. -/
private lemma coprodIInsertComparison_bijective
    {k : Type*} (G : k → Type*) [∀ i, Group (G i)] [DecidableEq k]
    (J : Finset k) {i : k} (hi : i ∉ J) :
    Function.Bijective (coprodIInsertComparison G J i) := by
  -- The factorwise split is a two-sided inverse to the comparison map.
  have hleft :
      (coprodIInsertComparisonInv G J i).comp
          (coprodIInsertComparison G J i) =
        MonoidHom.id (Monoid.Coprod (G i) (Monoid.CoprodI (fun j : J ↦ G j))) := by
    apply Monoid.Coprod.hom_ext
    · ext x
      simp only [coprodIInsertComparison, coprodIInsertComparisonInv,
        MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inl,
        Monoid.CoprodI.lift_of, MonoidHom.id_apply]
      split
      · rename_i hii
        have hproof : hii = True.intro := Subsingleton.elim _ _
        rw [hproof]
        rfl
      · rename_i hii
        exact False.elim (hii trivial)
    · apply Monoid.CoprodI.ext_hom
      intro j
      ext x
      have hji : (j : k) ≠ i := by
        intro hji
        apply hi
        exact hji ▸ j.property
      simp only [coprodIInsertComparison, coprodIInsertComparisonInv,
        MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inr,
        Monoid.CoprodI.lift_of, MonoidHom.id_apply]
      rw [dif_neg hji]
      rfl
  have hright :
      (coprodIInsertComparison G J i).comp
          (coprodIInsertComparisonInv G J i) =
        MonoidHom.id (Monoid.CoprodI (fun j : ↥(insert i J) ↦ G j)) := by
    apply Monoid.CoprodI.ext_hom
    intro j
    by_cases hji : j.1 = i
    · have hj : j = ⟨i, Finset.mem_insert_self i J⟩ := Subtype.ext hji
      subst j
      ext x
      simp only [coprodIInsertComparison, coprodIInsertComparisonInv,
        MonoidHom.comp_apply, Monoid.CoprodI.lift_of,
        MonoidHom.id_apply]
      split
      · rename_i hii
        have hproof : hii = True.intro := Subsingleton.elim _ _
        rw [hproof]
        rfl
      · rename_i hii
        exact False.elim (hii trivial)
    · ext x
      simp only [coprodIInsertComparison, coprodIInsertComparisonInv,
        MonoidHom.comp_apply, Monoid.CoprodI.lift_of,
        MonoidHom.id_apply]
      rw [dif_neg hji]
      rfl
  constructor
  · exact Function.LeftInverse.injective (fun x ↦
      DFunLike.congr_fun hleft x)
  · exact Function.RightInverse.surjective (fun x ↦
      DFunLike.congr_fun hright x)

/-- Helper for Exercise 71.2: compare an indexed coproduct with the same family
indexed by the subtype of the universal finset. -/
private def coprodIUnivComparison
    {k : Type*} [Fintype k] (G : k → Type*) [∀ i, Group (G i)] :
    Monoid.CoprodI G →* Monoid.CoprodI (fun i : (Finset.univ : Finset k) ↦ G i) :=
  Monoid.CoprodI.lift (fun i ↦
    @Monoid.CoprodI.of (Finset.univ : Finset k)
      (fun j : (Finset.univ : Finset k) ↦ G j) _ ⟨i, Finset.mem_univ i⟩)

/-- Helper for Exercise 71.2: the universal-finset comparison carries each canonical
factor inclusion to the corresponding subtype-indexed factor inclusion. -/
private lemma coprodIUnivComparison_comp_of
    {k : Type*} [Fintype k] (G : k → Type*) [∀ i, Group (G i)] (i : k) :
    (coprodIUnivComparison G).comp (@Monoid.CoprodI.of k G _ i) =
      @Monoid.CoprodI.of (Finset.univ : Finset k)
        (fun j : (Finset.univ : Finset k) ↦ G j) _ ⟨i, Finset.mem_univ i⟩ := by
  -- Compute the comparison on one canonical coproduct factor.
  exact Monoid.CoprodI.lift_comp_of _ i

/-- Helper for Exercise 71.2: forget the universal-finset membership proof on
the index of an indexed coproduct. -/
private def coprodIUnivComparisonInv
    {k : Type*} [Fintype k] (G : k → Type*) [∀ i, Group (G i)] :
    Monoid.CoprodI (fun i : (Finset.univ : Finset k) ↦ G i) →*
      Monoid.CoprodI G :=
  Monoid.CoprodI.lift (fun i ↦
    @Monoid.CoprodI.of k G _ i.1)

/-- Helper for Exercise 71.2: the universal-finset comparison of indexed
coproducts is bijective. -/
private lemma coprodIUnivComparison_bijective
    {k : Type*} [Fintype k] (G : k → Type*) [∀ i, Group (G i)] :
    Function.Bijective (coprodIUnivComparison G) := by
  have hleft :
      (coprodIUnivComparisonInv G).comp (coprodIUnivComparison G) =
        MonoidHom.id (Monoid.CoprodI G) := by
    apply Monoid.CoprodI.ext_hom
    intro i
    ext x
    rfl
  have hright :
      (coprodIUnivComparison G).comp (coprodIUnivComparisonInv G) =
        MonoidHom.id
          (Monoid.CoprodI (fun i : (Finset.univ : Finset k) ↦ G i)) := by
    apply Monoid.CoprodI.ext_hom
    intro i
    ext x
    rfl
  constructor
  · exact Function.LeftInverse.injective (fun x ↦
      DFunLike.congr_fun hleft x)
  · exact Function.RightInverse.surjective (fun x ↦
      DFunLike.congr_fun hright x)

/-- Helper for Exercise 71.2: the canonical map from the coproduct of the selected
summand fundamental groups to the fundamental group of their partial wedge core. -/
private noncomputable def finiteWedgePartialCoreCoprodMap
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p] (K : Finset k) :
    Monoid.CoprodI (fun i : K ↦ FundamentalGroup (S i) ⟨p, h.point_mem i⟩) →*
      FundamentalGroup (finiteWedgeCore S p K) ⟨p, point_mem_finiteWedgeCore S p K⟩ :=
  Monoid.CoprodI.lift (fun i ↦ FundamentalGroup.mapOfSubset
    (summand_subset_finiteWedgeCore S p K i.property) ⟨p, h.point_mem i⟩)

/-- Helper for Exercise 71.2: the partial-core coproduct map restricts on each
canonical factor to the inclusion-induced fundamental-group map. -/
private lemma finiteWedgePartialCoreCoprodMap_comp_of
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (K : Finset k) (i : K) :
    (finiteWedgePartialCoreCoprodMap S p K).comp
        (@Monoid.CoprodI.of K
          (fun j : K ↦ FundamentalGroup (S j) ⟨p, h.point_mem j⟩) _ i) =
      FundamentalGroup.mapOfSubset
        (summand_subset_finiteWedgeCore S p K i.property) ⟨p, h.point_mem i⟩ := by
  -- This is exactly the computation rule of the indexed coproduct lift.
  exact Monoid.CoprodI.lift_comp_of _ i

/-- Helper for Exercise 71.2: an indexed coproduct over an empty index type is
subsingleton. -/
private lemma coprodISubsingleton_of_isEmpty
    {k : Type*} (G : k → Type*) [∀ i, Group (G i)] [IsEmpty k] :
    Subsingleton (Monoid.CoprodI G) := by
  constructor
  intro x y
  have eq_one (z : Monoid.CoprodI G) : z = 1 := by
    have mulStep : ∀ a b : Monoid.CoprodI G,
        a = 1 → b = 1 → a * b = 1 := by
      intro a b ha hb
      rw [ha, hb, one_mul]
    exact Monoid.CoprodI.induction_on (motive := fun q ↦ q = 1) z rfl
      (fun i ↦ isEmptyElim i) mulStep
  exact (eq_one x).trans (eq_one y).symm

/-- Helper for Exercise 71.2: the canonical coproduct map for the empty partial
core is bijective. -/
private lemma finiteWedgePartialCoreCoprodMap_bijective_empty
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p] :
    Function.Bijective (finiteWedgePartialCoreCoprodMap S p ∅) := by
  -- Both the empty coproduct and the fundamental group of the singleton core are
  -- subsingletons; the identity elements witness surjectivity.
  letI : IsEmpty (↥(∅ : Finset k)) :=
    ⟨fun i ↦ (Finset.notMem_empty (α := k) i.1) i.2⟩
  letI : Nonempty (finiteWedgeCore S p ∅) :=
    ⟨⟨p, point_mem_finiteWedgeCore S p ∅⟩⟩
  letI : Subsingleton (finiteWedgeCore S p ∅) := by
    constructor
    intro x y
    apply Subtype.ext
    have hx : (x : X) = p := by
      simpa only [finiteWedgeCore, Finset.notMem_empty, Set.iUnion_false,
        Set.iUnion_empty, Set.union_empty, Set.mem_singleton_iff] using x.property
    have hy : (y : X) = p := by
      simpa only [finiteWedgeCore, Finset.notMem_empty, Set.iUnion_false,
        Set.iUnion_empty, Set.union_empty, Set.mem_singleton_iff] using y.property
    exact hx.trans hy.symm
  constructor
  · intro a b hab
    exact (coprodISubsingleton_of_isEmpty _).elim a b
  · intro y
    refine ⟨1, ?_⟩
    exact Subsingleton.elim _ y

/-- Helper for Exercise 71.2: a space that deformation retracts onto a singleton is
contractible. -/
private lemma contractibleSpace_of_singleton_isDeformationRetract
    {Y : Type*} [TopologicalSpace Y] (y : Y)
    (hy : Set.IsDeformationRetract ({y} : Set Y)) : ContractibleSpace Y := by
  letI : Nonempty ({y} : Set Y) := ⟨⟨y, Set.mem_singleton y⟩⟩
  letI : Subsingleton ({y} : Set Y) := by
    constructor
    intro a b
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp a.property).trans
      (Set.mem_singleton_iff.mp b.property).symm
  -- Reverse the deformation-retract equivalence to transfer contractibility from
  -- the singleton subtype to the ambient space.
  obtain ⟨e⟩ := hy.nonempty_homotopyEquiv
  exact e.symm.contractibleSpace

/-- Helper for Exercise 71.2: retaining no summands makes a relative thickening
contractible by the pasted deformation retraction. -/
private lemma finiteWedgeThickening_contractible_empty
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (K : Finset k) :
    ContractibleSpace (finiteWedgeThickening S p W ∅ K) := by
  let q : finiteWedgeThickening S p W ∅ K :=
    ⟨p, finiteWedgeCore_subset_thickening S p W ∅ K
      (point_mem_finiteWedgeCore S p ∅)⟩
  have hsingleton :
      (Subtype.val ⁻¹' finiteWedgeCore S p ∅ :
          Set (finiteWedgeThickening S p W ∅ K)) = {q} := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_singleton_iff]
      change (x : X) ∈ finiteWedgeCore S p ∅ at hx
      have hxval : (x : X) = p := by
        simpa only [finiteWedgeCore, Finset.notMem_empty, Set.iUnion_false,
          Set.iUnion_empty, Set.union_empty, Set.mem_singleton_iff] using hx
      exact Subtype.ext hxval
    · intro hx
      have hxq : x = q := Set.mem_singleton_iff.mp hx
      rw [hxq]
      exact point_mem_finiteWedgeCore S p ∅
  have hretract := finiteWedgeThickening_deformationRetractsToCore
    S p W hpW hW_retract ∅ K (Finset.empty_subset K)
  rw [hsingleton] at hretract
  -- The pasted endpoint contracts the entire thickening onto its canonical basepoint.
  exact contractibleSpace_of_singleton_isDeformationRetract q hretract

/-- Helper for Exercise 71.2: the intersection in the successor open cover is
contractible. -/
private lemma finiteWedgeSuccessorIntersection_contractible
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J : Finset k) {i : k} (hi : i ∉ J) :
    ContractibleSpace (↥(finiteWedgeSuccessorLeft S p W J i ∩
      finiteWedgeSuccessorRight S p W J i)) := by
  change ContractibleSpace
    (↥((Subtype.val ⁻¹' finiteWedgeThickening S p W {i} (insert i J) :
            Set (finiteWedgeCore S p (insert i J))) ∩
          (Subtype.val ⁻¹' finiteWedgeThickening S p W J (insert i J) :
            Set (finiteWedgeCore S p (insert i J)))))
  have hinter :
      (Subtype.val ⁻¹' finiteWedgeThickening S p W {i} (insert i J) :
          Set (finiteWedgeCore S p (insert i J))) ∩
          (Subtype.val ⁻¹' finiteWedgeThickening S p W J (insert i J) :
            Set (finiteWedgeCore S p (insert i J))) =
        (Subtype.val ⁻¹' finiteWedgeThickening S p W ∅ (insert i J) :
          Set (finiteWedgeCore S p (insert i J))) := by
    ext x
    change
      x.1 ∈ finiteWedgeThickening S p W {i} (insert i J) ∩
          finiteWedgeThickening S p W J (insert i J) ↔
        x.1 ∈ finiteWedgeThickening S p W ∅ (insert i J)
    exact Set.ext_iff.mp (finiteWedgeThickening_insert_inter S p W J hi) x.1
  letI : ContractibleSpace (finiteWedgeThickening S p W ∅ (insert i J)) :=
    finiteWedgeThickening_contractible_empty S p W hpW hW_retract (insert i J)
  letI : ContractibleSpace
      (Subtype.val ⁻¹' finiteWedgeThickening S p W ∅ (insert i J) :
        Set (finiteWedgeCore S p (insert i J))) :=
    ((setSubsetPreimageHomeomorph
      (finiteWedgeThickening_subset_core S p W
        (Finset.empty_subset (insert i J)))).symm).contractibleSpace
  -- Transport contractibility only across the canonical nested-subtype homeomorphism
  -- and the already-proved intersection identity.
  exact (Homeomorph.setCongr hinter).contractibleSpace

/-- Helper for Exercise 71.2: the two successor thickenings give the exact van
Kampen pushout square for the enlarged partial core. -/
private lemma finiteWedgeSuccessor_isPushout
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J : Finset k) {i : k} (hi : i ∉ J) :
    IsPushout
      (GrpCat.ofHom (FundamentalGroup.mapOfSubset Set.inter_subset_left
        ⟨finiteWedgeCorePoint S p (insert i J),
          finiteWedgeCorePoint_mem_successorIntersection S p W J i⟩))
      (GrpCat.ofHom (FundamentalGroup.mapOfSubset Set.inter_subset_right
        ⟨finiteWedgeCorePoint S p (insert i J),
          finiteWedgeCorePoint_mem_successorIntersection S p W J i⟩))
      (GrpCat.ofHom (FundamentalGroup.mapOfSubtype
        (finiteWedgeSuccessorLeft S p W J i)
        ⟨finiteWedgeCorePoint S p (insert i J),
          (finiteWedgeCorePoint_mem_successorIntersection S p W J i).1⟩))
      (GrpCat.ofHom (FundamentalGroup.mapOfSubtype
        (finiteWedgeSuccessorRight S p W J i)
        ⟨finiteWedgeCorePoint S p (insert i J),
          (finiteWedgeCorePoint_mem_successorIntersection S p W J i).2⟩)) := by
  letI : ContractibleSpace
      (↥(finiteWedgeSuccessorLeft S p W J i ∩
        finiteWedgeSuccessorRight S p W J i)) := by
    exact finiteWedgeSuccessorIntersection_contractible S p W hpW hW_retract J hi
  letI : PathConnectedSpace
      (↥(finiteWedgeSuccessorLeft S p W J i ∩
        finiteWedgeSuccessorRight S p W J i)) := inferInstance
  -- All topological side conditions now come from the named successor-piece API.
  exact FundamentalGroup.isPushoutOfOpenUnion
    (finiteWedgeSuccessorLeft S p W J i)
    (finiteWedgeSuccessorRight S p W J i)
    (finiteWedgeCorePoint S p (insert i J))
    (finiteWedgeCorePoint_mem_successorIntersection S p W J i)
    (finiteWedgeSuccessorLeft_isOpen S p W hW_open hpW J i)
    (finiteWedgeSuccessorRight_isOpen S p W hW_open hpW J i)
    (finiteWedgeSuccessor_union S p W J i)

/-- Helper for Exercise 71.2: the canonical binary free-product map of the two
successor pieces is bijective. -/
private lemma finiteWedgeSuccessorVanKampenLift_bijective
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k] [DecidableEq k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (J : Finset k) {i : k} (hi : i ∉ J) :
    Function.Bijective
      (Monoid.Coprod.lift
        (FundamentalGroup.mapOfSubtype (finiteWedgeSuccessorLeft S p W J i)
          ⟨finiteWedgeCorePoint S p (insert i J),
            (finiteWedgeCorePoint_mem_successorIntersection S p W J i).1⟩)
        (FundamentalGroup.mapOfSubtype (finiteWedgeSuccessorRight S p W J i)
          ⟨finiteWedgeCorePoint S p (insert i J),
            (finiteWedgeCorePoint_mem_successorIntersection S p W J i).2⟩)) := by
  letI : ContractibleSpace
      (↥(finiteWedgeSuccessorLeft S p W J i ∩
        finiteWedgeSuccessorRight S p W J i)) :=
    finiteWedgeSuccessorIntersection_contractible S p W hpW hW_retract J hi
  letI : Subsingleton
      (FundamentalGroup
        (↥(finiteWedgeSuccessorLeft S p W J i ∩
          finiteWedgeSuccessorRight S p W J i))
        ⟨finiteWedgeCorePoint S p (insert i J),
          finiteWedgeCorePoint_mem_successorIntersection S p W J i⟩) := inferInstance
  -- The exact van Kampen square now satisfies the algebraic subsingleton-pushout
  -- criterion proved above.
  exact Monoid.Coprod.lift_bijective_of_isPushout_of_subsingleton
    (FundamentalGroup.mapOfSubset Set.inter_subset_left
      ⟨finiteWedgeCorePoint S p (insert i J),
        finiteWedgeCorePoint_mem_successorIntersection S p W J i⟩)
    (FundamentalGroup.mapOfSubset Set.inter_subset_right
      ⟨finiteWedgeCorePoint S p (insert i J),
        finiteWedgeCorePoint_mem_successorIntersection S p W J i⟩)
    (FundamentalGroup.mapOfSubtype (finiteWedgeSuccessorLeft S p W J i)
      ⟨finiteWedgeCorePoint S p (insert i J),
        (finiteWedgeCorePoint_mem_successorIntersection S p W J i).1⟩)
    (FundamentalGroup.mapOfSubtype (finiteWedgeSuccessorRight S p W J i)
      ⟨finiteWedgeCorePoint S p (insert i J),
        (finiteWedgeCorePoint_mem_successorIntersection S p W J i).2⟩)
    (finiteWedgeSuccessor_isPushout S p W hW_open hpW hW_retract J hi)

/-- Helper for Exercise 71.2: a singleton deformation retract forces every based
fundamental group of the ambient space to be subsingleton. -/
private lemma fundamentalGroup_subsingleton_of_singleton_isDeformationRetract
    {Y : Type*} [TopologicalSpace Y] (y₀ y : Y)
    (hy : Set.IsDeformationRetract ({y} : Set Y)) :
    Subsingleton (FundamentalGroup Y y₀) := by
  letI : ContractibleSpace Y :=
    contractibleSpace_of_singleton_isDeformationRetract y hy
  -- Contractible spaces are simply connected, so their based loop groups are trivial.
  infer_instance

/-- Helper for Exercise 71.2: the canonical indexed-coproduct map to every
partial wedge core is bijective. -/
private lemma finiteWedgePartialCoreCoprodMap_bijective
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i)))
    (K : Finset k) :
    Function.Bijective (finiteWedgePartialCoreCoprodMap S p K) := by
  classical
  induction K using Finset.induction with
  | empty =>
      exact finiteWedgePartialCoreCoprodMap_bijective_empty S p
  | @insert i J hi ih =>
      let G : k → Type u := fun j ↦
        FundamentalGroup (S j) ⟨p, h.point_mem j⟩
      let K := insert i J
      have hsingleton : {i} ⊆ K := Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_self i J)
      have hJK : J ⊆ K := Finset.subset_insert i J
      have hSiU : S i ⊆ finiteWedgeThickening S p W {i} K := by
        intro x hx
        apply finiteWedgeCore_subset_thickening S p W {i} K
        rw [finiteWedgeCore_singleton S p i]
        exact hx
      have hUK : finiteWedgeThickening S p W {i} K ⊆
          finiteWedgeCore S p K :=
        finiteWedgeThickening_subset_core S p W hsingleton
      have hJV : finiteWedgeCore S p J ⊆
          finiteWedgeThickening S p W J K :=
        finiteWedgeCore_subset_thickening S p W J K
      have hVK : finiteWedgeThickening S p W J K ⊆
          finiteWedgeCore S p K :=
        finiteWedgeThickening_subset_core S p W hJK
      let leftLeg := FundamentalGroup.mapOfSubtype
        (finiteWedgeSuccessorLeft S p W J i)
        ⟨finiteWedgeCorePoint S p K,
          (finiteWedgeCorePoint_mem_successorIntersection S p W J i).1⟩
      let rightLeg := FundamentalGroup.mapOfSubtype
        (finiteWedgeSuccessorRight S p W J i)
        ⟨finiteWedgeCorePoint S p K,
          (finiteWedgeCorePoint_mem_successorIntersection S p W J i).2⟩
      let leftMap : G i →*
          FundamentalGroup (finiteWedgeSuccessorLeft S p W J i)
            ⟨finiteWedgeCorePoint S p K,
              finiteWedgeCorePoint_mem_successorLeft S p W J i⟩ :=
        fundamentalGroupNestedSubsetMap hSiU hUK ⟨p, h.point_mem i⟩
      let rightCoreMap :
          FundamentalGroup (finiteWedgeCore S p J)
              (finiteWedgeCorePoint S p J) →*
            FundamentalGroup (finiteWedgeSuccessorRight S p W J i)
              ⟨finiteWedgeCorePoint S p K,
                finiteWedgeCorePoint_mem_successorRight S p W J i⟩ :=
        fundamentalGroupNestedSubsetMap hJV hVK (finiteWedgeCorePoint S p J)
      let rightMap : Monoid.CoprodI (fun j : J ↦ G j) →*
          FundamentalGroup (finiteWedgeSuccessorRight S p W J i)
            ⟨finiteWedgeCorePoint S p K,
              finiteWedgeCorePoint_mem_successorRight S p W J i⟩ :=
        rightCoreMap.comp (finiteWedgePartialCoreCoprodMap S p J)
      have hleftRetract := finiteWedgeThickening_deformationRetractsToCore
        S p W hpW hW_retract {i} K hsingleton
      rw [finiteWedgeCore_singleton S p i] at hleftRetract
      have hleftMap : Function.Bijective leftMap := by
        exact fundamentalGroupNestedSubsetMap_bijective_of_isDeformationRetract
          hSiU hUK ⟨p, h.point_mem i⟩ hleftRetract
      have hrightCoreMap : Function.Bijective rightCoreMap := by
        exact fundamentalGroupNestedSubsetMap_bijective_of_isDeformationRetract
          hJV hVK (finiteWedgeCorePoint S p J)
            (finiteWedgeThickening_deformationRetractsToCore
              S p W hpW hW_retract J K hJK)
      have hrightMap : Function.Bijective rightMap := by
        exact hrightCoreMap.comp ih
      have hbinaryMap : Function.Bijective
          (Monoid.Coprod.map leftMap rightMap) := by
        exact ((MulEquiv.ofBijective leftMap hleftMap).coprodCongr
          (MulEquiv.ofBijective rightMap hrightMap)).bijective
      let vanKampenLift := Monoid.Coprod.lift leftLeg rightLeg
      have hvanKampenLift : Function.Bijective vanKampenLift :=
        finiteWedgeSuccessorVanKampenLift_bijective
          S p W hW_open hpW hW_retract J hi
      let successorComposite := vanKampenLift.comp
        (Monoid.Coprod.map leftMap rightMap)
      have hsuccessorComposite : Function.Bijective successorComposite := by
        exact hvanKampenLift.comp hbinaryMap
      have hcomparison :
          successorComposite =
            (finiteWedgePartialCoreCoprodMap S p K).comp
              (coprodIInsertComparison G J i) := by
        apply Monoid.Coprod.hom_ext
        · ext x
          change leftLeg (leftMap x) =
            finiteWedgePartialCoreCoprodMap S p K
              (@Monoid.CoprodI.of K
                (fun q : K ↦ FundamentalGroup (S q) ⟨p, h.point_mem q⟩) _
                ⟨i, Finset.mem_insert_self i J⟩ x)
          have hnested := DFunLike.congr_fun
            (fundamentalGroupMapOfSubtype_comp_nestedSubsetMap
              hSiU hUK ⟨p, h.point_mem i⟩) x
          have hpartial := DFunLike.congr_fun
            (finiteWedgePartialCoreCoprodMap_comp_of S p K
              ⟨i, Finset.mem_insert_self i J⟩) x
          calc
            leftLeg (leftMap x) =
                FundamentalGroup.mapOfSubset (hSiU.trans hUK)
                  ⟨p, h.point_mem i⟩ x := hnested
            _ = FundamentalGroup.mapOfSubset
                  (summand_subset_finiteWedgeCore S p K
                    (Finset.mem_insert_self i J))
                  ⟨p, h.point_mem i⟩ x := by rfl
            _ = finiteWedgePartialCoreCoprodMap S p K
                  (@Monoid.CoprodI.of K
                    (fun q : K ↦ FundamentalGroup (S q) ⟨p, h.point_mem q⟩) _
                    ⟨i, Finset.mem_insert_self i J⟩ x) := hpartial.symm
        · apply Monoid.CoprodI.ext_hom
          intro j
          ext x
          change rightLeg (rightCoreMap
              (finiteWedgePartialCoreCoprodMap S p J (Monoid.CoprodI.of x))) =
            finiteWedgePartialCoreCoprodMap S p K
              (@Monoid.CoprodI.of K
                (fun q : K ↦ FundamentalGroup (S q) ⟨p, h.point_mem q⟩) _
                ⟨j, Finset.mem_insert_of_mem j.property⟩ x)
          have hnested := DFunLike.congr_fun
            (fundamentalGroupMapOfSubtype_comp_nestedSubsetMap
              hJV hVK (finiteWedgeCorePoint S p J))
            (finiteWedgePartialCoreCoprodMap S p J (Monoid.CoprodI.of x))
          have hpartialJ := DFunLike.congr_fun
            (finiteWedgePartialCoreCoprodMap_comp_of S p J j) x
          have hdirect :
              FundamentalGroup.mapOfSubset (finiteWedgeCore_mono S p hJK)
                  (finiteWedgeCorePoint S p J)
                  (FundamentalGroup.mapOfSubset
                    (summand_subset_finiteWedgeCore S p J j.property)
                    ⟨p, h.point_mem j⟩ x) =
                (FundamentalGroup.mapOfSubset
                  ((summand_subset_finiteWedgeCore S p J j.property).trans
                    (finiteWedgeCore_mono S p hJK))
                  ⟨p, h.point_mem j⟩ x :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) := by
            exact DFunLike.congr_fun
              (fundamentalGroupMapOfSubset_comp
                (summand_subset_finiteWedgeCore S p J j.property)
                (finiteWedgeCore_mono S p hJK) ⟨p, h.point_mem j⟩) x
          have hpartialK := DFunLike.congr_fun
            (finiteWedgePartialCoreCoprodMap_comp_of S p K
              ⟨j, Finset.mem_insert_of_mem j.property⟩) x
          have hdirectCanonical :
              (FundamentalGroup.mapOfSubset (finiteWedgeCore_mono S p hJK)
                  (finiteWedgeCorePoint S p J)
                  (FundamentalGroup.mapOfSubset
                    (summand_subset_finiteWedgeCore S p J j.property)
                    ⟨p, h.point_mem j⟩ x) :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) =
                (FundamentalGroup.mapOfSubset
                  (summand_subset_finiteWedgeCore S p K
                    (Finset.mem_insert_of_mem j.property))
                  ⟨p, h.point_mem j⟩ x :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) := by
            exact hdirect.trans (by rfl)
          have hcoreInclusion :
              (FundamentalGroup.mapOfSubset (hJV.trans hVK)
                  (finiteWedgeCorePoint S p J)
                  (finiteWedgePartialCoreCoprodMap S p J
                    (Monoid.CoprodI.of x)) :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) =
                (FundamentalGroup.mapOfSubset (finiteWedgeCore_mono S p hJK)
                  (finiteWedgeCorePoint S p J)
                  (finiteWedgePartialCoreCoprodMap S p J
                    (Monoid.CoprodI.of x)) :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) := by
            rfl
          have hinductionStep :
              (FundamentalGroup.mapOfSubset (finiteWedgeCore_mono S p hJK)
                  (finiteWedgeCorePoint S p J)
                  (finiteWedgePartialCoreCoprodMap S p J
                    (Monoid.CoprodI.of x)) :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) =
                (FundamentalGroup.mapOfSubset (finiteWedgeCore_mono S p hJK)
                  (finiteWedgeCorePoint S p J)
                  (FundamentalGroup.mapOfSubset
                    (summand_subset_finiteWedgeCore S p J j.property)
                    ⟨p, h.point_mem j⟩ x) :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) := by
            exact congrArg
              (fun z ↦ FundamentalGroup.mapOfSubset
                (finiteWedgeCore_mono S p hJK)
                (finiteWedgeCorePoint S p J) z) hpartialJ
          have hpartialK' :
              (FundamentalGroup.mapOfSubset
                  (summand_subset_finiteWedgeCore S p K
                    (Finset.mem_insert_of_mem j.property))
                  ⟨p, h.point_mem j⟩ x :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) =
                (finiteWedgePartialCoreCoprodMap S p K
                  (@Monoid.CoprodI.of K
                    (fun q : K ↦ FundamentalGroup (S q) ⟨p, h.point_mem q⟩) _
                    ⟨j, Finset.mem_insert_of_mem j.property⟩ x) :
                  FundamentalGroup (finiteWedgeCore S p K)
                    (finiteWedgeCorePoint S p K)) := by
            exact hpartialK.symm
          exact hnested.trans (hcoreInclusion.trans
            (hinductionStep.trans (hdirectCanonical.trans hpartialK')))
      have hcomposed : Function.Bijective
          ((finiteWedgePartialCoreCoprodMap S p K).comp
            (coprodIInsertComparison G J i)) := by
        exact hcomparison ▸ hsuccessorComposite
      have hinsertComparison := coprodIInsertComparison_bijective G J hi
      change Function.Bijective (finiteWedgePartialCoreCoprodMap S p K)
      change Function.Bijective
        (⇑(finiteWedgePartialCoreCoprodMap S p K) ∘
          ⇑(coprodIInsertComparison G J i)) at hcomposed
      constructor
      · exact hcomposed.1.of_comp_right hinsertComparison.2
      · exact hcomposed.2.of_comp

/-- Helper for Exercise 71.2: the canonical map from
the indexed coproduct of the summand fundamental groups to the ambient fundamental group
is bijective. -/
private lemma finiteWedgeFundamentalGroup_coprodLift_bijective
    {X : Type u} [TopologicalSpace X] {k : Type*} [Fintype k]
    (S : k → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i))) :
    Function.Bijective
      (Monoid.CoprodI.lift
        (fun i ↦ FundamentalGroup.mapOfEq
          (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, X))
          (rfl : (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, X))
            ⟨p, h.point_mem i⟩ = p))) := by
  classical
  -- The finite induction proves the coproduct comparison for the full partial core.
  have hpartial := finiteWedgePartialCoreCoprodMap_bijective
    S p W hW_open hpW hW_retract Finset.univ
  have hcore : finiteWedgeCore S p Finset.univ = Set.univ :=
    finiteWedgeCore_univ S p
  let e : finiteWedgeCore S p Finset.univ ≃ₜ X :=
    (Homeomorph.setCongr hcore).trans (Homeomorph.Set.univ X)
  have heContinuousMap :
      (e : C(finiteWedgeCore S p Finset.univ, X)) =
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(finiteWedgeCore S p Finset.univ, X)) := by
    ext x
    rfl
  have hambient : Function.Bijective
      (FundamentalGroup.mapOfSubtype (finiteWedgeCore S p Finset.univ)
        ⟨p, point_mem_finiteWedgeCore S p Finset.univ⟩) := by
    have heBijective := e.toHomotopyEquiv.fundamentalGroupMap_bijective
      ⟨p, point_mem_finiteWedgeCore S p Finset.univ⟩
    change Function.Bijective
      (FundamentalGroup.map
        (e : C(finiteWedgeCore S p Finset.univ, X))
        ⟨p, point_mem_finiteWedgeCore S p Finset.univ⟩) at heBijective
    rw [heContinuousMap] at heBijective
    rw [FundamentalGroup.mapOfSubtype_eq_map_subtypeVal]
    exact heBijective
  let G : k → Type u := fun i ↦
    FundamentalGroup (S i) ⟨p, h.point_mem i⟩
  have hunivComparison := coprodIUnivComparison_bijective G
  have hcomposed := hambient.comp (hpartial.comp hunivComparison)
  change Function.Bijective
    ⇑((FundamentalGroup.mapOfSubtype (finiteWedgeCore S p Finset.univ)
        ⟨p, point_mem_finiteWedgeCore S p Finset.univ⟩).comp
      ((finiteWedgePartialCoreCoprodMap S p Finset.univ).comp
        (coprodIUnivComparison G))) at hcomposed
  have hmap :
      (FundamentalGroup.mapOfSubtype (finiteWedgeCore S p Finset.univ)
        ⟨p, point_mem_finiteWedgeCore S p Finset.univ⟩).comp
          ((finiteWedgePartialCoreCoprodMap S p Finset.univ).comp
            (coprodIUnivComparison G)) =
        Monoid.CoprodI.lift
          (fun i ↦ FundamentalGroup.mapOfEq
            (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, X))
            (rfl : (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, X))
              ⟨p, h.point_mem i⟩ = p)) := by
    apply Monoid.CoprodI.ext_hom
    intro i
    have hsubtypeComp :
        (FundamentalGroup.mapOfSubtype (finiteWedgeCore S p Finset.univ)
          ⟨p, point_mem_finiteWedgeCore S p Finset.univ⟩).comp
            (FundamentalGroup.mapOfSubset
              (summand_subset_finiteWedgeCore S p Finset.univ
                (Finset.mem_univ i))
              ⟨p, h.point_mem i⟩) =
          FundamentalGroup.mapOfSubtype (S i) ⟨p, h.point_mem i⟩ := by
      -- Apply the composition law by type, allowing proof irrelevance to identify
      -- the two membership witnesses for the wedge point in the full core.
      exact FundamentalGroup.mapOfSubtype_comp_mapOfSubset
        (summand_subset_finiteWedgeCore S p Finset.univ (Finset.mem_univ i))
        ⟨p, h.point_mem i⟩
    rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc,
      coprodIUnivComparison_comp_of,
      finiteWedgePartialCoreCoprodMap_comp_of,
      hsubtypeComp,
      FundamentalGroup.mapOfSubtype_eq_map_subtypeVal,
      Monoid.CoprodI.lift_comp_of,
      FundamentalGroup.mapOfEq_refl_eq_map]
  exact hmap ▸ hcomposed

/- Exercise 71.2: A space covered by finitely many closed subspaces meeting pairwise exactly
at a common point is their wedge. -/
#check Topology.IsFiniteWedge

/-- Exercise 71.2: If the wedge point is a deformation retract of an open neighborhood in
each subspace, the inclusion-induced maps exhibit the ambient fundamental group as the
external free product of the subspace fundamental groups. -/
theorem fundamentalGroup_isExternalFreeProduct_of_finiteWedge
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (S : ι → Set X) (p : X) [h : Topology.IsFiniteWedge S p]
    (W : ∀ i, Set (S i))
    (hW_open : ∀ i, IsOpen (W i))
    (hpW : ∀ i, (⟨p, h.point_mem i⟩ : S i) ∈ W i)
    (hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨p, h.point_mem i⟩, hpW i⟩ : W i)} : Set (W i))) :
    MonoidHom.IsExternalFreeProduct
      (fun i ↦ FundamentalGroup.mapOfEq
        (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, X))
        (rfl : (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, X))
          ⟨p, h.point_mem i⟩ = p)) := by
  -- Route correction: avoid the opaque extension predicate, dependent-topology reindexing,
  -- and unsupported `ULift` pushout transport. Close through the explicit coproduct map and
  -- postpone reindexing until the argument is entirely algebraic.
  apply MonoidHom.isExternalFreeProduct_of_coprodLift_bijective
  exact finiteWedgeFundamentalGroup_coprodLift_bijective
    S p W hW_open hpW hW_retract
