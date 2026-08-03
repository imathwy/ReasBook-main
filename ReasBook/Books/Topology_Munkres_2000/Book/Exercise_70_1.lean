module

import Topology_Munkres_2000.Book.Theorem_70_1
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Exercise_70_1.NormalClosure
public import Topology_Munkres_2000.Book.Notation_70_1
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

open scoped Monoid.Coprod

universe u

/-- Helper for Exercise 70.1: inclusion through a subspace induces the same
fundamental-group map as direct inclusion into the ambient space. -/
private lemma FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    {X : Type u} [TopologicalSpace X] {A U : Set X}
    (hAU : A ⊆ U) (a : A) :
    (FundamentalGroup.mapOfSubtype U ⟨a, hAU a.property⟩).comp
        (FundamentalGroup.mapOfSubset hAU a) =
      FundamentalGroup.mapOfSubtype A a := by
  -- Replace the subset inclusion by its continuous map and map the composite path class.
  ext q
  simp only [MonoidHom.comp_apply]
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  unfold FundamentalGroup.mapOfSubtype
  rw [FundamentalGroup.map_apply]
  exact (Path.Homotopic.Quotient.map_comp
    (p := q) (f := ContinuousMap.inclusion hAU)
    (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).symm

/-- The left normal closure is killed by inclusion into `X` when the intersection map is
trivial. -/
theorem vanKampenLeftNormalClosure_le_ker {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    vanKampenLeftNormalClosure U V x₀ hx₀ ≤
      (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩).ker := by
  -- It suffices to check the generators coming from the intersection group.
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, rfl⟩
  apply MonoidHom.mem_ker.mpr
  -- The composite inclusion is the direct intersection inclusion, which is trivial.
  have hfactor := FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    Set.inter_subset_left ⟨x₀, hx₀⟩
  have hvalue := DFunLike.congr_fun hfactor g
  simpa only [MonoidHom.comp_apply, hi, MonoidHom.one_apply] using hvalue

/-- The right normal closure is killed by inclusion into `X` when the intersection map is
trivial. -/
theorem vanKampenRightNormalClosure_le_ker {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    vanKampenRightNormalClosure U V x₀ hx₀ ≤
      (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩).ker := by
  -- The right normal closure is handled by the symmetric generator argument.
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, rfl⟩
  apply MonoidHom.mem_ker.mpr
  have hfactor := FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    Set.inter_subset_right ⟨x₀, hx₀⟩
  have hvalue := DFunLike.congr_fun hfactor g
  simpa only [MonoidHom.comp_apply, hi, MonoidHom.one_apply] using hvalue

/-- The homomorphism from the coproduct of quotient fundamental groups induced by the
inclusions of `U` and `V` into `X`. -/
noncomputable def vanKampenQuotientMap {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸ vanKampenLeftNormalClosure U V x₀ hx₀) ∗
        (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸ vanKampenRightNormalClosure U V x₀ hx₀) →*
    FundamentalGroup X x₀ :=
  Monoid.Coprod.lift
    (QuotientGroup.lift (vanKampenLeftNormalClosure U V x₀ hx₀)
      (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
      (vanKampenLeftNormalClosure_le_ker U V x₀ hx₀ hi))
    (QuotientGroup.lift (vanKampenRightNormalClosure U V x₀ hx₀)
      (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩)
      (vanKampenRightNormalClosure_le_ker U V x₀ hx₀ hi))

/-- The quotient free-product homomorphism restricts on the left factor to the map induced
by inclusion of `U` into `X`. -/
@[simp]
theorem vanKampenQuotientMap_comp_inl {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    (vanKampenQuotientMap U V x₀ hx₀ hi).comp Monoid.Coprod.inl =
      QuotientGroup.lift (vanKampenLeftNormalClosure U V x₀ hx₀)
        (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
        (vanKampenLeftNormalClosure_le_ker U V x₀ hx₀ hi) :=
  Monoid.Coprod.lift_comp_inl _ _

/-- The quotient free-product homomorphism restricts on the right factor to the map induced
by inclusion of `V` into `X`. -/
@[simp]
theorem vanKampenQuotientMap_comp_inr {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    (vanKampenQuotientMap U V x₀ hx₀ hi).comp Monoid.Coprod.inr =
      QuotientGroup.lift (vanKampenRightNormalClosure U V x₀ hx₀)
        (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩)
        (vanKampenRightNormalClosure_le_ker U V x₀ hx₀ hi) :=
  Monoid.Coprod.lift_comp_inr _ _

/-- On a left-factor coset represented by `g`, the quotient free-product homomorphism is
the inclusion-induced image of `g`. -/
@[simp]
theorem vanKampenQuotientMap_inl_mk {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1)
    (g : FundamentalGroup U ⟨x₀, hx₀.1⟩) :
    vanKampenQuotientMap U V x₀ hx₀ hi
        (Monoid.Coprod.inl (QuotientGroup.mk g)) =
      FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩ g :=
  by
    change ((vanKampenQuotientMap U V x₀ hx₀ hi).comp Monoid.Coprod.inl)
        (QuotientGroup.mk g) = _
    rw [vanKampenQuotientMap_comp_inl, QuotientGroup.lift_mk']

/-- On a right-factor coset represented by `g`, the quotient free-product homomorphism is
the inclusion-induced image of `g`. -/
@[simp]
theorem vanKampenQuotientMap_inr_mk {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1)
    (g : FundamentalGroup V ⟨x₀, hx₀.2⟩) :
    vanKampenQuotientMap U V x₀ hx₀ hi
        (Monoid.Coprod.inr (QuotientGroup.mk g)) =
      FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩ g :=
  by
    change ((vanKampenQuotientMap U V x₀ hx₀ hi).comp Monoid.Coprod.inr)
        (QuotientGroup.mk g) = _
    rw [vanKampenQuotientMap_comp_inr, QuotientGroup.lift_mk']

/-- Helper for Exercise 70.1: lifting a homomorphism through a quotient does not
change its range. -/
private lemma QuotientGroup.range_lift {G H : Type*} [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H) (hN : N ≤ f.ker) :
    (QuotientGroup.lift N f hN).range = f.range := by
  -- Normalize every quotient element to a representative in the source group.
  ext y
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hrepresentative : QuotientGroup.lift N f hN (QuotientGroup.mk' N g) = f g := by
      simpa only [MonoidHom.comp_apply] using
        DFunLike.congr_fun (QuotientGroup.lift_comp_mk' N f hN) g
    rw [hrepresentative] at hq
    exact ⟨g, hq⟩
  · rintro ⟨g, hg⟩
    refine ⟨QuotientGroup.mk' N g, ?_⟩
    have hrepresentative : QuotientGroup.lift N f hN (QuotientGroup.mk' N g) = f g := by
      simpa only [MonoidHom.comp_apply] using
        DFunLike.congr_fun (QuotientGroup.lift_comp_mk' N f hN) g
    exact hrepresentative.trans hg

/-- Helper for Exercise 70.1: the range of the quotient free-product map is the
join of the two ambient inclusion-map ranges. -/
private lemma vanKampenQuotientMap_range {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    (vanKampenQuotientMap U V x₀ hx₀ hi).range =
      (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩).range ⊔
        (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩).range := by
  -- First split the coproduct range, then remove the two quotient lifts.
  rw [vanKampenQuotientMap, Monoid.Coprod.range_lift,
    QuotientGroup.range_lift, QuotientGroup.range_lift]

/-- Part (1) of Exercise 70.1: the inclusions induce an epimorphism from the coproduct of
the quotients by the normal closures of the intersection images. -/
theorem vanKampenQuotientMap_surjective {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    Function.Surjective (vanKampenQuotientMap U V x₀ hx₀ hi) := by
  -- Surjectivity is equivalent to saying that the normalized range is the top subgroup.
  apply MonoidHom.range_eq_top.mp
  rw [vanKampenQuotientMap_range]
  -- The earlier generation theorem identifies the joined inclusion ranges with all of `π₁(X)`.
  exact fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hU hV hcover

/-- Helper for Exercise 70.1: the quotient projections into the two coproduct
factors agree after restriction to the intersection fundamental group. -/
private lemma vanKampenQuotientFactorMaps_compatible
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    ((Monoid.Coprod.inl :
        (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸
          vanKampenLeftNormalClosure U V x₀ hx₀) →*
          (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸
              vanKampenLeftNormalClosure U V x₀ hx₀) ∗
            (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸
              vanKampenRightNormalClosure U V x₀ hx₀)).comp
        (QuotientGroup.mk' (vanKampenLeftNormalClosure U V x₀ hx₀))).comp
      (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
    ((Monoid.Coprod.inr :
        (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸
          vanKampenRightNormalClosure U V x₀ hx₀) →*
          (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸
              vanKampenLeftNormalClosure U V x₀ hx₀) ∗
            (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸
              vanKampenRightNormalClosure U V x₀ hx₀)).comp
        (QuotientGroup.mk' (vanKampenRightNormalClosure U V x₀ hx₀))).comp
      (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩) := by
  -- Each intersection loop belongs to the generating range of both normal closures.
  apply MonoidHom.ext
  intro g
  have hleftMem :
      FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ g ∈
        vanKampenLeftNormalClosure U V x₀ hx₀ :=
    Subgroup.subset_normalClosure (Set.mem_range_self g)
  have hrightMem :
      FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ g ∈
        vanKampenRightNormalClosure U V x₀ hx₀ :=
    Subgroup.subset_normalClosure (Set.mem_range_self g)
  -- Both quotient classes are therefore the unit, so their coproduct images agree.
  have hleftOne :
      QuotientGroup.mk' (vanKampenLeftNormalClosure U V x₀ hx₀)
          (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ g) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hleftMem
  have hrightOne :
      QuotientGroup.mk' (vanKampenRightNormalClosure U V x₀ hx₀)
          (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ g) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hrightMem
  simp only [MonoidHom.comp_apply, hleftOne, hrightOne, map_one]

/-- Helper for Exercise 70.1: the quotient free-product map admits a homomorphic
left inverse supplied by the Seifert–van Kampen universal property. -/
private lemma exists_vanKampenQuotientMap_leftInverse
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    ∃ Φ : FundamentalGroup X x₀ →*
        (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸
            vanKampenLeftNormalClosure U V x₀ hx₀) ∗
          (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸
            vanKampenRightNormalClosure U V x₀ hx₀),
      Φ.comp (vanKampenQuotientMap U V x₀ hx₀ hi) = MonoidHom.id _ := by
  let quotientLeft :=
    (Monoid.Coprod.inl :
      (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸
          vanKampenLeftNormalClosure U V x₀ hx₀) →*
        (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸
            vanKampenLeftNormalClosure U V x₀ hx₀) ∗
          (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸
            vanKampenRightNormalClosure U V x₀ hx₀)).comp
      (QuotientGroup.mk' (vanKampenLeftNormalClosure U V x₀ hx₀))
  let quotientRight :=
    (Monoid.Coprod.inr :
      (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸
          vanKampenRightNormalClosure U V x₀ hx₀) →*
        (FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸
            vanKampenLeftNormalClosure U V x₀ hx₀) ∗
          (FundamentalGroup V ⟨x₀, hx₀.2⟩ ⧸
            vanKampenRightNormalClosure U V x₀ hx₀)).comp
      (QuotientGroup.mk' (vanKampenRightNormalClosure U V x₀ hx₀))
  -- The two quotient maps satisfy the compatibility required by Theorem 70.1.
  have hcompatible :
      quotientLeft.comp
          (FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
        quotientRight.comp
          (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩) := by
    exact vanKampenQuotientFactorMaps_compatible U V x₀ hx₀
  obtain ⟨Φ, hΦ, _⟩ :=
    seifertVanKampen U V x₀ hx₀ hU hV hcover quotientLeft quotientRight hcompatible
  refine ⟨Φ, ?_⟩
  -- It remains to compare the composite on the two quotient factors.
  apply Monoid.Coprod.hom_ext
  · apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro g
    have hvalue := DFunLike.congr_fun hΦ.1 g
    simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      vanKampenQuotientMap_inl_mk, MonoidHom.id_apply, quotientLeft] using hvalue
  · apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro g
    have hvalue := DFunLike.congr_fun hΦ.2 g
    simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      vanKampenQuotientMap_inr_mk, MonoidHom.id_apply, quotientRight] using hvalue

/-- Exercise 70.1 (2): The induced homomorphism from the coproduct of quotient fundamental
groups is an isomorphism. -/
theorem vanKampenQuotientMap_bijective {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hi : FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ = 1) :
    Function.Bijective (vanKampenQuotientMap U V x₀ hx₀ hi) := by
  -- The universal-property extension is a left inverse, hence gives injectivity.
  obtain ⟨Φ, hΦ⟩ :=
    exists_vanKampenQuotientMap_leftInverse U V x₀ hx₀ hU hV hcover hi
  have hleftInverse : Function.LeftInverse Φ (vanKampenQuotientMap U V x₀ hx₀ hi) := by
    intro g
    have hvalue := DFunLike.congr_fun hΦ g
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using hvalue
  refine ⟨hleftInverse.injective, ?_⟩
  -- Part (1) supplies the complementary surjectivity statement.
  exact vanKampenQuotientMap_surjective U V x₀ hx₀ hU hV hcover hi
