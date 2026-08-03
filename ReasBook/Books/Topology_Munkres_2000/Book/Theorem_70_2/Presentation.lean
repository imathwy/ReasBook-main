module

public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Mathlib.GroupTheory.Coprod.Basic
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u

namespace FundamentalGroup

/-- The canonical homomorphism from the free product of the fundamental groups of `U` and
`V` to the fundamental group of `X`. -/
noncomputable def vanKampenMap {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    Monoid.Coprod (FundamentalGroup U ⟨x₀, hx₀.1⟩)
        (FundamentalGroup V ⟨x₀, hx₀.2⟩) →* FundamentalGroup X x₀ :=
  Monoid.Coprod.lift
    (mapOfSubtype U ⟨x₀, hx₀.1⟩)
    (mapOfSubtype V ⟨x₀, hx₀.2⟩)

/-- The canonical free-product homomorphism restricts to the inclusion-induced map from
`π₁(U, x₀)`. -/
@[simp]
theorem vanKampenMap_comp_inl {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    (vanKampenMap U V x₀ hx₀).comp Monoid.Coprod.inl =
      mapOfSubtype U ⟨x₀, hx₀.1⟩ :=
  Monoid.Coprod.lift_comp_inl _ _

/-- The canonical free-product homomorphism restricts to the inclusion-induced map from
`π₁(V, x₀)`. -/
@[simp]
theorem vanKampenMap_comp_inr {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    (vanKampenMap U V x₀ hx₀).comp Monoid.Coprod.inr =
      mapOfSubtype V ⟨x₀, hx₀.2⟩ :=
  Monoid.Coprod.lift_comp_inr _ _

/-- The free-product relation identifying the two images of an intersection loop. -/
noncomputable def vanKampenRelation {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (g : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩) :
    Monoid.Coprod (FundamentalGroup U ⟨x₀, hx₀.1⟩)
      (FundamentalGroup V ⟨x₀, hx₀.2⟩) :=
  (Monoid.Coprod.inl (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ g))⁻¹ *
    Monoid.Coprod.inr (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ g)

/-- The set of free-product relations coming from loops in `U ∩ V`. -/
noncomputable def vanKampenRelations {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    Set (Monoid.Coprod (FundamentalGroup U ⟨x₀, hx₀.1⟩)
      (FundamentalGroup V ⟨x₀, hx₀.2⟩)) :=
  Set.range (vanKampenRelation U V x₀ hx₀)

/-- The least normal subgroup containing the free-product relations from `U ∩ V`. -/
noncomputable def vanKampenNormalClosure {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    Subgroup (Monoid.Coprod (FundamentalGroup U ⟨x₀, hx₀.1⟩)
      (FundamentalGroup V ⟨x₀, hx₀.2⟩)) :=
  Subgroup.normalClosure (vanKampenRelations U V x₀ hx₀)

/-- Every relation induced by a loop in `U ∩ V` lies in the kernel of the canonical
free-product homomorphism. -/
theorem vanKampenRelation_mem_ker {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (g : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩) :
    vanKampenRelation U V x₀ hx₀ g ∈ (vanKampenMap U V x₀ hx₀).ker := by
  -- Both ways of including an intersection loop into the ambient space coincide.
  have hleft :
      (mapOfSubtype U ⟨x₀, hx₀.1⟩).comp
          (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) =
        mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ := by
    ext q
    simp only [MonoidHom.comp_apply]
    rw [mapOfSubset_eq_map_inclusion]
    unfold mapOfSubtype
    rw [map_apply]
    exact (Path.Homotopic.Quotient.map_comp
      (p := q) (f := ContinuousMap.inclusion Set.inter_subset_left)
      (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).symm
  have hright :
      (mapOfSubtype V ⟨x₀, hx₀.2⟩).comp
          (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩) =
        mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ := by
    ext q
    simp only [MonoidHom.comp_apply]
    rw [mapOfSubset_eq_map_inclusion]
    unfold mapOfSubtype
    rw [map_apply]
    exact (Path.Homotopic.Quotient.map_comp
      (p := q) (f := ContinuousMap.inclusion Set.inter_subset_right)
      (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)))).symm
  apply MonoidHom.mem_ker.mpr
  simp only [vanKampenRelation, vanKampenMap, map_mul, map_inv,
    Monoid.Coprod.lift_apply_inl, Monoid.Coprod.lift_apply_inr]
  have hleftValue :
      mapOfSubtype U ⟨x₀, hx₀.1⟩
          (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩ g) =
        mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ g :=
    DFunLike.congr_fun hleft g
  have hrightValue :
      mapOfSubtype V ⟨x₀, hx₀.2⟩
          (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ g) =
        mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ g :=
    DFunLike.congr_fun hright g
  rw [hleftValue, hrightValue, inv_mul_cancel]

end FundamentalGroup
