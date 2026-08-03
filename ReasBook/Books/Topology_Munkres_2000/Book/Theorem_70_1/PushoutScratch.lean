module

public import Topology_Munkres_2000.Book.Theorem_59_1
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u

open CategoryTheory

namespace FundamentalGroup

/-- Helper for Theorem 70.1: the two inclusion composites from the intersection agree. -/
lemma openUnionSquare_commutes_test {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.ofHom (mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩) ≫
        GrpCat.ofHom (mapOfSubtype U ⟨x₀, hx₀.1⟩) =
      GrpCat.ofHom (mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩) ≫
      GrpCat.ofHom (mapOfSubtype V ⟨x₀, hx₀.2⟩) := by
  -- Both composites forget the two subtype layers and hence act identically on loops.
  rw [← GrpCat.ofHom_comp, ← GrpCat.ofHom_comp]
  apply congrArg GrpCat.ofHom
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
  exact hleft.trans hright.symm

end FundamentalGroup
