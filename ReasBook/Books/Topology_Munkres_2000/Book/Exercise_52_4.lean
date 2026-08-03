module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Definition_52_5.Convention

public section

universe u

namespace FundamentalGroup.LeftToRight


/-- Helper for Exercise 52.4: mapping a loop through the subtype inclusion and a
retraction, with the canonical endpoint cast, fixes its path-homotopy class. -/
private lemma quotientMap_subtypeVal_retraction {X : Type u} [TopologicalSpace X]
    {A : Set X} (r : Set.Retraction A) (a₀ : A)
    (p : Path.Homotopic.Quotient a₀ a₀) :
    ((Path.Homotopic.Quotient.map p ⟨Subtype.val, continuous_subtype_val⟩).map
      r.toContinuousMap).cast (r.apply_coe a₀).symm (r.apply_coe a₀).symm = p := by
  -- On representatives, the retraction law identifies the mapped path pointwise.
  induction p using Path.Homotopic.Quotient.ind with
  | mk path =>
      rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_cast]
      congr 1
      ext t
      exact congrArg Subtype.val (r.leftInverse (path t))

/-- Exercise 52.4. A retraction of a topological space onto a subspace induces a
surjective homomorphism on fundamental groups at every basepoint in the subspace. -/
theorem mapOfEq_surjective_of_retraction {X : Type u} [TopologicalSpace X]
    {A : Set X} (r : Set.Retraction A) (a₀ : A) :
    Function.Surjective (mapOfEq r.toContinuousMap (r.apply_coe a₀)) := by
  -- Lift each loop class along the continuous subtype inclusion.
  let inclusion : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  intro p
  refine ⟨map inclusion a₀ p, ?_⟩
  -- Expand the induced maps and invoke the path-level retraction computation.
  apply MulOpposite.unop_injective
  rw [mapOfEq_apply, map_apply, FundamentalGroup.map_apply]
  simp only [MulOpposite.unop_op]
  exact quotientMap_subtypeVal_retraction r a₀ p.unop

end FundamentalGroup.LeftToRight
