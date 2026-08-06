import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_2

universe u

-- Semantic search hits: `instUCompactlyGeneratedSpaceQuotient`,
-- `isQuotientMap_quotient_mk'`; local Chapter 5 precedent:
-- `compactlyGeneratedWeakHausdorffSpace_iff_isClosed_preimage_diagonal_of_isQuotientMap`.

open Set

section

variable {X : Type u}

/-- The equivalence relation defining `Quotient S` is exactly the preimage of the diagonal under
the quotient map `X × X → Quotient S × Quotient S`. -/
theorem quotient_preimage_diagonal_eq_relation (S : Setoid X) :
    ((Prod.map (Quotient.mk' : X → Quotient S) Quotient.mk') ⁻¹' diagonal (Quotient S)) =
      ({p : X × X | S.r p.1 p.2} : Set (X × X)) := by
  ext p
  simp [diagonal]

end

section

variable {X : Type u} [TopologicalSpace X]

/-- Remark 5.2.3. A quotient of a compactly generated space by a closed equivalence relation is
compactly generated. Here the closed equivalence relation on `X` is represented by the closed
subset `{p : X × X | S.r p.1 p.2}` of `X × X`, and "compactly generated" uses the Chapter 5
owner `CompactlyGeneratedWeakHausdorffSpace`. -/
theorem compactlyGeneratedWeakHausdorffSpace_quotient_of_isClosed_relation
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] (S : Setoid X)
    (hS : IsClosed ({p : X × X | S.r p.1 p.2} : Set (X × X))) :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} (Quotient S) := by
  let q : X → Quotient S := Quotient.mk'
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hΔ : IsClosed ((Prod.map q q) ⁻¹' diagonal (Quotient S)) := by
    simpa [q] using (quotient_preimage_diagonal_eq_relation S).symm ▸ hS
  exact
    (compactlyGeneratedWeakHausdorffSpace_iff_isClosed_preimage_diagonal_of_isQuotientMap q hq).2
      hΔ

/-- A `Fact`-packaged closed equivalence relation on a compactly generated space yields a
compactly generated quotient. -/
instance instCompactlyGeneratedWeakHausdorffSpaceQuotientOfFactIsClosedRelation
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] (S : Setoid X)
    [hS : Fact (IsClosed ({p : X × X | S.r p.1 p.2} : Set (X × X)))] :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} (Quotient S) :=
  compactlyGeneratedWeakHausdorffSpace_quotient_of_isClosed_relation S hS.out

end
