import StacksProject_2024.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsReduced X]

-- Semantic recall: `lean_leansearch` surfaced the generic-point owners
-- `genericPoints`, `genericPoints.ofComponent`, and `genericPoints.isGenericPoint_ofComponent`.
-- The canonical owner here is `genericPoints X`; the source-facing irreducible-component phrasing
-- is kept as a companion theorem.

/-- Canonical owner form of Lemma 31.5.12: on a reduced scheme, the weakly associated points are
exactly the generic points. -/
theorem weakAss_eq_genericPoints :
    X.weakAss = genericPoints X := sorry

/-- Canonical pointwise form of Lemma 31.5.12, stated against `genericPoints X`. -/
theorem mem_weakAss_iff_mem_genericPoints (x : X) :
    x ∈ X.weakAss ↔ x ∈ genericPoints X := by
  rw [weakAss_eq_genericPoints (X := X)]

/-- Under the reducedness hypothesis, every weakly associated point of `X` is a generic point. -/
theorem weakAss_subset_genericPoints :
    X.weakAss ⊆ genericPoints X := by
  intro x hx
  exact (mem_weakAss_iff_mem_genericPoints (X := X) x).1 hx

/-- Pointwise implication form of `weakAss_subset_genericPoints`. -/
theorem mem_genericPoints_of_mem_weakAss {x : X}
    (hx : x ∈ X.weakAss) :
    x ∈ genericPoints X :=
  weakAss_subset_genericPoints X hx

/-- Source-facing irreducible-component form of Lemma 31.5.12. -/
theorem mem_weakAss_iff_exists_irreducibleComponent_genericPoint (x : X) :
    x ∈ X.weakAss ↔ ∃ Z : irreducibleComponents X, IsGenericPoint x (Z : Set X) := by
  rw [mem_weakAss_iff_mem_genericPoints (X := X) x]
  constructor
  · intro hx
    let Z : irreducibleComponents X := genericPoints.equiv ⟨x, hx⟩
    have hxZ : x = genericPoints.ofComponent Z := by
      exact (Subtype.ext_iff.mp (genericPoints.ofComponent_apply_equiv ⟨x, hx⟩)).symm
    exact
      ⟨Z, hxZ ▸ genericPoints.isGenericPoint_ofComponent Z⟩
  · rintro ⟨Z, hZ⟩
    have hgp : IsGenericPoint (genericPoints.ofComponent Z : X) (Z : Set X) :=
      genericPoints.isGenericPoint_ofComponent Z
    have hxeq : x = genericPoints.ofComponent Z := IsGenericPoint.eq hZ hgp
    simpa [hxeq] using (genericPoints.ofComponent Z).2

end AlgebraicGeometry.Scheme
