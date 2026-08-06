import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_3_1

open AlgebraicTopology CategoryTheory
open scoped Manifold Topology

noncomputable section

universe u

-- The current chapter-local owners for Construction 20.3.4 are
-- `relativeTopHomologyGroup`, `relativeTopHomologyRestrict`, and
-- `isFundamentalClassAtSubspace`. This file keeps only the source-facing
-- union/intersection restriction names and the two patching/uniqueness statements.

section

variable (Coeff : Type u) [CommRing Coeff]
variable (n : ℕ)
variable (M : Type u) [TopologicalSpace M]

/-- Restriction from `K₁` to `K₁ ∩ K₂` on relative top homology. -/
abbrev relativeTopHomologyRestrictIntersectionLeft (K₁ K₂ : Set M) :
    relativeTopHomologyGroup Coeff n M K₁ ⟶
      relativeTopHomologyGroup Coeff n M (K₁ ∩ K₂) :=
  relativeTopHomologyRestrict Coeff n M (K₁ ∩ K₂) K₁ fun _ hx ↦ hx.1

/-- Restriction from `K₂` to `K₁ ∩ K₂` on relative top homology. -/
abbrev relativeTopHomologyRestrictIntersectionRight (K₁ K₂ : Set M) :
    relativeTopHomologyGroup Coeff n M K₂ ⟶
      relativeTopHomologyGroup Coeff n M (K₁ ∩ K₂) :=
  relativeTopHomologyRestrict Coeff n M (K₁ ∩ K₂) K₂ fun _ hx ↦ hx.2

/-- Restriction from `K₁ ∪ K₂` to `K₁` on relative top homology. -/
abbrev relativeTopHomologyRestrictUnionLeft (K₁ K₂ : Set M) :
    relativeTopHomologyGroup Coeff n M (K₁ ∪ K₂) ⟶
      relativeTopHomologyGroup Coeff n M K₁ :=
  relativeTopHomologyRestrict Coeff n M K₁ (K₁ ∪ K₂) fun _ hx ↦ Or.inl hx

/-- Restriction from `K₁ ∪ K₂` to `K₂` on relative top homology. -/
abbrev relativeTopHomologyRestrictUnionRight (K₁ K₂ : Set M) :
    relativeTopHomologyGroup Coeff n M (K₁ ∪ K₂) ⟶
      relativeTopHomologyGroup Coeff n M K₂ :=
  relativeTopHomologyRestrict Coeff n M K₂ (K₁ ∪ K₂) fun _ hx ↦ Or.inr hx

end

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ E = n)]

/-- Construction 20.3.4 (1): if compact subsets `K₁` and `K₂` carry local fundamental classes
whose restrictions to `K₁ ∩ K₂` agree, then there exists a patched local fundamental class on
`K₁ ∪ K₂` restricting back to the given classes on `K₁` and `K₂`. -/
theorem exists_fundamentalClassAtSubspace_union_of_agree
    (K₁ K₂ : Set M) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (η₁ : relativeTopHomologyGroup R n M K₁)
    (η₂ : relativeTopHomologyGroup R n M K₂)
    (hη₁ : isFundamentalClassAtSubspace R n M K₁ η₁)
    (hη₂ : isFundamentalClassAtSubspace R n M K₂ η₂)
    (hagree :
      (relativeTopHomologyRestrictIntersectionLeft R n M K₁ K₂) η₁ =
        (relativeTopHomologyRestrictIntersectionRight R n M K₁ K₂) η₂) :
    ∃ η : relativeTopHomologyGroup R n M (K₁ ∪ K₂),
      isFundamentalClassAtSubspace R n M (K₁ ∪ K₂) η ∧
        (relativeTopHomologyRestrictUnionLeft R n M K₁ K₂) η = η₁ ∧
        (relativeTopHomologyRestrictUnionRight R n M K₁ K₂) η = η₂ := sorry

/-- Construction 20.3.4 (2): under the compactness hypotheses, two local fundamental classes on
`K₁ ∪ K₂` with the same restrictions to `K₁` and `K₂` are equal. -/
theorem fundamentalClassAtSubspace_union_unique
    (K₁ K₂ : Set M) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {η η' : relativeTopHomologyGroup R n M (K₁ ∪ K₂)}
    (hη : isFundamentalClassAtSubspace R n M (K₁ ∪ K₂) η)
    (hη' : isFundamentalClassAtSubspace R n M (K₁ ∪ K₂) η')
    (hleft :
      (relativeTopHomologyRestrictUnionLeft R n M K₁ K₂) η =
        (relativeTopHomologyRestrictUnionLeft R n M K₁ K₂) η')
    (hright :
      (relativeTopHomologyRestrictUnionRight R n M K₁ K₂) η =
        (relativeTopHomologyRestrictUnionRight R n M K₁ K₂) η') :
    η = η' := sorry

end
