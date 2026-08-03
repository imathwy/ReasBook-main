import Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_lemma_6_4
import Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3

open IntersectionCut
open scoped BigOperators Matrix

-- This theorem extends the Section 6.2 corner/intersection-cut owner API from
-- `ch6_sec6_2_theorem_6_5` by adding the Theorem 6.12 source-facing notions while reusing the
-- current import path's equality-face owner `face_set` and the Chapter 3
-- `facet_defining_inequality` owner.

noncomputable section

section Theorem612

variable {n p k : ℕ}

/-- The equality face of the lower inequality `δ ≤ γ ⬝ᵥ x` is the same as the equality face of
the canonical valid-inequality owner `(-γ) ⬝ᵥ x ≤ -δ`. -/
theorem face_set_neg_eq
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    face_set P (-γ) (-δ) = face_set P γ δ := by
  ext x
  simp [mem_face_set_iff]

/-- A lower inequality `δ ≤ γ ⬝ᵥ x` is a nontrivial facet-defining inequality for `P` when the
equivalent Chapter 3 inequality `(-γ) ⬝ᵥ x ≤ -δ` is facet-defining and the original lower
inequality does not already hold on the whole nonnegative orthant. -/
def IsNontrivialFacetDefiningGeInequality
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) : Prop :=
  facet_defining_inequality P (-γ) (-δ) ∧
    ¬ ∀ x : Fin k → ℝ, (∀ j : Fin k, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x

/-- `IsNontrivialFacetDefiningGeInequality P γ δ` unfolds to the canonical facet-defining owner for
`(-γ) ⬝ᵥ x ≤ -δ`, together with failure of `δ ≤ γ ⬝ᵥ x` on the whole nonnegative orthant. -/
theorem isNontrivialFacetDefiningGeInequality_iff
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    IsNontrivialFacetDefiningGeInequality P γ δ ↔
      facet_defining_inequality P (-γ) (-δ) ∧
        ¬ ∀ x : Fin k → ℝ, (∀ j : Fin k, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  Iff.rfl

/-- A nontrivial facet-defining lower inequality is equivalently a nontrivial valid lower
inequality together with the canonical Chapter 3 facet-defining owner for `(-γ) ⬝ᵥ x ≤ -δ`. -/
theorem isNontrivialFacetDefiningGeInequality_iff_isNontrivialValidGeInequality
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    IsNontrivialFacetDefiningGeInequality P γ δ ↔
      facet_defining_inequality P (-γ) (-δ) ∧
        IsNontrivialValidGeInequality P γ δ := by
  rw [isNontrivialFacetDefiningGeInequality_iff,
    isNontrivialValidGeInequality_iff_is_valid_inequality_neg]
  constructor
  · rintro ⟨hfacet, hnontrivial⟩
    exact ⟨hfacet, facet_defining_inequality_valid hfacet, hnontrivial⟩
  · rintro ⟨hfacet, hvalid, hnontrivial⟩
    exact ⟨hfacet, hnontrivial⟩

namespace IsNontrivialFacetDefiningGeInequality

/-- A nontrivial facet-defining lower inequality is, in particular, nontrivially valid. -/
theorem nontrivialValid
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    IsNontrivialValidGeInequality P γ δ :=
  (isNontrivialFacetDefiningGeInequality_iff_isNontrivialValidGeInequality P γ δ).mp h |>.2

/-- The canonical Chapter 3 facet-defining owner attached to a nontrivial facet-defining lower
inequality. -/
theorem facetDefiningNeg
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    facet_defining_inequality P (-γ) (-δ) :=
  h.1

/-- A nontrivial facet-defining lower inequality does not already hold on the whole nonnegative
orthant. -/
theorem not_validOnNonnegativeOrthant
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    ¬ ∀ x : Fin k → ℝ, (∀ j : Fin k, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  h.2

/-- A nontrivial facet-defining lower inequality yields the canonical Chapter 3 valid-inequality
owner for `(-γ) ⬝ᵥ x ≤ -δ`. -/
theorem isValidInequalityNeg
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    is_valid_inequality P (-γ) (-δ) :=
  facet_defining_inequality_valid h.facetDefiningNeg

/-- The equality face of a nontrivial facet-defining lower inequality is a Chapter 3 facet in the
`is_facet` sense. -/
theorem isFacet
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    is_facet P (face_set P γ δ) := by
  simpa [face_set_neg_eq] using facet_defining_inequality_is_facet h.facetDefiningNeg

end IsNontrivialFacetDefiningGeInequality

/-- An inequality `γ ⬝ᵥ x ≥ δ` for `corner(B)` is an intersection cut when `δ > 0` and, after
normalizing the right-hand side to `1`, its coefficient vector is the intersection-cut
coefficient vector of some closed convex `ℤ^p × ℝ^(n - p)`-free set containing the apex in its
interior. -/
def IsIntersectionCutInequality
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (γ : Fin k → ℝ)
    (δ : ℝ) : Prop :=
  0 < δ ∧
    ∃ C : Set (Fin n → ℝ),
      IsClosed C ∧
        Convex ℝ C ∧
          xbar ∈ interior C ∧
            Disjoint (interior C) (mixed_integer_prefix_lattice hpn) ∧
              γ = δ • intersection_cut_coeff C xbar rays

/-- `IsIntersectionCutInequality hpn xbar rays γ δ` unfolds to a positive right-hand side and a
closed convex lattice-free set whose intersection-cut coefficients, scaled by `δ`, give `γ`. -/
theorem isIntersectionCutInequality_iff
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    IsIntersectionCutInequality hpn xbar rays γ δ ↔
      0 < δ ∧
        ∃ C : Set (Fin n → ℝ),
          IsClosed C ∧
            Convex ℝ C ∧
              xbar ∈ interior C ∧
                Disjoint (interior C) (mixed_integer_prefix_lattice hpn) ∧
                  γ = δ • intersection_cut_coeff C xbar rays :=
  Iff.rfl

namespace IsIntersectionCutInequality

/-- An intersection cut has positive right-hand side. -/
theorem rhs_pos
    {hpn : p ≤ n}
    {xbar : Fin n → ℝ}
    {rays : Fin k → Fin n → ℝ}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsIntersectionCutInequality hpn xbar rays γ δ) :
    0 < δ :=
  h.1

/-- An intersection cut comes from a closed convex `ℤ^p × ℝ^(n - p)`-free set containing the apex
in its interior. -/
theorem exists_closed_convexSet
    {hpn : p ≤ n}
    {xbar : Fin n → ℝ}
    {rays : Fin k → Fin n → ℝ}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsIntersectionCutInequality hpn xbar rays γ δ) :
    ∃ C : Set (Fin n → ℝ),
      IsClosed C ∧
        Convex ℝ C ∧
          xbar ∈ interior C ∧
            Disjoint (interior C) (mixed_integer_prefix_lattice hpn) ∧
              γ = δ • intersection_cut_coeff C xbar rays :=
  h.2

end IsIntersectionCutInequality

/-- Theorem 6.12. Every nontrivial facet-defining inequality for `corner(B)` is an intersection
cut. Concretely, after normalizing the right-hand side to `1`, the coefficient vector comes from
the intersection-cut coefficients of a closed convex `ℤ^p × ℝ^(n - p)`-free set containing the
apex in its interior. -/
theorem nontrivial_facet_defining_inequality_is_intersection_cut
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (γ : Fin k → ℝ)
    (δ : ℝ)
    (hfacet :
      IsNontrivialFacetDefiningGeInequality (corner_polyhedron hpn xbar rays) γ δ) :
    IsIntersectionCutInequality hpn xbar rays γ δ := sorry

end Theorem612
