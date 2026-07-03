import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_7_1 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.7.1 is a `bridge/view` item in the chapter convex-analysis API. The owner notions
`effective_domain`, `IsProperExtendedRealFunction`, `is_convex_function`, and
`subdifferential_domain` already live upstream; the chapter-level bridge theorem is
`relativeInterior_effective_domain_subset_subdifferential_domain`. This file combines that owner
theorem with the canonical convex-geometry nonemptiness theorem for `intrinsicInterior ℝ`. The
owner-level result therefore uses only the primitive data needed for the argument: convexity of
`f` and nonemptiness of `effective_domain f`. The textbook proper-convex formulation is kept only
as a thin source-facing corollary, since properness contributes here solely through
`hf.effective_domain_nonempty`. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall intrinsicInterior
recall subdifferential_domain
recall mem_subdifferential_domain
recall intrinsicInterior_nonempty
recall subdifferential_domain_subset_effective_domain

-- Proof sketch: `effective_domain f` is convex because `f` is convex, and it is nonempty by
-- hypothesis. Hence mathlib's owner theorem `intrinsicInterior_nonempty` gives nonemptiness of
-- `intrinsicInterior ℝ (effective_domain f)`, and Proposition 3.7 pushes that set into
-- `subdifferential_domain f`.
/-- Owner-level bridge: a convex extended-real-valued function with nonempty effective domain has
nonempty subdifferential domain. -/
theorem subdifferential_domain_nonempty_of_convex_of_effective_domain_nonempty
    (f : E → EReal) (hconv : is_convex_function f) (hdom : (effective_domain f).Nonempty) :
    (subdifferential_domain f).Nonempty := by
  exact
    ((intrinsicInterior_nonempty (effective_domain_convex_of_is_convex_function hconv)).2
      hdom).mono
      (relativeInterior_effective_domain_subset_subdifferential_domain f hconv)

/-- Proposition 3.7.1: any proper convex extended-real-valued function has a point where the
subdifferential is nonempty. Equivalently, `dom(∂ f)` is nonempty. -/
theorem subdifferential_domain_nonempty_of_proper_convex
    (f : E → EReal) (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f) :
    (subdifferential_domain f).Nonempty :=
  subdifferential_domain_nonempty_of_convex_of_effective_domain_nonempty f hconv
    hf.effective_domain_nonempty

-- Proof sketch: extract `x ∈ subdifferential_domain f` from the owner theorem, rewrite it as
-- `(subdifferential f x).Nonempty`, and recover `x ∈ effective_domain f` because the
-- subdifferential is empty off the effective domain.
/-- Owner-level companion: a convex extended-real-valued function with nonempty effective domain
has a point of its effective domain where the subdifferential is nonempty. -/
theorem exists_subdifferentiable_point_in_effective_domain_of_convex_of_effective_domain_nonempty
    (f : E → EReal) (hconv : is_convex_function f) (hdom : (effective_domain f).Nonempty) :
    ∃ x ∈ effective_domain f, (subdifferential f x).Nonempty := by
  rcases subdifferential_domain_nonempty_of_convex_of_effective_domain_nonempty f hconv hdom with
      ⟨x, hx⟩
  refine ⟨x, subdifferential_domain_subset_effective_domain hx, ?_⟩
  exact (mem_subdifferential_domain).1 hx

/-- Source-facing corollary: any proper convex extended-real-valued function has a point of its
effective domain where the subdifferential is nonempty. -/
theorem exists_subdifferentiable_point_in_effective_domain_of_proper_convex
    (f : E → EReal) (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f) :
    ∃ x ∈ effective_domain f, (subdifferential f x).Nonempty :=
  exists_subdifferentiable_point_in_effective_domain_of_convex_of_effective_domain_nonempty f
    hconv hf.effective_domain_nonempty

end

/-! ### Definition_3_7 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 3.7: the book's relative interior is the canonical convex-geometry notion
`intrinsicInterior ℝ`.
-/
recall intrinsicInterior
recall mem_intrinsicInterior

/-
The closed-ball membership criterion below is a `bridge/view` theorem. Its `core/canonical`
owner is mathlib's `mem_intrinsicInterior`, and the theorem merely rewrites that owner statement
into the textbook metric characterization inside the affine span.
-/
/-- A point lies in the intrinsic interior of `s` exactly when it belongs to the affine hull of `s`
and some positive closed ball around it, intersected with that affine hull, is contained in `s`.
This is the textbook closed-ball characterization of relative interior. -/
theorem mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset {s : Set E} {x : E} :
    x ∈ intrinsicInterior ℝ s ↔
      x ∈ affineSpan ℝ s ∧
        ∃ ε > 0, Metric.closedBall x ε ∩ affineSpan ℝ s ⊆ s := by
  constructor
  · intro hx
    rcases mem_intrinsicInterior.1 hx with ⟨y, hy, rfl⟩
    rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy) with ⟨ε, hε, hεs⟩
    refine ⟨y.property, ε / 2, half_pos hε, ?_⟩
    intro z hz
    exact hεs <| Metric.closedBall_subset_ball (half_lt_self hε) <| by
      change (⟨z, hz.2⟩ : affineSpan ℝ s) ∈ Metric.closedBall y (ε / 2)
      simpa using hz.1
  · rintro ⟨hx, ε, hε, hεs⟩
    refine mem_intrinsicInterior.2 ?_
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    refine mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset (Metric.closedBall_mem_nhds _ hε) fun y hy ↦
        hεs <| by
          refine ⟨?_, y.property⟩
          simpa using hy

end

/-! ### Proposition_3_7 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.7 is a `bridge/view` item in the chapter convex-analysis API: its source-facing
codomain is the owner set `subdifferential_domain`, and the proof is obtained pointwise from
`subdifferential_nonempty_at_relativeInterior_point`. Since the relative-interior hypothesis is
already vacuous when `effective_domain f` is empty and convexity itself handles any `⊥` values at
relative-interior points, this bridge theorem needs only the owner convexity hypothesis. -/
recall effective_domain
recall is_convex_function
recall intrinsicInterior
recall subdifferential_domain
recall subdifferential_nonempty_at_relativeInterior_point

-- Proof sketch: apply the owner theorem pointwise to each
-- `x ∈ intrinsicInterior ℝ (effective_domain f)`.
/-- Proposition 3.7: for a convex extended-real-valued function, the relative interior of `dom(f)`
is contained in the domain of the subdifferential. -/
theorem relativeInterior_effective_domain_subset_subdifferential_domain
    (f : E → EReal) (hconv : is_convex_function f) :
    intrinsicInterior ℝ (effective_domain f) ⊆ subdifferential_domain f :=
  fun _ hx ↦ subdifferential_nonempty_at_relativeInterior_point f _ hconv hx

end

/-! ### Theorem_3_7 (from Chap03) -/
/- Theorem 3.7 is recall-only as a `bridge/view` item in the chapter convex-subdifferential API:
the exact owner theorem is already
`subdifferential_unbounded_of_affineSpan_effective_domain_direction_finrank_lt`, stated on the
continuous-dual owner bridge `strongDualSubdifferential` rather than an expanded set-builder
presentation. The necessary domain hypothesis is part of that proposition statement; the textbook
omission is explained in the source file comments rather than encoded in the public name. -/
recall
  subdifferential_unbounded_of_affineSpan_effective_domain_direction_finrank_lt
