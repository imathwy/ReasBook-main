import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*} {α : Type*}
variable [Preorder 𝕜] [AddCommMonoid 𝕜] [One 𝕜]
variable [AddCommMonoid α]
variable [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.8.2 forms the function
  `g(x) = inf {∑ i, (fᵢ λᵢ)(x) | λᵢ ≥ 0, ∑ i, λᵢ = 1}` from a finite family of convex
  functions.
- `core/canonical`: the chapter owner abstractions already fixed upstream are
  `StdSimplex 𝕜 ι` from `Definition_2_2_10`, `Function.IsConvex`, `rightScalarMul`,
  the complete-lattice infimum `⨅ w : StdSimplex 𝕜 ι, ...` on function space, and the
  vertical-infimum owner `Function.verticalInfimum`; the proof pattern is governed by the owner
  theorems
  `Function.isConvex_sum_of_bot_lt` and
  `Function.isConvex_verticalInfimum`.
- `bridge/view`: the simplex constraint is carried by `w : StdSimplex 𝕜 ι`, while the
  nonnegative scalar passed to `rightScalarMul` at coordinate `i` is the canonical owner-side
  datum `⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)`; the convexity proof
  views the pointwise `iInf` through the
  corresponding support-set/vertical-infimum construction, but that wrapper is now only internal
  proof data rather than the public owner.
- Primitive data vs derived API: the simplex owner object and the pointwise `iInf` of the
  corresponding weighted-sum functions are the source-facing data; the explicit `sInf`
  coordinate formula and convexity statement are derived API.
- Layer target: `source-facing`; the simplex infimum remains the public object, while the ambient
  convexity, complete-lattice, and right-scalar APIs are reused from the chapter owners instead of
  being redeclared locally.

Domain-style sampling used here:
- `StdSimplex` from `Definition_2_2_10`;
- `StdSimplex.total` from mathlib's `ConvexSpace`;
- `Function.isConvex_sum_of_bot_lt` from `Theorem_5_2`;
- `rightScalarMul` from `Text_5_4_2`;
- the direct simplex `iInf` owner pattern in Theorem 5.8.4's
  `weighted_infimal_max_convolution`;
- `Function.verticalInfimum` from `Theorem_5_3`;
- `Function.isConvex_verticalInfimum` from `Theorem_5_3`.
- `simplex_right_scalar_infimal_maximum` / `weighted_infimal_max_convolution` in Theorems 5.8.3
  and 5.8.4, whose public owner layer already keeps `ι : Type*` abstract.
- `Function.IsConvex.rightScalarMul` from `Text_5_4_2`.
- Ambient minimization: the source-facing definition and its `sInf` specification only use the
  ambient `𝕜`-scalar action needed by `rightScalarMul`, and `StdSimplex` is indexed by an
  arbitrary finite type. The owner therefore stays at the generic codomain
  `WithBotTop α`; the stronger additive commutative `𝕜`-module structure and codomain
  specialization to `WithBotTop 𝕜` appear only in the derived convexity theorem.
- Primitive-vs-derived refinement: the extra pointwise condition `∀ i x, ⊥ < f i x` is not
  redundant data here; it is the owner-minimal hypothesis used to keep the finite-sum convexity
  route inside chapter owners, while the textbook properness wording is recovered below as a thin
  companion
  via `Function.IsProper.bot_lt`.
-/

variable (𝕜)

/-- The simplex-weighted infimum of right scalar multiples of a finite family `f` sends `x` to
the infimum of `∑ i, (f i wᵢ)(x)` over all simplex weights `w : StdSimplex 𝕜 ι`. The public
owner is the direct pointwise `iInf` over the weighted-sum family, rather than a parallel
support-set wrapper. -/
def simplex_right_scalar_infimal_sum (f : ι → E → WithBotTop α) : E → WithBotTop α :=
  ⨅ w : StdSimplex 𝕜 ι,
    w.sum fun i _ ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i

/-- The value of `simplex_right_scalar_infimal_sum f` at `x` is the infimum over simplex
weights of the sum of the corresponding weighted right scalar multiples. -/
theorem simplex_right_scalar_infimal_sum_eq_sInf
    (f : ι → E → WithBotTop α) (x : E) :
    simplex_right_scalar_infimal_sum 𝕜 f x =
      sInf
        {r : WithBotTop α |
          ∃ w : StdSimplex 𝕜 ι,
            r =
              (w.sum fun i _ ↦
                (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i) x} := by
  rw [simplex_right_scalar_infimal_sum, iInf_apply, ← sInf_range]
  congr
  ext r
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by simpa using hw.symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by simpa using hw.symm⟩

end

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

-- Proof sketch: for each simplex weight `w`, the function
-- `x ↦ (w.sum fun i _ ↦ ((⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i)) x`
-- is convex by combining
-- `Function.IsConvex.rightScalarMul` with the chapter owner theorem
-- `Function.isConvex_sum_of_bot_lt`; the pointwise `⊥`-exclusion is needed here and
-- comes from the hypotheses below. The direct public owner
-- `⨅ w : StdSimplex 𝕜 ι,
--   w.sum (fun i _ ↦ ((⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i))` is then
-- viewed through the corresponding
-- support-set/vertical-infimum construction, so Theorem 5.3 yields convexity.
-- Equivalently, for each `i`, let
-- `Kᵢ = {(λ, x, μ) | 0 ≤ λ ∧ (⟨λ, _⟩ : Set.Ici (0 : 𝕜)) •ʳ f i x ≤ μ}` in `𝕜 × E × 𝕜`;
-- convexity of `f i` gives convexity of this scaled-epigraph family. Form the convex set of
-- triples `(w, x, μ)` with `w : StdSimplex 𝕜 ι` and `μ = w.sum (fun i _ ↦ μᵢ)`, where each
-- `(⟨w.weights i, w.nonneg i⟩, x, μᵢ)` lies in `Kᵢ`. Its simplex slice has
-- vertical infimum exactly `simplex_right_scalar_infimal_sum 𝕜 f`, so Theorem 5.3 yields
-- convexity. No dense-order hypothesis on `𝕜` is needed at this owner layer.
/-- Theorem 5.8.2: the simplex-weighted infimum of a finite family of convex functions is convex.
The owner-minimal chapter form keeps the pointwise `⊥`-exclusion needed by the finite-sum
convexity API; the textbook properness wording is recovered below as a thin companion. -/
theorem isConvex_simplex_right_scalar_infimal_sum
    (f : ι → E → WithBotTop 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_sum 𝕜 f).IsConvex 𝕜 := sorry

/-- Textbook properness-form restatement of Theorem 5.8.2. This companion adds no new
mathematics: `(f i).IsProper` is used only to recover the pointwise `⊥`-exclusion
required by `Function.isConvex_simplex_right_scalar_infimal_sum`. -/
theorem isConvex_simplex_right_scalar_infimal_sum_of_proper
    (f : ι → E → WithBotTop 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_sum 𝕜 f).IsConvex 𝕜 := by
  exact isConvex_simplex_right_scalar_infimal_sum f
    (fun i x ↦ (hf_proper i).bot_lt x)
    hf_convex

end Function

end
