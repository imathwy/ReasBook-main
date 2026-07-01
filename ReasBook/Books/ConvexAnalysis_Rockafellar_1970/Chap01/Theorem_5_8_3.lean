import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*} {α : Type*}
variable [AddCommMonoid 𝕜] [One 𝕜] [Preorder 𝕜] [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

namespace StdSimplex

/-- For fixed simplex weights `w`, the corresponding family of weighted right scalar multiples. -/
def rightScalarFamily (w : StdSimplex 𝕜 ι) (f : ι → E → WithBotTop α) :
    ι → E → WithBotTop α :=
  fun i ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i

end StdSimplex

/-!
Source/core/bridge triage for this item.

-- `source-facing`: Theorem 5.8.3 fixes a finite family of convex functions on a `𝕜`-smul ambient
  and defines `h(x)` as the infimum, over all simplex weights `λ`, of the finite maximum
  of the scaled functions `(fᵢ λᵢ)(x)`. The textbook states the stronger hypotheses that the
  family is nonempty and that the `fᵢ` are proper convex; for this convexity conclusion, both the
  nonemptiness guard and the properness part are redundant.
- `core/canonical`: the chapter-level owner abstractions already exist upstream as
  `StdSimplex 𝕜 ι` from `Definition_2_2_10`, `Function.IsConvex`,
  `Function.IsConvex.iSup`, and `rightScalarMul`.
- `bridge/view`: for fixed simplex data `w : StdSimplex 𝕜 ι`, the textbook finite maximum is
  exactly the owner-side pointwise supremum
  `⨆ i, w.rightScalarFamily f i`; the outer infimum is then
  the direct function-lattice infimum over `w`, while the equivalent `sInf` formula is companion
  bridge API.
- Primitive data vs derived API: `w : StdSimplex 𝕜 ι` is the primitive owner for the simplex
  coefficients; the nonnegative scalar fed to `rightScalarMul` at coordinate `i` is the primitive
  subtype coefficient `⟨w.weights i, w.nonneg i⟩`, packaged by `w.rightScalarFamily`; for fixed
  `w` the finite maximum is the canonical pointwise supremum `⨆ i, w.rightScalarFamily f i`.
  The simplex-indexed function-lattice infimum
  is the source-facing object; its `sInf` value formula and convexity are derived API.
- Layer target: `source-facing`; the theorem keeps the textbook simplex-weighted maximum as its
  public object while reusing the chapter's canonical simplex owner and function-lattice infimum
  instead of a parallel support-set wrapper.

Domain-style sampling used here:
- `StdSimplex` from `Definition_2_2_10`;
- `StdSimplex.weights` and `StdSimplex.nonneg` from `Definition_2_2_10`;
- `StdSimplex.rightScalarFamily` from this item;
- `Function.IsConvex` from `Theorem_4_2` via `Theorem_5_3`;
- `Function.IsConvex.iSup` from `Theorem_5_5`;
- `rightScalarMul` from `Text_5_4_2`;
- `StdSimplex.total` from mathlib's `ConvexSpace`.

Ambient minimization: the source-facing owner `simplex_right_scalar_infimal_maximum` and its
`sInf` specification only use the chapter owner `rightScalarMul`, so they live at the primitive
`𝕜`-smul layer on the ambient space and codomain; they do not require the codomain to equal the
scalar type. The stronger additive commutative `𝕜`-module structure and codomain specialization
to `WithBotTop 𝕜` appear only in the derived convexity theorem through
`Function.IsConvex.rightScalarMul` and `Function.IsConvex.iSup`.
-/

variable (𝕜)

/-- The simplex-weighted infimal maximum attached to a finite family sends `x` to
the infimum, over all nonnegative weights summing to `1`, of the maximum of the values
`(fᵢ λᵢ)(x)`. -/
def simplex_right_scalar_infimal_maximum [Fintype ι] (f : ι → E → WithBotTop α) :
    E → WithBotTop α :=
  ⨅ w : StdSimplex 𝕜 ι, ⨆ i, w.rightScalarFamily f i

-- Proof sketch: the definition is already the direct function-lattice infimum over simplex
-- weights. Evaluating at `x` turns that outer `iInf` into the infimum of the range of the values
-- `⨆ i, (w.rightScalarFamily f i) x`, and `sInf_range` rewrites that infimum as the source-facing
-- `sInf` over exact finite maxima indexed by `w : StdSimplex 𝕜 ι`.
/-- The value of `simplex_right_scalar_infimal_maximum f` at `x` is the infimum over simplex
weights of the finite maximum of the corresponding weighted right scalar multiples. -/
theorem simplex_right_scalar_infimal_maximum_eq_sInf
    [Fintype ι]
    (f : ι → E → WithBotTop α) (x : E) :
    simplex_right_scalar_infimal_maximum 𝕜 f x =
      sInf {r : WithBotTop α |
          ∃ w : StdSimplex 𝕜 ι,
            r = ⨆ i, (w.rightScalarFamily f i) x} := by
  rw [simplex_right_scalar_infimal_maximum, iInf_apply, ← sInf_range]
  congr
  ext r
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    simpa [iSup_apply] using hw.symm
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    simpa [iSup_apply] using hw.symm

end

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [Fintype ι]

-- Proof sketch: for each simplex weight `w`, the function
-- `x ↦ ⨆ i, (w.rightScalarFamily f i) x` is convex by combining
-- `Function.IsConvex.rightScalarMul` with the owner theorem `Function.IsConvex.iSup`.
-- The outer simplex infimum is the source-facing object; the convexity proof uses the same
-- simplex-parameter epigraph/vertical-infimum bridge pattern as the neighboring weighted
-- infimum constructions.
/-- Theorem 5.8.3: if `fᵢ` is a finite family of convex functions on a `𝕜`-module, then
the function
`x ↦ inf {max_i (fᵢ λᵢ)(x) | λᵢ ≥ 0, ∑ i λᵢ = 1}` is convex. -/
theorem Function.isConvex_simplex_right_scalar_infimal_maximum
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_maximum 𝕜 f).IsConvex 𝕜 := sorry

/-- Textbook properness-form restatement of Theorem 5.8.3. This companion adds no new
mathematics: properness is not used in the convexity proof and is kept only as a source-facing
bridge from the stronger textbook wording to the owner-minimal convexity theorem above. -/
theorem Function.isConvex_simplex_right_scalar_infimal_maximum_of_proper
    (f : ι → E → WithBotTop 𝕜)
    (_hf_proper : ∀ i, (f i).IsProper)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_maximum 𝕜 f).IsConvex 𝕜 := by
  simpa using Function.isConvex_simplex_right_scalar_infimal_maximum f hf_convex

end
