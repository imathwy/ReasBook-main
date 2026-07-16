import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section

variable {X : Type*} {Y : Type*} {ι : Type*} {α : Type*}
variable [Fintype ι]
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [AddCommMonoid X]
variable [HasPairing X Y α] [HasPairingAddLeft X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.4.1 states that the Fenchel conjugate of a finite infimal
  convolution of a finite family is the pointwise sum of the individual conjugates.
- `core/canonical`: the project owners already present are `finiteInfimalConvolution` for
  `f₁ □ ⋯ □ f_m` and `convexConjugate` with notation `f⋆` for `f*`; for the codomain-general
  `WithTopBot α` identity, the relevant owner-side side condition is direct exclusion of the value
  `⊥`, stated as `∀ i x, f i x ≠ ⊥`.
- the ambient owner abstraction for the pairing term is `HasPairing X Y α` together with
  `HasPairingAddLeft X Y α`, since the
  equality uses only additivity of finite decompositions in the primal variable; the source
  linear and inner-product settings are specializations through canonical bridge instances from
  `HasLinearPairing`. At the
  codomain level, the `WithTopBot α` conjugacy/infimal-convolution identities are kept at the
  minimal lattice/additive-order layer (`ConditionallyCompleteLattice` + `AddCommGroup`) rather
  than a concrete numeric model or a linear-order specialization.
- `bridge/view`: the textbook properness wording is exposed only as a thin companion theorem,
  because at the owner level it reduces immediately to the `⊥`-exclusion hypothesis above via
  `Function.IsProper.ne_bot`.

Domain-style sampling used here:
- `finiteInfimalConvolution` and its decomposition companion API from Text 5.4.1;
- `convexConjugate` and its scoped notation `f⋆` from Defn 12.2;
- `HasPairing` / `HasPairingAddLeft` from `Chap01.HasPairing`, which are the chapter owners for
  the primal-additive pairing identities used by finite decomposition formulas;
- the chapter predicate `Function.IsProper` from Definition 4.6;
- `Function.isConvex_finiteInfimalConvolution` from Theorem 5.4, which is a
  derived convexity result for the owner `finiteInfimalConvolution`, not primitive data for this
  conjugacy identity.

Primitive data vs derived API:
- primitive input: a finite family `f : ι → X → WithTopBot α`;
- owner-side hypothesis actually used by the displayed identity: `∀ i x, f i x ≠ ⊥`;
- derived API: the owner-side finite-family conjugacy equality itself and its thin properness-form
  specialization.

Layer target: `core/canonical`. The main public theorem below is stated for an arbitrary finite
index type on the chapter pairing owner augmented by primal additivity, with the minimal
owner-side `⊥`-exclusion hypothesis; the source-facing properness form is kept only as a thin
companion specialization.
-/

-- Proof sketch: expand the Fenchel conjugate of the finite infimal convolution using the
-- decomposition formula for `finiteInfimalConvolution`, interchange the outer supremum with the
-- supremum over all finite decompositions, and then separate the resulting expression into the sum
-- of the independent Fenchel suprema defining the individual conjugates. Additivity of the
-- pairing in the primal variable is the only ambient structure needed to rewrite the pairing of a
-- decomposition sum as the sum of the pairings. The only function-side exclusion needed at this
-- owner level is that no summand
-- takes the value `⊥`, so that `WithTopBot α` addition does not encounter the `⊥ + ⊤` pathology.
/-- Theorem 16.4.1 in owner form: for a finite family on a pairing additive in the primal
variable, and hence in particular in the linear and self-paired inner-product settings of the
source, if each summand is
never equal to `⊥`, then the Fenchel conjugate of the finite infimal convolution is the pointwise
sum of the individual conjugates. The textbook properness wording is recovered at use sites via
`Function.IsProper.ne_bot`. -/
theorem convexConjugate_finiteInfimalConvolution_eq_sum
    (f : ι → X → WithTopBot α)
    (hf_ne_bot : ∀ i x, f i x ≠ ⊥) :
    (finiteInfimalConvolution f)⋆ = (∑ i, (f i)⋆ : Y → WithTopBot α) := sorry

/-- Properness-form specialization of Theorem 16.4.1. This companion adds no new mathematics: it
only repackages the owner-side `⊥`-exclusion as the canonical consequence
`Function.IsProper.ne_bot`. -/
theorem convexConjugate_finiteInfimalConvolution_eq_sum_of_proper
    (f : ι → X → WithTopBot α)
    (hf_proper : ∀ i, (f i).IsProper) :
    (finiteInfimalConvolution f)⋆ = (∑ i, (f i)⋆ : Y → WithTopBot α) :=
  convexConjugate_finiteInfimalConvolution_eq_sum f
    (fun i ↦ (hf_proper i).ne_bot)

end
