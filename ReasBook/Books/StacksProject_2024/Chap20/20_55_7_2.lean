import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (tensorWithIdealPowerQuotient : ℤ → CochainComplex C ℤ)
variable
  (β : ∀ i : ℤ,
    (tensorWithIdealPowerQuotient i).homology i ⟶
      (tensorWithIdealPowerQuotient (i + 1)).homology (i + 1))
variable (hβ : ∀ i : ℤ, β i ≫ β (i + 1) = 0)

/- Domain-style sampling for 20.55.7.2:
- primary domain: homological algebra of cochain complexes in an abelian category;
- sampled declarations:
  `CochainComplex.of`,
  `CochainComplex.of_x`,
  `CochainComplex.of_d`,
  `modfCohomologyBocksteinComplex`;
- best owner abstraction:
  `source-facing`: `idealQuotientBocksteinCohomologyComplex`,
  `core/canonical`: `CochainComplex.of`,
  `bridge/view`: the specialized degree and differential formulas below;
- primitive data: the degreewise cohomology objects
  `(tensorWithIdealPowerQuotient i).homology i`, the Bockstein maps `β i`, and the relation
  `hβ`;
- derived API: the degree projection and differential projection of the resulting cochain
  complex;
- source/core/bridge triage:
  `source-facing`: the displayed cohomology complex `H^•(M / \mathcal I)`;
  `core/canonical`: the constructor `CochainComplex.of`;
  `bridge/view`: the specialized degree and differential formulas below.

There is no upstream generic owner for an arbitrary square-zero family of Bockstein maps on these
degreewise homology objects. The Chapter 15 declaration `modfCohomologyBocksteinComplex` is the
project analogue, not the owner here. This file should therefore keep the source-facing complex as
a thin abbreviation while deriving all structure from the canonical constructor
`CochainComplex.of`, rather than duplicating any lower-level data API. -/
recall CochainComplex.of

/-- The Bockstein cohomology complex whose degree-`i` term is
`H^i(M \otimes^{\mathbf L} \mathcal I^i / \mathcal I^{i + 1})` and whose differential is the
Bockstein map. -/
abbrev idealQuotientBocksteinCohomologyComplex : CochainComplex C ℤ :=
  CochainComplex.of
    (fun i ↦ (tensorWithIdealPowerQuotient i).homology i)
    β
    hβ

/-- The degree-`i` term of the Bockstein cohomology complex is
`H^i(M \otimes^{\mathbf L} \mathcal I^i / \mathcal I^{i + 1})`. -/
@[simp] theorem idealQuotientBocksteinCohomologyComplex_X (i : ℤ) :
    (idealQuotientBocksteinCohomologyComplex tensorWithIdealPowerQuotient β hβ).X i =
      (tensorWithIdealPowerQuotient i).homology i :=
  rfl

/-- The differential of the Bockstein cohomology complex is the Bockstein map in each degree. -/
@[simp] theorem idealQuotientBocksteinCohomologyComplex_d (i : ℤ) :
    (idealQuotientBocksteinCohomologyComplex tensorWithIdealPowerQuotient β hβ).d i (i + 1) =
      β i := by
  simpa only [idealQuotientBocksteinCohomologyComplex] using
    (CochainComplex.of_d
      (fun i ↦ (tensorWithIdealPowerQuotient i).homology i)
      β
      hβ
      i)

end
