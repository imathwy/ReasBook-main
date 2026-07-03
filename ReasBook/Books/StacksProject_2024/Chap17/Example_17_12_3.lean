import Mathlib
import StacksProject_2024.Chap10.Definition_10_90_1
import StacksProject_2024.Chap10.Example_10_161_2

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial
open Module.Finite

noncomputable section

local notation "Cinf" => MvPolynomial ℕ+ ℂ

/- Domain-style sampling for Example 17.12.3:
- primary domain: commutative algebra of coherence and Noetherianity for countable-variable
  polynomial rings;
- source-facing owner: the countable polynomial ring `Cinf = MvPolynomial ℕ+ ℂ`;
- inspected owner declarations:
  * `IsCoherentRing R`;
  * `Module.Coherent.finitePresentation_submodule`;
  * `countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian`.
- primitive data: the owner ring `Cinf` and finitely generated ideals in it;
- derived API: finite presentation of finitely generated ideals and the failure of
  `IsNoetherianRing`.

The coherent statement is genuinely source-facing here, so the public surface stays at
`IsCoherentRing Cinf`. The ideal-theoretic clause is a thin companion extracted from that owner
predicate, while part `(2)` directly reuses the Chapter 10 countable-variable theorem.
-/

-- Proof sketch: use the canonical countable-variable owner `Cinf`. For a commutative ring,
-- coherence of the self-module is captured by finite presentation of finitely generated ideals.
/-- Example 17.12.3 (1): the countable polynomial ring `\mathbf{C}[x_1, x_2, x_3, \ldots]`,
modeled as `Cinf`, is coherent as a module over itself. -/
instance complex_countableVariablePolynomialRing_isCoherentRing :
    IsCoherentRing Cinf := by
  sorry

/-- Example 17.12.3 (1), ideal-theoretic form: every finitely generated ideal in
`\mathbf{C}[x_1, x_2, x_3, \ldots]` is finitely presented. -/
theorem complex_countableVariablePolynomialRing_fgIdeal_finitePresentation
    (I : Ideal Cinf) (hI : I.FG) :
    Module.FinitePresentation Cinf I := by
  exact
    (inferInstance : Module.Coherent Cinf Cinf).finitePresentation_submodule I (of_fg hI)

-- Proof sketch: this is exactly the non-Noetherian half of the Chapter 10 countable-variable
-- owner theorem specialized to `ℂ`.
/-- Example 17.12.3 (2): the countable polynomial ring `\mathbf{C}[x_1, x_2, x_3, \ldots]`,
viewed as a module over itself, is not Noetherian. -/
theorem complex_countableVariablePolynomialRing_not_isNoetherianRing :
    ¬ IsNoetherianRing Cinf := by
  exact (countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian ℂ).2
