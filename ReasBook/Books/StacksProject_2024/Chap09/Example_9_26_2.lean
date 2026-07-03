import Mathlib
import StacksProject_2024.Chap09.Definition_9_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField
open IntermediateField.AdjoinSimple
open scoped RatFunc

/- Domain-style sampling for Example 9.26.2:
- primary domain: simple transcendental field extensions;
- sampled owner declarations:
  `IsPurelyTranscendental`,
  `isPurelyTranscendental_adjoin_simple_of_transcendental`,
  `RatFunc.algEquivOfTranscendental`,
  `transcendental_algebraMap_iff`;
- best owner abstraction: the chapter owner `IsPurelyTranscendental`;
- primitive data: transcendence of `π` over `ℚ`;
- derived API: pure transcendence of `ℚ⟮π⟯` via the upstream simple-extension owner theorem, and
  the resulting rational-function equivalence via `RatFunc.algEquivOfTranscendental`.
-/

/-- The real number `π` is transcendental over `ℚ`. -/
-- Proof sketch: this is the classical transcendence theorem for `π`, for example from
-- Lindemann-Weierstrass.
-- TODO: supply the upstream transcendence theorem `Transcendental ℚ Real.pi`; the rest of this
-- file already reduces the textbook example to that single input.
theorem real_pi_transcendental : Transcendental ℚ Real.pi := sorry

/-- Example 9.26.2: the simple extension `ℚ(π)` is purely transcendental over `ℚ`. -/
-- Proof sketch: since `π` is transcendental over `ℚ`, the distinguished generator of `ℚ⟮π⟯`
-- yields the canonical owner theorem for simple transcendental extensions.
theorem rat_adjoin_pi_isPurelyTranscendental :
    IsPurelyTranscendental ℚ ℚ⟮Real.pi⟯ :=
  isPurelyTranscendental_adjoin_simple_of_transcendental real_pi_transcendental

noncomputable section

section

local instance ratFuncRatAlgebra : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Helper for Example 9.26.2: the canonical rational-function-field model of `ℚ(π)`. -/
-- Route correction: `RatFunc.algEquivOfTranscendental` is structure-valued, so this helper is a
-- `def` under the polynomial-induced `ℚ`-algebra instance on `RatFunc ℚ`.
-- Proof sketch: once `π` is known transcendental, the standard `RatFunc` equivalence specializes
-- directly to the simple extension `ℚ⟮π⟯`.
noncomputable def rat_adjoin_pi_algEquiv_ratFunc :
    RatFunc ℚ ≃ₐ[ℚ] ℚ⟮Real.pi⟯ :=
  RatFunc.algEquivOfTranscendental Real.pi real_pi_transcendental

/- In particular, `ℚ(π)` is `ℚ`-isomorphic to the one-variable rational function field `ℚ(x)`;
this is the canonical specialization of `RatFunc.algEquivOfTranscendental`. -/
#check RatFunc.algEquivOfTranscendental Real.pi real_pi_transcendental

end
