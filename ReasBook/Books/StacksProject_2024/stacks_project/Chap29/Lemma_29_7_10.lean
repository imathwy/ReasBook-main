import Mathlib
import StacksProject_2024.Chap29.Lemma_29_7_9
import StacksProject_2024.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

-- `source-facing`: the Stacks lemma is about agreement on an open subscheme whose
-- scheme-theoretic closure is all of `X`.
-- `core/canonical`: Chapter 29 already owns the reusable density notion
-- `schemeTheoreticallyDense U`.
-- `bridge/view`: the reduced-source companion below rewrites the closure hypothesis into that
-- canonical Chapter 29 owner.

variable {S X Y : Scheme}
variable [X.Over S] [Y.Over S]
variable {U : X.Opens}

/-- Lemma 29.7.10: if two `S`-morphisms `f, g : X ⟶ Y` agree on an open subscheme `U ⊆ X` whose
scheme theoretic closure in `X` is all of `X`, and `Y ⟶ S` is separated, then `f = g`. -/
@[stacks 01RH]
theorem eq_of_restrict_eq_of_schemeTheoreticClosure_eq_self
    {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] [IsSeparated (Y ↘ S)] (hfg : U.ι ≫ f = U.ι ≫ g)
    (hclosure : schemeTheoreticClosure U = X) :
    f = g := by
  sorry

/-- Reduced-source companion form of Lemma 29.7.10. When `U` is reduced, the Chapter 29 owner
`schemeTheoreticallyDense U` provides the reusable hypothesis replacing the explicit closure
equation. -/
theorem eq_of_restrict_eq_of_schemeTheoreticallyDense_of_isReduced
    {f g : X ⟶ Y} [IsReduced U.toScheme] [f.IsOver S] [g.IsOver S]
    [IsSeparated (Y ↘ S)]
    (hU : schemeTheoreticallyDense U) (hfg : U.ι ≫ f = U.ι ≫ g) :
    f = g := by
  have hclosure : schemeTheoreticClosure U = X :=
    (schemeTheoreticClosure_eq_self_iff_schemeTheoreticallyDense_of_isReduced U).mp hU
  exact eq_of_restrict_eq_of_schemeTheoreticClosure_eq_self hfg hclosure

end AlgebraicGeometry
