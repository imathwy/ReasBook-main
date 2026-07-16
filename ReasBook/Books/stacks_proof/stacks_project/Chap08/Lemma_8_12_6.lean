import stacks_proof.stacks_project.Chap08.Lemma_8_12_6_Support
import Mathlib.Tactic.StacksAttribute

open CategoryTheory.Limits

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

open scoped Functor

variable (u : C ⥤ D) (p : S ⥤ C)
variable [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6: the acyclic iso-comma support proof gives the public fibredness
statement for the localized pushforward projection. -/
theorem pushforwardProjection_isFibered_aux_from_isoComma :
    (u.pushforwardProjection p).IsFibered := by
  -- The heavy strict iso-comma construction now lives in the support module; this wrapper
  -- preserves the public aggregate-file API without redeclaring the support lemmas.
  exact pushforwardProjection_isFibered_aux (u := u) (p := p)

/-- Lemma 8.12.6: with notation and assumptions as in Lemma 8.12.5, the localized pushforward
category `uₚ p` is fibred over `D`. -/
@[stacks 04WG]
theorem pushforwardProjection_isFibered :
    (u.pushforwardProjection p).IsFibered := by
  -- Use the named public auxiliary wrapper so downstream imports keep the same owner theorem.
  exact pushforwardProjection_isFibered_aux_from_isoComma (u := u) (p := p)

/-- Helper for Lemma 8.12.6: owner-level instance packaging for the canonical fibred structure on
`u.pushforwardProjection p`. -/
instance instPushforwardProjectionIsFibered :
    (u.pushforwardProjection p).IsFibered :=
  pushforwardProjection_isFibered u p

end Functor

end

end CategoryTheory
