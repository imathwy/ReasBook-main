import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_27_14
import stacks_proof.stacks_project.Chap08.Lemma_8_12_5
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6_Support.NormalizedFrontier

open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

open scoped Functor

variable (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: strict iso-comma fibredness is equivalent to fibredness
of the localized pushforward projection, with the strict composite as the source side. -/
private theorem pushforwardProjectionIsoCommaForget_comp_isFibered_iff_pushforwardProjection_isFibered :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
      u.pushforwardProjection p).IsFibered ↔
        (u.pushforwardProjection p).IsFibered := by
  -- Record the imported comparison theorem in the orientation used by the strict frontier.
  exact pushforwardProjectionIsoComma_forget_comp_isFibered_iff (u := u) (p := p)

/-- Helper for Lemma 8.12.6 Support: the comparison with the strict iso-comma model
preserves fibredness, oriented with the localized pushforward projection as the target. -/
private theorem pushforwardProjection_isFibered_iff_isoCommaForget_comp_isFibered :
    (u.pushforwardProjection p).IsFibered ↔
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
        u.pushforwardProjection p).IsFibered := by
  -- Reorient the imported comparison theorem so later steps read from the target invariant.
  exact (pushforwardProjectionIsoCommaForget_comp_isFibered_iff_pushforwardProjection_isFibered
    (u := u) (p := p)).symm

/-- Helper for Lemma 8.12.6 Support: fibredness of the localized pushforward projection
pulls back along the strict iso-comma comparison functor. -/
private theorem pushforwardProjectionIsoCommaForget_comp_isFibered_of_pushforwardProjection_isFibered
    (h :
      (u.pushforwardProjection p).IsFibered) :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
      u.pushforwardProjection p).IsFibered := by
  -- Use the reverse transport direction recorded by the comparison iff.
  exact (pushforwardProjection_isFibered_iff_isoCommaForget_comp_isFibered
    (u := u) (p := p)).mp h

/-- Helper for Lemma 8.12.6 Support: fibredness of the strict iso-comma forgetful
composite descends along the comparison equivalence to the localized pushforward projection. -/
private theorem pushforwardProjection_isFibered_of_isoCommaForget_comp_isFibered
    (hStrict :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
        u.pushforwardProjection p).IsFibered) :
    (u.pushforwardProjection p).IsFibered := by
  -- Apply the forward direction of the comparison iff to transport strict fibredness.
  exact (pushforwardProjectionIsoCommaForget_comp_isFibered_iff_pushforwardProjection_isFibered
    (u := u) (p := p)).mp hStrict

/-- Helper for Lemma 8.12.6 Support: the imported strict normalized-frontier theorem and
the comparison equivalence directly give fibredness of the localized pushforward projection. -/
private theorem pushforwardProjection_isFibered_from_strict_frontier :
    (u.pushforwardProjection p).IsFibered := by
  -- Start from the strict iso-comma fibredness theorem owned by the support frontier.
  have hStrict :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
        u.pushforwardProjection p).IsFibered :=
    pushforwardProjectionIsoCommaForget_comp_isFibered_aux (u := u) (p := p)
  -- Transport that strict-frontier result across the project comparison iff.
  exact pushforwardProjection_isFibered_of_isoCommaForget_comp_isFibered (u := u) (p := p) hStrict

/-- Chap08 Lemma 8 12 6 Support: with notation and assumptions as in Lemma `8.12.5`, the localized category
`u ₚ p` is a fibred category over `D` via its canonical projection
`u.pushforwardProjection p`. -/
@[stacks 04WG]
theorem pushforwardProjection_isFibered_aux :
    (u.pushforwardProjection p).IsFibered := by
  -- Route correction: the strict iso-comma fibredness proof is owned by the support frontier.
  -- The main target only transports that result across the forgetful comparison equivalence.
  exact pushforwardProjection_isFibered_from_strict_frontier (u := u) (p := p)

end Functor

end

end CategoryTheory
