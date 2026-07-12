import StacksProject_2024.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`Definition_29_43_1` provides the source-facing owner `HProjective` on the canonical Chapter 31
projective-bundle surface together with its Chapter 29 companion bridges. This file therefore
records only the base-change lemma for that existing owner. -/

section

variable {X S S' : Scheme.{u}} {f : X ⟶ S}

/-- Lemma 29.43.8: a base change of a H-projective morphism is H-projective. -/
@[stacks 01WF]
theorem HProjective.pullback_snd
    (h : HProjective f) (g : S' ⟶ S) :
    HProjective (pullback.snd f g) := sorry

/-- Any base change of an H-projective morphism is H-projective. -/
instance instHProjectivePullbackSnd [h : HProjective f] (g : S' ⟶ S) :
    HProjective (pullback.snd f g) :=
  h.pullback_snd g

end

end AlgebraicGeometry
