import StacksProject_2024.stacks_project.Chap29.Definition_29_40_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`Definition_29_43_1` exports the source-facing owners `HProjective` and `Projective`, while
`Definition_29_40_1` exports the Chapter 29 affine-local owner `HQuasiProjective`. This file is
therefore the bridge layer relating those existing owners, and records the tagged source lemma
wrappers around that bridge API. -/

section

variable {X S : Scheme.{u}} {f : X ⟶ S}

@[stacks 01W9]
/-- Lemma 29.43.3 (1): an H-projective morphism is H-quasi-projective. -/
theorem HProjective.toHQuasiProjective
    (hf : HProjective f) :
    HQuasiProjective f := sorry

instance instHQuasiProjectiveOfHProjective [hf : HProjective f] :
    HQuasiProjective f :=
  hf.toHQuasiProjective

/- Lemma 29.43.3 (2) is the canonical bridge
`AlgebraicGeometry.HProjective.toProjective` already exported by
`Definition_29_43_1`. -/

#check AlgebraicGeometry.HProjective.toProjective

end

end AlgebraicGeometry
