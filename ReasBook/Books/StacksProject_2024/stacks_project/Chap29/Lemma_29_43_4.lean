import Mathlib
import StacksProject_2024.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
`lean_leansearch` recalled `Scheme.OpenCover` as the canonical owner for target Zariski covers.
Local Chapter 29 precedent already provides the source-facing morphism properties
`LocallyProjective` and `HProjective` in `Definition_29_43_1`, so this item is recorded directly as
the cover-by-`HProjective` reformulation of local projectivity. -/

section

variable {X S : Scheme.{u}}

/-- Lemma 29.43.4: a morphism of schemes is locally projective if and only if there exists an open
cover of the target such that each restricted morphism is H-projective. -/
@[stacks 01WB]
theorem locallyProjective_iff_exists_openCover_hProjective
    (f : X ⟶ S) :
    LocallyProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S,
        ∀ i : 𝒰.I₀, HProjective (f ∣_ ((𝒰.f i).opensRange)) := sorry

end

end AlgebraicGeometry
