import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall / owner check:
-- `lean_leansearch` recalled the canonical morphism predicate `QuasiCompact`.
-- Local Chapter 29 precedent supplies the source-facing sheaf owners `RelativelyVeryAmple`
-- and `RelativelyAmple`, so this item is the direct implication between those owners.

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- Lemma 29.38.2: let `f : X ⟶ S` be a morphism of schemes and let `\mathcal L`
be an invertible `\mathcal O_X`-module. If `f` is quasi-compact and `\mathcal L` is
relatively very ample over `S`, then `\mathcal L` is relatively ample over `S`. -/
@[stacks 01VN]
theorem RelativelyVeryAmple.relativelyAmple_of_quasiCompact
    [QuasiCompact f] [Scheme.Modules.Invertible L]
    (hL : RelativelyVeryAmple f L) :
    RelativelyAmple f L := sorry

end

end AlgebraicGeometry
