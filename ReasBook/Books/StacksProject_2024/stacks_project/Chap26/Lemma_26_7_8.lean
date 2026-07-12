import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {S : ShortComplex (Spec R).Modules}

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `SheafOfModules.IsQuasicoherent` and `ShortComplex.ShortExact`; local scheme-module precedent
-- states source short exact rows as `ShortComplex X.Modules` and uses the instance-valued
-- predicate `ℱ.IsQuasicoherent`.

/-- Lemma 26.7.8 (1): for a short exact sequence of sheaves of modules on the affine scheme
`Spec(R)`, if the left and middle terms are quasi-coherent, then so is the right term. -/
@[stacks 01IE]
theorem isQuasicoherent_right_of_shortExact_of_left_middle
    (hS : S.ShortExact)
    (h1 : S.X₁.IsQuasicoherent) (h2 : S.X₂.IsQuasicoherent) :
    S.X₃.IsQuasicoherent := sorry

/-- Lemma 26.7.8 (2): for a short exact sequence of sheaves of modules on the affine scheme
`Spec(R)`, if the left and right terms are quasi-coherent, then so is the middle term. -/
@[stacks 01IE]
theorem isQuasicoherent_middle_of_shortExact_of_left_right
    (hS : S.ShortExact)
    (h1 : S.X₁.IsQuasicoherent) (h3 : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := sorry

/-- Lemma 26.7.8 (3): for a short exact sequence of sheaves of modules on the affine scheme
`Spec(R)`, if the middle and right terms are quasi-coherent, then so is the left term. -/
@[stacks 01IE]
theorem isQuasicoherent_left_of_shortExact_of_middle_right
    (hS : S.ShortExact)
    (h2 : S.X₂.IsQuasicoherent) (h3 : S.X₃.IsQuasicoherent) :
    S.X₁.IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
