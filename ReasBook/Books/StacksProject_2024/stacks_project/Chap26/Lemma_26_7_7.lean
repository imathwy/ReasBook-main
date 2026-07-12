import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u})

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-module colimit owner
-- `AlgebraicGeometry.Scheme.Modules.instHasColimits` and the quasi-coherent owner predicate
-- `SheafOfModules.IsQuasicoherent`; local Chapter 26 precedent states affine quasi-coherence on
-- `(Spec R).Modules`.

/-- Lemma 26.7.7 (1): for the affine scheme `X = Spec(R)`, the direct sum, equivalently the
categorical coproduct, of an arbitrary family of quasi-coherent `\mathcal O_X`-modules is
quasi-coherent. -/
@[stacks 01ID]
theorem isQuasicoherent_coproduct {ι : Type u} (F : ι → (Spec R).Modules)
    (hF : ∀ i, (F i).IsQuasicoherent) :
    (∐ F).IsQuasicoherent := sorry

/-- Lemma 26.7.7 (2): for the affine scheme `X = Spec(R)`, the colimit of any diagram of
quasi-coherent `\mathcal O_X`-modules is quasi-coherent. -/
@[stacks 01ID]
theorem isQuasicoherent_colimit {J : Type u} [Category.{u} J]
    (F : J ⥤ (Spec R).Modules) (hF : ∀ j, (F.obj j).IsQuasicoherent) :
    (colimit F).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
