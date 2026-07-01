import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v w

-- Proof sketch: represent sections over `U` and `U'` by the extension-by-zero modules
-- `j_{U!}\mathcal O_U` and `j_{U'!}\mathcal O_{U'}`. The monomorphism `a : U' ⟶ U` induces a
-- canonical monomorphism between these representing objects, and injectivity of `ℐ` makes
-- precomposition with that mono surjective. Yoneda then identifies this with surjectivity of the
-- restriction map `ℐ(U) → ℐ(U')`.
/-- Lemma 21.12.6: for a sheaf of rings `R` on a site, a monomorphism `a : U' ⟶ U`, and an
injective `R`-module sheaf `ℐ`, the restriction map on sections along `a` is surjective. -/
theorem injective_module_restriction_surjective_of_mono
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U U' : C} (a : U' ⟶ U) [Mono a]
    (ℐ : SheafOfModules R) (hℐ : Injective ℐ) :
    Function.Surjective (ℐ.val.map a.op) := sorry
