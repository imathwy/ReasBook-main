import Mathlib
import Mathlib.Algebra.Category.Grp.Limits
import stacks_project.Chap21.Definition_21_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type (max u v)}
variable [Limits.HasFiniteProducts (Over U)]

-- Proof sketch: use Lemma `21.10.1` to regard `ℐ` as an injective abelian presheaf, then apply
-- Lemma `21.9.6` to the Čech cohomology functors of the covering family. The degree-zero case is
-- identified with sections over `U` by the sheaf condition from Lemma `21.8.2`, while positive
-- degrees vanish because higher right derived functors of a left exact functor vanish on
-- injective objects.
/-- Lemma 21.10.2: for a covering family `family : ι → Over U` on the slice site `(C / U, J.over
U)` and an injective abelian sheaf `ℐ`, the Čech cohomology of the underlying abelian presheaf is
the group of sections `ℐ(U)` in degree `0` and is zero in every positive degree. -/
theorem cechCohomology_of_injective_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{max u v}) (hℐ : Injective ℐ) (p : ℕ) :
    if hp : p = 0 then
      IsIsomorphic
        (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) p)
        (ℐ.1.obj (op U))
    else
      Limits.IsZero
        (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) p) :=
  sorry

-- Proof sketch: specialize `cechCohomology_of_injective_sheaf` to `p = 0`; the `if` reduces to
-- the degree-zero branch, which is the sheaf-condition identification of Čech `H^0` with
-- sections over `U`.
/-- The degree-zero Čech cohomology of an injective abelian sheaf is canonically isomorphic to its
sections over the covered object. -/
theorem cechCohomology_zero_of_injective_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{max u v}) (hℐ : Injective ℐ) :
    IsIsomorphic
      (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) 0)
      (ℐ.1.obj (op U)) :=
  sorry

-- Proof sketch: regard `ℐ` as injective in abelian presheaves by Lemma `21.10.1`, then identify
-- `\check H^p` with the `p`-th right derived functor of `\check H^0` using Lemma `21.9.6`.
-- Positive derived functors vanish on injective objects, so the resulting Čech cohomology object
-- is zero.
/-- In every positive degree, the Čech cohomology of an injective abelian sheaf vanishes. -/
theorem cechCohomology_isZero_of_pos_of_injective_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{max u v}) (hℐ : Injective ℐ)
    (p : ℕ) (hp : 0 < p) :
    Limits.IsZero
      (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) p) :=
  sorry

end CategoryTheory
