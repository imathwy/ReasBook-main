import Mathlib
import StacksProject_2024.Chap21.Definition_21_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasProducts AddCommGrpCat.{v}]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt (Sheaf J AddCommGrpCat.{v})]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{v})]
variable {U : C} [HasFiniteProducts (Over U)]
variable {ι : Type w}

/-- The degree-`n` Čech intersection index type of the covering family `family`. -/
private abbrev coverIntersectionIndex (family : ι → Over U) (n : ℕ) :=
  (((FormalCoproduct.mk ι family).cech).obj (op (SimplexCategory.mk n))).I

/-- The underlying object of `C` of the `i`-th degree-`n` Čech intersection of `family`. -/
private abbrev coverIntersectionObject (family : ι → Over U) (n : ℕ)
    (i : coverIntersectionIndex family n) : C :=
  ((((FormalCoproduct.mk ι family).cech).obj (op (SimplexCategory.mk n))).obj i).left

-- Proof sketch: apply the spectral sequence of Lemma `21.10.6`. The hypothesis says that every
-- positive cohomology presheaf `F.cohomologyPresheaf q` with `q > 0` vanishes on each term of the
-- Čech nerve of `family`, so its associated Čech complex is zero and the `E₂`-page is
-- concentrated on the `q = 0` row. The spectral sequence therefore degenerates at `E₂`, and the
-- remaining row identifies `\check H^p(\mathcal U, \mathcal F)` with `H^p(U, \mathcal F)`.
/-- Lemma 21.10.7: if every positive-degree cohomology group of `F` vanishes on every iterated
Čech intersection of the covering family `family`, then the degree-`p` Čech cohomology of `F`
with respect to `family` is canonically isomorphic to the site cohomology `H^p(U, F)`. The
iterated intersections are formalized by the objects `coverIntersectionObject family n i`. -/
theorem cechCohomology_iso_siteCohomology_of_acyclic_intersections
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (F : Sheaf J AddCommGrpCat.{v})
    (hacyclic : ∀ (q : ℕ) (_hq : 0 < q) (n : ℕ) (i : coverIntersectionIndex family n),
      IsZero (F.H' q (coverIntersectionObject family n i)))
    (p : ℕ) :
    IsIsomorphic
      (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) p)
      (F.H' p U) := sorry

end CategoryTheory
