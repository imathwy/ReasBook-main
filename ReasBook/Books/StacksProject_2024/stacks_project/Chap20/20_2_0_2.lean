import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Topology.Sheaves.AddCommGrpCat

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat
open CategoryTheory
open TopCat.Sheaf

noncomputable section

universe u

namespace TopCat.Sheaf

/-- Helper for 20.2.0.2: the `i`-th higher direct image functor on abelian sheaves along a
continuous map of topological spaces. -/
abbrev higherDirectImageFunctor {X Y : TopCat.{u}}
    [CategoryTheory.HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [CategoryTheory.HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    [CategoryTheory.HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]
    (f : X ⟶ Y) [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
    (i : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived i

/-- Helper for 20.2.0.2: the `i`-th higher direct image of an abelian sheaf along a continuous
map of topological spaces. -/
abbrev higherDirectImage {X Y : TopCat.{u}}
    [CategoryTheory.HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [CategoryTheory.HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    [CategoryTheory.HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]
    (f : X ⟶ Y) [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
    (F : X.Sheaf AddCommGrpCat.{u}) (i : ℕ) :
    Y.Sheaf AddCommGrpCat.{u} :=
  (higherDirectImageFunctor f i).obj F

end TopCat.Sheaf

namespace CategoryTheory
namespace Sheaf

/- Textbook surface notation for direct image of abelian sheaves on topological spaces. -/
local notation:max f:max " _*" => TopCat.Sheaf.pushforward AddCommGrpCat f

/- Lean surface notation for the higher direct image `R^i f_* 𝓕` on topological spaces. A thin
macro keeps instance search at use sites instead of forcing it during notation elaboration. -/
scoped macro:max "R^{" i:term "}_[" f:term "](" F:term ")" : term =>
  `((((TopCat.Sheaf.pushforward AddCommGrpCat $f).rightDerived $i).obj $F))

open scoped TopCat.Sheaf

/- Domain-style sampling for 20.2.0.2:
- primary domain: right derived functors in abelian sheaf categories, computed from injective
  resolutions;
- sampled owner API:
  `TopCat.Sheaf.higherDirectImageFunctor`,
  `TopCat.Sheaf.higherDirectImage`,
  `CategoryTheory.Functor.rightDerived`,
  `CategoryTheory.InjectiveResolution`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`,
  `(f _*)`;
- best owner abstraction: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- primitive data: a continuous map `f : X ⟶ Y`, an abelian sheaf `F` on `X`, and a chosen
  injective resolution `I : InjectiveResolution F`;
- derived API: the canonical comparison
  `R^{i}_[f](F) ≅ H^i((f_* I^•))`, obtained by
  specializing `CategoryTheory.InjectiveResolution.isoRightDerivedObj`.

Source/core/bridge triage:
- `source-facing`: higher direct images of abelian sheaves on topological spaces, computed by
  pushing forward a chosen injective resolution;
- `core/canonical`: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: specialization of that owner theorem to `TopCat.Sheaf.pushforward`.

The main canonical entry remains the direct recall of `isoRightDerivedObj`, but the source-facing
statement for `R^i f_*` should appear as a thin specialization theorem rather than only in prose.
Following the nearby `20_2_0_3` pattern, the specialized reusable entry here should be the actual
comparison isomorphism, with the propositional `IsIsomorphic` form kept only as a companion.
-/

/- 20.2.0.2: the `i`th higher direct image is computed by taking the `i`th cohomology object of
the pushforward of an injective resolution. In the general abelian-category form, for an additive
functor `F` and an injective resolution `I`, this is the canonical isomorphism
`R^i F(X) ≅ H^i(F(I^•))`; for `F = f_*` this is the formula
`R^i f_* 𝓕 ≅ H^i(f_* I^•)`. -/

section

variable {X Y : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]

variable (f : X ⟶ Y)
variable [(f _*).Additive]

/-- 20.2.0.2, propositional form: the higher direct image computed from a chosen injective
resolution is isomorphic to the homology object of the pushed-forward complex. -/
@[stacks 0713]
theorem higherDirectImage_isomorphic_to_homology_pushforward_of_injectiveResolution
    (F : X.Sheaf AddCommGrpCat.{u}) (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic
      (R^{i}_[f](F))
      ((HomologicalComplex.homologyFunctor (Y.Sheaf AddCommGrpCat.{u}) (ComplexShape.up ℕ) i).obj
        (((f _*).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) :=
  -- This is the canonical injective-resolution computation specialized to sheaf pushforward.
  ⟨I.isoRightDerivedObj (f _*) i⟩

end

end Sheaf
end CategoryTheory
