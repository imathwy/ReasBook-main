import Mathlib
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import stacks_project.Chap20.Definition_20_26_14

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

section

/-
Domain-style sampling for Lemma 20.50.6:
- primary domain: localization of symmetric monoidal homotopy categories to derived categories of
  `\mathcal O_X`-modules on a ringed space;
- sampled owner declarations:
  `CategoryTheory.LocalizedMonoidal`,
  `CategoryTheory.Localization.Monoidal.toMonoidalCategory`,
  `CategoryTheory.Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal`,
  `CategoryTheory.derivedCategory_moduleCat_symmetricCategory`,
  `CategoryTheory.SymmetricCategory`;
- best owner abstraction: the public owner is the `SymmetricCategory` structure on
  `DerivedCategory (RingedSpace.Modules X)`, obtained from the canonical localization functor
  `DerivedCategory.Qh : K(X) ⥤ D(X)` by transporting the owner instance on `LocalizedMonoidal`;
- primitive data: the ringed space `X`, the homotopy category `K(X)`, the derived category
  `D(X)`, and the monoidal stability of quasi-isomorphisms in `K(X)`;
- derived API: the public owner is the localized symmetric structure on `D(X)`; its monoidal
  superclass is still needed explicitly so the symmetric instance can be stated on the owner type.

Layer triage:
- `source-facing`: the symmetric monoidal structure on `D(\mathcal O_X)`;
- `core/canonical`: `DerivedCategory (RingedSpace.Modules X)` together with `LocalizedMonoidal`;
- `bridge/view`: any later comparison with a source-facing derived tensor-product owner belongs in
  a separate bridge file, not in the public owner API here.
-/

variable {X : RingedSpace.{u}}
variable [CategoryWithHomology (RingedSpace.Modules X)]
local notation "KMod" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)
variable [MonoidalCategory (HomotopyCategory (RingedSpace.Modules X) (up ℤ))]
variable [SymmetricCategory (HomotopyCategory (RingedSpace.Modules X) (up ℤ))]

-- Proof sketch: quasi-isomorphisms in `K(\mathcal O_X)` are detected on homology, and the tensor
-- product on the homotopy category is induced by the symmetric monoidal tensor product on cochain
-- complexes. Tensoring two quasi-isomorphisms therefore again yields a quasi-isomorphism.
/-- Quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes are stable
under tensor product. -/
private theorem homotopyCategory_quasiIso_isMonoidal :
    (Qis).IsMonoidal := by
  sorry

/-- The monoidal category structure on `D(\mathcal O_X)` obtained by localizing the tensor product
on the homotopy category of complexes of `\mathcal O_X`-modules. -/
noncomputable instance : MonoidalCategory DMod := by
  let _ : (Qis).IsMonoidal := homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : MonoidalCategory
      (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (𝟙_ KMod)))))

/-- Lemma 20.50.6: the derived category `D(\mathcal O_X)` inherits a symmetric monoidal
structure by localizing the symmetric monoidal structure on the homotopy category of complexes of
`\mathcal O_X`-modules, with the usual associativity and commutativity constraints. -/
noncomputable instance : SymmetricCategory DMod := by
  let _ : (Qis).IsMonoidal := homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : SymmetricCategory
      (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (𝟙_ KMod)))))

end

end AlgebraicGeometry.RingedSpace
