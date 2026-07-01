import Mathlib
import stacks_project.Chap17.Definition_17_24_1

-- Declarations for this item will be appended below by the statement pipeline.

set_option checkBinderAnnotations false

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace} {n : ℕ}

local notation "OX" => (RingedSpace.ringCatSheaf X)
local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => SheafOfModules.unit OX

/- Domain-style sampling for Definition 17.24.2:
- primary domain: Koszul complexes of `\mathcal O_X`-modules attached to finitely many global
  sections of the structure sheaf;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.koszulComplex`,
  `AlgebraicGeometry.RingedSpace.koszulComplex_X`,
  `SheafOfModules.freeHomEquiv`,
  `SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection`;
- best owner abstraction: the source-facing object is the specialized sheaf Koszul complex, so the
  owner is `koszulComplex`; the map `\mathcal O_X^{\oplus n} \to \mathcal O_X` induced by the
  chosen global sections is only bridge data obtained from `freeHomEquiv`;
- primitive data: a finite family `f : Fin n → 𝒪X.sections`;
- derived API: the induced morphism `(SheafOfModules.free (ULift (Fin n)) : ModX) ⟶ 𝒪X` and the
  resulting specialized complex.

Source/core/bridge triage:
- `source-facing`: the Koszul complex `K_•(\mathcal O_X, f_1, \ldots, f_n)`;
- `core/canonical`: `AlgebraicGeometry.RingedSpace.koszulComplex`;
- `bridge/view`: the passage from `f` to the canonical morphism
  `(𝒪X.freeHomEquiv).symm (f ∘ ULift.down)`. -/

/-- The morphism `\mathcal O_X^{\oplus n} \to \mathcal O_X` induced by a finite family of global
sections of the structure sheaf. -/
noncomputable abbrev koszulFamilyMap (f : Fin n → (𝒪X).sections) :
    (SheafOfModules.free (ULift (Fin n)) : ModX) ⟶ 𝒪X :=
  (SheafOfModules.freeHomEquiv 𝒪X).symm (f ∘ ULift.down)

/-- The induced morphism sends the `i`th tautological basis section of `\mathcal O_X^{\oplus n}`
to the chosen global section `f_i`. -/
theorem sectionsMap_koszulFamilyMap_freeSection
    (f : Fin n → (𝒪X).sections) (i : Fin n) :
    SheafOfModules.sectionsMap (koszulFamilyMap f)
      (SheafOfModules.freeSection (ULift.up i)) = f i := by
  simpa [koszulFamilyMap] using
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (f ∘ ULift.down) (ULift.up i))

/-- Definition 17.24.2: for global sections `f_1, \ldots, f_n` of `\mathcal O_X`, the Koszul
complex `K_•(\mathcal O_X, f_1, \ldots, f_n)` is the specialization of Definition 17.24.1 along
the canonical morphism `\mathcal O_X^{\oplus n} \to \mathcal O_X` induced by the family. -/
noncomputable abbrev koszulComplexOn
    (f : Fin n → (𝒪X).sections) : ChainComplex ModX ℕ :=
  koszulComplex (koszulFamilyMap f)

/-- The degree `m` object of `K_•(\mathcal O_X, f_1, \ldots, f_n)` is the `m`th exterior power of
`\mathcal O_X^{\oplus n}`. -/
theorem koszulComplexOn_X
    (f : Fin n → (𝒪X).sections) (m : ℕ) :
    (koszulComplexOn f).X m =
      (Λ^[m] (SheafOfModules.free (ULift (Fin n)) : ModX)) :=
  rfl

end AlgebraicGeometry.RingedSpace
