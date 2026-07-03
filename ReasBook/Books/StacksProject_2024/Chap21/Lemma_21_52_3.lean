import Mathlib
import StacksProject_2024.Chap18.Lemma_18_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "DMod" => DerivedCategory Mod

attribute [local instance] HasDerivedCategory.standard

variable [Abelian Mod]

local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/- Domain-style sampling for Lemma 21.52.3:
- primary domain: bounded-below coproduct preservation in the derived category of sheaves of
  modules, expressed by the represented `Hom` functor from `j_{U!}\mathcal O_U[0]`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_homEquiv`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `DerivedCategory.singleFunctor`,
  `CategoryTheory.preadditiveCoyoneda.obj`;
- best owner abstraction: the source-facing owner is
  `localizedStructureModuleExtensionByZeroDegreeZero`, while the canonical hypothesis layer is
  ordinary sheaf cohomology via `Sheaf.cohomologyPresheafFunctor` on underlying additive sheaves;
- primitive data: the object `U`, the direct-sum compatibility of the ordinary cohomology
  functors `H^p(U, -)`, and the bounded-below coproduct object `∐ M`;
- derived API: the represented `Hom`-functor coproduct comparison for
  `j_{U!}\mathcal O_U[0]`.

Source/core/bridge triage:
- `source-facing`: the bounded-below coproduct comparison for `j_{U!}\mathcal O_U[0]`;
- `core/canonical`: `Sheaf.cohomologyPresheafFunctor` together with the owner
  `localizedStructureModuleExtensionByZero 𝒪 U`;
- `bridge/view`: `preadditiveCoyoneda.obj (op (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U))`.
-/

/-- The degree-zero derived object attached to the standard generator `j_{U!}\mathcal O_U`. -/
abbrev localizedStructureModuleExtensionByZeroDegreeZero
    (U : C) : DMod :=
  (single0).obj (localizedStructureModuleExtensionByZero 𝒪 U)

-- Proof sketch: identify `Hom_D(j_{U!}\mathcal O_U[0], -)` with the degree-zero objectwise
-- cohomology functor at `U` using the adjunction from `18.19.2.1`. Then choose a lower bound for
-- the coproduct object `∐ M_i`, represent the summands by uniformly bounded-below complexes of
-- injectives, take their termwise direct sum, and apply the hypothesis that `H^p(U, -)` commutes
-- with direct sums to compare the resulting cohomology groups.
/- Lemma 21.52.3: if for a ringed site `(\mathcal C, \mathcal O)` and an object `U` the functors
`\mathcal F \mapsto H^p(U, \mathcal F)` commute with direct sums for all `p`, then the degree-zero
derived object attached to `j_{U!}\mathcal O_U` is compact with respect to bounded-below direct
sums: whenever a family `M_i` in `D(\mathcal O)` has a coproduct whose total object is bounded
below, the Hom group from `j_{U!}\mathcal O_U[0]` to that coproduct is canonically the direct sum
of the Hom groups to the summands. In Lean this canonical direct-sum comparison is encoded as
preservation of the coproduct colimit by the represented functor. -/
instance localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_boundedBelow
    (U : C) {ι : Type u} (M : ι → DMod) [HasCoproduct M]
    (hcomm :
      ∀ (p : ℕ) (ι : Type u),
        PreservesColimitsOfShape (Discrete ι)
          (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
            Sheaf.cohomologyPresheafFunctor J p ⋙
              (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))
    (hM : ∃ a : ℤ, (∐ M).IsGE a) :
    PreservesColimit (Discrete.functor M)
      (preadditiveCoyoneda.obj
        (op (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U))) := by
  sorry

end

end SheafOfModules.RingedSite
