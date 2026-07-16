import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_proof.stacks_project.Chap17.Definition_17_23_1
import «stacks_project».Chap17.«17_23_1_1»
import stacks_proof.stacks_project.Chap17.Lemma_17_22_4
import stacks_proof.stacks_project.Chap17.Lemma_17_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]
variable [MonoidalClosed (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)
open scoped AnnihilatorSheaf

/- Domain-style sampling for Lemma 17.23.2:
- primary domain: annihilator sheaves and their stalkwise comparison with annihilator ideals of
  stalk modules on a ringed space;
- sampled owner declarations:
  `SheafOfModules.annihilator`,
  `SheafOfModules.annihilatorι`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `AlgebraicGeometry.RingedSpace.moduleStalkHom`,
  `AlgebraicGeometry.RingedSpace.unitStalkLinearMap`,
  `AlgebraicGeometry.RingedSpace.internalHomStalkComparison_injective_of_isFiniteType`;
- best owner abstraction:
  the source-facing statement is the equality of ideals in the stalk ring `\mathcal O_{X,x}`;
  the annihilator-sheaf side should therefore be expressed via the chapter owner
  `annihilatorStalkIdeal ℱ x`, built from the canonical comparison map
  `annihilatorStalkToRing ℱ x`, rather than through an ad hoc existential presentation of stalk
  elements by local sections or a duplicated local identification of the unit-module stalk with
  the stalk ring;
- primitive data:
  a module sheaf `ℱ`, a point `x`, and the finite-type hypothesis on `ℱ`;
- derived API:
  the canonical stalk ideal `annihilatorStalkIdeal ℱ x`, obtained from the inclusion
  `annihilatorι ℱ` after transporting the unit-module stalk to the stalk ring via
  `annihilatorStalkToRing ℱ x`.

Source/core/bridge triage:
- `source-facing`: the stalkwise equality
  `(Ann_{\mathcal O_X}(\mathcal F))_x = Ann_{\mathcal O_{X,x}}(\mathcal F_x)`;
- `core/canonical`: `annihilator`, `annihilatorι`,
  `RingedSpace.stalkModuleCat`, and
  `RingedSpace.moduleStalkHom`;
- `bridge/view`: `annihilatorStalkToRing ℱ x` and `RingedSpace.unitStalkLinearMap`, identifying
  the annihilator-sheaf stalk with its image ideal inside `\mathcal O_{X,x}`.

The previous existential statement only unpacked the stalk-image side of this equality. The main
public entry is refined here to the actual ideal equality; the stalk-ideal owner itself now lives
in `17.23.1.1`, and any sectionwise/existential phrasing is derived bridge API rather than the
owner statement. -/

/-- Helper for Lemma 17.23.2: stalkwise exactness identifies the image of the annihilator-stalk
map with the kernel of the stalked action map. -/
private theorem stalkAnnihilatorRange_eq_ker_selfInternalHomUnitMap
    (ℱ : ModX) (x : X) :
    LinearMap.range (RingedSpace.moduleStalkHom x (annihilatorι ℱ)).hom =
      LinearMap.ker (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom := by
  let S : ShortComplex ModX :=
    ShortComplex.mk (annihilatorι ℱ) (selfInternalHomUnitMap ℱ)
      (kernel.condition (selfInternalHomUnitMap ℱ))
  have hS : S.Exact := by
    -- Proof comment: the annihilator sheaf is the kernel of the action map by construction.
    simpa [S] using ShortComplex.exact_kernel (selfInternalHomUnitMap ℱ)
  have hx :
      (RingedSpace.stalkShortComplex S x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
  -- Proof comment: pass the exact kernel sequence to the stalk and read it as `range = ker`.
  simpa [S, RingedSpace.stalkShortComplex] using
    ShortComplex.Exact.moduleCat_range_eq_ker hx

/-- Helper for Lemma 17.23.2: once a stalk element of `Ann(ℱ)` maps to the unit-stalk
representative of `r`, its image in the stalk ring is exactly `r`. -/
private theorem annihilatorStalkToRing_eq_of_moduleStalkHom_eq_unitSymm
    (ℱ : ModX) (x : X)
    {t : RingedSpace.stalkModuleCat (Ann(ℱ)) x} {r : X.presheaf.stalk x}
    (ht : (RingedSpace.moduleStalkHom x (annihilatorι ℱ)).hom t =
      (RingedSpace.unitStalkLinearEquiv x).symm r) :
    annihilatorStalkToRing ℱ x t = r := by
  -- Proof comment: expand the stalk-to-ring map and cancel the unit-stalk equivalence.
  change RingedSpace.unitStalkLinearMap x
      ((RingedSpace.moduleStalkHom x (annihilatorι ℱ)).hom t) = r
  rw [ht]
  simpa [RingedSpace.unitStalkLinearMap] using
    (RingedSpace.unitStalkLinearEquiv x).apply_symm_apply r

/-- Helper for Lemma 17.23.2: an annihilating scalar in the stalk ring corresponds to a unit-stalk
element in the kernel of the stalked action map. -/
private theorem internalHomComparison_selfInternalHomUnitMap_germ_apply
    (ℱ : ModX) (x : X) (U : Opens X) (hx : x ∈ U)
    (s : (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op U))
    (m : ℱ.val.obj (op U)) :
    ((RingedSpace.internalHomStalkComparison ℱ ℱ x).hom
        ((RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom
          (TopCat.Presheaf.germ
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf U x hx s)))
      (TopCat.Presheaf.germ ℱ.val.presheaf U x hx m) =
        TopCat.Presheaf.germ ℱ.val.presheaf U x hx
          (unitSectionToRingSection U s • m) := by
  -- TODO: rewrite the unit-stalk germ through `RingedSpace.moduleStalkMap_germ`, then identify
  -- the compared internal-Hom germ by `RingedSpace.uncurry_internalHomStalkComparison` together
  -- with `MonoidalClosed.uncurry_pre_app`, and finally reduce the sectionwise action to
  -- `unitSectionToRingSection U s • m`.
  sorry

/-- Helper for Lemma 17.23.2: after passing through the stalk comparison, the unit-stalk
representative of `r` acts on the stalk module by ordinary scalar multiplication with `r`. -/
private theorem internalHomComparison_selfInternalHomUnitMap_apply_unitStalkSymm
    (ℱ : ModX) (x : X) (r : X.presheaf.stalk x) (m : RingedSpace.stalkModuleCat ℱ x) :
    ((RingedSpace.internalHomStalkComparison ℱ ℱ x).hom
        ((RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom
          ((RingedSpace.unitStalkLinearEquiv x).symm r))) m =
      r • m := by
  -- TODO: represent the unit-stalk element and the module stalk element on a common refinement,
  -- rewrite both germs with `TopCat.Presheaf.germ_res_apply`, apply
  -- `internalHomComparison_selfInternalHomUnitMap_germ_apply` on that common neighborhood, and
  -- identify the result with stalk scalar multiplication via `PresheafOfModules.germ_smul`.
  sorry

private theorem unitStalkSymm_mem_kernel_of_mem_moduleAnnihilator
    (ℱ : ModX) (x : X) [ℱ.IsFiniteType]
    {r : X.presheaf.stalk x}
    (hr : r ∈ Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :
    (RingedSpace.unitStalkLinearEquiv x).symm r ∈
      LinearMap.ker (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom := by
  -- TODO: apply `LinearMap.mem_ker.mpr`, use
  -- `RingedSpace.internalHomStalkComparison_injective_of_isFiniteType ℱ ℱ x` to move to the
  -- stalk internal-Hom module, and then prove the resulting endomorphism is zero by `ext m`
  -- together with `internalHomComparison_selfInternalHomUnitMap_apply_unitStalkSymm` and
  -- `Module.mem_annihilator.mp hr`.
  sorry

-- Proof sketch: Lemma `17.23.1.1` gives the inclusion from the stalk image of
-- `Ann_{\mathcal O_X}(\mathcal F)` into `Ann_{\mathcal O_{X,x}}(\mathcal F_x)` through the owner
-- theorem `annihilatorStalkIdeal_le_module_annihilator`. For the reverse
-- inclusion, use Lemma `17.22.4` to identify the stalk of the internal action map with the stalk
-- action on `\mathcal F_x`; if `\mathcal F` is finite type, injectivity of that comparison shows
-- that any stalk scalar acting by zero on `\mathcal F_x` already comes from the kernel sheaf.
/-- Lemma 17.23.2: for a finite type `\mathcal O_X`-module sheaf `\mathcal F`, the ideal of the
stalk ring `\mathcal O_{X, x}` cut out by the stalk of the annihilator sheaf agrees with the
annihilator ideal of the stalk module `\mathcal F_x`. This is the stalkwise equality
`(\operatorname{Ann}_{\mathcal O_X}(\mathcal F))_x =
\operatorname{Ann}_{\mathcal O_{X, x}}(\mathcal F_x)`. -/
@[stacks 0H2J]
theorem stalk_annihilator_eq_module_annihilator
    (ℱ : ModX) (x : X) [ℱ.IsFiniteType] :
    annihilatorStalkIdeal ℱ x =
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  apply le_antisymm
  · -- Proof comment: the easy inclusion is already packaged by `17.23.1.1`.
    exact annihilatorStalkIdeal_le_module_annihilator ℱ x
  · intro r hr
    have hker :
        (RingedSpace.unitStalkLinearEquiv x).symm r ∈
          LinearMap.ker (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom :=
      unitStalkSymm_mem_kernel_of_mem_moduleAnnihilator ℱ x hr
    rw [← stalkAnnihilatorRange_eq_ker_selfInternalHomUnitMap (ℱ := ℱ) (x := x)] at hker
    rcases hker with ⟨t, ht⟩
    change r ∈ LinearMap.range (annihilatorStalkToRing ℱ x).hom
    refine ⟨t, ?_⟩
    exact annihilatorStalkToRing_eq_of_moduleStalkHom_eq_unitSymm
      (ℱ := ℱ) (x := x) ht

end SheafOfModules
