import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_project.Chap17.Lemma_17_3_1
import stacks_project.Chap17.Lemma_17_22_4
import stacks_project.Chap17.«17_23_1_1»

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
  `annihilatorStalkIdeal ℱ x`, built from the canonical inclusion `annihilatorι ℱ`, rather than
  through an ad hoc existential presentation of stalk elements by local sections or a duplicated
  local identification of the unit-module stalk with the stalk ring;
- primitive data:
  a module sheaf `ℱ`, a point `x`, and the finite-type hypothesis on `ℱ`;
- derived API:
  the canonical stalk ideal `annihilatorStalkIdeal ℱ x`, obtained from the inclusion
  `annihilatorι ℱ` after transporting the unit-module stalk to the stalk ring.

Source/core/bridge triage:
- `source-facing`: the stalkwise equality
  `(Ann_{\mathcal O_X}(\mathcal F))_x = Ann_{\mathcal O_{X,x}}(\mathcal F_x)`;
- `core/canonical`: `annihilator`, `annihilatorι`,
  `RingedSpace.stalkModuleCat`, and
  `RingedSpace.moduleStalkHom`;
- `bridge/view`: `RingedSpace.unitStalkLinearMap`, the canonical linear identification of the
  unit-module stalk with `\mathcal O_{X,x}`.

The previous existential statement only unpacked the stalk-image side of this equality. The main
public entry is refined here to the actual ideal equality; the stalk-ideal owner itself now lives
in `17.23.1.1`, and any sectionwise/existential phrasing is derived bridge API rather than the
owner statement. -/

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
theorem stalk_annihilator_eq_module_annihilator
    (ℱ : ModX) (x : X) [ℱ.IsFiniteType] :
    annihilatorStalkIdeal ℱ x =
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  apply le_antisymm
  · exact annihilatorStalkIdeal_le_module_annihilator ℱ x
  · intro r hr
    change r ∈ LinearMap.range
      ((RingedSpace.moduleStalkHom x (annihilatorι ℱ) ≫
        RingedSpace.unitStalkLinearMap x).hom)
    let S : ShortComplex ModX :=
      ShortComplex.mk (annihilatorι ℱ) (selfInternalHomUnitMap ℱ) (kernel.condition _)
    have hS : S.Exact := ShortComplex.exact_kernel (selfInternalHomUnitMap ℱ)
    have hSx : (RingedSpace.stalkShortComplex S x).Exact :=
      (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
    have hrange :
        LinearMap.range (RingedSpace.moduleStalkHom x (annihilatorι ℱ)).hom =
          LinearMap.ker (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom := by
      simpa [S, RingedSpace.stalkShortComplex] using hSx.moduleCat_range_eq_ker
    have hcompare :
        (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ) ≫
            RingedSpace.internalHomStalkComparison ℱ ℱ x).hom₂ =
          (LinearMap.lsmul (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)).comp
            (RingedSpace.unitStalkLinearMap x).hom := by
      sorry
    have hzero_lsmul :
        LinearMap.lsmul (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) r = 0 := by
      ext m
      exact Module.mem_annihilator.mp hr m
    have hker :
        (RingedSpace.unitStalkLinearEquiv x).symm r ∈
          LinearMap.ker (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom := by
      apply LinearMap.mem_ker.mpr
      apply RingedSpace.internalHomStalkComparison_injective_of_isFiniteType ℱ ℱ x
      have hzero :
          (RingedSpace.internalHomStalkComparison ℱ ℱ x).hom
            ((RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom
              ((RingedSpace.unitStalkLinearEquiv x).symm r)) = 0 := by
        apply ModuleCat.hom_injective
        ext m
        change
          ((RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ) ≫
              RingedSpace.internalHomStalkComparison ℱ ℱ x).hom₂
            ((RingedSpace.unitStalkLinearEquiv x).symm r))
            m = 0
        have hm :=
          congrArg
            (fun F ↦ F ((RingedSpace.unitStalkLinearEquiv x).symm r) m) hcompare
        have hzero_rhs :
            ((LinearMap.lsmul (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) ∘ₗ
                ModuleCat.Hom.hom (RingedSpace.unitStalkLinearMap x))
              ((RingedSpace.unitStalkLinearEquiv x).symm r))
              m = 0 := by
          rw [LinearMap.comp_apply]
          rw [show ModuleCat.Hom.hom (RingedSpace.unitStalkLinearMap x)
              ((RingedSpace.unitStalkLinearEquiv x).symm r) = r by
                simpa [RingedSpace.unitStalkLinearMap] using
                  (RingedSpace.unitStalkLinearEquiv x).apply_symm_apply r]
          simpa [LinearMap.ext_iff] using congrArg (fun f ↦ f m) hzero_lsmul
        exact hm.trans hzero_rhs
      exact hzero.trans (by
        simpa using ((RingedSpace.internalHomStalkComparison ℱ ℱ x).hom.map_zero).symm)
    rw [← hrange] at hker
    rcases hker with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    change RingedSpace.unitStalkLinearMap x (RingedSpace.moduleStalkHom x (annihilatorι ℱ) t) = r
    rw [ht]
    simpa [RingedSpace.unitStalkLinearMap] using
      (RingedSpace.unitStalkLinearEquiv x).apply_symm_apply r

end SheafOfModules
