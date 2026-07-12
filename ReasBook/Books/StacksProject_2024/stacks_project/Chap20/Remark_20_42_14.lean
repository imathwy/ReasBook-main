import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap20.«20_14_1_1»
import StacksProject_2024.Chap20.Lemma_20_27_1
import StacksProject_2024.Chap20.Lemma_20_31_8
import StacksProject_2024.Chap20.Remark_20_28_3
import StacksProject_2024.Chap20.Remark_20_42_13

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape
open SheafOfModules.RingedSite
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

section

variable {X' X S' S : RingedSpace.{u}}
variable (h : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S) (f : X ⟶ S)

variable [CategoryWithHomology (RingedSpace.Modules X')]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules S')]
variable [CategoryWithHomology (RingedSpace.Modules S)]

variable [(h^*).Additive]
variable [(f'^*).Additive]
variable [(g^*).Additive]
variable [(f^*).Additive]

variable [MonoidalCategory (ModuleDerived X')]
variable [BraidedCategory (ModuleDerived X')]
variable [MonoidalClosed (ModuleDerived X')]
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]

local notation "DModX" => ModuleDerived X

/- Domain-style sampling for Remark 20.42.14:
- primary domain: derived base change for pushforward combined with pullback/internal-Hom
  comparison in braided closed monoidal derived categories of module sheaves on ringed spaces;
- sampled owner declarations:
  `unboundedDerivedBaseChangeMap`,
  `unboundedDerivedBaseChangeMapAdjoint`,
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`,
  `Adjunction.homEquiv`;
- best owner abstraction:
  `source-facing`: the base-change morphism
    `Lg^* Rf_* (K ⟹ L) ⟶ R(f')_* (Lh^* K ⟹ Lh^* L)`;
  `core/canonical`: the chapter owner `unboundedDerivedBaseChangeMap` from Remark `20.28.3`,
    together with the ringed-site owner
    `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`;
  `bridge/view`: the composition of those two canonical maps for the object `K ⟹ L`.

Primitive data are the pullback-commutativity isomorphism, the two adjunctions, the chosen
pullback-tensor comparison for `h`, and the objects `K`, `L`. The deleted local adjoint-side
formula was only the transpose defining `unboundedDerivedBaseChangeMap`, so the public API should
reuse that owner directly instead of repeating it here.

Source/core/bridge triage:
- `source-facing`: `derivedInternalHomBaseChangeMap`;
- `core/canonical`: `unboundedDerivedBaseChangeMap`, `unboundedDerivedBaseChangeMapAdjoint`,
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`, and
  `Adjunction.homEquiv`;
- `bridge/view`: compose the canonical base-change map for `K ⟹ L` with the pullback/internal-Hom
  comparison on the target side.
-/

/-- Remark 20.42.14: given a commutative square of ringed spaces together with the induced
pullback-commutativity isomorphism on derived pullbacks, the adjunctions `Lf^* ⊣ Rf_*` and
`L(f')^* ⊣ R(f')_*`, and the pullback-tensor comparison for `h`, there is a canonical
base-change morphism
`Lg^* Rf_* (K ⟹ L) ⟶ R(f')_* (Lh^* K ⟹ Lh^* L)`. -/
@[stacks 08I4]
noncomputable def derivedInternalHomBaseChangeMap
    (pullbackCommIso :
      L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(h)^*)
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (pullbackTensorIso_h :
      ∀ (A B : DModX),
        (L(h)^*).obj (A ⊗ B) ≅ ((L(h)^*).obj A ⊗ (L(h)^*).obj B))
    (K L : DModX) :
    (L(g)^*).obj ((R(f)_*).obj (K ⟹ L)) ⟶
      (R(f')_*).obj ((L(h)^*).obj K ⟹ (L(h)^*).obj L) :=
  unboundedDerivedBaseChangeMap h f' f g adj_f adj_f' pullbackCommIso (K ⟹ L) ≫
    (R(f')_*).map (pullbackDerivedInternalHomComparison (L(h)^*) pullbackTensorIso_h K L)

-- Proof sketch: unfold `derivedInternalHomBaseChangeMap`. By definition it is the transpose,
-- under `L(f')^* ⊣ R(f')_*`, of the composite obtained by transporting `L(f')^* Lg^*` to
-- `Lh^* Lf^*`, applying the counit `Lf^* Rf_* (K ⟹ L) ⟶ K ⟹ L`, and then using the
-- pullback/internal-Hom comparison from Remark `20.42.13`.
/-- Applying the adjunction `L(f')^* ⊣ R(f')_*` to the internal-Hom base-change map recovers the
composite prescribed in the remark. -/
theorem derivedInternalHomBaseChangeMap_spec
    (pullbackCommIso :
      L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(h)^*)
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (pullbackTensorIso_h :
      ∀ (A B : DModX),
        (L(h)^*).obj (A ⊗ B) ≅ ((L(h)^*).obj A ⊗ (L(h)^*).obj B))
    (K L : DModX) :
    (adj_f'.homEquiv
        ((L(g)^*).obj ((R(f)_*).obj (K ⟹ L)))
        ((L(h)^*).obj K ⟹ (L(h)^*).obj L)).symm
        (derivedInternalHomBaseChangeMap h f' g f pullbackCommIso adj_f adj_f'
          pullbackTensorIso_h K L) =
      pullbackCommIso.hom.app ((R(f)_*).obj (K ⟹ L)) ≫
        (L(h)^*).map (adj_f.counit.app (K ⟹ L)) ≫
        pullbackDerivedInternalHomComparison (L(h)^*) pullbackTensorIso_h K L := by
  rw [derivedInternalHomBaseChangeMap, adj_f'.homEquiv_naturality_right_symm]
  simpa [unboundedDerivedBaseChangeMap,
    unboundedDerivedBaseChangeMapAdjoint]
    using unboundedDerivedBaseChangeMap_spec h f' f g adj_f adj_f' pullbackCommIso (K ⟹ L)

end

end AlgebraicGeometry.RingedSpace
