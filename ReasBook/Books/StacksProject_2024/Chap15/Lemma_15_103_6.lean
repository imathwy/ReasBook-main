import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Pretriangulated
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: distinguished triangles in `D(R)`, their homology long exact sequences, and
  localization of homology modules away from a single element;
- sampled owner declarations:
  `Triangle.mk`,
  `distTriang`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`,
  `LocalizedModule.Away`,
  `Localization.Away`;
- best owner abstraction: the cone bound and conclusion should use the canonical t-structure owner
  `IsGE`, while the distinguished-triangle relation remains
  `Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod`; homology and localization use the canonical
  owners `H` and `LocalizedModule.Away`;
- primitive data: the comparison maps `g : M ⟶ C` and `δ : C ⟶ M⟦1⟧` together with the
  distinguished-triangle proof for `Triangle.mk (f • 𝟙 M) g δ`, the localized negative homology
  vanishing of `M`, and the lower bound `C.IsGE (-1)`;
- derived API: the canonical conclusion `M.IsGE 0`, with the textbook negative-homology
  vanishing statement retained only as a thin bridge via `DerivedCategory.isGE_iff`.

Source/core/bridge triage:
- `source-facing`: the vanishing criterion for the cone of multiplication by `f`;
- `core/canonical`: `Triangle`, `distTriang`, `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`, `DerivedCategory.homologyFunctor`, and `LocalizedModule.Away`;
- `bridge/view`: the explicit cohomology-vanishing formulation from `DerivedCategory.isGE_iff`,
  together with the direct categorical packaging
  `ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))` of localized
  homology modules used here and in the immediate downstream local criterion
  `Lemma_15_127_4`. -/

section

variable {M C : DerivedCategory (ModuleCat R)} {f : R} {g : M ⟶ C} {δ : C ⟶ M⟦(1 : ℤ)⟧}

-- Proof sketch: use the long exact homology sequence of the distinguished triangle
-- `M --f·id--> M --> C --> M[1]`. If some negative homology of `M` were nonzero, its localization
-- would vanish by hypothesis, so it would contain nonzero `f`-power torsion; the kernel of
-- multiplication by `f` would then contribute nontrivially to the previous homology of the cone,
-- contradicting the vanishing of `H^i(C)` for `i < -1`.
/-- Canonical `t`-structure form of Lemma 15.103.6: let `C` be the cone of multiplication by
`f : R` on `M` in `D(R)`, written as a
distinguished triangle `M \xrightarrow{f} M \to C \to M[1]`. If the localized homology
`H^i(M)_f` vanishes for all `i < 0` and the homology of `C` vanishes for all `i < -1`, then
`M` lies in degrees `≥ 0`. -/
theorem isGE_zero_of_localized_isZero_and_cone_isGE_neg_one
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod)
    (hMloc : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))))
    (hC : C.IsGE (-1)) :
    M.IsGE 0 := by
  sorry

/-- Lemma 15.103.6: let `C` be the cone of multiplication by `f : R` on `M` in `D(R)`, written as
the distinguished triangle `M \xrightarrow{f} M \to C \to M[1]`. If the localized homology
`H^i(M)_f` vanishes for all `i < 0` and the homology of `C` vanishes for all `i < -1`, then
`H^i(M)` vanishes for all `i < 0`. -/
theorem isZero_homology_of_neg_of_localized_isZero_and_cone_isZero
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod)
    (hMloc : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))))
    (hC :
      ∀ i : ℤ, i < -1 →
        IsZero ((H i).obj C)) :
    ∀ i : ℤ, i < 0 →
      IsZero ((H i).obj M) := by
  simpa [DerivedCategory.isGE_iff] using
    isGE_zero_of_localized_isZero_and_cone_isGE_neg_one hT hMloc
      ((DerivedCategory.isGE_iff C (-1)).2 hC)

end

end

end CategoryTheory
