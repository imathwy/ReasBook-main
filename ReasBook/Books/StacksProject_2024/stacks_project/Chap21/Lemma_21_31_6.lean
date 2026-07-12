import StacksProject_2024.Chap07.Lemma_7_21_7
import StacksProject_2024.Chap21.«21_31_0_1»
import StacksProject_2024.Chap21.«21_30_0_1»
import StacksProject_2024.Chap21.Lemma_21_31_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for this item:
- primary domain: inverse-image sheaves on the localized Zariski and qc slice sites
  `LC_{Zar}/X` and `LC_{qc}/X`;
- inspected declarations:
  `π[_, _]⁻¹`,
  `a[_, _]⁻¹`,
  `comparisonTopologyPullback`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Presheaf.isSheaf_of_iso_iff`;
- best owner abstraction: the source-facing presheaf should be read on the underlying presheaf of
  the canonical Zariski inverse image `((π[τzar.over X, πX]⁻¹).obj ℱ).obj`, while the canonical
  qc owner remains `((a[hle, πX]⁻¹).obj ℱ).obj`;
- primitive data: the topologies `τzar`, `τqc`, the comparison `hle : τzar ≤ τqc`, the chosen
  small-to-big Zariski functor `πX`, and the small sheaf `ℱ`;
- derived API: the source-facing qc/Zariski comparison with the canonical qc inverse image
  `a_X⁻¹ ℱ`, together with the qc-sheaf property of the underlying presheaf of `π_X⁻¹ ℱ`.

Source/core/bridge triage:
- `source-facing`: the qc/Zariski sheaf and presheaf comparisons for this item, together with
  the qc-sheaf statement for `π_X⁻¹ ℱ`;
- `core/canonical`: `piInverseType`, `aInverseType`, and `comparisonTopologyPullback`;
- `bridge/view`: the presheaf-level qc comparison theorem below from `π_X⁻¹ ℱ` to `a_X⁻¹ ℱ`,
  and the qc-sheaf theorem for the underlying presheaf of `π_X⁻¹ ℱ`. -/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology
  (comparisonOver_le comparisonTopologyAdjunction comparisonTopologyPushforward
    comparisonTopology_unit_isIso)

noncomputable section

universe u

section

variable (τzar τqc : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  (((πFunctor X).sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint)]
-- Semantic recall: no dedicated Chapter 21 owner for the explicit presheaf
-- `(Y ⟶ X) ↦ Γ(Y, Y.hom.hom ⁻¹ ℱ)` was found, so this file keeps the generic inverse-image owner
-- `π[τzar.over X, πFunctor X]⁻¹` and records the source-faithful objectwise compatibility below
-- using `TopCat.Sheaf.pullback`.
variable {X : LCCat.{u}}
variable (ℱ : SmallTypeSheaf X)

section Comparison

variable (hle : τzar ≤ τqc)

local notation "πX⁻¹" => π[τzar.over X, πFunctor X]⁻¹
local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹

-- Proof sketch: this is the source-facing objectwise description of the canonical owner
-- `π_X⁻¹ ℱ`, namely evaluation at `Y : Over X` is the sections over `⊤ ⊆ Y` of the topological
-- pullback `Y.hom.hom ⁻¹ ℱ`.
/-- Lemma 21.31.6, source rule bridge: for `Y ⟶ X` in `LC`, the value of the canonical Zariski
inverse image `π_X⁻¹ ℱ` at `Y` is canonically isomorphic to the sections
`Γ(Y, Y.hom.hom ⁻¹ ℱ)`. -/
@[stacks 09X3]
theorem piInverseType_obj_isomorphic_pullbackSections
    (Y : Over X) :
    IsIsomorphic
      ((((πX⁻¹).obj ℱ : Sheaf (τzar.over X) (Type u)).obj).obj (Opposite.op Y))
      ((((TopCat.Sheaf.pullback (Type u) Y.hom.hom).obj ℱ).obj).obj
        (Opposite.op (⊤ : Opens Y.left.obj))) := sorry

-- Proof sketch: as in Lemma `21.31.7`, the source-facing `π_X` is modeled by a pullback-compatible
-- family of small-to-big Zariski site functors. The qc inverse image `a_X⁻¹` is definitionally
-- `π_X⁻¹ ⋙ ε[hle]_(X)⁻¹`. The source-facing presheaf comparison is therefore the canonical
-- unit of the localized comparison-topology adjunction for the identity functor on `Over X`,
-- composed with the owner-level identification that the corresponding pushforward is the same
-- underlying presheaf.
/-- Lemma 21.31.6 (1), qc/Zariski sheaf form: applying the localized comparison direct image
`ε_{X,*}` to `a_X⁻¹ ℱ` yields a sheaf canonically isomorphic to the Zariski inverse image
`π_X⁻¹ ℱ`. -/
@[stacks 09X3]
theorem piInverseType_isomorphic_comparisonPushforward_aInverseType
    [HasWeakSheafify (τqc.over X) (Type u)] :
    IsIsomorphic
      ((πX⁻¹).obj ℱ : Sheaf (τzar.over X) (Type u))
      ((comparisonTopologyPushforward (Type u) hle X).obj
        ((aX⁻¹).obj ℱ : Sheaf (τqc.over X) (Type u))) := sorry

-- Proof sketch: forget the sheaf-level comparison above to underlying presheaves, then use the
-- canonical identification of `ε_{X,*}` with the identity on presheaves.
/-- Lemma 21.31.6 (2), qc presheaf form: the underlying presheaf of `π_X⁻¹ ℱ`, viewed on
`LC_{qc}/X`, is canonically isomorphic to the underlying presheaf of `a_X⁻¹ ℱ`. -/
@[stacks 09X3]
theorem piInverseTypePresheaf_isomorphic_aInverseType
    [HasWeakSheafify (τqc.over X) (Type u)]
    : IsIsomorphic
        ((((πX⁻¹).obj ℱ : Sheaf (τzar.over X) (Type u)).obj) :
          (Over X)ᵒᵖ ⥤ Type u)
        ((((aX⁻¹).obj ℱ : Sheaf (τqc.over X) (Type u)).obj) :
          (Over X)ᵒᵖ ⥤ Type u) := sorry

-- Proof sketch: transport the qc sheaf property of the canonical owner `a_X⁻¹ ℱ`
-- across the presheaf-level comparison above. Together with the source-rule bridge above, this
-- identifies the sheaf with `Y ↦ Γ(Y, Y.hom.hom ⁻¹ ℱ)`.
/-- Lemma 21.31.6 (3), qc sheaf form: equivalently, the rule
`(Y ⟶ X) ↦ Γ(Y, Y.hom.hom ⁻¹ ℱ)`, identified objectwise with `π_X⁻¹ ℱ` by the source-rule
bridge above, is already a sheaf on `LC_{qc}/X`. -/
@[stacks 09X3]
theorem piInverseTypePresheaf_isSheaf
    (hle' : τzar ≤ τqc)
    [HasWeakSheafify (τqc.over X) (Type u)] :
    Presheaf.IsSheaf
      (τqc.over X)
      ((((πX⁻¹).obj ℱ : Sheaf (τzar.over X) (Type u)).obj) :
        (Over X)ᵒᵖ ⥤ Type u) := sorry

end Comparison

end
