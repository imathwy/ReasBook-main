import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_9
import StacksProject_2024.stacks_project.Chap20.Definition_20_47_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_47_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open DerivedCategory.TStructure
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "ModX" => RingedSpace.Modules X
local notation "CpxOX" => CochainComplex ModX ℤ
local notation "Cpx[" U "]" => CochainComplex (openSubspaceModuleCategory X U) ℤ
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U

/- Domain-style sampling for Lemma 20.47.7:
- primary domain: pseudo-coherence for complexes and derived `𝒪_X`-modules on ringed
  spaces, with bounded-above hypotheses imposed only after restricting to open neighborhoods;
- sampled owner declarations:
  `CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise`,
  `CochainComplex.minus`,
  `SheafOfModules.IsMPseudoCoherent`,
  `AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.of_representation`,
  `moduleRestrictionToOpenDerived`,
  `DerivedCategory.IsLE`;
- best owner abstraction: the source-facing complex owner
  `CochainComplex.IsLocallyBoundedAbove` belongs on the chosen representing complex `K`, while the
  derived-side local bounded-above condition should be owned directly by neighborhoodwise bounds
  on restricted derived objects via `moduleRestrictionToOpenDerived` and `IsLE`; the
  representative-based criterion is then a bridge theorem. The local bounded-above input on `K` is
  built from the canonical bounded-above owner `CochainComplex.minus` applied to restrictions of
  `K`, and the termwise hypothesis should use the upstream owner
  `SheafOfModules.IsMPseudoCoherent`; this file is the source-facing bridge from those
  complex-side hypotheses to the Chapter 20 complex predicate;
- primitive data: a representing cochain complex `K`, the canonical derived object
  `DerivedCategory.Q.obj K`, the source-facing local bounded-above owner on `K` built from
  `CochainComplex.minus` on open restrictions, the neighborhoodwise `IsLE` bounds on restricted
  derived objects, and the degreewise pseudo-coherence hypotheses on the terms `K.X i`;
- derived API: the source-facing theorem that `K` is `m`-pseudo-coherent, obtained via
  `ModuleDerived.IsMPseudoCoherent.of_representation`.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsLocallyBoundedAbove` and the main theorem below about a
  representing cochain complex;
- `core/canonical`: `CochainComplex.minus`, `IsMPseudoCoherent`, and
  `CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise`,
  `SheafOfModules.IsMPseudoCoherent`, `moduleRestrictionToOpenDerived`, and `DerivedCategory.IsLE`;
- `bridge/view`: the representative criterion for `ModuleDerived.IsLocallyBoundedAbove`, and the
  resulting derived `m`-pseudo-coherence transported back to the representing complex. -/

/-- A cochain complex of `𝒪_X`-modules is locally bounded above if near every point its
restriction to some open neighborhood is bounded above. -/
def CochainComplex.IsLocallyBoundedAbove (K : CpxOX) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    _root_.CochainComplex.minus
      (openSubspaceModuleCategory X U) (restrictedComplexOnOpen X U K)

namespace CochainComplex

/-- Unfolding `IsLocallyBoundedAbove` gives the neighborhoodwise bounded-above criterion on
restricted complexes. -/
theorem isLocallyBoundedAbove_iff (K : CpxOX) :
    CochainComplex.IsLocallyBoundedAbove K ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        _root_.CochainComplex.minus
          (openSubspaceModuleCategory X U) (restrictedComplexOnOpen X U K) :=
  Iff.rfl

/-- A globally bounded-above complex is locally bounded above. -/
theorem isLocallyBoundedAbove_of_boundedAbove
    (K : CpxOX) (hK : _root_.CochainComplex.minus ModX K) :
    CochainComplex.IsLocallyBoundedAbove K := by
  intro x
  refine ⟨⊤, by simp, ?_⟩
  sorry

end CochainComplex

namespace ModuleDerived

/-- A derived `𝒪_X`-module is locally bounded above if near every point its restriction to some
open neighborhood belongs to `D^{≤ n}` for some integer `n`. -/
def IsLocallyBoundedAbove (E : DModX) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ n : ℤ, ((DRes[U]).obj E).IsLE n

/-- A locally bounded-above derived `𝒪_X`-module is exactly one with a representing complex that
is locally bounded above on `X`. -/
theorem isLocallyBoundedAbove_iff_exists_locallyBoundedAbove_representative
    (E : DModX) :
    E.IsLocallyBoundedAbove ↔
      ∃ K : CpxOX, ∃ _ : E ≅ DerivedCategory.Q.obj K,
        CochainComplex.IsLocallyBoundedAbove K := by
  sorry

/-- A locally bounded-above derived `𝒪_X`-module is exactly one whose restriction to a
neighborhood of each point lies in some `D^{≤ n}`. -/
theorem isLocallyBoundedAbove_iff (E : DModX) :
    E.IsLocallyBoundedAbove ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ n : ℤ,
        ((DRes[U]).obj E).IsLE n :=
  Iff.rfl

end ModuleDerived

-- Proof sketch: if `K` is globally bounded above, then every restriction of
-- `Q.obj K` to an open subspace is represented by a bounded-above restricted
-- complex with the same upper bound, so the derived object satisfies the source-facing local
-- bounded-above proposition on every neighborhood.
namespace CochainComplex

/-- A bounded-above representing complex gives a locally bounded-above derived
`𝒪_X`-module. -/
theorem q_obj_isLocallyBoundedAbove_of_boundedAbove
    (K : CpxOX) (hK : _root_.CochainComplex.minus ModX K) :
    ModuleDerived.IsLocallyBoundedAbove (DerivedCategory.Q.obj K) := by
  rw [ModuleDerived.isLocallyBoundedAbove_iff_exists_locallyBoundedAbove_representative]
  exact ⟨K, Iso.refl _, isLocallyBoundedAbove_of_boundedAbove K hK⟩

/-- A locally bounded-above representing complex gives a locally bounded-above derived
`𝒪_X`-module. -/
theorem q_obj_isLocallyBoundedAbove_of_isLocallyBoundedAbove
    (K : CpxOX) (hK : CochainComplex.IsLocallyBoundedAbove K) :
    ModuleDerived.IsLocallyBoundedAbove (DerivedCategory.Q.obj K) := by
  rw [ModuleDerived.isLocallyBoundedAbove_iff_exists_locallyBoundedAbove_representative]
  exact ⟨K, Iso.refl _, hK⟩

end CochainComplex

-- Proof sketch: for each point, choose an open neighborhood on which `K` is bounded above. Apply
-- the truncation argument of Lemma `15.65.9` to the restricted complex on that neighborhood,
-- using Lemma `20.47.4` for the induction step on stupid truncation triangles. This gives local
-- derived `m`-pseudo-coherence of the restriction, and Lemma `20.47.2` converts the resulting
-- derived statement back to the restricted cochain complex, which is exactly the local data
-- required in Definition `20.47.1`.
namespace CochainComplex

/-- Lemma 20.47.7: a locally bounded-above cochain complex of `𝒪_X`-modules whose term
in degree `i` is `(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
@[stacks 09V7]
theorem isMPseudoCoherent_of_isLocallyBoundedAbove_of_termwise
    (K : CpxOX) (m : ℤ)
    (hbounded : CochainComplex.IsLocallyBoundedAbove K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherent (m - i)) :
    CochainComplex.IsMPseudoCoherent K m := by
  have hQbounded : ModuleDerived.IsLocallyBoundedAbove (DerivedCategory.Q.obj K) :=
    q_obj_isLocallyBoundedAbove_of_isLocallyBoundedAbove K hbounded
  have hQ : ModuleDerived.IsMPseudoCoherent (DerivedCategory.Q.obj K) m := by
    let _ := hQbounded
    sorry
  exact
    ModuleDerived.IsMPseudoCoherent.of_representation hQ (Iso.refl _)

end CochainComplex

end AlgebraicGeometry.RingedSpace
