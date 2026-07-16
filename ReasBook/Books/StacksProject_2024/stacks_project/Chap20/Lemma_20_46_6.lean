import StacksProject_2024.stacks_project.Chap20.Definition_20_46_1
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_44_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules
local notation "CpxX" => CochainComplex ModX ℤ
local notation "ResCpx" U => moduleRestrictionComplexToOpen X U

/- Domain-style sampling for Lemma 20.46.6:
- primary domain: local null-homotopies for morphisms from strictly perfect complexes of
  `𝒪_X`-modules;
- sampled owner declarations:
  `CochainComplex.IsStrictlyPerfect`,
  `openSubspaceModuleCategory`,
  `moduleRestrictionToOpen`,
  `moduleRestrictionComplexToOpen`,
  `SheafOfModules.RingedSite.IsLocallyNullHomotopic`,
  `SheafOfModules.RingedSite.exists_cover_homotopy_zero_of_isStrictlyPerfect_of_acyclic`,
  `SheafOfModules.RingedSite
    .exists_cover_homotopy_zero_of_isStrictlyPerfect_of_isStrictlyGE_of_homology_isZero`;
- best owner abstraction: restriction of `𝒪_X`-modules to an open subspace, together
  with its induced functor on cochain complexes, written on theorem surfaces below via
  `moduleRestrictionComplexToOpen X U`;
- primitive data: the complexes `E`, `F`, the morphism `α`, and the strict-perfect / homology
  vanishing hypotheses;
- derived API: the source-facing point-neighborhood reformulation on a ringed space, expressed on
  theorem surfaces via the canonical restricted-complex owner
  `moduleRestrictionComplexToOpen X U`, with Chapter `21.44.6` providing the ringed-site
  local-null-homotopy proof engine.

Source/core/bridge triage:
- `source-facing`: the ringed-space statement that every point admits an open neighborhood on
  which the restricted morphism is homotopic to zero;
- `core/canonical`: `openSubspaceModuleCategory X U`, `moduleRestrictionToOpen X U`, and
  `moduleRestrictionComplexToOpen X U`;
- `bridge/view`: the passage from the Chapter `21.44.6` opens-site local-null-homotopy statement
  at `⊤` to a point-containing open subset of `X`.

This file should therefore keep the source-facing neighborhood formulation, while expressing the
restricted complexes through the Chapter 20 owner `moduleRestrictionComplexToOpen X U`.
Chapter `21.44.6` remains the proof route on the localized ringed site, and the bridge API here is
the corresponding open-cover formulation specialized to the opens site of `X`. -/

-- Proof sketch: specialize the Chapter `21.44.6` owner theorem to the opens site of `X` at the
-- top object `⊤`. The companion bridge records the resulting open cover; the source-facing lemma
-- then extracts a member whose underlying open subset contains the chosen point `x`.
/-- Companion bridge: if `α : E ⟶ F` is a morphism of cochain complexes of `𝒪_X`-modules, with
`E` strictly perfect and `F` acyclic, then after restricting to the members of some open cover of
`X`, the restricted morphism is homotopic to zero. -/
theorem exists_open_cover_homotopy_zero_of_isStrictlyPerfect_of_acyclic
    (E F : CpxX) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E) (hF : F.Acyclic) :
    ∃ (ι : Type u) (cover : ι → Opens X.carrier), IsOpenCover cover ∧
      ∀ i : ι,
        let j := ResCpx (cover i)
        Nonempty (Homotopy (j.map α) 0) := sorry

/-- Lemma 20.46.6 (1): if `α : E ⟶ F` is a morphism of cochain complexes of `𝒪_X`-modules, with
`E` strictly perfect and `F` acyclic, then `α` is locally on `X` homotopic to zero. -/
@[stacks 08C7]
theorem exists_open_neighborhood_homotopy_zero_of_isStrictlyPerfect_of_acyclic
    (E F : CpxX) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E) (hF : F.Acyclic) (x : X) :
    ∃ U : Opens X.carrier,
      x ∈ U ∧
        let j := ResCpx U
        Nonempty (Homotopy (j.map α) 0) := sorry

-- Proof sketch: this is the bounded-below source-facing specialization of the second owner theorem
-- in Chapter `21.44.6`, again passing first through the opens-site open-cover statement and then
-- extracting a point-containing member of the cover.
/-- Companion bridge: if `α : E ⟶ F` is a morphism of cochain complexes of `𝒪_X`-modules, with
`E` strictly perfect, `E` vanishing in degrees `i < a`, and `H^i(F) = 0` for `i ≥ a`, then after
restricting to the members of some open cover of `X`, the restricted morphism is homotopic to
zero. -/
theorem exists_open_cover_homotopy_zero_of_isStrictlyPerfect_of_isStrictlyGE_of_homology_isZero
    [CategoryWithHomology ModX]
    (E F : CpxX) (α : E ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∃ (ι : Type u) (cover : ι → Opens X.carrier), IsOpenCover cover ∧
      ∀ i : ι,
        let j := ResCpx (cover i)
        Nonempty (Homotopy (j.map α) 0) := sorry

/-- Lemma 20.46.6 (2): if `α : E ⟶ F` is a morphism of cochain complexes of `𝒪_X`-modules, with
`E` strictly perfect, `E` vanishing in degrees `i < a`, and `H^i(F) = 0` for `i ≥ a`, then `α` is
locally on `X` homotopic to zero. -/
@[stacks 08C7]
theorem exists_open_neighborhood_homotopy_zero_of_isStrictlyPerfect_of_isStrictlyGE_of_homology_isZero
    [CategoryWithHomology ModX]
    (E F : CpxX) (α : E ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) (x : X) :
    ∃ U : Opens X.carrier,
      x ∈ U ∧
        let j := ResCpx U
        Nonempty (Homotopy (j.map α) 0) := sorry

end AlgebraicGeometry.RingedSpace
