import StacksProject_2024.stacks_project.Chap20.Definition_20_46_1
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_44_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules
local notation "CpxX" => CochainComplex ModX ℤ
local notation "ResCpx" U => moduleRestrictionComplexToOpen X U

/- Domain-style sampling for Lemma 20.46.7:
- primary domain: restriction of complexes of `𝒪_X`-modules to an open subspace and
  local lifting up to homotopy;
- sampled owner declarations:
  `moduleRestrictionComplexToOpen`,
  `SheafOfModules.RingedSite
    .exists_cover_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi`;
- best owner abstraction: the canonical restriction functor
  `moduleRestrictionComplexToOpen X U` on cochain complexes over the open subspace `U`;
- primitive data: the complexes `E`, `F`, `G`, the maps `α`, `f`, and the strict-perfect,
  bounded-below, and homology hypotheses;
- derived API: the open-cover companion below and the source-facing restricted lift `β` together
  with the restricted homotopy witnessing that `α` factors through `f` up to homotopy on a
  neighborhood.

Source/core/bridge triage:
- `source-facing`: the ringed-space neighborhood statement itself;
- `core/canonical`: `moduleRestrictionComplexToOpen X U`;
- `bridge/view`: the open-cover companion below, obtained from the Chapter 21 ringed-site
  cover-lifting theorem specialized to the opens site at `⊤`, and then converted to a
  point-containing open neighborhood of `X`.

This file should therefore keep the source-facing neighborhood formulation while reusing the
ambient restriction functor directly through the established Chapter 20 owner
`moduleRestrictionComplexToOpen X U`. -/

-- Proof sketch: specialize the Chapter `21.44.7` ringed-site theorem to the opens site of `X`
-- at the top object `⊤`. The resulting covering family gives, on each member of the cover, a
-- lift of the restricted morphism through the restricted map up to homotopy; the source-facing
-- lemma then chooses one member containing the chosen point `x`.
/-- Companion bridge: if `α : E ⟶ F` and `f : G ⟶ F` are morphisms of cochain complexes of
`𝒪_X`-modules, with `E` strictly perfect, `E^j = 0` for `j < a`, and `H^j(f)` an isomorphism for
`j > a` and surjective for `j = a`, then after restricting to the members of some open cover of
`X`, the map `α` lifts through `f` up to homotopy. -/
theorem exists_open_cover_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
    [CategoryWithHomology ModX]
    (E F G : CpxX) (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) :
    ∃ (ι : Type u) (cover : ι → Opens X.carrier), IsOpenCover cover ∧
      ∀ i : ι,
        let j := ResCpx (cover i)
        ∃ β : j.obj E ⟶ j.obj G,
          Nonempty (Homotopy (j.map α) (β ≫ j.map f)) := sorry

/-- Lemma 20.46.7: if `α : E ⟶ F` and `f : G ⟶ F` are morphisms of cochain complexes of
`𝒪_X`-modules, with `E` strictly perfect, `E^j = 0` for `j < a`, and `H^j(f)` an isomorphism for
`j > a` and surjective for `j = a`, then locally on `X` the map `α` lifts through `f` up to
homotopy. -/
@[stacks 08C8]
theorem exists_open_neighborhood_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
    [CategoryWithHomology ModX]
    (E F G : CpxX) (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a))
    (x : X) :
    ∃ U : Opens X.carrier,
      x ∈ U ∧
        let j := ResCpx U
        ∃ β : j.obj E ⟶ j.obj G,
          Nonempty (Homotopy (j.map α) (β ≫ j.map f)) := by
  obtain ⟨ι, cover, hcover, hlift⟩ :=
    exists_open_cover_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
      E F G α f a hE hE_ge hf_iso hf_epi
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  exact ⟨cover i, hxi, hlift i⟩

end AlgebraicGeometry.RingedSpace
