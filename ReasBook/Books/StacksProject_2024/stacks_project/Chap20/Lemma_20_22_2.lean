import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Constructible
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks
import StacksProject_2024.stacks_project.Chap06.ClosedSubsetInclusion
import StacksProject_2024.stacks_project.Chap20.«20_2_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat
open TopCat.Sheaf
open scoped TopCat.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X Y : TopCat.{u}} [SpectralSpace X] [SpectralSpace Y]

/-
Domain-style sampling for Lemma 20.22.2:
- primary domain: stalks of higher direct images for sheaves on spectral spaces, and restriction to
  subspaces defined by specializing loci;
- sampled owner declarations:
  `TopCat.Sheaf.higherDirectImage`,
  `TopCat.subsetInclusion`,
  `TopCat.Sheaf.pullback`,
  `TopCat.Presheaf.stalk`,
  `nhdsKer`;
- best owner abstraction: the source-facing subset
  `f ⁻¹' nhdsKer ({y} : Set Y)` should be handled through the canonical subspace inclusion
  `X.subsetInclusion`, and the higher direct image should be written through the Chapter 20 owner
  `R^{p}_[f](ℱ)` rather than a second local wrapper;
- primitive data: the spectral map `f`, the point `y`, and the induced subset of `X`;
- derived API: the stalk of `R^{p}_[f](ℱ)` at `y` and the top-open cohomology of the canonical
  pullback of `ℱ` to the subspace `TopCat.of (f ⁻¹' nhdsKer ({y} : Set Y))`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.22.2, identifying the stalk of `R^p f_* ℱ` at `y` with cohomology on
  the inverse image of the specializing subset of `y`;
- `core/canonical`: `TopCat.Sheaf.higherDirectImage`, `TopCat.subsetInclusion`,
  `TopCat.Sheaf.pullback`, and `TopCat.Presheaf.stalk`;
- `bridge/view`: the specialization from the generic subspace restriction owner to the subset
  `f ⁻¹' nhdsKer ({y} : Set Y)`.
-/

variable (f : X ⟶ Y)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (X.Sheaf AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]

-- Proof sketch: identify the stalk of `R^p f_* ℱ` with the filtered colimit over the
-- quasi-compact open neighbourhoods of `y` of the groups `H^p(f⁻¹(V), ℱ)`. The set of points
-- specializing to `y` is the canonical subset `nhdsKer ({y} : Set Y)`, and Lemma `20.19.3`
-- computes the cohomology of its inverse image as this filtered colimit.
/-- Lemma 20.22.2: for a spectral map of spectral spaces, the stalk at `y` of the `p`-th higher
direct image of an abelian sheaf `ℱ` is canonically isomorphic to the degree-`p` cohomology of
the restriction of `ℱ` to the inverse image of the canonical specializing subset
`nhdsKer ({y} : Set Y)`. -/
@[stacks 0A3E]
theorem higher_direct_image_stalk_isomorphic_preimage_specialization_cohomology
    (hf : IsSpectralMap f) (y : Y) (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify
      (Opens.grothendieckTopology (TopCat.of (f ⁻¹' nhdsKer (Set.singleton y))))
      AddCommGrpCat.{u}]
    [HasExt ((TopCat.of (f ⁻¹' nhdsKer (Set.singleton y))).Sheaf AddCommGrpCat.{u})] :
    IsIsomorphic
      (TopCat.Presheaf.stalk (R^{p}_[f](ℱ)).obj y)
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u}
            (X.subsetInclusion (f ⁻¹' nhdsKer (Set.singleton y)))).obj ℱ).H' p
        (⊤ : Opens (TopCat.of (f ⁻¹' nhdsKer (Set.singleton y))))) := by
  sorry

end Sheaf
end CategoryTheory
