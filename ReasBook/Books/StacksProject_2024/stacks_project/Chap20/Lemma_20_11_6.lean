import StacksProject_2024.Chap20.Lemma_20_11_2

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions X.Modules]
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Opens X.carrier)

local notation "ModX" => X.Modules
local notation "AbSheaf" => moduleUnderlyingSheaf X

/- Domain-style sampling for Lemma 20.11.6:
- primary domain: Čech cohomology versus sheaf cohomology for `𝒪_X`-modules on a fixed
  open subset and cover;
- sampled owner declarations:
  `cechIntersection`,
  `openCoverOver`,
  `moduleCechCohomologyAtOpen`,
  `IsModuleCechToModuleCohomologyMap`,
  `moduleUnderlyingSheaf`,
  `moduleCohomologyAtOpen`;
- best owner abstraction: the chapter owner
  predicate `IsModuleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p f` on the unique degree-`p`
  comparison morphism `f`, with finite intersections of the cover canonically owned by
  `cechIntersection 𝒰`;
- primitive data: the open `U`, the cover `𝒰`, the module `ℱ`, the degree `p`, and the intrinsic
  finite Čech intersections of the cover;
- derived API: the fact that the canonical comparison morphism is an isomorphism under the
  acyclicity hypothesis on those finite intersections.

Source/core/bridge triage:
- `source-facing`: the comparison theorem below;
- `core/canonical`: `IsModuleCechToModuleCohomologyMap`, `moduleCechCohomologyAtOpen`,
  `moduleUnderlyingSheaf`, and `moduleCohomologyAtOpen`;
- `bridge/view`: the internal passage from the open family `𝒰` to `openCoverOver U 𝒰 h𝒰`, and
  from an `𝒪_X`-module to its underlying additive sheaf.
-/

-- Proof sketch: apply the spectral sequence of Lemma `20.11.5` to `ℱ`. The hypothesis implies
-- that the higher cohomology presheaves vanish on every finite intersection of the cover, so the
-- `E₂`-page is concentrated on the `q = 0` row. Hence the spectral sequence degenerates at `E₂`,
-- and the edge map identifies the `p`-th Čech cohomology with the degree-`p` cohomology on `U`.
/-- An `𝒪_X`-module is Čech-acyclic on the finite intersections of the members of `𝒰` if every
positive-degree cohomology group of its underlying additive sheaf vanishes on each such
intersection. -/
def moduleAcyclicOnCechIntersections (ℱ : ModX) : Prop :=
  ∀ (q : ℕ) (_ : 0 < q) (n : ℕ) (σ : Fin (n + 1) → ι),
    IsZero (((AbSheaf).obj ℱ).H' q (cechIntersection 𝒰 σ))

/-- Lemma 20.11.6: if `ℱ` is Čech-acyclic on every finite intersection of the members of the open
covering `𝒰` of `U`, then every canonical degree-`p` comparison morphism from Čech cohomology to
cohomology on `U`, as a `Γ(U, 𝒪_X)`-module map, is an isomorphism. -/
@[stacks 01ET]
instance moduleCechCohomology_iso_moduleCohomologyAtOpen_of_acyclic_on_intersections
    (h𝒰 : iSup 𝒰 = U)
    (ℱ : ModX)
    (hacyclic : moduleAcyclicOnCechIntersections 𝒰 ℱ)
    (p : ℕ)
    (f : moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p ⟶ moduleCohomologyAtOpen U ℱ p)
    (hf : IsModuleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p f) :
    IsIso f := by
  sorry

/-- Companion corollary to Lemma 20.11.6: for each degree `p`, one may choose a comparison
morphism that is an isomorphism under the Čech-acyclicity hypothesis on finite intersections. -/
theorem exists_moduleCechToModuleCohomologyMap_isIso_of_acyclic_on_intersections
    (h𝒰 : iSup 𝒰 = U)
    (ℱ : ModX)
    (hacyclic : moduleAcyclicOnCechIntersections 𝒰 ℱ)
    (p : ℕ) :
    ∃ f : moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p ⟶ moduleCohomologyAtOpen U ℱ p,
      IsModuleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p f ∧ IsIso f := by
  obtain ⟨f, hf, _⟩ := existsUnique_moduleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p
  exact ⟨f, hf,
    moduleCechCohomology_iso_moduleCohomologyAtOpen_of_acyclic_on_intersections
      U 𝒰 h𝒰 ℱ hacyclic p f hf⟩

end AlgebraicGeometry.RingedSpace
