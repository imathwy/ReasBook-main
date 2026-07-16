import StacksProject_2024.stacks_project.Chap18.Definition_18_21_2
import StacksProject_2024.stacks_project.Chap21.Definition_21_13_4
import StacksProject_2024.stacks_project.Chap21.Lemma_21_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Sheaf
open Opposite
open RingedSite
open scoped CategoryTheory.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasExt (Sheaf J AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J RingCat.{u})

/- Domain-style sampling for Lemma 21.13.1:
- primary domain: cohomology over a sheaf or presheaf of sets on a ringed site, compared with the
  localized module-side `Ext` computation;
- sampled owner declarations:
  `cohomologyOverSheaf`,
  `underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology`,
  `cohomologyOverSheaf_isomorphic_localizedSite_cohomology`,
  `SheafOfModules.instAbelian`;
- best owner abstraction: the source-facing left-hand side is the Chapter 21 owner
  `cohomologyOverSheaf`, while the localized module-side cohomology is most cleanly expressed by
  the canonical `Ext` owner on the localized module category rather than by raw
  `Abelian.extFunctorObj` plumbing;
- primitive data: the structure sheaf `𝒪`, a sheaf or presheaf of sets `K`, an `𝒪`-module `ℱ`,
  and a cohomological degree `p`;
- derived API: the source-facing comparison isomorphisms below.

Source/core/bridge triage:
- `source-facing`: the two textbook comparisons for cohomology over a sheaf and over a presheaf of
  sets;
- `core/canonical`: `cohomologyOverSheaf`, `Ext`, and the localized comparison theorems from
  Lemmas `21.12.4` and `21.13.3`;
- `bridge/view`: the theorem statements below, which keep the Stacks surface while reusing the
  chapter owner abstractions and local canonical instance support. -/

section SheafComparison

variable (K : Sheaf J (Type u))

local notation "𝒪K" => RingedSite.structureSheaf (localizationAtSheaf 𝒪 K)

local instance localizedModuleCategoryAbelian :
    Abelian (SheafOfModules 𝒪K) :=
  SheafOfModules.instAbelian _

-- Proof sketch: apply Lemma `21.12.4 (1)` on the localized ringed site
-- `(𝒞/K, 𝒪|_K)` to the restricted module `j_K^* ℱ`. The resulting comparison identifies module
-- cohomology on the localized ringed site with the cohomology of the underlying abelian sheaf
-- pulled back to `𝒞/K`; Lemma `21.13.3 (2)` then identifies that localized-site cohomology with
-- the canonical `Ext` owner for `H^p(K, ℱ_ab)`.
/-- For a sheaf of sets `K`, the module cohomology of an `𝒪`-module over the localization at `K`
agrees with the cohomology of its underlying abelian sheaf over `K`. -/
theorem underlyingAbelianSheaf_cohomologyOverSheaf_eq_moduleCohomology
    [HasExt (SheafOfModules 𝒪K)]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    IsIsomorphic
      (H^p(K, (SheafOfModules.toSheaf 𝒪).obj ℱ))
      (AddCommGrpCat.of
        (Ext (SheafOfModules.unit 𝒪K)
          ((SheafOfModules.pushforward (𝟙 𝒪K)).obj ℱ) p)) := by
  sorry

end SheafComparison

section PresheafComparison

variable [HasSheafify J (Type u)]
variable (K : Cᵒᵖ ⥤ Type u)

private abbrev sheafifiedPresheaf : Sheaf J (Type u) :=
  (presheafToSheaf J (Type u)).obj K

local notation "𝒪aK" =>
  RingedSite.structureSheaf (localizationAtSheaf 𝒪 (sheafifiedPresheaf K))

local instance sheafifiedLocalizedModuleCategoryAbelian :
    Abelian (SheafOfModules 𝒪aK) :=
  SheafOfModules.instAbelian _

-- Proof sketch: replace the presheaf of sets `K` by its sheafification `aK`. By definition,
-- `H^p(K, ℱ)` is computed on the localized ringed site over `aK`, and the preceding
-- localized-site comparison identifies this with the cohomology of the underlying abelian sheaf
-- over `aK`, expressed through the canonical `Ext` owner on abelian sheaves.
/-- Lemma 21.13.1: for a ringed site `(𝒞, 𝒪)`, a presheaf of sets `K`, and an `𝒪`-module `ℱ`,
the cohomology `H^p(K, ℱ)` computed after sheafifying `K` agrees with the cohomology of the
underlying abelian sheaf of `ℱ` over `K`. -/
@[stacks 079Y]
theorem underlyingAbelianSheaf_cohomologyOverPresheaf_eq_moduleCohomology
    [HasExt (SheafOfModules 𝒪aK)]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    IsIsomorphic
      (cohomologyOverPresheaf K ((SheafOfModules.toSheaf 𝒪).obj ℱ) p)
      (AddCommGrpCat.of
        (Ext (SheafOfModules.unit 𝒪aK)
          ((SheafOfModules.pushforward (𝟙 𝒪aK)).obj ℱ) p)) := by
  exact underlyingAbelianSheaf_cohomologyOverSheaf_eq_moduleCohomology 𝒪
    (sheafifiedPresheaf K) ℱ p

end PresheafComparison

end Sheaf
end CategoryTheory
