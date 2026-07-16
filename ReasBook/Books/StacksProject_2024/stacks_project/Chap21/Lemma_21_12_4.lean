import StacksProject_2024.stacks_project.Chap21.Lemma_21_7_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable {𝒪 : Sheaf J RingCat.{u}}

local notation "AbSheaf" => SheafOfModules.toSheaf 𝒪

/-
Domain-style sampling for Lemma 21.12.4:
- primary domain: comparison between sheaf cohomology of the underlying abelian sheaf of an
  `𝒪`-module and the corresponding module cohomology on a ringed site, globally and over
  a localized object;
- sampled owner declarations:
  `RingedSite.ofRingSheaf`,
  `underlyingAbelianSheafFunctor`,
  `moduleGlobalSectionsDerived_underlyingAbelian_isomorphic`,
  `ringedSite_localizationModuleRestriction_cohomologyOver_eq`,
  `SheafOfModules.over`;
- best owner abstraction: the ambient ringed-site owner
  `underlyingAbelianSheafFunctor (RingedSite.ofRingSheaf J 𝒪)`, together with the localized
  comparison owner `ringedSite_localizationModuleRestriction_cohomologyOver_eq` and the canonical
  restriction owner `SheafOfModules.over`;
- primitive data: the ring-valued sheaf `𝒪`, an `𝒪`-module `ℱ`, an object `U : C`, and
  a cohomological degree;
- derived API: the source-facing global and localized comparison theorems below.

Source/core/bridge triage:
- `source-facing`: the textbook cohomology-vs-Ext identifications in Lemma `21.12.4`;
- `core/canonical`: `underlyingAbelianSheafFunctor`, its derived comparison owners in
  `Lemma_21_20_7`, and the localized cohomology owner
  `ringedSite_localizationModuleRestriction_cohomologyOver_eq`;
- `bridge/view`: the two theorem statements below, which keep the Stacks surface while exposing the
  comparison as canonical isomorphism rather than literal equality of objects in
  `AddCommGrpCat`.
-/

-- Proof sketch: let `X := RingedSite.ofRingSheaf J 𝒪` and view `ℱ` as a degree-zero object of
-- `D(𝒪_X)`. The owner comparison
-- `moduleGlobalSectionsDerived_underlyingAbelian_isomorphic` identifies the derived global
-- sections of `ℱ` with the derived global sections of its underlying abelian sheaf. Taking
-- degree-`i` cohomology then yields the source-facing comparison between `H^i(C, ℱ_ab)` and
-- `Ext^i_{Mod(𝒪)}(𝒪, ℱ)`.
section

variable [HasExt (Sheaf J AddCommGrpCat)]

/-- Lemma 21.12.4 (1): the global cohomology of the underlying abelian sheaf of an
`𝒪`-module is canonically isomorphic to the module cohomology computed in `Mod(𝒪)`. This is the
source-facing cohomology-group specialization of the owner-level derived comparison
`moduleGlobalSectionsDerived_underlyingAbelian_isomorphic`. -/
@[stacks 03FD]
theorem underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology
    [HasExt (SheafOfModules 𝒪)]
    (ℱ : SheafOfModules 𝒪) (i : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((AbSheaf).obj ℱ).H i))
      (AddCommGrpCat.of (Ext (SheafOfModules.unit 𝒪) ℱ i)) := sorry

-- Proof sketch: first use `ringedSite_localizationModuleRestriction_cohomologyOver_eq` to rewrite
-- `H^i(U, ℱ_ab)` as global cohomology of the underlying abelian sheaf of the localized module
-- `ℱ.over U` on `((C/U, J.over U), 𝒪_U)`. Then apply part `(1)` on that
-- localized ringed site to compare the resulting global cohomology group with
-- `Ext^i_{Mod(𝒪_U)}(𝒪_U, ℱ|_U)`.
section

variable (U : C)

local notation "𝒪_U" => 𝒪.over U

/-- Lemma 21.12.4 (2): for any object `U` of the site, the cohomology of the underlying abelian
sheaf over `U` is canonically isomorphic to the module cohomology of the localized module on the
localized ringed site `((C/U, J.over U), 𝒪_U)`. This is the localized source-facing
bridge obtained by combining `ringedSite_localizationModuleRestriction_cohomologyOver_eq` with the
global comparison from part `(1)` on the slice site. -/
@[stacks 03FD]
theorem underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology
    [HasWeakSheafify (J.over U) AddCommGrpCat]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat]
    [HasSheafify (J.over U) AddCommGrpCat]
    [HasExt (Sheaf (J.over U) AddCommGrpCat)]
    [HasExt (SheafOfModules 𝒪_U)]
    (ℱ : SheafOfModules 𝒪) (i : ℕ) :
    IsIsomorphic
      (((AbSheaf).obj ℱ).H' i U)
      (AddCommGrpCat.of (Ext (SheafOfModules.unit 𝒪_U) (ℱ.over U) i)) := sorry

end

end
