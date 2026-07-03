import Mathlib
import StacksProject_2024.Chap06.Definition_6_6_1
import StacksProject_2024.Chap12.Definition_12_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
universe u v

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Proposition 19.8.5:
-- primary domain: functorial injective embeddings in categories of presheaves of modules;
- sampled owner-level declarations:
  `PMod`,
  `HasFunctorialInjectiveEmbeddings`,
  `EnoughInjectives`,
  `CategoryTheory.exists_resolutionFunctorOne`;
- best owner abstraction: the source-facing and downstream owner here is
  `HasFunctorialInjectiveEmbeddings (PMod(𝒪))`, while the Chapter 12 bridge to
  `EnoughInjectives (PMod(𝒪))` is derived API used later in Chapter 13;
- primitive data: the canonical category `PresheafOfModules 𝒪`, written `PMod(𝒪)`;
- derived API: the owner-level instance
  `presheafOfModules_hasFunctorialInjectiveEmbeddings` and the existential corollary below.

Source/core/bridge triage:
- `source-facing`: Proposition 19.8.5, asserting existence of functorial injective embeddings in
  `PMod(𝒪)`;
- `core/canonical`: `HasFunctorialInjectiveEmbeddings`;
- `bridge/view`: the Chapter 12 passage
  `HasFunctorialInjectiveEmbeddings → EnoughInjectives`.
-/
/-- Proposition 19.8.5, owner-level form: presheaves of `\mathcal O`-modules admit functorial
injective embeddings. -/
instance presheafOfModules_hasFunctorialInjectiveEmbeddings
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    HasFunctorialInjectiveEmbeddings (PMod(𝒪)) := by
  sorry

/-- Proposition 19.8.5: for a category `C` and a presheaf of rings `𝒪` on `C`, the category
`PMod(𝒪)` of presheaves of `𝒪`-modules admits functorial injective embeddings. -/
theorem presheafOfModules_exists_functorialInjectiveEmbeddings
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    Nonempty (HasFunctorialInjectiveEmbeddings (PMod(𝒪))) :=
  ⟨presheafOfModules_hasFunctorialInjectiveEmbeddings 𝒪⟩

end

end CategoryTheory
