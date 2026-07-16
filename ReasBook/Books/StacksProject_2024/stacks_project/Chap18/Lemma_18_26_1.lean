import Mathlib
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite
open SheafOfModules.RingedSite (ringedSiteModuleCategory)
open scoped PresheafOfModules.Monoidal

noncomputable section

universe u v

namespace PresheafOfModules

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 18.26.1:
- primary domain: sheafification of presheaves of modules over a presheaf of commutative rings,
  together with the canonical tensor/sheafification comparison;
- sampled owner declarations:
  `commRingSheafification`,
  `moduleSheafification`,
  `Functor.Monoidal.μIso`;
- best owner abstraction:
  the `source-facing` owner is `moduleSheafification J 𝒪` for a presheaf of commutative rings
  `𝒪`; the tensor/sheafification comparison is therefore the canonical monoidal comparison
  attached to that owner functor;
- primitive data:
  a presheaf of commutative rings `𝒪` and presheaves of `𝒪`-modules `𝒜`, `ℬ`;
- derived API:
  the comparison isomorphism
  `(moduleSheafification J 𝒪).obj (𝒜 ⊗ ℬ) ≅
    (moduleSheafification J 𝒪).obj 𝒜 ⊗ (moduleSheafification J 𝒪).obj ℬ`
  and its underlying comparison morphism
  `(moduleSheafification J 𝒪).obj (𝒜 ⊗ ℬ) ⟶
    (moduleSheafification J 𝒪).obj 𝒜 ⊗ (moduleSheafification J 𝒪).obj ℬ`.

Source/core/bridge triage:
- `source-facing`: the sheafified tensor comparison
  `𝒜^# ⊗_{𝒪^#} ℬ^# ≅ (𝒜 ⊗_{p,𝒪} ℬ)^#`;
- `core/canonical`: the monoidal comparison isomorphism
  `Functor.Monoidal.μIso (moduleSheafification J 𝒪)`;
- `bridge/view`: the explicit `.obj` specialization below. Unlike the later specialization to a
  sheaf of rings, the ambient topology `J` is not inferable from a presheaf of modules alone, so
  this file keeps `moduleSheafification J 𝒪` explicit and reuses the canonical comparison directly
  instead of introducing a parallel wrapper.
-/

variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (ringPresheaf 𝒪))]
variable [MonoidalCategory (ringedSiteModuleCategory J (commRingSheafification J 𝒪))]
variable [Functor.Monoidal (moduleSheafification J 𝒪)]
variable (𝒜 ℬ : PresheafOfModules (ringPresheaf 𝒪))

/- Owner recall: `moduleSheafification J 𝒪` is the canonical module-sheafification functor from
`Definition_18_28_1`. -/
recall moduleSheafification

/- Core/canonical recall: the tensor comparison is the monoidal comparison isomorphism of
`moduleSheafification J 𝒪`. -/
recall Functor.Monoidal.μIso

/- Lemma 18.26.1: for presheaves of `\mathcal O`-modules `\mathcal A`, `\mathcal B`, the
sheafification of the presheaf tensor product is canonically isomorphic to the tensor product of
the sheafifications. -/
#check
  (Functor.Monoidal.μIso (moduleSheafification J 𝒪) 𝒜 ℬ).symm

/- Companion recall: the underlying comparison morphism is the `hom` of that canonical
isomorphism. -/
#check
  ((Functor.Monoidal.μIso (moduleSheafification J 𝒪) 𝒜 ℬ).symm).hom

end

end PresheafOfModules
