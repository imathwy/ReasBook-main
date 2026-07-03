import Mathlib
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_3_1 (from Chap07) -/
universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace Presheaf

/- Source/core/bridge triage for Definition 7.3.1:
- source-facing layer: the objectwise injective/surjective clauses on sections over every object
  of `C`;
- core/canonical owners: the chapter presheaf owner `_root_.CategoryTheory.Presheaf C` together
  with the categorical predicates `Mono φ` and `Epi φ`;
- bridge/view API: `NatTrans.mono_iff_mono_app`, `NatTrans.epi_iff_epi_app`,
  `CategoryTheory.mono_iff_injective`, and `CategoryTheory.epi_iff_surjective`;
- primitive data: the morphism `φ : F ⟶ G`;
- derived API: the objectwise function criteria recorded by the companion bridge theorems below.
-/

section

variable {F G : Presheaf C} (φ : F ⟶ G)

/- Definition 7.3.1 (injective clause), owner recall: for a morphism of set-valued presheaves,
the canonical owner notion is `Mono φ`. The textbook sectionwise formulation is the companion
bridge theorem below. -/
recall Mono

/- Definition 7.3.1 (surjective clause), owner recall: for a morphism of set-valued presheaves,
the canonical owner notion is `Epi φ`. The textbook sectionwise formulation is the companion
bridge theorem below. -/
recall Epi

-- Proof sketch: monomorphisms in a functor category are objectwise monomorphisms, and
-- monomorphisms in `Type` are exactly injective functions.
/-- Companion bridge: a morphism of presheaves of sets is a monomorphism exactly when it is
injective on sections over every object of `C`. -/
theorem mono_iff_injective :
    Mono φ ↔ ∀ U : C, Function.Injective (φ.app (op U)) := by
  constructor
  · intro hφ U
    exact (CategoryTheory.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app φ).1 hφ (op U))
  · intro hφ
    exact (NatTrans.mono_iff_mono_app φ).2 fun U ↦
      (CategoryTheory.mono_iff_injective _).2 (hφ U.unop)

-- Proof sketch: epimorphisms in a functor category are objectwise epimorphisms, and
-- epimorphisms in `Type` are exactly surjective functions.
/-- Companion bridge: a morphism of presheaves of sets is an epimorphism exactly when it is
surjective on sections over every object of `C`. -/
theorem epi_iff_surjective :
    Epi φ ↔ ∀ U : C, Function.Surjective (φ.app (op U)) := by
  constructor
  · intro hφ U
    exact (CategoryTheory.epi_iff_surjective _).1
      ((NatTrans.epi_iff_epi_app φ).1 hφ (op U))
  · intro hφ
    exact (NatTrans.epi_iff_epi_app φ).2 fun U ↦
      (CategoryTheory.epi_iff_surjective _).2 (hφ U.unop)

end
end Presheaf

end CategoryTheory

/-! ### Lemma_7_3_2 (from Chap07) -/
open Opposite

universe w v u

namespace CategoryTheory
namespace Presheaf

/-
Domain-style sampling for Lemma 7.3.2:
- primary domain: monomorphisms, epimorphisms, and isomorphisms of set-valued presheaves;
- inspected owner declarations:
  `CategoryTheory.Presheaf.mono_iff_injective`,
  `CategoryTheory.Presheaf.epi_iff_surjective`,
  `CategoryTheory.isIso_iff_mono_and_epi`;
- best owner abstraction: the categorical predicates `Mono`, `Epi`, and `IsIso` for morphisms of
  presheaves, with the sectionwise injective/surjective criteria as derived bridge API;
- primitive data: a morphism `φ : ℱ ⟶ 𝒢`;
- derived API: the objectwise injective and surjective reformulations.

Source/core/bridge triage:
- `source-facing`: the Stacks sectionwise injective, surjective, and bijective clauses for a
  morphism of presheaves of sets;
- `core/canonical`: `Mono φ`, `Epi φ`, and `IsIso φ`;
- `bridge/view`: `mono_iff_injective`, `epi_iff_surjective`, and the companion theorem below
  combining them with `isIso_iff_mono_and_epi`. -/

section

variable {C : Type u} [Category.{v} C]
variable {ℱ 𝒢 : Presheaf C} (φ : ℱ ⟶ 𝒢)

/- Lemma 7.3.2 (1): the injective maps of presheaves of sets are exactly the monomorphisms.
This is the exact canonical theorem already recorded in Definition 7.3.1. -/
recall mono_iff_injective

/- Lemma 7.3.2 (2): the surjective maps of presheaves of sets are exactly the epimorphisms.
This is the exact canonical theorem already recorded in Definition 7.3.1. -/
recall epi_iff_surjective

/-
Lemma 7.3.2 (3): the canonical owner theorem for "isomorphism iff injective and surjective" is
`CategoryTheory.isIso_iff_mono_and_epi`.
-/
recall isIso_iff_mono_and_epi

/-- Lemma 7.3.2 (3), companion bridge: a morphism of presheaves of sets is an isomorphism if and
only if it is injective and surjective in the sense of Definition 7.3.1. -/
theorem isIso_iff_injective_and_surjective :
    IsIso φ ↔
      (∀ U : C, Function.Injective (φ.app (op U))) ∧
        ∀ U : C, Function.Surjective (φ.app (op U)) := by
  -- Rewrite the categorical criterion through the established objectwise mono/epi bridges.
  rw [isIso_iff_mono_and_epi, mono_iff_injective, epi_iff_surjective]

end

end Presheaf
end CategoryTheory

/-! ### Definition_7_3_3 (from Chap07) -/
open CategoryTheory

universe u v w

section

variable {C : Type u} [Category.{v} C]

/-
Source/core/bridge triage for Definition 7.3.3:
- source-facing notion: a subpresheaf of a set-valued presheaf
- core/canonical owner: `CategoryTheory.Subfunctor`
- primitive data: for each object `U`, a subset `𝒢.obj U : Set (ℱ.obj U)` of sections stable
  under restriction
- derived API: the older name `Subpresheaf` is only a deprecated compatibility alias and should not
  be used as a second public owner
-/
/-
Definition 7.3.3: a subpresheaf of a set-valued presheaf `ℱ` is the canonical mathlib structure
`CategoryTheory.Subfunctor ℱ`, consisting of subsets `𝒢.obj U : Set (ℱ.obj U)` for every object
`U`, compatible with the restriction maps of `ℱ`. The older name `Subpresheaf ℱ` is only a
deprecated alias, so downstream code should use `Subfunctor ℱ` directly.
-/
recall Subfunctor

end

/-! ### Lemma_7_3_4 (from Chap07) -/
universe w v u

namespace CategoryTheory

open CategoryTheory.Subfunctor

namespace Presheaf

section

variable {C : Type u} [Category.{v} C]
variable {ℱ 𝒢 : Presheaf C} (φ : ℱ ⟶ 𝒢)

/- Domain-style sampling for Lemma 7.3.4:
- primary domain: images of morphisms of set-valued presheaves and their epi/mono factorizations;
- sampled owner declarations:
  `Presheaf`,
  `Subfunctor.range`,
  `Subfunctor.toRange`,
  `Subfunctor.toRange_ι`,
  `Subfunctor.range_eq_top`;
- best owner abstraction: the chapter owner `Presheaf C`, together with the range subpresheaf
  `Subfunctor.range φ`, whose inclusion is the canonical mono part of the image factorization of
  `φ`;
- primitive data: the morphism `φ`;
- derived API: factorization through the range via `toRange φ`, its epi instance, and the
  uniqueness criterion below identifying any epi factorization through a subpresheaf with
  `range φ`.

Source/core/bridge triage:
- `source-facing`: the unique subpresheaf of the target through which `φ` factors by an
  epimorphism;
- `core/canonical`: the chapter presheaf owner `Presheaf C` and the canonical range subpresheaf
  `Subfunctor.range φ`;
- `bridge/view`: the proof below identifies any epi factorization through a subpresheaf with the
  canonical range subpresheaf, but this bridge is internal to the source-facing uniqueness
  statement rather than a second public owner.
-/
/-- Lemma 7.3.4: a morphism of presheaves of sets factors through a unique subpresheaf of the
target such that the induced map to that subpresheaf is an epimorphism. -/
theorem existsUnique_subfunctor_factorization_epi :
    ∃! G' : Subfunctor 𝒢,
      ∃ α : ℱ ⟶ G'.toFunctor, Epi α ∧ α ≫ G'.ι = φ := by
  -- The source proof chooses the image subpresheaf, which is `range φ` in the canonical API.
  refine ⟨range φ, ?_, ?_⟩
  -- The canonical map into the range provides the required epi factorization.
  · exact ⟨toRange φ, inferInstance, toRange_ι φ⟩
  -- Any other epi factorization through a subpresheaf has the same range, hence the same subpresheaf.
  · intro G' hG'
    rcases hG' with ⟨α, hα_epi, hα⟩
    letI : Epi α := hα_epi
    calc
      G' = range (α ≫ G'.ι) := by
        symm
        rw [range_comp, range_eq_top, image_top, range_ι]
      _ = range φ := by simp [hα]

end
end Presheaf
end CategoryTheory

/-! ### Definition_7_3_5 (from Chap07) -/
/-
Domain-style sampling for Definition 7.3.5:
- primary domain: images of morphisms of set-valued presheaves
- sampled owner declarations:
  `CategoryTheory.Subfunctor.range`,
  `CategoryTheory.Subfunctor.toRange`,
  `CategoryTheory.Subfunctor.toRange_ι`,
  `CategoryTheory.Subfunctor.range_eq_top`
- best owner abstraction: the image subpresheaf is owned canonically by
  `CategoryTheory.Subfunctor.range`
- primitive data: the morphism `φ : ℱ ⟶ 𝒢`
- derived API: the factorization `Subfunctor.toRange φ`, the inclusion `(Subfunctor.range φ).ι`,
  and their companion lemmas already come from the owner abstraction and should not be repackaged
  locally

Source/core/bridge triage:
- `source-facing`: the image subpresheaf of a morphism of presheaves of sets
- `core/canonical`: `CategoryTheory.Subfunctor.range`
- `bridge/view`: none; the factorization through the image is already derived API of the canonical
  owner

This numbered item is only a recall of the canonical owner, so the refined file should keep the
direct recall and no parallel local alias or wrapper.
-/
/- Definition 7.3.5: notation as in Lemma 7.3.4, the image of a morphism `φ` of presheaves of
sets is the canonical subpresheaf `Subfunctor.range φ`. -/
recall CategoryTheory.Subfunctor.range
