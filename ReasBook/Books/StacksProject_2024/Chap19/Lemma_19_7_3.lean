import Mathlib
import StacksProject_2024.Chap18.Definition_18_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped CategoryTheory.FreeAbelianSheaf

universe u v

noncomputable section

/- Domain-style sampling for Lemma 19.7.3:
- primary domain: injective objects in the category of abelian sheaves on a site, tested on the
  source-facing family of free abelian sheaves on representables;
- sampled owner declarations:
  `Injective`,
  `Injective.factors`,
  `freeAbelianSheaf`,
  `(ℤ_ (yoneda.obj X))^#[K]`;
- best owner abstraction: the canonical class `Injective`; the free abelian sheaves on
  representables are the source-facing test objects, not a second owner abstraction;
- primitive data: an object `X`, a monomorphism `i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#`, and a morphism
  `φ : 𝒮 ⟶ 𝒥`;
- derived API: the extension morphism `ψ` across `i`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project test family `(ℤ_ (yoneda.obj X))^#`;
- `core/canonical`: `Injective` and its extension owner `Injective.factors`;
- `bridge/view`: this theorem, which proves injectivity from the source-facing extension test. -/

-- Proof sketch: argue by Baer's criterion as in More on Algebra, Lemma 15.54.1. For a strict
-- monomorphism of abelian sheaves and a map into `𝒥`, choose an object `X` and a section of the
-- larger sheaf not coming from the smaller one; the associated map from `Z_X^#`, formalized as
-- the free abelian sheaf on `yoneda.obj X`, and the assumed extension property produce a strictly
-- larger intermediate subsheaf to which the map extends, contradicting maximality.
/-- Lemma 19.7.3: if every morphism from an abelian subsheaf of `Z_X^#`, formalized as a
monomorphism into `(ℤ_ (yoneda.obj X))^#[K]`,
extends to `𝒥`, then `𝒥` is an injective abelian sheaf on `(C, K)`. -/
theorem injective_of_representable_free_abelian_extension_property
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    [HasWeakSheafify K AddCommGrpCat]
    (𝒥 : Sheaf K AddCommGrpCat)
    (h𝒥 : ∀ (X : C) (𝒮 : Sheaf K AddCommGrpCat)
      (i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#[K]) [Mono i]
      (φ : 𝒮 ⟶ 𝒥),
        ∃ ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒥,
          i ≫ ψ = φ) :
    Injective 𝒥 := by
  sorry
