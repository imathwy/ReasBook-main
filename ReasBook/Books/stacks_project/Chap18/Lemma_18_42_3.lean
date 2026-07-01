import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

-- Proof sketch: by Lemma 10.39.5 it is enough to test injectivity after tensoring with a finite
-- ideal `I ⊆ Λ`. Coherence makes `I` finitely presented, so Lemma 18.42.2 identifies
-- `\underline M(U) ⊗ I` with `\underline{M ⊗ I}(U)`. Since `M` is flat, `M ⊗ I → M` is
-- injective, and evaluation of the induced morphism of constant sheaves at `U` remains injective.
/-- Lemma 18.42.3: if `Λ` is a coherent ring, `M` is a flat `Λ`-module, and `U` is an object of
the site `C`, then the `Λ`-module of sections `\underline M(U)` of the constant sheaf is flat. -/
theorem constantSheaf_app_flat
    (hcoh : ∀ (I : Ideal Λ) [Module.Finite Λ I], Module.FinitePresentation Λ I)
    (M : ModuleCat.{u} Λ) [Module.Flat Λ M] (U : C) :
    Module.Flat Λ (((constantSheaf J (ModuleCat.{u} Λ)).obj M).1.obj (op U)) := sorry

end CategoryTheory
