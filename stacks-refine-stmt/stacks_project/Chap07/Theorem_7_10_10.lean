import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap07.PlusNotation
import stacks_project.Chap07.Definition_7_10_9
import stacks_project.Chap07.Definition_7_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open GrothendieckTopology Plus
open scoped CategoryTheory.GrothendieckTopology.PlusNotation

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (ℱ : Cᵒᵖ ⥤ Type (max u v))

private theorem eq_of_restrict_eq_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    ∀ ⦃X : C⦄ (S : J.Cover X) (x y : ℱ.obj (op X)),
      (∀ I : S.Arrow, ℱ.map I.f.op x = ℱ.map I.f.op y) → x = y := by
  intro X S x y hxy
  exact (hℱ S S.condition).ext fun Y f hf ↦ hxy ⟨Y, f, hf⟩

-- Proof sketch: use the explicit separatedness criterion proved by `Plus.sep`, which exactly
-- says that two sections of `ℱ⁺`
-- agreeing after restriction to a covering must already be equal.
/-- Theorem 7.10.10 (1): the plus construction `ℱ⁺` of a presheaf of sets is separated. -/
theorem plusObj_isSeparated :
    Presieve.IsSeparated J ℱ⁺ := by
  intro U S hS x t₁ t₂ ht₁ ht₂
  exact Plus.sep ℱ ⟨S, hS⟩ t₁ t₂ fun I ↦ (ht₁ I.f I.hf).trans (ht₂ I.f I.hf).symm

-- Proof sketch: unpack `Presieve.IsSeparated J ℱ` into the coverwise injectivity hypothesis used
-- by `Plus.isSheaf_of_sep`, and then apply that theorem directly.
/-- Theorem 7.10.10 (2), first assertion: if `ℱ` is separated, then `ℱ⁺` is a sheaf. -/
theorem plusObj_isSheaf_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    Presheaf.IsSheaf J ℱ⁺ := by
  exact Plus.isSheaf_of_sep ℱ (eq_of_restrict_eq_of_isSeparated J ℱ hℱ)

-- Proof sketch: `Plus.inj_of_sep` gives the objectwise injectivity statement for `J.toPlus ℱ`
-- once we feed it the coverwise separatedness condition coming directly from `hℱ`.
/-- Theorem 7.10.10 (2), second assertion: if `ℱ` is separated, then the canonical map
`ℱ ⟶ ℱ⁺` is injective in the sense of Definition 7.3.1. -/
theorem toPlus_injective_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    ∀ U : C, Function.Injective ((J.toPlus ℱ).app (op U)) := by
  exact Plus.inj_of_sep ℱ (eq_of_restrict_eq_of_isSeparated J ℱ hℱ)

-- Proof sketch: Definition 7.3.1 already identifies the objectwise injectivity statement with the
-- canonical owner `Mono`.
/-- Companion to Theorem 7.10.10 (2): if `ℱ` is separated, then the canonical map `ℱ ⟶ ℱ⁺` is
a monomorphism of presheaves. -/
theorem toPlus_mono_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    Mono (J.toPlus ℱ) := by
  exact (Presheaf.mono_iff_injective (J.toPlus ℱ)).2
    (toPlus_injective_of_isSeparated J ℱ hℱ)

/- Theorem 7.10.10 (3): if `ℱ` is already a sheaf, then the canonical map `ℱ ⟶ ℱ⁺` is an
isomorphism. This is exactly the canonical owner theorem
`GrothendieckTopology.isIso_toPlus_of_isSheaf`. -/
recall GrothendieckTopology.isIso_toPlus_of_isSheaf

/- Theorem 7.10.10 (4): the iterated plus construction `ℱ⁺⁺` is always a sheaf. This is exactly
the canonical owner theorem `GrothendieckTopology.Plus.isSheaf_plus_plus`. -/
recall GrothendieckTopology.Plus.isSheaf_plus_plus

end
