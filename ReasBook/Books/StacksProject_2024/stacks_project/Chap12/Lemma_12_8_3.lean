import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap04.Definition_4_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : MorphismProperty C) [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
  (X : C)

/- Domain-style sampling for Lemma 12.8.3:
- primary domain: preadditive localizations by a morphism property and zero-object detection in the
  localized category;
- inspected owner declarations:
  `Localization.preadditive` together with the canonical instance `Preadditive S.Localization`,
  `Localization.functor_additive` together with the canonical instance `S.Q.Additive`,
  `MorphismProperty.map_eq_iff_postcomp`,
  `MorphismProperty.map_eq_iff_precomp`,
  `IsZero.iff_id_eq_zero`;
- best owner abstraction: the canonical localization functor `S.Q`, with zero-object detection
  expressed by the owner predicate `IsZero (S.Q.obj X)`;
- primitive data: the morphism property `S`, the object `X`, and the left/right
  calculus-of-fractions instances;
- derived API: the existence of zero morphisms out of or into `X` lying in `S`, recovered from the
  canonical localization equality criteria. -/

/- Source/core/bridge triage for Lemma 12.8.3:
- source-facing: the source criterion compares the vanishing of `S.Q.obj X` with the existence of
  zero morphisms into or out of `X` that lie in `S`
- core/canonical owners: `S.HasLeftCalculusOfFractions` and `S.HasRightCalculusOfFractions`,
  acting through the canonical localization functor `S.Q`
- bridge/view: `map_eq_iff_postcomp`, `map_eq_iff_precomp`, and `IsZero.iff_id_eq_zero` move
  between the source-level zero-morphism formulation and the canonical zero-object criterion in the
  localization -/
-- Proof sketch: in the additive localization, `IsZero (S.Q.obj X)` is equivalent to
-- `S.Q.map (𝟙 X) = S.Q.map 0`. The canonical localization comparison lemmas
-- `map_eq_iff_postcomp` and `map_eq_iff_precomp` translate this equality into the existence of a
-- morphism in `S` that equalizes `𝟙 X` and `0`, i.e. into a zero morphism out of or into `X`
-- belonging to `S`.
/-- Lemma 12.8.3: for an additive category localized at a multiplicative system `S`, the object
`S.Q.obj X` is zero exactly when some zero morphism out of `X` belongs to `S`, and exactly when
some zero morphism into `X` belongs to `S`. -/
theorem localization_object_isZero_tfae :
    List.TFAE [IsZero (S.Q.obj X), ∃ Y : C, S (0 : X ⟶ Y), ∃ Z : C, S (0 : Z ⟶ X)] := by
  tfae_have 1 ↔ 2 := by
    rw [IsZero.iff_id_eq_zero, ← S.Q.map_id, ← S.Q.map_zero, map_eq_iff_postcomp S.Q S (𝟙 X) 0]
    simp
  tfae_have 1 ↔ 3 := by
    rw [IsZero.iff_id_eq_zero, ← S.Q.map_id, ← S.Q.map_zero, map_eq_iff_precomp S.Q S (𝟙 X) 0]
    simp
  tfae_finish

end CategoryTheory
