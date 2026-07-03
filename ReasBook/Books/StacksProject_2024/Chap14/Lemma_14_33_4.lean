import Mathlib
import StacksProject_2024.Chap14.Example_14_33_3

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open scoped Simplicial

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace SimplicialObject

variable {C : Type u₁} [Category.{v₁} C]

/- Domain-style sampling for Lemma 14.33.4:
- primary domain: augmented simplicial objects and maps from constant simplicial objects,
  controlled by the terminal simplex `[0]`;
- sampled owner declarations:
  `SimplicialObject.Augmented`,
  `SimplicialObject.augment`,
  `SimplexCategory.isTerminalZero`;
- best owner abstraction: the split-augmentation statement belongs on the canonical owner
  `SimplicialObject.Augmented C`, while the map out of a constant simplicial object is derived from
  the terminal-simplex structure and should stay a thin bridge rather than a second packaged owner;
- primitive data vs. derived API:
  primitive data are only `f : Z ⟶ X _⦋0⦌`;
  the induced morphism `(const C).obj Z ⟶ X` and its section property against an
  augmentation are derived API.

Source/core/bridge triage:
- `source-facing`: the map from the constant simplicial object on `Z` into `X`, determined by the
  degree-`0` morphism `f`;
- `core/canonical`: the augmented simplicial-object owner `SimplicialObject.Augmented C`;
- `bridge/view`: extend `f` along the unique maps `Δ ⟶ [0]`, then specialize to sections of an
  augmentation.
-/

/-- The canonical morphism from the constant simplicial object on `Z` to `X` induced by a map
`Z ⟶ X₀`. -/
def fromZero (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌) :
    (const C).obj Z ⟶ X where
  app Δ := f ≫ X.map (SimplexCategory.isTerminalZero.from (unop Δ)).op
  naturality := by
    intro Δ₁ Δ₂ φ
    dsimp
    simp only [Category.id_comp]
    have h :
        (SimplexCategory.isTerminalZero.from (unop Δ₂)).op =
          (SimplexCategory.isTerminalZero.from (unop Δ₁)).op ≫ φ := by
      apply Quiver.Hom.unop_inj
      simp only [unop_comp, Quiver.Hom.unop_op]
      rw [SimplexCategory.eq_const_to_zero
        (SimplexCategory.isTerminalZero.from (unop Δ₂))]
      rw [SimplexCategory.eq_const_to_zero
        (φ.unop ≫ SimplexCategory.isTerminalZero.from (unop Δ₁))]
    rw [h, Functor.map_comp, Category.assoc]

-- Proof sketch: in simplicial degree `0`, the unique map `[0] ⟶ [0]` is the identity, so the
-- defining component formula for `fromZero` reduces to `f`.
/-- The degree-`0` component of `fromZero X f` is the original morphism `f`. -/
@[simp] theorem fromZero_app_zero (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌) :
    (fromZero X f).app (op ⦋0⦌) = f := by
  -- The unique endomorphism of `[0]` is the identity, so the defining formula collapses to `f`.
  simp [fromZero]

/-- Helper for Lemma 14.33.4: composing the degree-`n` component of `fromZero X.left f` with the
augmentation equals the degree-`0` section hypothesis. -/
theorem fromZero_app_comp_hom_app (X : SimplicialObject.Augmented C)
    (f : X.right ⟶ X.left _⦋0⦌)
    (hf : f ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right)
    (n : SimplexCategoryᵒᵖ) :
    (fromZero X.left f).app n ≫ X.hom.app n = 𝟙 X.right := by
  -- Naturality along the unique map `[0] ⟶ [n]` identifies the degree-`n` composite with the
  -- degree-`0` composite, and the latter is the given section equation.
  let α : op ⦋0⦌ ⟶ n := (SimplexCategory.isTerminalZero.from (unop n)).op
  have h_naturality :
      (fromZero X.left f).app n ≫ X.hom.app n = f ≫ X.hom.app (op ⦋0⦌) := by
    simpa [fromZero, α, Category.assoc] using
      congrArg (fun k => f ≫ k) (X.hom.naturality α)
  rw [h_naturality, hf]

-- Proof sketch: check the equality degreewise. In degree `n`, naturality of the augmentation
-- identifies the component with `f ≫ X.hom.app (op ⦋0⦌)`, and the hypothesis says this is the
-- identity.
/-- A section of the degree-`0` component of an augmentation yields a section of the whole
augmentation morphism. -/
theorem fromZero_comp_hom (X : SimplicialObject.Augmented C)
    (f : X.right ⟶ X.left _⦋0⦌)
    (hf : f ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right) :
    fromZero X.left f ≫ X.hom = 𝟙 _ := by
  -- Equality of natural transformations is checked degreewise, and each component is handled by
  -- the naturality computation above.
  ext n
  exact fromZero_app_comp_hom_app X f hf n

end SimplicialObject

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

-- Proof sketch: apply `SimplicialObject.fromZero_comp_hom` to the augmented simplicial
-- object from Example 14.33.3 after pre- and post-composition. The hypothesis says exactly that
-- the chosen degree-`0` map is a section of the degree-`0` augmentation component.
/-- Lemma 14.33.4: if the degree-`0` component of the pre/postcomposed augmentation admits a
section `h₀`, then the induced morphism from the constant simplicial object on `F ⋙ G` to the
pre/postcomposed simplicial object is a section of the whole augmentation. -/
theorem prePostcomposeAugmentation_fromZero_comp_eq_id
    {X : SimplicialObject (C ⥤ C)}
    (F : A ⥤ C) (G : C ⥤ B)
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (h₀ : F ⋙ G ⟶ (prePostcomposeAugmented F G ε).left _⦋0⦌)
    (hh₀ : h₀ ≫ (prePostcomposeAugmented F G ε).hom.app (op ⦋0⦌) = 𝟙 (F ⋙ G)) :
    (prePostcomposeAugmented F G ε).left.fromZero h₀ ≫ (prePostcomposeAugmented F G ε).hom =
      𝟙 _ := by
  simpa using SimplicialObject.fromZero_comp_hom (prePostcomposeAugmented F G ε) h₀ hh₀

end CategoryTheory
