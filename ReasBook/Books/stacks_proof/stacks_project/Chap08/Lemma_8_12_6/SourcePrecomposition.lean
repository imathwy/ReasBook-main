import StacksProject_2024.Chap04.Lemma_4_27_14
import StacksProject_2024.Chap04.Lemma_4_33_8
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap08.Lemma_8_12_5
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Bicategory
open scoped Bicategory

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

open scoped Functor

variable (u : C ⥤ D) (p : S ⥤ C)

/-- Helper for Lemma 8.12.6: the prelocalized projection from `u ₚₚ p` to `D`. -/
abbrev pushforwardSourceProjection :
    u ₚₚ p ⥤ D :=
  CategoricalPullback.π₁ (Comma.snd (𝟭 D) u) p ⋙ Comma.fst (𝟭 D) u

/-- Helper for Lemma 8.12.6: the prelocalized projection inverts the fraction property from
Lemma `8.12.5`. -/
theorem pushforwardSourceProjection_invertsFractions :
    (u.pushforwardFractions p).IsInvertedBy (pushforwardSourceProjection u p) := by
  intro X Y f hf
  rcases hf with ⟨⟨hV, hleft⟩, _⟩
  change IsIso f.fst.left
  rw [hleft]
  infer_instance

/-- Helper for Lemma 8.12.6: the source object of the precomposition lift in `u ₚₚ p`. -/
abbrev pushforwardSourcePrecomposeObj (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) : u ₚₚ p :=
  { fst :=
      { left := V
        right := Y.fst.right
        hom := f ≫ Y.fst.hom }
    snd := Y.snd
    iso := Y.iso }

/-- Helper for Lemma 8.12.6: the comma-square compatibility for the chosen precomposition lift. -/
theorem pushforwardSourcePrecomposeHom_fst_w (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) :
    (𝟭 D).map f ≫ Y.fst.hom =
      (f ≫ Y.fst.hom) ≫ u.map (𝟙 Y.fst.right) := by
  simp

/-- Helper for Lemma 8.12.6: the pullback compatibility for the chosen precomposition lift. -/
theorem pushforwardSourcePrecomposeHom_w (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) :
    𝟙 Y.fst.right ≫ Y.iso.hom =
      (pushforwardSourcePrecomposeObj (u := u) (p := p) Y f).iso.hom ≫ p.map (𝟙 Y.snd) := by
  simp [pushforwardSourcePrecomposeObj]

/-- Helper for Lemma 8.12.6: the prelocalized morphism obtained by precomposing the comma arrow
with `f`. -/
abbrev pushforwardSourcePrecomposeHom (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) :
    pushforwardSourcePrecomposeObj (u := u) (p := p) Y f ⟶ Y :=
  { fst :=
      { left := f
        right := 𝟙 Y.fst.right
        w := pushforwardSourcePrecomposeHom_fst_w (u := u) (p := p) Y f }
    snd := 𝟙 Y.snd
    w := pushforwardSourcePrecomposeHom_w (u := u) (p := p) Y f }

/-- Helper for Lemma 8.12.6: the comma-square compatibility for the universal factor through the
precomposition lift. -/
theorem pushforwardSourcePrecomposeFactor_fst_w
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left)
    (g : Z.fst.left ⟶ V) (θ : Z ⟶ Y) (hθ : θ.fst.left = g ≫ f) :
    (𝟭 D).map g ≫ (f ≫ Y.fst.hom) = Z.fst.hom ≫ u.map θ.fst.right := by
  simpa [hθ, Category.assoc] using θ.fst.w

/-- Helper for Lemma 8.12.6: the pullback compatibility for the universal factor through the
precomposition lift. -/
theorem pushforwardSourcePrecomposeFactor_w
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left)
    (_g : Z.fst.left ⟶ V) (θ : Z ⟶ Y) :
    θ.fst.right ≫ (pushforwardSourcePrecomposeObj (u := u) (p := p) Y f).iso.hom =
      Z.iso.hom ≫ p.map θ.snd := by
  simpa only [pushforwardSourcePrecomposeObj] using θ.w

/-- Helper for Lemma 8.12.6: the universal factor through the precomposition lift in the source
category. -/
abbrev pushforwardSourcePrecomposeFactor
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left)
    (g : Z.fst.left ⟶ V) (θ : Z ⟶ Y) (hθ : θ.fst.left = g ≫ f) :
    Z ⟶ pushforwardSourcePrecomposeObj (u := u) (p := p) Y f :=
  { fst :=
      { left := g
        right := θ.fst.right
        w := pushforwardSourcePrecomposeFactor_fst_w (u := u) (p := p) f g θ hθ }
    snd := θ.snd
    w := pushforwardSourcePrecomposeFactor_w (u := u) (p := p) f g θ }

/-- Helper for Lemma 8.12.6: the source-level universal factor composes back to the given
morphism. -/
theorem pushforwardSourcePrecomposeFactor_comp
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left)
    (g : Z.fst.left ⟶ V) (θ : Z ⟶ Y) (hθ : θ.fst.left = g ≫ f) :
    pushforwardSourcePrecomposeFactor (u := u) (p := p) f g θ hθ ≫
        pushforwardSourcePrecomposeHom (u := u) (p := p) Y f =
      θ := by
  -- Compare the two composites componentwise in the categorical pullback.
  apply CategoricalPullback.hom_ext
  · apply CategoryTheory.Comma.hom_ext
    · simp [pushforwardSourcePrecomposeFactor, pushforwardSourcePrecomposeHom, hθ]
    · simp [pushforwardSourcePrecomposeFactor, pushforwardSourcePrecomposeHom]
  · simp [pushforwardSourcePrecomposeFactor, pushforwardSourcePrecomposeHom]

/-- Helper for Lemma 8.12.6: precomposing the comma arrow with a base map produces a strongly
cartesian morphism for the prelocalized projection to `D`. -/
theorem pushforwardSource_precompose_isStronglyCartesian
    (Y : u ₚₚ p) {V : D} (f : V ⟶ Y.fst.left) :
    (pushforwardSourceProjection u p).IsStronglyCartesian f
      (pushforwardSourcePrecomposeHom (u := u) (p := p) Y f) := by
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · -- The chosen precomposition lift lies over `f` by construction.
    refine IsHomLift.of_fac' (pushforwardSourceProjection u p) f
      (pushforwardSourcePrecomposeHom (u := u) (p := p) Y f) rfl rfl ?_
    simp [pushforwardSourceProjection, pushforwardSourcePrecomposeHom]
  · intro Z g θ hθlift
    -- The base map of `θ` is its left comma component.
    have hθ : θ.fst.left = g ≫ f := by
      simpa [pushforwardSourceProjection] using
        (IsHomLift.fac' (pushforwardSourceProjection u p) (g ≫ f) θ)
    let χ := pushforwardSourcePrecomposeFactor (u := u) (p := p) f g θ hθ
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- The source factor lies over `g` because its left component is exactly `g`.
      refine IsHomLift.of_fac' (pushforwardSourceProjection u p) g χ rfl rfl ?_
      simp [pushforwardSourceProjection, χ]
    · -- The factorization follows from componentwise composition in the pullback.
      exact pushforwardSourcePrecomposeFactor_comp (u := u) (p := p) f g θ hθ
    · intro τ hτ
      -- Uniqueness is detected componentwise because the target lift fixes the right data.
      let _ : (pushforwardSourceProjection u p).IsHomLift g τ := hτ.1
      have hτleft : τ.fst.left = g := by
        simpa [pushforwardSourceProjection] using
          (IsHomLift.fac' (pushforwardSourceProjection u p) g τ)
      have hright : τ.fst.right = θ.fst.right := by
        have hcomp := congrArg Limits.CategoricalPullback.Hom.fst hτ.2
        simpa [pushforwardSourcePrecomposeHom] using
          congrArg CategoryTheory.CommaMorphism.right hcomp
      have hτfst : τ.fst = χ.fst := by
        apply CategoryTheory.Comma.hom_ext
        · exact hτleft
        · simpa [χ] using hright
      have hτsnd : τ.snd = θ.snd := by
        have hcomp := congrArg Limits.CategoricalPullback.Hom.snd hτ.2
        simpa [pushforwardSourcePrecomposeHom] using hcomp
      apply CategoricalPullback.hom_ext
      · exact hτfst
      · simpa [χ] using hτsnd

/-- Helper for Lemma 8.12.6: under the construction localization lift, the image of `Q.map k`
under the localized projection is the source projection map of `k`. -/
theorem pushforwardProjection_fac_naturality
    {A B : u ₚₚ p} (k : A ⟶ B) :
    (u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k) =
      (pushforwardSourceProjection u p).map k := by
  -- The construction-lift factorization computes directly after precomposition with `Q`.
  simp only [pushforwardProjection, Functor.comp_map]
  dsimp [MorphismProperty.Q, Quot.liftOn, Quotient.functor, pushforwardSourceProjection]
  simp

/-- Helper for Lemma 8.12.6: after descending the source precomposition lift through `Q`, the
comparison isomorphism identifies its base map with the chosen source-side map. -/
theorem pushforwardProjection_precompose_fac
    (Y : u ₚₚ p) {V : D} (f : V ⟶ Y.fst.left) :
    (u.pushforwardProjection p).map
        ((u.pushforwardFractions p).Q.map
          (pushforwardSourcePrecomposeHom (u := u) (p := p) Y f)) =
      f := by
  -- This is the source proof's basic compatibility equation in construction-lift normal form.
  simpa [pushforwardSourceProjection, pushforwardSourcePrecomposeHom, Category.assoc] using
    pushforwardProjection_fac_naturality (u := u) (p := p)
      (pushforwardSourcePrecomposeHom (u := u) (p := p) Y f)

end Functor

end

end CategoryTheory
