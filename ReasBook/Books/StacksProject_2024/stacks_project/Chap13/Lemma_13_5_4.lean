import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_27_20
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open ObjectProperty
open MorphismProperty
open Pretriangulated

section

variable {D : Type u₁} {D' : Type u₂} [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D' n)]
  [Pretriangulated D] [Pretriangulated D']

section ExactFunctor

variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Domain-style sampling:
- primary domain: the triangulated kernel of an exact functor and its associated cone-defined
  morphism property;
- sampled owner declarations:
  `Functor.kernel`,
  `ObjectProperty.trW`,
  `IsSaturatedMultiplicativeSystem`;
- best owner abstraction: for an exact functor `F`, the intrinsic morphism property is
  `F.kernel.trW`; the source-facing class of morphisms inverted by `F` should be treated as a
  bridge/view of this owner via an equality theorem, with compatibility and saturation derived
  from the owner-level picture;
- primitive data: the functor `F` together with the exact-functor owners
  `[F.CommShift ℤ]` and `[F.IsTriangulated]`;
- derived API: the bridge `F.kernel.trW = ((isomorphisms D').inverseImage F)` and the resulting
  saturated multiplicative-system structure on the source-facing inverse-image class.

Source/core/bridge triage:
- `source-facing`: Lemma 13.5.4, asserting that the morphisms inverted by an exact functor form a
  saturated multiplicative system;
- `core/canonical`: the kernel object property `F.kernel` and the cone-defined owner `F.kernel.trW`;
- `bridge/view`: the identification of `F.kernel.trW` with the inverse-image class of
  isomorphisms.
-/

-- Proof sketch: complete `f` to a distinguished triangle in `D`; the cone of `f` belongs to
-- `F.kernel` exactly when the mapped triangle in `D'` has zero third object, which is equivalent
-- to `F.map f` being an isomorphism.
/-- For an exact functor, the source-facing class of inverted morphisms is exactly the canonical
cone-defined morphism property of its kernel subcategory. -/
theorem kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor
    : F.kernel.trW = (isomorphisms D').inverseImage F := by
  ext X Y f
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  simpa [Functor.kernel, prop_inverseImage_iff, MorphismProperty.inverseImage_iff,
      isomorphisms.iff] using
    ((F.kernel).trW_iff_of_distinguished (Triangle.mk f g h) hT).trans
      (Triangle.isZero₃_iff_isIso₁ (F.mapTriangle.obj (Triangle.mk f g h))
        (F.map_distinguished _ hT))

private theorem inverseImage_isomorphisms_of_exactFunctor_ext_left
    {X' X Y : D} (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X)
    (hs : ((isomorphisms D').inverseImage F) s) (hsf : s ≫ f₁ = s ≫ f₂) :
    ∃ (Y' : D) (t : Y ⟶ Y'), ((isomorphisms D').inverseImage F) t ∧ f₁ ≫ t = f₂ ≫ t := by
  rw [← kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] at hs
  rcases hs with ⟨Z, g, h, H, hZ⟩
  have hsf' : s ≫ (f₁ - f₂) = 0 := by
    simpa using (sub_eq_zero.2 hsf : s ≫ f₁ - s ≫ f₂ = 0)
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ H _ hsf'
  obtain ⟨Y', r, t, hT⟩ := distinguished_cocone_triangle q
  refine ⟨Y', r, ?_, ?_⟩
  · have hr : F.kernel.trW r :=
      ⟨_, _, _, rot_of_distTriang _ hT, F.kernel.le_shift _ _ hZ⟩
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hr
  · apply sub_eq_zero.1
    have hzero : (f₁ - f₂) ≫ r = 0 := by
      rw [hq]
      have hqr : q ≫ r = 0 := comp_distTriang_mor_zero₁₂ _ hT
      calc
        ((Triangle.mk s g h).mor₂ ≫ q) ≫ r = (Triangle.mk s g h).mor₂ ≫ (q ≫ r) := by
          simp [Category.assoc]
        _ = 0 := by
          rw [hqr]
          change (Triangle.mk s g h).mor₂ ≫ (0 : (Triangle.mk s g h).obj₃ ⟶ Y') = 0
          exact Limits.comp_zero
    simpa using hzero

private theorem inverseImage_isomorphisms_of_exactFunctor_ext_right
    {X Y Y' : D} (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y')
    (hs : ((isomorphisms D').inverseImage F) s) (hfs : f₁ ≫ s = f₂ ≫ s) :
    ∃ (X' : D) (t : X' ⟶ X), ((isomorphisms D').inverseImage F) t ∧ t ≫ f₁ = t ≫ f₂ := by
  rw [← kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] at hs
  change F.kernel.trW s at hs
  rw [F.kernel.trW_iff'] at hs
  rcases hs with ⟨Z, g, h, H, hZ⟩
  have hfs' : (f₁ - f₂) ≫ s = 0 := by
    simpa using (sub_eq_zero.2 hfs : f₁ ≫ s - f₂ ≫ s = 0)
  obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hfs'
  obtain ⟨X', t, r, hT⟩ := distinguished_cocone_triangle₁ q
  refine ⟨X', t, ?_, ?_⟩
  · have ht : F.kernel.trW t := ⟨_, _, _, hT, hZ⟩
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using ht
  · apply sub_eq_zero.1
    have hzero : t ≫ (f₁ - f₂) = 0 := by
      rw [hq]
      have htq : t ≫ q = 0 := comp_distTriang_mor_zero₁₂ _ hT
      calc
        t ≫ (q ≫ (Triangle.mk g s h).mor₁) = (t ≫ q) ≫ (Triangle.mk g s h).mor₁ := by
          simp [Category.assoc]
        _ = 0 := by
          rw [htq]
          change (0 : X' ⟶ (Triangle.mk g s h).obj₁) ≫ (Triangle.mk g s h).mor₁ = 0
          exact Limits.zero_comp
    simpa using hzero

private theorem kernel_trW_of_exactFunctor_hasLeftCalculusOfFractions
    : HasLeftCalculusOfFractions F.kernel.trW := by
  refine
    { toIsMultiplicative := ?_
      exists_leftFraction := ?_
      ext := ?_ }
  · simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using
      (inferInstance : ((isomorphisms D').inverseImage F).IsMultiplicative)
  · intro X Y φ
    obtain ⟨Z, f, g, H, hZ⟩ := φ.hs
    obtain ⟨Y', s', f', hT⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ := complete_distinguished_triangle_morphism₂ _ _ H hT φ.f (𝟙 Z)
      (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, hT, hZ⟩, hb₁.symm⟩
  · intro X' X Y f₁ f₂ s hs hsf
    have hs' : ((isomorphisms D').inverseImage F) s := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hs
    obtain ⟨Y', t, ht, hfac⟩ :=
      inverseImage_isomorphisms_of_exactFunctor_ext_left F f₁ f₂ s hs' hsf
    have ht' : F.kernel.trW t := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using ht
    exact ⟨Y', t, ht', hfac⟩

private theorem kernel_trW_of_exactFunctor_hasRightCalculusOfFractions
    : HasRightCalculusOfFractions F.kernel.trW := by
  refine
    { toIsMultiplicative := ?_
      exists_rightFraction := ?_
      ext := ?_ }
  · simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using
      (inferInstance : ((isomorphisms D').inverseImage F).IsMultiplicative)
  · intro X Y φ
    obtain ⟨Z, f, g, H, hZ⟩ := φ.hs
    obtain ⟨X', f', h', hT⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _ hT H φ.f (𝟙 Z)
      (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, hT, hZ⟩ a, ha₁⟩
  · intro X Y Y' f₁ f₂ s hs hfs
    have hs' : ((isomorphisms D').inverseImage F) s := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hs
    obtain ⟨X', t, ht, hfac⟩ :=
      inverseImage_isomorphisms_of_exactFunctor_ext_right F f₁ f₂ s hs' hfs
    have ht' : F.kernel.trW t := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using ht
    exact ⟨X', t, ht', hfac⟩

-- Proof sketch: the owner `F.kernel.trW` has the left and right calculus of fractions by the
-- standard `trW` completion arguments, with multiplicativity transported from the equivalent
-- inverse-image isomorphism class. The saturation axiom is then reduced to the corresponding
-- saturation of `isomorphisms D'` via the bridge theorem.
/-- The cone-defined morphism property attached to the kernel of an exact functor is a saturated
multiplicative system. -/
theorem kernel_trW_of_exactFunctor_isSaturatedMultiplicativeSystem
    : IsSaturatedMultiplicativeSystem F.kernel.trW := by
  letI : HasLeftCalculusOfFractions F.kernel.trW :=
    kernel_trW_of_exactFunctor_hasLeftCalculusOfFractions F
  letI : HasRightCalculusOfFractions F.kernel.trW :=
    kernel_trW_of_exactFunctor_hasRightCalculusOfFractions F
  refine
    { toHasLeftCalculusOfFractions := inferInstance
      toHasRightCalculusOfFractions := inferInstance
      saturation := ?_ }
  intro X₀ X₁ X₂ X₃ f g h hfg hgh
  have hfg' : ((isomorphisms D').inverseImage F) (f ≫ g) := by
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hfg
  have hgh' : ((isomorphisms D').inverseImage F) (g ≫ h) := by
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hgh
  have hg' : ((isomorphisms D').inverseImage F) g := by
    change ((isomorphisms D').inverseImage F) (f ≫ g) at hfg'
    change ((isomorphisms D').inverseImage F) (g ≫ h) at hgh'
    change ((isomorphisms D').inverseImage F) g
    rw [MorphismProperty.inverseImage_iff, isomorphisms.iff] at hfg' hgh' ⊢
    have hfg'' : isomorphisms D' (F.map f ≫ F.map g) := by
      simpa [Functor.map_comp] using hfg'
    have hgh'' : isomorphisms D' (F.map g ≫ F.map h) := by
      simpa [Functor.map_comp] using hgh'
    exact (show IsIso (F.map g) from by
      simpa [isomorphisms.iff] using
        IsSaturatedMultiplicativeSystem.saturation (F.map f) (F.map g) (F.map h) hfg'' hgh'')
  simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hg'

-- Proof sketch: transport the owner-level saturated multiplicative-system structure on
-- `F.kernel.trW` across the bridge to the source-facing inverse-image class.
/-- Lemma 13.5.4: if `F : D ⥤ D'` is an exact functor between pretriangulated categories, then
the morphisms `f` of `D` such that `F.map f` is an isomorphism form a saturated multiplicative
system. -/
theorem inverseImage_isomorphisms_of_exactFunctor_isSaturatedMultiplicativeSystem
    : IsSaturatedMultiplicativeSystem ((isomorphisms D').inverseImage F) := by
  simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using
    kernel_trW_of_exactFunctor_isSaturatedMultiplicativeSystem F

end ExactFunctor

end

end CategoryTheory
