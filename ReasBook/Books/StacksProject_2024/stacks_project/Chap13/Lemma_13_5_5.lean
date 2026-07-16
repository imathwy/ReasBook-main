import Mathlib
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import StacksProject_2024.stacks_project.Chap04.Definition_4_27_20
import StacksProject_2024.stacks_project.Chap13.Lemma_13_5_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Abelian
open ComposableArrows
open ObjectProperty
open MorphismProperty
open Pretriangulated

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [Functor.IsHomological H] [H.ShiftSequence ℤ]

local notation "S" => H.homologicalKernel.trW

/- Domain-style sampling for Lemma 13.5.5:
- primary domain: morphism properties attached to a homological functor on a pretriangulated
  category;
- inspected owner declarations:
  `Functor.mem_homologicalKernel_trW_iff`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.HasLeftCalculusOfFractions`,
  `MorphismProperty.HasRightCalculusOfFractions`,
  `IsSaturatedMultiplicativeSystem`;
- best owner abstraction: the canonical morphism property `H.homologicalKernel.trW`, together
  with the owner classes `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.IsMultiplicative`, and `IsSaturatedMultiplicativeSystem`;
- primitive-vs-derived split:
  primitive data: the homological functor `H`;
  derived API: the homological-kernel object property `H.homologicalKernel`, the canonical
  morphism property `H.homologicalKernel.trW`, the bridge
    `Functor.mem_homologicalKernel_trW_iff`, and the compatibility/multiplicativity/saturation
    results below.

Source/core/bridge triage:
- `source-facing`: the textbook class `S` of maps inducing isomorphisms on every shifted functor
  `H^i`;
- `core/canonical`: the owner `H.homologicalKernel.trW` together with the classes
  `MorphismProperty.IsMultiplicative`, `MorphismProperty.IsCompatibleWithTriangulation`, and
  `IsSaturatedMultiplicativeSystem`;
- `bridge/view`: `Functor.mem_homologicalKernel_trW_iff`, identifying the textbook description
  with the canonical owner.
-/

/- Companion recall: for a homological functor, the textbook class `S` of morphisms inducing
isomorphisms on all shifted values `H^i` is exactly the canonical morphism property
`H.homologicalKernel.trW`. -/
#check Functor.mem_homologicalKernel_trW_iff

/-- Helper for Lemma 13.5.5: the canonical textbook class of morphisms inverted by every shift of
`H` is multiplicative. -/
private instance homologicalKernel_trW_isMultiplicative :
    MorphismProperty.IsMultiplicative S where
  id_mem X := by
    -- Unpack membership in `S` into the shifted-isomorphism formulation.
    rw [H.mem_homologicalKernel_trW_iff]
    intro n
    simpa using (inferInstance : IsIso ((H.shift n).map (𝟙 X)))
  comp_mem f g hf hg := by
    -- Composition stays in `S` because every shifted image is a composition of isomorphisms.
    rw [H.mem_homologicalKernel_trW_iff] at hf hg ⊢
    intro n
    letI : IsIso ((H.shift n).map f) := hf n
    letI : IsIso ((H.shift n).map g) := hg n
    have : IsIso (((H.shift n).map f) ≫ (H.shift n).map g) := by infer_instance
    simpa [Functor.map_comp] using
      this

omit [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: if the first object of a distinguished triangle lies in the
homological kernel of `H`, then the second morphism belongs to `S`. -/
private theorem homologicalKernel_trW_of_second_morphism
    ⦃X Y Z : D⦄ ⦃f : X ⟶ Y⦄ ⦃g : Y ⟶ Z⦄ ⦃h : Z ⟶ X⟦(1 : ℤ)⟧⦄
    (hT : Triangle.mk f g h ∈ distTriang D) (hX : H.homologicalKernel X) :
    S g := by
  -- Rotate once so that `g` becomes the first morphism, and shift the kernel object accordingly.
  exact ⟨_, _, _, rot_of_distTriang _ hT, H.homologicalKernel.le_shift _ _ hX⟩

omit [Abelian A] [H.IsHomological] [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: if the third object of a distinguished triangle lies in the
homological kernel of `H`, then the first morphism belongs to `S`. -/
private theorem homologicalKernel_trW_of_first_morphism
    ⦃X Y Z : D⦄ ⦃f : X ⟶ Y⦄ ⦃g : Y ⟶ Z⦄ ⦃h : Z ⟶ X⟦(1 : ℤ)⟧⦄
    (hT : Triangle.mk f g h ∈ distTriang D) (hZ : H.homologicalKernel Z) :
    S f := by
  -- This is exactly the cone description of membership in `H.homologicalKernel.trW`.
  exact ⟨_, _, _, hT, hZ⟩

omit [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: left cancellation for `S` follows by factoring `f₁ - f₂` through the
cone of a denominator and then using the next map in the resulting distinguished triangle. -/
private theorem homologicalKernel_trW_ext_left
    ⦃X' X Y : D⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X)
    (hs : S s) (hsf : s ≫ f₁ = s ≫ f₂) :
    ∃ (Y' : D) (t : Y ⟶ Y'), S t ∧ f₁ ≫ t = f₂ ≫ t := by
  rcases hs with ⟨Z, g, h, Hs, hZ⟩
  -- Rewrite the equality as the vanishing of the difference to match exactness.
  have hsf' : s ≫ (f₁ - f₂) = 0 := by
    simpa using (sub_eq_zero.2 hsf : s ≫ f₁ - s ≫ f₂ = 0)
  -- Factor the difference through the cone object of `s`.
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ Hs _ hsf'
  obtain ⟨Y', r, t, hT⟩ := distinguished_cocone_triangle q
  refine ⟨Y', r, ?_, ?_⟩
  · exact homologicalKernel_trW_of_second_morphism (H := H) hT hZ
  · -- The factorization dies after postcomposing with the next triangle morphism.
    apply sub_eq_zero.1
    simpa using calc
      (f₁ - f₂) ≫ r = (g ≫ q) ≫ r := by
        simpa [Category.assoc] using congrArg (fun u ↦ u ≫ r) hq
      _ = 0 := by
        have hqr : q ≫ r = 0 := by
          simpa using comp_distTriang_mor_zero₁₂ _ hT
        have hgqr : g ≫ (q ≫ r) = g ≫ (0 : Z ⟶ Y') := congrArg (fun u ↦ g ≫ u) hqr
        have hg0 : g ≫ (0 : Z ⟶ Y') = 0 := by simp
        simpa [Category.assoc] using hgqr.trans hg0

omit [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: right cancellation for `S` is the dual cone argument, obtained from
the exactness of `Triangle.coyoneda`. -/
private theorem homologicalKernel_trW_ext_right
    ⦃X Y Y' : D⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y')
    (hs : S s) (hfs : f₁ ≫ s = f₂ ≫ s) :
    ∃ (X' : D) (t : X' ⟶ X), S t ∧ t ≫ f₁ = t ≫ f₂ := by
  rw [H.homologicalKernel.trW_iff'] at hs
  rcases hs with ⟨Z, g, h, Hs, hZ⟩
  -- Rewrite the equality as the vanishing of the difference to feed exactness.
  have hfs' : (f₁ - f₂) ≫ s = 0 := by
    simpa using (sub_eq_zero.2 hfs : f₁ ≫ s - f₂ ≫ s = 0)
  -- Factor the difference through the cone of `s` on the dual side.
  obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ Hs _ hfs'
  obtain ⟨X', t, r, hT⟩ := distinguished_cocone_triangle₁ q
  refine ⟨X', t, ?_, ?_⟩
  · exact homologicalKernel_trW_of_first_morphism (H := H) hT hZ
  · apply sub_eq_zero.1
    -- The factorization dies after precomposing with the previous triangle morphism.
    simpa using calc
      t ≫ (f₁ - f₂) = (t ≫ q) ≫ g := by
        simpa [Category.assoc] using congrArg (fun u ↦ t ≫ u) hq
      _ = 0 := by
        have htq : t ≫ q = 0 := by
          simpa using comp_distTriang_mor_zero₁₂ _ hT
        have htqg : (t ≫ q) ≫ g = 0 ≫ g := congrArg (fun u ↦ u ≫ g) htq
        have h0g : (0 : X' ⟶ Z) ≫ g = 0 := by simp
        simpa [Category.assoc] using htqg.trans h0g

/-- Helper for Lemma 13.5.5: the class `S` satisfies the triangulated compatibility axiom `MS6`
because the third vertical arrow in a morphism of distinguished triangles is an isomorphism on
every shifted value of `H` whenever the first two are. -/
instance :
    MorphismProperty.IsCompatibleWithTriangulation S := by
  refine
    { toIsCompatibleWithShift := inferInstance
      compatible_with_triangulation := ?_ }
  intro T₁ T₂ hT₁ hT₂ a b ha hb hab
  -- Complete the partial square to a morphism of distinguished triangles.
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b hab
  refine ⟨c, ?_, hc₂, hc₃⟩
  rw [H.mem_homologicalKernel_trW_iff] at ha hb ⊢
  intro n
  let φ : T₁ ⟶ T₂ :=
    { hom₁ := a
      hom₂ := b
      hom₃ := c
      comm₁ := hab
      comm₂ := hc₂
      comm₃ := hc₃ }
  let R₁ : ComposableArrows A 4 :=
    (H.homologySequenceComposableArrows₅ T₁ n (n + 1) rfl).δlast
  let R₂ : ComposableArrows A 4 :=
    (H.homologySequenceComposableArrows₅ T₂ n (n + 1) rfl).δlast
  let ψ₅ :
      H.homologySequenceComposableArrows₅ T₁ n (n + 1) rfl ⟶
        H.homologySequenceComposableArrows₅ T₂ n (n + 1) rfl :=
    homMk₅ ((H.shift n).map a) ((H.shift n).map b) ((H.shift n).map c)
      ((H.shift (n + 1)).map a) ((H.shift (n + 1)).map b) ((H.shift (n + 1)).map c)
      (by simpa [Functor.map_comp] using congrArg ((H.shift n).map) hab)
      (by simpa [Functor.map_comp] using congrArg ((H.shift n).map) hc₂)
      (by
        simpa using (H.homologySequenceδ_naturality T₁ T₂ φ n (n + 1) rfl).symm)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (n + 1)).map) hab)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (n + 1)).map) hc₂)
  let ψ : R₁ ⟶ R₂ :=
    δlastFunctor.map ψ₅
  have hR₁ : R₁.Exact := by
    simpa [R₁] using
      (H.homologySequenceComposableArrows₅_exact T₁ hT₁ n (n + 1) rfl).δlast
  have hR₂ : R₂.Exact := by
    simpa [R₂] using
      (H.homologySequenceComposableArrows₅_exact T₂ hT₂ n (n + 1) rfl).δlast
  -- The surrounding four vertical maps are isomorphisms, hence the middle one is too.
  letI : IsIso ((H.shift n).map a) := ha n
  letI : IsIso ((H.shift n).map b) := hb n
  letI : IsIso ((H.shift (n + 1)).map a) := ha (n + 1)
  letI : IsIso ((H.shift (n + 1)).map b) := hb (n + 1)
  have h₀ : Epi (app' ψ 0) := by
    simpa [ψ, ψ₅] using (show Epi ((H.shift n).map a) by infer_instance)
  have h₁ : IsIso (app' ψ 1) := by
    simpa [ψ, ψ₅] using (show IsIso ((H.shift n).map b) by infer_instance)
  have h₂ : IsIso (app' ψ 3) := by
    simpa [ψ, ψ₅] using (show IsIso ((H.shift (n + 1)).map a) by infer_instance)
  have h₃ : Mono (app' ψ 4) := by
    simpa [ψ, ψ₅] using (show Mono ((H.shift (n + 1)).map b) by infer_instance)
  have hψ :
      IsIso (app' ψ 2) :=
    isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ ψ h₀ h₁ h₂ h₃
  simpa [ψ, ψ₅] using hψ

/-- Lemma 13.5.5: the morphisms inverted by all shifted values of a homological functor form a
saturated multiplicative system compatible with the triangulated structure. -/
instance :
    IsSaturatedMultiplicativeSystem S := by
  -- Lemma 13.5.2 packages MS2 and MS3 from the two cancellation lemmas above.
  letI : MorphismProperty.HasLeftCalculusOfFractions S :=
    hasLeftCalculusOfFractions_of_ext_and_compatibleWithTriangulation S
      (homologicalKernel_trW_ext_left H)
  letI : MorphismProperty.HasRightCalculusOfFractions S :=
    hasRightCalculusOfFractions_of_ext_and_compatibleWithTriangulation S
      (homologicalKernel_trW_ext_right H)
  refine
    { toHasLeftCalculusOfFractions := inferInstance
      toHasRightCalculusOfFractions := inferInstance
      saturation := ?_ }
  intro X₀ X₁ X₂ X₃ f g h hfg hgh
  -- Saturation is checked after applying each shifted functor into the abelian target.
  rw [H.mem_homologicalKernel_trW_iff] at hfg hgh ⊢
  intro n
  have hfg' : isomorphisms A (((H.shift n).map f) ≫ (H.shift n).map g) := by
    simpa [Functor.map_comp, isomorphisms.iff] using hfg n
  have hgh' : isomorphisms A (((H.shift n).map g) ≫ (H.shift n).map h) := by
    simpa [Functor.map_comp, isomorphisms.iff] using hgh n
  simpa [isomorphisms.iff] using
    IsSaturatedMultiplicativeSystem.saturation
      ((H.shift n).map f) ((H.shift n).map g) ((H.shift n).map h) hfg' hgh'

end

end CategoryTheory
