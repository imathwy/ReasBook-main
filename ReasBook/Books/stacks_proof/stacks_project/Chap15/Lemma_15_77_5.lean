import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_proof.stacks_project.Chap13.Definition_13_27_1
import stacks_proof.stacks_project.Chap13.Situation_13_15_1
import stacks_proof.stacks_project.Chap13.Remark_13_12_4
import stacks_proof.stacks_project.Chap15.Definition_15_69_1
import stacks_proof.stacks_project.Chap15.Lemma_15_77_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling:
- primary domain: functorial Ext in the derived category, specifically the condition that the
  fixed-degree Ext functor on modules preserves monomorphisms;
- sampled owner declarations:
  `CategoryTheory.derivedExtToModuleFunctor`,
  `CategoryTheory.Functor.PreservesMonomorphisms`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge`;
- best owner abstraction: `(derivedExtToModuleFunctor K n).PreservesMonomorphisms` is the
  canonical owner-level form of the source hypothesis "Ext^n_R(K,-) sends injective maps to
  injective maps", so a separate local predicate would just duplicate that owner API;
- primitive data: the bounded-above object `K`, the degree `n`, and the canonical Ext functor
  `derivedExtToModuleFunctor K n`;
- derived API: the pointwise mono statements for the functorial maps
  `(derivedExtToModuleFunctor K n).map f`, the projective-amplitude conclusion for the upper
  truncation, and the compatible biproduct decomposition.

Source/core/bridge triage:
- `source-facing`: Lemma `15.77.5`;
- `core/canonical`: `Functor.PreservesMonomorphisms` applied to
  `derivedExtToModuleFunctor K n`;
- `bridge/view`: the explicit pointwise maps `(derivedExtToModuleFunctor K n).map f`, which
  remain available from the owner functor without a second local wrapper.
-/

/-- Helper for Lemma 15.77.5: the additive-group-valued functor
`M ↦ Ext^n_R(K, M[0])` on `R`-modules. This is the local replacement for the broken upstream
Chapter 15 owner import. -/
noncomputable abbrev derivedExtToModuleFunctor
    (K : DMod) (n : ℤ) :
    ModuleCat R ⥤ AddCommGrpCat :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ) ⋙
    shiftFunctor _ n ⋙
      preadditiveCoyonedaObj K ⋙
        forget₂ _ AddCommGrpCat

/-- Helper for Lemma 15.77.5: the upper truncation has projective amplitude once its degree
`-a` Ext against all modules vanishes. -/
lemma truncGE_has_projectiveAmplitude_of_ext_neg_a_vanishing
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt :
      ∀ (M : ModuleCat R),
        ∀ e : Ext^(-a)(((t.truncGE (a + 1)).obj K.obj), (single₀).obj M), e = 0) :
    ∃ b : ℤ, HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b := by
  -- Route correction: this is where the source proof invokes Lemma `15.69.2` after establishing
  -- that `τ≥a+1 K` is still bounded above and has vanishing degree `-a` Ext against every
  -- module.
  -- TODO: reintroduce the exact `(4) → (1)` application of Lemma `15.69.2` once the earlier
  -- dependency frontier is repaired. Importing `Chap15/Lemma_15_69_2` currently triggers the
  -- upstream build failure in `Chap13/Lemma_13_23_4`, so the amplitude packaging remains blocked
  -- for infrastructure reasons rather than a local statement mismatch.
  let _ := hExt
  sorry

/-- Helper for Lemma 15.77.5: the upper truncation has zero degree-`-a` Ext against an injective
target module. -/
lemma truncGE_ext_neg_a_vanishes_on_injective_targets
    (K : D⁻((ModuleCat R))) (a : ℤ) (I : ModuleCat R) [Injective I] :
    ∀ e : Ext^(-a)(((t.truncGE (a + 1)).obj K.obj), (single₀).obj I), e = 0 := by
  -- Route correction: the remaining blocker is the source-faithful injective-target computation
  -- from Chapter `13`, specialized to `τ_{\ge a + 1} K` and the degree-zero injective target
  -- `I[0]`.
  -- TODO: compute `Ext^{-a}` against `I[0]` using the trivial injective resolution of `I[0]`,
  -- then use that `τ_{\ge a + 1} K` has no degree-`a` cohomology to force the class to vanish.
  sorry

/-- Helper for Lemma 15.77.5: after mapping a class to an injective envelope, the middle morphism
of the truncation triangle kills it by mono-preservation on `Ext^{-a}(K,-)`. -/
lemma truncation_triangle_middle_comp_zero_of_preserves_monos
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : (derivedExtToModuleFunctor K.obj (-a)).PreservesMonomorphisms)
    (M : ModuleCat R)
    (e : Ext^(-a)(((t.truncGE (a + 1)).obj K.obj), (single₀).obj M)) :
    ((t.triangleLEGE a (a + 1) rfl).obj K.obj).mor₂ ≫ e = 0 := by
  -- Route correction: the main proof skeleton is already reduced to this exact comparison step.
  -- It remains to embed `M` into `Injective.under M`, use the previous injective-target lemma to
  -- kill the image of `e`, and then apply mono-preservation of `derivedExtToModuleFunctor K.obj
  -- (-a)` to pull the vanishing back along `Injective.ι M`.
  let _ := hExt
  let _ := e
  sorry

/-- Helper for Lemma 15.77.5: the degree `-a` Ext of the upper truncation vanishes on all
modules under the mono-preservation hypothesis for `Ext^{-a}(K,-)`. -/
lemma truncGE_ext_neg_a_vanishes_of_preserves_monos
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : (derivedExtToModuleFunctor K.obj (-a)).PreservesMonomorphisms) :
    ∀ (M : ModuleCat R),
      ∀ e : Ext^(-a)(((t.truncGE (a + 1)).obj K.obj), (single₀).obj M), e = 0 := by
  let T : Triangle DMod := (t.triangleLEGE a (a + 1) rfl).obj K.obj
  have hT : T ∈ distTriang DMod := by
    -- Proof comment: use the canonical lower/upper truncation triangle of `K`.
    simpa [T] using t.triangleLEGE_distinguished a (a + 1) rfl K.obj
  intro M e
  have hCompZero : T.mor₂ ≫ e = 0 := by
    -- Proof comment: this is the single remaining comparison step from the source proof.
    simpa [T] using truncation_triangle_middle_comp_zero_of_preserves_monos K a hExt M e
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ (T := T) hT e hCompZero
  have hSourceLE : (T.obj₁⟦(1 : ℤ)⟧).IsLE (a - 1) := by
    have hObj₁LE : T.obj₁.IsLE a := by
      dsimp [T]
      infer_instance
    letI : T.obj₁.IsLE a := hObj₁LE
    simpa using (TStructure.t.isLE_shift T.obj₁ a 1 (a - 1))
  have hTargetGE : (((single₀).obj M)⟦-a⟧).IsGE a := by
    have hSingleGE : ((single₀).obj M).IsGE 0 := by
      infer_instance
    letI : ((single₀).obj M).IsGE 0 := hSingleGE
    simpa using (TStructure.t.isGE_shift ((single₀).obj M) 0 (-a) a)
  have hg_zero : g = 0 := by
    -- Proof comment: any factor through the shifted lower truncation vanishes by the `t`-bounds.
    exact TStructure.t.zero_of_isLE_of_isGE g (a - 1) a (by omega) hSourceLE hTargetGE
  calc
    e = T.mor₃ ≫ g := hg
    _ = 0 := by
      simp [hg_zero]

-- Proof sketch: apply Lemma `15.69.2` to the truncation `τ_{\ge a+1}K` using the hypothesis that
-- `Ext^{-a}_R(K,-)` sends monomorphisms to monomorphisms, which forces the degree `-a` Ext of the
-- upper truncation to vanish against all modules. This gives projective-amplitude in `[a+1,b]`
-- for some `b`; then apply Lemma `15.77.1 (3)` to the canonical truncation triangle from
-- Remark `13.12.4`.
/-- Lemma 15.77.5: if `K` is an object of `D^-(R)` and `Ext^{-a}_R(K, -)` sends injective
`R`-module maps to injective maps, then the upper truncation `\tau_{\ge a + 1}K` has
projective-amplitude in `[a + 1, b]` for some `b`, and there is a unique isomorphism
`K \cong \tau_{\le a}K \oplus \tau_{\ge a + 1}K` compatible with the canonical truncation maps. -/
@[stacks 0G97]
theorem existsUnique_truncation_biprod_and_projectiveAmplitude_of_ext_preserves_monos
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : (derivedExtToModuleFunctor K.obj (-a)).PreservesMonomorphisms) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE a).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι a).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := by
  have hTailExt :
      ∀ (M : ModuleCat R),
        ∀ e : Ext^(-a)(((t.truncGE (a + 1)).obj K.obj), (single₀).obj M), e = 0 :=
    truncGE_ext_neg_a_vanishes_of_preserves_monos K a hExt
  rcases truncGE_has_projectiveAmplitude_of_ext_neg_a_vanishing K a hTailExt with ⟨b, hAmp⟩
  let T : Triangle DMod := (t.triangleLEGE a (a + 1) rfl).obj K.obj
  have hT : T ∈ distTriang DMod := by
    -- Proof comment: use the canonical truncation triangle from Remark `13.12.4`.
    simpa [T] using t.triangleLEGE_distinguished a (a + 1) rfl K.obj
  have hLower :
      ∀ i : ℤ, a + 1 ≤ i → IsZero ((H i).obj T.obj₁) := by
    intro i hi
    -- Proof comment: the lower truncation has no cohomology above degree `a`.
    simpa [T] using
      (DerivedCategory.isZero_of_isLE ((t.truncLE a).obj K.obj) a i (by omega))
  have hSplit :
      ∃! e : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃,
        T.mor₁ ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = T.mor₂ :=
    existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge
      (K := T.obj₁) (L := T.obj₃) (M := T.obj₂) (a := a + 1) (b := b) hAmp hLower hT
  refine ⟨b, hAmp, ?_⟩
  -- Proof comment: unfold the canonical truncation triangle so the compatibility equations match
  -- the source-facing truncation maps in the statement.
  simpa [T] using hSplit

end

end CategoryTheory
