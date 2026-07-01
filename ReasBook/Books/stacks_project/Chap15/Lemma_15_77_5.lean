import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_project.Chap13.Situation_13_15_1
import stacks_project.Chap15.Definition_15_69_1
import stacks_project.Chap15.Lemma_15_66_1
import stacks_project.Chap15.Lemma_15_77_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

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

-- Proof sketch: apply Lemma `15.69.2` to the truncation `τ_{\ge a+1}K` using the hypothesis that
-- `Ext^{-a}_R(K,-)` sends monomorphisms to monomorphisms, which forces the degree `-a` Ext of the
-- upper truncation to vanish against all modules. This gives projective-amplitude in `[a+1,b]`
-- for some `b`; then apply Lemma `15.77.1 (3)` to the canonical truncation triangle from
-- Remark `13.12.4`.
/-- Lemma 15.77.5: if `K` is an object of `D^-(R)` and `Ext^{-a}_R(K, -)` sends injective
`R`-module maps to injective maps, then the upper truncation `\tau_{\ge a + 1}K` has
projective-amplitude in `[a + 1, b]` for some `b`, and there is a unique isomorphism
`K \cong \tau_{\le a}K \oplus \tau_{\ge a + 1}K` compatible with the canonical truncation maps. -/
theorem existsUnique_truncation_biprod_and_projectiveAmplitude_of_ext_preserves_monos
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : (derivedExtToModuleFunctor K.obj (-a)).PreservesMonomorphisms) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE a).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι a).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := sorry

end

end CategoryTheory
