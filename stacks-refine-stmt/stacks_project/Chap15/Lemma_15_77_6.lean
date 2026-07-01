import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_project.Chap13.Situation_13_15_1
import stacks_project.Chap15.Definition_15_69_1
import stacks_project.Chap15.Lemma_15_66_1
import stacks_project.Chap15.Lemma_15_77_1
import stacks_project.Chap15.Lemma_15_77_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: bounded-above derived-module objects, vanishing of a fixed-degree Ext functor
  against modules, and the induced gap splitting of canonical truncations in the standard
  `t`-structure;
- sampled owner declarations:
  `CategoryTheory.existsUnique_truncation_biprod_and_projectiveAmplitude_of_ext_preserves_monos`,
  `CategoryTheory.derivedExtToModuleFunctor`,
  `DerivedCategory.isLE_iff`,
  `CategoryTheory.TStructure.isLE_iff_isIso_truncLEι_app`;
- best owner abstraction: this lemma remains `source-facing`, but its canonical owner inputs are
  the zero-object condition on the degree-`-a` functor `derivedExtToModuleFunctor K.obj (-a)`
  and the canonical truncation API already used in Lemma `15.77.5`;
- primitive data: the bounded-above object `K`, the index `a`, and the owner-level vanishing
  condition `IsZero (derivedExtToModuleFunctor K.obj (-a))`;
- derived API: projective-amplitude of the upper truncation and the unique compatible biproduct
  decomposition with the degree-`a` gap.

Source/core/bridge triage:
- `source-facing`: Lemma `15.77.6`;
- `core/canonical`: `derivedExtToModuleFunctor`, `Functor.PreservesMonomorphisms`,
  `DerivedCategory.IsLE`, and the truncation-transition API of the standard `t`-structure;
- `bridge/view`: the native compatibility equations for the canonical splitting, without
  introducing a second owner.
-/

-- Proof sketch: view the hypothesis as the canonical zero-object condition on
-- `derivedExtToModuleFunctor K.obj (-a)`, hence in particular as the owner-level
-- mono-preservation hypothesis from Lemma `15.77.5`. Apply that lemma to obtain the canonical
-- splitting `K ≅ τ_{\le a}K ⊞ τ_{\ge a + 1}K` and projective-amplitude for the upper truncation.
-- The vanishing in degree `-a` forces `H^a(K) = 0`, so `τ_{\le a}K` identifies with
-- `τ_{\le a - 1}K`, giving the stated gap decomposition.
/-- Lemma 15.77.6: if `K` is an object of `D^-(R)` and `Ext^{-a}_R(K, M)` vanishes for every
`R`-module `M`, then there is a unique isomorphism
`K \cong \tau_{\le a - 1}K \oplus \tau_{\ge a + 1}K` compatible with the canonical truncation
maps, and the upper truncation `\tau_{\ge a + 1}K` has projective-amplitude in `[a + 1, b]` for
some `b`. -/
theorem existsUnique_truncation_gap_biprod_and_projectiveAmplitude_of_ext_vanishing
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : IsZero (derivedExtToModuleFunctor K.obj (-a))) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE (a - 1)).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι (a - 1)).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := sorry

end

end CategoryTheory
