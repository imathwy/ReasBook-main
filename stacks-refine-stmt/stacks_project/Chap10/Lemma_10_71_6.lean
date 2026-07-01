import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.Abelian.Ext

/- Domain triage: this item lies in the abelian-category `Ext` exact-sequence domain.
* sampled owner declarations: `covariantSequence`, `covariantSequence_exact`,
  `mono_postcomp_mk₀_of_mono`, and `addEquiv₀`;
* core/canonical owner abstraction: the covariant long exact `Ext` sequence attached to a short
  exact short complex, packaged as `covariantSequence` with exactness theorem
  `covariantSequence_exact`;
* primitive data: the short exact sequence and the object in the first `Ext` variable;
* derived API: the degree-`0` monomorphism `mono_postcomp_mk₀_of_mono` and the canonical
  identification `addEquiv₀ : Ext X Y 0 ≃+ (X ⟶ Y)`.

This file is therefore `core/canonical`: Lemma 10.71.6 adds no new source-facing data beyond the
owner long exact sequence, so the correct refinement is direct recall of that owner theorem and its
degree-`0` companions rather than a parallel module-specific wrapper sequence. -/

/- Lemma 10.71.6: for a short exact sequence `0 ⟶ N' ⟶ N ⟶ N'' ⟶ 0` in `R`-modules and any
module `M`, the owner exactness theorem is `covariantSequence_exact`. The textbook display is its
degree-`0` and degree-`1` initial segment, with the leading
`0 ⟶ Hom_R(M, N')` supplied by `mono_postcomp_mk₀_of_mono` and the identification
`Ext⁰(M, Nᵢ) ≅ Hom_R(M, Nᵢ)` supplied by `addEquiv₀`. -/
recall covariantSequence_exact

/- Companion recall: the long exact sequence itself is packaged by the owner declaration
`covariantSequence`. -/
recall covariantSequence

/- Companion recall: the first degree-`0` map in the covariant sequence is monic, giving the
leading `0 ⟶ Hom_R(M, N')` in the textbook display. -/
recall mono_postcomp_mk₀_of_mono

/- Companion recall: degree `0` `Ext` is canonically identified with morphisms by `addEquiv₀`. -/
recall addEquiv₀

end CategoryTheory.Abelian.Ext
