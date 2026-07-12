import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.Abelian.Ext

/- Domain triage: this item lies in the abelian-category `Ext` exact-sequence domain.
Sampled owner-style declarations: `contravariantSequence`, `contravariantSequence_exact`,
`covariantSequence`, `covariantSequence_exact`, `mono_precomp_mk₀_of_epi`,
`mono_postcomp_mk₀_of_mono`, and `addEquiv₀`.

Layering for this item:
* source-facing: the textbook degree-`0`/`1` six-term exact sequences attached to a short exact
  sequence in an abelian category and a fixed object in the remaining `Ext` variable;
* core/canonical owner: the mathlib exactness theorems `contravariantSequence_exact` and
  `covariantSequence_exact`, together with the packaged long exact sequences
  `contravariantSequence` and `covariantSequence`;
* bridge/view: the degree-`0` monomorphism lemmas `mono_precomp_mk₀_of_epi` and
  `mono_postcomp_mk₀_of_mono`, and the canonical identification `addEquiv₀ : Ext⁰ ≃ Hom`.

Primitive data: a short exact sequence in an abelian category and the fixed object in the
remaining `Ext` variable.
Derived API: the long exact `Ext` sequences, their exactness theorems, the leading degree-`0`
monomorphisms, and the identification `Ext⁰ ≃ Hom`.

No local wrapper API is needed: the textbook six-term displays are the initial segments of these
canonical long exact sequences, so the correct refinement is direct recall of the owner
declarations rather than a parallel local sequence package. -/

/- Lemma 12.6.4 (1): for a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in an abelian category
and any object `N`, the contravariant `Ext` groups form the canonical long exact sequence. The
textbook six-term display is its degree-`0` and degree-`1` initial segment, with the leading
`0 ⟶ Hom(M₃, N)` supplied by monicity of the degree-`0` map and the identification
`Ext⁰(Mᵢ, N) ≅ Hom(Mᵢ, N)`. -/
recall contravariantSequence_exact

/- Companion recall: the long exact sequence itself is packaged by the owner declaration
`contravariantSequence`. -/
recall contravariantSequence

/- Companion recall: the first degree-`0` map in the contravariant sequence is monic, giving the
leading `0 ⟶ Hom(M₃, N)` in the textbook six-term sequence. -/
recall mono_precomp_mk₀_of_epi

/- Lemma 12.6.4 (2): for a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in an abelian category
and any object `N`, the covariant `Ext` groups form the canonical long exact sequence. The
textbook six-term display is its degree-`0` and degree-`1` initial segment, with the leading
`0 ⟶ Hom(N, M₁)` supplied by monicity of the degree-`0` map and the identification
`Ext⁰(N, Mᵢ) ≅ Hom(N, Mᵢ)`. -/
recall covariantSequence_exact

/- Companion recall: the long exact sequence itself is packaged by the owner declaration
`covariantSequence`. -/
recall covariantSequence

/- Companion recall: the first degree-`0` map in the covariant sequence is monic, giving the
leading `0 ⟶ Hom(N, M₁)` in the textbook six-term sequence. -/
recall mono_postcomp_mk₀_of_mono

/- Companion recall: degree `0` `Ext` is canonically identified with morphisms by `addEquiv₀`. -/
recall addEquiv₀

end CategoryTheory.Abelian.Ext
