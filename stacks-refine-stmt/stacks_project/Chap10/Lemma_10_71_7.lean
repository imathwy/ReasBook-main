import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.Abelian.Ext

/-
Lemma 10.71.7 lies in the abelian-category `Ext` exact-sequence domain.

Layering for this item:
* source-facing: the textbook six-term display coming from a short exact sequence
  `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` and the contravariant `Ext` long exact sequence in the first variable,
  with `N` fixed in the second variable;
* core/canonical owner: `contravariantSequence` and its exactness theorem
  `contravariantSequence_exact`;
* bridge/view: the leading `0 ⟶ Hom(M'', N)` is supplied by `mono_precomp_mk₀_of_epi`, and the
  degree-`0` identification `Ext⁰(Mᵢ, N) ≅ Hom(Mᵢ, N)` is supplied by `addEquiv₀`.

Sampled owner-style declarations: `contravariantSequence`, `contravariantSequence_exact`,
`mono_precomp_mk₀_of_epi`, and `addEquiv₀`. Since the source adds no extra public data beyond this
owner package, the main entry is direct canonical recall rather than a parallel wrapper sequence.
-/

/- Lemma 10.71.7: for a short exact sequence `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` in `R`-modules and any
module `N`, the owner exactness theorem is `contravariantSequence_exact`. The textbook display is
its degree-`0` and degree-`1` initial segment, with the leading `0 ⟶ Hom_R(M'', N)` supplied by
`mono_precomp_mk₀_of_epi` and the identification `Ext⁰(Mᵢ, N) ≅ Hom_R(Mᵢ, N)` supplied by
`addEquiv₀`. -/
recall contravariantSequence_exact

/- Companion recall: the long exact sequence itself is packaged by the owner declaration
`contravariantSequence`. -/
recall contravariantSequence

/- Companion recall: the first degree-`0` map in the contravariant sequence is monic, giving the
leading `0 ⟶ Hom_R(M'', N)` in the textbook display. -/
recall mono_precomp_mk₀_of_epi

/- Companion recall: degree `0` `Ext` is canonically identified with morphisms by `addEquiv₀`. -/
recall addEquiv₀

end CategoryTheory.Abelian.Ext
