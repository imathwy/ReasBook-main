import Mathlib.Tactic.Recall
import stacks_project.Chap12.Lemma_12_6_3
import stacks_project.Chap12.Lemma_12_6_4

namespace CategoryTheory.Abelian.Ext

/- Domain-style sampling for Lemma 15.55.2:
- primary domain: `Ext¹` for the abelian category of `R`-modules and its classification by short
  exact sequences;
- sampled owner declarations:
  `ExtensionClass.toExtAddEquiv`,
  `ExtensionClass.toExt_pullback`,
  `contravariantSequence`,
  `covariantSequence_exact`,
  `covariantSequence`,
  `contravariantSequence_exact`,
  `mono_precomp_mk₀_of_epi`,
  `mono_postcomp_mk₀_of_mono`,
  `addEquiv₀`;
- best owner abstraction: the source-facing extension group is `ExtensionClass`, the canonical
  owner is `Ext`, the project-level bridge is owned by
  `stacks_project.Chap12.Lemma_12_6_3`, and the surrounding long exact sequences are owned by
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`;
- primitive data: the ambient module category and the two module objects;
- derived API: the additive comparison `ExtensionClass N M ≃+ Ext M N 1`, its pullback/pushout
  compatibility, the packaged long exact sequences, their exactness theorems, the leading
  degree-`0` monomorphisms, and the canonical identification `Ext⁰ ≃ Hom`.

Source/core/bridge triage:
- `source-facing`: `ExtensionClass N M`;
- `core/canonical`: `Ext M N 1`;
- `bridge/view`: `ExtensionClass.toExtAddEquiv`.

This file stays at the `bridge/view` layer: it recalls the canonical comparison and its standard
companions, without introducing any parallel module-specific wrapper API.
-/
/- Lemma 15.55.2: in the abelian category of `R`-modules, the categorical extension group
`Ext_𝒜(M, N)` is the source-facing owner `ExtensionClass N M`, and the canonical comparison with
the algebraic group `Ext¹_R(M, N)` is `ExtensionClass.toExtAddEquiv`. The source compatibility
with the long exact and six-term `Ext` sequences is expressed by the canonical owner sequence
declarations and their degree-`0` companions recalled below. -/
recall ExtensionClass.toExtAddEquiv

/- Companion recall: the comparison is compatible with pullback in the first `Ext` variable via
the canonical theorem `ExtensionClass.toExt_pullback`. -/
recall ExtensionClass.toExt_pullback

/- Companion recall: the comparison is compatible with pushout in the second `Ext` variable via
the canonical theorem `ExtensionClass.toExt_pushout`. -/
recall ExtensionClass.toExt_pushout

/- Companion recall: the contravariant six-term exact sequence is the canonical owner theorem
`contravariantSequence_exact`. -/
recall contravariantSequence_exact

/- Companion recall: the contravariant long exact sequence itself is packaged by the owner
declaration `contravariantSequence`. -/
recall contravariantSequence

/- Companion recall: the first degree-`0` map in the contravariant sequence is monic, giving the
leading `0 ⟶ Hom_R(M'', N)` in the textbook six-term display. -/
recall mono_precomp_mk₀_of_epi

/- Companion recall: the covariant six-term exact sequence is the canonical owner theorem
`covariantSequence_exact`. -/
recall covariantSequence_exact

/- Companion recall: the covariant long exact sequence itself is packaged by the owner declaration
`covariantSequence`. -/
recall covariantSequence

/- Companion recall: the first degree-`0` map in the covariant sequence is monic, giving the
leading `0 ⟶ Hom_R(M, N')` in the textbook six-term display. -/
recall mono_postcomp_mk₀_of_mono

/- Companion recall: degree `0` `Ext` is canonically identified with `Hom` by `addEquiv₀`. -/
recall addEquiv₀

end CategoryTheory.Abelian.Ext
