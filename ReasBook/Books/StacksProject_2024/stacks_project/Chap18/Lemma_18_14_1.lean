import Mathlib
import StacksProject_2024.Chap18.Lemma_18_14_2

-- Declarations for this item will be appended below by the statement pipeline.

import Mathlib.CategoryTheory.Limits.ExactFunctor

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{u})

/- Domain-style sampling for Lemma 18.14.1:
- primary domain: sheaves of modules on a Grothendieck site, together with exact functors between
  abelian categories and the generic kernel/cokernel comparison isomorphisms attached to a
  functor that preserves finite (co)limits;
- sampled owner declarations:
  `Mod`,
  `SheafOfModules.toSheaf`,
  `toSheaf_preservesColimits`,
  `ExactFunctor.of`,
  `ShortComplex.exact_map_iff_of_faithful`,
  `PreservesKernel.iso`,
  `PreservesCokernel.iso`;
- best owner abstraction: the source-facing owner notation `Mod(𝒪)` on top of the canonical owner
  `SheafOfModules 𝒪`, together with the
  bridge/view functor `SheafOfModules.toSheaf 𝒪` to sheaves of abelian groups;
- primitive-vs-derived split:
  the primitive data are only the ambient site, the ring-valued sheaf `𝒪`, and the canonical
  forgetful functor `SheafOfModules.toSheaf 𝒪`;
  abelianness of `Mod(𝒪)`, colimit preservation of `SheafOfModules.toSheaf 𝒪` from
  `Lemma_18_14_2`, and the kernel/cokernel comparison isomorphisms already live upstream, while
  the source-facing content here is the canonical exact functor
  `ExactFunctor.of (SheafOfModules.toSheaf 𝒪)` and the resulting exactness comparison for short
  complexes.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that `Mod(𝒪)` is abelian and that the forgetful
  functor to abelian sheaves is exact, plus the exactness comparison for short complexes;
- `core/canonical`: the owner category `SheafOfModules 𝒪`, the source-facing notation `Mod(𝒪)`,
  the canonical bridge functor
  `SheafOfModules.toSheaf 𝒪`, the bundled exact functor
  `ExactFunctor.of (SheafOfModules.toSheaf 𝒪)`, and the generic declarations
  `ShortComplex.exact_map_iff_of_faithful`, `PreservesKernel.iso`, and
  `PreservesCokernel.iso`;
- `bridge/view`: the specialization of `ShortComplex.exact_map_iff_of_faithful` to
  `SheafOfModules.toSheaf 𝒪`, which compares exactness in `Mod(𝒪)` with exactness after applying
  the canonical forgetful functor.

The two comparison isomorphisms are already owned upstream by `PreservesKernel.iso` and
`PreservesCokernel.iso`, so this file should not keep parallel public abbreviations for them.
-/

/- Lemma 18.14.1 (1): the category `Mod(𝒪)` of sheaves of `𝒪`-modules is abelian. This is the
canonical mathlib instance on `Mod(𝒪)`. -/
#synth Abelian (Mod(𝒪))

section Exactness

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Lemma 18.14.1: for a ringed topos `(Sh(𝒞), 𝒪)`, the category `Mod(𝒪)` of sheaves of
`𝒪`-modules is abelian, and the forgetful functor to abelian sheaves is exact. This is the
canonical bundled exact functor `ExactFunctor.of (SheafOfModules.toSheaf 𝒪)`. -/
#check
  (ExactFunctor.of (SheafOfModules.toSheaf 𝒪) :
    Mod(𝒪) ⥤ₑ Sheaf J AddCommGrpCat.{u})

-- Proof sketch: `ShortComplex.exact_map_iff_of_faithful` is the canonical owner theorem here.
-- Finite-colimit preservation of `SheafOfModules.toSheaf 𝒪` is already available upstream from
-- Lemma `18.14.2`, so this file should reuse that owner instance directly.
/- Companion recall: exactness of a short complex of `𝒪`-module sheaves agrees with exactness of
the underlying short complex of abelian sheaves by the canonical owner theorem
`ShortComplex.exact_map_iff_of_faithful`. -/
variable (S : ShortComplex (Mod(𝒪))) in
#check (S.exact_map_iff_of_faithful (SheafOfModules.toSheaf 𝒪)).symm

/- Companion recall: the kernel comparison for `SheafOfModules.toSheaf 𝒪` is the canonical
generic isomorphism `PreservesKernel.iso`. -/
#check PreservesKernel.iso (SheafOfModules.toSheaf 𝒪)

/- Companion recall: the cokernel comparison for `SheafOfModules.toSheaf 𝒪` is the canonical
generic isomorphism `PreservesCokernel.iso`. -/
#check PreservesCokernel.iso (SheafOfModules.toSheaf 𝒪)

end Exactness
