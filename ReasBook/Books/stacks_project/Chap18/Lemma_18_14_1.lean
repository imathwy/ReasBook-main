import Mathlib

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
  `SheafOfModules.toSheaf`,
  `exactFunctor`,
  `PreservesKernel.iso`,
  `PreservesCokernel.iso`;
- best owner abstraction: the canonical owner category `SheafOfModules 𝒪` together with the
  bridge/view functor `SheafOfModules.toSheaf 𝒪` to sheaves of abelian groups;
- primitive-vs-derived split:
  the primitive data are only the ambient site, the ring-valued sheaf `𝒪`, and the canonical
  forgetful functor `SheafOfModules.toSheaf 𝒪`;
  abelianness of `SheafOfModules 𝒪` and the kernel/cokernel comparison isomorphisms already live
  upstream, while the source-facing content here is the exactness of `SheafOfModules.toSheaf 𝒪`
  and the resulting exactness comparison for short complexes.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that `Mod(𝒪)` is abelian and that the forgetful
  functor to abelian sheaves is exact, plus the exactness comparison for short complexes;
- `core/canonical`: the owner category `SheafOfModules 𝒪`, the canonical bridge functor
  `SheafOfModules.toSheaf 𝒪`, and the generic declarations `exactFunctor`,
  `PreservesKernel.iso`, and `PreservesCokernel.iso`;
- `bridge/view`: the theorem `moduleSheaf_exact_iff_underlyingAbelian_exact`, which compares
  exactness in `Mod(𝒪)` with exactness after applying the canonical forgetful functor.

The two comparison isomorphisms are already owned upstream by `PreservesKernel.iso` and
`PreservesCokernel.iso`, so this file should not keep parallel public abbreviations for them.
-/

/- Lemma 18.14.1 (1): the category `Mod(𝒪)` of sheaves of `𝒪`-modules is abelian. This is the
canonical mathlib instance on `SheafOfModules 𝒪`. -/
#synth Abelian (SheafOfModules 𝒪)

section Exactness

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Forgetting the module structure on sheaves preserves finite colimits. -/
private noncomputable instance moduleSheafToSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf 𝒪) := sorry

-- Proof sketch: `SheafOfModules 𝒪` is abelian by the owner API, and
-- `SheafOfModules.toSheaf 𝒪` already preserves finite limits. Together with the finite-colimit
-- preservation above, this is exactly the bundled notion of an exact functor.
/-- Lemma 18.14.1: for a ringed topos `(Sh(𝒞), 𝒪)`, the category `Mod(𝒪)` of sheaves of
`𝒪`-modules is abelian, and the forgetful functor to abelian sheaves is exact. -/
theorem moduleSheaf_toSheaf_exact :
    exactFunctor (SheafOfModules 𝒪) (Sheaf J AddCommGrpCat.{u})
      (SheafOfModules.toSheaf 𝒪) := sorry

-- Proof sketch: use the exactness of `SheafOfModules.toSheaf 𝒪`; exact functors preserve exact
-- short complexes, and for this forgetful functor the kernel-cokernel comparison identifies the
-- exactness condition with the one in abelian sheaves.
/-- Exactness of a short complex of `𝒪`-module sheaves agrees with exactness of the underlying
short complex of abelian sheaves. -/
theorem moduleSheaf_exact_iff_underlyingAbelian_exact
    (S : ShortComplex (SheafOfModules 𝒪)) :
    S.Exact ↔ (S.map (SheafOfModules.toSheaf 𝒪)).Exact := sorry

/- Companion recall: the kernel comparison for `SheafOfModules.toSheaf 𝒪` is the canonical
generic isomorphism `PreservesKernel.iso`. -/
#check PreservesKernel.iso (SheafOfModules.toSheaf 𝒪)

/- Companion recall: the cokernel comparison for `SheafOfModules.toSheaf 𝒪` is the canonical
generic isomorphism `PreservesCokernel.iso`. -/
#check PreservesCokernel.iso (SheafOfModules.toSheaf 𝒪)

end Exactness
