import Mathlib
import stacks_project.Chap12.Remark_12_29_2
import stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [Ring A] [Ring B] (f : A →+* B)

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.65.11:
- primary domain: pseudo-coherence in derived categories under restriction of scalars along
  a ring hom `f : A →+* B`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.IsPseudoCoherent`,
  `ModuleCat.restrictScalars`,
  `restrictScalars_exact`,
  `CategoryTheory.Functor.mapDerivedCategory`;
- best owner abstraction: the source-facing content is the pair of comparison theorems below,
  while the restriction construction itself is owned canonically by the exact derived functor
  `(ModuleCat.restrictScalars f).mapDerivedCategory`; this file should reuse that owner directly
  rather than keep an `Algebra`-specific wrapper;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived `B`-complex `K`, and the pseudo-coherence
  hypothesis on the restricted module object `((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))`;
  derived API is the equivalence between the absolute pseudo-coherence owners on `K` and on its
  image under the canonical restriction functor;
- source/core/bridge triage:
  `source-facing`: `isMPseudoCoherent_iff_restrictScalars`,
    `isPseudoCoherent_iff_restrictScalars`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`,
    `DerivedCategory.IsPseudoCoherent`, `ModuleCat.IsPseudoCoherent`,
    `ModuleCat.restrictScalars`, `restrictScalars_exact`, and
    `Functor.mapDerivedCategory`;
  `bridge/view`: restriction of scalars along `f` via
    `(ModuleCat.restrictScalars f).mapDerivedCategory`.
-/

local instance restrictScalars_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
  ((exactFunctor_iff (ModuleCat.restrictScalars.{u} f)).1 (restrictScalars_exact f)).1

-- Proof sketch: for `→`, view a bounded finite-free `B`-model for `K` termwise as a bounded-above
-- complex of pseudo-coherent `A`-modules using the hypothesis that `B` is pseudo-coherent over
-- `A` after restriction of scalars along `f`, then apply Lemma `15.65.9` and the
-- distinguished-triangle criterion of Lemma
-- `15.65.2`. For `←`, start from an `A`-linear approximation of the restricted complex, tensor it with `B`,
-- and descend on the top nonvanishing cohomology degree exactly as in the Stacks Project proof.
/-- Lemma 15.65.11: if `f : A →+* B` is a ring map and `B` is pseudo-coherent as an `A`-module,
then a
derived `B`-complex is `m`-pseudo-coherent exactly when its restriction of scalars to `A` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_iff_restrictScalars
    (K : DModB) (m : ℤ)
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsMPseudoCoherent m := sorry

-- Proof sketch: apply `isMPseudoCoherent_iff_restrictScalars` for every `m : ℤ` and use the
-- characterization of pseudo-coherence as `m`-pseudo-coherence for all `m` from Lemma `15.65.5`
-- on both the `B`-linear complex and its restriction to `A`.
/-- Under the same hypothesis on `B`, pseudo-coherence of a derived `B`-complex is equivalent to
pseudo-coherence after restriction of scalars to `A`. -/
theorem isPseudoCoherent_iff_restrictScalars
    (K : DModB)
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsPseudoCoherent ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsPseudoCoherent := sorry

end

end CategoryTheory
