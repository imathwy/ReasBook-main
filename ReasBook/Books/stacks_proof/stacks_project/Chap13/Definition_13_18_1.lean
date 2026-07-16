import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

/- Definition 13.18.1 is the cochain-complex definition of an injective resolution: for a cochain
complex `K`, it is a quasi-isomorphism from `K` to a bounded-below cochain complex of injective
objects. The main owner of this file is therefore the source-facing cochain-complex notion
`CochainComplex.InjectiveResolution`. -/

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: bounded-below injective models for cochain complexes;
- sampled owner declarations:
  `CochainComplex.PlusWithTermsIn`,
  `CochainComplex.InjectivePlus`,
  `CochainComplex.plus_iff`,
  `CochainComplex.isKInjective_of_injective`,
  `CochainComplex.ProjectiveResolution`;
- best owner abstraction: the source-facing owner is `CochainComplex.InjectiveResolution`; its
  bounded-below injective datum should be owned by the chapter owner
  `CochainComplex.InjectivePlus 𝒜`, which is the thin source-facing vocabulary layer over the
  generic owner `CochainComplex.PlusWithTermsIn (isInjective 𝒜)`;
- primitive data here: a chosen bounded-below injective complex in the owner
  `CochainComplex.InjectivePlus 𝒜` and a comparison morphism from the original complex;
- derived API here: coercions to the bounded-below / underlying complex, the bounded-below witness,
  termwise injectivity, quasi-isomorphism, and the resulting `IsKInjective` instance.
- `source-facing`: `CochainComplex.InjectiveResolution`;
- `core/canonical`: `CochainComplex.InjectivePlus 𝒜`, viewed through the generic owner
  `CochainComplex.PlusWithTermsIn (isInjective 𝒜)`;
- `bridge/view`: the coercions from `InjectiveResolution K` to the underlying bounded-below and
  raw cochain complexes.

This file is therefore `source-facing`: it bundles a chosen injective resolution of a cochain
complex, but its bounded-below injective data should be owned by the generic bounded-below owner
`CochainComplex.PlusWithTermsIn` rather than by a duplicate local full-subcategory definition.
-/

/-- The bounded-below cochain complexes whose terms are injective objects. -/
abbrev InjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.PlusWithTermsIn (isInjective 𝒜)

namespace PlusWithTermsIn

/-- A bounded-below cochain complex of injective objects is K-injective. -/
instance instIsKInjective (I : PlusWithTermsIn (isInjective 𝒜)) :
    CochainComplex.IsKInjective (I : CochainComplex 𝒜 ℤ) := by
  obtain ⟨a, ha⟩ := I.exists_isStrictlyGE
  let _ : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective ((I : CochainComplex 𝒜 ℤ).X n) := I.term_mem
  exact isKInjective_of_injective (I : CochainComplex 𝒜 ℤ) a

end PlusWithTermsIn

/-- Helper for Definition 13.18.1: recover a quasi-isomorphism witness from typeclass inference
for the comparison morphism into the bounded-below injective complex. -/
theorem quasiIso_from_instance {K : CochainComplex 𝒜 ℤ} {I : InjectivePlus 𝒜}
    (ι : K ⟶ I) [QuasiIso ι] : QuasiIso ι :=
  inferInstance

/-- Definition 13.18.1: a bounded-below injective resolution of a cochain complex is a
quasi-isomorphism from the given complex to a bounded-below cochain complex of injective
objects. -/
@[stacks 013I]
structure InjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The bounded-below injective cochain complex appearing in the resolution. -/
  complex : InjectivePlus 𝒜
  /-- The comparison map from the original complex to the resolving complex. -/
  ι : K ⟶ complex
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso : QuasiIso ι

attribute [instance] InjectiveResolution.quasiIso

namespace InjectiveResolution

/-- An injective resolution can be used as its bounded-below injective complex. -/
instance {K : CochainComplex 𝒜 ℤ} :
    CoeOut (InjectiveResolution K) (InjectivePlus 𝒜) where
  coe I := I.complex

/-- An injective resolution can be used as its bounded-below resolving complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (InjectiveResolution K) (Plus 𝒜) where
  coe I := I.complex

/-- An injective resolution can be used as its resolving cochain complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (InjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe I := I.complex

/-- The resolving complex in an injective resolution is bounded below. -/
theorem plus {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    CochainComplex.plus 𝒜 (I : CochainComplex 𝒜 ℤ) := by
  simpa using I.complex.plus

/-- The resolving complex in an injective resolution is zero in all sufficiently negative
degrees. -/
theorem exists_isStrictlyGE {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    ∃ a : ℤ, (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := by
  simpa using I.complex.exists_isStrictlyGE

/-- Each term of the resolving complex in an injective resolution is injective. -/
theorem injective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) (n : ℤ) :
    Injective ((I : CochainComplex 𝒜 ℤ).X n) := by
  simpa using I.complex.term_mem n

attribute [instance] InjectiveResolution.injective

-- Proof sketch: unpack the canonical bounded-below owner `CochainComplex.plus 𝒜 I` to obtain a
-- degree bound, then apply `CochainComplex.isKInjective_of_injective`.
/-- The resolving complex of a bounded-below injective resolution is K-injective. -/
instance instIsKInjective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    IsKInjective (I : CochainComplex 𝒜 ℤ) :=
  PlusWithTermsIn.instIsKInjective I.complex

end InjectiveResolution

end CochainComplex
