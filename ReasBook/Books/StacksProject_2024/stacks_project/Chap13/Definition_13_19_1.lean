import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

/- Definition 13.19.1: for an object `A` of an abelian category, the canonical mathlib structure
`CategoryTheory.ProjectiveResolution A` encodes a projective resolution of `A`; its associated
cochain complex is `R.cochainComplex`, and the map to `A[0]` is `R.π'`. -/
recall CategoryTheory.ProjectiveResolution

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: bounded-above projective models for cochain complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn`,
  `CochainComplex.MinusWithTermsIn.term_mem`,
  `CochainComplex.MinusWithTermsIn.exists_isStrictlyLE`,
  `CochainComplex.isKProjective_of_projective`,
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectivePlus`;
- best owner abstraction: the source-facing thin vocabulary layer
  `CochainComplex.ProjectiveMinus 𝒜` over the generic owner
  `CochainComplex.MinusWithTermsIn (isProjective 𝒜)` for bounded-above complexes whose terms are
  projective;
- primitive data here: a chosen bounded-above projective complex in that owner and a comparison
  morphism to the target complex;
- derived API here: coercions from a chosen projective resolution to the canonical owner / bounded-
  above / underlying complex, the bounded-above witness, termwise projectivity, quasi-isomorphism,
  and the resulting `IsKProjective` instance.

This file is therefore `source-facing`: it bundles a chosen projective resolution of a cochain
complex, but its bounded-above termwise-projective data should be owned by the chapter owner
`CochainComplex.ProjectiveMinus 𝒜`, viewed through the generic owner
`CochainComplex.MinusWithTermsIn (isProjective 𝒜)`, rather than by a duplicate local full
subcategory definition.
-/

/-- The bounded-above cochain complexes whose terms are projective objects. -/
abbrev ProjectiveMinus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.MinusWithTermsIn (isProjective 𝒜)

namespace MinusWithTermsIn

-- Proof sketch: unpack the bounded-above owner `MinusWithTermsIn (isProjective 𝒜)` into the
-- bounded-above witness and termwise projectivity, then apply
-- `CochainComplex.isKProjective_of_projective`.
/-- A bounded-above projective complex is K-projective. -/
instance instIsKProjective (P : ProjectiveMinus 𝒜) :
    IsKProjective (P : CochainComplex 𝒜 ℤ) := by
  obtain ⟨d, hd⟩ := P.exists_isStrictlyLE
  let _ : (P : CochainComplex 𝒜 ℤ).IsStrictlyLE d := hd
  let _ : ∀ n : ℤ, Projective ((P : CochainComplex 𝒜 ℤ).X n) := P.term_mem
  exact isKProjective_of_projective (P : CochainComplex 𝒜 ℤ) d

end MinusWithTermsIn

/-- A bounded-above projective resolution of a cochain complex is a quasi-isomorphism from a
bounded-above cochain complex of projective objects to the given complex. -/
structure ProjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The bounded-above projective cochain complex appearing in the resolution. -/
  complex : ProjectiveMinus 𝒜
  /-- The comparison map from the resolving complex to the target complex. -/
  π : (complex : CochainComplex 𝒜 ℤ) ⟶ K
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso : QuasiIso π := by infer_instance

attribute [instance] ProjectiveResolution.quasiIso

namespace IsStrictlyLEQuasiIsoWithTermsIn

variable {a : ℤ} {K Q : CochainComplex 𝒜 ℤ} {π : Q ⟶ K}

/-- A bounded-above quasi-isomorphism from a cochain complex of projective objects canonically
packages as a cochain-complex projective resolution. -/
abbrev toProjectiveResolution
    (hπ : IsStrictlyLEQuasiIsoWithTermsIn (isProjective 𝒜) a K Q π) :
    ProjectiveResolution K where
  complex := hπ.toMinusWithTermsIn
  π := π
  quasiIso := hπ.quasiIso

end IsStrictlyLEQuasiIsoWithTermsIn

namespace ProjectiveResolution

/-- A projective resolution can be used as its bounded-above projective complex. -/
instance {K : CochainComplex 𝒜 ℤ} :
    CoeOut (ProjectiveResolution K) (ProjectiveMinus 𝒜) where
  coe P := P.complex

/-- A projective resolution can be used as its bounded-above resolving complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (ProjectiveResolution K) (Minus 𝒜) where
  coe P := P.complex

/-- A projective resolution can be used as its resolving cochain complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (ProjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe P := P.complex

/-- The resolving complex in a projective resolution is bounded above. -/
theorem minus {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    CochainComplex.minus 𝒜 (P : CochainComplex 𝒜 ℤ) :=
  by
    simpa using P.complex.minus

/-- The resolving complex in a projective resolution is zero in all sufficiently high degrees. -/
theorem exists_isStrictlyLE {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    ∃ d : ℤ, (P : CochainComplex 𝒜 ℤ).IsStrictlyLE d :=
  by
    simpa using P.complex.exists_isStrictlyLE

/-- Each term of the resolving complex in a projective resolution is projective. -/
theorem projective {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) (n : ℤ) :
    Projective ((P : CochainComplex 𝒜 ℤ).X n) :=
  by
    simpa using P.complex.term_mem n

attribute [instance] ProjectiveResolution.projective

-- Proof sketch: the canonical owner `MinusWithTermsIn (isProjective 𝒜)` already packages the
-- bounded-above/projective hypotheses and carries the `IsKProjective` instance.
/-- The resolving complex in a projective resolution is K-projective. -/
instance instIsKProjective {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    IsKProjective (P : CochainComplex 𝒜 ℤ) :=
  MinusWithTermsIn.instIsKProjective P.complex

end ProjectiveResolution

end CochainComplex
