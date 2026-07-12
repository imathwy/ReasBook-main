import Mathlib
import StacksProject_2024.Chap28.Definition_28_4_1
import StacksProject_2024.Chap28.Definition_28_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the affine-cover recursion principle
-- `AlgebraicGeometry.of_affine_open_cover`; combined with the local Chapter 28 owner
-- `Scheme.HasRingPropertyLocally`, this item is best exposed as affine/open-cover criteria for
-- that existing scheme predicate.

variable (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P]

/-- Lemma 28.4.3 (1): a scheme `X` has ring property `P` locally if and only if for every affine
open `U ⊆ X`, the ring of sections `Γ(X, U)` satisfies `P`. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing :
    X.HasRingPropertyLocally P ↔
      ∀ U : X.affineOpens, P (Γ(X, U)) := sorry

/-- Lemma 28.4.3 (2): a scheme `X` has ring property `P` locally if and only if it admits an
affine open covering whose section rings satisfy `P`. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing :
    X.HasRingPropertyLocally P ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, P (Γ(X, (𝒰.f i).opensRange)) := sorry

/-- Lemma 28.4.3 (3): a scheme `X` has ring property `P` locally if and only if it admits an
open covering by open subschemes that have ring property `P` locally. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally :
    X.HasRingPropertyLocally P ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, ((𝒰.f i).opensRange).toScheme.HasRingPropertyLocally P := sorry

variable {X : Scheme.{u}} {P : CommRingCat.{u} → Prop}

/-- Companion instance for Lemma 28.4.3: ring properties that hold locally on a scheme also hold
locally on every open subscheme. -/
instance instHasRingPropertyLocallyToScheme [RingPropertyIsLocal P] [X.HasRingPropertyLocally P]
    (U : X.Opens) :
    U.toScheme.HasRingPropertyLocally P := by
  sorry

/-- Lemma 28.4.3 (4): if a scheme `X` has ring property `P` locally, then every open subscheme of
`X` has ring property `P` locally. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_toScheme [RingPropertyIsLocal P]
    (hX : X.HasRingPropertyLocally P) (U : X.Opens) :
    U.toScheme.HasRingPropertyLocally P := by
  letI := hX
  infer_instance

end AlgebraicGeometry.Scheme
