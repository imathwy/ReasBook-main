import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

-- Semantic search note: `lean_leansearch` recalled mathlib's `Sheaf.H`,
-- `GrothendieckTopology.OneHypercover`, and generic spectral-sequence owners. The fixed-object
-- source statement is kept on the local Chapter 25 fixed-target `Hypercovering` owner, with
-- `H^i(X, -)` represented by the public objectwise sheaf-cohomology owner `Sheaf.H'`.

variable {C : Type u} [Category.{max u v} C]
variable {J : GrothendieckTopology C}
variable [Limits.HasPullbacks C]
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]

/-- A comparison datum from Čech cohomology of a fixed-target hypercovering to object
cohomology, including naturality in the coefficient sheaf. -/
structure HypercoveringCechComparison {X : C}
    (K : @Hypercovering C _ J X) (i : ℕ) where
  /-- The map induced on Čech cohomology by a morphism of coefficient sheaves. -/
  cechMapApp :
    ∀ {ℱ 𝒜 : Sheaf J AddCommGrpCat.{max u v}},
      (ℱ ⟶ 𝒜) →
      (hypercoveringCechCohomology K ℱ i ⟶
        hypercoveringCechCohomology K 𝒜 i)
  /-- The comparison map `\check H^i(K, ℱ) ⟶ H^i(X, ℱ)`. -/
  app :
    ∀ (ℱ : Sheaf J AddCommGrpCat.{max u v}),
      hypercoveringCechCohomology K ℱ i ⟶
        Sheaf.H' ℱ i X
  /-- Naturality of the comparison with respect to coefficient morphisms. -/
  naturality :
    ∀ {ℱ 𝒜 : Sheaf J AddCommGrpCat.{max u v}} (φ : ℱ ⟶ 𝒜),
      app ℱ ≫ ((Sheaf.cohomologyPresheafFunctor J i).map φ).app (op X) =
        (cechMapApp φ :
          hypercoveringCechCohomology K ℱ i ⟶
            hypercoveringCechCohomology K 𝒜 i) ≫ app 𝒜

/-- A spectral-sequence datum for a fixed-target hypercovering. The `cohomologySheaf` field is
the source's `\underline H^q(ℱ)`, exposed by its sectionwise identification with
`U ↦ H^q(U, ℱ)`. -/
structure HypercoveringCohomologySpectralSequence {X : C}
    (K : @Hypercovering C _ J X)
    (ℱ : Sheaf J AddCommGrpCat.{max u v}) where
  /-- The sheaf `\underline H^q(ℱ)` for each `q`. -/
  cohomologySheaf : ℕ → Sheaf J AddCommGrpCat.{max u v}
  /-- Sectionwise identification of `\underline H^q(ℱ)` with object cohomology. -/
  cohomologySheafSectionsIso :
    ∀ (q : ℕ) (U : C),
      (cohomologySheaf q).1.obj (op U) ≅
        Sheaf.H' ℱ q U
  /-- The chosen cohomological spectral sequence. -/
  spectralSequence : E₂CohomologicalSpectralSequence AddCommGrpCat.{max u v}
  /-- The `E₂`-page is the Čech cohomology of `K` with coefficients in
  `\underline H^q(ℱ)`. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
        hypercoveringCechCohomology K (cohomologySheaf q) p
  /-- The chosen abutment groups. -/
  abutment : ℕ → AddCommGrpCat.{max u v}
  /-- The abutment identifies with `H^n(X, ℱ)`. -/
  abutmentIso :
    ∀ n : ℕ,
      abutment n ≅
        Sheaf.H' ℱ n X

/-- Lemma 25.5.3 (1): for a hypercovering `K` of an object `X` and an abelian sheaf `ℱ`,
the derived comparison map `s(ℱ(K)) ⟶ RΓ(X, ℱ)` induces natural transformations
`\check H^i(K, -) ⟶ H^i(X, -)` in the coefficient sheaf. -/
@[stacks 01GY]
theorem hypercoveringCechComparison_exists {X : C}
    (K : @Hypercovering C _ J X) (i : ℕ) :
    Nonempty (HypercoveringCechComparison K i) := sorry

/-- Lemma 25.5.3 (2): for a hypercovering `K` of an object `X` and an abelian sheaf `ℱ`,
there is a spectral sequence with
`E₂^{p,q} = \check H^p(K, \underline H^q(ℱ))` converging to `H^{p+q}(X, ℱ)`. The structure
records the `E₂`-page, abutment, and the sectionwise meaning of `\underline H^q(ℱ)`. -/
@[stacks 01GY]
theorem hypercoveringCohomologySpectralSequence_exists {X : C}
    (K : @Hypercovering C _ J X)
    (ℱ : Sheaf J AddCommGrpCat.{max u v}) :
    Nonempty (HypercoveringCohomologySpectralSequence K ℱ) := sorry

end CategoryTheory
