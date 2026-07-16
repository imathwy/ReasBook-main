import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

-- Semantic search note: `lean_leansearch` recalled mathlib's sheaf-cohomology owner
-- `CategoryTheory.Sheaf.H` together with the generic double-complex/spectral-sequence APIs. For
-- this item, the source-faithful owner is still the Chapter 25 presheaf-level source object
-- `(presheafToSheaf J AddCommGrpCat).obj (𝒢 ⋙ AddCommGrpCat.free)`, whose `Ext` functors realize
-- `H^i(𝒢, -)` in the same way Chapter 20 realizes objectwise sheaf cohomology.

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [Limits.HasEqualizers C] [Limits.HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max w v})]
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

/-- The source sheaf `( \mathbf Z \mathcal G )^\#` whose `Ext` groups compute the cohomology of
the presheaf `𝒢` with coefficients in abelian sheaves. -/
abbrev hypercoveringOfCohomologySource
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) :
    Sheaf J AddCommGrpCat.{max w v} :=
  (presheafToSheaf J AddCommGrpCat.{max w v}).obj (𝒢 ⋙ AddCommGrpCat.free)

/-- The coefficient-side cohomology functor `\mathcal F \mapsto H^i(\mathcal G, \mathcal F)`,
formalized as `Ext^i((\mathbf Z \mathcal G)^\#, \mathcal F)`. -/
abbrev hypercoveringOfSheafCohomology
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w} :=
  Abelian.extFunctorObj (hypercoveringOfCohomologySource 𝒢 :
    Sheaf J AddCommGrpCat.{max w v}) i

/-- A chosen comparison from the Čech cohomology of a hypercovering to the corresponding
cohomology of the underlying presheaf, together with the coefficient-functoriality data of the
resulting natural transformation. -/
structure HypercoveringOfCechComparison
    (K : HypercoveringOf J 𝒢) (i : ℕ) where
  /-- The coefficient-change map on Čech cohomology groups. -/
  cechMapApp :
    ∀ {ℱ 𝒜 : Sheaf J AddCommGrpCat.{max w v}},
      (ℱ ⟶ 𝒜) →
      (hypercoveringOfCechCohomology K ℱ i ⟶
        hypercoveringOfCechCohomology K 𝒜 i)
  /-- The comparison map on the degree-`i` group for a fixed coefficient sheaf. -/
  app :
    ∀ (ℱ : Sheaf J AddCommGrpCat.{max w v}),
      hypercoveringOfCechCohomology K ℱ i ⟶
        (hypercoveringOfSheafCohomology 𝒢 i).obj ℱ
  /-- Naturality of the comparison with respect to coefficient morphisms. -/
  naturality :
    ∀ {ℱ 𝒜 : Sheaf J AddCommGrpCat.{max w v}} (φ : ℱ ⟶ 𝒜),
      app ℱ ≫ (hypercoveringOfSheafCohomology 𝒢 i).map φ =
        cechMapApp φ ≫ app 𝒜

/-- A chosen `E_2`-spectral sequence computing the cohomology of `𝒢` from a hypercovering `K`.
The explicit `E_2^{p,q} = \check H^p(K, \underline H^q(\mathcal F))` identification is recorded
at the source level by the `pageTwo` family and the isomorphisms `pageTwoIso`. -/
structure HypercoveringOfCohomologySpectralSequence
    (K : HypercoveringOf J 𝒢)
    (ℱ : Sheaf J AddCommGrpCat.{max w v}) where
  /-- The chosen cohomological spectral sequence. -/
  spectralSequence : E₂CohomologicalSpectralSequence AddCommGrpCat.{max u v w}
  /-- The chosen `E_2`-page terms. -/
  pageTwo : ℕ → ℕ → AddCommGrpCat.{max u v w}
  /-- The `E_2`-page of the chosen spectral sequence. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅ pageTwo p q
  /-- The chosen abutment groups. -/
  abutment : ℕ → AddCommGrpCat.{max u v w}
  /-- The abutment identifies with the cohomology of `𝒢` with coefficients in `ℱ`. -/
  abutmentIso :
    ∀ n : ℕ,
      abutment n ≅
        (hypercoveringOfSheafCohomology 𝒢 n).obj ℱ

/-- Lemma 25.6.4 (1): for a hypercovering `K` of a presheaf `𝒢` and an abelian sheaf
`\mathcal F`, there is a canonical comparison from Čech cohomology on `K` to the cohomology of
`𝒢`, natural in the coefficient sheaf. This source-facing statement packages the induced natural
transformation `\check H^i(K, -) \to H^i(\mathcal G, -)`; the underlying morphism
`s(\mathcal F(K)) \to R\Gamma(\mathcal G, \mathcal F)` in `D^+(\mathrm{Ab})` is its derived
origin. -/
@[stacks 09VX]
theorem hypercoveringOfCechComparison_exists
    (K : HypercoveringOf J 𝒢) (i : ℕ) :
    Nonempty (HypercoveringOfCechComparison K i) := sorry

/-- Lemma 25.6.4 (2): for a hypercovering `K` of a presheaf `𝒢` and an abelian sheaf
`\mathcal F`, there is a cohomological spectral sequence with `E_2`-page
`\check H^p(K, \underline H^q(\mathcal F))` converging to `H^{p + q}(\mathcal G, \mathcal F)`.
The chosen owner below records the spectral sequence together with its `E_2`-page and abutment
identifications. -/
@[stacks 09VX]
theorem hypercoveringOfCohomologySpectralSequence_exists
    (K : HypercoveringOf J 𝒢)
    (ℱ : Sheaf J AddCommGrpCat.{max w v}) :
    Nonempty
      (HypercoveringOfCohomologySpectralSequence K ℱ) := sorry

end CategoryTheory
