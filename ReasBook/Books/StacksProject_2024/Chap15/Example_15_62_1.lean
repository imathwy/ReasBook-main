import Mathlib
import Mathlib.Algebra.Homology.CochainComplexOpposite
import stacks_project.Chap12.Definition_12_14_1
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap15.Definition_15_59_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex
open scoped DerivedTensorProduct

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksProject

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat.{u} R)] [WellPowered.{0} (ModuleCat.{u} R)]

local notation "ModR" => ModuleCat R
local notation "single₀" => DerivedCategory.singleFunctor ModR (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor ModR

/-- Internal cochain view of a chain complex, obtained from the Chapter `12`
owner `ChainComplex.chainToCochain`. -/
private abbrev cochainView
    (K : ChainComplex ModR ℤ) : CochainComplex ModR ℤ :=
  (ChainComplex.chainToCochain ModR).obj K

/-- The abutment object `H_n(K_• \otimes_R^{\mathbf L} M)`, written through the standard
chain-to-cochain transport into the derived category. -/
private abbrev derivedTensorHomologyAbutment
    (K : ChainComplex ModR ℤ) (M : ModR) (n : ℤ) : ModR :=
  (H (-n)).obj
    (DerivedCategory.Q.obj (cochainView K) ⊗[R]^L
      (single₀).obj M)

/-- The `E₂`-term `Tor_j^R(H_i(K_•), M)` in `ModuleCat R`. -/
private abbrev firstTorPageTwo
    (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) : ModR :=
  (((Tor ModR j).obj (K.homology i)).obj M)

/-- The homological `(i,j)` entry of the second page, read from the cohomological spectral
sequence by the sign convention of Example `15.62.1`. -/
private abbrev firstTorPageTwoObj
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) : ModR :=
  (E.page 2).X (-(j : ℤ), -i)

/-- The `E₁`-term `Tor_j^R(K_i, M)` in `ModuleCat R`. -/
private abbrev secondTorPageOne
    (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) : ModR :=
  (((Tor ModR j).obj (K.X i)).obj M)

/-- The homological `(i,j)` entry of the first page, again read via the sign convention of
Example `15.62.1`. -/
private abbrev secondTorPageOneObj
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) : ModR :=
  (E.page 1).X (-i, -(j : ℤ))

/-- The morphism on `Tor_j^R(-, M)` induced by the differential `K_i ⟶ K_{i - 1}`. -/
private abbrev secondTorPageOneMap
    (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) :
    secondTorPageOne K M i j ⟶ secondTorPageOne K M (i - 1) j :=
  (((Tor ModR j).map (K.d i (i - 1))).app M)

/-- Internal bridge: a cohomological spectral sequence converges to
`H_*(K_• \otimes_R^{\mathbf L} M)` if it is associated to a filtered complex whose reindexed
cohomology objects identify with the derived tensor-product homology abutment and which satisfies
the Chapter `12` convergence owner. -/
private def convergesToDerivedTensorHomology
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  ∃ (F : FilteredComplex ModR) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology (-n) ≅ derivedTensorHomologyAbutment K M n)

/-
Domain-style sampling for Example `15.62.1`.
- primary domain: cohomological spectral sequences in `ModuleCat R`, reindexed homologically, with
  convergence to the homology of the derived tensor product;
- sampled owner API:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.FilteredComplex.underlying`,
  `ChainComplex.chainToCochain`,
  `CategoryTheory.CommSq`,
  `CategoryTheory.DerivedCategory.homologyFunctor`;
- best owner abstraction: a cohomological spectral sequence `E` together with an associated
  filtered complex `F : FilteredComplex (ModuleCat R)` satisfying the canonical owner predicate
  `F.convergesToCohomology E`;
- primitive data: `E : CohomologicalSpectralSequence (ModuleCat R) 0`, the filtered complex
  witness `F : FilteredComplex (ModuleCat R)` in the convergence clause, and the canonical
  lower-support condition `∃ n : ℤ, ((chainToCochain ModR).obj K).IsStrictlyLE n` on the cochain
  view of the chain complex `K`, expressing that `K` is bounded below;
- derived API: the homological reindexing of the pages, the `Tor`-page identifications, the
  `d₁` comparison squares, the derived-category abutment object
  `derivedTensorHomologyAbutment`, and the shared internal bridge
  `convergesToDerivedTensorHomology`;
- source/core/bridge triage:
  `source-facing`: `IsFirstTorSpectralSequence` and `IsSecondTorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`, `FilteredComplex.convergesToCohomology`,
    `FilteredComplex.underlying`,
    `DerivedCategory.homologyFunctor`, `ChainComplex.chainToCochain`, `CommSq`;
  `bridge/view`: the internal chain-to-cochain transport via
    `ChainComplex.chainToCochain`, the shared abutment/page abbreviations, and the internal
    convergence clause `convergesToDerivedTensorHomology`.
-/

/-- The first spectral sequence of Example `15.62.1`, read in homological indexing: its `E₂`-page
is `Tor_j^R(H_i(K_•), M)`, and it converges to `H_*(K_• \otimes_R^{\mathbf L} M)`. -/
def IsFirstTorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  (∀ (i : ℤ) (j : ℕ),
      Nonempty (firstTorPageTwoObj E i j ≅ firstTorPageTwo K M i j)) ∧
    convergesToDerivedTensorHomology E K M

/-- The second spectral sequence of Example `15.62.1`, read in homological indexing: its
`E₁`-page is `Tor_j^R(K_i, M)`, the `d₁` differential is induced by `K_i ⟶ K_{i - 1}`, and it
converges to `H_*(K_• \otimes_R^{\mathbf L} M)`. -/
def IsSecondTorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  (∃ pageOneIso :
      ∀ (i : ℤ) (j : ℕ),
        secondTorPageOneObj E i j ≅ secondTorPageOne K M i j,
      ∀ (i : ℤ) (j : ℕ),
        CommSq ((E.page 1).d (-i, -(j : ℤ)) (-(i - 1), -(j : ℤ))) (pageOneIso i j).hom
          (pageOneIso (i - 1) j).hom (secondTorPageOneMap K M i j)) ∧
    convergesToDerivedTensorHomology E K M

-- Proof sketch: choose a free resolution of `M`, convert the tensor double chain complex
-- `K_• ⊗_R P_•` to the cohomological double-complex formalism of Chapter `12`, apply the two
-- spectral sequences of Lemma `12.25.3`, identify the resulting `E₂`- and `E₁`-pages with the
-- stated `Tor` groups, and then identify the total cohomology with the homology of
-- `K_• \otimes_R^{\mathbf L} M` via the canonical derived tensor product of Chapter `15`.
/-- Example 15.62.1: if `K_•` is a chain complex of `R`-modules with `K_n = 0` for `n \ll 0` and
`M` is an `R`-module, then there exist two spectral sequences converging to
`H_*(K_• \otimes_R^{\mathbf L} M)`: a first one with `E₂`-page
`Tor_j^R(H_i(K_•), M)` and a second one with `E₁`-page `Tor_j^R(K_i, M)`. -/
theorem exists_tor_spectral_sequences_of_boundedBelow_chainComplex
    (K : ChainComplex ModR ℤ)
    (hK : ∃ n : ℤ, ((chainToCochain ModR).obj K).IsStrictlyLE n)
    (M : ModR) :
    ∃ E₂ E₁ : CohomologicalSpectralSequence ModR 0,
      IsFirstTorSpectralSequence E₂ K M ∧
        IsSecondTorSpectralSequence E₁ K M := sorry

end

end StacksProject
