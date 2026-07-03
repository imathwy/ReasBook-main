import Mathlib
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.CategoryTheory.Abelian.Projective.Extend

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_15_62_1 (from Chap15) -/
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

/-! ### Example_15_62_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorChangeOfRings DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [CategoryTheory.LocallySmall (ModuleCat S)] [CategoryTheory.WellPowered (ModuleCat S)]
variable [CategoryTheory.Limits.HasWidePullbacks (ModuleCat S)]
variable [CategoryTheory.Limits.HasCoproducts (ModuleCat S)]
variable [CategoryTheory.Limits.InitialMonoClass (ModuleCat S)]

local notation "ModR" => ModuleCat R
local notation "ModS" => ModuleCat S
local notation "H" => DerivedCategory.homologyFunctor ModS
local notation "singleR" => DerivedCategory.singleFunctor ModR (0 : ℤ)
local notation "singleS" => DerivedCategory.singleFunctor ModS (0 : ℤ)

/- 
Domain-style sampling for Example `15.62.2`.
- primary domain: cohomological spectral sequences in `ModuleCat S` encoding the change-of-rings
  Tor spectral sequence;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.DerivedCategory.homologyFunctor`;
- best owner abstraction: a cohomological spectral sequence `E` together with the chapter owner
  predicate `F.convergesToCohomology E` for an associated filtered complex `F`;
- primitive data: the spectral sequence `E` and the auxiliary filtered-complex witness occurring in
  the convergence clause;
- derived API: the homological reindexing of the page-two terms and the abutment identifications;
- source/core/bridge triage:
  `source-facing`: `ConvergesToChangeOfRingsTor` and `IsChangeOfRingsTorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`, `IsAssociatedToFilteredComplex`,
    `FilteredComplex.convergesToCohomology`, `FilteredComplex.underlying`,
    `DerivedCategory.homologyFunctor`;
  `bridge/view`: `changeOfRingsTorPageTwo` and `changeOfRingsTorAbutment`.
-/

/-- The derived-category model of the page-two term
`Tor_n^S(Tor_m^R(M, S), N)` as an object of `ModuleCat S`. -/
private abbrev changeOfRingsTorPageTwo
    (M : ModR) (N : ModS) (m n : ℕ) : ModS :=
  (((Tor ModS n).obj
      ((H (-((m : ℤ)))).obj
        ((singleR).obj M ⊗[R]^L[S]))).obj N)

/-- The derived-category model of the abutment term `Tor_k^R(M, N)` with its natural
`S`-module structure. -/
private abbrev changeOfRingsTorAbutment
    (M : ModR) (N : ModS) (k : ℕ) : ModS :=
  (H (-((k : ℤ)))).obj (((singleR).obj M) ⊗[R]^L[S] ((singleS).obj N))

/-- A cohomological spectral sequence over `ModuleCat S` converges to the change-of-rings Tor
abutment if it is associated to a filtered complex whose cohomology identifies with
`Tor_*^R(M, N)` and which satisfies the Chapter `12` convergence package. -/
def ConvergesToChangeOfRingsTor
    (E : CohomologicalSpectralSequence ModS 0) (M : ModR) (N : ModS) : Prop :=
  ∃ (F : FilteredComplex ModS) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ k : ℕ,
        Nonempty (F.underlying.homology (-((k : ℤ))) ≅ changeOfRingsTorAbutment M N k)

/-- The change-of-rings Tor spectral sequence over `ModuleCat S`: its `E₂`-page is
`Tor_n^S(Tor_m^R(M, S), N)`, and it converges to `Tor_*^R(M, N)` with its natural `S`-module
structure. -/
def IsChangeOfRingsTorSpectralSequence
    (E : CohomologicalSpectralSequence ModS 0) (M : ModR) (N : ModS) : Prop :=
  (∀ m n : ℕ,
      Nonempty ((E.page 2).X (-((n : ℤ)), -((m : ℤ))) ≅ changeOfRingsTorPageTwo M N m n)) ∧
    ConvergesToChangeOfRingsTor E M N

-- Proof sketch: choose a free `R`-resolution `P_•` of `M`, apply Example `15.62.1` over the ring
-- `S` to the chain complex `P_• ⊗_R S` and the `S`-module `N`, identify its `E₂` page with
-- `Tor_n^S(Tor_m^R(M, S), N)`, and identify the abutment with the homology of
-- `(P_• ⊗_R S) ⊗_S N = P_• ⊗_R N`, i.e. with `Tor_*^R(M, N)`.
/-- Example 15.62.2: for a ring map `R → S`, an `R`-module `M`, and an `S`-module `N`, there is a
spectral sequence with `E_2^{m,n} = Tor_n^S(Tor_m^R(M, S), N)` converging to `Tor_{m+n}^R(M, N)`.
The statement is recorded in `ModuleCat S`, so both the `E₂`-page and the abutment carry their
natural `S`-module structures. -/
theorem exists_changeOfRings_tor_spectralSequence
    (M : ModR) (N : ModS) :
    ∃ E : CohomologicalSpectralSequence ModS 0,
      IsChangeOfRingsTorSpectralSequence E M N := sorry

end

/-! ### Example_15_62_3 (from Chap15) -/
open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable (A : Type u) [CommRing A] {B : Type u} [CommRing B]
variable [Algebra A B]

section

variable {A' : Type u} [CommRing A'] [Algebra A A']

local notation "ModB" => ModuleCat B
local notation "ModA'" => ModuleCat A'
local notation "BTensorAprime" => TensorProduct A B A'
local notation "ModBTensorAprime" => ModuleCat BTensorAprime
local notation "singleB" => DerivedCategory.singleFunctor ModB (0 : ℤ)
local notation "HAprime" => DerivedCategory.homologyFunctor ModA'
variable [LocallySmall.{0} (ModuleCat (TensorProduct A B A'))]
variable [WellPowered.{0} (ModuleCat (TensorProduct A B A'))]
variable [CategoryTheory.Limits.HasWidePullbacks (ModuleCat (TensorProduct A B A'))]
variable [CategoryTheory.Limits.HasCoproducts (ModuleCat (TensorProduct A B A'))]
variable [CategoryTheory.Limits.InitialMonoClass (ModuleCat (TensorProduct A B A'))]

/- 
Domain-style sampling for Example `15.62.3`.
- primary domain: cohomological spectral sequences in `ModuleCat B'` encoding the Tor
  base-change spectral sequence with its natural post-base-change module structure;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.Tor`;
- best owner abstraction: for the tensor-product ring `B' = B ⊗[A] A'`, a cohomological spectral
  sequence `E : CohomologicalSpectralSequence (ModuleCat (TensorProduct A B A')) 0` together with
  the chapter owner predicate `F.convergesToCohomology E` for an associated filtered complex
  `F : FilteredComplex (ModuleCat (TensorProduct A B A'))`;
- primitive data: the spectral sequence `E` and the filtered-complex witness `F` in the
  convergence clause;
- derived API: the textbook `A'`-module `E₂`-page objects
  `Tor_i^A(Tor_j^B(M, N), A')` and the base-changed Tor abutment in `ModuleCat B'`;
- source/core/bridge triage:
  `source-facing`: `ConvergesToTorBaseChange`, `IsTorBaseChangeSpectralSequence`, and the
    textbook page-two projection `IsTorBaseChangeSpectralSequence.pageTwoOverAprimeIso`;
  `core/canonical`: `CohomologicalSpectralSequence`, `IsAssociatedToFilteredComplex`,
    `FilteredComplex.convergesToCohomology`, `DerivedCategory.homologyFunctor`, `Tor`, 
    `derivedTensorWithAlgebra`, and `ModuleCat.extendScalars`;
  `bridge/view`: the restriction-of-scalars view along `A' → B'` used to place the page-two term
    of a spectral sequence in `ModuleCat B'` directly in the textbook `A'`-module form, together
    with the internal convergence clause below.
-/

/-- The textbook page-two term `Tor_i^A(Tor_j^B(M, N), A')`, viewed in `ModuleCat A'`. -/
private abbrev torBaseChangePageTwo
    (M N : ModB) (i j : ℕ) : ModA' :=
  (HAprime (-(i : ℤ))).obj
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        ((singleB).obj (((Tor ModB j).obj M).obj N))) ⊗[A]^L[A'])

/-- The abutment object `Tor_n^{B'}(M', N')` with its canonical `B'`-module structure. -/
private abbrev torBaseChangeAbutment
    (M N : ModB) (n : ℕ) : ModBTensorAprime :=
  (((Tor ModBTensorAprime n).obj
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] BTensorAprime)).obj M)).obj
    ((ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] BTensorAprime)).obj N))

/-- A cohomological spectral sequence converges to the change-of-rings Tor groups if it is
associated to a filtered complex whose cohomology objects are isomorphic in `ModuleCat B'` to
`Tor_*^{B'}(M', N')` and which satisfies the Chapter `12` convergence package. -/
def ConvergesToTorBaseChange
    (E : CohomologicalSpectralSequence ModBTensorAprime 0)
    (M N : ModB) : Prop :=
  ∃ (F : FilteredComplex ModBTensorAprime) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℕ,
        Nonempty (F.underlying.homology (-(n : ℤ)) ≅ torBaseChangeAbutment A M N n)

/-- The change-of-rings spectral sequence for Tor over `ModuleCat B'`: after restricting scalars
along `A' → B ⊗[A] A'`, its `E₂`-page is the textbook `A'`-module term
`Tor_i^A(Tor_j^B(M, N), A')`; its abutment is `Tor_{i + j}^{B'}(M', N')` with its natural
`B'`-module structure. -/
def IsTorBaseChangeSpectralSequence
    (E : CohomologicalSpectralSequence ModBTensorAprime 0)
    (M N : ModB) : Prop :=
  (∀ i j : ℕ,
      Nonempty
        ((ModuleCat.restrictScalars (algebraMap A' BTensorAprime)).obj
            ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅ torBaseChangePageTwo A M N i j)) ∧
    ConvergesToTorBaseChange A E M N

/-- The source-facing `E₂`-page identification in Example `15.62.3`: after restricting scalars
along `A' → B ⊗[A] A'`, the page-two term is `Tor_i^A(Tor_j^B(M, N), A')`. -/
theorem IsTorBaseChangeSpectralSequence.pageTwoOverAprimeIso
    {E : CohomologicalSpectralSequence ModBTensorAprime 0}
    {M N : ModB}
    (hE : IsTorBaseChangeSpectralSequence A E M N)
    (i j : ℕ) :
    Nonempty
      ((ModuleCat.restrictScalars (algebraMap A' BTensorAprime)).obj
          ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅
        torBaseChangePageTwo A M N i j) := by
  exact hE.1 i j

/-- The abutment half of Example `15.62.3`: a Tor base-change spectral sequence converges to
`Tor_*^{B ⊗[A] A'}(M', N')` through an associated filtered complex satisfying the Chapter `12`
convergence owner. -/
theorem IsTorBaseChangeSpectralSequence.convergesToTorBaseChange
    {E : CohomologicalSpectralSequence ModBTensorAprime 0}
    {M N : ModB}
    (hE : IsTorBaseChangeSpectralSequence A E M N) :
    ConvergesToTorBaseChange A E M N := by
  exact hE.2

-- Proof sketch: choose a free `B`-resolution `F_• → M`; because `B` is flat over `A` and `M` is
-- `A`-flat, the terms of `F_•` are `A`-flat. Tensor with `N`, then apply derived scalar extension
-- from `B` to `B' = B ⊗[A] A'`. The resulting filtered complex lives in `ModuleCat B'`; after
-- restricting the `E₂` page along `A' → B'`, its page-two terms identify with
-- `Tor_i^A(Tor_j^B(M, N), A')`, and its abutment is `Tor_{i+j}^{B'}(M', N')`.
/-- Example 15.62.3: let `A → B` and `A → A'` be ring maps, set `B' = B ⊗[A] A'`, and let `M`
and `N` be `B`-modules. If `B` is flat over `A` and `M` and `N` are flat over `A`, then there is
a spectral sequence with `E₂`-page `Tor_i^A(Tor_j^B(M, N), A')` converging to
`Tor_{i+j}^{B'}(M', N')`. In this file the source-facing `E₂`-page formula is stated directly as
an `A'`-module identification by restricting scalars on the spectral-sequence terms, while the
abutment keeps its natural `B'`-module structure. -/
theorem exists_tor_baseChange_spectralSequence
    (A' : Type u) [CommRing A'] [Algebra A A']
    [LocallySmall.{0} (ModuleCat (TensorProduct A B A'))]
    [WellPowered.{0} (ModuleCat (TensorProduct A B A'))]
    [CategoryTheory.Limits.HasWidePullbacks (ModuleCat (TensorProduct A B A'))]
    [CategoryTheory.Limits.HasCoproducts (ModuleCat (TensorProduct A B A'))]
    [CategoryTheory.Limits.InitialMonoClass (ModuleCat (TensorProduct A B A'))]
    (M N : ModB)
    (hBflat : Module.Flat A B)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (hNflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj N)) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat (TensorProduct A B A')) 0,
      IsTorBaseChangeSpectralSequence A E M N := sorry

end

end

/-! ### Example_15_62_4 (from Chap15) -/
open CategoryTheory
open scoped DerivedTensorProduct

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksProject

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat.{u} R)]
variable [WellPowered.{0} (ModuleCat.{u} R)]

/-
Domain-style sampling for Example `15.62.4`.
- primary domain: cohomological spectral sequences in the bounded-above derived category of
  `R`-modules and their convergence to derived tensor-product cohomology;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.firstDoubleComplexFilteredComplex`,
  `CategoryTheory.secondDoubleComplexFilteredComplex`,
  `CategoryTheory.derivedTensorProduct`,
  `CategoryTheory.DerivedCategory.homologyFunctor`;
- best owner abstraction: a cohomological spectral sequence `E` with source-facing Prop-valued
  predicates recording the right or left `E₂`-page formula together with the Chapter `12`
  convergence owner `F.convergesToCohomology E` for some associated filtered complex `F`;
- primitive data: `E : CohomologicalSpectralSequence ModR 0` and the existential filtered-complex
  witness `F : FilteredComplex ModR` occurring in the convergence clause;
- derived API: the right and left `E₂`-page identifications and the common abutment
  identification with `H^*(K ⊗[R]^L L)`;
- source/core/bridge triage:
  `source-facing`: `IsRightCohomologyDerivedTensorSpectralSequence` and
    `IsLeftCohomologyDerivedTensorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`, `FilteredComplex.convergesToCohomology`,
    `firstDoubleComplexFilteredComplex`, `secondDoubleComplexFilteredComplex`,
    `DerivedCategory.homologyFunctor`, and `derivedTensorProduct`;
  `bridge/view`: the local page-two and abutment abbreviations together with the shared internal
    convergence clause used to state the source-facing predicates concisely.
-/
local notation "ModR" => ModuleCat R
local notation "DModMinus" => boundedAboveDerivedCategory ModR
local notation "H" => DerivedCategory.homologyFunctor ModR
local notation "single₀" => DerivedCategory.singleFunctor ModR (0 : ℤ)

/-- The abutment object `H^n(K^• \otimes_R^{\mathbf L} L^•)`. -/
private abbrev derivedTensorCohomologyAbutment
    (K L : DModMinus) (n : ℤ) : ModR :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The right-hand `E₂`-term `H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))`. -/
private abbrev rightDerivedTensorPageTwo
    (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj (K.obj ⊗[R]^L ((single₀).obj ((H q).obj L.obj)))

/-- The left-hand `E₂`-term `H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`. -/
private abbrev leftDerivedTensorPageTwo
    (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj (((single₀).obj ((H q).obj K.obj)) ⊗[R]^L L.obj)

/-- Internal bridge: a cohomological spectral sequence converges to
`H^*(K^• \otimes_R^{\mathbf L} L^•)` if it is associated to a filtered complex whose cohomology
identifies with that of the derived tensor product and which satisfies the Chapter `12`
convergence owner. -/
private def convergesToDerivedTensorCohomology
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  ∃ (F : FilteredComplex ModR) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ derivedTensorCohomologyAbutment K L n)

/-- The first spectral sequence of Example `15.62.4`: its `E₂`-page is
`H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))`, and it converges to
`H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`. -/
def IsRightCohomologyDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ rightDerivedTensorPageTwo K L p q)) ∧
    convergesToDerivedTensorCohomology E K L

/-- The second spectral sequence of Example `15.62.4`: its `E₂`-page is
`H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`, and it converges to
`H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`. -/
def IsLeftCohomologyDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ leftDerivedTensorPageTwo K L p q)) ∧
    convergesToDerivedTensorCohomology E K L

-- Proof sketch: replace `K^•` and `L^•` by bounded-above complexes of projective `R`-modules and
-- apply the two spectral sequences of Homology, Section `12.25` to the double complex
-- `Tot(K^• ⊗_R L^•)`. The projective replacements compute the same derived tensor product, so the
-- two `E₂`-pages identify with `H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))` and
-- `H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)` respectively, and both abut to
-- `H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`.
/-- Example 15.62.4: for objects `K^•` and `L^•` of `D^{-}(R)`, there are two cohomological
spectral sequences converging to `H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`, one with
`E_2^{p,q} = H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))` and the other with
`E_2^{p,q} = H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`. Because both are cohomological spectral
sequences, their page-two differentials have bidegree `(2, -1)`, i.e.
`d_2^{p,q} : E_2^{p,q} → E_2^{p+2,q-1}`. -/
theorem exists_derivedTensor_cohomology_spectralSequences
    (K L : DModMinus) :
    ∃ E_right E_left : CohomologicalSpectralSequence ModR 0,
      IsRightCohomologyDerivedTensorSpectralSequence E_right K L ∧
        IsLeftCohomologyDerivedTensorSpectralSequence E_left K L := sorry

end

end StacksProject
