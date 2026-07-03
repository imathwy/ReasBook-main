import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap15.Lemma_15_60_1

-- Declarations for this item will be appended below by the statement pipeline.

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
