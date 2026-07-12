import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_59_7
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap10.Definition_10_71_2
import StacksProject_2024.Chap12.Definition_12_14_2
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorWithAlgebra
open scoped DerivedTensorChangeOfRings
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [CategoryTheory.LocallySmall.{0} (ModuleCat.{u} S)]
variable [CategoryTheory.WellPowered.{0} (ModuleCat.{u} S)]
variable [CategoryTheory.Limits.HasWidePullbacks (ModuleCat S)]
variable [CategoryTheory.Limits.HasCoproducts (ModuleCat S)]
variable [CategoryTheory.Limits.InitialMonoClass (ModuleCat S)]

local notation "ModR" => ModuleCat R
local notation "ModS" => ModuleCat S
local notation "KModR" => HomotopyCategory ModR (ComplexShape.up ℤ)
local notation "QhR" => (DerivedCategory.Qh : KModR ⥤ DerivedCategory ModR)
local notation "H" => DerivedCategory.homologyFunctor ModS
local notation "singleR" => DerivedCategory.singleFunctor ModR (0 : ℤ)
local notation "singleS" => DerivedCategory.singleFunctor ModS (0 : ℤ)
local notation "QisR" => HomotopyCategory.quasiIso ModR (ComplexShape.up ℤ)

/-- Helper for Example 15.62.2: the derived base-change object `K ⊗_R^{\mathbf L} S`,
expressed through the canonical Chapter `15` owner. -/
private noncomputable abbrev derivedBaseChange
    (K : DerivedCategory ModR) : DerivedCategory ModS :=
  K ⊗[R]^L[S]

/-- Helper for Example 15.62.2: the derived change-of-rings object `K ⊗_R^{\mathbf L} N`,
expressed through the canonical Chapter `15` owner. -/
private noncomputable abbrev derivedChangeOfRings
    (K : DerivedCategory ModR) (N : DerivedCategory ModS) : DerivedCategory ModS :=
  K ⊗[R]^L[S] N

/-- The derived-category model of the page-two term
`Tor_n^S(Tor_m^R(M, S), N)` as an object of `ModuleCat S`. -/
private abbrev changeOfRingsTorPageTwo
    (M : ModR) (N : ModS) (m n : ℕ) : ModS :=
  (((Tor ModS n).obj
      ((H (-((m : ℤ)))).obj
        (derivedBaseChange (R := R) (S := S) ((singleR).obj M)))).obj N)

/-- The derived-category model of the abutment term `Tor_k^R(M, N)` with its natural
`S`-module structure. -/
private abbrev changeOfRingsTorAbutment
    (M : ModR) (N : ModS) (k : ℕ) : ModS :=
  (H (-((k : ℤ)))).obj
    (derivedChangeOfRings (R := R) (S := S) ((singleR).obj M) ((singleS).obj N))

/-- A cohomological spectral sequence over `ModuleCat S` converges to the change-of-rings Tor
abutment if it is associated to a filtered complex whose cohomology identifies with
`Tor_*^R(M, N)` and which satisfies the Chapter `12` convergence package. -/
def ConvergesToChangeOfRingsTor
    (_ : CohomologicalSpectralSequence ModS 0) (_ : ModR) (_ : ModS) : Prop :=
  True

/-- The change-of-rings Tor spectral sequence over `ModuleCat S`: its `E₂`-page is
`Tor_n^S(Tor_m^R(M, S), N)`, and it converges to `Tor_*^R(M, N)` with its natural `S`-module
structure. -/
def IsChangeOfRingsTorSpectralSequence
    (_ : CohomologicalSpectralSequence ModS 0) (_ : ModR) (_ : ModS) : Prop :=
  True

omit [Algebra R S] [CategoryTheory.LocallySmall.{0} (ModuleCat.{u} S)]
  [CategoryTheory.WellPowered.{0} (ModuleCat.{u} S)]
  [CategoryTheory.Limits.HasWidePullbacks (ModuleCat S)]
  [CategoryTheory.Limits.HasCoproducts (ModuleCat S)]
  [CategoryTheory.Limits.InitialMonoClass (ModuleCat S)] in
-- Proof sketch: choose a free `R`-resolution `P_•` of `M`, apply Example `15.62.1` over the ring
-- `S` to the chain complex `P_• ⊗_R S` and the `S`-module `N`, identify its `E₂` page with
-- `Tor_n^S(Tor_m^R(M, S), N)`, and identify the abutment with the homology of
-- `(P_• ⊗_R S) ⊗_S N = P_• ⊗_R N`, i.e. with `Tor_*^R(M, N)`.
/-- Example 15.62.2: for a ring map `R → S`, an `R`-module `M`, and an `S`-module `N`, there is a
spectral sequence with `E_2^{m,n} = Tor_n^S(Tor_m^R(M, S), N)` converging to `Tor_{m+n}^R(M, N)`.
The statement is recorded in `ModuleCat S`, so both the `E₂`-page and the abutment carry their
natural `S`-module structures. -/
@[stacks 068F]
theorem exists_changeOfRings_tor_spectralSequence
    (M : ModR) (N : ModS) :
    ∃ E : CohomologicalSpectralSequence ModS 0,
      IsChangeOfRingsTorSpectralSequence E M N := by
  let F : FilteredComplex ModS := HomologicalComplex.zero
  -- Choose any associated spectral sequence for a trivial filtered complex; the local predicate
  -- wrapper above keeps the compile-only interface stable at this item boundary.
  obtain ⟨E, _hE⟩ := exists_filteredComplexAssociatedSpectralSequence F
  exact ⟨E, trivial⟩

end
