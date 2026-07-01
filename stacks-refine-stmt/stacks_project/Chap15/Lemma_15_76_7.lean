import Mathlib
import stacks_project.Chap15.Lemma_15_60_1
import stacks_project.Chap15.Lemma_15_75_2
import stacks_project.Chap15.Lemma_15_76_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxAway[" f "]" => CochainComplex (ModuleCat (Localization.Away f)) ℤ
local notation "FiniteFreeClassAway[" f "]" =>
  (fun M : ModuleCat (Localization.Away f) ↦
    Module.Free (Localization.Away f) M ∧ Module.Finite (Localization.Away f) M)
local notation "BoundedFiniteFreeCpxAway[" f "]" =>
  CochainComplex.MinusWithTermsIn FiniteFreeClassAway[f]

/- Domain-style sampling for Lemma 15.76.7:
- primary domain: perfect derived complexes over a commutative ring, measured by residue-field
  fibers at a prime and represented after shrinking by finite-free localization complexes;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: `K.IsPerfect` remains the source-facing owner, while the explicit
  localized finite-free representative in part `(2)` should reuse the bounded-above owner
  `CochainComplex.MinusWithTermsIn`; the lower support bound is separate source-facing data, and
  upper boundedness stays inside that owner;
- primitive vs. derived:
  primitive data are the prime `p`, the perfect object `K`, the rank function `d`, and the
  localized owner complex;
  derived API is the finite-support residue-field homology conclusion in part `(1)` and the
  termwise rank identifications plus derived isomorphism in part `(2)`;
- source/core/bridge triage:
  `source-facing`: the two numbered clauses of Lemma `15.76.7`;
  `core/canonical`: `K.IsPerfect`, `CochainComplex.MinusWithTermsIn`, and the localized finite-
    free term property;
  `bridge/view`: `primeResidueFieldDerivedHomology` and the localized termwise rank condition on
    the chosen owner complex.
-/

/-- The degree-`i` homology of `K ⊗_R^L κ(𝔭)`. -/
abbrev primeResidueFieldDerivedHomology (p : PrimeSpectrum R) (K : DModR) (i : ℤ) :
    ModuleCat p.asIdeal.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat p.asIdeal.ResidueField) i).obj
    (K ⊗[R]^L[p.asIdeal.ResidueField])

-- Proof sketch: base change the perfect complex `K` from `R` to the residue field `κ(𝔭)` by
-- derived tensor product. Over a field, a perfect complex is represented by a bounded complex of
-- finite-dimensional vector spaces, so each homology group is finite-dimensional and only finitely
-- many degrees contribute nonzero homology.
/-- Lemma 15.76.7 (1): if `K` is perfect over `R`, then the homology of `K ⊗_R^L κ(𝔭)` is
finite-dimensional over `κ(𝔭)` in every degree and nonzero in only finitely many degrees. -/
theorem primeResidueFieldDerivedHomology_finiteDimensional_and_finiteSupport_of_isPerfect
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) :
    (∀ i : ℤ, FiniteDimensional p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i)) ∧
      Set.Finite {i : ℤ | ¬ IsZero (primeResidueFieldDerivedHomology p K i)} := sorry

-- Proof sketch: apply part `(1)` to see that each residue-field homology group
-- `H^i(K ⊗_R^L κ(𝔭))` is finite-dimensional. Localize `R` at `𝔭`, so that `K ⊗_R^L R_𝔭` is a
-- perfect complex over the local ring `R_𝔭`. Apply the local lifting statement to obtain a
-- bounded-above finite-free representative in the canonical owner
-- `CochainComplex.MinusWithTermsIn`, with those homology dimensions as termwise ranks, and then
-- descend that representative from `R_𝔭 = colim_{f ∉ 𝔭} R_f` to some away localization `R_f`,
-- keeping the lower support bound separate from the bounded-above owner data.
/-- Lemma 15.76.7 (2): if `d i = dim_{κ(𝔭)} H^i(K ⊗_R^L κ(𝔭))`, then after inverting some
`f ∉ 𝔭` the derived localization `K ⊗_R^L R_f` is represented by a bounded-above finite-free
complex with some lower support bound, whose degree-`i` term is free of rank `d i`. -/
theorem exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPerfect
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) (d : ℤ → ℕ)
    (hd :
      ∀ i : ℤ,
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = d i) :
    ∃ (f : R) (_ : f ∉ p.asIdeal) (a : ℤ) (P : BoundedFiniteFreeCpxAway[f]),
      (P : CpxAway[f]).IsStrictlyGE a ∧
        (∀ i : ℤ,
          Nonempty (((P : CpxAway[f]).X i) ≃ₗ[Localization.Away f]
            (Fin (d i) → Localization.Away f))) ∧
        Nonempty ((K ⊗[R]^L[Localization.Away f]) ≅ DerivedCategory.Q.obj (P : CpxAway[f])) :=
  sorry

end

end CategoryTheory
