import Mathlib
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap13.Lemma_13_11_6
import stacks_project.Chap15.Definition_15_59_13

open scoped BigOperators
open scoped DerivedTensorProduct
open scoped ZeroObject
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [CategoryTheory.Limits.HasWidePullbacks (ModuleCat R)]
  [CategoryTheory.Limits.HasCoproducts (ModuleCat R)]
  [CategoryTheory.Limits.InitialMonoClass (ModuleCat R)]

/- 
Domain-style sampling for Lemma `15.64.4`.
- primary domain: cohomological spectral sequences in the bounded derived category `D^b(R)`
  computing the cohomology of a derived tensor product;
- sampled owner/canonical declarations in this domain:
  `CohomologicalSpectralSequence`,
  `FilteredComplex.convergesToCohomology`,
  `exists_kunneth_filteredTensorSpectralSequence`,
  `derivedTensorProduct`;
- best owner abstraction: a cohomological spectral sequence
  `E : CohomologicalSpectralSequence (ModuleCat R) 0` together with the Chapter `12`
  convergence owner on an associated filtered complex, while the displayed `E₂`-page and
  abutment objects remain source-facing bridge abbreviations;
- primitive vs. derived:
  primitive data are the spectral sequence `E` and the associated filtered complex `F` in the
  convergence clause; the `E₂`-page and abutment comparisons are derived API expressed
  propositionally by existential/nonempty comparison isomorphisms, while boundedness and
  convergence are expressed through the canonical Chapter `12` owner `F.convergesToCohomology E`;
- source/core/bridge triage:
  `source-facing`: `IsKunnethDerivedTensorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`,
    `FilteredComplex.convergesToCohomology`, and the Chapter `15` owner theorem
    `exists_kunneth_filteredTensorSpectralSequence`;
  `bridge/view`: `boundedDerivedTensorCohomology`, `kunnethDerivedTensorPageTwo`, and the
    convergence predicate below.

The numbered item is source-facing, but its convergence clause should be phrased through the
canonical filtered-complex owner API rather than through a parallel local filtered-cochain wrapper.
-/

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "H" => DerivedCategory.homologyFunctor Mod

/-- The abutment object `H^n(K \otimes_R^{\mathbf L} L)` for bounded derived `R`-complexes
`K, L ∈ D^b(R)`. -/
abbrev boundedDerivedTensorCohomology
    (K L : DbMod) (n : ℤ) : ModuleCat R :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The `E_2^{p,q}` term
`\bigoplus_{i + j = q} \operatorname{Tor}^R_{-p}(H^i(K), H^j(L))`
of the Künneth spectral sequence, with the convention that it is zero for `p > 0`. -/
abbrev kunnethDerivedTensorPageTwo
    (K L : DbMod) (p q : ℤ) : ModuleCat R :=
  if _ : p ≤ 0 then
    ∐ fun i : ℤ ↦
      (((Tor Mod (Int.toNat (-p))).obj
          ((H i).obj K.obj)).obj
        ((H (q - i)).obj L.obj))
  else
    (0 : Mod)

/-- A cohomological spectral sequence converges to `H^*(K ⊗[R]^L L)` if it is associated to a
filtered complex whose cohomology identifies with that of the derived tensor product and which
satisfies the Chapter `12` convergence owner. -/
def ConvergesToDerivedTensorCohomology
    (E : CohomologicalSpectralSequence Mod 0) (K L : DbMod) : Prop :=
  ∃ (F : FilteredComplex Mod) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ boundedDerivedTensorCohomology K L n)

/-- The Künneth spectral sequence for bounded derived `R`-complexes `K` and `L`: a bounded
cohomological spectral sequence with the expected `E_2`-page and abutment. -/
def IsKunnethDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence Mod 0) (K L : DbMod) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ kunnethDerivedTensorPageTwo K L p q)) ∧
    ConvergesToDerivedTensorCohomology E K L

-- Proof sketch: represent `K` and `L` by bounded complexes, filter them by stupid truncations,
-- and apply Proposition `15.64.3` to the resulting filtered tensor complex. The associated
-- spectral sequence is bounded by the boundedness of `K` and `L`, its `E₁`-page identifies with
-- the graded pieces `H^{-i}(K)[i]` and `H^{-j}(L)[j]`, and reindexing the page `r - 1` terms by
-- `E_r^{p,q} = (E')_{r - 1}^{-q, p + 2q}` gives the stated `E₂`-page and abutment.
/-- Lemma 15.64.4 (Künneth Spectral Sequence): for bounded derived `R`-complexes `K` and `L`,
there exists a bounded cohomological spectral sequence whose `E_2`-page is
`\bigoplus_{i + j = q} \operatorname{Tor}^R_{-p}(H^i(K), H^j(L))` and which converges to
`H^{p + q}(K \otimes_R^{\mathbf L} L)`. The differentials are those of a cohomological spectral
sequence, so they have bidegree `(r, -r + 1)`. -/
theorem exists_kunnethDerivedTensorSpectralSequence
    (K L : DbMod) :
    ∃ E : CohomologicalSpectralSequence Mod 0,
      IsKunnethDerivedTensorSpectralSequence E K L := sorry

end

end CategoryTheory
