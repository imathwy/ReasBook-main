import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_76_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
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

/- Domain-style sampling for Lemma 15.78.1:
- primary domain: pseudo-coherent bounded-below objects of `D(R)`, residue-field derived homology,
  and localized finite-free / perfect representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfect` from `Definition_15_75_1`,
  `primeResidueFieldDerivedHomology`,
  `exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPerfect` from
    `Lemma_15_76_7`,
  `exists_localizationAway_gapSplit_of_residueField_homology_isZero` from `Lemma_15_77_4`;
- best owner abstraction: this file is `source-facing` for the bounded-below pseudo-coherent
  criterion, but the bounded-above finite-free representative is already owned upstream by
  `CochainComplex.MinusWithTermsIn`, so the public representative statement here should reuse that
  owner instead of a parallel raw `CochainComplex` witness;
- primitive vs. derived:
  primitive data are `p`, `K`, the lower bound `a`, the pseudo-coherence / bounded-below
  hypotheses, and the vanishing below `a` of the internally defined residue-field dimensions
  `dim_{κ(𝔭)} H^i(K ⊗^L κ(𝔭))`;
  derived API is the away-localized bounded finite-free representative with terms of rank
  `Module.finrank` of those residue-field homology groups, and the resulting localized
  perfectness;
- source/core/bridge triage:
  `source-facing`: the two existence theorems below;
  `core/canonical`: `K.IsPerfect` and `CochainComplex.MinusWithTermsIn`;
  `bridge/view`: `primeResidueFieldDerivedHomology` and the gap-splitting localization theorem
    from `15.77.4`, which feed the perfectness bridge from `15.76.7`.
-/

variable
    (p : PrimeSpectrum R) (K : DModR) (a : ℤ)
    (hK : K.IsPseudoCoherent)
    (hboundedBelow : ∃ n : ℤ, K.IsGE n)
    (hda :
      ∀ i : ℤ,
        i < a →
          Module.rank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = 0)

-- Proof sketch: use the bounded-below hypothesis to lower the vanishing index to the chosen
-- bound `a`, so `H^i(K) = 0` for `i < a`. The condition that the internally defined residue-field
-- dimension is zero for `i < a` turns the residue-field homology in those degrees into zero
-- objects, and Lemma `15.77.4` then yields, after inverting some `f ∉ 𝔭`, a splitting with
-- perfect upper truncation `τ_{\ge a}`. The lower truncation vanishes because `K` is bounded
-- below, so the localization is perfect; then Lemma `15.76.7 (1)` gives finite-dimensionality of
-- the residue-field homology, and Lemma `15.76.7 (2)` yields the finite-interval free
-- representative with the corresponding termwise ranks.
/-- Lemma 15.78.1: let `R` be a commutative ring, let `𝔭 ⊂ R` be a prime, and let `K` be a
pseudo-coherent bounded-below object of `D(R)`. Set
`d i = dim_{κ(𝔭)} H^i(K \otimes_R^{\mathbf L} κ(𝔭))`. If `d i = 0` for all `i < a`, then after
inverting some `f ∉ 𝔭`, the localized derived object `K \otimes_R^{\mathbf L} R_f` is
represented by a bounded-above finite-free cochain complex whose degree-`i` term is free of rank
`dim_{κ(𝔭)} H^i(K \otimes_R^{\mathbf L} κ(𝔭))` and which vanishes in degrees `< a`. -/
theorem exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPseudoCoherent_of_isGE
    :
    ∃ (f : R) (_ : f ∉ p.asIdeal) (P : BoundedFiniteFreeCpxAway[f]),
      (P : CpxAway[f]).IsStrictlyGE a ∧
        (∀ i : ℤ,
          Nonempty (((P : CpxAway[f]).X i) ≃ₗ[Localization.Away f]
            (Fin (Module.finrank p.asIdeal.ResidueField
              (primeResidueFieldDerivedHomology p K i)) → Localization.Away f))) ∧
        Nonempty ((K ⊗[R]^L[Localization.Away f]) ≅ DerivedCategory.Q.obj (P : CpxAway[f])) :=
  sorry

-- Proof sketch: apply the representative theorem above and then use the fact that a bounded
-- complex of finite free modules is perfect in the derived category.
/-- If the residue-field homology of `K` has dimension `0` in all degrees `< a`, then after
inverting some element away from `𝔭`, the localized derived complex is perfect. -/
theorem exists_away_isPerfect_of_primeResidueFieldDerivedHomology_vanishing_below
    :
    ∃ f : R, f ∉ p.asIdeal ∧
      (K ⊗[R]^L[Localization.Away f]).IsPerfect := sorry

end

end CategoryTheory
