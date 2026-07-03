import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_78_1 (from Chap15) -/
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

/-! ### Lemma_15_78_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.78.2:
- primary domain: perfectness and tor-amplitude for pseudo-coherent derived `R`-complexes,
  detected on residue-field fibers over prime and maximal ideals;
- sampled owner declarations:
  `K.IsPerfect`,
  `HasTorAmplitudeIn K a b`,
  `primeResidueFieldDerivedHomology`,
  `K ⊗[R]^L[κ(𝔭)]`;
- best owner abstraction: the public source-facing statement should be expressed in terms of the
  canonical owners `K.IsPerfect`, `HasTorAmplitudeIn`, and the earlier chapter bridge
  `primeResidueFieldDerivedHomology`, rather than re-expanding residue-field fibers through
  `derivedTensorProduct` and `singleFunctor`;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K`, the interval bounds `a, b`, and the
  residue-field homology objects indexed by primes;
  derived API is the conjunction `K.IsPerfect ∧ HasTorAmplitudeIn K a b` and the maximal-ideal
  specialization of the prime-fiber vanishing condition.

Source/core/bridge triage:
- `source-facing`: the TFAE criterion below;
- `core/canonical`: `K.IsPerfect` and `HasTorAmplitudeIn K a b`;
- `bridge/view`: `primeResidueFieldDerivedHomology`, which names the degreewise homology of the
  canonical derived base change `K ⊗_R^L κ(𝔭)` without introducing a second owner abstraction.
-/

-- Proof sketch: the implications from perfection with tor-amplitude to prime fibers and then to
-- maximal fibers are immediate by derived base change. For the converse, use Lemma `15.77.4` to
-- deduce vanishing of the cohomology of `K` outside `[a, b]` and to obtain local perfect
-- tor-amplitude bounds near every maximal ideal; then conclude globally from Lemma `15.75.12` and
-- Lemma `15.67.16`.
/-- Lemma 15.78.2: for a pseudo-coherent object `K` of `D(R)`, the following are equivalent:
`K` is perfect with tor-amplitude in `[a, b]`; for every prime `𝔭` of `R`, the derived fiber
`K \otimes_R^{\mathbf L} κ(\mathfrak p)` has vanishing homology outside `[a, b]`; and it is
enough to check this only on maximal ideals. -/
theorem perfect_torAmplitude_tfae_prime_and_maximal_residueField_homology_vanishing_of_isPseudoCoherent
    (K : DMod) (a b : ℤ) (hK : K.IsPseudoCoherent) :
    List.TFAE [
      K.IsPerfect ∧ HasTorAmplitudeIn K a b,
      ∀ 𝔭 : PrimeSpectrum R, ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology 𝔭 K i),
      ∀ (𝔪 : PrimeSpectrum R) (_ : 𝔪.asIdeal.IsMaximal) (i : ℤ), i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology 𝔪 K i)
    ] := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_78_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.78.3:
- primary domain: perfectness and negative derived-fiber homology criteria for pseudo-coherent
  bounded-below objects of `D(R)` under localization at primes and maximal ideals;
- sampled owner declarations:
  `K.IsPerfect`,
  `derivedTensorWithAlgebra_isPerfect`,
  `primeResidueFieldDerivedHomology`,
  `K.IsPseudoCoherent`,
  `MaximalSpectrum`;
- best owner abstraction: this file is `source-facing` for the local/global `TFAE`, while the
  core/canonical owners are `K.IsPerfect`, `K.IsPseudoCoherent`, `K.IsGE`, the standard derived
  base-change notation `K ⊗[R]^L[S]`, the prime-fiber homology owner
  `primeResidueFieldDerivedHomology`, and the chapter-level maximal-local owner
  `MaximalSpectrum R`;
- primitive vs. derived:
  primitive data are `K`, the prime and maximal localization tests, the residue-field homology
  vanishing tests, and the bounded-below hypothesis in the final theorem;
  derived API is the fiber homology object itself, already owned upstream by
  `primeResidueFieldDerivedHomology`, so this file should reuse that owner instead of restating
  raw homology-functor applications, with maximal tests transported through the canonical bridge
  `m.toPrimeSpectrum : PrimeSpectrum R`;
- source/core/bridge triage:
  `source-facing`: the two `TFAE` theorems below;
  `core/canonical`: `K.IsPerfect`, `K.IsPseudoCoherent`, `K.IsGE`, `derivedTensorWithAlgebra`,
    and `primeResidueFieldDerivedHomology`;
  `bridge/view`: the prime-localization specialization of `derivedTensorWithAlgebra_isPerfect`.
-/

/-- The ideal underlying a point of `Spec R` is prime, viewed as a local typeclass instance. -/
local instance (𝔭 : PrimeSpectrum R) : 𝔭.asIdeal.IsPrime := 𝔭.isPrime

-- Proof sketch: specialize derived base change of perfect complexes to the algebra maps
-- `R → R_𝔭` for prime localizations.
/-- A perfect derived `R`-complex remains perfect after localization at any prime ideal. -/
theorem isPerfect_localizationAtPrime_of_isPerfect
    {K : DMod} (hK : K.IsPerfect) (𝔭 : PrimeSpectrum R) :
    (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect := by
  have hloc : (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect :=
    derivedTensorWithAlgebra_isPerfect K hK
  exact hloc

-- Proof sketch: `(2) ⇒ (3)` is immediate. For `(3) ⇒ (2)`, localize further from a maximal ideal
-- containing the given prime. The implications `(2) ⇒ (4)` and `(3) ⇒ (5)` come from base change
-- to residue fields. For `(4) ⇒ (2)` and `(5) ⇒ (3)`, reduce to the local case and use the gap
-- splitting statement of Lemma `15.77.4` together with Nakayama to force the lower truncation to
-- vanish.
/-- For a pseudo-coherent object of `D(R)`, perfectness after localization at primes, perfectness
after localization at maximal ideals, and vanishing of sufficiently negative residue-field
homology at primes or maximal ideals are equivalent conditions. -/
theorem prime_and_maximal_localizations_and_residueField_vanishing_tfae_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) :
    List.TFAE
      [ ∀ 𝔭 : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect
      , ∀ 𝔪 : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔭 K i)
      , ∀ 𝔪 : MaximalSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)
      ] := sorry

-- Proof sketch: perfection implies perfectness after prime localization by the first theorem.
-- The bounded-below hypothesis and Lemma `15.78.1` upgrade the residue-field vanishing conditions
-- to local perfectness near each maximal ideal, and the previous TFAE then yields equivalence of
-- all five conditions.
/-- Lemma 15.78.3: for a pseudo-coherent bounded-below object `K` of `D(R)`, the following are
equivalent: `K` is perfect, all prime localizations `K \otimes_R^{\mathbf L} R_\mathfrak p` are
perfect, all maximal localizations `K \otimes_R^{\mathbf L} R_\mathfrak m` are perfect, and the
derived fibers over primes or maximal ideals have vanishing homology in all sufficiently negative
degrees. -/
theorem perfect_primeLocalizations_maximalLocalizations_residueField_vanishing_tfae_of_isPseudoCoherent_of_isGE
    (K : DMod) (hK : K.IsPseudoCoherent) (hboundedBelow : ∃ n : ℤ, K.IsGE n) :
    List.TFAE
      [ K.IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect
      , ∀ 𝔪 : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔭 K i)
      , ∀ 𝔪 : MaximalSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)
      ] := sorry

end

end CategoryTheory

/-! ### Lemma_15_78_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)

/-
Domain sampling pass:
* primary domain: projective amplitude and perfectness criteria for pseudo-coherent objects in the
  derived category `D(R)`, tested by derived `Ext` against degree-zero modules;
* sampled owner declarations:
  - `HasProjectiveAmplitudeIn` from `Definition_15_69_1`, the chapter owner for projective
    amplitude;
  - `projectiveAmplitudeIn_ext_vanishing_tfae` from `Lemma_15_69_2`, the source-facing TFAE using
    unrestricted `Ext`-vanishing;
  - `derivedExtFilteredColimitComparison_isIso_of_isMPseudoCoherent` and
    `derivedExtFilteredColimitComparison_mono_at_neg_of_isMPseudoCoherent` from `Lemma_15_66_1`,
    whose statements are phrased on the canonical comparison map `colimit.post`, giving the
    chapter bridge from all modules to finitely presented test modules under
    pseudo-coherence;
  - `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension` from `Lemma_15_75_2`, the
    perfectness owner criterion.

Source/core/bridge triage:
* `source-facing`: the finitely-presented `Ext`-vanishing clauses appearing in Stacks
  `Lemma 15.78.4`;
* `core/canonical`: `HasProjectiveAmplitudeIn`, `HasTorAmplitudeIn`, and
  `DerivedCategory.IsPerfect`, together with the unrestricted `Ext`-vanishing package from
  `Lemma_15_69_2`;
* `bridge/view`: Lemma `15.66.1`, which justifies replacing unrestricted module tests by
  finitely presented ones for pseudo-coherent objects.

Primitive data here are only the finitely-presented `Ext`-vanishing predicates themselves. The
perfectness, tor-amplitude, projective-amplitude, and cohomology-vanishing owners are already
canonical upstream, so this file should keep only the source-facing specialization and reuse those
owners directly in the main `TFAE`.
-/

-- Proof sketch: `(2) → (1)` is the final implication of Lemma `15.75.2`. For `(1) → (2)`, a
-- projective representative concentrated in `[a, b]` is automatically a flat representative in
-- the same range, so Lemma `15.75.2` upgrades it to perfection with tor-amplitude in `[a, b]`.
-- Under pseudo-coherence, Lemma `15.66.1` together with Lemma `10.11.3` lets one test the relevant
-- `Ext`-vanishing only on finitely presented modules, and then Lemma `15.69.2` gives the
-- equivalence with the projective-amplitude criteria.
/-- Lemma 15.78.4: let `R` be a ring, let `K` be a pseudo-coherent object of `D(R)`, and let
`a, b ∈ ℤ`. Then the following are equivalent: `K` has projective-amplitude in `[a, b]`; `K` is
perfect and has tor-amplitude in `[a, b]`; `Ext^i_R(K, N) = 0` for every finitely presented
`R`-module `N` and every `i ∉ [-b, -a]`; `H^n(K) = 0` for `n > b` and
`Ext^i_R(K, N) = 0` for every finitely presented `R`-module `N` and every `i > -a`; and
`H^n(K) = 0` for `n ∉ [a - 1, b]` and `Ext^{-a + 1}_R(K, N) = 0` for every finitely presented
`R`-module `N`. -/
theorem projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent
    (K : DMod) (a b : ℤ) (hK : K.IsPseudoCoherent) :
    List.TFAE [
      HasProjectiveAmplitudeIn K a b,
      K.IsPerfect ∧ HasTorAmplitudeIn K a b,
      ∀ (N : ModuleCat R) [Module.FinitePresentation R N] (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          ∀ e : Ext^i(K, (single₀).obj N), e = 0,
      (∀ n : ℤ, b < n → IsZero ((H n).obj K)) ∧
        ∀ (N : ModuleCat R) [Module.FinitePresentation R N] (i : ℤ), -a < i →
          ∀ e : Ext^i(K, (single₀).obj N), e = 0,
      (∀ n : ℤ, n ∉ Set.Icc (a - 1) b → IsZero ((H n).obj K)) ∧
        ∀ (N : ModuleCat R) [Module.FinitePresentation R N],
          ∀ e : Ext^(-a + 1)(K, (single₀).obj N), e = 0
    ] := sorry

end

end CategoryTheory

/-! ### Lemma_15_78_5 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.78.5:
- primary domain: perfectness and tor-amplitude for pseudo-coherent derived complexes under flat
  restriction of scalars, detected on residue-field fibers of `A → B`;
- sampled owner declarations:
  `K.IsPseudoCoherent`,
  `K.IsPerfect`,
  `HasTorAmplitudeIn`,
  `HasGlobalDimensionLE`,
  `HasWeakDimensionLE`;
- best owner abstraction: the theorem is source-facing and should conclude in the canonical owner
  language `K.IsPerfect ∧ HasTorAmplitudeIn K (a - d) b`; on the ring side, the primitive
  derived-category conclusion is driven by the weak-dimension owner `HasWeakDimensionLE`, while
  the source hypothesis `HasGlobalDimensionLE (p.asIdeal.Fiber B) d` is a stronger bridge input
  reused via the upstream instance `HasGlobalDimensionLE ⟹ HasWeakDimensionLE`;
- primitive vs. derived:
  primitive data are the flat map `A → B`, the pseudo-coherent object `K : D(B)`, the interval
  bounds `a, b`, and the uniform fiberwise global-dimension bound;
  derived API is the perfectness/tor-amplitude conclusion for `K` over `B`, together with the
  restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K : DModA)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, matching the textbook hypothesis in terms of global
  dimension of every fiber ring;
- `core/canonical`: `K.IsPseudoCoherent`, `K.IsPerfect`, and `HasTorAmplitudeIn`;
- `bridge/view`: the restricted derived object over `A`, and the ring-side implication from
  `HasGlobalDimensionLE` on each fiber to the weak-dimension owner used by Lemma `15.67.19`.
-/

-- Proof sketch: use the flatness of `A → B` to compare tor-amplitude over `A` with the homology
-- of the fibers over `B ⊗[A] κ(p)`. For each prime `p`, the fiber ring has global dimension at
-- most `d`, so Lemma `15.67.19` upgrades the fiberwise amplitude interval from `[a, b]` to
-- `[a - d, b]`. Then apply Lemma `15.78.2` to the pseudo-coherent `B`-complex `K` to conclude
-- that `K` is perfect over `B` with tor-amplitude in the same interval.
/-- Lemma 15.78.5: let `A → B` be a flat ring map, let `d ≥ 0`, and let `K^•` be a
pseudo-coherent object of `D(B)`. If every fiber ring `B ⊗[A] κ(\mathfrak p)` has global
dimension at most `d` and `K^•`, viewed over `A`, has tor-amplitude in `[a, b]`, then `K^•` is
perfect over `B` and has tor-amplitude in `[a - d, b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_fiber_hasGlobalDimensionLE
    (K : DModB) (a b : ℤ) (d : ℕ)
    (hfiber :
      ∀ p : PrimeSpectrum A, HasGlobalDimensionLE (p.asIdeal.Fiber B) d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        a b) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

end

end CategoryTheory

/-! ### Lemma_15_78_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.78.6:
- primary domain: pseudo-coherent derived complexes over a flat local ring map, with perfection
  and tor-amplitude detected on the closed-fiber residue field;
- sampled owner declarations:
  `K.IsPerfect`,
  `HasTorAmplitudeIn`,
  `primeResidueFieldDerivedHomology`,
  `hasGlobalDimensionLE_of_isRegularLocalRing`;
- best owner abstraction: the core/canonical owners are `K.IsPerfect`, `HasTorAmplitudeIn`, and
  the residue-field-fiber bridge `primeResidueFieldDerivedHomology`; this file is only a
  `source-facing` local closed-fiber specialization, so it should reuse those owners rather than
  restating the derived special fiber entrywise;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K`, the local closed-fiber regularity hypothesis,
  the dimension bound `ringKrullDim ((maximalIdeal A).Fiber B) = d`, and the closed-point
  residue-field homology vanishing of the restriction of scalars of `K` to `D(A)`;
  derived API is the conjunction `K.IsPerfect ∧ HasTorAmplitudeIn K (a - d) b` and the thin
  bridge from tor-amplitude over `A` to the closed-point vanishing hypothesis;
- source/core/bridge triage:
  `source-facing`: the two local closed-fiber criteria below;
  `core/canonical`: `K.IsPerfect`, `HasTorAmplitudeIn`, and
    `primeResidueFieldDerivedHomology`;
  `bridge/view`: restriction of scalars along `A → B`.
-/

-- Proof sketch: identify the derived tensor with `κ(maximalIdeal A)` as a complex over the closed
-- fiber `(maximalIdeal A).Fiber B`, use the regular-local hypothesis and Proposition `10.110.1`
-- to bound the global dimension of that fiber by `d`, and then apply Lemma `15.67.19` to shift
-- the homology support from `[a, b]` to `[(a - d), b]`. Finally use the maximal-ideal case of
-- Lemma `15.78.2` for the local ring `B`.
/-- A weaker sufficient hypothesis for Lemma `15.78.6`: it is enough to assume that the derived
special fiber `K^• \otimes_A^{\mathbf L} κ(\mathfrak m_A)` has vanishing homology outside
`[a, b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_baseResidueFieldDerivedHomology_vanishing_of_closedFiber_isRegularLocalRing
    (K : DModB) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKκ :
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint A)
            ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
            i)) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

-- Proof sketch: tor-amplitude over `A` implies the required vanishing of the derived special
-- fiber over `κ(maximalIdeal A)`. Apply the residue-field criterion above to obtain perfection of
-- `K` over `B` and tor-amplitude in `[(a - d), b]`.
/-- Lemma 15.78.6: let `A → B` be a flat local ring homomorphism, let `d ≥ 0`, and let `K^•` be a
pseudo-coherent object of `D(B)`. If the closed fiber `(maximalIdeal A).Fiber B`, equivalently
`B ⧸ (Ideal.map (algebraMap A B) (maximalIdeal A))`, is a regular local ring of dimension `d`,
and `K^•`, viewed over `A`, has tor-amplitude in `[a, b]`, then `K^•` is perfect over `B` with
tor-amplitude in `[(a - d), b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_closedFiber_isRegularLocalRing
    (K : DModB) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        a b) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

end

end CategoryTheory
