import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Bezout
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Valuation.ValuationRing

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_125_1 (from Chap15) -/
open CategoryTheory
open scoped DirectSum

universe u v w

section

variable {R : Type u} [CommRing R]

namespace LinearMap

variable {M : Type*} {N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map is principal-pure if multiplication by every principal ideal meets its range
exactly as in the Stacks Project hypothesis `fA = A ∩ fB`. -/
def IsPrincipalPure (f : M →ₗ[R] N) : Prop :=
  ∀ r : R,
    principalIdeal r • f.range = f.range ⊓ principalIdeal r • ⊤

end LinearMap

open LinearMap

/- Domain-style sampling:
- primary domain: short exact sequences of `R`-modules tested against cyclic quotient modules
  `R ⧸ (f)` and the resulting split-summand criterion;
- sampled owner declarations:
  `principalIdeal`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `LinearMap.IsPrincipalPure`,
  `LinearMap.compRight`,
  `Module.Projective.iff_split`;
- best owner abstraction: this file is `source-facing`; the exact-sequence side should reuse the
  canonical short-complex owner `ShortComplex.ShortExact`. No upstream chapter/mathlib owner was
  found for the principal-purity condition `fA = A ∩ fB`, so the source-facing owner in this file
  should be the left map itself via `LinearMap.IsPrincipalPure`, with its range expression kept
  internal to that definition;
  the cyclic quotient side should use the chapter owner `principalIdeal`, and the surjectivity
  statement should remain on the canonical postcomposition map `LinearMap.compRight`; although
  `IsSplitMono` is the categorical owner of a split inclusion, this theorem quantifies modules in
  different universes, so the stable source-facing direct-summand witness remains the explicit
  split data `s.comp i = LinearMap.id`;
- primitive data vs. derived API:
  primitive data are the short complex `S`, the principal-purity property of the image submodule
  carried by the left map `S.f.hom`, and a split inclusion of `P` into a direct sum of principal
  quotients;
  derived API is the lifting-surjectivity criterion phrased through `LinearMap.compRight`.

Source/core/bridge triage:
- `source-facing`: the equivalence theorem below;
- `core/canonical`: `principalIdeal`, `ShortComplex.ShortExact`,
  `LinearMap.IsPrincipalPure`, `LinearMap.compRight`, `Module.Projective.iff_split`, and the
  range submodule `S.f.hom.range` appearing only inside the owner definition;
- `bridge/view`: the theorem below, which combines the exact short-complex owner with the
  map-level principal-purity owner in the source lifting criterion.
-/

-- Proof sketch: for the forward implication, reduce to a summand `R ⧸ (f)` and lift a map
-- `R ⧸ (f) → C` by choosing a preimage of `1` in `B` and correcting it using the hypothesis
-- `fA = A ∩ fB`. For the reverse implication, take the direct sum over all maps `R ⧸ (f) → P`,
-- map it onto `P`, and apply the assumed lifting property to the resulting short exact sequence;
-- the principal-purity condition on its kernel gives a splitting.
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Lemma 15.125.1: an `R`-module `P` is a direct summand of a direct sum of modules of the form
`R ⧸ (f)` if and only if for every short exact sequence `0 → A → B → C → 0` of `R`-modules with
`fA = A ∩ fB` for all `f : R`, the induced map `Hom_R(P, B) → Hom_R(P, C)` is surjective. -/
theorem directSummand_iff_surjective_compRight_of_principalPure_shortExact :
    (∃ (ι : Type w) (r : ι → R)
      (i : P →ₗ[R] (⨁ j : ι, R ⧸ principalIdeal (r j)))
      (s : (⨁ j : ι, R ⧸ principalIdeal (r j)) →ₗ[R] P),
      s.comp i = LinearMap.id) ↔
      ∀ ⦃S : ShortComplex (ModuleCat R)⦄
        (hS : S.ShortExact)
        (hi : IsPrincipalPure S.f.hom),
        Function.Surjective
          (LinearMap.compRight R S.g.hom : (P →ₗ[R] S.X₂) →ₗ[R] P →ₗ[R] S.X₃) := sorry

end

/-! ### Lemma_15_125_2_Generalized_valuation_rings (from Chap15) -/
universe u

section

open Submodule.IsPrincipal

/-
Domain-style sampling:
- primary domain: commutative algebra of generalized valuation rings and their ideal theory;
- sampled owner declarations:
  `PreValuationRing`,
  `PreValuationRing.iff_dvd_total`,
  `PreValuationRing.iff_ideal_total`,
  `ValuationRing.iff_local_bezout_domain`;
- best owner abstraction: `PreValuationRing R` is the canonical owner for the non-domain
  generalized valuation-ring condition, while `ValuationRing R` remains the domain specialization;
- primitive data vs. derived API:
  primitive data is only the ambient nontrivial commutative ring `R` together with the owner
  predicate `PreValuationRing R`;
  derived API is the source-facing comparison with the local Bézout and ideal-order formulations,
  so the TFAE should reuse the owner instead of restating total divisibility as a separate clause.

Source/core/bridge triage:
- `source-facing`: the three-way equivalence in the Stacks lemma;
- `core/canonical`: `PreValuationRing`, `ValuationRing`, `IsLocalRing`, `IsBezout`, and the ideal
  order on `Ideal R`;
- `bridge/view`: the theorem `generalized_valuation_ring_tfae`, which compares the source-facing
  local Bézout and ideal-order statements to the canonical owner `PreValuationRing R`.
-/

variable {R : Type u} [CommRing R]

theorem isPrincipal_span_finset_of_ideal_total
    (h : @Std.Total (Ideal R) (· ≤ ·)) (s : Finset R) :
    (Ideal.span (s : Set R)).IsPrincipal := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (bot_isPrincipal : (⊥ : Ideal R).IsPrincipal)
  | insert x s _ hs =>
      rcases h.total (Ideal.span ({x} : Set R)) (Ideal.span (s : Set R)) with hxs | hsx
      · simpa [Finset.coe_insert, Ideal.span_insert, sup_eq_right.mpr hxs] using hs
      · simpa [Finset.coe_insert, Ideal.span_insert, sup_eq_left.mpr hsx] using
          (inferInstance : (Ideal.span ({x} : Set R)).IsPrincipal)

theorem isBezout_of_ideal_total (h : @Std.Total (Ideal R) (· ≤ ·)) : IsBezout R := by
  refine ⟨fun I hI ↦ ?_⟩
  rcases hI with ⟨s, rfl⟩
  exact isPrincipal_span_finset_of_ideal_total h s

theorem ideal_eq_span_singleton_of_not_mem_maximalIdeal_mul [IsLocalRing R] {I : Ideal R}
    [I.IsPrincipal] {x : R} (hxI : x ∈ I) (hx : x ∉ IsLocalRing.maximalIdeal R * I) :
    I = Ideal.span ({x} : Set R) := by
  obtain ⟨r, hr⟩ :=
    Ideal.mem_span_singleton'.mp (by
      simpa [Ideal.span_singleton_generator I] using hxI :
        x ∈ Ideal.span ({generator I} : Set R))
  have hr_not_mem : r ∉ IsLocalRing.maximalIdeal R := by
    intro hr_mem
    apply hx
    simpa [hr] using
      (Ideal.mul_mem_mul hr_mem (generator_mem I) :
        r * generator I ∈ IsLocalRing.maximalIdeal R * I)
  have hr_unit : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp hr_not_mem
  rcases hr_unit with ⟨u, rfl⟩
  apply le_antisymm
  · rw [← Ideal.span_singleton_generator I]
    exact (Ideal.span_singleton_le_iff_mem (Ideal.span ({x} : Set R))).2 <|
      Ideal.mem_span_singleton'.2 ⟨↑u⁻¹, by
        calc
          ↑u⁻¹ * x = ↑u⁻¹ * (↑u * generator I) := by rw [hr]
          _ = generator I := by simp⟩
  · exact (Ideal.span_singleton_le_iff_mem I).2 hxI

theorem span_pair_eq_span_left_or_right [IsLocalRing R] [IsBezout R] (a b : R) :
    Ideal.span ({a, b} : Set R) = Ideal.span ({a} : Set R) ∨
      Ideal.span ({a, b} : Set R) = Ideal.span ({b} : Set R) := by
  let I : Ideal R := Ideal.span ({a, b} : Set R)
  letI : I.IsPrincipal := by
    simpa [I] using (inferInstance : (Ideal.span ({a, b} : Set R)).IsPrincipal)
  by_cases hI : I = ⊥
  · left
    have ha : a = 0 := by
      simpa using (show a ∈ (⊥ : Ideal R) by
        simpa [I, hI] using (Ideal.subset_span (by simp : a ∈ ({a, b} : Set R))))
    have hb : b = 0 := by
      simpa using (show b ∈ (⊥ : Ideal R) by
        simpa [I, hI] using (Ideal.subset_span (by simp : b ∈ ({a, b} : Set R))))
    simp [ha, hb]
  have h_not :
      a ∉ IsLocalRing.maximalIdeal R * I ∨ b ∉ IsLocalRing.maximalIdeal R * I := by
    by_contra h
    have ha_mul : a ∈ IsLocalRing.maximalIdeal R * I := by
      by_contra ha
      exact h (Or.inl ha)
    have hb_mul : b ∈ IsLocalRing.maximalIdeal R * I := by
      by_contra hb
      exact h (Or.inr hb)
    have hle : I ≤ IsLocalRing.maximalIdeal R * I := by
      change Ideal.span ({a, b} : Set R) ≤ IsLocalRing.maximalIdeal R * I
      refine Ideal.span_le.2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha_mul
      · exact hb_mul
    have hfg : I.FG := (inferInstance : I.IsPrincipal).fg
    exact hI <|
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) I hfg hle
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  rcases h_not with ha | hb
  · left
    exact ideal_eq_span_singleton_of_not_mem_maximalIdeal_mul
      (show a ∈ I by
        change a ∈ Ideal.span ({a, b} : Set R)
        exact Ideal.subset_span (by simp))
      ha
  · right
    exact ideal_eq_span_singleton_of_not_mem_maximalIdeal_mul
      (show b ∈ I by
        change b ∈ Ideal.span ({a, b} : Set R)
        exact Ideal.subset_span (by simp))
      hb

theorem ideal_total_of_isLocalRing_isBezout [IsLocalRing R] [IsBezout R] :
    @Std.Total (Ideal R) (· ≤ ·) := by
  constructor
  intro I J
  classical
  by_cases hIJ : I ≤ J
  · exact Or.inl hIJ
  · right
    by_cases hJI : J ≤ I
    · exact hJI
    · have hIJ' : ∃ a, a ∈ I ∧ a ∉ J := by
        by_contra h
        apply hIJ
        intro a haI
        by_contra haJ
        exact h ⟨a, haI, haJ⟩
      have hJI' : ∃ b, b ∈ J ∧ b ∉ I := by
        by_contra h
        apply hJI
        intro b hbJ
        by_contra hbI
        exact h ⟨b, hbJ, hbI⟩
      obtain ⟨a, haI, haJ⟩ := hIJ'
      obtain ⟨b, hbJ, hbI⟩ := hJI'
      rcases span_pair_eq_span_left_or_right a b with hspan | hspan
      · exfalso
        apply hbI
        have hb_span : b ∈ Ideal.span ({a} : Set R) := by
          simpa [← hspan] using (Ideal.subset_span (by simp : b ∈ ({a, b} : Set R)))
        exact ((Ideal.span_singleton_le_iff_mem I).2 haI) hb_span
      · exfalso
        apply haJ
        have ha_span : a ∈ Ideal.span ({b} : Set R) := by
          simpa [← hspan] using (Ideal.subset_span (by simp : a ∈ ({a, b} : Set R)))
        exact ((Ideal.span_singleton_le_iff_mem J).2 hbJ) ha_span

variable (R : Type u) [CommRing R] [Nontrivial R]

-- Proof sketch: use the canonical owner `PreValuationRing R` for the generalized valuation-ring
-- condition, obtain `IsLocalRing R` from the existing instance, derive `IsBezout R` by showing
-- every two-generated ideal is principal, and compare the first and third clauses using
-- `PreValuationRing.iff_ideal_total`.
/-- Lemma 15.125.2 (Generalized valuation rings): for a nonzero commutative ring `R`, the
following are equivalent: `R` is a generalized valuation ring in the canonical sense
`PreValuationRing R`, `R` is a local Bézout ring, and the ideals of `R` are linearly ordered by
inclusion. -/
theorem generalized_valuation_ring_tfae :
    List.TFAE
      [PreValuationRing R,
        IsLocalRing R ∧ IsBezout R,
        @Std.Total (Ideal R) (· ≤ ·)] := by
  tfae_have 1 ↔ 3 := PreValuationRing.iff_ideal_total
  tfae_have 3 → 2 := by
    intro h
    letI : PreValuationRing R := (PreValuationRing.iff_ideal_total.mpr h)
    exact ⟨inferInstance, isBezout_of_ideal_total h⟩
  tfae_have 2 → 3 := by
    rintro ⟨hlocal, hbezout⟩
    letI : IsLocalRing R := hlocal
    letI : IsBezout R := hbezout
    exact ideal_total_of_isLocalRing_isBezout
  tfae_finish

end

/-! ### Lemma_15_125_3 (from Chap15) -/
open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: finitely presented module decompositions over generalized valuation rings;
- sampled owner declarations:
  `PreValuationRing`,
  `PreValuationRing.iff_ideal_total`,
  `principalIdeal`;
- best owner abstraction: this item remains `source-facing`, with the ambient generalized
  valuation-ring hypothesis carried directly by the canonical owner `PreValuationRing R`; the
  cyclic quotient summands should use the chapter owner `principalIdeal` rather than restating
  `Ideal.span ({f} : Set R)`. The bridge from the ideal-order formulation to this owner is
  `PreValuationRing.iff_ideal_total`; the stronger PID structure theorem
  `Module.equiv_free_prod_directSum` is only a downstream specialization and would change the
  theorem's semantics by introducing a free part, so the decomposition here should stay on the
  canonical `LinearEquiv`/`DirectSum` surface instead of collapsing to that later view or
  introducing a local package;
- primitive data vs. derived API:
  primitive data is the ambient ring `R` together with the finitely presented `R`-module `M`;
  derived API is the finite index `n`, the family `f : Fin n → R`, and the resulting linear
  equivalence from `M` to the direct sum of the corresponding principal quotient modules.

Source/core/bridge triage:
- `source-facing`: the existence of a finite cyclic-quotient decomposition for `M`;
- `core/canonical`: `PreValuationRing`, `principalIdeal`, and `LinearEquiv`;
- `bridge/view`: `PreValuationRing.iff_ideal_total`, relating the source's ideal-order language to
  the canonical owner `PreValuationRing`.
-/

section

variable {R : Type u} [CommRing R] [PreValuationRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

-- Proof sketch: if `R` is subsingleton, then every `R`-module is subsingleton, so one may take
-- `n = 0` and the unique linear equivalence to the empty direct sum. Otherwise, argue by induction
-- on the dimension of `M / maximalIdeal R • ⊤` over the residue field of the local ring coming
-- from `PreValuationRing R`. Choose a lift whose annihilator is the annihilator of `M`, split off
-- the corresponding cyclic summand using the principal-pure lifting criterion of
-- Lemma `15.125.1`, and conclude that the resulting annihilator ideal is principal because `M` is
-- finitely presented.
/-- Lemma 15.125.3: if `R` is a generalized valuation ring in the canonical sense
`PreValuationRing R`, then every finitely presented `R`-module is linearly isomorphic to a finite
direct sum of principal quotient modules `R ⧸ (fᵢ)`. -/
theorem finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients :
    ∃ (n : ℕ) (f : Fin n → R),
      Nonempty (M ≃ₗ[R] ⨁ i : Fin n, R ⧸ principalIdeal (f i)) := sorry

end

/-! ### Lemma_15_125_4 (from Chap15) -/
open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: local-global decomposition of finitely presented modules into finite direct sums
  of principal quotient modules over generalized valuation rings;
- sampled owner declarations:
  `PreValuationRing`,
  `principalIdeal`,
  `finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients`,
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact`;
- best owner abstraction: this item is `source-facing`, not a new core owner. The ambient
  generalized valuation-ring hypothesis should be expressed through the canonical owner
  `PreValuationRing`, and the cyclic summands should reuse the chapter owner `principalIdeal`;
- primitive data vs. derived API:
  primitive data is the ambient commutative ring `R`, the finitely presented module `M`, and the
  local maximal-ideal hypotheses `PreValuationRing (Localization.AtPrime m)`;
  derived API is the existence of a split inclusion of `M` into a finite direct sum of principal
  quotient modules.

Source/core/bridge triage:
- `source-facing`: the theorem below, which packages the Stacks local-global statement as explicit
  retract data;
- `core/canonical`: `PreValuationRing`, `Module.FinitePresentation`, and the quotient owner
  `principalIdeal`;
- `bridge/view`: `finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients`
  provides the stronger local decomposition over a genuine prevaluation ring, while
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact`
  is the canonical bridge from local decomposition data to the global retract conclusion, so this
  file should reuse that existing split-data surface rather than introduce a parallel local direct-
  summand wrapper.
-/

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

-- Proof sketch: by the bridge theorem
-- `directSummand_iff_surjective_compRight_of_principalPure_shortExact`, it
-- suffices to prove the required lifting property for `M`. Check surjectivity after localization
-- at each maximal ideal using the locality result of Algebra, Lemma `10.23.1`; finite
-- presentation identifies localized `Hom` with `Hom` out of the localized module, and the owner
-- lemma `finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients` gives that
-- each `M_m` is a finite direct sum of principal quotients over `Localization.AtPrime m`. Apply
-- Lemma `15.125.1` locally to obtain the chapter's canonical split-data conclusion, then shrink
-- the indexing set to a finite subset because `M` is finite.
/-- Lemma 15.125.4: if every localization of `R` at a maximal ideal is a generalized valuation
ring, then every finitely presented `R`-module is a direct summand of a finite direct sum of
principal quotient modules `R ⧸ (fᵢ)`. -/
theorem finitelyPresented_module_directSummand_finite_directSum_principal_quotients_of_maximal_localizations_preValuationRing
    (hR : ∀ (m : Ideal R) (_ : m.IsMaximal), PreValuationRing (Localization.AtPrime m)) :
    ∃ (n : ℕ) (f : Fin n → R)
      (i : M →ₗ[R] (⨁ j : Fin n, R ⧸ principalIdeal (f j)))
      (s : (⨁ j : Fin n, R ⧸ principalIdeal (f j)) →ₗ[R] M),
      s.comp i = LinearMap.id := sorry

end

/-! ### Definition_15_125_5 (from Chap15) -/
universe u

/- Domain-style sampling:
- primary domain: elementary divisor domains and Smith normal form over commutative domains;
- sampled owner declarations:
  `IsBezout`,
  `Module.Basis.SmithNormalForm`,
  `Submodule.smithNormalForm`,
  `Submodule.exists_smith_normal_form_of_rank_eq`;
- source/core/bridge triage:
  `source-facing`: the ring property that every finite matrix over `R` admits an elementary-divisor
  diagonal form;
  `core/canonical`: mathlib's Smith-normal-form owner `Module.Basis.SmithNormalForm` for
  submodules of finite free modules over a PID, together with the canonical Bézout owner
  `IsBezout`;
  `bridge/view`: the explicit matrix predicate `Matrix.HasElementaryDivisorDiagonal` and the
  rectangular diagonal matrix `Matrix.smithNormalDiagonal`, which keep the source matrix language
  without introducing a second owner abstraction.
- primitive data: only the ring-level elementary-divisor property;
- derived API: the Bézout instance and the PID-to-elementary-divisor instance.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Definition 15.125.5 (1): a Bezout domain is the canonical mathlib property `IsBezout R`,
namely that every finitely generated ideal of `R` is principal. -/
#check IsBezout

end

namespace Matrix

variable {R : Type u}

/-- The rectangular diagonal matrix with diagonal entries `d` and all other entries equal to `0`.
-/
def smithNormalDiagonal [Zero R] {n m : ℕ} (d : Fin (Nat.min n m) → R) :
    Matrix (Fin n) (Fin m) R :=
  fun i j ↦ if hij : i.1 = j.1 ∧ i.1 < Nat.min n m then d ⟨i.1, hij.2⟩ else 0

/-- A matrix admits an elementary-divisor diagonal form if left and right multiplication by
invertible matrices turns it into a rectangular diagonal matrix whose diagonal entries form a
divisibility chain. -/
def HasElementaryDivisorDiagonal [CommRing R] {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) : Prop :=
  ∃ U : (Matrix (Fin n) (Fin n) R)ˣ, ∃ V : (Matrix (Fin m) (Fin m) R)ˣ,
    ∃ d : Fin (Nat.min n m) → R,
      (((U : Matrix (Fin n) (Fin n) R) * A) * (V : Matrix (Fin m) (Fin m) R)) =
        smithNormalDiagonal d ∧
      List.IsChain (· ∣ ·) (List.ofFn d)

end Matrix

section

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Definition 15.125.5: an elementary divisor domain is a domain such that every finite
rectangular matrix over `R` can be diagonalized by invertible left and right multipliers, with
diagonal entries forming a divisibility chain. -/
class IsElementaryDivisorDomain (R : Type u) [CommRing R] [IsDomain R] : Prop where
  hasElementaryDivisorDiagonal {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    A.HasElementaryDivisorDiagonal

-- Proof sketch: apply the elementary-divisor condition to the `1 × 2` matrix `[x y]`; the single
-- diagonal entry then generates the ideal `(x, y)`, showing that every two-generated ideal is
-- principal, hence `R` is Bézout by the standard mathlib characterization.
/-- An elementary divisor domain is a Bézout domain. -/
instance isBezout_of_isElementaryDivisorDomain [IsElementaryDivisorDomain R] : IsBezout R := sorry

-- Proof sketch: over a principal ideal domain, Smith normal form supplies the required
-- diagonalization data, and its diagonal coefficients satisfy the standard divisibility chain.
/-- Every principal ideal domain is an elementary divisor domain. -/
instance isElementaryDivisorDomain_of_isPrincipalIdealRing
    [IsPrincipalIdealRing R] : IsElementaryDivisorDomain R := sorry

end

/-! ### Lemma_15_125_6 (from Chap15) -/
universe u

/- 
Domain-style sampling:
- primary domain: Smith normal form over domains and the induced Bézout property of finitely
  generated ideals;
- sampled owner API:
  `Matrix.HasElementaryDivisorDiagonal`,
  `IsElementaryDivisorDomain`,
  `IsBezout`,
  `isBezout_of_isElementaryDivisorDomain`;
- best owner abstraction: the chapter owner for the source hypothesis is
  `IsElementaryDivisorDomain`, introduced in `Definition_15_125_5`, and the target conclusion is
  the canonical mathlib owner `IsBezout`;
- primitive vs. derived:
  the Smith-normal-form diagonalization data are primitive source-facing content already owned by
  `Definition_15_125_5`, while the Bézout-domain conclusion is derived API owned by the instance
  `isBezout_of_isElementaryDivisorDomain`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma asserting that every elementary divisor domain is Bézout;
  `core/canonical`: `IsElementaryDivisorDomain` and `IsBezout`;
  `bridge/view`: this file, which should reuse the upstream owner instance directly rather than
  duplicate the Smith-normal-form data and reprove the implication locally.

The previous local file rebuilt `smithDiagonal`, the diagonal-chain predicate, the elementary
divisor domain class, and the PID instance. Those are redundant primitive owners once
`Definition_15_125_5` exists, so the canonical refinement is direct recall of the upstream
instance.
-/

/- Lemma 15.125.6: every elementary divisor domain is a Bézout domain. This is exactly the
chapter instance `isBezout_of_isElementaryDivisorDomain`. -/
#check isBezout_of_isElementaryDivisorDomain

/-! ### Lemma_15_125_7 (from Chap15) -/
universe u v

section

-- Proof sketch: use the owner theorem `IsBezout.iff_span_pair_isPrincipal`. Any two elements of
-- the localization can be written as fractions, and each denominator becomes a unit, so the ideal
-- they generate agrees with the image of the corresponding two-generated ideal upstairs.
/-- Lemma 15.125.7: the localization of a Bezout ring, hence in particular of a Bezout domain, is
again Bezout. -/
theorem isBezout_localization
    (A : Type u) [CommRing A] [IsBezout A] (S : Submonoid A)
    (B : Type v) [CommRing B] [Algebra A B] [IsLocalization S B] :
    IsBezout B := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S y
  have hspan :
      Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B) =
        Ideal.map (algebraMap A B) (Ideal.span ({a, b} : Set A)) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact
          (IsLocalization.mk'_mem_map_algebraMap_iff S B
            (Ideal.span ({a, b} : Set A)) a s).2
            ⟨1, Submonoid.one_mem S, Ideal.subset_span (by simp)⟩
      · exact
          (IsLocalization.mk'_mem_map_algebraMap_iff S B
            (Ideal.span ({a, b} : Set A)) b t).2
            ⟨1, Submonoid.one_mem S, Ideal.subset_span (by simp)⟩
    · refine Ideal.map_le_iff_le_comap.2 ?_
      have ha : algebraMap A B a ∈
          Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B) := by
        exact IsLocalization.mk'_spec' B a s ▸
          (Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B)).mul_mem_left
            (algebraMap A B s) (Ideal.subset_span (by simp))
      have hb : algebraMap A B b ∈
          Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B) := by
        exact IsLocalization.mk'_spec' B b t ▸
          (Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B)).mul_mem_left
            (algebraMap A B t) (Ideal.subset_span (by simp))
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
  have hprincipal :
      (Ideal.map (algebraMap A B) (Ideal.span ({a, b} : Set A))).IsPrincipal :=
    Submodule.IsPrincipal.map_ringHom (algebraMap A B)
      (show (Ideal.span ({a, b} : Set A)).IsPrincipal by infer_instance)
  simpa [hspan] using hprincipal

end

section

-- Proof sketch: prime localizations are local by the owner API `IsLocalization.AtPrime.isLocalRing`;
-- combine that with the generic localized Bezout theorem above and use the canonical
-- valuation-ring owner instance on the canonical local ring `Localization.AtPrime p`.
/-- Every prime localization of a Bezout domain is a valuation ring. -/
theorem valuationRing_localizationAtPrime_of_isBezout
    (A : Type u) [CommRing A] [IsDomain A] [IsBezout A] (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := by
  letI : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_of_atPrime (Localization.AtPrime p) p
  letI : IsBezout (Localization.AtPrime p) :=
    isBezout_localization A p.primeCompl (Localization.AtPrime p)
  letI : IsLocalRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p) p
  infer_instance

end

/-! ### Lemma_15_125_8 (from Chap15) -/
open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: finitely presented modules over Bézout domains, their torsion submodules, and
  split decompositions into torsion and torsion-free parts;
- sampled owner declarations:
  `IsBezout`,
  `Submodule.torsion`,
  `Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)`,
  `nonempty_linearEquiv_quotient_torsionBy_prod_of_fittingIdeal_eq_principalIdeal`,
  `lequivProdOfRightSplitExact`,
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact`;
- best owner abstraction:
  this file is mostly `source-facing`, while the core owners are the Bézout property
  `IsBezout`, the canonical torsion submodule `Submodule.torsion`, and the chapter’s direct-sum
  product decomposition owner for split exact sequences, specialized here to the torsion
  short exact sequence; for part (4), the direct-summand surface should match the owner theorem
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact` by using a finite index
  type rather than a chosen `Fin n` encoding;
- primitive data vs. derived API:
  primitive data are the ambient Bézout domain and finitely presented module;
  derived API are the torsion-free quotient, the split product decomposition, and the retract of
  the torsion submodule into a finite direct sum of principal quotients indexed by a finite type,
  using the canonical quotient-torsion-free owner from Lemma `15.22.2` instead of a parallel
  local predicate.

Source/core/bridge triage:
- `source-facing`: the four assertions of Lemma `15.125.8`;
- `core/canonical`: `IsBezout`, `Submodule.torsion`, and the quotient torsion-free owner API from
  Lemma `15.22.2`, together with the split-exact product equivalence owner;
- `bridge/view`: the local-global retract theorem from Lemma `15.125.4`, specialized here to
  finitely presented modules over Bézout domains via Lemma `15.125.7`.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]

-- Proof sketch: reduce from an arbitrary free ambient module to a finite free one by choosing
-- finitely many basis vectors supporting a finite generating set of the submodule. Then argue by
-- induction on the rank, projecting to the last coordinate and using that a finitely generated
-- ideal in a Bézout domain is principal.
/-- Lemma 15.125.8 (1): every finite submodule of a free `R`-module is finite free. -/
theorem finite_submodule_free_of_free_over_isBezout
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Free R F]
    (N : Submodule R F) [Module.Finite R N] :
    Module.Free R N := sorry

section

variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

-- Proof sketch: apply Lemma `15.125.4` using Lemma `15.125.7` to realize `M` as a direct summand
-- of a finite direct sum of cyclic quotients. The quotient by `Submodule.torsion R M` is then a
-- finite torsion-free summand of a free module; the torsion-free input is the canonical owner
-- `Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)` from Lemma `15.22.2`, so part (1) gives
-- freeness without introducing a local wrapper for torsion-freeness.
/-- Lemma 15.125.8 (2): for a finitely presented `R`-module `M`, the quotient by its torsion
submodule is a finite free `R`-module. -/
theorem torsion_quotient_free_of_finitelyPresented_over_isBezout :
    Module.Free R (M ⧸ Submodule.torsion R M) := sorry

-- Proof sketch: the quotient `M ⧸ Submodule.torsion R M` is free by part (2), hence projective.
-- Apply the canonical splitting of the short exact sequence
-- `0 → Submodule.torsion R M → M → M ⧸ Submodule.torsion R M → 0`; a section of the quotient map
-- then gives the source-facing product decomposition via the canonical split-exact owner
-- `lequivProdOfRightSplitExact`.
/-- Lemma 15.125.8 (3): a finitely presented `R`-module splits as the product of its torsion-free
quotient and its torsion submodule. -/
theorem nonempty_linearEquiv_quotient_torsion_prod_of_finitelyPresented_over_isBezout :
    Nonempty (M ≃ₗ[R] (M ⧸ Submodule.torsion R M) × Submodule.torsion R M) := sorry

-- Proof sketch: again start from the direct-summand presentation of Lemma `15.125.4`. Applying
-- the torsion functor to the finite direct sum `⨁ i, R ⧸ (f i)` identifies `Submodule.torsion R M`
-- with a direct summand of that torsion module; because each `f i` is nonzero in a domain, the
-- whole direct sum is already torsion, so the torsion submodule is a direct summand of a module of
-- the required form. The public surface keeps the finite-index owner level, quantifying over a
-- finite type `ι` rather than choosing a specific encoding `Fin n`.
/-- Lemma 15.125.8 (4): the torsion submodule of a finitely presented `R`-module is a direct
summand of a finite direct sum of cyclic modules `R ⧸ (fᵢ)` with `fᵢ ≠ 0`. -/
theorem torsion_directSummand_finite_directSum_principal_quotients_of_finitelyPresented_over_isBezout :
    ∃ (ι : Type v) (_ : Fintype ι) (f : ι → R),
      (∀ i, f i ≠ 0) ∧
        ∃ (i : Submodule.torsion R M →ₗ[R] (⨁ j : ι, R ⧸ principalIdeal (f j)))
          (s : (⨁ j : ι, R ⧸ principalIdeal (f j)) →ₗ[R] Submodule.torsion R M),
            s.comp i = LinearMap.id := sorry

end

end

/-! ### Lemma_15_125_9 (from Chap15) -/
open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: finitely generated modules over principal ideal domains and their structure
  theorem;
- sampled owner declarations:
  `Module.equiv_free_prod_directSum`,
  `principalIdeal`,
  `Fintype.equivFin`,
  `DirectSum.lequivCongrLeft`;
- best owner abstraction: this item is `source-facing`, while the canonical owner for the
  decomposition is mathlib's `Module.equiv_free_prod_directSum`;
- primitive data vs. derived API:
  primitive data is the PID `R` and the finite `R`-module `M`;
  derived API is the finite index type `ι`, the family `f : ι → R` of nonzero elements, and the
  resulting linear equivalence to a free part times cyclic principal quotients;

Source/core/bridge triage:
- `source-facing`: the textbook existence statement with finitely many cyclic summands
  `R ⧸ principalIdeal (f i)`;
- `core/canonical`: `Module.equiv_free_prod_directSum`;
- `bridge/view`: the sampled `Fintype.equivFin` and `DirectSum.lequivCongrLeft` reindexing bridge
  was rejected as non-canonical for the public statement; only the quotient ideals are rewritten
  through the chapter owner `principalIdeal`. -/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: apply the stronger mathlib structure theorem
-- `Module.equiv_free_prod_directSum`. It gives a decomposition of `M` as a free part together
-- with a finite direct sum of cyclic modules `R ⧸ R ∙ p_i ^ e_i` for irreducible `p_i`. Then set
-- `f i = p_i ^ e_i`; these are nonzero because `R` is a domain.
/-- Lemma 15.125.9: every finite module over a principal ideal domain is linearly isomorphic to a
free finite-rank module times a finite direct sum of cyclic quotient modules `R ⧸ (fᵢ)` with
`fᵢ ≠ 0`. -/
lemma finite_module_exists_linearEquiv_free_prod_directSum_principal_quotients :
    ∃ (r : ℕ) (ι : Type u) (_ : Fintype ι) (f : ι → R),
      (∀ i, f i ≠ 0) ∧
        Nonempty (M ≃ₗ[R] (Fin r →₀ R) × ⨁ i : ι, R ⧸ principalIdeal (f i)) := by
  classical
  obtain ⟨r, ι, hι, p, hp, e, hM⟩ := Module.equiv_free_prod_directSum R M
  let f : ι → R := fun i ↦ p i ^ e i
  refine ⟨r, ι, hι, f, ?_, ?_⟩
  · intro i
    dsimp [f]
    exact pow_ne_zero _ (hp _).ne_zero
  · simpa [f, principalIdeal] using hM

end

/-! ### Lemma_15_125_10 (from Chap15) -/
universe u

/- Domain-style sampling:
- primary domain: unimodular rows over Bézout domains and their completion to invertible matrices;
- sampled owner declarations:
  `IsBezout`,
  `span_range_eq_top_iff_surjective_fintypeLinearCombination`,
  `Matrix.GL`;
- best owner abstraction: `Matrix.GL (Fin (n + 1)) R` for the completion object, with
  `Fintype.linearCombination R f` as the canonical core map behind the unit-ideal hypothesis;
- primitive data: a finite row `f : Fin (n + 1) → R`;
- derived API: the condition that `f` generates the unit ideal and the resulting invertible
  completion with first row `f`, indexed canonically by `0`, together with the operational
  surjective-`linearCombination` bridge;
- source/core/bridge triage:
  `source-facing`: completion of a unimodular row to an invertible square matrix;
  `core/canonical`: `Matrix.GL (Fin (n + 1)) R` and `Fintype.linearCombination R f`;
  `bridge/view`: `Ideal.span (Set.range f) = ⊤`, via
  `span_range_eq_top_iff_surjective_fintypeLinearCombination`. -/

section

open Matrix

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]

-- Proof sketch: argue by induction on `n`. For `n = 1`, the hypothesis that `f 0` generates the
-- unit ideal says `f 0` is a unit, so the `1 × 1` matrix `[f 0]` is invertible. For `n > 1`,
-- replace the first `n - 1` entries by a single generator of their ideal using the Bézout
-- property, apply the induction hypothesis to complete that shorter row, and then compose with a
-- `2 × 2` unimodular block sending `(f, fₙ)` to a row generating `1`.
/-- Lemma 15.125.10: over a Bézout domain, any finite row generating the unit ideal is the first
row of an invertible square matrix. -/
theorem exists_invertible_matrix_first_row_eq_of_span_range_eq_top
    {n : ℕ} (f : Fin (n + 1) → R) (hunit : Ideal.span (Set.range f) = ⊤) :
    ∃ A : GL (Fin (n + 1)) R, A 0 = f := sorry

/-- Canonical `Fintype.linearCombination` bridge view of
`exists_invertible_matrix_first_row_eq_of_span_range_eq_top`. -/
theorem exists_invertible_matrix_first_row_eq_of_surjective_fintypeLinearCombination
    {n : ℕ} (f : Fin (n + 1) → R)
    (hsurj : Function.Surjective (Fintype.linearCombination R f)) :
    ∃ A : GL (Fin (n + 1)) R, A 0 = f := by
  apply exists_invertible_matrix_first_row_eq_of_span_range_eq_top
  simpa using (span_range_eq_top_iff_surjective_fintypeLinearCombination R f).2 hsurj

end
