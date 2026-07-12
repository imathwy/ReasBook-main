import Mathlib
import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v

noncomputable section

open Proposition_11_11_4_1
open Representation
open scoped Representation SubgroupInduction

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A] [Algebra A ℂ] [FaithfulSMul A ℂ]
variable [Finite G]

noncomputable local instance instFintypeG_p1142 : Fintype G := Fintype.ofFinite G

local notation "P0" => tensorCharacterRingZeroPrimeIdeal
local notation "Pm" => tensorCharacterRingRegularPrime

variable [IsDomain A] [Ring.HasFiniteQuotients A]
/- The arithmetic source hypothesis used throughout Proposition 11-11.4-2: the coefficient ring
`A` contains (the image in `ℂ` of) every `Nat.card G`-th root of unity.  This is the exact
hypothesis convention of Theorems 11-11.2-1 / 11-11.2-2, and it makes `A = 𝒪_{ℚ(ζ_{|G|})}` an
admissible coefficient ring.  It replaces the (jointly unsatisfiable) hypothesis
`IsIntegralClosure A ℤ ℂ` of the original development. -/
variable
  (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)))

omit [IsDomain A] [Ring.HasFiniteQuotients A] in
include hroots in
/-- Helper for Proposition 11-11.4-2: over Serre's arithmetic coefficient ring, distinct
zero-residual class primes are separated by an element of the tensor character ring lying in
exactly one of the two kernels. -/
private lemma zero_prime_separator_of_ne
    (c₁ c₂ : ConjClasses G) (hc : c₁ ≠ c₂) :
    ∃ χ : A ⊗R(G), χ ∈ (P0 A c₂).asIdeal ∧ χ ∉ (P0 A c₁).asIdeal := by
  -- The Frobenius weighted indicator at `n = 1` gives a tensor character supported exactly on the
  -- chosen conjugacy class once the `|G|`-th roots of unity descend to `A` (the source hypothesis
  -- `hroots`).
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c₁
  rcases Representation.weighted_adamsOperator_conjClassIndicator_lifts_to_tensorCharacterRing
      A 1 (ConjClasses.mk x) hroots with ⟨χ, hχ⟩
  have hχ₂eval :
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c₂ χ = 0 := by
    obtain ⟨y, hy⟩ := ConjClasses.mk_surjective c₂
    have hxy : ConjClasses.mk y ≠ ConjClasses.mk x := by
      intro h
      exact hc (h.symm.trans hy)
    -- Evaluate the weighted indicator at a representative of `c₂`;
    -- the class indicator vanishes there.
    rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G) c₂ χ hy]
    change (χ : G → ℂ) y = 0
    rw [hχ]
    have hyfin : IsOfFinOrder y := isOfFinOrder_of_finite y
    have hcard_ne : Nat.card G ≠ 0 := by
      exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
    have hindicator :
        (algebraMap A ℂ) ((ConjClasses.mk x).carrier.indicator 1 y : A) = 0 := by
      simp [Set.indicator, ConjClasses.mem_carrier_iff_mk_eq, hxy]
    simpa [Representation.adamsOperator, hyfin, ConjClasses.indicator, hcard_ne] using hindicator
  have hχ₁eval :
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk x) χ ≠ 0 := by
    -- Evaluating the same weighted indicator back on the chosen class `ConjClasses.mk x` returns
    -- the nonzero scalar `1`.
    rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
      (A := A) (G := G) (ConjClasses.mk x) χ rfl]
    change (χ : G → ℂ) x ≠ 0
    rw [hχ]
    have hxfin : IsOfFinOrder x := isOfFinOrder_of_finite x
    have hcard_ne : Nat.card G ≠ 0 := by
      exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
    have hindicator :
        (algebraMap A ℂ) (((ConjClasses.mk x).carrier.indicator 1 x : A)) ≠ 0 := by
      have hone : (algebraMap A ℂ) (1 : A) ≠ 0 := by
        exact_mod_cast one_ne_zero
      simp [Set.indicator, ConjClasses.mem_carrier_iff_mk_eq] at hone ⊢
    simpa [Representation.adamsOperator, hxfin, ConjClasses.indicator, hcard_ne] using hindicator
  refine ⟨χ, ?_, ?_⟩
  · -- Membership in `P₀,c₂` is exactly vanishing of the fixed-class complex evaluation.
    change tensorCharacterRingZeroPrimeIdealEval A c₂ χ = 0
    rw [tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex (A := A) (G := G) c₂]
    exact hχ₂eval
  · -- Non-membership in `P₀,c₁` is the corresponding nonvanishing statement.
    change tensorCharacterRingZeroPrimeIdealEval A (ConjClasses.mk x) χ ≠ 0
    rw [tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex
      (A := A) (G := G) (ConjClasses.mk x)]
    exact hχ₁eval

omit [IsDomain A] [Ring.HasFiniteQuotients A] in
include hroots in
/-- The zero-residual branch of Proposition 11-11.4-2: over Serre's coefficient ring, when the
maximal ideal is `0`, the
equality `P₀,c₁ = P₀,c₂` holds exactly for equal conjugacy classes `c₁ = c₂`. -/
theorem zero_residual_prime_eq_iff
    (c₁ c₂ : ConjClasses G) :
    P0 A c₁ = P0 A c₂ ↔
        c₁ = c₂ := by
  constructor
  · intro hP
    -- Route correction: the forward implication is reduced to a separator witness between the two
    -- zero kernels, so only the source-profile separation lemma remains open.
    by_contra hc
    obtain ⟨χ, hχ₂, hχ₁⟩ := zero_prime_separator_of_ne (A := A) (hroots := hroots) c₁ c₂ hc
    have hχ₁' : χ ∈ (P0 A c₁).asIdeal := by
      simpa [hP] using hχ₂
    exact hχ₁ hχ₁'
  · intro hc
    -- The reverse implication is just substitution of the conjugacy-class parameter.
    subst hc
    rfl

section RegularPrime

omit [IsDomain A] [Ring.HasFiniteQuotients A] in
/-- Helper for Proposition 11-11.4-2: the complex fixed-class evaluation at `ConjClasses.mk x`
is just the realized tensor character value at `x`. -/
private theorem tensorCharacterRingValueAtConjClassComplex_mk_eq_apply
    (χ : A ⊗R(G)) (x : G) :
    tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk x) χ =
      (χ : G → ℂ) x := by
  simpa [tensorCharacterRingToSubalgebra] using
    (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
      (A := A) (G := G) (ConjClasses.mk x) χ rfl)

include hroots in
/-- Helper for Proposition 11-11.4-2: after embedding into `ℂ`, the `A`-valued fixed-class
evaluation at `ConjClasses.mk x` is the realized tensor-character value at `x`. -/
private theorem algebraMapValueAtConjClassMk_eq_apply
    (χ : A ⊗R(G)) (x : G) :
    algebraMap A ℂ
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) χ) =
      (χ : G → ℂ) x := by
  -- Combine the `A`-valued evaluation bridge with the concrete representative computation.
  calc
    algebraMap A ℂ
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) χ) =
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk x) χ := by
        simpa using
          tensorCharacterRingValueAtConjClass_complex_eq
            (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) χ
    _ = (χ : G → ℂ) x :=
      tensorCharacterRingValueAtConjClassComplex_mk_eq_apply (A := A) (G := G) χ x

/-- Helper for Proposition 11-11.4-2: if an ambient tensor character realizes an induced class
function, then fixed-class complex evaluation at `ConjClasses.mk z` is just the induced value at
`z`. -/
private theorem inducedWitnessValueAtConjClassComplex_eq_inducedApply
    {L : Subgroup G} {f : L → ℂ} {ξ : A ⊗R(G)}
    (hξ_eval : (ξ : G → ℂ) = Ind[L](f)) (z : G) :
    tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk z) ξ =
      Ind[L](f) z := by
  -- Evaluate at the chosen representative `z`, then rewrite through the named induction witness.
  calc
    tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk z) ξ =
      (ξ : G → ℂ) z :=
      tensorCharacterRingValueAtConjClassComplex_mk_eq_apply (A := A) (G := G) ξ z
    _ = Ind[L](f) z := by
      simpa using congrFun hξ_eval z

include hroots in
/-- Helper for Proposition 11-11.4-2: if the complex fixed-class evaluation vanishes, then the
corresponding `A`-valued fixed-class evaluation lies in the residual maximal ideal `M`. -/
private theorem valueAtConjClass_mem_residual_of_complex_zero
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : ConjClasses G) (χ : A ⊗R(G))
    (hzero : tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c χ = 0) :
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ ∈ M.1.asIdeal := by
  let a : A := tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ
  have ha : algebraMap A ℂ a = ((0 : ℤ) : ℂ) := by
    change algebraMap A ℂ
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ) = ((0 : ℤ) : ℂ)
    calc
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ) =
        tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c χ := by
          simpa using
            tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G) c χ
      _ = (0 : ℂ) := hzero
      _ = ((0 : ℤ) : ℂ) := by simp
  change a ∈ M.1.asIdeal
  exact mem_residual_maximal_of_integer_value_dvd
    (A := A) (p := p) (M := M)
    (n := 0)
    ha
    (dvd_zero ((p : ℤ)))

include hroots in
/-- Helper for Proposition 11-11.4-2: Brauer's associated auxiliary character yields an ambient
tensor character that vanishes on `c₂` and has a fixed-class value at `c₁` equal to an integer
prime to `p`.

Faithful rework (no `IsIntegralClosure.equiv`): rather than transporting the Chapter 10 auxiliary
tensor (whose coefficients are arbitrary algebraic integers) along the now-unavailable equivalence
`(integralClosure ℤ ℂ) ≃ A`, we realize Brauer's *explicit* auxiliary function directly over `A`
from `hroots` (`brauerAux_mem_characterRingScalarExtension_of_roots`), induce it into `A ⊗ R(G)`,
and read off its value `n` at `x` (with `p ∤ n`) and its vanishing at `y` from the Chapter 10
support clauses. -/
private theorem regular_separator_evaluation_data
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c₁ c₂ : PRegularConjClass G p) (hc : c₁ ≠ c₂) :
    ∃ χ : A ⊗R(G), ∃ n : ℤ,
      χ ∈ (PrimeSpectrum.comap
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₂ : ConjClasses G)).toRingHom
          (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal ∧
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G) χ) =
        (n : ℂ) ∧
      ¬ (p : ℤ) ∣ n := by
  classical
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective (c₁ : ConjClasses G)
  obtain ⟨y, hy⟩ := ConjClasses.mk_surjective (c₂ : ConjClasses G)
  have hxreg : IsPRegular (p : ℕ) x := by
    exact c₁.2 x (ConjClasses.mem_carrier_iff_mk_eq.mpr hx)
  have hyreg : IsPRegular (p : ℕ) y := by
    exact c₂.2 y (ConjClasses.mem_carrier_iff_mk_eq.mpr hy)
  have hnotconj : ¬ IsConj y x := by
    intro hyx
    apply hc
    apply Subtype.ext
    calc
      (c₁ : ConjClasses G) = ConjClasses.mk x := hx.symm
      _ = ConjClasses.mk y := by
        simpa using (ConjClasses.mk_eq_mk_iff_isConj.mpr hyx).symm
      _ = (c₂ : ConjClasses G) := hy
  let P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)) :=
    Classical.choice
      (show Nonempty (Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G))) from Sylow.nonempty)
  let L : Subgroup G := associatedPElementarySubgroup (p : ℕ) x P
  -- Realize Brauer's explicit auxiliary function directly over `A` from `hroots`, then induce it
  -- from `L` into `A ⊗ R(G)` (no transport along the now-unavailable `IsIntegralClosure.equiv`).
  have hfmem :
      brauerAssociatedAuxiliaryFunction (p : ℕ) x P ∈ characterRingScalarExtension A L :=
    brauerAux_mem_characterRingScalarExtension_of_roots
      (A := A) (G := G) (hroots := hroots) p x P hxreg
  obtain ⟨ξ, _hξ_mem, hξ_eval⟩ :=
    induced_realization_mem_tensorCharacterRingInductionIdeal (A := A) (G := G) L hfmem
  -- The Chapter 10 support clauses give the value at `x` (an integer prime to `p`) and the
  -- vanishing at any `p`-regular element not conjugate to `x`.
  obtain ⟨ψ0, hψ0⟩ :=
    exists_tensor_character_realizing_brauerAssociatedAuxiliaryFunction (p := (p : ℕ)) x P hxreg
  obtain ⟨_hψ0_int, ⟨n, hnval, hndiv⟩, hψ0_zero⟩ :=
    associated_auxiliary_character_support_clauses_of_realization
      (p := (p : ℕ)) x P hxreg ψ0 hψ0
  rw [hψ0] at hnval hψ0_zero
  refine ⟨ξ, n, ?_, ?_, hndiv⟩
  · -- Vanishing of the induced witness at `c₂` forces the `A`-valued value into the residual
    -- maximal ideal `M`.
    have hy_zero :
        tensorCharacterRingValueAtConjClassComplex
            (A := A) (G := G) (c₂ : ConjClasses G) ξ = 0 := by
      calc
        tensorCharacterRingValueAtConjClassComplex
            (A := A) (G := G) (c₂ : ConjClasses G) ξ =
          tensorCharacterRingValueAtConjClassComplex
            (A := A) (G := G) (ConjClasses.mk y) ξ := by
              rw [← hy]
        _ = (ξ : G → ℂ) y :=
          tensorCharacterRingValueAtConjClassComplex_mk_eq_apply (A := A) (G := G) ξ y
        _ = Ind[L](brauerAssociatedAuxiliaryFunction (p : ℕ) x P) y := by
              simpa using congrFun hξ_eval y
        _ = 0 := hψ0_zero y hyreg hnotconj
    change tensorCharacterRingValueAtConjClass
        (A := A) (hroots := hroots) (G := G) (c₂ : ConjClasses G) ξ ∈ M.1.asIdeal
    exact valueAtConjClass_mem_residual_of_complex_zero
      (A := A) (hroots := hroots) (G := G) p M (c₂ : ConjClasses G) ξ hy_zero
  · -- The induced value at `c₁` is the Chapter 10 integer `n` (prime to `p`).
    calc
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G) ξ) =
        algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ) := by
            rw [← hx]
      _ = (ξ : G → ℂ) x :=
        algebraMapValueAtConjClassMk_eq_apply (A := A) (hroots := hroots) (G := G) ξ x
      _ = Ind[L](brauerAssociatedAuxiliaryFunction (p : ℕ) x P) x := by
            simpa using congrFun hξ_eval x
      _ = (n : ℂ) := hnval

include hroots in
/-- Helper for Proposition 11-11.4-2: distinct `p`-regular conjugacy classes are separated by a
tensor character whose fixed-class value is `0` at `c₂` and an integer prime to `p` at `c₁`, so
the two pullback primes over `M` cannot coincide. -/
private lemma regular_value_separator_of_ne
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c₁ c₂ : PRegularConjClass G p) (hc : c₁ ≠ c₂) :
    ∃ χ : A ⊗R(G),
      χ ∈ (PrimeSpectrum.comap
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₂ : ConjClasses G)).toRingHom
          (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal ∧
      χ ∉ (PrimeSpectrum.comap
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G)).toRingHom
          (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  obtain ⟨χ, n, hχ₂, hχ₁value, hndiv⟩ :=
    regular_separator_evaluation_data (A := A) (hroots := hroots) (G := G) p M c₁ c₂ hc
  refine ⟨χ, ?_, ?_⟩
  · -- The Brauer auxiliary witness already lands in the pullback prime at `c₂`.
    exact hχ₂
  · -- The supporting value at `c₁` is an integer prime to `p`, so it cannot belong to `M`.
    change tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G) χ ∉
      M.1.asIdeal
    exact not_mem_residual_maximal_of_integer_value_not_dvd
      (A := A) (p := p) (M := M) hχ₁value hndiv

include hroots in
/-- Helper for Proposition 11-11.4-2: equality of the regular-branch value-comap primes over a
fixed residual maximal ideal should already determine the underlying `p`-regular conjugacy class.
-/
private theorem regular_value_comap_eq_iff
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c₁ c₂ : PRegularConjClass G p) :
    PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G)).toRingHom
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
      PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₂ : ConjClasses G)).toRingHom
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) ↔
      c₁ = c₂ := by
  constructor
  · intro hcomap
    -- Route correction: distinct `p`-regular classes are already separated inside `A ⊗ R(G)`, so
    -- no regular-fiber transport is needed here.
    by_contra hc
    obtain ⟨χ, hχ₂, hχ₁⟩ := regular_value_separator_of_ne (A := A) (hroots := hroots) (G := G) p M c₁ c₂ hc
    have hχ₁' :
        χ ∈ (PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
      exact hcomap.symm ▸ hχ₂
    exact hχ₁ hχ₁'
  · intro hc
    -- Equal class parameters give definitionally equal fixed-class pullback primes.
    subst hc
    rfl

include hroots in
/-- Proposition 11-11.4-2 (2): for a fixed nonzero maximal ideal `M` of residual characteristic
`p`, the equality `P_{M,c₁} = P_{M,c₂}` holds exactly for equal `p`-regular conjugacy classes
`c₁ = c₂` in the arithmetic coefficient-ring setting where `Pm` is defined. -/
theorem regular_prime_eq_iff
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c₁ c₂ : PRegularConjClass G p) :
    tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M c₁ =
        tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M c₂ ↔
        c₁ = c₂ := by
  constructor
  · intro hP
    -- Route correction: rewrite Serre's regular owners as fixed-class pullbacks over `M`, then
    -- delegate uniqueness to the remaining comap-level blocker.
    have hcomap :
        PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
          PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₂ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
      calc
        PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₁ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
          tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M c₁ := by
            simpa using
              (value_comap_eq_tensorCharacterRingRegularPrime
                (A := A) (hroots := hroots) (G := G) p M (c₁ : ConjClasses G))
      _ = tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M c₂ := hP
      _ =
          PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c₂ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
            simpa using
              (value_comap_eq_tensorCharacterRingRegularPrime
                (A := A) (hroots := hroots) (G := G) p M (c₂ : ConjClasses G)).symm
    exact (regular_value_comap_eq_iff (A := A) (hroots := hroots) (G := G) p M c₁ c₂).mp hcomap
  · intro hc
    -- The reverse implication is substitution of the regular owner parameter.
    subst hc
    rfl

end RegularPrime

end
