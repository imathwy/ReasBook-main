import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.ZeroFiberPrimeClassification
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeClassification
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeFiberSeparators
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeScalarWitness

open scoped Representation

noncomputable section

universe v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
local notation "RegularPrimeIndex" =>
  Σ p : Nat.Primes, NonzeroResidualCharacteristicMaximalIdeal A p ×
    PRegularGaloisPowerClass ΓK p

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]
-- Serre's standing §12.7 arithmetic hypothesis: `A` is the integral closure of `ℤ` in its
-- fraction field `K`. This is the faithful setting of the exercise (cf. `Lemma_12_12_7_4`).
variable [IsIntegralClosure A ℤ K]

omit [IsDomain A] in
/-- Helper for Exercise 12-12.7-8: any nonzero prime of the coefficient ring `A` is some
residual-characteristic maximal ideal. This isolates the coefficient-ring split used in the
nonzero branch of the spectrum classification. -/
private theorem nonzero_primeSpectrum_eq_residual_maximal_local
    (q : PrimeSpectrum A) (hq : q.asIdeal ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
      M.1.asIdeal = q.asIdeal := by
  -- A nonzero prime is maximal because every nonzero quotient of `A` is finite.
  letI : q.asIdeal.IsMaximal :=
    Ring.HasFiniteQuotients.maximalOfPrime hq
  have hfiniteQuot : Finite (A ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient hq
  letI : Finite (A ⧸ q.asIdeal) := hfiniteQuot
  -- The residue field is therefore finite, hence has prime characteristic.
  have hfiniteResidue : Finite q.asIdeal.ResidueField := by
    exact Finite.of_surjective
      (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).surjective
  letI : Finite q.asIdeal.ResidueField := hfiniteResidue
  let p : Nat.Primes :=
    ⟨ringChar q.asIdeal.ResidueField, CharP.prime_ringChar q.asIdeal.ResidueField⟩
  let M : NonzeroResidualCharacteristicMaximalIdeal A p :=
    ⟨⟨q.asIdeal, inferInstance⟩, hq, by
      simpa [p] using
        (inferInstance : CharP q.asIdeal.ResidueField (ringChar q.asIdeal.ResidueField))⟩
  -- The packaged maximal ideal is definitionally the original prime.
  exact ⟨p, M, rfl⟩

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: the surjective-spectrum reduction.  For a *surjective* ring
hom `f`, the induced `PrimeSpectrum.comap f` is surjective as soon as `ker f` is contained in the
nilradical (its range is `zeroLocus (ker f)`, and `ker f ≤ nilradical` makes that all of the
spectrum). -/
private theorem comap_surjective_of_ker_le_nilradical {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (hk : RingHom.ker f ≤ nilradical R) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  intro P
  have hmem : P ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective _ f hf, PrimeSpectrum.mem_zeroLocus]
    intro x hx
    exact nilradical_le_prime P.asIdeal (hk hx)
  exact hmem

/-- Helper for Exercise 12-12.7-8: the canonical map `R_K(G)-side → fiber over `M`` (the right
inclusion `s ↦ 1 ⊗ s` of the tensor product `κ(M) ⊗_A (A ⊗ R_K(G))`) is surjective, because the
residue map `A ↠ κ(M)` is surjective and lets every scalar of `κ(M)` be absorbed into the right
factor. -/
private theorem regular_fiber_includeRight_surjective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Surjective
      (Algebra.TensorProduct.includeRight (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) := by
  haveI : M.1.asIdeal.IsMaximal := M.1.isMaximal
  have hAres : Function.Surjective (algebraMap A M.1.asIdeal.ResidueField) := by
    have h1 := (Ideal.bijective_algebraMap_quotient_residueField M.1.asIdeal).surjective
    have h2 := Ideal.Quotient.mk_surjective (I := M.1.asIdeal)
    have hcomp : (algebraMap A M.1.asIdeal.ResidueField)
        = (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField).comp
            (Ideal.Quotient.mk M.1.asIdeal) := rfl
    rw [hcomp, RingHom.coe_comp]; exact h1.comp h2
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul b s =>
      obtain ⟨r, rfl⟩ := hAres b
      refine ⟨algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) r * s, ?_⟩
      rw [Algebra.TensorProduct.includeRight_apply, ← Algebra.smul_def,
        ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [map_add]⟩

/-- Helper for Exercise 12-12.7-8: if Serre's fixed-fiber evaluator vanishes on `1 ⊗ s`, then the
underlying owner value `s g` lies in `M` for **every** `g ∈ G` (not just `p`-regular ones).  The
`p`-regular vanishing comes from `regular_fiber_eval_family_includeRight_zero_iff`; it is globalized
to all of `G` through Lemma 12-12.7-4's `p'`-component congruence
`characterValueSubMemPrimeIdealOverPrimeOfPRegularComponent`
(`s g ≡ s (s_{p'}) mod M`, valid because `M` lies over `(p)`). -/
private theorem regular_fiber_includeRight_values_in_maximal
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (s : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (h0 : regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
        (Algebra.TensorProduct.includeRight (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) s) = 0) :
    ∀ g : G, ∃ a : A, a ∈ M.1.asIdeal ∧ algebraMap A K a = (s : G → K) g := by
  classical
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  haveI : M.1.asIdeal.IsMaximal := M.1.isMaximal
  haveI : NumberField K := NumberField.of_intermediateField K
  haveI : IsIntegrallyClosed A :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (K := K)).mpr
      (IsIntegrallyClosedIn.of_isIntegralClosure ℤ)
  have hvanReg : ∀ x : {x : G // IsPRegular p x},
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = (s : G → K) x.1 := by
    intro x
    have hzc : (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
        (Algebra.TensorProduct.includeRight (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) s))
          (pRegularGaloisPowerClassMk ΓK p x) = 0 := by rw [h0]; rfl
    exact (regular_fiber_eval_family_includeRight_zero_iff (A := A) (K := K) (G := G) (p := p) M
      (pRegularGaloisPowerClassMk ΓK p x) s).mp hzc x rfl
  have hs_mem : (s : G → K) ∈ A ⊗R[K](G) := s.2
  set Q : PrimeSpectrum A := ⟨M.1.asIdeal, inferInstance⟩ with hQdef
  have hpspan : Ideal.span ({(p : A)} : Set A) ≤ Q.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact (Ideal.algebraMap_residueField_eq_zero (I := M.1.asIdeal) (x := (p : A))).mp
      (by simpa using M.2.2.cast_eq_zero)
  intro g
  obtain ⟨a, ha⟩ := hvanReg ⟨pRegularComponent (p : ℕ) g,
    isPRegular_pRegularComponent (p := (p : ℕ)) g⟩
  obtain ⟨q, hq⟩ := characterValueSubMemPrimeIdealOverPrimeOfPRegularComponent
    (K := K) (A := A) (p := (p : ℕ)) hs_mem g Q hpspan
  exact ⟨a.1 + q.1, M.1.asIdeal.add_mem a.2 q.2, by rw [map_add, ha, hq]; ring⟩

/-- Helper for Exercise 12-12.7-8: the minimal-polynomial nilpotency step.  An owner `s` all of
whose values lie in `M` becomes nilpotent in the fiber over `M`: the function
`∏_{g} (s - s g)` vanishes identically on `G`, hence is `0` in `A ⊗ R_K(G)`; mapping into the fiber
turns each constant `s g` (which lies in `M`) into `0`, so `(1 ⊗ s) ^ |G| = 0`.  This is exactly
Serre's observation that mod-`M` the character ring is supported on the `p`-regular classes up to
nilpotents — proved here by elementary means, with no modular character-count input. -/
private theorem regular_fiber_includeRight_isNilpotent
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (s : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (aG : G → A) (haG_mem : ∀ g, aG g ∈ M.1.asIdeal)
    (haG_val : ∀ g, algebraMap A K (aG g) = (s : G → K) g) :
    IsNilpotent
      (Algebra.TensorProduct.includeRight (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) s) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI : M.1.asIdeal.IsMaximal := M.1.isMaximal
  set ι := Algebra.TensorProduct.includeRight
      (R := A) (A := M.1.asIdeal.ResidueField)
      (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) with hι
  refine ⟨Fintype.card G, ?_⟩
  have hinj : Function.Injective
      ((characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G).val) :=
    fun a b h => Subtype.ext h
  -- The honest minimal-polynomial product vanishes already in the owner ring.
  have hprodS : (∏ g : G,
      (s - algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) (aG g)))
        = 0 := by
    apply hinj
    rw [map_prod, map_zero]
    funext g0
    rw [Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ g0)
    have he : (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G).val
          (s - algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) (aG g0))
          g0
        = (s : G → K) g0 - algebraMap A K (aG g0) := by
      rw [map_sub, AlgHom.commutes]; rfl
    rw [he, haG_val g0, sub_self]
  -- Each constant `aG g ∈ M` maps to `0` in the fiber.
  have hz : ∀ g : G,
      ι (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) (aG g)) = 0 := by
    intro g
    rw [ι.commutes (aG g), Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
      TensorProduct.smul_tmul',
      show (aG g) • (1 : M.1.asIdeal.ResidueField) = 0 from by
        rw [← Algebra.algebraMap_eq_smul_one]
        exact (Ideal.algebraMap_residueField_eq_zero (I := M.1.asIdeal) (x := aG g)).mpr
          (haG_mem g),
      TensorProduct.zero_tmul]
  have himg : ι (∏ g : G,
      (s - algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) (aG g)))
        = 0 := by rw [hprodS, map_zero]
  rw [map_prod] at himg
  have hfac : ∀ g : G,
      ι (s - algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) (aG g))
        = ι s := by
    intro g; rw [map_sub, hz g, sub_zero]
  simp only [hfac] at himg
  rw [Finset.prod_const, Finset.card_univ] at himg
  exact himg

/-- Serre's modular character-count theorem (Brauer), spectrum form for Exercise 12-12.7-8.

The canonical fixed-fiber evaluator
`regular_fiber_eval_family_algHom M : Fiber ↠ (p-regular Γ_K-classes → κ(M))`
is a *surjective* ring hom (`regular_fiber_eval_family_surjective_from_separators`), but it is
**not** injective once `p ∣ |G|`: the fiber is a finite (Artinian) `κ(M)`-algebra of rank equal to
the number of *all* `Γ_K`-power classes, while the target has dimension equal to the number of
`p`-*regular* `Γ_K`-power classes (strictly fewer when `p`-singular classes exist).  So the fiber is
genuinely non-reduced.  Nevertheless its *prime/maximal spectrum* is still indexed exactly by the
`p`-regular `Γ_K`-classes — the nilpotents add no new primes.  Equivalently the induced spectrum map
`PrimeSpectrum.comap (eval family)` is **surjective**.

This is the spectrum form of Serre's modular character-count statement.  It is proved here directly
(no Chapter 18 / Brauer-count input): since the evaluator is surjective, it suffices to show its
kernel sits inside the nilradical of the (Artinian) fiber.  An element `1 ⊗ s` of the kernel has
`s` vanishing modulo `M` on every `p`-regular class; Lemma 12-12.7-4's `p'`-component congruence
(`s g ≡ s (s_{p'}) mod M`, valid because `M` lies over `(p)`) propagates this to **all** `g ∈ G`,
and then the minimal polynomial `∏_g (T - s g) ≡ T^{|G|} mod M` forces `(1 ⊗ s)^{|G|} = 0`.  So the
nilpotents add no new primes and the comap is surjective.  The injective half of the correspondence
(each `p`-regular class yields a distinct prime of the fiber) is also proved unconditionally below
from surjectivity of the evaluator. -/
theorem regular_fiber_eval_family_comap_surjective
    [IsIntegralClosure A ℤ K]
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Surjective
      (PrimeSpectrum.comap
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom) := by
  classical
  -- Serre's fixed-fiber evaluator is surjective.
  have hsurjf : Function.Surjective
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M) :=
    regular_fiber_eval_family_surjective_from_separators (A := A) (K := K) (G := G) M
  have hsurjR : Function.Surjective
      ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom) := by
    intro y; obtain ⟨x, hx⟩ := hsurjf y; exact ⟨x, hx⟩
  -- It suffices to show the kernel is contained in the nilradical.
  have hker : RingHom.ker (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
      ≤ nilradical
        (M.1.asIdeal.Fiber (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) := by
    intro ξ hξ
    -- Write `ξ = 1 ⊗ s` and read off vanishing of `s` modulo `M` on all `p`-regular classes.
    obtain ⟨s, rfl⟩ :=
      regular_fiber_includeRight_surjective (A := A) (K := K) (G := G) M ξ
    have hf0 : regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
        (Algebra.TensorProduct.includeRight (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) s) = 0 := by
      simpa using RingHom.mem_ker.mp hξ
    rw [mem_nilradical]
    -- Globalize to all of `G` (Lemma 12-12.7-4 congruence), then conclude by minimal-polynomial
    -- nilpotency.
    choose aG haG_mem haG_val using
      regular_fiber_includeRight_values_in_maximal (A := A) (K := K) (G := G) M s hf0
    exact regular_fiber_includeRight_isNilpotent (A := A) (K := K) (G := G)
      M s aG haG_mem haG_val
  exact comap_surjective_of_ker_le_nilradical _ hsurjR hker

/-- Helper for Exercise 12-12.7-8: distinct `p`-regular `Γ_K`-classes give distinct primes of the
fixed fiber over `M`.  This injective half is unconditional: it follows purely from surjectivity of
Serre's fixed-fiber evaluator (a surjective ring hom induces an injective `PrimeSpectrum.comap`)
together with the fact that the coordinate-evaluation primes of a finite product of fields are
pairwise distinct. -/
private theorem regular_fiber_eval_coordinate_injective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Injective
      (fun c : PRegularGaloisPowerClass ΓK p ↦
        PrimeSpectrum.comap
          (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
          (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c)) := by
  intro c₁ c₂ h
  have hcomap :
      regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₁ =
        regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₂ :=
    PrimeSpectrum.comap_injective_of_surjective
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
      (regular_fiber_eval_family_surjective_from_separators (A := A) (K := K) (G := G) M)
      h
  exact (regular_fiber_eval_prime_eq_iff (A := A) (K := K) (G := G) M c₁ c₂).mp hcomap

/-- Helper for Exercise 12-12.7-8: every prime of the fixed fiber over `M` is the
`PrimeSpectrum.comap` of a coordinate-evaluation prime indexed by a `p`-regular `Γ_K`-class.  This is
the completeness half; it consumes Serre's modular character-count theorem
(`regular_fiber_eval_family_comap_surjective`). -/
private theorem regular_fiber_eval_coordinate_surjective
    [IsIntegralClosure A ℤ K]
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Surjective
      (fun c : PRegularGaloisPowerClass ΓK p ↦
        PrimeSpectrum.comap
          (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
          (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c)) := by
  intro q
  obtain ⟨P, hP⟩ :=
    regular_fiber_eval_family_comap_surjective (A := A) (K := K) (G := G) (p := p) M q
  obtain ⟨c, hc⟩ :=
    exists_eq_comap_evalRingHom_bot_of_primeSpectrum_pRegularGaloisPowerClass
      (A := A) (K := K) (G := G) M P
  refine ⟨c, ?_⟩
  show
    PrimeSpectrum.comap
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
        (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c) = q
  rw [show regular_fiber_eval_prime (A := A) (K := K) (G := G) M c = P from hc]
  exact hP

/-- Helper for Exercise 12-12.7-8: the coordinate-evaluation map sending a `p`-regular `Γ_K`-class
to the corresponding prime of the fixed fiber over `M` is a bijection.  The injective half is
unconditional; the surjective half is Serre's modular character-count theorem. -/
private theorem regular_fiber_eval_coordinate_bijective
    [IsIntegralClosure A ℤ K]
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Bijective
      (fun c : PRegularGaloisPowerClass ΓK p ↦
        PrimeSpectrum.comap
          (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
          (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c)) :=
  ⟨regular_fiber_eval_coordinate_injective (A := A) (K := K) (G := G) M,
    regular_fiber_eval_coordinate_surjective (A := A) (K := K) (G := G) M⟩

/-- Route correction for Exercise 12-12.7-8: the *correct* spectrum-level replacement for the
(false) fiber algebra-isomorphism.  The fixed fiber over `M` is a finite non-reduced `κ(M)`-algebra,
but its **prime spectrum** is in bijection with the set of `p`-regular `Γ_K`-classes.  The bijection
sends a class `c` to the `PrimeSpectrum.comap` of the coordinate-evaluation prime; its inverse is
named here.

Only this equivalence's surjective half consumes Serre's modular character-count theorem; the
injective half is unconditional. -/
noncomputable def fixed_maximal_fiber_primeSpectrum_equiv_pRegularGaloisPowerClass
    [IsIntegralClosure A ℤ K]
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    PrimeSpectrum
        (M.1.asIdeal.Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃
        PRegularGaloisPowerClass ΓK p :=
  (Equiv.ofBijective _
    (regular_fiber_eval_coordinate_bijective (A := A) (K := K) (G := G) M)).symm

/-- Helper for Exercise 12-12.7-8: the ambient regular prime `P_{M,c}` attached to a `p`-regular
`Γ_K`-class `c`, built **directly** from Serre's (surjective) fixed-fiber evaluator — no fiber
identification is needed.  It is the transport to `A ⊗ R_K(G)` of the `PrimeSpectrum.comap` of the
coordinate-evaluation prime at `c`. -/
noncomputable def regular_fiber_coordinate_prime_of_eval
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    SpecAKG :=
  regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M
    (PrimeSpectrum.comap
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
      (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c))

/-- Helper for Exercise 12-12.7-8: the directly-constructed coordinate prime
`regular_fiber_coordinate_prime_of_eval M c` is Serre's intrinsic regular prime for the class `c`.
This is the existence ("easy") direction and is proved **unconditionally** from surjectivity of the
fixed-fiber evaluator — it does not consume the modular character-count theorem. -/
private theorem regular_fiber_coordinate_prime_of_eval_is_regularPrime
    [IsIntegralClosure A ℤ K]
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    IsGaloisPowerClassScalarExtensionRegularPrime K M c
      (regular_fiber_coordinate_prime_of_eval (A := A) (K := K) (G := G) M c) := by
  have hmem :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        f ∈ (regular_fiber_coordinate_prime_of_eval (A := A) (K := K) (G := G) M c).asIdeal ↔
          ∀ x : {x : G // IsPRegular p x},
            pRegularGaloisPowerClassMk ΓK p x = c →
              ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
    intro f
    -- Unfold the transported coordinate prime until membership becomes coordinate vanishing.
    change
      (Algebra.TensorProduct.includeRight
        (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) f) ∈
          Ideal.comap
            (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
            ((regular_fiber_eval_prime (A := A) (K := K) (G := G) M c).asIdeal) ↔
        ∀ x : {x : G // IsPRegular p x},
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    change
      ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M)
          ((Algebra.TensorProduct.includeRight
            (R := A) (A := M.1.asIdeal.ResidueField)
            (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)) ∈
          (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c).asIdeal ↔
        ∀ x : {x : G // IsPRegular p x},
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    change
      ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M)
            ((Algebra.TensorProduct.includeRight
              (R := A) (A := M.1.asIdeal.ResidueField)
              (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)) c = 0 ↔
        ∀ x : {x : G // IsPRegular p x},
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    exact
      regular_fiber_eval_family_includeRight_zero_iff
        (A := A) (K := K) (G := G) (p := p) M c f
  refine ⟨?_, ?_⟩
  · -- On scalars, the transported coordinate prime contracts back to the fixed maximal ideal `M`.
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx⟩ := pRegularGaloisPowerClassMk_surjective (G := G) ΓK p c
      rcases (hmem (algebraMap A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a)).1 ha x hx with
        ⟨b, hb⟩
      have hba : b.1 = a := by
        apply (IsFractionRing.injective A K)
        change algebraMap A K b.1 = algebraMap A K a
        simpa using hb
      simpa [hba] using b.2
    · intro ha
      refine (hmem (algebraMap A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a)).2 ?_
      intro x hx
      refine ⟨⟨a, ha⟩, ?_⟩
      change algebraMap A K a = algebraMap A K a
      rfl
  · -- The same membership calculation is Serre's intrinsic residue criterion at the class `c`.
    intro f
    exact hmem f

/-- Helper for Exercise 12-12.7-8: under the integral-closure hypothesis, every `p`-regular
`Γ_K`-class produces an ambient regular prime.  This existence ("easy") direction is now
**unconditional** (no modular character-count input): the witness is the directly-constructed
`regular_fiber_coordinate_prime_of_eval`. -/
private theorem exists_regular_prime_for_fixed_class_of_isIntegralClosure
    [IsIntegralClosure A ℤ K]
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    ∃ P : SpecAKG, IsGaloisPowerClassScalarExtensionRegularPrime K M c P := by
  -- Choose the ambient prime obtained directly from the (surjective) fixed-fiber evaluator at `c`.
  refine ⟨regular_fiber_coordinate_prime_of_eval (A := A) (K := K) (G := G) M c, ?_⟩
  exact
    regular_fiber_coordinate_prime_of_eval_is_regularPrime
      (A := A) (K := K) (G := G) (p := p) M c

/-- Helper for Exercise 12-12.7-8: under the integral-closure hypothesis, the completeness step:
every prime of `A ⊗ R_K(G)` lying over the fixed maximal ideal `M` is one of the regular primes
`P_{M,c}`.  This direction consumes Serre's modular character-count theorem (through
`regular_fiber_eval_coordinate_surjective`). -/
private theorem exists_intrinsic_regularPrime_of_comap_eq_fixed_maximal_of_isIntegralClosure
    [IsIntegralClosure A ℤ K]
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭 := by
  -- Classify every prime of the fixed fiber by a `p`-regular `Γ_K`-class, then transport back.
  have hclass :
      ∀ q :
        PrimeSpectrum
          (M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)),
        ∃ c : PRegularGaloisPowerClass ΓK p,
          IsGaloisPowerClassScalarExtensionRegularPrime K M c
            (regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M q) := by
    intro q
    obtain ⟨c, hc⟩ :=
      regular_fiber_eval_coordinate_surjective (A := A) (K := K) (G := G) M q
    refine ⟨c, ?_⟩
    -- Beta-reduce the surjectivity witness, then transport by `congrArg` (no expensive defeq
    -- through `primesOverOrderIsoFiber`).
    have hc' :
        PrimeSpectrum.comap
            (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
            (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c) = q := hc
    have hcoord :
        regular_fiber_coordinate_prime_of_eval (A := A) (K := K) (G := G) M c =
          regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M q :=
      congrArg (regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M) hc'
    rw [← hcoord]
    exact
      regular_fiber_coordinate_prime_of_eval_is_regularPrime
        (A := A) (K := K) (G := G) (p := p) M c
  -- The ambient prime over `M` is classified by first transporting it to the fixed fiber.
  exact
    exists_isGaloisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal_of_regularFiberClassification
      (A := A) (K := K) (G := G) M hclass
      h𝔭

section RegularPrime

variable {p : Nat.Primes}

private local instance : Fintype (PRegularGaloisPowerClass ΓK p) := Fintype.ofFinite _
private local instance : DecidableEq (PRegularGaloisPowerClass ΓK p) := Classical.decEq _

/-- Helper for Exercise 12-12.7-8: for each fixed residual-characteristic maximal ideal `M` and
`p`-regular `Γ_K`-class `c`, the coordinate kernel of Serre's fixed-fiber evaluator gives the
ambient regular prime attached to `(M, c)`. -/
private theorem exists_regular_prime_for_fixed_class
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    ∃ P : SpecAKG, IsGaloisPowerClassScalarExtensionRegularPrime K M c P := by
  -- In Serre's §12.7 setting `A` is the integral closure of `ℤ` in `K`, so the fixed-fiber
  -- evaluator is available: delegate to the integrality-based construction.
  exact exists_regular_prime_for_fixed_class_of_isIntegralClosure
    (A := A) (K := K) (G := G) M c

/-- Helper for Exercise 12-12.7-8: the regular prime `P_{M,c}` attached to a nonzero maximal
ideal `M` of residual characteristic `p` and a `p`-regular `Γ_K`-class `c`. -/
noncomputable def galoisPowerClassScalarExtensionRegularPrime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) : SpecAKG :=
  Classical.choose (exists_regular_prime_for_fixed_class (A := A) (K := K) (G := G) M c)

/-- Helper for Exercise 12-12.7-8: the regular prime `P_{M,c}` satisfies Serre's intrinsic
regular-prime criterion. -/
theorem galoisPowerClassScalarExtensionRegularPrime_spec
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    IsGaloisPowerClassScalarExtensionRegularPrime K M c
      (galoisPowerClassScalarExtensionRegularPrime K M c) := by
  -- The chosen owner is extracted directly from the coordinate-kernel existence statement.
  exact Classical.choose_spec
    (exists_regular_prime_for_fixed_class (A := A) (K := K) (G := G) M c)

/-- Helper for Exercise 12-12.7-8: Serre's intrinsic regular-prime predicate determines
`P_{M,c}` uniquely. -/
theorem
    eq_galoisPowerClassScalarExtensionRegularPrime_of_isGaloisPowerClassScalarExtensionRegularPrime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) {P : SpecAKG}
    (hP : IsGaloisPowerClassScalarExtensionRegularPrime K M c P) :
    P = galoisPowerClassScalarExtensionRegularPrime K M c := by
  -- Two primes with the same intrinsic residue test have the same ideal membership relation.
  apply PrimeSpectrum.ext
  ext f
  exact (hP.2 f).trans
    ((galoisPowerClassScalarExtensionRegularPrime_spec
      (A := A) (K := K) (G := G) M c).2 f).symm

/-- Helper for Exercise 12-12.7-8: once a prime over a fixed maximal ideal `M` is known to
satisfy Serre's intrinsic regular-prime predicate for some class `c`, it must already be the
chosen indexed prime `P_{M,c}`. -/
private theorem exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_exists_intrinsic_witness
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : SpecAKG}
    (h𝔭 :
      ∃ c : PRegularGaloisPowerClass ΓK p,
        IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  rcases h𝔭 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  -- The intrinsic predicate already pins down the chosen coordinate kernel uniquely.
  symm
  exact
    eq_galoisPowerClassScalarExtensionRegularPrime_of_isGaloisPowerClassScalarExtensionRegularPrime
      (A := A) (K := K) (G := G) M c hc

end RegularPrime


/-- Helper for Exercise 12-12.7-8: a prime of `A ⊗ R_K(G)` lying over a fixed nonzero maximal
ideal `M` should be one of the indexed regular primes `P_{M,c}`. This is the remaining fixed-fiber
classification step in the nonzero branch. -/
private theorem exists_intrinsic_regularPrime_of_comap_eq_fixed_maximal
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭 := by
  -- In Serre's §12.7 setting `A` is the integral closure of `ℤ` in `K`; delegate to the
  -- integrality-based fixed-maximal classification.
  exact exists_intrinsic_regularPrime_of_comap_eq_fixed_maximal_of_isIntegralClosure
    (A := A) (K := K) (G := G) M h𝔭

/-- Helper for Exercise 12-12.7-8: once a prime over a fixed maximal ideal `M` has been shown to
come from Serre's intrinsic regular-prime criterion, it coincides with the chosen indexed prime
`P_{M,c}`. -/
theorem exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  -- Once the intrinsic witness is available, uniqueness of the regular prime owner identifies 𝔭.
  exact
    exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_exists_intrinsic_witness
      (A := A) (K := K) (G := G) M
      (exists_intrinsic_regularPrime_of_comap_eq_fixed_maximal
        (A := A) (K := K) (G := G) M h𝔭)

end RegularPrime

/-- Helper for Exercise 12-12.7-8: a prime whose contraction to `A` is zero must be one of the
zero-residual primes `P₀,c`. This is the source-facing adapter to the already-proved bottom-fiber
classification. -/
private theorem exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot_local
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    ∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭 := by
  -- The zero branch is delegated entirely to the extracted bottom-fiber classification module.
  exact
    exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot
      (A := A) (K := K) (G := G) h𝔭

/-- The canonical indexing map sending a `Γ_K`-class `c` to `P₀,c` and a regular-prime index
`⟨p, M, c⟩` to `P_{M,c}`. -/
noncomputable abbrev galoisPowerClassScalarExtensionPrimeIdealAssociation :
    GaloisPowerClass ΓK ⊕ RegularPrimeIndex → SpecAKG :=
  Sum.elim (galoisPowerClassScalarExtensionZeroPrimeIdeal K)
    (fun i ↦
      match i with
      | ⟨_, M, c⟩ => galoisPowerClassScalarExtensionRegularPrime K M c)

local notation "primeIdealAssociation" =>
  (galoisPowerClassScalarExtensionPrimeIdealAssociation K :
    GaloisPowerClass ΓK ⊕ RegularPrimeIndex → SpecAKG)

/-- Exercise 12-12.7-8: in the arithmetic setting where `K` is the fraction field of the domain
`A`, every prime of `A ⊗ R_K(G)` is either one of the zero-residual primes `P₀,c` indexed by
`Γ_K`-classes or one of the regular primes `P_{M,c}` indexed by residual-characteristic maximal
ideals and `p`-regular `Γ_K`-classes. -/
theorem galoisPowerClassScalarExtensionPrimeIdealClassification
    (𝔭 : SpecAKG) :
    (∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭) ∨
      ∃ (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
        (c : PRegularGaloisPowerClass ΓK p),
        galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  by_cases h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥
  · -- The zero-contraction branch is already completely classified by the bottom-fiber API.
    exact Or.inl <|
      exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot_local
        (A := A) (K := K) (G := G) h𝔭
  · -- Otherwise the contraction is a nonzero prime of `A`, hence a residual-characteristic
    -- maximal ideal, and the remaining fixed-fiber step should classify `𝔭`.
    let q : PrimeSpectrum A :=
      PrimeSpectrum.comap
        (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) 𝔭
    have hq : q.asIdeal ≠ ⊥ := by
      simpa [q] using h𝔭
    obtain ⟨p, M, hM⟩ :=
      nonzero_primeSpectrum_eq_residual_maximal_local (A := A) q hq
    have hcontract :
        Ideal.comap
            (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
            𝔭.asIdeal = M.1.asIdeal := by
      simpa [q] using hM.symm
    obtain ⟨c, hc⟩ :=
      exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal
        (A := A) (K := K) (G := G) M hcontract
    exact Or.inr ⟨p, M, c, hc⟩

/-- Companion bridge for Exercise 12-12.7-8: surjectivity of the canonical indexing map is
equivalent to the explicit source-facing spectrum classification theorem. -/
theorem galoisPowerClassScalarExtensionPrimeIdealAssociation_surjective_iff :
    Function.Surjective primeIdealAssociation ↔
      ∀ 𝔭 : SpecAKG,
        (∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭) ∨
          ∃ (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
            (c : PRegularGaloisPowerClass ΓK p),
            galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  constructor
  · intro hsurj 𝔭
    obtain ⟨i, hi⟩ := hsurj 𝔭
    cases i with
    | inl c =>
        exact Or.inl ⟨c, hi⟩
    | inr i =>
        cases i with
        | mk p i =>
            cases i with
            | mk M c =>
                exact Or.inr ⟨p, M, c, hi⟩
  · intro hclass 𝔭
    rcases hclass 𝔭 with ⟨c, hc⟩ | ⟨p, M, c, hc⟩
    · exact ⟨Sum.inl c, hc⟩
    · exact ⟨Sum.inr ⟨p, M, c⟩, hc⟩

/-- Exercise 12-12.7-8, surjective indexing-map form: the canonical indexing map from the
disjoint union of the zero family and the regular family onto `Spec (A ⊗ R_K(G))` is surjective.
-/
theorem galoisPowerClassScalarExtensionPrimeIdealAssociation_surjective :
    Function.Surjective primeIdealAssociation := by
  rw [galoisPowerClassScalarExtensionPrimeIdealAssociation_surjective_iff]
  exact galoisPowerClassScalarExtensionPrimeIdealClassification (A := A) (K := K) (G := G)

end

end Representation
