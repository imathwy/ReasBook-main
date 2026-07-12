import StacksProject_2024.Chap15.Lemma_15_126_7
import StacksProject_2024.Chap15.Lemma_15_126_8.Index
import StacksProject_2024.Chap15.Lemma_15_3_3
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_52_5
import StacksProject_2024.Chap10.Lemma_10_156_2
import StacksProject_2024.Chap10.Lemma_10_79_1
import StacksProject_2024.Chap10.Lemma_10_112_1
import StacksProject_2024.Chap10.Lemma_10_112_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter IsLocalRing
open Ideal.Quotient (eq_zero_iff_mem)
open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Domain triage:
-- * primary domain: Hilbert-Samuel multiplicity bounds for parameter ideals in Noetherian local
--   rings;
-- * sampled owner API: `parameterIdeal`, `IsSystemOfParameters`,
--   `hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal_of_isSystemOfParameters`,
--   `minimalPrimes.finite_of_isNoetherianRing`;
-- * core/canonical: the chosen parameter family `g` together with its owner ideal
--   `parameterIdeal g`;
-- * source-facing: count the top-dimensional minimal primes `p` of `R`, equivalently those with
--   `ringKrullDim (R ⧸ p) = ringKrullDim R`, and compare that count with the canonical quotient
--   length of `R ⧸ parameterIdeal g`.
-- Primitive-vs-derived split:
-- * primitive data: the local Noetherian ring and the chosen family `g` with
--   `hg : IsSystemOfParameters g`;
-- * derived API: the top-dimensional minimal-prime subset cut out by the ambient dimension and
--   the resulting length bound in `ℕ∞`.

-- Proof sketch: filter the reduced ring by the product of its top-dimensional minimal-prime
-- quotients, so the cokernel has support of dimension `< d`. Hilbert-Samuel theory for the
-- parameter ideal of `g` shows that the leading coefficient of the length polynomial of the product
-- is at least the number of top-dimensional minimal primes, while the lower-dimensional error terms
-- do not affect the leading coefficient. Then apply Lemma `15.126.7`.
/-- Helper for Lemma 15.126.8: the source-facing set of top-dimensional minimal primes of `R`. -/
private abbrev topDimMinimalPrimes : Set (Ideal R) :=
  { p : Ideal R | p ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R }

omit [IsLocalRing R] in
/-- Helper for Lemma 15.126.8: the top-dimensional minimal primes form a finite set. -/
private theorem topDimMinimalPrimes_finite :
    (topDimMinimalPrimes (R := R)).Finite := by
  -- Forget the dimension cut and view the set as a subset of the finite set of all minimal primes.
  refine (minimalPrimes.finite_of_isNoetherianRing R).subset ?_
  intro p hp
  exact hp.1

omit [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.8: the nilradical of a local ring is a proper ideal. -/
private theorem nilradical_ne_top : nilradical R ≠ ⊤ := by
  -- The nilradical lies inside the Jacobson radical, which is the maximal ideal in a local ring.
  refine ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top ?_
  simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
    (nilradical_le_jacobson R : nilradical R ≤ Ring.jacobson R)

/-- Helper for Lemma 15.126.8: the reduced quotient of a local ring is again local. -/
private local instance reducedQuotient_isLocalRing :
    IsLocalRing (R ⧸ nilradical R) :=
  IsLocalRing.quotient (nilradical R) (nilradical_ne_top (R := R))

/-- Helper for Lemma 15.126.8: a parameter ideal admits an eventual Hilbert-Samuel `χ`-polynomial
with respect to the chosen system of parameters. -/
private theorem exists_parameterIdeal_hilbertSamuelChiPolynomial
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) :
    ∃ P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(parameterIdeal g) R n).toNat : ℚ) := by
  -- Apply the owner existence theorem to the parameter ideal, which is an ideal of definition.
  exact exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition R R hg.2

omit [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.8: each chosen parameter maps into the maximal ideal of the reduced
quotient. -/
private theorem reducedParameterFamily_mem_maximalIdeal
    {d : ℕ} (g : Fin d → maximalIdeal R) (i : Fin d) :
    Ideal.Quotient.mk (nilradical R) (g i : R) ∈ maximalIdeal (R ⧸ nilradical R) := by
  -- The quotient map is surjective, so it carries the maximal ideal onto the maximal ideal.
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (nilradical R))
    Ideal.Quotient.mk_surjective]
  exact Ideal.mem_map_of_mem _ (g i).property

/-- Helper for Lemma 15.126.8: the chosen parameter family descends termwise to the reduced
quotient `R ⧸ nilradical R`. -/
private abbrev reducedParameterFamily
    {d : ℕ} (g : Fin d → maximalIdeal R) :
    Fin d → maximalIdeal (R ⧸ nilradical R) :=
  fun i ↦
    ⟨Ideal.Quotient.mk (nilradical R) (g i : R),
      reducedParameterFamily_mem_maximalIdeal (R := R) g i⟩

/-- Helper for Lemma 15.126.8: quotienting the chosen parameter ideal by the nilradical identifies
its image with the parameter ideal of the descended family. -/
private theorem parameterIdeal_reducedParameterFamily_eq_map
    {d : ℕ} (g : Fin d → maximalIdeal R) :
    parameterIdeal (reducedParameterFamily (R := R) g) =
      Ideal.map (Ideal.Quotient.mk (nilradical R)) (parameterIdeal g) := by
  -- Rewrite both parameter ideals as spans of the underlying finite sets of generators.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span, Ideal.map_span]
  have hrange :
      (Ideal.Quotient.mk (nilradical R)) '' Set.range (fun i : Fin d ↦ (g i : R)) =
        Set.range fun i : Fin d ↦
          ((reducedParameterFamily (R := R) g i : maximalIdeal (R ⧸ nilradical R)) :
            R ⧸ nilradical R) := by
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g i, ⟨i, rfl⟩, rfl⟩
  rw [hrange]

/-- Helper for Lemma 15.126.8: quotienting by the nilradical does not change Krull dimension. -/
private theorem ringKrullDim_reducedQuotient_eq :
    ringKrullDim (R ⧸ nilradical R) = ringKrullDim R := by
  let π : R →+* (R ⧸ nilradical R) := Ideal.Quotient.mk (nilradical R)
  have hsurj : Function.Surjective (PrimeSpectrum.comap π) := by
    intro p
    let pzero : V((nilradical R : Set R)) := ⟨p, by
      -- Every prime ideal contains the nilradical.
      change nilradical R ≤ p.asIdeal
      exact nilradical_le_prime p.asIdeal⟩
    refine ⟨(Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (nilradical R)).symm pzero, ?_⟩
    -- Forget the zero-locus wrapper and use the quotient-spectrum homeomorphism formula.
    exact congrArg Subtype.val
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (nilradical R)).apply_symm_apply pzero)
  have hdim_le :
      ringKrullDim R ≤ ringKrullDim (R ⧸ nilradical R) := by
    -- The quotient map induces a surjective spectrum map because `V(nilradical) = Spec(R)`.
    exact ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing π hsurj
      (Or.inl inferInstance)
  have hquot_le :
      ringKrullDim (R ⧸ nilradical R) ≤ ringKrullDim R := by
    -- Quotients are integral over the source ring, so their dimension cannot increase.
    letI : Algebra R (R ⧸ nilradical R) := Ideal.Quotient.algebra (nilradical R)
    exact ringKrullDim_le_of_isIntegral (R := R) (S := R ⧸ nilradical R)
  exact le_antisymm hquot_le hdim_le

/-- Helper for Lemma 15.126.8: the descended parameter family is still a system of parameters on
the reduced quotient. -/
private theorem reduced_parameterIdeal_isSystemOfParameters
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) :
    IsSystemOfParameters (reducedParameterFamily (R := R) g) := by
  let π : R →+* (R ⧸ nilradical R) := Ideal.Quotient.mk (nilradical R)
  rw [isSystemOfParameters_iff]
  refine ⟨?_, ?_⟩
  · -- The reduced quotient has the same prime spectrum, hence the same Krull dimension.
    simpa [ringKrullDim_reducedQuotient_eq (R := R)] using hg.1
  · -- Transport the ideal-of-definition equality through the surjective quotient map.
    rw [Ideal.IsIdealOfDefinition] at hg ⊢
    apply Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
    rw [Ideal.comap_radical, parameterIdeal_reducedParameterFamily_eq_map (R := R) g,
      Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      RingHom.ker_eq_comap_bot, Ideal.comap_bot, hg.2, IsLocalRing.maximalIdeal_comap π]
    -- The nilradical contributes nothing new after taking radicals.
    refine le_antisymm ?_ (Ideal.le_radical)
    refine Ideal.radical_mono ?_
    refine sup_le le_rfl ?_
    simpa [nilradical, Ideal.zero_eq_bot] using
      (Ideal.radical_mono (show (⊥ : Ideal R) ≤ parameterIdeal g by bot_le))

/-- Helper for Lemma 15.126.8: the composite map from `R` to the reduced quotient modulo the
descended parameter ideal kills the original parameter ideal. -/
private theorem parameterIdeal_le_reducedParameterFamily_kernel
    {d : ℕ} (g : Fin d → maximalIdeal R) :
    parameterIdeal g ≤ RingHom.ker
      ((Ideal.Quotient.mk (parameterIdeal (reducedParameterFamily (R := R) g))).comp
        (Ideal.Quotient.mk (nilradical R))) := by
  intro r hr
  rw [RingHom.mem_ker]
  -- After identifying the descended parameter ideal with the mapped ideal, the vanishing is tautological.
  change Ideal.Quotient.mk (parameterIdeal (reducedParameterFamily (R := R) g))
      (Ideal.Quotient.mk (nilradical R) r) = 0
  rw [eq_zero_iff_mem, parameterIdeal_reducedParameterFamily_eq_map (R := R) g]
  exact Ideal.mem_map_of_mem _ hr

/-- Helper for Lemma 15.126.8: passing to the reduced quotient cannot increase the length of the
parameter-ideal quotient. -/
private theorem reduced_parameterIdeal_quotient_length_le
    {d : ℕ} (g : Fin d → maximalIdeal R) :
    Module.length (R ⧸ nilradical R)
        ((R ⧸ nilradical R) ⧸ parameterIdeal (reducedParameterFamily (R := R) g)) ≤
      Module.length R (R ⧸ parameterIdeal g) := by
  let I : Ideal R := parameterIdeal g
  let S : Type u := R ⧸ nilradical R
  let J : Ideal S := parameterIdeal (reducedParameterFamily (R := R) g)
  let φ : (R ⧸ I) →+* (S ⧸ J) :=
    Ideal.Quotient.lift I
      ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (nilradical R)))
      (parameterIdeal_le_reducedParameterFamily_kernel (R := R) g)
  have hφsurj : Function.Surjective φ := by
    -- Every quotient class in the reduced parameter quotient comes from the same representative upstairs.
    intro y
    refine Quotient.inductionOn' y ?_
    intro s
    refine Quotient.inductionOn' s ?_
    intro r
    refine ⟨Ideal.Quotient.mk I r, rfl⟩
  letI : Algebra (R ⧸ I) (S ⧸ J) := φ.toAlgebra
  let ψ : (R ⧸ I) →ₗ[R ⧸ I] (S ⧸ J) := {
    toFun := fun a ↦ algebraMap (R ⧸ I) (S ⧸ J) a
    map_add' := by
      intro a b
      simp
    map_smul' := by
      intro a b
      change algebraMap (R ⧸ I) (S ⧸ J) (a * b) =
        a • algebraMap (R ⧸ I) (S ⧸ J) b
      simpa [Algebra.smul_def] using
        (map_mul (algebraMap (R ⧸ I) (S ⧸ J)) a b) }
  have hψsurj : Function.Surjective ψ := by
    simpa [ψ] using hφsurj
  have hlen_source :
      Module.length (R ⧸ I) (S ⧸ J) ≤ Module.length (R ⧸ I) (R ⧸ I) :=
    Module.length_le_of_surjective (g := ψ) hψsurj
  have hlen_target :
      Module.length (R ⧸ I) (S ⧸ J) = Module.length (S ⧸ J) (S ⧸ J) :=
    Module.length_eq_of_surjective hφsurj
  have hlen_domain :
      Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) :=
    Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
  have htarget :
      Module.length S (S ⧸ J) = Module.length (S ⧸ J) (S ⧸ J) :=
    Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
  -- Compare lengths first over the intermediate quotient `R ⧸ parameterIdeal g`, then transport
  -- back to the original ring via the surjective quotient map.
  calc
    Module.length (R ⧸ nilradical R)
        ((R ⧸ nilradical R) ⧸ parameterIdeal (reducedParameterFamily (R := R) g)) =
      Module.length (S ⧸ J) (S ⧸ J) := by
        simpa [S, J] using htarget
    _ = Module.length (R ⧸ I) (S ⧸ J) := hlen_target.symm
    _ ≤ Module.length (R ⧸ I) (R ⧸ I) := hlen_source
    _ = Module.length R (R ⧸ I) := hlen_domain.symm
    _ = Module.length R (R ⧸ parameterIdeal g) := rfl

/-- Helper for Lemma 15.126.8: the Hilbert-Samuel multiplicity numerator attached to the parameter
ideal dominates the number of top-dimensional minimal primes in dimension `0`. -/
private theorem zeroDim_exists_parameterIdeal_multiplicity_numerator_ge_topDimMinimalPrimes
    (g : Fin 0 → maximalIdeal R) (hg : IsSystemOfParameters g) :
    ∃ P : Polynomial ℚ, ∃ e : ℕ,
      (topDimMinimalPrimes (R := R)).encard ≤ e ∧
        (∀ᶠ n : ℕ in atTop,
          P.eval (n : ℚ) = ((χ_(parameterIdeal g) R n).toNat : ℚ)) ∧
        P.leadingCoeff = (e : ℚ) / (Nat.factorial 0) := by
  have hzero : ringKrullDim R = 0 := hg.1
  have hparam : parameterIdeal g = ⊥ := by
    -- In dimension `0`, the empty parameter family generates the zero ideal.
    rw [parameterIdeal_eq_span]
    simp
  let e : ℕ := (Module.length R (R ⧸ (⊥ : Ideal R))).toNat
  let P : Polynomial ℚ := Polynomial.C (e : ℚ)
  have hP :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(parameterIdeal g) R n).toNat : ℚ) := by
    -- The Hilbert-Samuel `χ`-function for `⊥` is constant, so the eventual polynomial is constant.
    filter_upwards with n
    have hchiENat : χ_(⊥ : Ideal R) R n = Module.length R (R ⧸ (⊥ : Ideal R)) := by
      change Module.length R (R ⧸ ((⊥ : Ideal R) ^ (n + 1) • (⊤ : Submodule R R))) =
        Module.length R (R ⧸ (⊥ : Ideal R))
      have hsub : ((⊥ : Ideal R) ^ (n + 1) • (⊤ : Submodule R R)) = (⊥ : Ideal R) := by
        ext r
        simp
      rw [hsub]
    have hchi :
        ((χ_(⊥ : Ideal R) R n).toNat : ℚ) =
          ((Module.length R (R ⧸ (⊥ : Ideal R))).toNat : ℚ) := by
      simpa using congrArg (fun z : ℕ∞ ↦ (z.toNat : ℚ)) hchiENat
    rw [Polynomial.eval_C, hparam]
    simpa [P, e] using hchi.symm
  have hencard :
      (topDimMinimalPrimes (R := R)).encard ≤ e := by
    by_cases hsub : Subsingleton R
    · have hempty : topDimMinimalPrimes (R := R) = ∅ := by
        -- A subsingleton ring has no prime ideals, hence no top-dimensional minimal primes.
        ext p
        constructor
        · intro hp
          have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp.1
          exact False.elim (hp_prime.ne_top (Subsingleton.elim _ _))
        · simp
      have hlen_zero : Module.length R (R ⧸ (⊥ : Ideal R)) = 0 := by
        simp [Module.length_eq_zero]
      have he_zero : e = 0 := by
        simp [e]
      simpa [hempty, he_zero]
    · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hsub
      have hsubset : topDimMinimalPrimes (R := R) ⊆ ({maximalIdeal R} : Set (Ideal R)) := by
        intro p hp
        have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp.1
        have hmax_mem : maximalIdeal R ∈ minimalPrimes R := by
          -- In a zero-dimensional local ring, the maximal ideal is itself a minimal prime.
          rw [← Ideal.primeHeight_eq_zero_iff (I := maximalIdeal R)]
          exact_mod_cast
            (show ((maximalIdeal R).primeHeight : WithBot ℕ∞) = 0 by
              simpa [hzero] using IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := R))
        have hmax_min : Minimal Ideal.IsPrime (maximalIdeal R) := by
          simpa [minimalPrimes_eq_minimals] using hmax_mem
        have hp_le : p ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal_of_isPrime p
        have hmax_le : maximalIdeal R ≤ p := hmax_min.2 hp_prime hp_le
        exact Set.mem_singleton_iff.mpr (le_antisymm hp_le hmax_le)
      have hencard_le_one :
          (topDimMinimalPrimes (R := R)).encard ≤ 1 := by
        calc
          (topDimMinimalPrimes (R := R)).encard ≤ ({maximalIdeal R} : Set (Ideal R)).encard :=
            Set.encard_mono hsubset
          _ = 1 := Set.encard_singleton _
      have hfiniteLength : IsFiniteLength R R := by
        -- Zero-dimensional Noetherian local rings are Artinian, hence have finite length.
        have hdimle : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hzero
        have hArt : IsArtinianRing R :=
          (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, hdimle⟩
        exact (isArtinianRing_iff_isFiniteLength R).mp hArt
      have hlen_eq : Module.length R (R ⧸ (⊥ : Ideal R)) = Module.length R R :=
        by
          simpa using (((⊥ : Ideal R) : Submodule R R).quotEquivOfEqBot rfl).length_eq
      have hlen_ne_top : Module.length R (R ⧸ (⊥ : Ideal R)) ≠ ⊤ :=
        by
          rw [hlen_eq]
          exact Module.length_ne_top_iff.mpr hfiniteLength
      have hlen_pos : 0 < Module.length R (R ⧸ (⊥ : Ideal R)) := by
        rw [hlen_eq]
        simpa using (Module.length_pos_iff (R := R) (M := R)).2 inferInstance
      have hone_le_e : (1 : ℕ∞) ≤ e := by
        rw [show (e : ℕ∞) = Module.length R (R ⧸ (⊥ : Ideal R)) by
          exact ENat.coe_toNat hlen_ne_top]
        exact ENat.one_le_iff_ne_zero.mpr hlen_pos.ne'
      calc
        (topDimMinimalPrimes (R := R)).encard ≤ 1 := hencard_le_one
        _ ≤ e := hone_le_e
  refine ⟨P, e, hencard, hP, ?_⟩
  -- The constant polynomial has leading coefficient equal to its constant value.
  calc
    P.leadingCoeff = (e : ℚ) := by
      simpa [P] using (Polynomial.leadingCoeff_C (e : ℚ))
    _ = (e : ℚ) / (Nat.factorial 0) := by norm_num

/-- Helper for Lemma 15.126.8: the quotient by a prime ideal has Krull dimension equal to the
coheight of the corresponding point of `Spec R`. -/
private theorem prime_quotient_ringKrullDim_eq_coheight
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) = Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
  let x : PrimeSpectrum R := ⟨p, inferInstance⟩
  -- Rewrite the quotient spectrum as the upper interval above the prime `p`.
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici x := by
    ext q
    change p ≤ q.asIdeal ↔ x ≤ q
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici x).symm

/-- Helper for Lemma 15.126.8: if a prime quotient has the full ambient dimension, then the prime
is one of the top-dimensional minimal primes. -/
private theorem prime_mem_topDimMinimalPrimes_of_quotient_dim_eq_ringKrullDim
    {d : ℕ} (q : PrimeSpectrum R) (hqdim : ringKrullDim (R ⧸ q.asIdeal) = d)
    (hdim : ringKrullDim R = d) :
    q.asIdeal ∈ topDimMinimalPrimes (R := R) := by
  have hqmin : q.asIdeal ∈ minimalPrimes R := by
    obtain ⟨p, hpmin, hp_le_q⟩ :=
      Ideal.exists_minimalPrimes_le (J := q.asIdeal) (show (⊥ : Ideal R) ≤ q.asIdeal by bot_le)
    by_cases hp_eq_q : p = q.asIdeal
    · simpa [hp_eq_q] using hpmin
    · have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hpmin
      let xp : PrimeSpectrum R := ⟨p, hp_prime⟩
      have hp_lt_q : xp < q := by
        change p < q.asIdeal
        exact lt_of_le_of_ne hp_le_q hp_eq_q
      have hq_coheight_fin : Order.coheight q < ⊤ := by
        have hqdim_lt_top : ringKrullDim (R ⧸ q.asIdeal) < ⊤ := by
          rw [hqdim]
          simp
        rw [prime_quotient_ringKrullDim_eq_coheight (R := R) q.asIdeal] at hqdim_lt_top
        exact WithBot.coe_lt_coe.mp hqdim_lt_top
      have hstrict : ringKrullDim (R ⧸ q.asIdeal) < ringKrullDim R := by
        have hpdim_strict : ringKrullDim (R ⧸ q.asIdeal) < ringKrullDim (R ⧸ p) := by
          rw [prime_quotient_ringKrullDim_eq_coheight (R := R) q.asIdeal,
            prime_quotient_ringKrullDim_eq_coheight (R := R) p]
          exact WithBot.coe_lt_coe.mpr (Order.coheight_strictAnti hp_lt_q hq_coheight_fin)
        exact hpdim_strict.trans_le (ringKrullDim_quotient_le p)
      rw [hqdim, hdim] at hstrict
      exact False.elim (lt_irrefl (d : WithBot ℕ∞) hstrict)
  -- Package the minimal-prime conclusion together with the dimension equality.
  exact ⟨hqmin, by simpa [hdim] using hqdim⟩

/-- Helper for Lemma 15.126.8: localized surjectivity of the reduced diagonal excludes each
top-dimensional minimal prime from the support of its cokernel. -/
private theorem reduced_diagonal_cokernel_not_mem_support_top_dim_minimalPrime
    (q : minimalPrimes R) (hqdim : ringKrullDim (R ⧸ q.1) = ringKrullDim R) :
    (⟨q.1, Ideal.minimalPrimes_isPrime q.2⟩ : PrimeSpectrum R) ∉
      Module.support R
        (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
          LinearMap.range (reducedDiagonalLinearMap (R := R)))) := by
  -- The source proof first localizes at `q` and uses surjectivity of the reduced diagonal there.
  exact
    (localized_surjective_iff_not_mem_support_cokernel
      (reducedDiagonalLinearMap (R := R))
      (⟨q.1, Ideal.minimalPrimes_isPrime q.2⟩ : PrimeSpectrum R)).mp <| by
        simpa using localized_reduced_diagonal_surjective_at_minimalPrime (R := R) q

/-- Helper for Lemma 15.126.8: a support prime of the reduced-diagonal cokernel cannot have the
same quotient dimension as the ambient ring. -/
private theorem reduced_diagonal_cokernel_support_prime_quotient_dim_ne
    {d : ℕ} (q : PrimeSpectrum R)
    (hq :
      q ∈ Module.support R
        (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
          LinearMap.range (reducedDiagonalLinearMap (R := R)))))
    (hdim : ringKrullDim R = d) :
    ringKrullDim (R ⧸ q.asIdeal) ≠ d := by
  intro hqdim
  have hqtop :
      q.asIdeal ∈ topDimMinimalPrimes (R := R) :=
    prime_mem_topDimMinimalPrimes_of_quotient_dim_eq_ringKrullDim
      (R := R) q hqdim hdim
  let qmin : minimalPrimes R := ⟨q.asIdeal, hqtop.1⟩
  have hq_not_mem :
      q ∉ Module.support R
        (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
          LinearMap.range (reducedDiagonalLinearMap (R := R)))) := by
    -- Route correction: instead of trying to bound `supportDim` immediately, first rule out the
    -- top-dimensional primes from the support one by one.
    simpa using
      reduced_diagonal_cokernel_not_mem_support_top_dim_minimalPrime (R := R) qmin hqtop.2
  exact hq_not_mem hq

/-- Helper for Lemma 15.126.8: if a finite module has full ambient support dimension, then some
prime in its support has quotient dimension equal to the ambient dimension. -/
private theorem exists_support_prime_quotient_dim_eq_of_supportDim_eq_ringKrullDim
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {d : ℕ} (hsuppdim : Module.supportDim R N = d) (hdim : ringKrullDim R = d) :
    ∃ q : PrimeSpectrum R, q ∈ Module.support R N ∧ ringKrullDim (R ⧸ q.asIdeal) = d := by
  -- Realize the finite support dimension by a chain in `Supp(N)` of length exactly `d`.
  have hlt_succ : Module.supportDim R N < d + 1 := by
    simpa [hsuppdim]
  have hall_succ : ∀ l : LTSeries (Module.support R N), l.length < d + 1 := by
    simpa [Module.supportDim] using
      (Order.krullDim_lt_coe_iff (α := Module.support R N) (n := d + 1)).1 hlt_succ
  have hnot_lt : ¬ Module.supportDim R N < d := by
    simpa [hsuppdim]
  have hexists :
      ∃ l : LTSeries (Module.support R N), ¬ l.length < d := by
    by_contra hnone
    have hall : ∀ l : LTSeries (Module.support R N), l.length < d := by
      intro l
      by_contra hlt
      exact hnone ⟨l, hlt⟩
    have hlt : Module.supportDim R N < d := by
      simpa [Module.supportDim] using
        (Order.krullDim_lt_coe_iff (α := Module.support R N) (n := d)).2 hall
    exact hnot_lt hlt
  obtain ⟨l, hl_ge⟩ := hexists
  have hlen : l.length = d := by
    exact le_antisymm (Nat.le_of_lt_succ (hall_succ l)) (Nat.le_of_not_lt hl_ge)
  -- The head of that chain has coheight at least `d`, hence exactly `d` inside `Spec R`.
  have hcoheight_sub : (d : ℕ∞) ≤ Order.coheight l.head := by
    simpa [hlen] using (Order.length_le_coheight_head (p := l))
  have hcoheight_ge : (d : ℕ∞) ≤ Order.coheight (l.head : PrimeSpectrum R) := by
    calc
      (d : ℕ∞) ≤ Order.coheight l.head := hcoheight_sub
      _ ≤ Order.coheight (l.head : PrimeSpectrum R) :=
        Order.coheight_le_coheight_apply_of_strictMono
          (fun x : Module.support R N ↦ (x : PrimeSpectrum R))
          (fun _ _ h ↦ h) l.head
  have hcoheight_le : Order.coheight (l.head : PrimeSpectrum R) ≤ d := by
    have htmp : (Order.coheight (l.head : PrimeSpectrum R) : WithBot ℕ∞) ≤ d := by
      calc
        (Order.coheight (l.head : PrimeSpectrum R) : WithBot ℕ∞) =
            ringKrullDim (R ⧸ (l.head : PrimeSpectrum R).asIdeal) := by
              symm
              exact prime_quotient_ringKrullDim_eq_coheight (R := R)
                ((l.head : PrimeSpectrum R).asIdeal)
        _ ≤ ringKrullDim R :=
          ringKrullDim_quotient_le ((l.head : PrimeSpectrum R).asIdeal)
        _ = d := hdim
    exact WithBot.coe_le_coe.mp htmp
  have hcoheight_eq : Order.coheight (l.head : PrimeSpectrum R) = d :=
    le_antisymm hcoheight_le hcoheight_ge
  refine ⟨(l.head : PrimeSpectrum R), l.head.2, ?_⟩
  -- Rewrite the quotient dimension as the coheight of the chosen support prime.
  simpa [hcoheight_eq] using
    prime_quotient_ringKrullDim_eq_coheight (R := R) ((l.head : PrimeSpectrum R).asIdeal)

/-- Helper for Lemma 15.126.8: if no support prime of a finite module has the full ambient quotient
dimension, then the support dimension is strictly smaller than the ambient dimension. -/
private theorem supportDim_lt_of_forall_mem_support_quotient_dim_ne_top
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {d : ℕ} (hdim : ringKrullDim R = d)
    (hneq : ∀ q : PrimeSpectrum R, q ∈ Module.support R N → ringKrullDim (R ⧸ q.asIdeal) ≠ d) :
    Module.supportDim R N < d := by
  -- First bound the support dimension above by the ambient dimension.
  have hle : Module.supportDim R N ≤ d := by
    simpa [hdim] using (Module.supportDim_le_ringKrullDim (R := R) (M := N))
  -- Equality would force a support prime of quotient dimension `d`, contradicting `hneq`.
  by_contra hnot_lt
  have hsuppdim : Module.supportDim R N = d := le_antisymm hle (le_of_not_gt hnot_lt)
  obtain ⟨q, hq, hqdim⟩ :=
    exists_support_prime_quotient_dim_eq_of_supportDim_eq_ringKrullDim
      (R := R) (N := N) hsuppdim hdim
  exact (hneq q hq) hqdim

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.8: quotienting by the range of a linear map annihilates that map. -/
private theorem mkQ_range_comp_eq_zero
    {A : Type*} {B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) :
    (Submodule.mkQ (LinearMap.range f)).comp f = 0 := by
  -- Every value of `f` already lies in `range f`, so its quotient class vanishes.
  ext x
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.8: quotienting an exact surjective pair by `I • ⊤` preserves
exactness. -/
private theorem quotientMapByIdeal_exact
    {A : Type*} [CommRing A]
    {N : Type*} {P : Type*} {Q : Type*}
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q]
    (I : Ideal A) (f : N →ₗ[A] P) (g : P →ₗ[A] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A P)) y
    -- Lift the quotient-side `I • ⊤` witness back through the surjective map `g`.
    change ((I • (⊤ : Submodule A Q)).mkQ (g x)) = 0 at hy
    have hxI : g x ∈ I • (⊤ : Submodule A Q) := by
      simpa using (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A Q))).mp hy
    have hxLift :
        ∃ y' : P, y' ∈ I • (⊤ : Submodule A P) ∧ g y' = g x := by
      refine
        Submodule.smul_induction_on hxI
          (fun a ha z _ ↦ ?_)
          (fun y z hy' hz' ↦ ?_)
      · obtain ⟨y', rfl⟩ := hg z
        refine ⟨a • y', ?_, by simp⟩
        exact Submodule.smul_mem_smul ha (by simp)
      · rcases hy' with ⟨y', hy'I, rfl⟩
        rcases hz' with ⟨z', hz'I, rfl⟩
        exact ⟨y' + z', Submodule.add_mem _ hy'I hz'I, by simp⟩
    rcases hxLift with ⟨y', hy'I, hy'g⟩
    have hxy : g (x - y') = 0 := by
      simp [hy'g]
    rcases (hExact (x - y')).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule A N)).mkQ n, ?_⟩
    -- Exactness upstairs now descends to the quotient classes.
    change ((I • (⊤ : Submodule A P)).mkQ (f n)) = (I • (⊤ : Submodule A P)).mkQ x
    rw [hn]
    simpa using hy'I
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A N)) x
    -- The easy direction is immediate from `g ∘ f = 0`.
    change ((I • (⊤ : Submodule A Q)).mkQ (g (f x))) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    have hgf : g (f x) = 0 := by
      simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
    rw [hgf]
    exact Submodule.zero_mem _

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.8: quotienting a binary product by `I • ⊤` makes length additive. -/
private theorem length_quotientByIdealTop_prod_eq_add
    {A : Type*} [CommRing A]
    (I : Ideal A) {M : Type*} {N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    Module.length A (((M × N) ⧸ I • (⊤ : Submodule A (M × N)))) =
      Module.length A (M ⧸ I • (⊤ : Submodule A M)) +
        Module.length A (N ⧸ I • (⊤ : Submodule A N)) := by
  let inlbar := (LinearMap.inl A M N).quotientMapByIdeal I
  let sndbar := (LinearMap.snd A M N).quotientMapByIdeal I
  let fstbar := (LinearMap.fst A M N).quotientMapByIdeal I
  have hleft : Function.LeftInverse fstbar inlbar := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro m
    -- The quotient of `fst` is a left inverse to the quotient of `inl` on generators.
    simp [inlbar, fstbar, LinearMap.quotientMapByIdeal]
  have hinj : Function.Injective inlbar := hleft.injective
  have hsurj : Function.Surjective sndbar := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro n
    -- Every quotient class in the right factor comes from `(0, n)`.
    refine ⟨Submodule.Quotient.mk (0, n), ?_⟩
    simp [sndbar, LinearMap.quotientMapByIdeal]
  have hexact : Function.Exact inlbar sndbar := by
    -- Descend the split exact sequence `0 → M → M × N → N → 0`.
    exact quotientMapByIdeal_exact I (LinearMap.inl A M N) (LinearMap.snd A M N)
      (Function.Exact.inl_snd : Function.Exact (LinearMap.inl A M N) (LinearMap.snd A M N))
      LinearMap.snd_surjective
  simpa [inlbar, sndbar] using
    (Module.length_eq_add_of_exact inlbar sndbar hinj hsurj hexact)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.8: after splitting off the `none` coordinate, quotient length of an
`Option`-indexed product is the sum of the two quotient lengths. -/
private theorem length_quotient_piOption_eq_add
    {A : Type*} [CommRing A]
    (I : Ideal A) {ι : Type*} {M : Option ι → Type*}
    [(i : Option ι) → AddCommGroup (M i)] [(i : Option ι) → Module A (M i)] :
    Module.length A (((i : Option ι) → M i) ⧸ I • (⊤ : Submodule A ((i : Option ι) → M i))) =
      Module.length A (M none ⧸ I • (⊤ : Submodule A (M none))) +
        Module.length A ((((i : ι) → M (some i)) ⧸
          I • (⊤ : Submodule A ((i : ι) → M (some i))))) := by
  calc
    Module.length A (((i : Option ι) → M i) ⧸ I • (⊤ : Submodule A ((i : Option ι) → M i))) =
        Module.length A
          (((M none × ((i : ι) → M (some i))) ⧸
            I • (⊤ : Submodule A (M none × ((i : ι) → M (some i)))))) := by
      -- Transport the quotient through the canonical `Option`-splitting equivalence.
      exact
        (quotientByIdealTopLinearEquiv (R := A) (I := I)
          (LinearEquiv.piOptionEquivProd A)).length_eq
    _ =
        Module.length A (M none ⧸ I • (⊤ : Submodule A (M none))) +
          Module.length A ((((i : ι) → M (some i)) ⧸
            I • (⊤ : Submodule A ((i : ι) → M (some i))))) := by
      simpa using
        (length_quotientByIdealTop_prod_eq_add (I := I)
          (M := M none) (N := ((i : ι) → M (some i))))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.8: Hilbert-Samuel `χ` on a finite product is the sum of the factorwise
Hilbert-Samuel `χ`-functions. -/
private theorem finite_pi_hilbertSamuelChi_eq_sum
    {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] {M : ι → Type*}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module A (M i)]
    (I : Ideal A) (n : ℕ) :
    χ_ I ((i : ι) → M i) n = ∑ i, χ_ I (M i) n := by
  classical
  let P : ∀ (κ : Type*) [Fintype κ], Prop := fun κ _ =>
    ∀ (M : κ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)],
      χ_ I ((i : κ) → M i) n = ∑ i, χ_ I (M i) n
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β _ e hα
      intro M hAdd hMod
      letI : ∀ i, AddCommGroup (M i) := hAdd
      letI : ∀ i, Module A (M i) := hMod
      letI : Fintype α := Fintype.ofEquiv β e.symm
      -- Reindex the product along the equivalence and transport the quotient length.
      calc
        χ_ I ((i : β) → M i) n = χ_ I ((i : α) → M (e i)) n := by
          simpa [Ideal.hilbertSamuelChi] using
            (quotientByIdealTopLinearEquiv (R := A) (I := I ^ (n + 1))
              (LinearEquiv.piCongrLeft A (fun i : β ↦ M i) e)).length_eq
        _ = ∑ i, χ_ I (M (e i)) n := hα (fun i ↦ M (e i))
        _ = ∑ i, χ_ I (M i) n := by
          exact Fintype.sum_equiv e (fun i ↦ χ_ I (M i) n) (fun _ ↦ rfl)
    · intro M hAdd hMod
      letI : ∀ i, AddCommGroup (M i) := hAdd
      letI : ∀ i, Module A (M i) := hMod
      -- The empty product is the zero module, so both sides vanish.
      simp [Ideal.hilbertSamuelChi, Module.length_eq_zero]
    · intro α _ hα
      intro M hAdd hMod
      letI : ∀ i, AddCommGroup (M i) := hAdd
      letI : ∀ i, Module A (M i) := hMod
      letI : ∀ i : α, AddCommGroup (M (some i)) := fun i ↦ hAdd (some i)
      letI : ∀ i : α, Module A (M (some i)) := fun i ↦ hMod (some i)
      -- Split off the `none` coordinate and apply the induction hypothesis to the tail.
      calc
        χ_ I ((i : Option α) → M i) n =
            χ_ I (M none) n + χ_ I ((i : α) → M (some i)) n := by
              simpa [Ideal.hilbertSamuelChi] using
                (length_quotient_piOption_eq_add (I := I ^ (n + 1)) (M := M))
        _ = χ_ I (M none) n + ∑ i, χ_ I (M (some i)) n := by
              rw [hα (fun i ↦ M (some i))]
        _ = ∑ i, χ_ I (M i) n := by
              rw [Fintype.sum_option]
  exact hP M

/-- Helper for Lemma 15.126.8: the reduced diagonal and its cokernel quotient form a short exact
sequence over `R`. -/
private theorem reduced_diagonal_shortExact :
    let A := R ⧸ nilradical R
    let B := ∀ p : minimalPrimes R, R ⧸ p.1
    let φ : A →ₗ[R] B := reducedDiagonalLinearMap (R := R)
    (moduleCatMk φ (Submodule.mkQ (LinearMap.range φ))
      (mkQ_range_comp_eq_zero (R := R) φ)).ShortExact := by
  intro A B φ
  refine
    { exact := ?_
      mono_f := ?_
      epi_g := ?_ }
  · -- The quotient by the range of `φ` is exact by construction.
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  · -- Injectivity is exactly the reduced-diagonal injectivity already proved in the owner API.
    exact (ModuleCat.mono_iff_injective _).2 (reduced_diagonal_map_injective (R := R))
  · -- The cokernel quotient map is surjective by definition.
    exact (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

/-- Helper for Lemma 15.126.8: any eventual Hilbert-Samuel `χ`-polynomial for the reduced
parameter ideal on the reduced quotient has degree `d`. -/
private theorem reduced_parameterIdeal_hilbertSamuelChiPolynomial_degree_eq
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) (P : Polynomial ℚ)
    (hP :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) =
          ((χ_(parameterIdeal (reducedParameterFamily (R := R) g))
              (R ⧸ nilradical R) n).toNat : ℚ)) :
    P.degree = d := by
  let S : Type u := R ⧸ nilradical R
  have hsys : IsSystemOfParameters (reducedParameterFamily (R := R) g) :=
    reduced_parameterIdeal_isSystemOfParameters (R := R) g hg
  have hIdef :
      (parameterIdeal (reducedParameterFamily (R := R) g)).IsIdealOfDefinition :=
    hsys.2
  -- Compare with the canonical Hilbert-Samuel degree of the reduced quotient ring.
  rw [← hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition
    (R := S) (M := S) hIdef hP]
  exact (((local_noetherian_ring_dimension_tfae (R := S) d).out 0 1 rfl rfl).mp hsys.1)

/-- Helper for Lemma 15.126.8: positive Krull dimension on the reduced quotient rules out finite
length over itself. -/
private theorem reducedQuotient_not_isFiniteLength_of_pos
    {d : ℕ} (hdim : ringKrullDim R = d) (hd : 0 < d) :
    ¬ IsFiniteLength (R ⧸ nilradical R) (R ⧸ nilradical R) := by
  intro hfinite
  let S : Type u := R ⧸ nilradical R
  have hArt : IsArtinianRing S := by
    exact (isArtinianRing_iff_isFiniteLength S).mp hfinite
  have hdimle0 : Ring.KrullDimLE 0 S := by
    exact (isArtinianRing_iff_krullDimLE_zero (R := S)).mp hArt
  have hzero : ringKrullDim S = 0 := by
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdimle0
  have hSdim : ringKrullDim S = d := by
    simpa [S] using (ringKrullDim_reducedQuotient_eq (R := R)).trans hdim
  have hdzero : (d : WithBot ℕ∞) ≠ 0 := by
    simpa using hd.ne'
  exact hdzero (hSdim.symm.trans hzero)

/-- Helper for Lemma 15.126.8: the annihilator of a quotient ring, viewed as an `R`-module, is
the defining ideal. -/
private theorem annihilator_quotient_eq (I : Ideal R) :
    Module.annihilator R (R ⧸ I) = I := by
  ext r
  rw [Module.mem_annihilator]
  constructor
  · intro hr
    simpa using hr (1 : R ⧸ I)
  · intro hr x
    refine Quotient.inductionOn' x ?_
    intro a
    change Ideal.Quotient.mk I (r * a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact I.mul_mem_left hr

/-- Helper for Lemma 15.126.8: the Hilbert-Samuel `χ`-function of the reduced quotient computed
with the original parameter ideal agrees with the `χ`-function computed using the descended
parameter family. -/
private theorem reduced_quotient_hilbertSamuelChi_eq
    {d : ℕ} (g : Fin d → maximalIdeal R) (n : ℕ) :
    χ_(parameterIdeal g) (R ⧸ nilradical R) n =
      χ_(parameterIdeal (reducedParameterFamily (R := R) g))
        (R ⧸ nilradical R) n := by
  let S : Type u := R ⧸ nilradical R
  let π : R →+* S := Ideal.Quotient.mk (nilradical R)
  let J : Ideal S := parameterIdeal (reducedParameterFamily (R := R) g)
  have hsmul :
      ((parameterIdeal g) ^ (n + 1) • (⊤ : Submodule R S)) =
        Submodule.restrictScalars R (J ^ (n + 1) : Ideal S) := by
    -- Replace the action of the original parameter ideal on the quotient ring by the image ideal.
    rw [Ideal.smul_top_eq_map]
    simp [J, parameterIdeal_reducedParameterFamily_eq_map (R := R) g, Ideal.map_pow]
  have hself :
      (J ^ (n + 1) • (⊤ : Submodule S S)) = (J ^ (n + 1) : Ideal S) := by
    -- On the ring viewed as a module over itself, `I • ⊤` is just the ideal `I`.
    rw [Ideal.smul_top_eq_map]
    simp [J]
  calc
    χ_(parameterIdeal g) (R ⧸ nilradical R) n =
        Module.length R
          (S ⧸ Submodule.restrictScalars R (J ^ (n + 1) : Ideal S)) := by
            simp [Ideal.hilbertSamuelChi, S, hsmul]
    _ = Module.length S (S ⧸ (J ^ (n + 1) : Ideal S)) := by
          -- Transport the quotient length across the surjective map `R → S`.
          exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = χ_(parameterIdeal (reducedParameterFamily (R := R) g)) (R ⧸ nilradical R) n := by
          simp [Ideal.hilbertSamuelChi, S, J, hself]

/-- Helper for Lemma 15.126.8: any eventual Hilbert-Samuel `χ`-polynomial for the reduced quotient
with respect to the original parameter ideal is also eventual for the descended parameter ideal. -/
private theorem reduced_quotient_eventuallyEq_hilbertSamuelChi
    {d : ℕ} (g : Fin d → maximalIdeal R) {P : Polynomial ℚ}
    (hP :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) =
          ((χ_(parameterIdeal g) (R ⧸ nilradical R) n).toNat : ℚ)) :
    ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) =
        ((χ_(parameterIdeal (reducedParameterFamily (R := R) g))
            (R ⧸ nilradical R) n).toNat : ℚ) := by
  filter_upwards [hP] with n hn
  rw [hn, reduced_quotient_hilbertSamuelChi_eq (R := R) g n]

/-- Helper for Lemma 15.126.8: once the product-side degree-`d` coefficient is known, the
reduced-diagonal short exact sequence transfers it to the reduced quotient. -/
private theorem reduced_diagonal_transfer_coeff_d_to_reduced_quotient
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) (hd : 0 < d)
    {P_M : Polynomial ℚ} {e : ℕ}
    (hP_M :
      ∀ᶠ n : ℕ in atTop,
        P_M.eval (n : ℚ) =
          ((χ_(parameterIdeal g) ((∀ p : minimalPrimes R, R ⧸ p.1)) n).toNat : ℚ))
    (hcoeff_M : P_M.coeff d = (e : ℚ) / d.factorial) :
    ∃ P_S : Polynomial ℚ,
      (∀ᶠ n : ℕ in atTop,
        P_S.eval (n : ℚ) =
          ((χ_(parameterIdeal (reducedParameterFamily (R := R) g))
              (R ⧸ nilradical R) n).toNat : ℚ)) ∧
      P_S.leadingCoeff = (e : ℚ) / d.factorial := by
  let S : Type u := R ⧸ nilradical R
  let M : Type u := ∀ p : minimalPrimes R, R ⧸ p.1
  let φ : S →ₗ[R] M := reducedDiagonalLinearMap (R := R)
  let Q : Type u := M ⧸ LinearMap.range φ
  let row : ShortComplex (ModuleCat R) :=
    moduleCatMk φ (Submodule.mkQ (LinearMap.range φ))
      (mkQ_range_comp_eq_zero (R := R) φ)
  rcases exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition R S hg.2 with ⟨P_S, hP_S₀⟩
  rcases exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition R Q hg.2 with ⟨P_Q, hP_Q⟩
  have hP_S :
      ∀ᶠ n : ℕ in atTop,
        P_S.eval (n : ℚ) = ((χ_(parameterIdeal g) S n).toNat : ℚ) := hP_S₀
  have hP_S_reduced :
      ∀ᶠ n : ℕ in atTop,
        P_S.eval (n : ℚ) =
          ((χ_(parameterIdeal (reducedParameterFamily (R := R) g)) S n).toNat : ℚ) :=
    reduced_quotient_eventuallyEq_hilbertSamuelChi (R := R) g hP_S
  have hShortExact : row.ShortExact := by
    -- Reuse the previously packaged exact reduced-diagonal row.
    simpa [row, S, M, φ] using reduced_diagonal_shortExact (R := R)
  have hSnotFiniteR : ¬ IsFiniteLength R S := by
    intro hfinite
    have hlenR : Module.length R S ≠ ⊤ :=
      Module.length_ne_top_iff.mpr hfinite
    have hlenS : Module.length S S ≠ ⊤ := by
      simpa [S] using hlenR
    exact reducedQuotient_not_isFiniteLength_of_pos (R := R) hg.1 hd
      (Module.length_ne_top_iff.mp hlenS)
  have hQsupport :
      Nat.castOrderEmbedding.withBotMap P_Q.degree = Module.supportDim R Q := by
    -- The Hilbert-Samuel degree of `Q` is its support dimension.
    simpa [hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition
      (R := R) (M := Q) hg.2 hP_Q] using
      (hilbertSamuelPolynomialDegree_eq_supportDim (R := R) (M := Q))
  have hQdeg_lt : P_Q.degree < d := by
    -- The cokernel support has dimension `< d`, so its degree-`d` coefficient vanishes.
    apply (Nat.castOrderEmbedding.withBotMap.lt_iff_lt).mp
    have hQdim_lt :
        Module.supportDim R Q < d := by
      have hsupport_pointwise :
          ∀ q : PrimeSpectrum R,
            q ∈ Module.support R Q → ringKrullDim (R ⧸ q.asIdeal) ≠ d := by
        intro q hq
        simpa [Q, φ] using
          reduced_diagonal_cokernel_support_prime_quotient_dim_ne (R := R) q hq hg.1
      exact supportDim_lt_of_forall_mem_support_quotient_dim_ne_top
        (R := R) (N := Q) hg.1 hsupport_pointwise
    simpa [hQsupport] using hQdim_lt
  have hSdegree :
      P_S.degree = d := by
    apply Nat.castOrderEmbedding.withBotMap.injective
    calc
      Nat.castOrderEmbedding.withBotMap P_S.degree =
          Module.supportDim R S := by
            simpa [hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition
              (R := R) (M := S) hg.2 hP_S] using
              (hilbertSamuelPolynomialDegree_eq_supportDim (R := R) (M := S))
      _ = ringKrullDim (R ⧸ Module.annihilator R S) := by
            simpa using (Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := S))
      _ = ringKrullDim (R ⧸ nilradical R) := by
            rw [annihilator_quotient_eq (R := R) (I := nilradical R)]
      _ = ringKrullDim R := ringKrullDim_reducedQuotient_eq (R := R)
      _ = d := hg.1
  have hdiff :
      ((P_M - P_Q - P_S).degree < P_S.degree) := by
    -- The short exact sequence kills the degree-`d` error term coming from the cokernel.
    simpa [row] using
      (hilbertSamuelChi_difference_degree_lt_of_shortExact
        (I := parameterIdeal g) (S := row) (P₁ := P_S) (P₂ := P_M) (P₃ := P_Q)
        hg.2 hShortExact hP_S hP_M hP_Q hSnotFiniteR).2
  have hcoeff_Q_zero : P_Q.coeff d = 0 := by
    exact Polynomial.coeff_eq_zero_of_degree_lt hQdeg_lt
  have hcoeff_diff_zero : (P_M - P_Q - P_S).coeff d = 0 := by
    exact Polynomial.coeff_eq_zero_of_degree_lt (by simpa [hSdegree] using hdiff)
  have hcoeff_S : P_S.coeff d = (e : ℚ) / d.factorial := by
    -- Read the degree-`d` coefficient from the vanished difference polynomial.
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, hcoeff_M, hcoeff_Q_zero] at hcoeff_diff_zero
    linarith
  refine ⟨P_S, hP_S_reduced, ?_⟩
  -- Once the reduced-quotient polynomial has degree `d`, its leading coefficient is its
  -- `X^d`-coefficient.
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hSdegree]
  exact hcoeff_S

/-- Helper for Lemma 15.126.8: an eventual nonnegative rational polynomial of degree at most `r`
has nonnegative `X^r`-coefficient. -/
private theorem coeff_nonneg_of_eventually_nonnegative_values
    (S : Polynomial ℚ) (r : ℕ)
    (hdeg : S.degree ≤ r)
    (hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ S.eval (n : ℚ)) :
    0 ≤ S.coeff r := by
  -- Match the source-faithful sign argument from Lemma `15.126.7`: a negative top coefficient
  -- would force the polynomial to tend to `-∞` along the naturals.
  by_contra hcoeff
  have hcoeff_lt : S.coeff r < 0 := lt_of_not_ge hcoeff
  by_cases hlt : S.degree < r
  · -- If the degree is already `< r`, the `X^r`-coefficient vanishes.
    rw [Polynomial.coeff_eq_zero_of_degree_lt hlt] at hcoeff_lt
    exact lt_irrefl 0 hcoeff_lt
  have hdegEq : S.degree = r := le_antisymm hdeg (le_of_not_gt hlt)
  by_cases hr : r = 0
  · -- Degree `0` means the polynomial is constant, so eventual nonnegativity reads off that value.
    subst hr
    have hconst : S = Polynomial.C (S.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero hdeg
    have hconstNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ S.coeff 0 := by
      filter_upwards [hnonneg] with n hn
      rw [hconst] at hn
      simpa using hn
    rcases eventually_atTop.mp hconstNonneg with ⟨N, hN⟩
    exact hcoeff_lt.not_ge (hN N le_rfl)
  have hdegPos : 0 < S.degree := by
    simpa [hdegEq] using (Nat.pos_iff_ne_zero.mpr hr)
  have hnat : S.natDegree = r :=
    Polynomial.natDegree_eq_of_degree_eq_some hdegEq
  have hlead_lt : S.leadingCoeff < 0 := by
    rw [Polynomial.leadingCoeff, hnat]
    exact hcoeff_lt
  have htoBot :
      Tendsto (fun z : ℚ ↦ S.eval z) atTop atBot :=
    S.tendsto_atBot_of_leadingCoeff_nonpos hdegPos hlead_lt.le
  have hnegRat : ∀ᶠ z : ℚ in atTop, S.eval z ≤ (-1 : ℚ) :=
    (tendsto_atBot.1 htoBot) (-1)
  have hnegNat : ∀ᶠ n : ℕ in atTop, S.eval (n : ℚ) < 0 := by
    filter_upwards [hnegRat.comp_tendsto tendsto_natCast_atTop_atTop] with n hn
    linarith
  rcases eventually_atTop.mp (hnonneg.and hnegNat) with ⟨N, hN⟩
  exact (not_lt_of_ge (hN N le_rfl).1 (hN N le_rfl).2).elim

/-- Helper for Lemma 15.126.8: a lower-dimensional minimal-prime factor contributes no `X^d`
term to an eventual Hilbert-Samuel `χ`-polynomial. -/
private theorem non_top_dim_minimal_prime_factor_exists_coeff_d_zero
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g)
    (p : minimalPrimes R) (hpdim : ringKrullDim (R ⧸ p.1) < d) :
    ∃ P : Polynomial ℚ,
      (∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(parameterIdeal g) (R ⧸ p.1) n).toNat : ℚ)) ∧
      P.coeff d = 0 := by
  rcases exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition R (R ⧸ p.1) hg.2 with
    ⟨P, hP⟩
  have hPdim :
      Nat.castOrderEmbedding.withBotMap P.degree = ringKrullDim (R ⧸ p.1) := by
    calc
      Nat.castOrderEmbedding.withBotMap P.degree =
          Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R (R ⧸ p.1)) := by
            rw [hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition
              (R := R) (M := R ⧸ p.1) hg.2 hP]
      _ = Module.supportDim R (R ⧸ p.1) := by
            simpa using
              (hilbertSamuelPolynomialDegree_eq_supportDim (R := R) (M := R ⧸ p.1))
      _ = ringKrullDim (R ⧸ Module.annihilator R (R ⧸ p.1)) := by
            simpa using
              (Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := R ⧸ p.1))
      _ = ringKrullDim (R ⧸ p.1) := by
            rw [annihilator_quotient_eq (R := R) (I := p.1)]
  have hdeg_lt : P.degree < d := by
    apply (Nat.castOrderEmbedding.withBotMap.lt_iff_lt).mp
    simpa [hPdim] using hpdim
  refine ⟨P, hP, ?_⟩
  -- Once the degree drops below `d`, the `X^d`-coefficient vanishes.
  exact Polynomial.coeff_eq_zero_of_degree_lt hdeg_lt

/-- Helper for Lemma 15.126.8: the remaining product-side task is to assemble factorwise eventual
Hilbert-Samuel polynomials on `∏ p, R ⧸ p` and read off a degree-`d` coefficient that dominates the
top-dimensional minimal-prime count. -/
private theorem minimal_prime_product_exists_hilbertSamuelChiPolynomial_with_top_count
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) :
    ∃ P_M : Polynomial ℚ, ∃ e : ℕ,
      (topDimMinimalPrimes (R := R)).encard ≤ e ∧
        (∀ᶠ n : ℕ in atTop,
          P_M.eval (n : ℚ) =
            ((χ_(parameterIdeal g) ((∀ p : minimalPrimes R, R ⧸ p.1)) n).toNat : ℚ)) ∧
        P_M.coeff d = (e : ℚ) / d.factorial := by
  -- TODO: follow the source proof factor by factor. For top-dimensional `p`, build an eventual
  -- polynomial on `R ⧸ p.1` whose `X^d`-coefficient is `e_p / d!` with `0 < e_p`; for
  -- lower-dimensional `p`, use `non_top_dim_minimal_prime_factor_exists_coeff_d_zero`; then sum
  -- the factor polynomials via `finite_pi_hilbertSamuelChi_eq_sum` and compare the resulting
  -- coefficient with `(topDimMinimalPrimes (R := R)).encard`.
  sorry

/-- Helper for Lemma 15.126.8: in positive dimension, the remaining source-faithful blocker is the
reduced-diagonal comparison on `R ⧸ nilradical R`, which should directly bound the top-dimensional
minimal-prime count by the reduced parameter-ideal quotient length. -/
private theorem topDimMinimalPrimes_le_reduced_parameterIdeal_quotient_length_of_pos
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) (hd : 0 < d) :
    (topDimMinimalPrimes (R := R)).encard ≤
      Module.length (R ⧸ nilradical R)
        ((R ⧸ nilradical R) ⧸ parameterIdeal (reducedParameterFamily (R := R) g)) := by
  -- Route correction: the old blocker asked for an eventual Hilbert-Samuel polynomial directly on
  -- `R`; the source proof actually runs on the reduced quotient and only then compares lengths.
  let S : Type u := R ⧸ nilradical R
  let _ : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let M : Type u := ∀ p : minimalPrimes R, R ⧸ p.1
  let φ : S →ₗ[R] M := reducedDiagonalLinearMap (R := R)
  let Q : Type u := M ⧸ LinearMap.range φ
  rcases minimal_prime_product_exists_hilbertSamuelChiPolynomial_with_top_count
      (R := R) g hg with ⟨P_M, e, hencard, hP_M, hcoeff_M⟩
  rcases reduced_diagonal_transfer_coeff_d_to_reduced_quotient
      (R := R) g hg hd hP_M hcoeff_M with ⟨P_S, hP_S, hlead_S⟩
  have hsys_reduced :
      IsSystemOfParameters (reducedParameterFamily (R := R) g) :=
    reduced_parameterIdeal_isSystemOfParameters (R := R) g hg
  have hlength :
      (e : ℕ∞) ≤
        Module.length S
          (S ⧸ parameterIdeal (reducedParameterFamily (R := R) g)) :=
    hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal_of_isSystemOfParameters
      (R := S) (x := reducedParameterFamily (R := R) g) hsys_reduced P_S e hP_S hlead_S
  -- Once the product-side numerator has been transferred to the reduced quotient, apply
  -- Lemma `15.126.7` on the reduced ring and compare with the top-dimensional prime count.
  calc
    (topDimMinimalPrimes (R := R)).encard ≤ e := hencard
    _ ≤ Module.length S
          (S ⧸ parameterIdeal (reducedParameterFamily (R := R) g)) := hlength

/-- Lemma 15.126.8: let `(R, 𝔪)` be a Noetherian local ring, let `g₁, …, g_d` be a system of
parameters, written as `g : Fin d → maximalIdeal R`, and let `t` be the number of minimal prime
ideals `𝔭` of `R` with `ringKrullDim (R ⧸ 𝔭) = ringKrullDim R`. Then `t` is at most the length of
`R / (g₁, …, g_d)`, written canonically as `Module.length R (R ⧸ parameterIdeal g)`. -/
@[stacks 0BWX]
theorem encard_topDimMinimalPrimes_le_length_quotient_parameterIdeal_of_isSystemOfParameters
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) :
    ({ p : Ideal R | p ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R }).encard ≤
      Module.length R (R ⧸ parameterIdeal g) := by
  by_cases hd0 : d = 0
  · -- In dimension `0`, the multiplicity package from the zero-dimensional branch already closes
    -- the desired length bound over `R`.
    subst hd0
    rcases zeroDim_exists_parameterIdeal_multiplicity_numerator_ge_topDimMinimalPrimes
        (R := R) g hg with ⟨P, e, hencard, hP, hlead⟩
    calc
      ({ p : Ideal R | p ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R }).encard ≤
          (e : ℕ∞) := by
            simpa [topDimMinimalPrimes] using hencard
      _ ≤ Module.length R (R ⧸ parameterIdeal g) :=
        hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal_of_isSystemOfParameters
          g hg P e hP hlead
  · -- In positive dimension, first prove the bound on the reduced quotient and then compare the
    -- reduced parameter quotient back to the original one.
    have hd : 0 < d := Nat.pos_iff_ne_zero.mpr hd0
    calc
      ({ p : Ideal R | p ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R }).encard ≤
          Module.length (R ⧸ nilradical R)
            ((R ⧸ nilradical R) ⧸ parameterIdeal (reducedParameterFamily (R := R) g)) := by
              simpa [topDimMinimalPrimes] using
                topDimMinimalPrimes_le_reduced_parameterIdeal_quotient_length_of_pos
                  (R := R) g hg hd
      _ ≤ Module.length R (R ⧸ parameterIdeal g) :=
        reduced_parameterIdeal_quotient_length_le (R := R) g

end
