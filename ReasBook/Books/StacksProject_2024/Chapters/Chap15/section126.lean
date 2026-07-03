import Mathlib
import Mathlib.RingTheory.OrderOfVanishing

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_126_1 (from Chap15) -/
universe u

section

open Pointwise

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: commutative algebra of principal-ideal quotient lengths and order of vanishing;
* sampled owner API: `Ring.ord`, `Ring.ord_mul`, `Ideal.exact_mulQuot_quotOfMul`, and
  `Module.length_eq_add_of_exact`;
* source/core/bridge triage:
  `source-facing`: the textbook quotient-length formulas for powers of a principal ideal;
  `core/canonical`: `Ring.ord` together with the multiplicative owner theorem `Ring.ord_mul`;
  `bridge/view`: unfolding `Ring.ord` and rewriting by `Ideal.span_singleton_pow`.

Primitive-vs-derived split:
* primitive data: the ring `R`, the element `x : R`, and the exponent `n`;
* derived API: the explicit quotient-length formulas are source-facing bridges from the owner-level
  `Ring.ord` statements; minimal-prime avoidance and dimension bounds belong only to later
  applications such as Lemma `15.126.2`.
-/

private lemma smul_span_singleton_eq_span_singleton_mul (a b : R) :
    b • Ideal.span ({a} : Set R) = Ideal.span ({a * b} : Set R) := by
  calc
    b • Ideal.span ({a} : Set R) = ({b} : Set R) • Ideal.span ({a} : Set R) := by
      symm
      exact Submodule.singleton_set_smul (Ideal.span ({a} : Set R)) b
    _ = Ideal.span ({b * a} : Set R) := by
      simpa [Set.singleton_mul_singleton] using
        (Submodule.set_smul_span ({b} : Set R) ({a} : Set R))
    _ = Ideal.span ({a * b} : Set R) := by
      rw [mul_comm]

private theorem ord_mul_le_add (a b : R) :
    Ring.ord R (a * b) ≤ Ring.ord R a + Ring.ord R b := by
  have hlen :
      Module.length R (R ⧸ b • Ideal.span ({a} : Set R)) =
        Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker +
          Module.length R (R ⧸ Ideal.span ({b} : Set R)) := by
    simpa using
      (Module.length_eq_add_of_exact
        ((Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker.subtype)
        (Ideal.quotOfMul b (Ideal.span ({a} : Set R)))
        (Submodule.subtype_injective _)
        (Ideal.quotOfMul_surjective (Ideal.span ({a} : Set R)))
        (LinearMap.exact_subtype_ker_map (Ideal.quotOfMul b (Ideal.span ({a} : Set R)))))
  have hker :
      Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker ≤
        Module.length R (R ⧸ Ideal.span ({a} : Set R)) := by
    have hrange :
        (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker =
          (Ideal.mulQuot b (Ideal.span ({a} : Set R))).range :=
      LinearMap.exact_iff.mp (Ideal.exact_mulQuot_quotOfMul (Ideal.span ({a} : Set R)))
    calc
      Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker =
          Module.length R (Ideal.mulQuot b (Ideal.span ({a} : Set R))).range := by
            rw [hrange]
      _ =
          Module.length R
            ((R ⧸ Ideal.span ({a} : Set R)) ⧸ (Ideal.mulQuot b (Ideal.span ({a} : Set R))).ker) := by
            symm
            exact (LinearMap.quotKerEquivRange (Ideal.mulQuot b (Ideal.span ({a} : Set R)))).length_eq
      _ ≤ Module.length R (R ⧸ Ideal.span ({a} : Set R)) := by
            exact Module.length_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  calc
    Ring.ord R (a * b) =
        Module.length R (R ⧸ b • Ideal.span ({a} : Set R)) := by
          rw [Ring.ord, smul_span_singleton_eq_span_singleton_mul]
    _ =
        Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker +
          Module.length R (R ⧸ Ideal.span ({b} : Set R)) := hlen
    _ ≤
        Ring.ord R a + Ring.ord R b :=
      by
        simpa [Ring.ord, add_comm, add_left_comm, add_assoc] using
          add_le_add_right hker (Module.length R (R ⧸ Ideal.span ({b} : Set R)))

-- Proof sketch: iterate the product inequality `ord (ab) ≤ ord a + ord b`.
/-- Lemma 15.126.1 (1), core/canonical form: for every commutative ring `R`, element `x : R`, and
exponent `n : ℕ`, the order of vanishing of `x ^ n` is at most `n` times the order of vanishing of
`x`. The one-dimensional and minimal-prime hypotheses from the source are not part of this
canonical owner-level inequality; they are only needed in later applications. -/
theorem ord_pow_le_nsmul_ord (x : R) (n : ℕ) :
    Ring.ord R (x ^ n) ≤ n • Ring.ord R x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        Ring.ord R (x ^ n.succ) = Ring.ord R (x ^ n * x) := by
          rw [pow_succ]
        _ ≤ Ring.ord R (x ^ n) + Ring.ord R x :=
          ord_mul_le_add (x ^ n) x
        _ ≤ n • Ring.ord R x + Ring.ord R x := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right ih (Ring.ord R x)
        _ = n.succ • Ring.ord R x := by
          rw [succ_nsmul]

/-- Lemma 15.126.1 (1), source-facing bridge: `length_R (R / (x)^n) ≤ n * length_R (R / (x))`. -/
theorem length_quotient_span_singleton_pow_le_mul_length_quotient_span_singleton
    (x : R) (n : ℕ) :
    Module.length R (R ⧸ (Ideal.span {x}) ^ n) ≤
      n • Module.length R (R ⧸ Ideal.span {x}) := by
  rw [Ideal.span_singleton_pow]
  simpa [Ring.ord] using ord_pow_le_nsmul_ord x n

-- Proof sketch: iterate the canonical multiplicativity theorem `Ring.ord_mul`.
/-- Lemma 15.126.1 (2), core/canonical form: if `x` is a nonzerodivisor, then
`Ring.ord R (x ^ n) = n • Ring.ord R x`. -/
theorem ord_pow_eq_nsmul_ord_of_mem_nonZeroDivisors
    {x : R} (hx : x ∈ nonZeroDivisors R) (n : ℕ) :
    Ring.ord R (x ^ n) = n • Ring.ord R x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        Ring.ord R (x ^ n.succ) = Ring.ord R (x ^ n * x) := by
          rw [pow_succ]
        _ = Ring.ord R (x ^ n) + Ring.ord R x :=
          Ring.ord_mul R hx
        _ = n • Ring.ord R x + Ring.ord R x := by
          rw [ih]
        _ = n.succ • Ring.ord R x := by
          rw [succ_nsmul]

/-- Lemma 15.126.1 (2), source-facing bridge: if `x` is a nonzerodivisor, then
`length_R (R / (x)^n) = n * length_R (R / (x))`. -/
theorem length_quotient_span_singleton_pow_eq_mul_length_quotient_span_singleton_of_mem_nonZeroDivisors
    {x : R} (hx : x ∈ nonZeroDivisors R) (n : ℕ) :
    Module.length R (R ⧸ (Ideal.span {x}) ^ n) =
      n • Module.length R (R ⧸ Ideal.span {x}) := by
  rw [Ideal.span_singleton_pow]
  simpa [Ring.ord] using ord_pow_eq_nsmul_ord_of_mem_nonZeroDivisors hx n

end

/-! ### Lemma_15_126_2 (from Chap15) -/
universe u

open IsLocalRing

section

/- Domain triage:
* primary domain: one-dimensional local commutative algebra, comparing minimal-prime counts with
  principal-ideal quotient length;
* sampled owner API: `Ring.ord`, `minimalPrimes.finite_of_isNoetherianRing`,
  `Ring.KrullDimLE 1`, and the chapter-level principal-ideal length theorem
  `ord_pow_le_nsmul_ord`;
* source/core/bridge triage:
  `source-facing`: the Stacks bound on the number of minimal primes of a one-dimensional local
  ring cut by an element of the maximal ideal avoiding all minimal primes;
* `core/canonical`: the owner for `Module.length R (R ⧸ Ideal.span {x})` is `Ring.ord R x`;
* `bridge/view`: the textbook quotient length is already canonically owned by `Ring.ord`, so no
  parallel local length wrapper belongs in this file.

Primitive-vs-derived split:
* primitive data: the local Noetherian ring, the distinguished element `x : maximalIdeal R`, and
  the canonical membership-style minimal-prime avoidance predicate
  `∀ p ∈ minimalPrimes R, (x : R) ∉ p`;
* derived API: the quotient-length bound, expressed canonically through `Ring.ord`.
-/

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

-- Proof sketch: pass to the reduced quotient to preserve the number of minimal primes while only
-- decreasing the quotient length. Embed the reduced ring into the product of its minimal-prime
-- quotients, show the cokernel has finite length and is killed by a power of `x`, and then compare
-- lengths after multiplication by `x^n`. Apply Lemma `15.126.1` to the one-dimensional reduced
-- quotients to conclude that each minimal prime contributes at least `1` to the total length.
/-- Lemma 15.126.2: let `(R, 𝔪)` be a Noetherian local ring of dimension `1`, and let
`x : maximalIdeal R` avoid every minimal prime of `R`. Then the number of minimal prime ideals of
`R`, written as `(minimalPrimes R).encard`, is at most the order of vanishing `Ring.ord R x`,
which is canonically `Module.length R (R ⧸ Ideal.span {x})`. The explicit equality
`ringKrullDim R = 1` from the source is replaced by the owner hypothesis `[Ring.KrullDimLE 1 R]`;
the maximal-ideal condition is absorbed into the input type `x : maximalIdeal R`. -/
theorem encard_minimalPrimes_le_ord
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) :
    (minimalPrimes R).encard ≤ Ring.ord R x := sorry

end

/-! ### Lemma_15_126_3 (from Chap15) -/
universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Domain-style sampling:
-- * primary domain: systems of parameters in Noetherian local rings, with minimal-prime
--   avoidance and one-step dimension reduction;
-- * sampled owner declarations: `IsSystemOfParameters`, `parameterIdeal`,
--   `generatedIdeal_clause_iff_exists_systemOfParameters`,
--   `ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes`.
--
-- Source/core/bridge triage:
-- * source-facing: the lemma asserts that an element `f` outside all minimal primes can be
--   extended, in first-position order, to a system of parameters whose tail lies in a prescribed
--   power of the maximal ideal;
-- * core/canonical: `IsSystemOfParameters` is the owner abstraction for the chosen parameter
--   family, so the primitive data should be the ordered tail `y : Fin d → maximalIdeal R`, with
--   the full family derived as `Fin.cons f y`;
-- * bridge/view: minimal-prime avoidance should use the chapter's canonical membership-style
--   owner surface `∀ p ∈ minimalPrimes R, (f : R) ∉ p`, and
--   the existence step in the quotient should be read through the owner theorem
--   `generatedIdeal_clause_iff_exists_systemOfParameters` rather than through a lower-level
--   generated-ideal witness package.
-- Proof sketch: if `d = 0`, use the one-term parameter family `Fin.cons f` and the tail condition
-- is vacuous. Otherwise, Lemma `ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes`
-- lowers the quotient dimension to `d`, and the owner-level existence clause from Proposition
-- `10.60.9`, packaged by `generatedIdeal_clause_iff_exists_systemOfParameters`, supplies a
-- length-`d` system of parameters in `R / (f)`. Lift those parameters to `R`, then replace each
-- lift by its `k`-th power so that the tail lands in `(maximalIdeal R)^k` without changing the
-- generated radical.
/-- Lemma 15.126.3: write `dim R = d + 1`. If `f : maximalIdeal R` avoids every minimal prime of
`R`, then there exist `d` further parameters in `(maximalIdeal R)^k` whose ordered extension
`Fin.cons f y` is a system of parameters. This is the source-facing ordered `Fin.cons` form of
adjoining further parameters in `(maximalIdeal R)^k` to the specified element `f`. -/
theorem exists_systemOfParameters_cons_mem_maximalIdeal_pow_of_not_mem_minimalPrimes
    {d k : ℕ} (hdim : ringKrullDim R = d.succ) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ y : Fin d → maximalIdeal R,
      IsSystemOfParameters (Fin.cons f y) ∧
        ∀ j, (y j : R) ∈ maximalIdeal R ^ k := sorry

end

/-! ### Lemma_15_126_4 (from Chap15) -/
universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Domain-style sampling:
-- * primary domain: systems of parameters and parameter ideals in two-dimensional Noetherian
--   local rings;
-- * sampled owner declarations: `IsSystemOfParameters`, `parameterIdeal`,
--   `isSystemOfParameters_iff_of_ringKrullDim_eq`,
--   `exists_systemOfParameters_cons_mem_maximalIdeal_pow_of_not_mem_minimalPrimes`;
-- * best owner abstraction: the chosen parameter family should be expressed in the chapter's
--   canonical `Fin.cons` form, here specialized to a singleton tail;
-- * primitive-vs-derived: the primitive data are the chosen second parameter `g` and the resulting
--   family `Fin.cons f ![g]`, while perturbation stability and quotient-length equality are
--   derived properties of that owner family.

-- Source/core/bridge triage:
-- * source-facing: the lemma fixes the first parameter `f` and chooses one further parameter in
--   dimension `2`;
-- * core/canonical: the parameter family is owned by `IsSystemOfParameters (Fin.cons f ![g])`
--   and its ideal `parameterIdeal (Fin.cons f ![g])`;
-- * bridge/view: the older pair notation `![f, g]` is only a coordinate presentation of the same
--   owner family, so it should not remain the primary public surface.

-- Proof sketch: use Lemma `15.126.3` with tail length `d = 1` and `k = 1` to choose
-- `g ∈ maximalIdeal R` such that `Fin.cons f ![g]` is a system of parameters. Since the
-- corresponding parameter ideal is an ideal of definition, Lemma `10.32.5` gives `n` with
-- `(maximalIdeal R) ^ n ≤ parameterIdeal (Fin.cons f ![g])`. For any
-- `h ∈ (maximalIdeal R) ^ (n + 1)`, write `h = af + bg` with `a, b ∈ maximalIdeal R`; then
-- `Fin.cons (f + h) ![g]` generates the same ideal as `Fin.cons f ![g]` because `1 + a` is a
-- unit, so the perturbed family is again a system of parameters and the quotient lengths agree.
/-- Lemma 15.126.4: in a two-dimensional Noetherian local ring, if `f ∈ maximalIdeal R` avoids
all minimal primes, then there exist `g ∈ maximalIdeal R` and an exponent `n` (equivalently
`N = n + 1`) such that `Fin.cons f ![g]` is a system of parameters, and every perturbation of the
head entry by an element of `(maximalIdeal R)^(n + 1)` preserves the system of parameters and the
quotient length. -/
theorem exists_systemOfParameters_cons_singleton_stable_under_highOrder_perturbation_of_not_mem_minimalPrimes
    (hdim : ringKrullDim R = 2) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ g : maximalIdeal R, ∃ n : ℕ,
      IsSystemOfParameters (Fin.cons f ![g]) ∧
        ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (n + 1)) →
          IsSystemOfParameters (Fin.cons (f + h) ![g]) ∧
            Module.length R (R ⧸ parameterIdeal (Fin.cons f ![g])) =
              Module.length R (R ⧸ parameterIdeal (Fin.cons (f + h) ![g])) := sorry

end

/-! ### Lemma_15_126_5 (from Chap15) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalRing R]

/-
Domain-style sampling:
- primary domain: two-dimensional local commutative algebra, with height-one prime ideals and
  principal quotients;
- sampled owner declarations:
  `IsNormalRing`,
  `principalIdeal`,
  `PrimeSpectrum R`,
  `IsReduced`,
  `Ideal.height`,
  `chinese_remainder_prod_eq_iInf`,
  `exists_power_sum_ne_zero`;
- best owner abstraction: the source-facing input is a finite distinct collection of height-one
  prime ideals, so the right owner surface here is a
  `Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }` rather than an indexed family plus a
  separate injectivity witness;
  mathlib's `IsDedekindDomain.HeightOneSpectrum` is too specific for this normal local setting,
  while the quotient by the chosen element should use the chapter owner `principalIdeal` rather
  than restating `Ideal.span ({f} : Set R)`;
- primitive data vs. derived API:
  primitive data is the finite set `ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }`;
  derived API is the existence of a common nonzero element whose principal quotient is reduced.

Source/core/bridge triage:
- `source-facing`: the common-element existence statement for a finite family of pairwise distinct
  height-one primes;
- `core/canonical`: `IsNormalRing`, `principalIdeal`, `IsReduced`, and the height API on ideals;
- `bridge/view`: none beyond the canonical direct subtype
  `{ p : PrimeSpectrum R // p.asIdeal.height = 1 }`.
-/

-- Proof sketch: start with any nonzero element in the finite intersection of the given height-one
-- primes and apply the stable-perturbation lemma from the previous item to vary it by a deep
-- maximal-ideal element. Interpreting the resulting principal divisor through the discrete
-- valuation rings at the height-one primes, choose the perturbation so that the number of minimal
-- primes of the quotient is maximal; then all valuation multiplicities become `1`, which is
-- equivalent to the quotient by the principal ideal being reduced.
/-- Lemma 15.126.5: in a two-dimensional Noetherian local normal ring, any finite family of
pairwise distinct height-one prime ideals has a common nonzero element whose principal quotient is
reduced. -/
theorem exists_mem_heightOnePrimes_with_reduced_principal_quotient
    (hdim : ringKrullDim R = 2)
    (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    ∃ f : R, f ≠ 0 ∧ (∀ p ∈ ps, f ∈ p.1.asIdeal) ∧ IsReduced (R ⧸ principalIdeal f) := sorry

end

/-! ### Lemma_15_126_6 (from Chap15) -/
universe u

open IsLocalRing

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalRing A]

/- Domain-style sampling for Lemma 15.126.6:
- primary domain: two-dimensional local commutative algebra, with height-one primes, principal
  divisors, and reduced principal quotients;
- sampled owner declarations:
  `exists_mem_heightOnePrimes_with_reduced_principal_quotient`,
  `IsNormalRing`,
  `IsLocalRing.notMem_maximalIdeal`,
  `principalIdeal`,
  `IsReduced`,
  `Ideal.height`;
- best owner abstraction: the source-facing input remains the single nonzero element
  `a ≠ 0`, while the canonical chapter owner driving the construction is the finite-family
  height-one-prime theorem `exists_mem_heightOnePrimes_with_reduced_principal_quotient`; the
  local-ring owner `IsLocalRing.notMem_maximalIdeal` shows that the extra source-side hypothesis
  `a ∈ maximalIdeal A` is redundant for the resulting divisibility conclusion;
- primitive data vs. derived API:
  primitive data is the element `a` together with `a ≠ 0`;
  derived API is the resulting nonzero element `c` with reduced principal quotient and a power of
  `c` divisible by `a`.

Source/core/bridge triage:
- `source-facing`: the divisibility statement for one nonzero element, with the source
  maximal-ideal formulation recovered as the nonunit case;
- `core/canonical`: `IsNormalRing`, `exists_mem_heightOnePrimes_with_reduced_principal_quotient`,
  `principalIdeal`, `IsReduced`, and the height-one-prime API on ideals;
- `bridge/view`: passing from the finite family of height-one primes appearing in the divisor of
  `a` to the single-element divisibility consequence. -/

-- Proof sketch: if `a ∉ maximalIdeal A`, then `a` is a unit by
-- `IsLocalRing.notMem_maximalIdeal`, so the conclusion is trivial with `c = 1` and `n = 0`.
-- Otherwise `a` lies in the maximal ideal, and Lemma `15.126.5` applied to the finite family of
-- height-one primes occurring in the divisor of `a` yields a common nonzero element `c` with
-- `A ⧸ (c)` reduced. For any exponent `n` at least as large as all coefficients in `div(a)`, the
-- divisor `-div(a) + div(c ^ n)` is effective, and Lemma `10.157.6` then identifies this
-- effectivity with the divisibility relation `a ∣ c ^ n`.
/-- Lemma 15.126.6: in a two-dimensional Noetherian normal local domain, every nonzero element
divides a power of some nonzero element `c` such that the principal quotient
`A ⧸ principalIdeal c` is reduced. -/
theorem exists_nonzero_reduced_principal_quotient_dvd_pow
    (hdim : ringKrullDim A = 2) (a : A) (ha0 : a ≠ 0) :
    ∃ c : A, c ≠ 0 ∧ IsReduced (A ⧸ principalIdeal c) ∧ ∃ n : ℕ, a ∣ c ^ n := sorry

end

/-! ### Lemma_15_126_7 (from Chap15) -/
universe u

open Filter
open IsLocalRing
open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Proof sketch: let `I = parameterIdeal x`. Proposition 10.59.5 gives an eventual polynomial
-- representative `P` of the rationalized Hilbert-Samuel `χ`-function
-- `n ↦ ((χ_ I R n).toNat : ℚ)`, while the Hilbert-Samuel degree API together with
-- Proposition 10.60.9 identifies the degree of any such representative with `d` from
-- `hx : IsSystemOfParameters x`.
-- Compare the first difference
-- `length_R (R / I^(n + 1)) - length_R (R / I^n)` with the surjective map
-- `⨁_{i₁ + ··· + i_d = n} R / I ⟶ I^n / I^(n + 1)` induced by the monomials
-- `g₁ ^ i₁ * ··· * g_d ^ i_d`; this bounds the degree-`d - 1` leading term by
-- `length_R (R / I) / (d - 1)!`, which is equivalent to `e ≤ Module.length R (R ⧸ I)`.
/-- Lemma 15.126.7: let `(R, 𝔪)` be a Noetherian local ring, let `x` be a system of parameters of
length `d`, and let `I = parameterIdeal x`. If `P` is an eventual polynomial representative of the
canonical rationalized Hilbert-Samuel `χ`-function
`n ↦ ((χ_ I R n).toNat : ℚ)` and has leading
coefficient
`e / d!`, then `(e : ℕ∞) ≤ Module.length R (R ⧸ I)`. -/
theorem hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal_of_isSystemOfParameters
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (e : ℕ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hlead : P.leadingCoeff = (e : ℚ) / d.factorial) :
    (e : ℕ∞) ≤ Module.length R (R ⧸ parameterIdeal x) := sorry

end

/-! ### Lemma_15_126_8 (from Chap15) -/
universe u

open IsLocalRing

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
/-- Lemma 15.126.8: let `(R, 𝔪)` be a Noetherian local ring, let `g₁, …, g_d` be a system of
parameters, written as `g : Fin d → maximalIdeal R`, and let `t` be the number of minimal prime
ideals `𝔭` of `R` with `ringKrullDim (R ⧸ 𝔭) = ringKrullDim R`. Then `t` is at most the length of
`R / (g₁, …, g_d)`, written canonically as `Module.length R (R ⧸ parameterIdeal g)`. -/
theorem encard_topDimMinimalPrimes_le_length_quotient_parameterIdeal_of_isSystemOfParameters
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) :
    ({ p : Ideal R | p ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R }).encard ≤
      Module.length R (R ⧸ parameterIdeal g) := sorry

end

/-! ### Lemma_15_126_9 (from Chap15) -/
universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Source/core/bridge triage:
-- * source-facing: the lemma asserts stability of a system of parameters whose distinguished
--   first entry is the prescribed element `f`;
-- * core/canonical: the owner abstractions are `IsSystemOfParameters`, `parameterIdeal`, and the
--   canonical ordered family `Fin.cons f y`;
-- * bridge/view: the previous existential packaging by a family `x`, an index `i`, and an
--   equality `x i = f` was only a coordinate-level presentation of the same ordered family, so it
--   should be replaced by the owner-level `Fin.cons` form already used in Lemma `15.126.3`.
-- Proof sketch: apply Lemma `15.126.3` to choose a tail `y` such that `Fin.cons f y` is a system
-- of parameters. Since its parameter ideal is an ideal of definition, Lemma `10.32.5` gives a
-- power of the maximal ideal contained in that parameter ideal. For `h` in that power, write `h`
-- modulo the chosen parameter family so that replacing the head entry `f` by `f + h` does not
-- change the generated ideal. Equality of parameter ideals then gives both the perturbed
-- system-of-parameters statement and the equality of quotient lengths.
/-- Lemma 15.126.9: write `dim R = d + 1`. If `f : maximalIdeal R` avoids every minimal prime of
`R`, then there exist `d` further parameters and an exponent `n` such that the ordered family
`Fin.cons f y` is a system of parameters, and every perturbation of the distinguished head entry by
an element of `(maximalIdeal R)^(n + 1)` again yields a system of parameters with the same
quotient length. -/
theorem exists_systemOfParameters_stable_under_highOrder_perturbation_of_not_mem_minimalPrimes
    {d : ℕ} (hdim : ringKrullDim R = d.succ) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ y : Fin d → maximalIdeal R, ∃ n : ℕ,
      IsSystemOfParameters (Fin.cons f y) ∧
        ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (n + 1)) →
          IsSystemOfParameters (Fin.cons (f + h) y) ∧
            Module.length R (R ⧸ parameterIdeal (Fin.cons f y)) =
              Module.length R (R ⧸ parameterIdeal (Fin.cons (f + h) y)) := sorry

end

/-! ### Proposition_15_126_10 (from Chap15) -/
universe u

section

/- Domain-style sampling:
- primary domain: local commutative algebra over Noetherian catenary normal local rings, with the
  normality and catenary hypotheses carried by the chapter ring-level owners;
- sampled owner declarations:
  `IsNormalRing`,
  `IsCatenaryRing`,
  `principalIdeal`,
  `Ideal.IsRadical`;
- best owner abstraction: the ambient ring hypotheses should be expressed through the existing
  chapter owners `IsNormalRing R` and `IsCatenaryRing R`, while principal quotients use the
  Chapter 15 owner `principalIdeal`;
- primitive data vs. derived API:
  primitive data is the radical ideal `J` together with `hJrad : J.IsRadical` and `hJne : J ≠ ⊥`;
  derived API is the existence of a nonzero element of `J` whose principal quotient is reduced.

Source/core/bridge triage:
- `source-facing`: the existence statement for a nonzero element of the given radical ideal;
- `core/canonical`: `IsNormalRing`, `IsCatenaryRing`, `Ideal.IsRadical`, and `principalIdeal`;
- `bridge/view`: none. The local redeclaration of `IsCatenaryRing` would be a duplicate owner and
  should be removed in favor of the chapter owner. -/

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalRing R]
  [IsCatenaryRing R]

-- Proof sketch: imitate Lemma `15.126.5` using the catenary version of the perturbation argument.
-- Start with a nonzero element of the nonzero radical ideal `J`, use the stable perturbation
-- family from Lemma `15.126.9`, and bound the number of minimal primes of the perturbed principal
-- quotients via Lemma `15.126.8`. Choosing a perturbation with maximal number of minimal primes
-- forces every height-one valuation multiplicity to become `1`, which is equivalent to the
-- reducedness of the principal quotient.
/-- Proposition 15.126.10: if `J` is a nonzero radical ideal in a catenary Noetherian local normal
domain, then `J` contains a nonzero element whose principal quotient is reduced. -/
theorem exists_nonzero_mem_radicalIdeal_with_reduced_principal_quotient
    (J : Ideal R) (hJrad : J.IsRadical) (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ principalIdeal f) := sorry

end
