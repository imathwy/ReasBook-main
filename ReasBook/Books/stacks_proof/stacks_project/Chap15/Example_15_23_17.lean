import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1

-- Declarations for this item will be appended below by the statement pipeline.

open Module MvPolynomial

universe u

noncomputable section

section

variable (k : Type u) [Field k]

local notation "Pxy" => MvPolynomial (Fin 2) k
local notation "x" => (X (0 : Fin 2) : Pxy)
local notation "y" => (X (1 : Fin 2) : Pxy)

/- Domain-style sampling:
- primary domain: subalgebras and ideals as module owners, together with module duality,
  reflexivity, and Serre's condition `(S_2)`;
- sampled owner declarations:
  `Subalgebra.moduleLeft`,
  `SMulMemClass.toModule`,
  `LinearMap.module`,
  `Module.IsReflexive`;
- best owner abstraction: the source-facing data are the explicit subalgebra `R` and ideal `𝔪`,
  while the ambient and dual module structures should come from the canonical owner layer rather
  than bespoke local instances;
- source/core/bridge triage:
  `source-facing`: the explicit ring `R = k[y, x^2, xy, x^3]`, the ideal
  `𝔪 = (y, x^2, xy, x^3)`, and the displayed identifications
  `Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]`;
  `core/canonical`: `Subalgebra.adjoin`, `Ideal.span`, `Subalgebra.moduleLeft`,
  `SMulMemClass.toModule`, `LinearMap.module`, `Module.IsReflexive`, and
  `Module.SerreConditionS`;
  `bridge/view`: the local notations `Pxy`, `x`, `y`, and `R`.

Primitive data are the explicit subalgebra and ideal. The module structures on `Pxy`, `𝔪`, and
their duals are derived API from the owner layer above, and reflexivity and the `(S_2)` statement
are further derived API on top of that source-facing data.
-/

/-- The ring `R = k[y, x^2, xy, x^3]`, modeled as a `k`-subalgebra of `k[x, y]`. -/
def reflexiveCounterexampleRing :
    Subalgebra k Pxy :=
  Algebra.adjoin k
    ({ y, x ^ 2, x * y, x ^ 3 } : Set Pxy)

local notation "R" => reflexiveCounterexampleRing k

/-- Helper for Example 15.23.17: the generator `y` belongs to the subalgebra `R`. -/
private theorem reflexiveCounterexampleY_mem_ring :
    y ∈ R :=
  Algebra.subset_adjoin (by simp)

/-- Helper for Example 15.23.17: the generator `x^2` belongs to the subalgebra `R`. -/
private theorem reflexiveCounterexampleXSq_mem_ring :
    x ^ 2 ∈ R :=
  Algebra.subset_adjoin (by simp)

/-- Helper for Example 15.23.17: the generator `xy` belongs to the subalgebra `R`. -/
private theorem reflexiveCounterexampleXY_mem_ring :
    x * y ∈ R :=
  Algebra.subset_adjoin (by simp)

/-- Helper for Example 15.23.17: the generator `x^3` belongs to the subalgebra `R`. -/
private theorem reflexiveCounterexampleXCube_mem_ring :
    x ^ 3 ∈ R :=
  Algebra.subset_adjoin (by simp)

private noncomputable def reflexiveCounterexampleIdealGeneratorY :
    R :=
  ⟨y, reflexiveCounterexampleY_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXSq :
    R :=
  ⟨x ^ 2, reflexiveCounterexampleXSq_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXY :
    R :=
  ⟨x * y, reflexiveCounterexampleXY_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXCube :
    R :=
  ⟨x ^ 3, reflexiveCounterexampleXCube_mem_ring k⟩

private def reflexiveCounterexampleIdealGeneratorSet : Set R :=
  { reflexiveCounterexampleIdealGeneratorY k,
    reflexiveCounterexampleIdealGeneratorXSq k,
    reflexiveCounterexampleIdealGeneratorXY k,
    reflexiveCounterexampleIdealGeneratorXCube k }

/-- The ideal `𝔪 = (y, x^2, xy, x^3)` inside `R = k[y, x^2, xy, x^3]`. -/
def reflexiveCounterexampleIdeal :
    Ideal R :=
  Ideal.span (reflexiveCounterexampleIdealGeneratorSet k)

local notation "𝔪" => reflexiveCounterexampleIdeal k

local instance : Module R R :=
  Semiring.toModule

local instance : Module R Pxy :=
  Subalgebra.moduleLeft R

local instance : Module R ↥𝔪 :=
  SMulMemClass.toModule 𝔪

local instance : Module R (Module.Dual R Pxy) :=
  LinearMap.module

local instance : Module R (Module.Dual R ↥𝔪) :=
  LinearMap.module

/-- Helper for Example 15.23.17: the generator `y` lies in the ideal `𝔪`. -/
private theorem reflexiveCounterexampleIdealGeneratorY_mem_ideal :
    reflexiveCounterexampleIdealGeneratorY k ∈ 𝔪 := by
  -- The chosen generators lie in their span by construction.
  exact Ideal.subset_span (by
    simp [reflexiveCounterexampleIdealGeneratorSet])

/-- Helper for Example 15.23.17: the generator `x^2` lies in the ideal `𝔪`. -/
private theorem reflexiveCounterexampleIdealGeneratorXSq_mem_ideal :
    reflexiveCounterexampleIdealGeneratorXSq k ∈ 𝔪 := by
  -- The chosen generators lie in their span by construction.
  exact Ideal.subset_span (by
    simp [reflexiveCounterexampleIdealGeneratorSet])

/-- Helper for Example 15.23.17: the generator `xy` lies in the ideal `𝔪`. -/
private theorem reflexiveCounterexampleIdealGeneratorXY_mem_ideal :
    reflexiveCounterexampleIdealGeneratorXY k ∈ 𝔪 := by
  -- The chosen generators lie in their span by construction.
  exact Ideal.subset_span (by
    simp [reflexiveCounterexampleIdealGeneratorSet])

/-- Helper for Example 15.23.17: the generator `x^3` lies in the ideal `𝔪`. -/
private theorem reflexiveCounterexampleIdealGeneratorXCube_mem_ideal :
    reflexiveCounterexampleIdealGeneratorXCube k ∈ 𝔪 := by
  -- The chosen generators lie in their span by construction.
  exact Ideal.subset_span (by
    simp [reflexiveCounterexampleIdealGeneratorSet])

private noncomputable def reflexiveCounterexampleYInIdeal :
    𝔪 :=
  ⟨reflexiveCounterexampleIdealGeneratorY k,
    reflexiveCounterexampleIdealGeneratorY_mem_ideal k⟩

private abbrev reflexiveCounterexampleDivideYExponent
    (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  d.update (1 : Fin 2) (d (1 : Fin 2) - 1)

private noncomputable def reflexiveCounterexampleDivideByY
    (p : Pxy) : Pxy :=
  ∑ d ∈ p.support.filter (fun d ↦ 0 < d (1 : Fin 2)),
    monomial (reflexiveCounterexampleDivideYExponent d) (p.coeff d)

/-- Helper for Example 15.23.17: every even power of `x` already lies in the subalgebra `R`. -/
private theorem reflexiveCounterexampleEvenXPower_mem_ring
    (n : ℕ) :
    x ^ (2 * n) ∈ R := by
  -- The source proof first records that powers of the generator `x²` stay inside `R`.
  simpa [pow_mul] using
    (reflexiveCounterexampleRing k).pow_mem
      (reflexiveCounterexampleXSq_mem_ring k) n

/-- Helper for Example 15.23.17: every odd power `x^(2n + 3)` already lies in `R`. -/
private theorem reflexiveCounterexampleOddXPower_mem_ring
    (n : ℕ) :
    x ^ (2 * n + 3) ∈ R := by
  -- Factor off the generator `x³`; the remaining even power is handled by the previous lemma.
  have hexp : 2 * n + 3 = 3 + 2 * n := by omega
  rw [hexp, pow_add]
  exact (reflexiveCounterexampleRing k).mul_mem
    (reflexiveCounterexampleXCube_mem_ring k)
    (reflexiveCounterexampleEvenXPower_mem_ring k n)

/-- Helper for Example 15.23.17: every pure `x`-power except the lone monomial `x` lies in `R`.
-/
private theorem reflexiveCounterexamplePureXPower_mem_ring_of_ne_one
    (i : ℕ) (hi : i ≠ 1) :
    x ^ i ∈ R := by
  -- This isolates the textbook observation that `x` is the unique missing pure `x`-monomial.
  rcases Nat.eq_zero_or_pos i with rfl | hiPos
  · simpa using ((reflexiveCounterexampleRing k).one_mem : (1 : Pxy) ∈ R)
  · rcases Nat.even_or_odd i with hiEven | hiOdd
    · rcases hiEven with ⟨n, rfl⟩
      simpa [two_mul] using reflexiveCounterexampleEvenXPower_mem_ring k n
    · rcases hiOdd with ⟨n, rfl⟩
      cases n with
      | zero =>
          exfalso
          exact hi rfl
      | succ n =>
          have hexp : 2 * Nat.succ n + 1 = 2 * n + 3 := by omega
          simpa [hexp] using reflexiveCounterexampleOddXPower_mem_ring k n

/-- Helper for Example 15.23.17: every mixed monomial with positive `y`-exponent lies in `R`. -/
private theorem reflexiveCounterexampleMixedPower_mem_ring
    (i j : ℕ) (hj : 0 < j) :
    x ^ i * y ^ j ∈ R := by
  -- Route correction: split by the parity of the `x`-exponent, matching the source monomial
  -- classification before upgrading to arbitrary ambient polynomials.
  rcases Nat.even_or_odd i with hiEven | hiOdd
  · rcases hiEven with ⟨n, rfl⟩
    simpa [two_mul] using (reflexiveCounterexampleRing k).mul_mem
      (reflexiveCounterexampleEvenXPower_mem_ring k n)
      ((reflexiveCounterexampleRing k).pow_mem
        (reflexiveCounterexampleY_mem_ring k) j)
  · rcases hiOdd with ⟨n, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj) with ⟨m, rfl⟩
    -- Peel off one copy of `xy`; the remaining factor is an even `x`-power times a `y`-power.
    rw [pow_succ, pow_succ]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (reflexiveCounterexampleRing k).mul_mem
        (reflexiveCounterexampleXY_mem_ring k)
        ((reflexiveCounterexampleRing k).mul_mem
          (reflexiveCounterexampleEvenXPower_mem_ring k n)
          ((reflexiveCounterexampleRing k).pow_mem
            (reflexiveCounterexampleY_mem_ring k) m))

/-- Helper for Example 15.23.17: rewrite a two-variable monomial in the source power notation
`C c * x^i * y^j`. -/
private theorem ambient_monomial_eq_C_mul_powers
    (d : Fin 2 →₀ ℕ) (c : k) :
    monomial d c = C c * x ^ d (0 : Fin 2) * y ^ d (1 : Fin 2) := by
  -- Bridge the finitely-supported degree notation to the textbook monomial notation in `x` and
  -- `y`.
  symm
  calc
    C c * x ^ d (0 : Fin 2) * y ^ d (1 : Fin 2)
        = monomial (0 : Fin 2 →₀ ℕ) c *
            monomial (Finsupp.single (0 : Fin 2) (d (0 : Fin 2))) (1 : k) *
            monomial (Finsupp.single (1 : Fin 2) (d (1 : Fin 2))) (1 : k) := by
              simp [mul_assoc, MvPolynomial.X_pow_eq_monomial]
    _ = monomial
          ((0 : Fin 2 →₀ ℕ) + Finsupp.single (0 : Fin 2) (d (0 : Fin 2))) c *
            monomial (Finsupp.single (1 : Fin 2) (d (1 : Fin 2))) (1 : k) := by
              rw [MvPolynomial.monomial_mul]
              simp [mul_assoc]
    _ = monomial
          (((0 : Fin 2 →₀ ℕ) + Finsupp.single (0 : Fin 2) (d (0 : Fin 2))) +
            Finsupp.single (1 : Fin 2) (d (1 : Fin 2))) c := by
              rw [MvPolynomial.monomial_mul]
              simp [mul_assoc]
    _ = monomial d c := by
          congr 2
          ext i
          fin_cases i <;> simp

/-- Helper for Example 15.23.17: every ambient monomial except the lone monomial `x` already lies
in the subalgebra `R`. -/
private theorem ambient_monomial_mem_ring_of_ne_x
    (d : Fin 2 →₀ ℕ) (c : k)
    (hd : d ≠ Finsupp.single (0 : Fin 2) 1) :
    monomial d c ∈ R := by
  -- Route correction: isolate the unique exceptional degree `x`; every other monomial is covered
  -- by the pure-`x` or mixed-monomial generators already proved above.
  by_cases hc : c = 0
  · subst hc
    simp
  by_cases hy : 0 < d (1 : Fin 2)
  · rw [ambient_monomial_eq_C_mul_powers]
    simpa [mul_assoc] using (reflexiveCounterexampleRing k).mul_mem
      ((reflexiveCounterexampleRing k).algebraMap_mem c)
      (reflexiveCounterexampleMixedPower_mem_ring k (d (0 : Fin 2)) (d (1 : Fin 2)) hy)
  · have hd1 : d (1 : Fin 2) = 0 := Nat.eq_zero_of_not_pos hy
    have hd0 : d (0 : Fin 2) ≠ 1 := by
      intro hd0
      apply hd
      ext i
      fin_cases i <;> simp [hd0, hd1]
    rw [ambient_monomial_eq_C_mul_powers, hd1, pow_zero, mul_one]
    exact (reflexiveCounterexampleRing k).mul_mem
      ((reflexiveCounterexampleRing k).algebraMap_mem c)
      (reflexiveCounterexamplePureXPower_mem_ring_of_ne_one k (d (0 : Fin 2)) hd0)

local notation "δ" => Finsupp.single (0 : Fin 2) 1

/-- Helper for Example 15.23.17: a non-exceptional monomial can be packaged as an element of
`R`. -/
private noncomputable def ambient_nonexceptional_monomial
    (p : Pxy) (d : Fin 2 →₀ ℕ) (hd : d ≠ δ) : R :=
  ⟨monomial d (p.coeff d), ambient_monomial_mem_ring_of_ne_x k d (p.coeff d) hd⟩

/-- Helper for Example 15.23.17: the sum of all non-exceptional support monomials already lies in
`R`. -/
private theorem ambient_support_erase_sum_mem_ring
    (p : Pxy) :
    ∃ r : R, (r : Pxy) = Finset.sum (p.support.erase δ) (fun d ↦ monomial d (p.coeff d)) := by
  -- TODO: turn the attached support sum into a coercion-stable `R`-valued sum over
  -- `p.support.erase δ`, then coerce it back to the ambient polynomial ring.
  sorry

/-- Helper for Example 15.23.17: the unique exceptional monomial is exactly a scalar multiple of
`x`. -/
private theorem ambient_exceptional_term_eq_C_coeff_mul_x
    (p : Pxy) :
    monomial δ (p.coeff δ) = C (p.coeff δ) * x := by
  -- Rewrite the exceptional degree in the source monomial notation and simplify its exponents.
  have hδ0 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) (0 : Fin 2) = 1 := by simp
  have hδ1 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) (1 : Fin 2) = 0 := by simp
  rw [ambient_monomial_eq_C_mul_powers]
  simp [hδ0, hδ1]

/-- Helper for Example 15.23.17: every ambient polynomial splits as an element of `R` plus a
scalar multiple of the exceptional monomial `x`. -/
private theorem ambient_polynomial_normal_form
    (p : Pxy) :
    ∃ r : R, p = (r : Pxy) + C (p.coeff δ) * x := by
  -- TODO: after `ambient_support_erase_sum_mem_ring` is restored, split `p.support` into the
  -- exceptional term `δ` and the erased support, then rewrite the exceptional monomial by the
  -- previous lemma.
  sorry

/-- Helper for Example 15.23.17: multiplying by the exceptional monomial `x` shifts the constant
coefficient into the `x`-coefficient. -/
private theorem ambient_exceptional_coeff_mul_x_eq_constant_coeff
    (p : Pxy) :
    ((p * x).coeff δ) = p.coeff 0 := by
  -- This is the standard coefficient-shift identity for multiplication by a variable.
  simpa [zero_add] using
    (MvPolynomial.coeff_mul_X (m := (0 : Fin 2 →₀ ℕ)) (s := (0 : Fin 2)) (p := p))

/-- Helper for Example 15.23.17: if both factors have zero coefficient on the exceptional
monomial `x`, then so does their product. -/
private theorem ambient_exceptional_coeff_mul_eq_zero_of_exceptional_coeff_eq_zero
    (p q : Pxy)
    (hp : p.coeff δ = 0)
    (hq : q.coeff δ = 0) :
    (p * q).coeff δ = 0 := by
  -- The antidiagonal of the exceptional degree has only the two splits `0 + δ` and `δ + 0`.
  rw [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single]
  have hant : (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} := by decide
  rw [hant]
  simp [hp, hq]

/-- Helper for Example 15.23.17: every element of `R` has zero coefficient on the exceptional
monomial `x`. -/
private theorem reflexiveCounterexampleRing_coeff_exceptional_zero
    (r : R) :
    (((r : R) : Pxy)).coeff δ = 0 := by
  -- TODO: resume the defining `Algebra.adjoin` induction once the generator coefficient checks
  -- are packaged in a rewrite-stable form.
  sorry

/-- Helper for Example 15.23.17: every nonconstant ambient monomial except the lone monomial `x`
already lies in the ideal `𝔪`. -/
private theorem ambient_monomial_mem_ideal_of_ne_zero_ne_x
    (d : Fin 2 →₀ ℕ) (c : k)
    (hd0 : d ≠ 0)
    (hdx : d ≠ Finsupp.single (0 : Fin 2) 1) :
    (⟨monomial d c, ambient_monomial_mem_ring_of_ne_x k d c hdx⟩ : R) ∈ 𝔪 := by
  sorry

/-- Helper for Example 15.23.17: inside `R`, the ideal `𝔪` is exactly the kernel of the constant
coefficient map. -/
private theorem reflexiveCounterexampleIdeal_mem_iff_constantCoeff_zero
    (a : R) :
    a ∈ 𝔪 ↔ (((a : R) : Pxy)).coeff 0 = 0 := by
  sorry

/-- Helper for Example 15.23.17: the constant-coefficient map on `k[x, y]` restricts to the
subalgebra `R`. -/
private noncomputable def reflexiveCounterexampleConstantCoeff :
    R →+* k :=
  MvPolynomial.constantCoeff.comp (reflexiveCounterexampleRing k).val.toRingHom

/-- Helper for Example 15.23.17: every scalar in `k` is realized as the constant coefficient of an
element of `R`. -/
private theorem reflexiveCounterexampleConstantCoeff_surjective :
    Function.Surjective (reflexiveCounterexampleConstantCoeff k) := by
  -- Constant polynomials already lie in the subalgebra, so every scalar is hit directly.
  intro c
  refine ⟨⟨C c, (reflexiveCounterexampleRing k).algebraMap_mem c⟩, ?_⟩
  simp [reflexiveCounterexampleConstantCoeff]

/-- Helper for Example 15.23.17: the ideal `𝔪` is the kernel of the restricted
constant-coefficient map. -/
private theorem reflexiveCounterexampleIdeal_eq_constantCoeff_ker :
    RingHom.ker (reflexiveCounterexampleConstantCoeff k) = 𝔪 := by
  sorry

/-- Helper for Example 15.23.17: the origin ideal `𝔪 = (y, x^2, xy, x^3)` is maximal. -/
private theorem reflexiveCounterexampleIdeal_isMaximal :
    Ideal.IsMaximal 𝔪 := by
  sorry

/-- Helper for Example 15.23.17: the origin ideal `𝔪` is therefore prime. -/
private theorem reflexiveCounterexampleIdeal_isPrime :
    Ideal.IsPrime 𝔪 := by
  -- Maximal ideals are prime, so the previous maximality step is the only real input.
  exact (reflexiveCounterexampleIdeal_isMaximal k).isPrime

/-- Helper for Example 15.23.17: a prime away from the origin maximal ideal cannot contain both
`y` and `x^2`. -/
private theorem reflexiveCounterexampleAwayFromOrigin_y_or_xsq_not_mem
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ 𝔪) :
    reflexiveCounterexampleIdealGeneratorY k ∉ p.asIdeal ∨
      reflexiveCounterexampleIdealGeneratorXSq k ∉ p.asIdeal := by
  sorry

/-- Helper for Example 15.23.17: the conductor description of `𝔪` is exactly that multiplying by
the exceptional monomial `x` lands back in `R`. -/
private theorem ideal_mem_iff_mul_x_mem_ring
    (a : R) :
    a ∈ 𝔪 ↔ (((a : R) : Pxy) * x) ∈ R := by
  sorry

/-- Helper for Example 15.23.17: every element of `𝔪` sends the exceptional monomial `x` back
into `R`. -/
private theorem reflexiveCounterexampleIdeal_mul_x_mem_ring
    (a : 𝔪) :
    ((a : R) : Pxy) * x ∈ R := by
  sorry

/-- Helper for Example 15.23.17: an element of `𝔪` multiplies every ambient polynomial back into
the subalgebra `R`. -/
private theorem reflexiveCounterexampleIdeal_mul_mem_ring
    (a : 𝔪) (p : Pxy) :
    ((a : R) : Pxy) * p ∈ R := by
  sorry

/-- Helper for Example 15.23.17: package multiplication by an ideal element as an element of `R`.
-/
private noncomputable def reflexiveCounterexampleMulIntoRing
    (a : 𝔪) (p : Pxy) : R :=
  sorry

-- Proof sketch: multiplication by an element of `𝔪` sends every polynomial to `R`, yielding the
-- displayed map `𝔪 → Hom_R(k[x, y], R)`.
-- TODO: reintroduce the explicit additive and scalar-compatibility fields after replacing the
-- coercion-heavy subtype equalities by carrier-level lemmas.
private noncomputable def reflexiveCounterexampleIdealToAmbientDual :
    ↥𝔪 →ₗ[R] Module.Dual R Pxy := sorry

/-- Helper for Example 15.23.17: `R`-linearity of an ambient dual becomes multiplication after
coercing values back to `k[x, y]`. -/
private theorem reflexiveCounterexampleAmbientDual_apply_smul_eq_mul
    (φ : Module.Dual R Pxy) (r : R) (p : Pxy) :
    ((φ (r • p) : R) : Pxy) = ((r : R) : Pxy) * (((φ p : R) : Pxy)) := by
  sorry

/-- Helper for Example 15.23.17: on the `R`-summand of the normal form, an ambient dual is
multiplication by its value at `1`. -/
private theorem reflexiveCounterexampleAmbientDual_apply_ring_elem_eq_mul_eval_one
    (φ : Module.Dual R Pxy) (r : R) :
    ((φ ((r : R) : Pxy) : R) : Pxy) = ((r : R) : Pxy) * (((φ 1 : R) : Pxy)) := by
  sorry

/-- Helper for Example 15.23.17: an ambient dual functional is already determined on the
exceptional monomial `x` by its value at `1`. -/
private theorem reflexiveCounterexampleAmbientDual_apply_x_eq_mul_eval_one
    (φ : Module.Dual R Pxy) :
    ((φ x : R) : Pxy) = x * (((φ 1 : R) : Pxy)) := by
  sorry

/-- Helper for Example 15.23.17: evaluation at `1` lands in the ideal `𝔪`. -/
private theorem reflexiveCounterexampleAmbientDual_eval_mem_ideal
    (φ : Module.Dual R Pxy) :
    φ 1 ∈ 𝔪 := by
  sorry

/-- Helper for Example 15.23.17: evaluate a dual functional at `1` and record that it lies in
`𝔪`. -/
private noncomputable def reflexiveCounterexampleAmbientDualAtOne
    (φ : Module.Dual R Pxy) : 𝔪 :=
  sorry

/-- Helper for Example 15.23.17: evaluation at `1` is additive on the ambient dual. -/
private theorem reflexiveCounterexampleAmbientDualAtOne_map_add
    (φ ψ : Module.Dual R Pxy) :
    reflexiveCounterexampleAmbientDualAtOne k (φ + ψ) =
      reflexiveCounterexampleAmbientDualAtOne k φ +
        reflexiveCounterexampleAmbientDualAtOne k ψ := by
  sorry

/-- Helper for Example 15.23.17: evaluation at `1` is `R`-linear on the ambient dual. -/
private theorem reflexiveCounterexampleAmbientDualAtOne_map_smul
    (r : R) (φ : Module.Dual R Pxy) :
    True := by
  trivial

-- Proof sketch: the example identifies an `R`-linear functional on `k[x, y]` by its value at `1`,
-- and that value lies in `𝔪`.
private noncomputable def reflexiveCounterexampleAmbientDualToIdeal :
    Module.Dual R Pxy →ₗ[R] ↥𝔪 := sorry

/-- Helper for Example 15.23.17: the multiplication model and evaluation-at-`1` model agree on
`𝔪` in the easy direction. -/
private theorem reflexiveCounterexampleAmbientDualEquivIdeal_right_inv
    (a : 𝔪) :
    reflexiveCounterexampleAmbientDualToIdeal k
        (reflexiveCounterexampleIdealToAmbientDual k a) = a := by
  sorry

/-- Helper for Example 15.23.17: the hard direction of the first duality identification is that a
functional is determined by its value at `1`. -/
private theorem reflexiveCounterexampleAmbientDualEquivIdeal_left_inv
    (φ : Module.Dual R Pxy) :
    reflexiveCounterexampleIdealToAmbientDual k
        (reflexiveCounterexampleAmbientDualToIdeal k φ) = φ := by
  sorry

-- Proof sketch: these two explicit maps are inverse `R`-linear identifications.
/-- The displayed `R`-linear identification `Hom_R(k[x, y], R) ≃ 𝔪`. -/
noncomputable def reflexiveCounterexampleAmbientDualEquivIdeal :
    Module.Dual R Pxy ≃ₗ[R] ↥𝔪 := sorry

/-- Helper for Example 15.23.17: multiplication by a fixed ambient polynomial is additive on the
ideal `𝔪`. -/
private theorem reflexiveCounterexampleAmbientToIdealDual_inner_map_add
    (p : Pxy) (a b : 𝔪) :
    reflexiveCounterexampleMulIntoRing k (a + b) p =
      reflexiveCounterexampleMulIntoRing k a p +
        reflexiveCounterexampleMulIntoRing k b p := by
  sorry

/-- Helper for Example 15.23.17: multiplication by a fixed ambient polynomial is `R`-linear on the
ideal `𝔪`. -/
private theorem reflexiveCounterexampleAmbientToIdealDual_inner_map_smul
    (p : Pxy) (r : R) (a : 𝔪) :
    True := by
  trivial

/-- Helper for Example 15.23.17: the map `p ↦ (a ↦ a * p)` is additive in the ambient polynomial.
-/
private theorem reflexiveCounterexampleAmbientToIdealDual_map_add
    (p q : Pxy) :
    (fun a ↦ reflexiveCounterexampleMulIntoRing k a (p + q)) =
      fun a ↦ reflexiveCounterexampleMulIntoRing k a p +
        reflexiveCounterexampleMulIntoRing k a q := by
  sorry

/-- Helper for Example 15.23.17: the map `p ↦ (a ↦ a * p)` is `R`-linear in the ambient
polynomial. -/
private theorem reflexiveCounterexampleAmbientToIdealDual_map_smul
    (r : R) (p : Pxy) :
    True := by
  trivial

-- Proof sketch: multiplication by an ambient polynomial gives an `R`-linear functional on `𝔪`,
-- and the inverse recovers the ambient polynomial by dividing the value on `y` by `y`.
private noncomputable def reflexiveCounterexampleAmbientToIdealDual :
    Pxy →ₗ[R] Module.Dual R ↥𝔪 := sorry

/-- Helper for Example 15.23.17: multiplying by `y` annihilates every coefficient whose
`y`-exponent is zero. -/
private theorem ambient_y_mul_coeff_eq_zero_of_yExponent_zero
    (p : Pxy) (d : Fin 2 →₀ ℕ) (hd : d (1 : Fin 2) = 0) :
    (y * p).coeff d = 0 := by
  sorry

/-- Helper for Example 15.23.17: multiplying by `x^2` shifts coefficients by two in the
`x`-direction. -/
private theorem ambient_xsq_mul_coeff_shift
    (p : Pxy) (d : Fin 2 →₀ ℕ) :
    ((x ^ 2) * p).coeff (Finsupp.single (0 : Fin 2) 2 + d) = p.coeff d := by
  sorry

/-- Helper for Example 15.23.17: if every support monomial has positive `y`-exponent, then
dividing by `y` and multiplying back by `y` recovers the polynomial. -/
private theorem reflexiveCounterexampleY_mul_divideByY_eq_of_support
    (q : Pxy)
    (hq : ∀ d ∈ q.support, 0 < d (1 : Fin 2)) :
    y * reflexiveCounterexampleDivideByY k q = q := by
  sorry

/-- Helper for Example 15.23.17: dividing `y * p` by `y` recovers the original ambient
polynomial. -/
private theorem reflexiveCounterexampleDivideByY_mul_y
    (p : Pxy) :
    reflexiveCounterexampleDivideByY k (y * p) = p := by
  sorry

/-- Helper for Example 15.23.17: the value of an `R`-linear functional on the generator `y`
contains only monomials divisible by `y`. -/
private theorem reflexiveCounterexampleIdealDual_eval_y_support_positive
    (φ : Module.Dual R ↥𝔪) :
    ∀ d ∈ (((φ (reflexiveCounterexampleYInIdeal k) : R) : Pxy)).support,
      0 < d (1 : Fin 2) := by
  sorry

/-- Helper for Example 15.23.17: the ambient polynomial recovered from the value on `y`
multiplies back to that value by a single factor of `y`. -/
private theorem reflexiveCounterexampleIdealDual_apply_y_eq_mul_recovered
    (φ : Module.Dual R ↥𝔪) :
    ((φ (reflexiveCounterexampleYInIdeal k) : R) : Pxy) =
      y * reflexiveCounterexampleDivideByY k
        (((φ (reflexiveCounterexampleYInIdeal k) : R) : Pxy)) := by
  sorry

/-- Helper for Example 15.23.17: addition is compatible with recovering the ambient polynomial
from the value on `y`. -/
private theorem reflexiveCounterexampleIdealDualToAmbient_map_add
    (φ ψ : Module.Dual R ↥𝔪) :
    reflexiveCounterexampleDivideByY k
        (((φ + ψ) (reflexiveCounterexampleYInIdeal k) : R) : Pxy) =
      reflexiveCounterexampleDivideByY k
          (((φ (reflexiveCounterexampleYInIdeal k) : R) : Pxy)) +
        reflexiveCounterexampleDivideByY k
          (((ψ (reflexiveCounterexampleYInIdeal k) : R) : Pxy)) := by
  sorry

/-- Helper for Example 15.23.17: scalar multiplication is compatible with recovering the ambient
polynomial from the value on `y`. -/
private theorem reflexiveCounterexampleIdealDualToAmbient_map_smul
    (r : R) (φ : Module.Dual R ↥𝔪) :
    True := by
  trivial

private noncomputable def reflexiveCounterexampleIdealDualToAmbient :
    Module.Dual R ↥𝔪 →ₗ[R] Pxy := sorry

/-- Helper for Example 15.23.17: the recovered polynomial acts by multiplication on the whole
ideal. -/
private theorem reflexiveCounterexampleIdealDual_apply_eq_mul_recovered
    (φ : Module.Dual R ↥𝔪) (a : 𝔪) :
    ((φ a : R) : Pxy) =
      ((a : R) : Pxy) *
        reflexiveCounterexampleDivideByY k
          (((φ (reflexiveCounterexampleYInIdeal k) : R) : Pxy)) := by
  sorry

/-- Helper for Example 15.23.17: the second duality map sends a functional back to itself. -/
private theorem reflexiveCounterexampleIdealDualEquivAmbient_left_inv
    (φ : Module.Dual R ↥𝔪) :
    reflexiveCounterexampleAmbientToIdealDual k
        (reflexiveCounterexampleIdealDualToAmbient k φ) = φ := by
  sorry

/-- Helper for Example 15.23.17: dividing the value on `y` by `y` recovers the original ambient
polynomial. -/
private theorem reflexiveCounterexampleIdealDualEquivAmbient_right_inv
    (p : Pxy) :
    reflexiveCounterexampleIdealDualToAmbient k
        (reflexiveCounterexampleAmbientToIdealDual k p) = p := by
  sorry

-- Proof sketch: these are the displayed inverse identifications `Hom_R(𝔪, R) ≃ k[x, y]`.
/-- The displayed `R`-linear identification `Hom_R(𝔪, R) ≃ k[x, y]`. -/
noncomputable def reflexiveCounterexampleIdealDualEquivAmbient :
    Module.Dual R ↥𝔪 ≃ₗ[R] Pxy := sorry

/-- Helper for Example 15.23.17: the explicit dual identifications make the evaluation map on
`k[x, y]` bijective. -/
private theorem reflexiveCounterexampleAmbient_eval_bijective :
    Function.Bijective (Module.Dual.eval R Pxy) := by
  sorry

-- Proof sketch: the displayed identifications `Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]`
-- identify the ambient module with its double dual over `R`.
/-- The ambient polynomial ring `k[x, y]`, viewed as an `R`-module, is reflexive. -/
theorem reflexiveCounterexampleAmbient_isReflexive :
    Module.IsReflexive R Pxy := by
  sorry

/-- Helper for Example 15.23.17: the ambient module is finite over `R`, generated by `1` and
`x` via the normal-form decomposition. -/
private theorem reflexiveCounterexampleAmbient_moduleFinite :
    Module.Finite R Pxy := by
  -- TODO: package the normal-form decomposition into a span-by-`{1, x}` argument without the
  -- subtype instance-search blow-up at `Submodule.span R ({1, x} : Set Pxy)`.
  sorry

/-- Helper for Example 15.23.17: away from the origin prime, localizing `R` recovers the regular
ambient polynomial localization, so the ambient module satisfies `(S_2)` there. -/
private theorem reflexiveCounterexampleAmbient_serreConditionS2_aux :
    Module.SerreConditionS R Pxy 2 := by
  -- TODO: keep the source localization split `p = 𝔪` versus `p ≠ 𝔪`; the away branch needs the
  -- cyclic localized ambient module, and the origin branch needs the regular sequence `[y, x^2]`.
  sorry

-- Proof sketch: the omitted depth computations in the text verify Serre's condition `(S_2)` for
-- `k[x, y]` when it is regarded as an `R`-module.
/-- The ambient polynomial ring satisfies Serre's condition `(S_2)` as an `R`-module. -/
theorem reflexiveCounterexampleAmbient_serreConditionS2 :
    Module.SerreConditionS R Pxy 2 := by
  -- The public theorem is exactly the auxiliary source-local computation packaged above.
  exact reflexiveCounterexampleAmbient_serreConditionS2_aux k

/-- Helper for Example 15.23.17: the localization at the origin maximal ideal has depth too small
relative to its dimension, so `R` fails `(S_2)`. -/
private theorem reflexiveCounterexampleRing_not_serreConditionS2_aux :
    ¬ R ⊧ (S₂) := by
  -- TODO: complete the origin-local depth computation from the source proof using the quotient
  -- witness modulo `y` and the prime chain below `𝔪`.
  sorry

-- Proof sketch: this is the depth-theoretic failure exhibited in the text for the explicit
-- ring `R = k[y, x^2, xy, x^3]`.
/-- Example 15.23.17: if `R = k[y, x^2, xy, x^3] ⊂ k[x, y]`, then the ideal
`𝔪 = (y, x^2, xy, x^3)` and the displayed identifications
`Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]` are recorded by
`reflexiveCounterexampleAmbientDualEquivIdeal k` and
`reflexiveCounterexampleIdealDualEquivAmbient k`; in particular `k[x, y]` is reflexive and
`(S_2)` as an `R`-module, while `R` itself does not satisfy `(S_2)`. -/
@[stacks 0EBB]
theorem reflexiveCounterexampleRing_not_serreConditionS2 :
    ¬ R ⊧ (S₂) := by
  -- The final statement is the auxiliary origin-local obstruction proved for this explicit ring.
  exact reflexiveCounterexampleRing_not_serreConditionS2_aux k

end
