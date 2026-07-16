import Mathlib
import stacks_proof.stacks_project.Chap10.Remark_10_63_12
import stacks_proof.stacks_project.Chap10.Theorem_10_85_4
import stacks_proof.stacks_project.Chap15.Definition_15_15_1
import stacks_proof.stacks_project.Chap15.Lemma_15_3_3
import stacks_proof.stacks_project.Chap15.Lemma_15_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial IsLocalRing
open scoped BigOperators

universe u

noncomputable section

section

variable (k : Type u) [Field k]

local notation "I∞" =>
  Ideal.span (Set.range fun i : ℕ ↦ ((X i : MvPolynomial ℕ k) ^ 2))
local notation "R∞" => infiniteSquareZeroPolynomialQuotient k
local notation "F∞" => ℕ →₀ R∞

noncomputable local instance : SMul R∞ R∞ := ⟨(· * ·)⟩
noncomputable local instance : SMulZeroClass R∞ R∞ where
  smul := (· * ·)
  smul_zero := mul_zero
noncomputable local instance : MulAction R∞ R∞ where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc
noncomputable local instance : DistribSMul R∞ R∞ where
  smul := (· * ·)
  smul_zero := mul_zero
  smul_add := mul_add
noncomputable local instance : Module R∞ R∞ where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc
  smul_zero := mul_zero
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul
noncomputable local instance : Module R∞ F∞ := Finsupp.module ℕ R∞

/- Domain triage:
* primary domain: commutative algebra of local rings and weak association.
* sampled owner abstractions:
  `IsAutoAssociatedRing`,
  `isAutoAssociatedRing_iff`,
  `infiniteSquareZeroPolynomialQuotient`,
  `infiniteSquareZeroPolynomialQuotientResidueFieldEquiv`.
* layer choice: the explicit shift map below is the `source-facing` witness, while
  `IsAutoAssociatedRing` is the chapter's `core/canonical` owner for the ring-side clause of
  Example `15.15.5`; that clause should therefore be exposed as an instance rather than a
  parallel theorem.
* primitive data: the quotient ring `R∞` and the basis prescription `e_i ↦ f_i - x_i f_{i + 1}`.
* derived API: the square-zero identities, the induced linear map `squareZeroShiftMap`, and its
  injective non-split behavior.
-/

/-- The image of the variable `X i` in the square-zero polynomial quotient. -/
abbrev squareZeroVariable (i : ℕ) : R∞ :=
  Ideal.Quotient.mk I∞ (X i : MvPolynomial ℕ k)

-- Proof sketch: each square `X i ^ 2` lies in the defining ideal `I∞`, so its image in the
-- quotient is zero.
/-- Each coordinate variable is square-zero in the quotient ring. -/
@[simp] theorem squareZeroVariable_sq_eq_zero (i : ℕ) :
    squareZeroVariable k i ^ (2 : ℕ) = 0 := by
  -- The defining quotient relation kills every square `X i ^ 2`.
  change Ideal.Quotient.mk I∞ ((X i : MvPolynomial ℕ k) ^ (2 : ℕ)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

private def squareZeroShiftFamily (i : ℕ) : F∞ :=
  Finsupp.single i 1 - Finsupp.single (i + 1) (squareZeroVariable k i)

/-- The map `e_i ↦ f_i - x_i f_{i + 1}` on the countable free module over the square-zero
polynomial quotient. -/
noncomputable def squareZeroShiftMap :
    F∞ →ₗ[R∞] F∞ :=
  Finsupp.linearCombination R∞ (squareZeroShiftFamily k)

-- Proof sketch: unfold `squareZeroShiftMap`, use `Finsupp.linearCombination_single`, and rewrite
-- scalar multiplication on `Finsupp.single`.
/-- On a single basis term, the shift map acts by `e_i r ↦ e_i r - e_{i+1} (x_i r)`. -/
@[simp] theorem squareZeroShiftMap_single (i : ℕ) (r : R∞) :
    squareZeroShiftMap k (Finsupp.single i r) =
      Finsupp.single i r -
        Finsupp.single (i + 1) (squareZeroVariable k i * r) := by
  -- The basis-vector computation is exactly `linearCombination_single` followed by scalar
  -- multiplication on finitely supported singleton vectors.
  rw [squareZeroShiftMap, Finsupp.linearCombination_single]
  ext j
  change
    r * ((Finsupp.single i (1 : R∞) - Finsupp.single (i + 1) (squareZeroVariable k i)) j) =
      (Finsupp.single i r - Finsupp.single (i + 1) (squareZeroVariable k i * r)) j
  rw [Finsupp.sub_apply, Finsupp.sub_apply]
  by_cases hji : j = i
  · subst hji
    rw [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (Nat.ne_of_lt (Nat.lt_succ_self j)),
      Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (Nat.ne_of_lt (Nat.lt_succ_self j))]
    simp
  · by_cases hsucc : j = i + 1
    · subst hsucc
      rw [Finsupp.single_eq_of_ne (show i + 1 ≠ i by exact Nat.succ_ne_self _),
        Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show i + 1 ≠ i by exact Nat.succ_ne_self _),
        Finsupp.single_eq_same]
      rw [sub_eq_add_neg, sub_eq_add_neg]
      rw [mul_comm (squareZeroVariable k i) r]
      calc
        r * (0 + -squareZeroVariable k i) = r * -squareZeroVariable k i := by simp
        _ = -(r * squareZeroVariable k i) := by exact mul_neg r (squareZeroVariable k i)
        _ = 0 + -(r * squareZeroVariable k i) := by simp
    · rw [Finsupp.single_eq_of_ne hji, Finsupp.single_eq_of_ne hsucc,
        Finsupp.single_eq_of_ne hji, Finsupp.single_eq_of_ne hsucc]
      simp

/-- Helper for Example 15.15.5: the zeroth coordinate of the shift map is unchanged. -/
@[simp] lemma squareZeroShiftMap_coeff_zero (l : F∞) :
    squareZeroShiftMap k l 0 = l 0 := by
  classical
  -- Route correction: stabilize the triangular coordinate formula first, rather than unfolding
  -- the whole non-splitting argument through quotients and cokernels.
  induction l using Finsupp.induction_linear with
  | zero =>
      -- The zero vector has zero image in every coordinate.
      simp [squareZeroShiftMap]
  | add l m hl hm =>
      -- Coordinate `0` is preserved additively because `squareZeroShiftMap` is linear.
      simp [map_add, hl, hm]
  | single i r =>
      -- On a basis vector, only the `i`-coordinate survives at `0`.
      by_cases hi : i = 0
      · subst hi
        simp [squareZeroShiftMap_single]
      · simp [squareZeroShiftMap_single, hi]

/-- Helper for Example 15.15.5: the `(n + 1)`-st coordinate only depends on the current and
previous coefficients, giving the source-faithful lower-triangular recursion. -/
@[simp] lemma squareZeroShiftMap_coeff_succ (l : F∞) (n : ℕ) :
    squareZeroShiftMap k l (n + 1) =
      l (n + 1) - squareZeroVariable k n * l n := by
  classical
  induction l using Finsupp.induction_linear with
  | zero =>
      -- The triangular formula is immediate on the zero vector.
      simp [squareZeroShiftMap]
  | add l m hl hm =>
      -- Additivity preserves the recursion coordinatewise.
      calc
        squareZeroShiftMap k (l + m) (n + 1)
            = squareZeroShiftMap k l (n + 1) + squareZeroShiftMap k m (n + 1) := by
                rw [LinearMap.map_add]
                rfl
        _ =
            (l (n + 1) - squareZeroVariable k n * l n) +
              (m (n + 1) - squareZeroVariable k n * m n) := by
                rw [hl, hm]
        _ =
            (l + m) (n + 1) - squareZeroVariable k n * (l + m) n := by
                rw [Finsupp.add_apply, Finsupp.add_apply, mul_add]
                simp_rw [sub_eq_add_neg]
                abel
  | single i r =>
      -- A singleton contributes either on the diagonal `i = n + 1` or the subdiagonal `i = n`.
      by_cases hi : i = n
      · subst hi
        simp [squareZeroShiftMap_single]
      · by_cases hsucc : i = n + 1
        · subst hsucc
          simp [squareZeroShiftMap_single]
        · simp [squareZeroShiftMap_single, hi, hsucc]

/-- Helper for Example 15.15.5: the explicit shift map is injective by the triangular coordinate
recursion. -/
theorem squareZeroShiftMap_injective :
    Function.Injective (squareZeroShiftMap k) := by
  intro l m hEq
  -- Passing to the difference reduces injectivity to the vanishing of all coordinates of a kernel
  -- element, recovered inductively from the triangular recursion.
  have hKernel : squareZeroShiftMap k (l - m) = 0 := by
    calc
      squareZeroShiftMap k (l - m)
          = squareZeroShiftMap k l - squareZeroShiftMap k m := by
              rw [LinearMap.map_sub]
      _ = 0 := by rw [hEq, sub_self]
  apply Finsupp.ext
  intro n
  induction n with
  | zero =>
      -- The zeroth coordinate reads off the zeroth coefficient directly.
      have h0 := congrArg (fun x : F∞ ↦ x 0) hKernel
      exact sub_eq_zero.mp <| by simpa [squareZeroShiftMap_coeff_zero] using h0
  | succ n ih =>
      -- Once the previous coefficient vanishes, the next coordinate identifies the next one.
      have hsucc := congrArg (fun x : F∞ ↦ x (n + 1)) hKernel
      exact sub_eq_zero.mp <| by simpa [squareZeroShiftMap_coeff_succ, ih] using hsucc

/-- Helper for Example 15.15.5: the augmentation kills every square-zero variable. -/
@[simp] lemma infiniteSquareZeroPolynomialQuotientAugmentation_squareZeroVariable (i : ℕ) :
    infiniteSquareZeroPolynomialQuotientAugmentation k (squareZeroVariable k i) = 0 := by
  -- The augmentation is induced by the constant coefficient map, which vanishes on each variable.
  simp [squareZeroVariable, infiniteSquareZeroPolynomialQuotientAugmentation]

/-- Helper for Example 15.15.5: every square-zero variable lies in the maximal ideal. -/
lemma squareZeroVariable_mem_maximalIdeal (i : ℕ) :
    squareZeroVariable k i ∈ maximalIdeal R∞ := by
  -- A variable has zero augmentation, so the unit criterion forces it to be a nonunit.
  have hnonunit : squareZeroVariable k i ∈ nonunits R∞ := by
    intro hunit
    have hne :
        infiniteSquareZeroPolynomialQuotientAugmentation k (squareZeroVariable k i) ≠ 0 :=
      (infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero
        (k := k) (x := squareZeroVariable k i)).1 hunit
    exact hne <| infiniteSquareZeroPolynomialQuotientAugmentation_squareZeroVariable (k := k) i
  exact (IsLocalRing.mem_maximalIdeal (squareZeroVariable k i)).2 hnonunit

/-- Helper for Example 15.15.5: the ideal generated by the square-zero variables is contained in
the maximal ideal. -/
lemma span_squareZeroVariables_le_maximalIdeal :
    Ideal.span (Set.range fun i : ℕ ↦ squareZeroVariable k i) ≤ maximalIdeal R∞ := by
  -- It suffices to check the generators, and each variable was shown above to be a nonunit.
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact squareZeroVariable_mem_maximalIdeal (k := k) i

/-- Helper for Example 15.15.5: the maximal ideal is exactly the kernel of the augmentation. -/
lemma maximalIdeal_eq_augmentation_ker :
    maximalIdeal R∞ = RingHom.ker (infiniteSquareZeroPolynomialQuotientAugmentation k) := by
  ext x
  change x ∈ maximalIdeal R∞ ↔ infiniteSquareZeroPolynomialQuotientAugmentation k x = 0
  constructor
  · intro hx
    -- Elements of the maximal ideal are nonunits, hence have zero augmentation by the unit test.
    by_contra hx0
    have hxunit : IsUnit x :=
      (infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero (k := k) x).2 hx0
    exact ((IsLocalRing.mem_maximalIdeal x).1 hx) hxunit
  · intro hx
    -- Conversely, nonzero augmentation is exactly the unit locus, so zero augmentation is maximal.
    have hnonunit : x ∈ nonunits R∞ := by
      intro hxunit
      exact
        ((infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero (k := k) x).1
          hxunit) hx
    exact (IsLocalRing.mem_maximalIdeal x).2 hnonunit

/-- Helper for Example 15.15.5: on the polynomial ring, the kernel of the constant coefficient map
is the ideal generated by all variables. -/
lemma ker_constantCoeff_eq_span_variables :
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ℕ k →+* k) =
      Ideal.span (MvPolynomial.X '' (Set.univ : Set ℕ)) := by
  ext p
  rw [RingHom.mem_ker]
  constructor
  · intro hp
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hmzero
    have hm_eq_zero : m = 0 := by
      ext i
      have hmi : m i = 0 := by
        by_contra hmi
        exact hmzero ⟨i, Set.mem_univ i, hmi⟩
      simpa using hmi
    have hcoeff : MvPolynomial.coeff m p ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    exact hcoeff <| by simpa [MvPolynomial.constantCoeff, hm_eq_zero] using hp
  · intro hp
    rw [MvPolynomial.mem_ideal_span_X_image] at hp
    by_contra hcoeff
    have hzero_mem : (0 : ℕ →₀ ℕ) ∈ p.support := MvPolynomial.mem_support_iff.mpr hcoeff
    obtain ⟨i, -, hi⟩ := hp 0 hzero_mem
    simpa using hi

/-- Helper for Example 15.15.5: the augmentation kernel of the square-zero quotient is generated
by the images of the variables. -/
lemma augmentation_ker_eq_span_squareZeroVariables :
    RingHom.ker (infiniteSquareZeroPolynomialQuotientAugmentation k) =
      Ideal.span (Set.range fun i : ℕ ↦ squareZeroVariable k i) := by
  -- Transport the polynomial-side kernel computation across the quotient map.
  calc
    RingHom.ker (infiniteSquareZeroPolynomialQuotientAugmentation k)
        = Ideal.map (Ideal.Quotient.mk I∞)
            (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ℕ k →+* k)) := by
              simpa [infiniteSquareZeroPolynomialQuotientAugmentation] using
                (Ideal.ker_quotient_lift
                  (MvPolynomial.constantCoeff : MvPolynomial ℕ k →+* k)
                  (by
                    rw [Ideal.span_le]
                    rintro _ ⟨i, rfl⟩
                    simp [RingHom.mem_ker, MvPolynomial.constantCoeff, MvPolynomial.X_pow_eq_monomial]))
    _ = Ideal.map (Ideal.Quotient.mk I∞)
          (Ideal.span (MvPolynomial.X '' (Set.univ : Set ℕ))) := by
            rw [ker_constantCoeff_eq_span_variables (k := k)]
    _ = Ideal.span ((Ideal.Quotient.mk I∞) '' (MvPolynomial.X '' (Set.univ : Set ℕ))) := by
            rw [Ideal.map_span]
    _ = Ideal.span (Set.range fun i : ℕ ↦ squareZeroVariable k i) := by
            congr 1
            ext x
            constructor
            · rintro ⟨y, ⟨i, -, rfl⟩, rfl⟩
              exact ⟨i, rfl⟩
            · rintro ⟨i, rfl⟩
              exact ⟨X i, ⟨i, Set.mem_univ i, rfl⟩, rfl⟩

/-- Helper for Example 15.15.5: the maximal ideal is generated by the square-zero variables. -/
lemma maximalIdeal_eq_span_squareZeroVariables :
    maximalIdeal R∞ = Ideal.span (Set.range fun i : ℕ ↦ squareZeroVariable k i) := by
  -- The local-ring maximal ideal is exactly the augmentation kernel computed above.
  rw [maximalIdeal_eq_augmentation_ker (k := k),
    augmentation_ker_eq_span_squareZeroVariables (k := k)]

/-- Helper for Example 15.15.5: the squarefree prefix exponent vector records one copy of each
variable from `0` through `n`. -/
private abbrev squarefreePrefixExponent (n : ℕ) : ℕ →₀ ℕ :=
  Finset.sum (Finset.range (n + 1)) fun i ↦ (Finsupp.single i 1 : ℕ →₀ ℕ)

/-- Helper for Example 15.15.5: the finite prefix product of variables is the monomial with the
squarefree prefix exponent vector. -/
private lemma squarefree_prefix_product_eq_monomial (n : ℕ) :
    Finset.prod (Finset.range (n + 1)) (fun i ↦ (X i : MvPolynomial ℕ k)) =
      MvPolynomial.monomial (squarefreePrefixExponent n) (1 : k) := by
  -- Rewrite the product inductively so that `MvPolynomial.monomial_mul` keeps track of the
  -- exponent vector exactly.
  induction n with
  | zero =>
      simpa [squarefreePrefixExponent] using
        (MvPolynomial.X_pow_eq_monomial (R := k) (σ := ℕ) (n := 0) (e := 1))
  | succ n ih =>
      calc
        Finset.prod (Finset.range (n + 1 + 1)) (fun i ↦ (X i : MvPolynomial ℕ k))
            = Finset.prod (Finset.range (n + 1)) (fun i ↦ (X i : MvPolynomial ℕ k)) *
                X (n + 1) := by
                  rw [Finset.prod_range_succ]
        _ = MvPolynomial.monomial (squarefreePrefixExponent n) (1 : k) * X (n + 1) := by
                rw [ih]
        _ = MvPolynomial.monomial (squarefreePrefixExponent n) (1 : k) *
              MvPolynomial.monomial (Finsupp.single (n + 1) 1) (1 : k) := by
                rw [show X (n + 1) =
                  MvPolynomial.monomial (Finsupp.single (n + 1) 1) (1 : k) by
                    simpa using
                      (MvPolynomial.X_pow_eq_monomial
                        (R := k) (σ := ℕ) (n := n + 1) (e := 1))]
        _ = MvPolynomial.monomial
              (squarefreePrefixExponent n + Finsupp.single (n + 1) 1) (1 : k) := by
                rw [MvPolynomial.monomial_mul]
                simp
        _ = MvPolynomial.monomial (squarefreePrefixExponent (n + 1)) (1 : k) := by
                simp [squarefreePrefixExponent, Finset.sum_range_succ]

/-- Helper for Example 15.15.5: each coordinate of the squarefree prefix exponent is at most
`1`. -/
private lemma squarefreePrefixExponent_apply_eq_indicator (n i : ℕ) :
    squarefreePrefixExponent n i = if i ∈ Finset.range (n + 1) then 1 else 0 := by
  -- The sum of singletons contributes exactly once when `i` lies in the chosen finite prefix and
  -- otherwise contributes nothing.
  simp [squarefreePrefixExponent, Finsupp.single_apply]

/-- Helper for Example 15.15.5: the squarefree prefix monomial is not in the square ideal on the
polynomial side. -/
lemma squarefree_prefix_product_not_mem_squareZeroIdeal (n : ℕ) :
    Finset.prod (Finset.range (n + 1)) (fun i ↦ (X i : MvPolynomial ℕ k)) ∉ I∞ := by
  -- Route correction: rewrite the generators as square monomials and then use the monomial ideal
  -- membership criterion instead of building a bespoke support ideal.
  have hspan :
      I∞ =
        Ideal.span
          ((fun s : ℕ →₀ ℕ ↦ (MvPolynomial.monomial s) (1 : k)) ''
            Set.range (fun i : ℕ ↦ Finsupp.single i 2)) := by
    congr 1
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Finsupp.single i 2, ⟨i, rfl⟩, by
        simpa [eq_comm] using
          (MvPolynomial.X_pow_eq_monomial (R := k) (σ := ℕ) (n := i) (e := 2))⟩
    · rintro ⟨q, ⟨i, rfl⟩, hp⟩
      exact ⟨i, by simpa [eq_comm, MvPolynomial.X_pow_eq_monomial] using hp⟩
  intro hmem
  rw [hspan, MvPolynomial.mem_ideal_span_monomial_image] at hmem
  have hsupport :
      squarefreePrefixExponent n ∈
        (Finset.prod (Finset.range (n + 1)) (fun i ↦ (X i : MvPolynomial ℕ k))).support := by
    simpa [squarefree_prefix_product_eq_monomial (k := k) n]
  rcases hmem (squarefreePrefixExponent n) hsupport with ⟨s, ⟨i, hs⟩, hs_le⟩
  subst hs
  have hnot : ¬ 2 ≤ squarefreePrefixExponent n i := by
    rw [squarefreePrefixExponent_apply_eq_indicator (n := n) (i := i)]
    split_ifs <;> omega
  exact hnot <| by simpa using hs_le i

/-- Helper for Example 15.15.5: every finite prefix product of distinct square-zero variables is
nonzero in the quotient ring. -/
lemma squareZeroVariable_prefixProduct_ne_zero (n : ℕ) :
    Finset.prod (Finset.range (n + 1)) (fun i ↦ squareZeroVariable k i) ≠ 0 := by
  -- Push the polynomial-side obstruction through the quotient map defining the square-zero ring.
  intro hzero
  have hzero' :
      Ideal.Quotient.mk I∞
        (Finset.prod (Finset.range (n + 1)) (fun i ↦ (X i : MvPolynomial ℕ k))) = 0 := by
    simpa [squareZeroVariable] using hzero
  have hmem :
      Finset.prod (Finset.range (n + 1)) (fun i ↦ (X i : MvPolynomial ℕ k)) ∈ I∞ :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero'
  exact squarefree_prefix_product_not_mem_squareZeroIdeal (k := k) n hmem

/-- Helper for Example 15.15.5: the torsion ideal of `x₀` has radical equal to the maximal ideal.
-/
lemma squareZeroVariable_zero_torsion_radical_eq_maximalIdeal :
    (Ideal.torsionOf R∞ R∞ (squareZeroVariable k 0)).radical = maximalIdeal R∞ := by
  let J : Ideal R∞ := Ideal.torsionOf R∞ R∞ (squareZeroVariable k 0)
  apply le_antisymm
  · -- Any annihilator of the nonzero element `x₀` lies in the maximal ideal, so the same holds
    -- after taking radicals.
    have hJle : J ≤ maximalIdeal R∞ := by
      intro a ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      rcases hunit with ⟨u, rfl⟩
      have hax : (↑u : R∞) * squareZeroVariable k 0 = 0 := by
        simpa [J, Ideal.mem_torsionOf_iff, smul_eq_mul] using ha
      have hxzero : squareZeroVariable k 0 = 0 := by
        have := congrArg (fun t : R∞ ↦ ↑u⁻¹ * t) hax
        simpa [mul_assoc] using this
      have hx_ne : squareZeroVariable k 0 ≠ 0 := by
        simpa using squareZeroVariable_prefixProduct_ne_zero (k := k) 0
      exact hx_ne hxzero
    simpa [((maximalIdeal.isMaximal R∞).isPrime).radical] using Ideal.radical_mono hJle
  · -- Every square-zero variable has square equal to zero, hence lies in the radical of `J`.
    rw [maximalIdeal_eq_span_squareZeroVariables (k := k)]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    refine (Ideal.mem_radical_iff).2 ?_
    refine ⟨2, ?_⟩
    exact (squareZeroVariable_sq_eq_zero (k := k) i).symm ▸ J.zero_mem


/-- Example 15.15.5 (ring side): the square-zero quotient
`k[x₀, x₁, x₂, \ldots] / (x_i^2)` is an auto-associated local ring. -/
-- TODO: use `x₀` as the weak-association witness, show its torsion ideal is contained in the
-- maximal ideal, and prove every prime above it contains all square-zero variables.
instance :
    IsAutoAssociatedRing R∞ := by
  -- The source-faithful witness is `x₀`, whose torsion ideal has maximal-ideal radical.
  rw [isAutoAssociatedRing_iff]
  have htorsion_prime :
      (Ideal.torsionOf R∞ R∞ (squareZeroVariable k 0)).radical.IsPrime := by
    simpa [squareZeroVariable_zero_torsion_radical_eq_maximalIdeal (k := k)] using
      (maximalIdeal.isMaximal R∞).isPrime
  letI := htorsion_prime
  refine ⟨squareZeroVariable k 0, ?_⟩
  -- Once the radical is prime, minimal primes collapse to the singleton containing that radical.
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  simpa [squareZeroVariable_zero_torsion_radical_eq_maximalIdeal (k := k)]

-- Proof sketch: prove injectivity by checking linear independence on each finite partial family
-- of images `u(e₁), ..., u(eₙ)`. To rule out a splitting, tensor with the residue field `k` to get
-- a bijection via `infiniteSquareZeroPolynomialQuotientResidueFieldEquiv k`; a left inverse would
-- then force surjectivity, but `f₁` would require the infinite preimage
-- `e₁ + x₁ e₂ + x₁ x₂ e₃ + ⋯`, which is not finitely supported.
/- Companion to Example 15.15.5 (module side): over the auto-associated local ring
`R = k[x₀, x₁, x₂, \ldots] / (x_i^2)`, whose residue field is canonically `k`, the map
`u(e_i) = f_i - x_i f_{i + 1}` on the free module `ℕ →₀ R` is injective but not a split
injection. -/
-- TODO: combine the explicit non-surjectivity witness `f₀` with a source-faithful proof that any
-- left inverse makes the cokernel projective, free, and maximal-ideal generated, hence zero.
/-- Helper for Example 15.15.5: on a basis vector, the shift map differs from the identity by an
element of `maximalIdeal R∞ • ⊤`. -/
lemma squareZeroShiftMap_single_sub_mem_maximalIdeal_smul_top (i : ℕ) (r : R∞) :
    squareZeroShiftMap k (Finsupp.single i r) - Finsupp.single i r ∈
      maximalIdeal R∞ • (⊤ : Submodule R∞ F∞) := by
  -- The source-faithful basis computation isolates the single off-diagonal term.
  have hcoeff :
      squareZeroVariable k i * r ∈ maximalIdeal R∞ := by
    exact Ideal.mul_mem_right r (maximalIdeal R∞) (squareZeroVariable_mem_maximalIdeal (k := k) i)
  have hsingle :
      Finsupp.single (i + 1) (squareZeroVariable k i * r) ∈
        maximalIdeal R∞ • (⊤ : Submodule R∞ F∞) := by
    -- The singleton is a scalar multiple of the `(i + 1)`-st basis vector by a maximal-ideal
    -- coefficient.
    simpa using
      (Submodule.smul_mem_smul hcoeff
        (show Finsupp.single (i + 1) (1 : R∞) ∈ (⊤ : Submodule R∞ F∞) by simp) :
          (squareZeroVariable k i * r) • Finsupp.single (i + 1) (1 : R∞) ∈
            maximalIdeal R∞ • (⊤ : Submodule R∞ F∞))
  have hshift :
      squareZeroShiftMap k (Finsupp.single i r) - Finsupp.single i r =
        -Finsupp.single (i + 1) (squareZeroVariable k i * r) := by
    -- After canceling the diagonal term, only the off-diagonal correction remains.
    rw [squareZeroShiftMap_single]
    abel
  rw [hshift]
  exact Submodule.neg_mem _ hsingle

/-- Helper for Example 15.15.5: the shift map differs from the identity by an element of
`maximalIdeal R∞ • ⊤` on every finitely supported vector. -/
lemma squareZeroShiftMap_sub_mem_maximalIdeal_smul_top (l : F∞) :
    squareZeroShiftMap k l - l ∈ maximalIdeal R∞ • (⊤ : Submodule R∞ F∞) := by
  classical
  -- Extend the basis computation by linear induction over finitely supported functions.
  induction l using Finsupp.induction_linear with
  | zero =>
      -- The zero vector is fixed, so the difference is zero.
      simpa [squareZeroShiftMap]
  | add l m hl hm =>
      -- Linearity turns the global difference into the sum of the two smaller differences.
      have hadd :
          squareZeroShiftMap k (l + m) - (l + m) =
            (squareZeroShiftMap k l - l) + (squareZeroShiftMap k m - m) := by
        rw [LinearMap.map_add]
        abel
      rw [hadd]
      exact Submodule.add_mem _ hl hm
  | single i r =>
      -- The singleton case is the previously established basis computation.
      exact squareZeroShiftMap_single_sub_mem_maximalIdeal_smul_top (k := k) i r

/-- Helper for Example 15.15.5: on quotient representatives, the reduced shift map acts as the
identity. -/
lemma squareZeroShiftMap_quotientMapByIdeal_apply_mkQ (l : F∞) :
    (squareZeroShiftMap k).quotientMapByIdeal (maximalIdeal R∞)
      ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l) =
        (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l := by
  -- Evaluate the quotient map on a representative and then use the maximal-ideal difference
  -- computation to identify the resulting class.
  calc
    (squareZeroShiftMap k).quotientMapByIdeal (maximalIdeal R∞)
        ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l)
      = (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ (squareZeroShiftMap k l) := by
          rw [quotientMapByIdeal_apply_mkQ]
    _ = (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l := by
          exact (Submodule.Quotient.eq _).2
            (squareZeroShiftMap_sub_mem_maximalIdeal_smul_top (k := k) l)

/-- Helper for Example 15.15.5: modulo the maximal ideal, the shift map becomes the identity
because each off-diagonal term is killed by the residue map. -/
lemma squareZeroShiftMap_quotientMapByIdeal_maximalIdeal_eq_id :
    (squareZeroShiftMap k).quotientMapByIdeal (maximalIdeal R∞) = LinearMap.id := by
  -- Check the induced map on quotient representatives, where the maximal-ideal correction
  -- vanishes and only the diagonal identity term survives.
  apply DFunLike.ext
  intro x
  obtain ⟨l, rfl⟩ :=
    Submodule.mkQ_surjective (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)) x
  simpa using squareZeroShiftMap_quotientMapByIdeal_apply_mkQ (k := k) l

/-- Helper for Example 15.15.5: if `v` is a left inverse to the shift map, then `v` also reduces
to the identity modulo the maximal ideal. -/
lemma split_left_inverse_quotientMapByIdeal_maximalIdeal_eq_id
    {v : F∞ →ₗ[R∞] F∞}
    (hv : v ∘ₗ squareZeroShiftMap k = LinearMap.id) :
    v.quotientMapByIdeal (maximalIdeal R∞) = LinearMap.id := by
  -- Reduce the left-inverse identity modulo `maximalIdeal R∞` and cancel the already-corrected
  -- shift map.
  apply DFunLike.ext
  intro x
  obtain ⟨l, rfl⟩ :=
    Submodule.mkQ_surjective (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)) x
  calc
    v.quotientMapByIdeal (maximalIdeal R∞)
        ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l)
      =
        v.quotientMapByIdeal (maximalIdeal R∞)
          (LinearMap.id ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l)) := by
            rfl
    _ =
        v.quotientMapByIdeal (maximalIdeal R∞)
          ((squareZeroShiftMap k).quotientMapByIdeal (maximalIdeal R∞)
            ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l)) := by
              rw [squareZeroShiftMap_quotientMapByIdeal_maximalIdeal_eq_id]
    _ =
        ((v.quotientMapByIdeal (maximalIdeal R∞)).comp
          ((squareZeroShiftMap k).quotientMapByIdeal (maximalIdeal R∞)))
            ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l) := by
              rfl
    _ =
        ((v.comp (squareZeroShiftMap k)).quotientMapByIdeal (maximalIdeal R∞))
          ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l) := by
            rw [← quotientMapByIdeal_comp]
    _ = LinearMap.id ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ l) := by
          simpa [hv]

/-- Helper for Example 15.15.5: the kernel of a left inverse is a split summand, hence
projective. -/
lemma split_left_inverse_kernel_projective
    {v : F∞ →ₗ[R∞] F∞}
    (hv : v ∘ₗ squareZeroShiftMap k = LinearMap.id) :
    Module.Projective R∞ (LinearMap.ker v) := by
  let p : F∞ →ₗ[R∞] LinearMap.ker v :=
    LinearMap.codRestrict (LinearMap.ker v)
      (LinearMap.id - (squareZeroShiftMap k).comp v)
      (fun x ↦ by
        -- Applying `v` to the correction term removes the section part by `hv`.
        change v (x - squareZeroShiftMap k (v x)) = 0
        have hv_apply : v (squareZeroShiftMap k (v x)) = v x := by
          simpa [LinearMap.comp_apply] using
            congrArg (fun f : F∞ →ₗ[R∞] F∞ ↦ f (v x)) hv
        simpa [hv_apply])
  have hp : p.comp (LinearMap.ker v).subtype = LinearMap.id := by
    -- Restricting the correction term back to `ker v` simply returns the kernel element.
    ext x a
    change (x.1 - squareZeroShiftMap k (v x.1)) a = x.1 a
    simpa [x.2]
  exact Module.Projective.of_split (LinearMap.ker v).subtype p hp

/-- Helper for Example 15.15.5: the kernel complement of a left inverse satisfies
`K ≤ maximalIdeal R∞ • K` because both maps reduce to the identity modulo the maximal ideal. -/
lemma split_left_inverse_kernel_le_maximalIdeal_smul
    {v : F∞ →ₗ[R∞] F∞}
    (hv : v ∘ₗ squareZeroShiftMap k = LinearMap.id) :
    (⊤ : Submodule R∞ (LinearMap.ker v)) ≤
      maximalIdeal R∞ • (⊤ : Submodule R∞ (LinearMap.ker v)) := by
  intro x _
  -- First show the ambient representative of `x` is zero modulo `maximalIdeal R∞`.
  have hx_zero :
      (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ x.1 = 0 := by
    calc
      (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ x.1
          =
            (LinearMap.id :
              (F∞ ⧸ (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞))) →ₗ[R∞]
                (F∞ ⧸ (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞))))
              ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ x.1) := by
                rfl
      _ =
          v.quotientMapByIdeal (maximalIdeal R∞)
            ((maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ x.1) := by
              rw [split_left_inverse_quotientMapByIdeal_maximalIdeal_eq_id (k := k) hv]
      _ =
          (maximalIdeal R∞ • (⊤ : Submodule R∞ F∞)).mkQ (v x.1) := by
            rw [quotientMapByIdeal_apply_mkQ]
      _ = 0 := by simpa [x.2]
  have hx_mem : x.1 ∈ maximalIdeal R∞ • (⊤ : Submodule R∞ F∞) :=
    (Submodule.Quotient.mk_eq_zero _).1 hx_zero
  -- Then use the right-inverse correction lemma to move that ambient membership into `ker v`.
  have hx_map :
      x.1 ∈
        Submodule.map (LinearMap.ker v).subtype
          (maximalIdeal R∞ • (⊤ : Submodule R∞ (LinearMap.ker v))) := by
    simpa [x.2] using
      sub_section_mem_map_smul_top_ker_of_rightInverse
        (I := maximalIdeal R∞) v (squareZeroShiftMap k) hv (z := x.1) hx_mem
  rcases hx_map with ⟨y, hyI, hyval⟩
  have hyx : y = x := by
    apply Subtype.ext
    simpa using hyval
  simpa [hyx] using hyI

/-- Helper for Example 15.15.5: in the scalar module `R∞`, belonging to `J • ⊤` is equivalent to
belonging to the ideal `J` itself. -/
lemma mem_smul_top_iff_mem_ideal (J : Ideal R∞) (x : R∞) :
    x ∈ (J • (⊤ : Submodule R∞ R∞) : Submodule R∞ R∞) ↔ x ∈ J := by
  constructor
  · intro hx
    -- Unpack the submodule smul as a finite sum of scalar multiples coming from `J`.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      simpa using Ideal.mul_mem_right y J hr
    · intro y z hy hz
      exact J.add_mem hy hz
  · intro hx
    -- The reverse direction is the single-generator witness `x • 1`.
    simpa using
      (Submodule.smul_mem_smul (I := J) (N := (⊤ : Submodule R∞ R∞)) hx (by simp) :
        x • (1 : R∞) ∈ J • (⊤ : Submodule R∞ R∞))

/-- Helper for Example 15.15.5: a free module over the local ring `R∞` is zero once every
element lies in `maximalIdeal R∞ • M`. -/
lemma subsingleton_of_free_of_top_le_maximalIdeal_smul
    {M : Type*} [AddCommGroup M] [Module R∞ M] [Module.Free R∞ M]
    (htop : (⊤ : Submodule R∞ M) ≤ maximalIdeal R∞ • (⊤ : Submodule R∞ M)) :
    Subsingleton M := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex R∞ M) R∞ M := Module.Free.chooseBasis R∞ M
  have hindex_empty : IsEmpty (Module.Free.ChooseBasisIndex R∞ M) := by
    by_contra hnonempty
    obtain ⟨i⟩ := not_isEmpty_iff.mp hnonempty
    let coord : M →ₗ[R∞] R∞ := (Finsupp.lapply i).comp b.repr.toLinearMap
    have hbi :
        b i ∈ maximalIdeal R∞ • (⊤ : Submodule R∞ M) := htop (by simp)
    have hcoord_mem :
        coord (b i) ∈ maximalIdeal R∞ • (⊤ : Submodule R∞ R∞) := by
      exact (Submodule.smul_top_le_comap_smul_top (maximalIdeal R∞) coord) hbi
    have hone_mem :
        (1 : R∞) ∈ maximalIdeal R∞ • (⊤ : Submodule R∞ R∞) := by
      simpa [coord, Finsupp.lapply_apply] using hcoord_mem
    have hone_max :
        (1 : R∞) ∈ maximalIdeal R∞ :=
      (mem_smul_top_iff_mem_ideal (k := k) (maximalIdeal R∞) 1).1 hone_mem
    have htop_eq : maximalIdeal R∞ = ⊤ :=
      (maximalIdeal R∞).eq_top_of_isUnit_mem hone_max (isUnit_one : IsUnit (1 : R∞))
    exact (maximalIdeal.isMaximal R∞).ne_top htop_eq
  refine ⟨fun x y ↦ ?_⟩
  -- With no basis indices left, all coordinate functions are vacuous and every two elements agree.
  apply b.repr.injective
  ext i
  exact (hindex_empty.false i).elim

/-- Helper for Example 15.15.5: the vector `f₀` has no finitely supported preimage under the shift
map because the coordinate recursion forces the infinite prefix-product tail from the source. -/
lemma squareZeroShiftMap_not_surjective :
    ¬ Function.Surjective (squareZeroShiftMap k) := by
  intro hsurj
  obtain ⟨l, hl⟩ := hsurj (Finsupp.single 0 1)
  -- The coordinate identities force the source-faithful infinite recursion
  -- `l₀ = 1` and `l_{n+1} = x_n l_n`.
  have hprefix :
      ∀ n : ℕ, l n = Finset.prod (Finset.range n) (fun i ↦ squareZeroVariable k i) := by
    intro n
    induction n with
    | zero =>
        have h0 := congrArg (fun x : F∞ ↦ x 0) hl
        simpa [squareZeroShiftMap_coeff_zero] using h0
    | succ n ih =>
        have hsucc := congrArg (fun x : F∞ ↦ x (n + 1)) hl
        have hrec : l (n + 1) = squareZeroVariable k n * l n := by
          exact sub_eq_zero.mp <| by
            simpa [squareZeroShiftMap_coeff_succ] using hsucc
        calc
          l (n + 1) = squareZeroVariable k n * l n := hrec
          _ = squareZeroVariable k n *
                Finset.prod (Finset.range n) (fun i ↦ squareZeroVariable k i) := by
                  rw [ih]
          _ = Finset.prod (Finset.range (n + 1)) (fun i ↦ squareZeroVariable k i) := by
                  rw [Finset.prod_range_succ, mul_comm]
  let N : ℕ := l.support.sup id
  have hNzero : l (N + 1) = 0 := by
    by_cases hmem : N + 1 ∈ l.support
    · have hle : N + 1 ≤ N := by
        simpa [N] using (Finset.le_sup hmem : id (N + 1) ≤ l.support.sup id)
      omega
    · by_contra hne
      exact hmem (Finsupp.mem_support_iff.mpr hne)
  have hNnonzero :
      Finset.prod (Finset.range (N + 1)) (fun i ↦ squareZeroVariable k i) ≠ 0 :=
    squareZeroVariable_prefixProduct_ne_zero (k := k) N
  exact hNnonzero <| by simpa [hprefix (N + 1)] using hNzero

theorem squareZeroShiftMap_injective_not_split :
    Function.Injective (squareZeroShiftMap k) ∧
      ¬ ∃ v : F∞ →ₗ[R∞] F∞,
          v ∘ₗ squareZeroShiftMap k = LinearMap.id := by
  refine ⟨squareZeroShiftMap_injective (k := k), ?_⟩
  -- Route correction: pass from a hypothetical left inverse to its complementary kernel, show
  -- that kernel satisfies `K = maximalIdeal R∞ • K`, and then kill it using freeness over the
  -- local ring.
  rintro ⟨v, hv⟩
  have hprojective : Module.Projective R∞ (LinearMap.ker v) :=
    split_left_inverse_kernel_projective (k := k) hv
  letI : Module.Projective R∞ (LinearMap.ker v) := hprojective
  letI : Module.Free R∞ (LinearMap.ker v) := projective_module_free_of_isLocalRing
  have hker_subsingleton : Subsingleton (LinearMap.ker v) :=
    subsingleton_of_free_of_top_le_maximalIdeal_smul (k := k)
      (split_left_inverse_kernel_le_maximalIdeal_smul (k := k) hv)
  have hsurj : Function.Surjective (squareZeroShiftMap k) := by
    intro y
    refine ⟨v y, ?_⟩
    have hker :
        y - squareZeroShiftMap k (v y) ∈ LinearMap.ker v :=
      sub_section_mem_ker_of_rightInverse v (squareZeroShiftMap k) hv y
    have hzero :
        (⟨y - squareZeroShiftMap k (v y), hker⟩ : LinearMap.ker v) = 0 :=
      Subsingleton.elim _ _
    have hzero_val : y - squareZeroShiftMap k (v y) = 0 := congrArg Subtype.val hzero
    exact (sub_eq_zero.mp hzero_val).symm
  exact squareZeroShiftMap_not_surjective (k := k) hsurj

end
