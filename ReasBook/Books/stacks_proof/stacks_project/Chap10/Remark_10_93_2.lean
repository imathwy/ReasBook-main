import Mathlib
import StacksProject_2024.Chap10.Lemma_10_91_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace Module

open scoped PowerSeries

/-
Domain triage:
- `source-facing`: the coefficientwise `p`-adic divisibility-tail condition on `ℤ⟦X⟧` and
  the resulting submodule singled out in the remark;
- `core/canonical`: the chapter owner predicates `Module.Flat`, `Module.MittagLeffler`, and
  `Module.Projective`;
- `bridge/view`: the nonfree divisible-tail submodule obstructing projectivity of `ℤ⟦X⟧`.
Sampled owner-level declarations in this domain:
- `Module.MittagLeffler` from `Definition_10_88_7`;
- `Module.noetherian_pi_flat_and_mittagLeffler` from `Lemma_10_91_3`;
- `Module.noetherian_mvPowerSeries_flat_and_mittagLeffler` from `Lemma_10_91_4`;
- `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated` from
  `Theorem_10_93_3`.
Primitive data are exactly `HasPAdicallyDivisibleTail` and the induced `Submodule`; the flat,
Mittag-Leffler, and projective clauses are derived API and should reuse the chapter owners rather
than a parallel local class. -/

/-- A formal power series over `ℤ` has an eventually `p`-adically divisible tail if, for every
integer `m`, only finitely many coefficients fail to be divisible by `p^(m + 1)`. This is the
same positive-exponent condition from the remark, reindexed to avoid a redundant positivity
guard. -/
def HasPAdicallyDivisibleTail (p : ℕ) (f : ℤ⟦X⟧) : Prop :=
  ∀ m : ℕ, Set.Finite {i : ℕ | ¬ ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i f)}

/-- Unfolding `HasPAdicallyDivisibleTail` gives the coefficientwise eventual divisibility condition
used in the remark, with the positive exponent written as `m + 1`. -/
theorem hasPAdicallyDivisibleTail_iff (p : ℕ) (f : ℤ⟦X⟧) :
    HasPAdicallyDivisibleTail p f ↔
      ∀ m : ℕ, Set.Finite {i : ℕ | ¬ ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i f)} :=
  Iff.rfl

-- Proof sketch: every coefficient of the zero series is `0`, so it is divisible by every power of
-- `p`; hence the exceptional set is empty for each exponent `m + 1`.
/-- The zero power series has an eventually `p`-adically divisible tail. -/
theorem hasPAdicallyDivisibleTail_zero (p : ℕ) :
    HasPAdicallyDivisibleTail p (0 : ℤ⟦X⟧) := by
  -- For each exponent, all zero-series coefficients are zero and hence divisible.
  intro m
  simp

-- Proof sketch: for each fixed `m`, the coefficients of `f + g` can fail to be divisible by
-- `p^(m + 1)`
-- only where the corresponding coefficient of `f` or of `g` already fails, so the exceptional set
-- is contained in the union of two finite sets.
/-- The eventually `p`-adically divisible-tail condition is closed under addition. -/
theorem hasPAdicallyDivisibleTail_add (p : ℕ) {f g : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) (hg : HasPAdicallyDivisibleTail p g) :
    HasPAdicallyDivisibleTail p (f + g) := by
  -- The bad coefficients of `f + g` lie in the union of the bad coefficients of `f` and `g`.
  intro m
  refine ((hf m).union (hg m)).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq, Set.mem_union] at hi ⊢
  by_contra hnot
  push Not at hnot
  exact hi (by simpa using dvd_add hnot.1 hnot.2)

-- Proof sketch: multiplying all coefficients by an integer scalar preserves divisibility by each
-- fixed power `p^(m + 1)`, so no new infinite exceptional set can appear.
/-- The eventually `p`-adically divisible-tail condition is closed under scalar multiplication. -/
theorem hasPAdicallyDivisibleTail_smul (p : ℕ) (n : ℤ) {f : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) :
    HasPAdicallyDivisibleTail p (n • f) := by
  -- If a coefficient of `f` is divisible by the fixed power of `p`, then so is its scalar multiple.
  intro m
  refine (hf m).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  intro hdiv
  exact hi (by
    simpa only [PowerSeries.coeff_smul] using dvd_mul_of_dvd_right hdiv n)

/-- The submodule of `ℤ[[x]]` whose coefficients are eventually divisible by every power of `p`. -/
def pAdicallyDivisibleTailSubmodule (p : ℕ) : Submodule ℤ ℤ⟦X⟧ where
  carrier := {f | HasPAdicallyDivisibleTail p f}
  zero_mem' := hasPAdicallyDivisibleTail_zero p
  add_mem' := fun hf hg ↦ hasPAdicallyDivisibleTail_add p hf hg
  smul_mem' := fun n _ hf ↦ hasPAdicallyDivisibleTail_smul p n hf

/-- Membership in `pAdicallyDivisibleTailSubmodule p` is exactly the eventual divisibility
condition on coefficients. -/
theorem mem_pAdicallyDivisibleTailSubmodule_iff (p : ℕ) (f : ℤ⟦X⟧) :
    f ∈ pAdicallyDivisibleTailSubmodule p ↔ HasPAdicallyDivisibleTail p f :=
  Iff.rfl

/-- Helper for Chap10 Remark 10 93 2: the binary sequence `b` determines the power series with
coefficient `(p : ℤ)^i` exactly when `b i` is true. -/
def pAdicBinaryTail (p : ℕ) (b : ℕ → Bool) : ℤ⟦X⟧ :=
  PowerSeries.mk fun i ↦ (p : ℤ) ^ i * if b i then 1 else 0

/-- Helper for Chap10 Remark 10 93 2: binary `p`-power coefficient tails satisfy the eventual
`p`-adic divisibility condition. -/
theorem pAdicBinaryTail_hasPAdicallyDivisibleTail (p : ℕ) (b : ℕ → Bool) :
    HasPAdicallyDivisibleTail p (pAdicBinaryTail p b) := by
  -- For a fixed exponent `m + 1`, every coefficient at index `i ≥ m + 1` contains that power.
  intro m
  refine (Set.finite_lt_nat (m + 1)).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  contrapose! hi
  have hpow : (p : ℤ) ^ (m + 1) ∣ (p : ℤ) ^ i := pow_dvd_pow (p : ℤ) hi
  simpa only [pAdicBinaryTail, PowerSeries.coeff_mk] using
    dvd_mul_of_dvd_left hpow (if b i then 1 else 0 : ℤ)

/-- Helper for Chap10 Remark 10 93 2: binary tails are elements of the divisible-tail submodule. -/
theorem pAdicBinaryTail_mem (p : ℕ) (b : ℕ → Bool) :
    pAdicBinaryTail p b ∈ pAdicallyDivisibleTailSubmodule p :=
  pAdicBinaryTail_hasPAdicallyDivisibleTail p b

/-- Helper for Chap10 Remark 10 93 2: binary tails bundled as elements of the canonical tail
submodule. -/
def pAdicBinaryTailSubmodule (p : ℕ) (b : ℕ → Bool) :
    ↥(pAdicallyDivisibleTailSubmodule p) :=
  ⟨pAdicBinaryTail p b, pAdicBinaryTail_mem p b⟩

/-- Helper for Chap10 Remark 10 93 2: for prime `p`, the binary-tail construction is injective. -/
theorem pAdicBinaryTailSubmodule_injective {p : ℕ} (hp : Nat.Prime p) :
    Function.Injective (pAdicBinaryTailSubmodule p) := by
  -- Equality in the submodule gives equality of every coefficient in `ℤ⟦X⟧`.
  intro b c h
  funext i
  have hseries : pAdicBinaryTail p b = pAdicBinaryTail p c := congrArg Subtype.val h
  have hcoeff := congrArg (fun f : ℤ⟦X⟧ ↦ PowerSeries.coeff i f) hseries
  simp only [pAdicBinaryTail, PowerSeries.coeff_mk] at hcoeff
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hpow : (p : ℤ) ^ i ≠ 0 := pow_ne_zero i hp0
  have hind :
      (if b i then (1 : ℤ) else 0) = (if c i then (1 : ℤ) else 0) :=
    mul_left_cancel₀ hpow hcoeff
  -- The remaining Boolean check says that the two `0`/`1` indicators are equal.
  by_cases hb : b i
  · by_cases hc : c i
    · simp [hb, hc]
    · simp [hb, hc] at hind
  · by_cases hc : c i
    · simp [hb, hc] at hind
    · simp [hb, hc]

/-- Helper for Chap10 Remark 10 93 2: Cantor's diagonal argument for binary sequences on `ℕ`. -/
theorem nat_bool_uncountable : Uncountable (ℕ → Bool) := by
  -- A purported enumeration misses the sequence obtained by flipping the diagonal values.
  rw [uncountable_iff_forall_not_surjective]
  intro f hsurj
  let g : ℕ → Bool := fun n ↦ ! f n n
  obtain ⟨n, hn⟩ := hsurj g
  have hsame : g n = f n n := (congrFun hn n).symm
  simp [g] at hsame

/-- Helper for Chap10 Remark 10 93 2: the divisible-tail submodule is uncountable for prime `p`. -/
theorem tailSubmodule_uncountable {p : ℕ} (hp : Nat.Prime p) :
    Uncountable ↥(pAdicallyDivisibleTailSubmodule p) := by
  -- Inject the uncountable Cantor space of binary sequences into the tail submodule.
  letI : Uncountable (ℕ → Bool) := nat_bool_uncountable
  exact (pAdicBinaryTailSubmodule_injective hp).uncountable

/-- Helper for Chap10 Remark 10 93 2: the standard integer module action is associative with
itself in the explicit form needed for ideal actions on `ℤ`-modules. -/
private theorem intModule_self_isScalarTower {M : Type*} [AddCommGroup M] [Module ℤ M] :
    @IsScalarTower ℤ ℤ M Semiring.toModule.toDistribMulAction.toDistribSMul.toSMul
      DistribMulAction.toDistribSMul.toSMul DistribMulAction.toDistribSMul.toSMul := by
  -- Pin the `ℤ`-module scalar action rather than the default additive-group `zsmul` action.
  refine @IsScalarTower.mk ℤ ℤ M Semiring.toModule.toDistribMulAction.toDistribSMul.toSMul
    DistribMulAction.toDistribSMul.toSMul DistribMulAction.toDistribSMul.toSMul ?_
  intro x y z
  simpa only [smul_eq_mul] using
    (@mul_smul ℤ M Int.instSemigroup
      (Module.toDistribMulAction (R := ℤ) (M := M)).toMulAction.toSemigroupAction x y z)

/-- Helper for Chap10 Remark 10 93 2: coefficients of multiplication by an integer constant in
`ℤ⟦X⟧` are ordinary integer multiples of coefficients. -/
theorem powerSeries_coeff_intCast_mul (n : ℤ) (f : ℤ⟦X⟧) (i : ℕ) :
    PowerSeries.coeff i ((n : ℤ⟦X⟧) * f) = n * PowerSeries.coeff i f := by
  -- Rewrite the integer cast as the constant power series and use the coefficient formula.
  rw [show (n : ℤ⟦X⟧) = PowerSeries.C n from
    (map_intCast (PowerSeries.C : ℤ →+* ℤ⟦X⟧) n).symm]
  rw [PowerSeries.coeff_C_mul]

/-- Helper for Chap10 Remark 10 93 2: coefficients of an integer scalar multiple of a power
series are scalar multiples of coefficients. -/
theorem powerSeries_coeff_int_smul (n : ℤ) (f : ℤ⟦X⟧) (i : ℕ) :
    PowerSeries.coeff i (n • f) = n * PowerSeries.coeff i f := by
  -- The `ℤ`-module scalar action on `ℤ⟦X⟧` is multiplication by the integer constant series.
  simpa only [zsmul_eq_mul] using powerSeries_coeff_intCast_mul n f i

/-- Helper for Chap10 Remark 10 93 2: the mod-`p` coefficient sequence of a divisible-tail
series has finite support. -/
theorem tailResidueSupportFinite {p : ℕ} (x : ↥(pAdicallyDivisibleTailSubmodule p)) :
    (Function.support fun i : ℕ =>
      ((PowerSeries.coeff i (x : ℤ⟦X⟧) : ℤ) : ZMod p)).Finite := by
  -- The support modulo `p` is contained in the exceptional set for divisibility by `p`.
  refine (x.property 0).subset ?_
  intro i hi
  simp only [Function.mem_support, Set.mem_setOf_eq] at hi ⊢
  intro hdiv
  have hzero : ((PowerSeries.coeff i (x : ℤ⟦X⟧) : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using hdiv
  exact hi hzero

/-- Helper for Chap10 Remark 10 93 2: the finitely supported mod-`p` coefficient residue of a
divisible-tail series. -/
noncomputable def tailResidueFun {p : ℕ} (x : ↥(pAdicallyDivisibleTailSubmodule p)) :
    ℕ →₀ ZMod p :=
  Finsupp.ofSupportFinite
    (fun i : ℕ => ((PowerSeries.coeff i (x : ℤ⟦X⟧) : ℤ) : ZMod p))
    (tailResidueSupportFinite x)

/-- Helper for Chap10 Remark 10 93 2: evaluation of the finitely supported residue sequence is
coefficientwise reduction modulo `p`. -/
theorem tailResidueFun_apply {p : ℕ} (x : ↥(pAdicallyDivisibleTailSubmodule p)) (i : ℕ) :
    tailResidueFun x i = ((PowerSeries.coeff i (x : ℤ⟦X⟧) : ℤ) : ZMod p) := by
  -- The `Finsupp` wrapper does not change the underlying coefficient function.
  simp [tailResidueFun, Finsupp.ofSupportFinite_coe]

/-- Helper for Chap10 Remark 10 93 2: the coefficient residue construction is additive. -/
theorem tailResidueFun_add {p : ℕ}
    (x y : ↥(pAdicallyDivisibleTailSubmodule p)) :
    tailResidueFun (x + y) = tailResidueFun x + tailResidueFun y := by
  -- Reduce additivity to coefficientwise addition in `ZMod p`.
  ext i
  simp [tailResidueFun_apply, map_add]

/-- Helper for Chap10 Remark 10 93 2: the coefficient residue construction is `ℤ`-linear. -/
theorem tailResidueFun_smul {p : ℕ} (n : ℤ)
    (x : ↥(pAdicallyDivisibleTailSubmodule p)) :
    tailResidueFun (n • x) = n • tailResidueFun x := by
  -- Scalar compatibility is coefficientwise scalar compatibility for power series.
  ext i
  simp only [Finsupp.coe_smul, Pi.smul_apply, zsmul_eq_mul]
  rw [tailResidueFun_apply, tailResidueFun_apply, SetLike.val_smul,
    powerSeries_coeff_int_smul]
  simp

/-- Helper for Chap10 Remark 10 93 2: the linear map sending a tail series to its finitely
supported mod-`p` residue coefficients. -/
noncomputable def tailResidueToFinsupp {p : ℕ} :
    ↥(pAdicallyDivisibleTailSubmodule p) →ₗ[ℤ] ℕ →₀ ZMod p where
  toFun := tailResidueFun
  map_add' := tailResidueFun_add
  map_smul' := tailResidueFun_smul

/-- Helper for Chap10 Remark 10 93 2: applying the residue linear map is coefficientwise
reduction modulo `p`. -/
theorem tailResidueToFinsupp_apply {p : ℕ}
    (x : ↥(pAdicallyDivisibleTailSubmodule p)) (i : ℕ) :
    tailResidueToFinsupp x i =
      ((PowerSeries.coeff i (x : ℤ⟦X⟧) : ℤ) : ZMod p) := by
  -- This is the computation rule inherited from `tailResidueFun`.
  exact tailResidueFun_apply x i

/-- Helper for Chap10 Remark 10 93 2: reducing a multiple of `p` in the tail submodule gives zero
under the coefficient residue map. -/
theorem spanSingleton_smul_top_le_tailResidue_ker {p : ℕ} :
    ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ :
      Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule p)) ≤
        LinearMap.ker (tailResidueToFinsupp (p := p)) := by
  -- Check membership in the kernel on ideal multiples and then close under addition.
  letI := intModule_self_isScalarTower (M := ↥(pAdicallyDivisibleTailSubmodule p))
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr n hn
    rw [Ideal.mem_span_singleton] at hr
    rcases hr with ⟨c, hc⟩
    ext i
    rw [tailResidueToFinsupp_apply, SetLike.val_smul, powerSeries_coeff_int_smul, hc, mul_assoc]
    change (((p : ℤ) * (c * PowerSeries.coeff i (n : ℤ⟦X⟧)) : ℤ) : ZMod p) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c * PowerSeries.coeff i (n : ℤ⟦X⟧), by ring⟩
  · intro x y hx hy
    rw [LinearMap.mem_ker] at hx hy ⊢
    rw [map_add, hx, hy, add_zero]

/-- Helper for Chap10 Remark 10 93 2: if all residue coefficients vanish, then the tail series is
a multiple of `p` inside the tail submodule. -/
theorem tailResidue_ker_le_spanSingleton_smul_top {p : ℕ} :
    LinearMap.ker (tailResidueToFinsupp (p := p)) ≤
      ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ :
        Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule p)) := by
  -- Divide every coefficient by `p`; the shifted tail condition proves the quotient is still in
  -- the tail submodule.
  intro x hx
  have hcoeff_dvd (i : ℕ) : (p : ℤ) ∣ PowerSeries.coeff i (x : ℤ⟦X⟧) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hxzero : tailResidueToFinsupp x = 0 := LinearMap.mem_ker.mp hx
    have hfun := congrArg (fun f : ℕ →₀ ZMod p => f i) hxzero
    simpa [tailResidueToFinsupp_apply] using hfun
  let ySeries : ℤ⟦X⟧ := PowerSeries.mk fun i =>
    PowerSeries.coeff i (x : ℤ⟦X⟧) / (p : ℤ)
  have hyTail : HasPAdicallyDivisibleTail p ySeries := by
    intro m
    refine (x.property (m + 1)).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro hdiv
    have hquot :
        (p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i (x : ℤ⟦X⟧) / (p : ℤ) := by
      exact Int.dvd_div_of_mul_dvd (by
        simpa [pow_succ, pow_succ', Nat.add_assoc, mul_comm, mul_left_comm, mul_assoc]
          using hdiv)
    exact hi (by
      simpa [ySeries, PowerSeries.coeff_mk] using hquot)
  let y : ↥(pAdicallyDivisibleTailSubmodule p) := ⟨ySeries, hyTail⟩
  have hxy : (p : ℤ) • y = x := by
    apply Subtype.ext
    apply PowerSeries.ext
    intro i
    simp only [SetLike.val_smul, y, ySeries]
    rw [powerSeries_coeff_int_smul, PowerSeries.coeff_mk]
    exact Int.mul_ediv_cancel' (hcoeff_dvd i)
  rw [← hxy]
  letI := intModule_self_isScalarTower (M := ↥(pAdicallyDivisibleTailSubmodule p))
  exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top

/-- Helper for Chap10 Remark 10 93 2: the kernel of the residue map is exactly the submodule of
`p`-multiples. -/
theorem tailResidueToFinsupp_ker {p : ℕ} :
    LinearMap.ker (tailResidueToFinsupp (p := p)) =
      ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ :
        Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule p)) := by
  -- Combine the two kernel inclusions obtained from reduction and coefficient division.
  exact le_antisymm tailResidue_ker_le_spanSingleton_smul_top
    spanSingleton_smul_top_le_tailResidue_ker

/-- Helper for Chap10 Remark 10 93 2: the mod-`p` quotient of the divisible-tail submodule is
countable. -/
theorem tailModPQuotient_countable {p : ℕ} (hp : Nat.Prime p) :
    Countable
      (↥(pAdicallyDivisibleTailSubmodule p) ⧸
        ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ :
          Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule p))) := by
  -- Transport the quotient by `p`-multiples to the range of the residue map, a subtype of the
  -- countable finitely supported residue module.
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Q : Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule p) :=
    ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ :
      Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule p))
  let e : (↥(pAdicallyDivisibleTailSubmodule p) ⧸ Q) ≃ₗ[ℤ]
      LinearMap.range (tailResidueToFinsupp (p := p)) :=
    (Submodule.quotEquivOfEq Q (LinearMap.ker (tailResidueToFinsupp (p := p)))
      (tailResidueToFinsupp_ker (p := p)).symm).trans
        (tailResidueToFinsupp (p := p)).quotKerEquivRange
  exact Countable.of_equiv (LinearMap.range (tailResidueToFinsupp (p := p))) e.toEquiv.symm

/-- Helper for Chap10 Remark 10 93 2: if a vector lies in `(p) • ⊤`, then every coordinate of its
basis representation is divisible by `p`. -/
theorem basis_repr_coord_dvd_of_mem_modPrimeQuotient
    {M ι : Type*} [AddCommGroup M] [Module ℤ M] (b : Module.Basis ι ℤ M)
    {p : ℕ} {x : M}
    (hx : x ∈ ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M)) (i : ι) :
    (p : ℤ) ∣ b.repr x i := by
  -- Induct over the ideal-multiple submodule; the generator `p` divides every scalar coefficient.
  letI := intModule_self_isScalarTower (M := M)
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr n hn
    rw [Ideal.mem_span_singleton] at hr
    rcases hr with ⟨c, hc⟩
    rw [hc, b.repr.map_smul]
    exact ⟨c * b.repr n i, by simp [mul_assoc]⟩
  · intro x y hx hy
    rw [b.repr.map_add]
    exact dvd_add hx hy

/-- Helper for Chap10 Remark 10 93 2: countability of a prime-mod quotient of a free abelian
group forces the chosen basis index to be countable. -/
theorem freeChooseBasisIndex_countable_of_modPrime_quotient_countable
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] {p : ℕ}
    (hp : Nat.Prime p)
    [Countable
      (M ⧸ ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M))] :
    Countable (Module.Free.ChooseBasisIndex ℤ M) := by
  -- Inject the chosen basis into the quotient modulo `p`; equality of two basis classes would
  -- make `p` divide the `i`th coordinate of `b i - b j`, namely `1`.
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ M) ℤ M :=
    Module.Free.chooseBasis ℤ M
  let Q : Submodule ℤ M :=
    ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M)
  have hinj : Function.Injective (fun i : Module.Free.ChooseBasisIndex ℤ M =>
      Submodule.Quotient.mk (p := Q) (b i)) := by
    intro i j hij
    by_contra hne
    have hmem : b i - b j ∈ Q := (Submodule.Quotient.eq Q).mp hij
    have hdvd : (p : ℤ) ∣ b.repr (b i - b j) i :=
      basis_repr_coord_dvd_of_mem_modPrimeQuotient b (p := p) hmem i
    have hcoord : b.repr (b i - b j) i = 1 := by
      simp [hne]
    have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
      rwa [hcoord] at hdvd
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hp1)
  exact hinj.countable

/-- Helper for Chap10 Remark 10 93 2: a free abelian group with countable reduction modulo a
prime is countable. -/
theorem free_countable_of_countable_modPrime_quotient
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] {p : ℕ}
    (hp : Nat.Prime p)
    [Countable
      (M ⧸ ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M))] :
    Countable M := by
  -- Once the basis index is countable, the basis representation embeds `M` into countable
  -- finitely supported integer-coordinate functions.
  letI : Countable (Module.Free.ChooseBasisIndex ℤ M) :=
    freeChooseBasisIndex_countable_of_modPrime_quotient_countable hp
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ M) ℤ M :=
    Module.Free.chooseBasis ℤ M
  exact b.repr.injective.countable

/-- Helper for Chap10 Remark 10 93 2: an uncountable abelian group with countable reduction modulo
a prime cannot be free. -/
theorem not_free_of_countable_modPrime_quotient_of_uncountable
    {M : Type*} [AddCommGroup M] [Module ℤ M] {p : ℕ} (hp : Nat.Prime p)
    [Countable
      (M ⧸ ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M))]
    (hM : Uncountable M) :
    ¬ Module.Free ℤ M := by
  -- Freeness would make `M` countable, contradicting the supplied uncountability.
  intro hfree
  letI : Module.Free ℤ M := hfree
  have hcount : Countable M := free_countable_of_countable_modPrime_quotient hp
  exact (@Uncountable.not_countable M hM) hcount

-- Proof sketch: the remark shows that `pAdicallyDivisibleTailSubmodule p` is uncountable, while
-- the residue classes of the monomials `x^i` span its quotient modulo `p`. A free abelian group of
-- uncountable rank would have uncountable dimension after reduction mod `p`, giving a
-- contradiction.
/-- For a prime `p`, the divisible-tail submodule from the remark is not free as an abelian
group. -/
theorem pAdicallyDivisibleTailSubmodule_not_free {p : ℕ} (hp : Nat.Prime p) :
    ¬ Module.Free ℤ ↥(pAdicallyDivisibleTailSubmodule p) := by
  -- The proof now reduces exactly to the two cardinality invariants from the source argument.
  letI : Countable
      (↥(pAdicallyDivisibleTailSubmodule p) ⧸
        ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ :
          Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule p))) :=
    tailModPQuotient_countable hp
  exact not_free_of_countable_modPrime_quotient_of_uncountable hp
    (tailSubmodule_uncountable hp)

/-- Helper for Chap10 Remark 10 93 2: membership in `(p) • ⊤` is the same as being a scalar
multiple by `(p : ℤ)`. -/
theorem mem_spanSingleton_smul_top_iff {M : Type*} [AddCommGroup M] [Module ℤ M]
    (p : ℕ) (x : M) :
    x ∈ ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M) ↔
      ∃ y : M, (p : ℤ) • y = x := by
  -- Ideal-multiple induction extracts an explicit `p`-multiple; the reverse direction inserts
  -- the generator `p` into its principal ideal.
  letI := intModule_self_isScalarTower (M := M)
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      rw [Ideal.mem_span_singleton] at hr
      rcases hr with ⟨c, hc⟩
      refine ⟨c • y, ?_⟩
      rw [hc]
      rw [← mul_zsmul]
      rw [mul_comm]
      exact (int_smul_eq_zsmul (inferInstance : Module ℤ M) (c * (p : ℤ)) y).symm
    · intro y z hy hz
      rcases hy with ⟨y', hy'⟩
      rcases hz with ⟨z', hz'⟩
      refine ⟨y' + z', ?_⟩
      rw [zsmul_add, hy', hz']
  · rintro ⟨y, hy⟩
    rw [← hy]
    have hmem := Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton (p : ℤ)))
      (show y ∈ (⊤ : Submodule ℤ M) from Submodule.mem_top)
    convert hmem using 1
    exact (int_smul_eq_zsmul (inferInstance : Module ℤ M) (p : ℤ) y).symm

/-- Helper for Chap10 Remark 10 93 2: an integer divisible by every power of a prime is zero. -/
theorem int_eq_zero_of_primePow_dvd_all {p : ℕ} (hp : Nat.Prime p) {z : ℤ}
    (hz : ∀ n : ℕ, ((p : ℤ) ^ n) ∣ z) :
    z = 0 := by
  -- If `z` were nonzero, choose a prime power larger than `|z|`; divisibility would force the
  -- same prime power to be at most `|z|`.
  by_contra hz0
  let n : ℕ := (Nat.log p z.natAbs).succ
  have hlt : z.natAbs < p ^ n := by
    simpa [n] using Nat.lt_pow_succ_log_self hp.one_lt z.natAbs
  have hle : p ^ n ≤ z.natAbs := by
    have hleInt := Int.natAbs_le_of_dvd_ne_zero (hz n) hz0
    simpa using hleInt
  exact (not_lt_of_ge hle) hlt

/-- Helper for Chap10 Remark 10 93 2: a module with countable reduction modulo a prime is
countable once it embeds into a coordinate free abelian group. -/
private theorem countable_of_countable_modPrime_quotient_of_injective_finsupp
    {M ι : Type*} [AddCommGroup M] [Module ℤ M] {p : ℕ} (hp : Nat.Prime p)
    (f : M →ₗ[ℤ] ι →₀ ℤ) (hf : Function.Injective f)
    [Countable
      (M ⧸ ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M))] :
    Countable M := by
  classical
  let Q : Submodule ℤ M :=
    ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ : Submodule ℤ M)
  let rep : M ⧸ Q → M := Quotient.out
  let S : Set ι := ⋃ q : M ⧸ Q, ((f (rep q)).support : Set ι)
  have hS_countable : S.Countable := by
    -- The support-control set is a countable union of finite supports of quotient representatives.
    dsimp only [S]
    exact Set.countable_iUnion fun q ↦ Finset.countable_toSet (f (rep q)).support
  have hsupport : ∀ x : M, f x ∈ Finsupp.supported ℤ ℤ S := by
    intro x
    rw [Finsupp.mem_supported']
    intro i hiS
    -- Outside the representative supports, repeated division modulo `p` shows every coordinate is
    -- divisible by every power of `p`, hence zero.
    have hdiv_all : ∀ n : ℕ, ((p : ℤ) ^ n) ∣ f x i := by
      intro n
      induction n generalizing x with
      | zero =>
          simp
      | succ n ih =>
          let q : M ⧸ Q := Submodule.Quotient.mk x
          let r : M := rep q
          have hmk : Submodule.Quotient.mk (p := Q) r =
              Submodule.Quotient.mk (p := Q) x := by
            simpa [q, r, rep] using Submodule.Quotient.mk_out q
          have hmem_rx : r - x ∈ Q := (Submodule.Quotient.eq Q).mp hmk
          have hmem_xr : x - r ∈ Q := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using Q.neg_mem hmem_rx
          rcases (mem_spanSingleton_smul_top_iff (M := M) p (x - r)).mp hmem_xr with
            ⟨y, hy⟩
          have hr_zero : f r i = 0 := by
            have hi_support : i ∉ (f r).support := by
              intro hi
              exact hiS (Set.mem_iUnion.2 ⟨q, by simpa [r] using hi⟩)
            exact Finsupp.notMem_support_iff.mp hi_support
          have hsub : f (x - r) i = (p : ℤ) * f y i := by
            calc
              f (x - r) i = f ((p : ℤ) • y) i := by rw [hy]
              _ = ((p : ℤ) • f y) i := by rw [map_zsmul]
              _ = (p : ℤ) * f y i := by
                rw [Finsupp.smul_apply, zsmul_eq_mul]
                norm_num
          have hx_coord : f x i = (p : ℤ) * f y i := by
            calc
              f x i = f ((x - r) + r) i := by rw [sub_add_cancel]
              _ = f (x - r) i + f r i := by rw [map_add]; rfl
              _ = (p : ℤ) * f y i + 0 := by rw [hsub, hr_zero]
              _ = (p : ℤ) * f y i := by rw [add_zero]
          rcases ih y with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          rw [hx_coord, ha]
          ring
    exact int_eq_zero_of_primePow_dvd_all hp hdiv_all
  haveI : Countable S := hS_countable.to_subtype
  have hcount_supported : Countable (Finsupp.supported ℤ ℤ S) :=
    Countable.of_equiv (S →₀ ℤ)
      (Finsupp.supportedEquivFinsupp (M := ℤ) (R := ℤ) S).symm.toEquiv
  -- The original module embeds into the countable supported-coordinate submodule.
  let supportedMap : M → Finsupp.supported ℤ ℤ S := fun x ↦ ⟨f x, hsupport x⟩
  have hsupp_inj : Function.Injective supportedMap := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  letI : Countable (Finsupp.supported ℤ ℤ S) := hcount_supported
  exact hsupp_inj.countable

/-- Helper for Chap10 Remark 10 93 2: projectivity of `ℤ⟦X⟧` would force the `2`-adic
divisible-tail submodule to be countable. -/
private theorem tailSubmodule_countable_of_integerPowerSeries_projective
    (hprojective : Module.Projective ℤ ℤ⟦X⟧) :
    Countable ↥(pAdicallyDivisibleTailSubmodule 2) := by
  classical
  -- Route correction: avoid the failed hereditary-freeness theorem.  A projective split embeds
  -- the tail submodule into basis coordinates of a free module, and its mod-`2` quotient is
  -- already countable.
  rcases Module.Projective.iff_split.mp hprojective with ⟨F, _, _, _, i, s, hs⟩
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ F) ℤ F :=
    Module.Free.chooseBasis ℤ F
  let coord : ↥(pAdicallyDivisibleTailSubmodule 2) →ₗ[ℤ]
      Module.Free.ChooseBasisIndex ℤ F →₀ ℤ :=
    b.repr.toLinearMap.comp (i.comp (pAdicallyDivisibleTailSubmodule 2).subtype)
  have hcoord_inj : Function.Injective coord := by
    intro x y hxy
    apply Subtype.ext
    have hi_eq : i (x : ℤ⟦X⟧) = i (y : ℤ⟦X⟧) :=
      b.repr.injective (by simpa [coord] using hxy)
    have hsx : s (i (x : ℤ⟦X⟧)) = x := by
      have hlin := LinearMap.congr_fun hs (x : ℤ⟦X⟧)
      simpa using hlin
    have hsy : s (i (y : ℤ⟦X⟧)) = y := by
      have hlin := LinearMap.congr_fun hs (y : ℤ⟦X⟧)
      simpa using hlin
    have happ := congrArg (fun z : F ↦ s z) hi_eq
    simpa [hsx, hsy] using happ
  letI : Countable
      (↥(pAdicallyDivisibleTailSubmodule 2) ⧸
        ((Ideal.span ({(2 : ℤ)} : Set ℤ)) • ⊤ :
          Submodule ℤ ↥(pAdicallyDivisibleTailSubmodule 2))) :=
    tailModPQuotient_countable Nat.prime_two
  exact countable_of_countable_modPrime_quotient_of_injective_finsupp
    Nat.prime_two coord hcoord_inj

/-- Helper for Chap10 Remark 10 93 2: the uncountable `2`-adic tail submodule obstructs
projectivity of `ℤ⟦X⟧`. -/
private theorem tailSubmodule_countability_obstructs_integerPowerSeries_projective :
    ¬ Module.Projective ℤ ℤ⟦X⟧ := by
  -- A projective ambient module would make the tail submodule countable, contradicting the
  -- Cantor-family injection into it.
  intro hprojective
  have hcount : Countable ↥(pAdicallyDivisibleTailSubmodule 2) :=
    tailSubmodule_countable_of_integerPowerSeries_projective hprojective
  exact (@Uncountable.not_countable _ (tailSubmodule_uncountable Nat.prime_two)) hcount

-- Proof sketch: identify `ℤ[[x]]` with the one-variable case of the formal power-series module
-- covered by the owner theorem `noetherian_pi_flat_and_mittagLeffler`.
/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is flat. -/
instance integerPowerSeries_flat : Module.Flat ℤ ℤ⟦X⟧ := by
  simpa [PowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat ℤ ((Unit →₀ ℕ) → ℤ) ∧ MittagLeffler ℤ ((Unit →₀ ℕ) → ℤ)).1

-- Proof sketch: apply the same owner theorem `noetherian_pi_flat_and_mittagLeffler` to the
-- coefficient module presentation of `ℤ⟦X⟧`.
/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is Mittag-Leffler. -/
instance integerPowerSeries_mittagLeffler : MittagLeffler ℤ ℤ⟦X⟧ := by
  simpa [PowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat ℤ ((Unit →₀ ℕ) → ℤ) ∧ MittagLeffler ℤ ((Unit →₀ ℕ) → ℤ)).2

-- Proof sketch: if `ℤ⟦X⟧` were projective, a split embedding into a free module would put the
-- `2`-adic tail submodule inside countable-coordinate support determined by its countable mod-`2`
-- quotient.  This contradicts the Cantor-family uncountability of the tail.
/-- Chap10 Remark 10 93 2: the `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is flat and
Mittag-Leffler but not projective. This is the source-facing counterexample showing that
Lemma 10.93.1 fails without the countable-generation assumption. -/
@[stacks 059Y]
theorem integerPowerSeries_flat_mittagLeffler_and_not_projective :
    Module.Flat ℤ ℤ⟦X⟧ ∧ MittagLeffler ℤ ℤ⟦X⟧ ∧ ¬ Module.Projective ℤ ℤ⟦X⟧ := by
  -- The imported product theorem supplies the first two clauses; the tail-submodule obstruction
  -- supplies nonprojectivity.
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact tailSubmodule_countability_obstructs_integerPowerSeries_projective

/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is not projective. -/
theorem integerPowerSeries_not_projective :
    ¬ Module.Projective ℤ ℤ⟦X⟧ :=
  integerPowerSeries_flat_mittagLeffler_and_not_projective.2.2

end Module
