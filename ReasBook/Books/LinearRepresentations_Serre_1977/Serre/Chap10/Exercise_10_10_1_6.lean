import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} [Semiring k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable {V : Type v} [AddCommGroup V] [Module k V]

-- Layer triage:
-- * source-facing: Serre's `p`-unipotence criterion for a linear automorphism.
-- * core/canonical: `IsPElement` and `IsNilpotent` on the owner `Module.End k V`.
-- * bridge/view: `LinearEquiv.toLinearMap`.
--
-- Proof sketch: if `x` has `p`-power order `p ^ m`, then in characteristic `p` one has
-- `(x - 1)^(p ^ m) = x^(p ^ m) - 1 = 0`, so `x - 1` is nilpotent. Conversely, if `x - 1` is
-- nilpotent, then for some `m` we have `(x - 1)^(p ^ m) = 0`; the same characteristic-`p`
-- binomial identity rewrites this as `x^(p ^ m) - 1 = 0`, hence `x^(p ^ m) = 1`.
/-- Helper for Exercise 10-10.1-6: in characteristic `2`, every positive power `2 ^ n` of the
negation endomorphism acts as negation, because `v = -v` for every vector. -/
lemma neg_one_end_pow_two_apply [CharP k 2] (n : ℕ) (v : V) :
    ((-(1 : Module.End k V)) ^ (2 ^ n)) v = -v := by
  -- For `n = 0` the claim is just the definition of `-1`.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- In characteristic `2`, every vector satisfies `v = -v`.
      have htwo : (2 : k) • v = 0 := by
        simpa using
          (show ((2 : k) • v) = (0 : k) • v from
            congrArg (fun a : k => a • v) (CharP.cast_eq_zero (R := k) (p := 2)))
      have htwo' : (2 : ℕ) • v = 0 := by
        convert htwo using 1
        symm
        exact Nat.cast_smul_eq_nsmul k 2 v
      have hv : v = -v := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [two_nsmul] using htwo'
      have heven : Even (2 ^ (n + 1)) := by
        refine ⟨2 ^ n, by omega⟩
      have hpow : (-(1 : Module.End k V)) ^ (2 ^ (n + 1)) = 1 :=
        heven.neg_one_pow
      rw [hpow]
      exact hv

/-- Helper for Exercise 10-10.1-6: the `p ^ n`-th power of the negation endomorphism acts as
negation in characteristic `p`. -/
lemma neg_one_end_pow_prime_apply (n : ℕ) (v : V) :
    ((-(1 : Module.End k V)) ^ p ^ n) v = -v := by
  have hp : Nat.Prime p := Fact.out
  -- Split according to whether the prime is `2` or odd.
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · simpa using neg_one_end_pow_two_apply (k := k) (V := V) n v
  · have hpown : Odd (p ^ n) := hpodd.pow
    have hpow : (-(1 : Module.End k V)) ^ (p ^ n) = -1 :=
      hpown.neg_one_pow
    rw [hpow]
    rfl

/-- Helper for Exercise 10-10.1-6: applying the characteristic-`p` binomial identity to the
linear endomorphism `x.toLinearMap - 1` gives the pointwise formula
`(x - 1)^(p ^ n) v = (x^(p ^ n) - 1) v`. -/
lemma sub_pow_prime_pow_apply (x : V ≃ₗ[k] V) (n : ℕ) (v : V) :
    (((x.toLinearMap - 1) ^ p ^ n) v) = ((x.toLinearMap ^ p ^ n - 1) v) := by
  have hp : Nat.Prime p := Fact.out
  have hcomm : Commute x.toLinearMap (-(1 : Module.End k V)) := by
    simpa using (Commute.all x.toLinearMap (-(1 : Module.End k V)))
  -- The extra `p`-multiple from the noncommutative binomial formula vanishes on vectors.
  obtain ⟨r, hr⟩ := Commute.exists_add_pow_prime_pow_eq hp hcomm n
  have hterm : p • x (r v) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k]
    simp
  have hv := congrArg (fun f : Module.End k V => f v) hr
  simpa [sub_eq_add_neg, Module.End.pow_apply, neg_one_end_pow_prime_apply (k := k) (p := p)
    (V := V) n v, hterm] using hv

/-- Exercise 10-10.1-6 (1): for a linear automorphism `x` of a `k`-module in characteristic `p`,
with `p` prime, `x` is a `p`-element if and only if the endomorphism `x - 1` is nilpotent. -/
theorem isPElement_iff_isNilpotent_sub_one (x : V ≃ₗ[k] V) :
    IsPElement p x ↔ IsNilpotent (x.toLinearMap - 1) := by
  constructor
  · intro hx
    -- Push the `p`-power order witness to the endomorphism side.
    rcases (isPElement_iff_exists_pow_eq_one x).mp hx with ⟨n, hn⟩
    refine ⟨p ^ n, ?_⟩
    ext v
    rw [sub_pow_prime_pow_apply (k := k) (p := p) (V := V) x n v]
    have hval : (x ^ p ^ n) v = v := by
      simpa using congrArg (fun e : V ≃ₗ[k] V => e v) hn
    have hiter : (x.toLinearMap ^ p ^ n) v = v := by
      simpa [Module.End.pow_apply, LinearEquiv.pow_apply] using hval
    simpa using sub_eq_zero.mpr hiter
  · rintro ⟨n, hn⟩
    -- Raise the nilpotence exponent to a prime-power exponent large enough for Serre's criterion.
    let m := Nat.clog p n
    have hp : Nat.Prime p := Fact.out
    have hle : n ≤ p ^ m :=
      Nat.le_pow_clog hp.one_lt n
    have hzero : (x.toLinearMap - 1) ^ (p ^ m) = 0 :=
      pow_eq_zero_of_le hle hn
    have hxpow : x.toLinearMap ^ p ^ m = 1 := by
      ext v
      have hsub : (((x.toLinearMap - 1) ^ p ^ m) v) = ((x.toLinearMap ^ p ^ m - 1) v) :=
        sub_pow_prime_pow_apply (k := k) (p := p) (V := V) x m v
      rw [hzero] at hsub
      have hsub' : ((x.toLinearMap ^ p ^ m - 1) v) = 0 := by
        simpa using hsub.symm
      simpa using sub_eq_zero.mp hsub'
    -- Convert the endomorphism equality back to the original automorphism.
    refine (isPElement_iff_exists_pow_eq_one x).2 ⟨m, ?_⟩
    ext v
    have hval : (⇑x)^[p ^ m] v = v := by
      simpa [Module.End.pow_apply] using congrArg (fun f : Module.End k V => f v) hxpow
    simpa [LinearEquiv.pow_apply] using hval

end

section

variable {k : Type u} [Field k]
variable {p : ℕ} [CharP k p]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

open Module.End

-- Layer triage:
-- * source-facing: the two Serre criteria for `p`-elements and `p'`-elements of a linear
--   automorphism.
-- * core/canonical: `IsPElement`, `IsPRegular`, `IsNilpotent`, and `Module.End.IsSemisimple`.
-- * bridge/view: `LinearEquiv.toLinearMap`.
--
-- Proof sketch: if `x` has order prime to `p`, then its minimal polynomial divides `X^m - 1`
-- for some `m` with `Nat.Coprime p m`, and `X^m - 1` is squarefree in characteristic `p`; hence
-- the induced endomorphism is semisimple. Conversely, one may pass to a finite extension over
-- which a semisimple endomorphism diagonalizes; there its eigenvalues lie in a finite
-- multiplicative group of order prime to `p`, so the order of `x` is also prime to `p`.
/-- Helper for Exercise 10-10.1-6: a `p'`-regular linear automorphism is semisimple because
`X ^ orderOf x - 1` is squarefree and annihilates `x.toLinearMap`. -/
lemma isPRegular_toLinearMap_isSemisimple [Fact p.Prime] (x : V ≃ₗ[k] V)
    (hx : IsPRegular p x) :
    IsSemisimple x.toLinearMap := by
  have hreg : ¬ p ∣ orderOf x := (isPRegular_iff_not_dvd_orderOf x).mp hx
  have hcast : (orderOf x : k) ≠ 0 := by
    intro hzero
    exact hreg ((CharP.cast_eq_zero_iff k p (orderOf x)).mp hzero)
  have hsep : ((Polynomial.X ^ orderOf x - (1 : Polynomial k))).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff]
    exact hcast
  -- Evaluate the annihilating polynomial on the endomorphism.
  have hpow : x.toLinearMap ^ orderOf x = 1 := by
    ext v
    change (x.toLinearMap ^ orderOf x) v = (1 : Module.End k V) v
    rw [Module.End.pow_apply]
    change (⇑x)^[orderOf x] v = v
    rw [← LinearEquiv.pow_apply]
    exact congrArg (fun e : V ≃ₗ[k] V => e v) (pow_orderOf_eq_one x)
  have haeval : Polynomial.aeval x.toLinearMap (Polynomial.X ^ orderOf x - (1 : Polynomial k)) = 0 := by
    simp [hpow]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval

/-- Helper for Exercise 10-10.1-6: over a finite field, every linear automorphism has finite
order because its underlying permutation of the finite set `V` does. -/
lemma linearEquiv_isOfFinOrder_of_finite_field [Finite k] (x : V ≃ₗ[k] V) :
    IsOfFinOrder x := by
  let b := Module.Free.chooseBasis k V
  let e : Equiv.Perm V := x.toEquiv
  haveI : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  letI : Fintype (Module.Free.ChooseBasisIndex k V) :=
    Fintype.ofFinite (Module.Free.ChooseBasisIndex k V)
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype (Module.Free.ChooseBasisIndex k V →₀ k) := by
    infer_instance
  haveI : Finite V := by
    exact Finite.of_equiv (Module.Free.ChooseBasisIndex k V →₀ k) b.repr.toEquiv.symm
  rcases isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite e) with ⟨n, hnpos, hn⟩
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, ?_⟩
  ext v
  have hperm : (x.toEquiv ^ n) v = v := by
    simpa [e] using congrArg (fun σ : Equiv.Perm V => σ v) hn
  simpa [LinearEquiv.pow_apply] using hperm

/-- Helper for Exercise 10-10.1-6: any power of a finite-order semisimple automorphism is again
semisimple. This is used for the `p`-unipotent factor, which lies in `Subgroup.zpowers x`. -/
lemma isSemisimple_toLinearMap_of_mem_zpowers (x y : V ≃ₗ[k] V)
    (hx : IsOfFinOrder x) (hs : IsSemisimple x.toLinearMap) (hy : y ∈ Subgroup.zpowers x) :
    IsSemisimple y.toLinearMap := by
  classical
  -- Replace the `zpow` witness by a natural power representative modulo `orderOf x`.
  rw [hx.mem_zpowers_iff_mem_range_orderOf] at hy
  rcases Finset.mem_image.mp hy with ⟨n, _, hy⟩
  subst hy
  convert (hs.pow n : IsSemisimple (x.toLinearMap ^ n)) using 1
  ext v
  simp [Module.End.pow_apply, LinearEquiv.pow_apply]

/-- Helper for Exercise 10-10.1-6: a semisimple unipotent automorphism is the identity. -/
lemma linearEquiv_eq_one_of_isSemisimple_of_isNilpotent_sub_one (y : V ≃ₗ[k] V)
    (hs : IsSemisimple y.toLinearMap) (hn : IsNilpotent (y.toLinearMap - 1)) :
    y = 1 := by
  -- Shift by the identity and use that a nilpotent semisimple endomorphism must be zero.
  have hsemisimple_sub : IsSemisimple (y.toLinearMap - 1) := by
    simpa using
      (Module.End.isSemisimple_sub_algebraMap_iff (f := y.toLinearMap) (μ := (1 : k))).2 hs
  have hzero : y.toLinearMap - 1 = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hn hsemisimple_sub
  exact LinearEquiv.toLinearMap_injective (sub_eq_zero.mp hzero)

/-- Exercise 10-10.1-6 (2): for a linear automorphism `x` of a finite-dimensional vector space
over a finite field `k` of characteristic `p`, `x` is a `p'`-element if and only if the
induced endomorphism `x.toLinearMap` is semisimple. -/
theorem isPRegular_iff_isSemisimple [Finite k] (x : V ≃ₗ[k] V) :
    IsPRegular p x ↔ IsSemisimple x.toLinearMap := by
  letI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  constructor
  · intro hx
    -- The forward implication is the standard squarefree-polynomial criterion.
    exact isPRegular_toLinearMap_isSemisimple (p := p) x hx
  · intro hs
    -- Decompose `x` into its canonical `p`-unipotent and `p'`-regular parts.
    have hxfin : IsOfFinOrder x :=
      linearEquiv_isOfFinOrder_of_finite_field (k := k) (V := V) x
    let hdecomp := p_component_decomposition_exists (p := p) x hxfin
    -- The `p`-unipotent component is a power of `x`, hence still semisimple.
    have hxu_semisimple : IsSemisimple (pUnipotentComponent p x).toLinearMap := by
      exact isSemisimple_toLinearMap_of_mem_zpowers (x := x) (y := pUnipotentComponent p x)
        hxfin hs hdecomp.left_mem_zpowers
    -- Part (1) identifies the `p`-unipotent component with a unipotent semisimple map.
    have hxu_nilpotent : IsNilpotent ((pUnipotentComponent p x).toLinearMap - 1) := by
      exact (isPElement_iff_isNilpotent_sub_one (p := p) (x := pUnipotentComponent p x)).mp
        hdecomp.isPElement
    have hxu_one : pUnipotentComponent p x = 1 :=
      linearEquiv_eq_one_of_isSemisimple_of_isNilpotent_sub_one
        (y := pUnipotentComponent p x) hxu_semisimple hxu_nilpotent
    -- Once the `p`-unipotent component is trivial, only the `p'`-regular part remains.
    have hxeq : x = pRegularComponent p x := by
      calc
        x = pUnipotentComponent p x * pRegularComponent p x := hdecomp.eq_mul
        _ = pRegularComponent p x := by simp [hxu_one]
    rw [hxeq]
    exact hdecomp.isPRegular

end
