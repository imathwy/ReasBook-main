import Mathlib
import stacks_proof.stacks_project.Chap10.Proposition_10_158_9
import stacks_proof.stacks_project.Chap10.Lemma_10_160_7
import stacks_proof.stacks_project.Chap10.Definition_10_160_5
import stacks_proof.stacks_project.Chap15.Definition_15_37_3
import stacks_proof.stacks_project.Chap15.Lemma_15_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped Topology

universe u v w

section

/- Domain-style sampling for Lemma 15.39.1:
- primary domain: adic formal smoothness of coefficient maps into finite-variable formal power
  series rings over fields and Cohen rings.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`,
  * `Algebra.formallySmooth_of_charZero`,
  * `Algebra.formallySmooth_of_isSeparableOver`,
  * `cohenRing_zmodPow_quotient_algebraMap_formallySmooth`.
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the chapter owner for the adic
  lifting property used here, and the project’s canonical owner for “finitely many variables” is
  `MvPowerSeries σ _` with `[Finite σ]`, not the coordinate encoding `Fin n`;
  field-theoretic formal smoothness and the Cohen-ring quotient results are upstream bridge inputs
  rather than separate local owners.
- primitive data: the coefficient field or Cohen ring together with its characteristic
  hypotheses.
- derived API: the three maximal-ideal-adic formal smoothness statements for the corresponding
  multivariable formal power series rings.

Source/core/bridge triage:
- `source-facing`: the three textbook cases in Lemma 15.39.1.
- `core/canonical`: `Algebra.FormallySmooth` and the owner theorem
  `RingHom.formally_smooth_for_adic`.
- `bridge/view`: passage from the coefficient-ring formal smoothness statements to the power-series
  targets.
-/

/-- Helper for Lemma 15.39.1: algebraic formal smoothness of a field extension upgrades to
maximal-ideal-adic formal smoothness because fields carry the discrete topology. -/
theorem field_formally_smooth_for_madic_of_formallySmooth
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfs : Algebra.FormallySmooth k K) :
    RingHom.formally_smooth_for_adic (algebraMap k K) (maximalIdeal K) := by
  let f : k →+* K := algebraMap k K
  letI : TopologicalSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  letI : TopologicalSpace K := Ideal.adicTopology (maximalIdeal K)
  letI : TopologicalRing.IsPreadicRing K :=
    { toIsTopologicalRing := inferInstance
      exists_ideal_isAdic := ⟨maximalIdeal K, rfl⟩ }
  -- With discrete source and the natural adic target topology, the standard bridge upgrades the
  -- algebraic formal smoothness of the coefficient map to the required topological one.
  change f.FormallySmoothTopologically
  have hring : f.FormallySmooth := by
    rw [RingHom.formallySmooth_algebraMap]
    exact hfs
  simpa [f] using RingHom.FormallySmooth.toTopologically hring continuous_of_discreteTopology

/-- Helper for Lemma 15.39.1: each formal variable lies in the maximal ideal of a multivariable
power series ring over a local ring. -/
theorem mvPowerSeries_X_mem_maximalIdeal
    {σ : Type v} {S : Type u} [CommRing S] [IsLocalRing S] (i : σ) :
    MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries σ S) := by
  -- A unit power series has unit constant coefficient, but `X i` has constant coefficient `0`.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hcoeff : IsUnit (MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries σ S)) :=
    MvPowerSeries.isUnit_constantCoeff _ hunit
  simpa [MvPowerSeries.constantCoeff_X] using hcoeff

/-- Helper for Lemma 15.39.1: a coefficient from the maximal ideal stays in the maximal ideal of
the corresponding multivariable power series ring. -/
theorem mvPowerSeries_coeff_mem_maximalIdeal
    {σ : Type v} {S : Type u} [CommRing S] [IsLocalRing S] {x : S}
    (hx : x ∈ maximalIdeal S) :
    algebraMap S (MvPowerSeries σ S) x ∈ maximalIdeal (MvPowerSeries σ S) := by
  -- If the coefficient became a unit upstairs, its constant coefficient would already be a unit.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hunit
  exact hx <| by
    simpa [MvPowerSeries.c_eq_algebraMap] using MvPowerSeries.isUnit_constantCoeff _ hunit

/-- Helper for Lemma 15.39.1: the coefficient inclusion into a multivariable power series ring is
continuous for the maximal-ideal-adic topologies. -/
theorem continuous_algebraMap_to_mvPowerSeries_madic
    {σ : Type v} {S : Type u} [CommRing S] [IsLocalRing S] [Finite σ] :
    letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
    letI : TopologicalSpace (MvPowerSeries σ S) :=
      Ideal.adicTopology (maximalIdeal (MvPowerSeries σ S))
    Continuous (algebraMap S (MvPowerSeries σ S)) := by
  -- It is enough that the maximal ideal maps into the maximal ideal upstairs.
  rw [RingHom.continuous_adic_iff_exists_pow_map_le]
  refine ⟨1, ?_⟩
  simpa [pow_one] using
    (Ideal.map_le_iff_le_comap.mpr fun x hx ↦
      mvPowerSeries_coeff_mem_maximalIdeal (σ := σ) hx :
      Ideal.map (algebraMap S (MvPowerSeries σ S)) (maximalIdeal S) ≤
        maximalIdeal (MvPowerSeries σ S))

/-- Helper for Lemma 15.39.1: if a map kills an ideal modulo a square-zero quotient, then any
lift kills the square of that ideal. -/
theorem ker_sq_of_quotient_ker_and_square_zero
    {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    (I : Ideal B) (J : Ideal A) (hJ : J ^ 2 = ⊥)
    {f : B →+* A} {g : B →+* A ⧸ J}
    (hfg : (Ideal.Quotient.mk J).comp f = g)
    (hg : I ≤ RingHom.ker g) :
    I ^ 2 ≤ RingHom.ker f := by
  -- First show that the chosen lift sends `I` into `J`.
  have hmapJ : Ideal.map f I ≤ J := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro x hx
    have hxzero : g x = 0 := RingHom.mem_ker.mp (hg hx)
    have hxquot : Ideal.Quotient.mk J (f x) = 0 := by
      simpa [hxzero] using DFunLike.congr_fun hfg x
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp hxquot
  -- Squaring then lands in `J² = 0`.
  have hmapBot : Ideal.map f (I ^ 2) ≤ ⊥ := by
    calc
      Ideal.map f (I ^ 2) = Ideal.map f I ^ 2 := by
        rw [Ideal.map_pow]
      _ ≤ J ^ 2 := Ideal.pow_right_mono hmapJ 2
      _ = ⊥ := hJ
  simpa [RingHom.ker_eq_comap_bot] using
    (Ideal.map_le_iff_le_comap.mp hmapBot : I ^ 2 ≤ Ideal.comap f ⊥)

/-- Helper for Lemma 15.39.1: if the quotient map out of `ℤ` kills `p ^ N` modulo a square-zero
ideal, then the original map kills `p ^ (2 * N)`. -/
theorem int_base_map_kills_pow_of_square_zero
    {A : Type u} [CommRing A] {J : Ideal A} (hJ : J ^ 2 = ⊥)
    {g0 : ℤ →+* A} {g : ℤ →+* A ⧸ J}
    (hfg : (Ideal.Quotient.mk J).comp g0 = g)
    {p N : ℕ} (hkill : g ((p : ℤ) ^ N) = 0) :
    g0 ((p : ℤ) ^ (2 * N)) = 0 := by
  -- The element `p ^ N` already vanishes in the quotient, so its chosen lift lands in `J`.
  have hmem : g0 ((p : ℤ) ^ N) ∈ J := by
    have hquot : Ideal.Quotient.mk J (g0 ((p : ℤ) ^ N)) = 0 := by
      simpa [hkill] using DFunLike.congr_fun hfg ((p : ℤ) ^ N)
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp hquot
  -- Squaring that lift lands in `J² = 0`, which is exactly the desired exponent doubling.
  have hsq : g0 ((p : ℤ) ^ (2 * N)) ∈ J ^ 2 := by
    rw [pow_two, two_mul, pow_add, map_mul]
    exact Ideal.mul_mem_mul hmem hmem
  have hzero : g0 ((p : ℤ) ^ (2 * N)) ∈ (⊥ : Ideal A) := by
    simpa [hJ] using hsq
  exact hzero

/-- Helper for Lemma 15.39.1: if an integer-valued base map kills `p ^ N`, then it descends
through the canonical quotient `ZMod (p ^ N)`. -/
theorem int_base_map_descends_to_zmod_pow
    {A : Type u} [CommRing A] {p N : ℕ} {g0 : ℤ →+* A}
    (hkill : g0 ((p : ℤ) ^ N) = 0) :
    ∃ gZ : ZMod (p ^ N) →+* A,
      gZ.comp (Int.castRingHom (ZMod (p ^ N))) = g0 := by
  let gq : ℤ ⧸ Ideal.span ({(((p ^ N) : ℤ))} : Set ℤ) →+* A :=
    Ideal.Quotient.lift (Ideal.span ({(((p ^ N) : ℤ))} : Set ℤ)) g0 <| by
      intro z hz
      -- Any element of the span is a multiple of the killed generator, so the map vanishes on it.
      rcases (Ideal.mem_span_singleton.mp hz) with ⟨k, rfl⟩
      rw [map_mul, hkill, zero_mul]
  -- Transport the quotient map through the canonical identification `ℤ/(p^(2N)) ≃ ZMod (p^(2N))`.
  refine ⟨gq.comp (Int.quotientSpanNatEquivZMod (p ^ N)).symm.toRingHom, ?_⟩
  -- On integer generators, the descended map agrees with the original map by construction.
  ext z
  simp [gq]

/-- Helper for Lemma 15.39.1: a ring homomorphism that kills the chosen power `r ^ N` factors
through the quotient by the principal ideal that it generates. -/
theorem ringHom_factors_through_quotient_span_singleton_pow
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {r : R} {N : ℕ} {f : R →+* S}
    (hkill : f (r ^ N) = 0) :
    ∃ fbar : R ⧸ Ideal.span ({(r ^ N)} : Set R) →+* S,
      fbar.comp (Ideal.Quotient.mk (Ideal.span ({(r ^ N)} : Set R))) = f := by
  let fbar : R ⧸ Ideal.span ({(r ^ N)} : Set R) →+* S :=
    Ideal.Quotient.lift (Ideal.span ({(r ^ N)} : Set R)) f <| by
      intro z hz
      -- Any element of the principal ideal is a multiple of the killed generator.
      rcases (Ideal.mem_span_singleton.mp hz) with ⟨k, rfl⟩
      rw [map_mul, hkill, zero_mul]
  refine ⟨fbar, ?_⟩
  ext x
  rfl

/-- Helper for Lemma 15.39.1: over a finite set of variables and a discrete target topology,
nilpotent variable images admit evaluation of multivariable formal power series. -/
theorem mvPowerSeries_hasEval_of_finite_of_isNilpotent
    {σ : Type v} {A : Type u} [Finite σ] [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    (a : σ → A) (ha : ∀ s, IsNilpotent (a s)) :
    MvPowerSeries.HasEval a := by
  refine ⟨fun s ↦ (ha s).isTopologicallyNilpotent, ?_⟩
  -- For finitely many variables, every subset of the index type is cofinite.
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_cofinite]
  exact Set.toFinite _

/-- Helper for Lemma 15.39.1: passing to an ideal quotient preserves nilpotence. -/
theorem idealQuotient_mk_isNilpotent
    {A : Type u} [CommRing A] {J : Ideal A} {x : A}
    (hx : IsNilpotent x) :
    IsNilpotent (Ideal.Quotient.mk J x) := by
  -- Nilpotence is preserved by any ring homomorphism, in particular by the quotient map.
  exact hx.map (Ideal.Quotient.mk J)

/-- Helper for Lemma 15.39.1: if the total degree reaches a finite cutoff, then one coordinate
exponent reaches its corresponding coordinate cutoff. -/
theorem exists_index_with_succ_exponent_le_of_succ_sum_le_degree
    {σ : Type v} [Fintype σ] (d : σ →₀ ℕ) (e : σ → ℕ)
    (hdeg : (∑ i, e i).succ ≤ d.degree) :
    ∃ i, (e i).succ ≤ d i := by
  -- If every coordinate stayed below its successor cutoff, then the total degree would stay at
  -- most `∑ i, e i`, contradicting the strict cutoff `Nat.succ (∑ i, e i)`.
  by_contra h
  have hle : ∀ i, d i ≤ e i := by
    intro i
    exact Nat.lt_succ_iff.mp <| Nat.lt_of_not_ge (fun hi ↦ h ⟨i, hi⟩)
  have hdeg_le : d.degree ≤ ∑ i, e i := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun i _ ↦ hle i
  exact Nat.not_succ_le_self _ (le_trans hdeg hdeg_le)

/-- Helper for Lemma 15.39.1: a monomial whose total degree crosses the nilpotence cutoff
evaluates to zero at the chosen nilpotent tuple. -/
theorem mvPolynomial_eval₂Hom_monomial_eq_zero_of_degree_ge_nilpotence_cutoff
    {σ : Type v} {S : Type u} {T : Type w}
    [Fintype σ] [CommRing S] [CommRing T]
    (φ : S →+* T) (a : σ → T) (e : σ → ℕ)
    (ha : ∀ i, a i ^ (e i).succ = 0)
    {d : σ →₀ ℕ} {r : S}
    (hd : (∑ i, e i).succ ≤ d.degree) :
    MvPolynomial.eval₂Hom φ a (MvPolynomial.monomial d r) = 0 := by
  classical
  obtain ⟨i, hi⟩ :=
    exists_index_with_succ_exponent_le_of_succ_sum_le_degree (d := d) (e := e) hd
  have hi_mem : i ∈ d.support := by
    refine Finsupp.mem_support_iff.mpr ?_
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos _) hi)
  have hi_zero : a i ^ d i = 0 := by
    -- Once one exponent reaches its cutoff, the whole monomial vanishes.
    rw [← Nat.add_sub_of_le hi, pow_add, ha i, zero_mul]
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, Finset.prod_eq_zero hi_mem hi_zero, mul_zero]

/-- Helper for Lemma 15.39.1: if every monomial of a polynomial lies above the nilpotence cutoff,
then the whole polynomial evaluates to zero. -/
theorem mvPolynomial_eval₂Hom_eq_zero_of_degree_ge_nilpotence_cutoff
    {σ : Type v} {S : Type u} {T : Type w}
    [Fintype σ] [CommRing S] [CommRing T]
    (φ : S →+* T) (a : σ → T) (e : σ → ℕ)
    (ha : ∀ i, a i ^ (e i).succ = 0)
    (p : MvPolynomial σ S)
    (hp : ∀ d, p.coeff d ≠ 0 → (∑ i, e i).succ ≤ d.degree) :
    MvPolynomial.eval₂Hom φ a p = 0 := by
  -- Expand into monomials and kill each monomial by the cutoff lemma.
  rw [p.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  exact
    mvPolynomial_eval₂Hom_monomial_eq_zero_of_degree_ge_nilpotence_cutoff
      (φ := φ) (a := a) (e := e) ha (hd := hp d (Finsupp.mem_support_iff.mp hd))

/-- Helper for Lemma 15.39.1: on an honest polynomial, evaluation at nilpotent variables only
depends on the finite total-degree truncation determined by the nilpotence cutoffs. -/
theorem mvPolynomial_eval₂_eq_eval₂_truncTotal_of_nilpotent_variables
    {σ : Type v} {S : Type u} {T : Type w}
    [Fintype σ] [CommRing S] [CommRing T]
    (φ : S →+* T) (a : σ → T) (e : σ → ℕ)
    (ha : ∀ i, a i ^ (e i).succ = 0)
    (p : MvPolynomial σ S) :
    MvPolynomial.eval₂ φ a p =
      MvPolynomial.eval₂ φ a
        (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ p) := by
  let D : ℕ := (∑ i, e i).succ
  change MvPolynomial.eval₂Hom φ a p =
    MvPolynomial.eval₂Hom φ a (MvPowerSeries.truncTotal (σ := σ) (R := S) D p)
  have htail :
      MvPolynomial.eval₂Hom φ a
        (p - MvPowerSeries.truncTotal (σ := σ) (R := S) D p) = 0 := by
    -- In the polynomial tail, every surviving monomial has total degree at least `D`.
    refine
      mvPolynomial_eval₂Hom_eq_zero_of_degree_ge_nilpotence_cutoff
        (φ := φ) (a := a) (e := e) ha
        (p := p - MvPowerSeries.truncTotal (σ := σ) (R := S) D p) ?_
    intro d hd
    by_contra hlt
    have hcoeff :
        (MvPowerSeries.truncTotal (σ := σ) (R := S) D p).coeff d = p.coeff d :=
      MvPowerSeries.coeff_truncTotal (p := (p : MvPowerSeries σ S)) (h := Nat.lt_of_not_ge hlt)
    have : (p - MvPowerSeries.truncTotal (σ := σ) (R := S) D p).coeff d = 0 := by
      simp [hcoeff]
    exact hd this
  -- Evaluating the vanishing tail shows that the polynomial and its truncation agree.
  exact sub_eq_zero.mp (by simpa [D] using htail)

/-- Helper for Lemma 15.39.1: if a power of the maximal ideal lies in the kernel of the quotient
map, then any chosen lift of a coordinate variable is nilpotent. -/
theorem mvPowerSeries_variable_lifts_nilpotent_of_pow_le_ker
    {σ : Type v} {S : Type u} {A : Type w}
    [CommRing S] [IsLocalRing S] [CommRing A]
    {J : Ideal A} (hJ : J ^ 2 = ⊥)
    {g : MvPowerSeries σ S →+* A ⧸ J} {M : ℕ}
    (hker : maximalIdeal (MvPowerSeries σ S) ^ M ≤ RingHom.ker g)
    {x : A} {i : σ} (hx : Ideal.Quotient.mk J x = g (MvPowerSeries.X i)) :
    x ^ (2 * M) = 0 := by
  -- The kernel bound forces the `M`-th power of the variable image to vanish in the quotient.
  have hXpow_zero : g ((MvPowerSeries.X i : MvPowerSeries σ S) ^ M) = 0 := by
    apply RingHom.mem_ker.mp
    exact hker <| Ideal.pow_mem_pow (mvPowerSeries_X_mem_maximalIdeal (σ := σ) (S := S) i) M
  -- Transport that vanishing statement to the chosen lift `x`.
  have hxpow_mem : x ^ M ∈ J := by
    have hquot : Ideal.Quotient.mk J (x ^ M) = 0 := by
      calc
        Ideal.Quotient.mk J (x ^ M) = (Ideal.Quotient.mk J x) ^ M := by rw [map_pow]
        _ = (g (MvPowerSeries.X i)) ^ M := by rw [hx]
        _ = g ((MvPowerSeries.X i : MvPowerSeries σ S) ^ M) := by rw [map_pow]
        _ = 0 := hXpow_zero
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp hquot
  -- Squaring inside the square-zero ideal kills the doubled power of the lift.
  have hpow_mem : x ^ (2 * M) ∈ J ^ 2 := by
    simpa [pow_two, two_mul, pow_add] using
      (Ideal.mul_mem_mul hxpow_mem hxpow_mem : x ^ M * x ^ M ∈ J * J)
  have hzero : x ^ (2 * M) ∈ (⊥ : Ideal A) := by
    simpa [hJ] using hpow_mem
  exact hzero

/-- Helper for Lemma 15.39.1: the high total-degree tail of a multivariable power series can be
partitioned into finitely many pieces, one for each variable whose exponent crosses the chosen
cutoff. -/
theorem mvPowerSeries_tail_piece_sum_of_degree_cutoff
    {σ : Type v} {S : Type u}
    [Fintype σ] [CommRing S]
    (e : σ → ℕ) (f : MvPowerSeries σ S) :
    ∃ ψ : σ → MvPowerSeries σ S,
      f - (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ f : MvPowerSeries σ S) =
        ∑ i, ψ i ∧
      ∀ i d, d i < (e i).succ → (ψ i).coeff d = 0 := by
  classical
  let D : ℕ := (∑ i, e i).succ
  let tail : MvPowerSeries σ S :=
    f - (MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPowerSeries σ S)
  let chooseIndex : ∀ {d : σ →₀ ℕ}, D ≤ d.degree → σ :=
    fun {d} hd =>
      Classical.choose <|
        exists_index_with_succ_exponent_le_of_succ_sum_le_degree
          (d := d) (e := e) (by simpa [D] using hd)
  have chooseIndex_spec : ∀ {d : σ →₀ ℕ} (hd : D ≤ d.degree),
      (e (chooseIndex hd)).succ ≤ d (chooseIndex hd) := by
    intro d hd
    exact Classical.choose_spec <|
      exists_index_with_succ_exponent_le_of_succ_sum_le_degree
        (d := d) (e := e) (by simpa [D] using hd)
  let ψ : σ → MvPowerSeries σ S := fun i d =>
    if hd : D ≤ d.degree then
      if chooseIndex hd = i then tail.coeff d else 0
    else
      0
  refine ⟨ψ, ?_, ?_⟩
  · -- Compare coefficients and send each high-degree monomial to its chosen cutoff index.
    ext d
    suffices hcoeff : tail d = ∑ i, ψ i d by
      simpa [tail] using hcoeff
    by_cases hd : D ≤ d.degree
    · rw [Fintype.sum_eq_single (chooseIndex hd)]
      · simp [ψ, hd]
        rfl
      · intro i hi
        simp [ψ, hd, hi, eq_comm]
    · have hcoeff_trunc :
        (MvPowerSeries.truncTotal (σ := σ) (R := S) D f).coeff d = f.coeff d :=
        MvPowerSeries.coeff_truncTotal (p := f) (h := Nat.lt_of_not_ge hd)
      have hsum_zero : ∑ i, ψ i d = 0 := by
        simp [ψ, hd]
      rw [hsum_zero]
      rw [show tail d =
        (MvPowerSeries.coeff d) f - MvPolynomial.coeff d (MvPowerSeries.truncTotal (σ := σ) (R := S) D f) by
          rfl]
      rw [hcoeff_trunc, sub_self]
  · intro i d hid
    change ψ i d = 0
    by_cases hd : D ≤ d.degree
    · by_cases hchoose : chooseIndex hd = i
      · have hge : (e i).succ ≤ d i := by
          simpa [hchoose] using chooseIndex_spec hd
        exact (hid.not_ge hge).elim
      · simp [ψ, hd, hchoose]
    · simp [ψ, hd]

/-- Helper for Lemma 15.39.1: the high total-degree tail is a finite sum of multiples of the
chosen variable powers, so any ring map killing those powers kills the whole tail. -/
theorem mvPowerSeries_tail_eq_sum_variable_powers_mul_of_degree_cutoff
    {σ : Type v} {S : Type u}
    [Fintype σ] [CommRing S]
    (e : σ → ℕ) (f : MvPowerSeries σ S) :
    ∃ h : σ → MvPowerSeries σ S,
      f - (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ f : MvPowerSeries σ S) =
        ∑ i, (MvPowerSeries.X i : MvPowerSeries σ S) ^ (e i).succ * h i := by
  classical
  obtain ⟨ψ, hψsum, hψvanish⟩ :=
    mvPowerSeries_tail_piece_sum_of_degree_cutoff (σ := σ) (S := S) e f
  have hdiv : ∀ i, (MvPowerSeries.X i : MvPowerSeries σ S) ^ (e i).succ ∣ ψ i := by
    intro i
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro d hd
    exact hψvanish i d hd
  choose h hh using hdiv
  -- Factor each tail piece by the first variable power whose exponent passes the cutoff.
  refine ⟨h, hψsum.trans ?_⟩
  simpa [hh]

/-- Helper for Lemma 15.39.1: once sufficiently high variable powers vanish, a ring hom from a
multivariable power series ring agrees with evaluation on the finite total-degree truncation. -/
theorem mvPowerSeries_ringHom_eq_eval₂_truncTotal_of_killed_variable_powers
    {σ : Type v} {S : Type u} {T : Type w}
    [Fintype σ] [CommRing S] [CommRing T]
    (g : MvPowerSeries σ S →+* T) (φ : S →+* T) (e : σ → ℕ)
    (hφ : g.comp (algebraMap S (MvPowerSeries σ S)) = φ)
    (hX : ∀ i, g ((MvPowerSeries.X i : MvPowerSeries σ S) ^ (e i).succ) = 0)
    (f : MvPowerSeries σ S) :
    g f =
      MvPolynomial.eval₂Hom φ (fun i ↦ g (MvPowerSeries.X i))
        (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ f) := by
  classical
  let D : ℕ := (∑ i, e i).succ
  obtain ⟨h, htail⟩ :=
    mvPowerSeries_tail_eq_sum_variable_powers_mul_of_degree_cutoff
      (σ := σ) (S := S) e f
  have htail_zero :
      g (f - (MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPowerSeries σ S)) = 0 := by
    -- Apply the map to the explicit tail factorization and use the power-killing hypotheses.
    calc
      g (f - (MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPowerSeries σ S)) =
          g (∑ i, (MvPowerSeries.X i : MvPowerSeries σ S) ^ (e i).succ * h i) := by
            rw [htail]
      _ = ∑ i, g ((MvPowerSeries.X i : MvPowerSeries σ S) ^ (e i).succ * h i) := by
            rw [map_sum]
      _ = 0 := by
            simp_rw [map_mul, hX, zero_mul]
            simp
  have hpoly :
      g.comp MvPolynomial.coeToMvPowerSeries.ringHom =
        MvPolynomial.eval₂Hom φ (fun i ↦ g (MvPowerSeries.X i)) := by
    -- On polynomials, both ring maps agree on coefficients and variables.
    apply MvPolynomial.ringHom_ext'
    · ext s
      simpa [RingHom.comp_apply, MvPowerSeries.c_eq_algebraMap] using
        DFunLike.congr_fun hφ s
    · intro i
      simp [RingHom.comp_apply]
  have hg_trunc :
      g f =
        g ((MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPolynomial σ S) :
          MvPowerSeries σ S) := by
    -- The killed tail shows that the whole series and its finite truncation have the same image.
    calc
      g f =
          g
            (f - (MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPowerSeries σ S) +
              (MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPowerSeries σ S)) := by
              simpa using
                congrArg g
                  (sub_add_cancel f
                    ((MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPolynomial σ S) :
                      MvPowerSeries σ S)).symm
      _ =
          g (f - (MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPowerSeries σ S)) +
            g ((MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPolynomial σ S) :
              MvPowerSeries σ S) := by
              rw [map_add]
      _ =
          0 +
            g ((MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPolynomial σ S) :
              MvPowerSeries σ S) := by
              rw [htail_zero]
      _ =
          g ((MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPolynomial σ S) :
            MvPowerSeries σ S) := by
              simp
  -- Now replace the truncated power series by the corresponding polynomial evaluation formula.
  calc
    g f =
        g ((MvPowerSeries.truncTotal (σ := σ) (R := S) D f : MvPolynomial σ S) :
          MvPowerSeries σ S) := hg_trunc
    _ =
        (g.comp MvPolynomial.coeToMvPowerSeries.ringHom)
          (MvPowerSeries.truncTotal (σ := σ) (R := S) D f) := by
            rfl
    _ =
        MvPolynomial.eval₂Hom φ (fun i ↦ g (MvPowerSeries.X i))
          (MvPowerSeries.truncTotal (σ := σ) (R := S) D f) := by
            simpa using DFunLike.congr_fun hpoly (MvPowerSeries.truncTotal (σ := σ) (R := S) D f)

/-- Helper for Lemma 15.39.1: once the coefficients are lifted and the variables are lifted to
nilpotent elements, the square-zero problem for multivariable power series has an algebraic
solution. -/
theorem mvPowerSeries_eval₂Hom_lifts_square_zero_problem
    {σ : Type v} {S : Type u} {A : Type w}
    [Finite σ] [CommRing S] [CommRing A]
    {J : Ideal A} {φS : S →+* A} {g : MvPowerSeries σ S →+* A ⧸ J}
    (x : σ → A)
    (hx : ∀ i, Ideal.Quotient.mk J (x i) = g (MvPowerSeries.X i))
    (hφS : (Ideal.Quotient.mk J).comp φS = g.comp (algebraMap S (MvPowerSeries σ S)))
    (hxnil : ∀ i, IsNilpotent (x i)) :
    ∃ φ : MvPowerSeries σ S →+* A,
      (Ideal.Quotient.mk J).comp φ = g ∧ φ.comp (algebraMap S (MvPowerSeries σ S)) = φS := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  letI : UniformSpace S := ⊥
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : UniformSpace A := ⊥
  letI : TopologicalSpace (A ⧸ J) := ⊥
  letI : DiscreteTopology (A ⧸ J) := ⟨rfl⟩
  letI : UniformSpace (A ⧸ J) := ⊥
  let ha : MvPowerSeries.HasEval x :=
    mvPowerSeries_hasEval_of_finite_of_isNilpotent (a := x) hxnil
  let φ : MvPowerSeries σ S →+* A :=
    MvPowerSeries.eval₂Hom (φ := φS) (a := x) continuous_of_discreteTopology ha
  refine ⟨φ, ?_, ?_⟩
  · let xbar : σ → A ⧸ J := fun i ↦ Ideal.Quotient.mk J (x i)
    have hxbar_nil : ∀ i, IsNilpotent (xbar i) := fun i ↦ idealQuotient_mk_isNilpotent (hxnil i)
    let hbar : MvPowerSeries.HasEval xbar :=
      mvPowerSeries_hasEval_of_finite_of_isNilpotent (a := xbar) hxbar_nil
    have hquot_eval :
        (Ideal.Quotient.mk J).comp φ =
          MvPowerSeries.eval₂Hom (φ := (Ideal.Quotient.mk J).comp φS) (a := xbar)
            continuous_of_discreteTopology hbar := by
      -- Postcomposing the chosen lift with the quotient map simply evaluates the quotiented
      -- coefficients and the quotiented variable tuple.
      refine RingHom.ext fun f ↦ ?_
      simpa [φ, xbar, MvPowerSeries.coe_eval₂Hom] using
        congrFun
          (MvPowerSeries.comp_eval₂
            (φ := φS) (a := x) continuous_of_discreteTopology ha continuous_of_discreteTopology) f
    have hg_eval :
        g =
          MvPowerSeries.eval₂Hom (φ := (Ideal.Quotient.mk J).comp φS) (a := xbar)
            continuous_of_discreteTopology hbar := by
      classical
      letI : Fintype σ := Fintype.ofFinite σ
      let e : σ → ℕ := fun i ↦ Classical.choose (hxbar_nil i)
      have he_zero : ∀ i, xbar i ^ e i = 0 := by
        intro i
        exact Classical.choose_spec (hxbar_nil i)
      have he : ∀ i, xbar i ^ (e i).succ = 0 := by
        intro i
        calc
          xbar i ^ (e i).succ = xbar i ^ e i * xbar i := by
            simp [e, pow_succ]
          _ = 0 := by
            simp [he_zero i]
      -- Route correction: compare both maps by the same finite truncation formula instead of
      -- using a continuity/uniqueness argument on the `WithPiTopology` domain.
      refine RingHom.ext fun f ↦ ?_
      calc
        g f =
            MvPolynomial.eval₂Hom ((Ideal.Quotient.mk J).comp φS)
              (fun i ↦ g (MvPowerSeries.X i))
              (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ f) := by
              exact
                mvPowerSeries_ringHom_eq_eval₂_truncTotal_of_killed_variable_powers
                  (σ := σ) (S := S) (T := A ⧸ J) g
                  ((Ideal.Quotient.mk J).comp φS) e hφS.symm
                  (by
                    intro i
                    calc
                      g ((MvPowerSeries.X i : MvPowerSeries σ S) ^ (e i).succ) =
                          (g (MvPowerSeries.X i)) ^ (e i).succ := by
                            rw [map_pow]
                      _ = (xbar i) ^ (e i).succ := by
                            simpa [xbar] using congrArg (fun z ↦ z ^ (e i).succ) (hx i).symm
                      _ = 0 := he i)
                  f
        _ =
            MvPolynomial.eval₂Hom ((Ideal.Quotient.mk J).comp φS) xbar
              (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ f) := by
              simp [xbar, hx]
        _ =
            MvPowerSeries.eval₂Hom (φ := (Ideal.Quotient.mk J).comp φS) (a := xbar)
              continuous_of_discreteTopology hbar f := by
              calc
                MvPolynomial.eval₂Hom ((Ideal.Quotient.mk J).comp φS) xbar
                    (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ f) =
                  MvPolynomial.eval₂Hom ((Ideal.Quotient.mk J).comp φS)
                    (fun i ↦
                      (MvPowerSeries.eval₂Hom
                        (φ := (Ideal.Quotient.mk J).comp φS) (a := xbar)
                        continuous_of_discreteTopology hbar) (MvPowerSeries.X i))
                    (MvPowerSeries.truncTotal (σ := σ) (R := S) (∑ i, e i).succ f) := by
                      simp [xbar, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
                _ =
                    MvPowerSeries.eval₂Hom (φ := (Ideal.Quotient.mk J).comp φS) (a := xbar)
                      continuous_of_discreteTopology hbar f := by
                      symm
                      exact
                        mvPowerSeries_ringHom_eq_eval₂_truncTotal_of_killed_variable_powers
                          (σ := σ) (S := S) (T := A ⧸ J)
                          (MvPowerSeries.eval₂Hom
                            (φ := (Ideal.Quotient.mk J).comp φS) (a := xbar)
                            continuous_of_discreteTopology hbar)
                          ((Ideal.Quotient.mk J).comp φS) e
                          (by
                            ext s
                            change
                              MvPowerSeries.eval₂Hom
                                  (φ := (Ideal.Quotient.mk J).comp φS) (a := xbar)
                                  continuous_of_discreteTopology hbar (MvPowerSeries.C s) =
                                ((Ideal.Quotient.mk J).comp φS) s
                            simp [MvPowerSeries.coe_eval₂Hom])
                          (by
                            intro i
                            rw [map_pow]
                            simpa [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X] using he i)
                          f
    -- Once the quotient map is identified with the canonical evaluation morphism, the chosen lift
    -- descends to the prescribed square-zero quotient problem.
    exact hquot_eval.trans hg_eval.symm
  · -- On coefficients, the evaluation lift was built from the chosen coefficient map `φS`.
    ext s
    change φ (MvPowerSeries.C s) = φS s
    simp [φ, MvPowerSeries.coe_eval₂Hom]

/-- Helper for Lemma 15.39.1: adic formal smoothness of the coefficient map implies adic formal
smoothness of the induced map into the corresponding finite-variable power series ring. -/
theorem mvPowerSeries_formally_smooth_for_madic_of_coeff_formally_smooth
    {R : Type u} {S : Type v} {σ : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S] [Finite σ]
    (hcoeff : RingHom.formally_smooth_for_adic (algebraMap R S) (maximalIdeal S)) :
    RingHom.formally_smooth_for_adic
      (algebraMap R (MvPowerSeries σ S)) (maximalIdeal (MvPowerSeries σ S)) := by
  rw [RingHom.formally_smooth_for_adic_iff] at hcoeff ⊢
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
  letI : TopologicalSpace (MvPowerSeries σ S) :=
    Ideal.adicTopology (maximalIdeal (MvPowerSeries σ S))
  refine
    { toContinuous := continuous_of_discreteTopology
      lift_condition := ?_ }
  intro A _ _ _ J _ hJ g hg g0 hg0 hcomm
  classical
  let gS : S →+* A ⧸ J := g.comp (algebraMap S (MvPowerSeries σ S))
  have hgS : Continuous gS := by
    -- Restrict the quotient map along the coefficient inclusion into the power series ring.
    exact
      hg.comp
        (continuous_algebraMap_to_mvPowerSeries_madic (σ := σ) (S := S))
  have hcommS : (Ideal.Quotient.mk J).comp g0 = gS.comp (algebraMap R S) := by
    -- The coefficient square is the original commutative square restricted along `S → S[[X]]`.
    ext r
    calc
      Ideal.Quotient.mk J (g0 r) = g (algebraMap R (MvPowerSeries σ S) r) := by
        simpa [RingHom.comp_apply] using DFunLike.congr_fun hcomm r
      _ = g (algebraMap S (MvPowerSeries σ S) (algebraMap R S r)) := by
        simpa using
          congrArg g
            (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S (MvPowerSeries σ S)) r)
      _ = gS (algebraMap R S r) := by
        rfl
  obtain ⟨φS, _, hφSquot, hφSbase⟩ :=
    RingHom.FormallySmoothTopologically.exists_lift hcoeff J hJ gS hgS g0 hg0 hcommS
  have hmadic : IsAdic (maximalIdeal (MvPowerSeries σ S)) := rfl
  rcases
      RingHom.pow_le_ker_of_continuous_to_discrete_quotient
        (I := maximalIdeal (MvPowerSeries σ S)) hmadic g hg with
    ⟨M, hker⟩
  let xbar : σ → A ⧸ J := fun i ↦ g (MvPowerSeries.X i)
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (xbar i)
  have hxnil : ∀ i, IsNilpotent (x i) := by
    intro i
    -- Route correction: derive nilpotence from the adic kernel bound instead of from a separate
    -- continuity comparison for arbitrary quotient maps.
    exact ⟨2 * M,
      mvPowerSeries_variable_lifts_nilpotent_of_pow_le_ker
        (σ := σ) (S := S) (A := A) hJ (g := g) (M := M) hker (hx i)⟩
  obtain ⟨φ, hφquot, hφcoeff⟩ :=
    mvPowerSeries_eval₂Hom_lifts_square_zero_problem
      (σ := σ) (S := S) (A := A) (J := J) (φS := φS) (g := g) x
      (by
        intro i
        simpa [xbar] using hx i)
      (by
        ext s
        simpa [gS, RingHom.comp_assoc] using DFunLike.congr_fun hφSquot s)
      hxnil
  have hkerφ :
      maximalIdeal (MvPowerSeries σ S) ^ (M * 2) ≤ RingHom.ker φ := by
    simpa [pow_mul, hφquot] using
      (ker_sq_of_quotient_ker_and_square_zero
        (I := maximalIdeal (MvPowerSeries σ S) ^ M) (J := J) hJ
        (f := φ) (g := g) hφquot hker)
  have hopen :
      IsOpen
        (((maximalIdeal (MvPowerSeries σ S)) ^ (M * 2) : Ideal (MvPowerSeries σ S)) :
          Set (MvPowerSeries σ S)) := by
    exact (isAdic_iff.mp hmadic).1 (M * 2)
  have hφcont : Continuous φ :=
    RingHom.continuous_of_open_ideal_le_ker
      φ ((maximalIdeal (MvPowerSeries σ S)) ^ (M * 2)) hopen hkerφ
  have hφbase : φ.comp (algebraMap R (MvPowerSeries σ S)) = g0 := by
    -- The power-series lift restricts to the coefficient lift, which already extends `g0`.
    ext r
    calc
      φ (algebraMap R (MvPowerSeries σ S) r) =
          φ (algebraMap S (MvPowerSeries σ S) (algebraMap R S r)) := by
            simpa using
              congrArg φ
                (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S (MvPowerSeries σ S)) r)
      _ = φS (algebraMap R S r) := by
            simpa [RingHom.comp_apply] using
              DFunLike.congr_fun hφcoeff (algebraMap R S r)
      _ = g0 r := by
            simpa [RingHom.comp_apply] using DFunLike.congr_fun hφSbase r
  exact ⟨φ, hφcont, hφquot, hφbase⟩

/-- Helper for Lemma 15.39.1: a kernel power for a quotient map out of a Cohen ring kills the
corresponding power of the residue-characteristic element. -/
theorem cohenRing_residueChar_power_killed_of_maximalIdeal_pow_le_ker
    {Λ : Type u} {A : Type v} [CommRing Λ] [IsCohenRing Λ] [CommRing A]
    {J : Ideal A} {g : Λ →+* A ⧸ J} {M : ℕ}
    (hker : maximalIdeal Λ ^ M ≤ RingHom.ker g) :
    g ((ringChar (ResidueField Λ) : Λ) ^ M) = 0 := by
  -- The residue characteristic generates the maximal ideal of a Cohen ring.
  apply RingHom.mem_ker.mp
  exact hker <| Ideal.pow_mem_pow IsCohenRing.residueChar_mem_maximalIdeal M

/-- Helper for Lemma 15.39.1: the canonical map from `ℤ` to a Cohen ring is formally smooth for
the maximal-ideal-adic topology. -/
theorem int_to_cohenRing_formally_smooth_for_madic
    {Λ : Type u} [CommRing Λ] [IsCohenRing Λ] :
    RingHom.formally_smooth_for_adic (algebraMap ℤ Λ) (maximalIdeal Λ) := by
  rw [RingHom.formally_smooth_for_adic_iff]
  letI : TopologicalSpace ℤ := ⊥
  letI : DiscreteTopology ℤ := ⟨rfl⟩
  letI : TopologicalSpace Λ := Ideal.adicTopology (maximalIdeal Λ)
  refine
    { toContinuous := continuous_of_discreteTopology
      lift_condition := ?_ }
  intro A _ _ _ J _ hJ g hg g0 _ hcomm
  let p : ℕ := ringChar (ResidueField Λ)
  have hmadic : IsAdic (maximalIdeal Λ) := rfl
  rcases
      RingHom.pow_le_ker_of_continuous_to_discrete_quotient
        (I := maximalIdeal Λ) hmadic g hg with
    ⟨M, hker⟩
  -- Continuity of the quotient map forces a power of the maximal ideal, hence a power of `p`,
  -- to vanish in the discrete quotient.
  have hgkillM : g ((p : Λ) ^ M) = 0 := by
    exact
      cohenRing_residueChar_power_killed_of_maximalIdeal_pow_le_ker
        (Λ := Λ) (A := A) (J := J) (g := g) (M := M) hker
  have hbasekillM : (g.comp (algebraMap ℤ Λ)) ((p : ℤ) ^ M) = 0 := by
    simpa [RingHom.comp_apply, map_pow] using hgkillM
  -- Route correction: first descend the integer and Cohen-ring maps to the same finite
  -- `p`-power quotient, then solve the square-zero problem there by formal smoothness.
  have hg0kill2M : g0 ((p : ℤ) ^ (2 * M)) = 0 := by
    exact
      int_base_map_kills_pow_of_square_zero
        (J := J) hJ (g0 := g0) (g := g.comp (algebraMap ℤ Λ)) hcomm
        (p := p) (N := M) hbasekillM
  let N : ℕ := 2 * M + 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hgkillN : g ((p : Λ) ^ N) = 0 := by
    have hNsplit : N = M + (M + 1) := by
      dsimp [N]
      omega
    rw [hNsplit, pow_add, map_mul, hgkillM, zero_mul]
  have hg0killN : g0 ((p : ℤ) ^ N) = 0 := by
    have hNsplit : N = 2 * M + 1 := by
      rfl
    rw [hNsplit, pow_add, pow_one, map_mul, hg0kill2M, zero_mul]
  let IΛ : Ideal Λ := Ideal.span ({((p ^ N) : Λ)} : Set Λ)
  let qΛ : Λ →+* Λ ⧸ IΛ := Ideal.Quotient.mk IΛ
  obtain ⟨gQ, hgQ⟩ :=
    ringHom_factors_through_quotient_span_singleton_pow
      (R := Λ) (S := A ⧸ J) (r := (p : Λ)) (N := N) (f := g) hgkillN
  obtain ⟨gZ, hgZ⟩ :=
    int_base_map_descends_to_zmod_pow
      (A := A) (p := p) (N := N) (g0 := g0) hg0killN
  let n : ℕ+ := ⟨N, hNpos⟩
  letI : CharP (Λ ⧸ IΛ) (p ^ N) := by
    simpa [IΛ, n, N] using (quotient_charP_residueCharPow (Λ := Λ) n)
  letI : Algebra (ZMod (p ^ N)) (Λ ⧸ IΛ) := ZMod.algebra _ _
  have hfs :
      RingHom.FormallySmooth (algebraMap (ZMod (p ^ N)) (Λ ⧸ IΛ)) := by
    simpa [IΛ, n, N] using
      (cohenRing_zmodPow_quotient_algebraMap_formallySmooth (Λ := Λ) n)
  have hcommZ :
      (Ideal.Quotient.mk J).comp gZ =
        gQ.comp (algebraMap (ZMod (p ^ N)) (Λ ⧸ IΛ)) := by
    exact RingHom.ext_zmod _ _
  obtain ⟨φQ, hφQ, hφZ⟩ :=
    RingHom.FormallySmooth.exists_lift hfs J hJ gQ gZ hcommZ
  let φ : Λ →+* A := φQ.comp qΛ
  have hφquot : (Ideal.Quotient.mk J).comp φ = g := by
    -- Postcomposing the quotient-level lift with `Λ → Λ ⧸ (p ^ N)` recovers the original
    -- quotient map `g`.
    ext x
    calc
      Ideal.Quotient.mk J (φ x) = gQ (qΛ x) := by
        simpa [φ] using DFunLike.congr_fun hφQ (qΛ x)
      _ = g x := by
        simpa [qΛ] using DFunLike.congr_fun hgQ x
  have hφbase : φ.comp (algebraMap ℤ Λ) = g0 := by
    have hbase :
        qΛ.comp (algebraMap ℤ Λ) =
          (algebraMap (ZMod (p ^ N)) (Λ ⧸ IΛ)).comp
            (Int.castRingHom (ZMod (p ^ N))) := by
      exact RingHom.ext_int _ _
    -- The quotient lift agrees with the prescribed integer map after transporting across `ZMod`.
    rw [show φ = φQ.comp qΛ by rfl, RingHom.comp_assoc, hbase, ← RingHom.comp_assoc, hφZ, hgZ]
  have hkerφ : maximalIdeal Λ ^ (M * 2) ≤ RingHom.ker φ := by
    simpa [pow_mul, hφquot] using
      (ker_sq_of_quotient_ker_and_square_zero
        (I := maximalIdeal Λ ^ M) (J := J) hJ (f := φ) (g := g) hφquot hker)
  have hopen : IsOpen (((maximalIdeal Λ) ^ (M * 2) : Ideal Λ) : Set Λ) := by
    exact (isAdic_iff.mp hmadic).1 (M * 2)
  have hφcont : Continuous φ :=
    RingHom.continuous_of_open_ideal_le_ker
      φ ((maximalIdeal Λ) ^ (M * 2)) hopen hkerφ
  exact ⟨φ, hφcont, hφquot, hφbase⟩

section CharZeroField

variable {σ : Type v} [Finite σ] (K : Type u) [Field K] [CharZero K]

local notation "P" => MvPowerSeries σ K

-- Proof sketch: first use Proposition `10.158.9` to see that `ℚ → K` is formally smooth for a
-- characteristic-zero field `K`. Then apply the universal property of the finite-variable formal
-- power series ring to lift maps coefficientwise, giving formal smoothness for the maximal-ideal
-- adic topology on `MvPowerSeries σ K`.
/-- Lemma 15.39.1 (1): if `K` is a field of characteristic zero, then the canonical map
`ℚ → K[[x_i]]`, formalized as `algebraMap ℚ (MvPowerSeries σ K)` for a finite variable set `σ`, is
formally
smooth in the `maximalIdeal`-adic topology. -/
@[stacks 07NL]
theorem rational_to_mvPowerSeries_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap ℚ P) (maximalIdeal P) := by
  -- First identify `ℚ → K` as algebraically formally smooth in characteristic zero.
  have hcoeff : RingHom.formally_smooth_for_adic (algebraMap ℚ K) (maximalIdeal K) := by
    exact field_formally_smooth_for_madic_of_formallySmooth
      (Algebra.formallySmooth_of_charZero (k := ℚ) (K := K))
  -- Then pass from the coefficient ring to the finite-variable power series ring.
  exact
    mvPowerSeries_formally_smooth_for_madic_of_coeff_formally_smooth
      (σ := σ) hcoeff

end CharZeroField

section CharPField

variable {σ : Type v} [Finite σ] (L : Type u) [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]

local instance : Algebra (ZMod p) L := ZMod.algebra L p
local notation "P" => MvPowerSeries σ L

-- Proof sketch: by Proposition `10.158.9`, a field `L` of characteristic `p` is formally smooth
-- over `𝔽_p = ZMod p`. The universal property of the finite-variable formal power series ring then
-- upgrades this coefficientwise lifting property to the maximal-ideal adic topology on
-- `MvPowerSeries σ L`.
/-- Lemma 15.39.1 (2): if `L` is a field of characteristic `p > 0`, then the canonical map
`𝔽_p → L[[x_i]]`, formalized as `algebraMap (ZMod p) (MvPowerSeries σ L)` for a finite variable
set `σ`, is formally smooth in the `maximalIdeal`-adic topology. -/
@[stacks 07NL]
theorem zmod_to_mvPowerSeries_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap (ZMod p) P) (maximalIdeal P) := by
  -- The coefficient extension `𝔽_p → L` is formally smooth because finite fields are perfect.
  have hcoeff : RingHom.formally_smooth_for_adic (algebraMap (ZMod p) L) (maximalIdeal L) := by
    have hfs : Algebra.FormallySmooth (ZMod p) L := by
      letI : Algebra.IsSeparableOver (ZMod p) L := by
        letI : PerfectField (ZMod p) := inferInstance
        exact Algebra.IsSeparableOver.of_perfectField
      exact Algebra.formallySmooth_of_isSeparableOver
    exact field_formally_smooth_for_madic_of_formallySmooth hfs
  -- Then pass from the coefficient ring to the finite-variable power series ring.
  exact
    mvPowerSeries_formally_smooth_for_madic_of_coeff_formally_smooth
      (σ := σ) hcoeff

end CharPField

section CohenRing

variable {σ : Type v} [Finite σ] (Λ : Type u) [CommRing Λ] [IsCohenRing Λ]

local notation "P" => MvPowerSeries σ Λ

-- Proof sketch: choose the prime `p` generating the maximal ideal of the Cohen ring `Λ`. Lemma
-- `10.160.7` gives formal smoothness of the maps `ZMod (p^m) → Λ ⧸ (p^m)` for all `m > 0`, and
-- Lemma `10.160.7` together with Definition `15.37.1` implies `ℤ → Λ` is formally smooth in the
-- `maximalIdeal Λ`-adic topology. The universal property of finite-variable formal power series
-- then yields the corresponding statement for `MvPowerSeries σ Λ`.
/-- Lemma 15.39.1 (3): if `Λ` is a Cohen ring, then the canonical map
`ℤ → Λ[[x_i]]`, formalized as `algebraMap ℤ (MvPowerSeries σ Λ)` for a finite variable set `σ`, is
formally
smooth in the `maximalIdeal`-adic topology. -/
@[stacks 07NL]
theorem int_to_mvPowerSeries_over_cohenRing_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap ℤ P) (maximalIdeal P) := by
  -- Route correction: solve the mixed-characteristic coefficient lifting problem first, then
  -- apply the same finite-variable power-series bridge as in the field cases.
  have hcoeff : RingHom.formally_smooth_for_adic (algebraMap ℤ Λ) (maximalIdeal Λ) := by
    exact int_to_cohenRing_formally_smooth_for_madic
  exact
    mvPowerSeries_formally_smooth_for_madic_of_coeff_formally_smooth
      (σ := σ) hcoeff

end CohenRing

end
