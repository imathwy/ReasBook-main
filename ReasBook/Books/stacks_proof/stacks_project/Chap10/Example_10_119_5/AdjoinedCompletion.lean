import stacks_proof.stacks_project.Chap10.Example_10_119_5.CoefficientDVRCompletion

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

local notation "A" => finitePthPowerCoefficientSubring k p

-- Proof sketch: if `f ∈ A` then `R = A`, so the result comes from the DVR structure on `A`;
-- otherwise apply the one-dimensional Krull-Akizuki argument to the overring `R`.
/-- The adjoined ring `R = A[f]` is Noetherian. -/
theorem finitePthPowerCoefficientAdjoinSubring_isNoetherianRing
    (f : PowerSeries k) :
    IsNoetherianRing ↥(finitePthPowerCoefficientAdjoinSubring k p f) := by
  -- The DVR `A` is Noetherian, and the adjoined ring is finite over `A`.
  letI : Module.Finite ↥A ↥(finitePthPowerCoefficientAdjoinSubring k p f) :=
    finitePthPowerCoefficientAdjoinSubring_moduleFinite k p f
  exact IsNoetherianRing.of_finite ↥A
    ↥(finitePthPowerCoefficientAdjoinSubring k p f)

-- Proof sketch: if `f ∈ A` then `R = A`, and otherwise `R` still sits between the DVR `A` and
-- the complete local ring `k[[x]]`, with maximal ideal induced by the `x`-adic valuation.
/-- The adjoined ring `R = A[f]` is local. -/
theorem finitePthPowerCoefficientAdjoinSubring_isLocal
    (f : PowerSeries k) :
    IsLocalRing ↥(finitePthPowerCoefficientAdjoinSubring k p f) := by
  let R := finitePthPowerCoefficientAdjoinSubring k p f
  haveI : IsLocalHom (algebraMap ↥A (PowerSeries k)) :=
    finitePthPowerCoefficientSubring_algebraMap_isLocalHom k p
  -- It is enough to show that every unit of the ambient local ring which lies in `R` has its
  -- inverse in `R`.
  refine Subring.isLocalRing_of_unit R ?_
  intro x hx hxUnit
  rcases hxUnit with ⟨u, rfl⟩
  -- The `p`th power of the ambient unit lies in `A`, and localness of `A → k[[X]]` makes it a
  -- unit already in `A`.
  let xpA : ↥A :=
    ⟨(u : PowerSeries k) ^ p,
      pow_mem_finitePthPowerCoefficientSubring k p (u : PowerSeries k)⟩
  have hxpAUnit : IsUnit xpA := by
    rw [← isUnit_map_iff (algebraMap ↥A (PowerSeries k)) xpA]
    change IsUnit ((u : PowerSeries k) ^ p)
    exact u.isUnit.pow p
  rcases hxpAUnit with ⟨v, hv⟩
  -- The inverse in `R` is `u^(p-1)` times the inverse of `u^p` coming from `A`.
  let bval : PowerSeries k :=
    (u : PowerSeries k) ^ (p - 1) * ((v⁻¹ : Units ↥A) : ↥A)
  have hbmem : bval ∈ R := by
    exact R.mul_mem (R.pow_mem hx (p - 1))
      (finitePthPowerCoefficientSubring_le_adjoinSubring k p f
        ((v⁻¹ : Units ↥A) : ↥A).2)
  let b : ↥R := ⟨bval, hbmem⟩
  refine (isUnit_iff_exists_inv).mpr ⟨b, ?_⟩
  apply Subtype.ext
  dsimp [b, bval]
  have hvPS : (((v : Units ↥A) : ↥A) : PowerSeries k) = (u : PowerSeries k) ^ p := by
    simpa [xpA] using congrArg (fun z : ↥A => (z : PowerSeries k)) hv
  have hvinvPS :
      ((((v⁻¹ : Units ↥A) : ↥A) : PowerSeries k) * (u : PowerSeries k) ^ p) = 1 := by
    rw [← hvPS]
    simpa only [Units.val_mul, Units.val_one, Subring.coe_mul, Subring.coe_one] using
      congrArg (fun z : ↥A => (z : PowerSeries k)) (Units.inv_mul v)
  have hp_ne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  calc
    (u : PowerSeries k) *
        ((u : PowerSeries k) ^ (p - 1) *
          (((v⁻¹ : Units ↥A) : ↥A) : PowerSeries k))
        = ((u : PowerSeries k) * (u : PowerSeries k) ^ (p - 1)) *
            (((v⁻¹ : Units ↥A) : ↥A) : PowerSeries k) := by
          rw [← mul_assoc]
    _ = (u : PowerSeries k) ^ p * (((v⁻¹ : Units ↥A) : ↥A) : PowerSeries k) := by
          rw [mul_comm (u : PowerSeries k) ((u : PowerSeries k) ^ (p - 1)),
            ← pow_succ, Nat.sub_one_add_one hp_ne]
    _ = (((v⁻¹ : Units ↥A) : ↥A) : PowerSeries k) * (u : PowerSeries k) ^ p := by
          rw [mul_comm]
    _ = 1 := hvinvPS

instance
    (f : PowerSeries k) :
    IsLocalRing ↥(finitePthPowerCoefficientAdjoinSubring k p f) :=
  finitePthPowerCoefficientAdjoinSubring_isLocal k p f

section AdjoinedRing

variable (f : PowerSeries k)

local notation "R" => finitePthPowerCoefficientAdjoinSubring k p f
local notation "ACompletion" => AdicCompletion (maximalIdeal ↥A) ↥A
local notation "RCompletion" => AdicCompletion (maximalIdeal ↥R) ↥R

/-- Helper for Example 10.119.5: the integral inclusion `A → A[f]` is a local homomorphism, so it
induces a map on maximal-ideal completions. -/
local instance : IsLocalHom (algebraMap ↥A ↥R) := by
  -- The finite inclusion is integral, and the subtype map into `k[[X]]` is injective.
  letI : Module.Finite ↥A ↥R :=
    finitePthPowerCoefficientAdjoinSubring_moduleFinite k p f
  have hIntegral : Algebra.IsIntegral ↥A ↥R := inferInstance
  have hInjective : Function.Injective (algebraMap ↥A ↥R) := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ↥R => (z : PowerSeries k)) h
  exact (algebraMap_isIntegral_iff.mpr hIntegral).isLocalHom hInjective

/-- A nonzero element with a vanishing power certifies that the ambient ring is not reduced. -/
lemma not_isReduced_of_exists_ne_zero_pow_eq_zero
    {S : Type*} [MonoidWithZero S] {z : S} {n : ℕ}
    (hz : z ≠ 0) (hzpow : z ^ n = 0) :
    ¬ IsReduced S := by
  -- In a reduced ring, every nilpotent element must vanish.
  intro hred
  exact hz (eq_zero_of_pow_eq_zero hzpow)

/-- Helper for Chap10 Example 10 119 5: equality modulo the extended `I`-power makes the
ordinary quotient class lie in the corresponding `I`-adic multiple. -/
private lemma quotientClass_mem_pow_smul_of_eq_mod_mapPow
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]
    (I : Ideal A₀) (n : ℕ) (x : B₀) (a : A₀)
    (h : Ideal.Quotient.mk ((Ideal.map (algebraMap A₀ B₀) I) ^ n) x =
      Ideal.Quotient.mk ((Ideal.map (algebraMap A₀ B₀) I) ^ n) (algebraMap A₀ B₀ a)) :
    (LinearMap.range (Algebra.linearMap A₀ B₀)).mkQ x ∈
      I ^ n • (⊤ : Submodule A₀ (B₀ ⧸ LinearMap.range (Algebra.linearMap A₀ B₀))) := by
  let Q : Submodule A₀ B₀ := LinearMap.range (Algebra.linearMap A₀ B₀)
  let q : B₀ →ₗ[A₀] B₀ ⧸ Q := Q.mkQ
  -- First read the quotient equality as membership in the extended ideal power.
  have hxsub : x - algebraMap A₀ B₀ a ∈ (Ideal.map (algebraMap A₀ B₀) I) ^ n := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  have hxsub' : x - algebraMap A₀ B₀ a ∈ Ideal.map (algebraMap A₀ B₀) (I ^ n) := by
    simpa [Ideal.map_pow] using hxsub
  have hxsmulB : x - algebraMap A₀ B₀ a ∈ I ^ n • (⊤ : Submodule A₀ B₀) := by
    simpa [Ideal.smul_top_eq_map] using hxsub'
  -- Push the `I`-multiple through the quotient map; the image of the top submodule is top.
  have hqmem : q (x - algebraMap A₀ B₀ a) ∈
      I ^ n • (⊤ : Submodule A₀ (B₀ ⧸ Q)) := by
    have hmap : q (x - algebraMap A₀ B₀ a) ∈
        (I ^ n • (⊤ : Submodule A₀ B₀)).map q := by
      exact ⟨x - algebraMap A₀ B₀ a, hxsmulB, rfl⟩
    rw [Submodule.map_smul''] at hmap
    rwa [Submodule.map_top, LinearMap.range_eq_top.mpr Q.mkQ_surjective] at hmap
  -- The base element dies in the quotient by the image of `A`, so the class of `x` is the same.
  have hbase : q (algebraMap A₀ B₀ a) = 0 := by
    change Q.mkQ (algebraMap A₀ B₀ a) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self (Algebra.linearMap A₀ B₀) a
  have hqeq : q (x - algebraMap A₀ B₀ a) = q x := by
    simp [map_sub, hbase]
  simpa [q, Q, hqeq] using hqmem

/-- Helper for Chap10 Example 10 119 5: the residue quotient of `A[f]` modulo the extended
maximal ideal is finite over the residue field of `A`. -/
private lemma adjoinSubring_residueQuotient_finite :
    Module.Finite (↥A ⧸ maximalIdeal ↥A)
      (↥R ⧸ Ideal.map (algebraMap ↥A ↥R) (maximalIdeal ↥A)) := by
  -- Finite generation over `A` descends to the quotient, then restricts to the residue field.
  letI : Module.Finite ↥A ↥R :=
    finitePthPowerCoefficientAdjoinSubring_moduleFinite k p f
  exact Module.Finite.of_restrictScalars_finite ↥A (↥A ⧸ maximalIdeal ↥A)
    (↥R ⧸ Ideal.map (algebraMap ↥A ↥R) (maximalIdeal ↥A))

/-- Helper for Chap10 Example 10 119 5: every finite quotient coordinate of a base-completion
element lifted to `A[f]` is represented by an element from `A`. -/
private lemma baseCompletion_stage_lifts_to_adjoinBase
    (c : ACompletion) (n : ℕ) :
    ∃ a : ↥A,
      AdicCompletion.evalₐ (Ideal.map (algebraMap ↥A ↥R) (maximalIdeal ↥A)) n
        (maximalIdealCompletionAlgEquivMadicCompletion
          (Ideal.fg_of_isNoetherianRing (maximalIdeal ↥A))
          (adjoinSubring_residueQuotient_finite (k := k) (p := p) (f := f))
          (maximalIdealCompletionMap (algebraMap ↥A ↥R) c)) =
        Ideal.Quotient.mk
          ((Ideal.map (algebraMap ↥A ↥R) (maximalIdeal ↥A)) ^ n)
          (algebraMap ↥A ↥R a) := by
  -- The owner API computes the finite-stage coordinate as the quotient map from the base stage.
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal ↥A) n c)
  refine ⟨a, ?_⟩
  rw [maximalIdealCompletionAlgEquivMadicCompletion_eval_base]
  -- Choose a representative of the source quotient coordinate and map that representative to
  -- the adjoined ring quotient.
  rw [← ha]
  simp [Ideal.quotientMapₐ]

/-- Helper for Example 10.119.5: the distinguished completed generator coming from the adjoined
power series `f`. -/
private noncomputable def adjoined_completion_generator :
    RCompletion :=
  AdicCompletion.of (maximalIdeal ↥R) ↥R
    ⟨f, Subring.subset_closure (Set.mem_insert f (finitePthPowerCoefficientSubring k p))⟩

/-- Helper for Example 10.119.5: the element of `A^` corresponding to the ambient series `f`
under the completion comparison `A^ ≃ k[[x]]`. -/
private noncomputable def completion_base_series_lift :
    ACompletion :=
  (finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries k p).symm f

/-- Helper for Example 10.119.5: the lift of the ambient series `f` from `A^` into `R^`. -/
private noncomputable def adjoined_completion_base_lift :
    RCompletion :=
  maximalIdealCompletionMap (algebraMap ↥A ↥R)
    (completion_base_series_lift (k := k) (p := p) (f := f))

/-- Helper for Example 10.119.5: the completed generator and the base lift have the same `p`th
power, so their difference is `p`-nilpotent. -/
lemma completion_generator_minus_baseLift_pow_eq_zero :
    (adjoined_completion_generator (k := k) (p := p) (f := f) -
        adjoined_completion_base_lift (k := k) (p := p) (f := f)) ^ p = 0 := by
  -- Normalize the two `p`th powers to the same completed image of `f ^ p ∈ A`.
  letI : CharP k p := by
    cases (inferInstance : ExpChar k p) with
    | zero =>
        exact False.elim (Nat.not_prime_one (Fact.out : Nat.Prime 1))
    | prime _ =>
        infer_instance
  have hCInjective : Function.Injective (PowerSeries.C : k →+* PowerSeries k) :=
    PowerSeries.C_injective
  letI : CharP (PowerSeries k) p := charP_of_injective_ringHom hCInjective p
  have hRInjective : Function.Injective (algebraMap ↥R (PowerSeries k)) := by
    intro x y h
    exact Subtype.ext h
  letI : CharP ↥R p := RingHom.charP (algebraMap ↥R (PowerSeries k)) hRInjective p
  letI : IsNoetherianRing ↥R :=
    finitePthPowerCoefficientAdjoinSubring_isNoetherianRing k p f
  have hCompletionInjective :
      Function.Injective (algebraMap ↥R RCompletion) := by
    simpa using
      (AdicCompletion.of_injective (I := maximalIdeal ↥R) (M := ↥R))
  have hCharCompletion : CharP RCompletion p := by
    constructor
    intro n
    constructor
    · intro hn
      have hnR : (n : ↥R) = 0 :=
        hCompletionInjective (by simpa using hn)
      exact (CharP.cast_eq_zero_iff ↥R p n).1 hnR
    · intro hn
      have hnR : (n : ↥R) = 0 :=
        (CharP.cast_eq_zero_iff ↥R p n).2 hn
      simpa using congrArg (algebraMap ↥R RCompletion) hnR
  letI : CharP RCompletion p := hCharCompletion
  let fpA : ↥A :=
    ⟨f ^ p, pow_mem_finitePthPowerCoefficientSubring k p f⟩
  let fR : ↥R :=
    ⟨f, Subring.subset_closure (Set.mem_insert f (finitePthPowerCoefficientSubring k p))⟩
  have hfR_pow : fR ^ p = algebraMap ↥A ↥R fpA := by
    ext
    rfl
  have hbase_pow_source :
      completion_base_series_lift (k := k) (p := p) (f := f) ^ p =
        AdicCompletion.of (maximalIdeal ↥A) ↥A fpA := by
    -- Apply the `A^ ≃ k[[X]]` comparison to reduce to equality in the ambient power-series ring.
    apply (finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries k p).injective
    simp [completion_base_series_lift, fpA, map_pow,
      finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries_of]
  have hgen_pow :
      adjoined_completion_generator (k := k) (p := p) (f := f) ^ p =
        algebraMap ↥R RCompletion (algebraMap ↥A ↥R fpA) := by
    -- The dense generator is an algebra-map value, so powers commute with the completion map.
    calc
      adjoined_completion_generator (k := k) (p := p) (f := f) ^ p =
          (algebraMap ↥R RCompletion fR) ^ p := by
            rfl
      _ = algebraMap ↥R RCompletion (fR ^ p) := by
            exact (map_pow (algebraMap ↥R RCompletion) fR p).symm
      _ = algebraMap ↥R RCompletion (algebraMap ↥A ↥R fpA) := by
            rw [hfR_pow]
  have hbase_pow :
      adjoined_completion_base_lift (k := k) (p := p) (f := f) ^ p =
        algebraMap ↥R RCompletion (algebraMap ↥A ↥R fpA) := by
    -- Functoriality of maximal-ideal completion carries the source `f ^ p` into `R^`.
    calc
      adjoined_completion_base_lift (k := k) (p := p) (f := f) ^ p =
          maximalIdealCompletionMap (algebraMap ↥A ↥R)
            (completion_base_series_lift (k := k) (p := p) (f := f) ^ p) := by
            simpa [adjoined_completion_base_lift] using
              (map_pow (maximalIdealCompletionMap (algebraMap ↥A ↥R))
                (completion_base_series_lift (k := k) (p := p) (f := f)) p).symm
      _ =
          maximalIdealCompletionMap (algebraMap ↥A ↥R)
            (AdicCompletion.of (maximalIdeal ↥A) ↥A fpA) := by
            rw [hbase_pow_source]
      _ = algebraMap ↥R RCompletion (algebraMap ↥A ↥R fpA) := by
            have hcomp := RingHom.congr_fun
              (maximalIdealCompletionMap_comp (algebraMap ↥A ↥R)) fpA
            simpa using hcomp
  have hpowers :
      adjoined_completion_generator (k := k) (p := p) (f := f) ^ p =
        adjoined_completion_base_lift (k := k) (p := p) (f := f) ^ p := by
    rw [hgen_pow, hbase_pow]
  rw [sub_pow_char, hpowers, sub_self]

/-- Helper for Example 10.119.5: if the completed generator equals the base lift, then the
original series `f` already lies in `A`. -/
lemma completion_generator_eq_baseLift_imp_mem_base
    (hEq :
      adjoined_completion_generator (k := k) (p := p) (f := f) =
        adjoined_completion_base_lift (k := k) (p := p) (f := f)) :
    f ∈ A := by
  -- Route correction: the old route tried to descend directly from equality in `R^` to
  -- `f ∈ A`. The intended replacement is stagewise Hausdorff descent through the
  -- `(maximalIdeal A)R`-adic finite quotients.
  let mAR : Ideal ↥R := Ideal.map (algebraMap ↥A ↥R) (maximalIdeal ↥A)
  let hmA : (maximalIdeal ↥A).FG := Ideal.fg_of_isNoetherianRing (maximalIdeal ↥A)
  let hfinite : Module.Finite (↥A ⧸ maximalIdeal ↥A) (↥R ⧸ mAR) :=
    adjoinSubring_residueQuotient_finite (k := k) (p := p) (f := f)
  let e : RCompletion ≃ₐ[↥R] AdicCompletion mAR ↥R :=
    maximalIdealCompletionAlgEquivMadicCompletion hmA hfinite
  let fR : ↥R :=
    ⟨f, Subring.subset_closure (Set.mem_insert f (finitePthPowerCoefficientSubring k p))⟩
  let Q : Submodule ↥A ↥R := LinearMap.range (Algebra.linearMap ↥A ↥R)
  let qf : ↥R ⧸ Q := Q.mkQ fR
  -- At each finite stage, equality in the completion gives equality modulo `(maximalIdeal A)R`.
  have hmem_all :
      ∀ n : ℕ, qf ∈
        (maximalIdeal ↥A) ^ n • (⊤ : Submodule ↥A (↥R ⧸ Q)) := by
    intro n
    have hstage :
        AdicCompletion.evalₐ mAR n
            (e (adjoined_completion_generator (k := k) (p := p) (f := f))) =
          AdicCompletion.evalₐ mAR n
            (e (adjoined_completion_base_lift (k := k) (p := p) (f := f))) := by
      exact congrArg (fun z : RCompletion ↦ AdicCompletion.evalₐ mAR n (e z)) hEq
    have hgen_stage :
        AdicCompletion.evalₐ mAR n
            (e (adjoined_completion_generator (k := k) (p := p) (f := f))) =
          Ideal.Quotient.mk (mAR ^ n) fR := by
      have hof := maximalIdealCompletionAlgEquivMadicCompletion_of hmA hfinite fR
      simpa [e, fR, mAR, adjoined_completion_generator] using
        congrArg (fun z ↦ AdicCompletion.evalₐ mAR n z) hof
    obtain ⟨a, ha⟩ :=
      baseCompletion_stage_lifts_to_adjoinBase (k := k) (p := p) (f := f)
        (completion_base_series_lift (k := k) (p := p) (f := f)) n
    have hbase_stage :
        AdicCompletion.evalₐ mAR n
            (e (adjoined_completion_base_lift (k := k) (p := p) (f := f))) =
          Ideal.Quotient.mk (mAR ^ n) (algebraMap ↥A ↥R a) := by
      simpa [e, mAR, hfinite, hmA, adjoined_completion_base_lift] using ha
    have hquot :
        Ideal.Quotient.mk (mAR ^ n) fR =
          Ideal.Quotient.mk (mAR ^ n) (algebraMap ↥A ↥R a) := by
      rw [← hgen_stage, hstage, hbase_stage]
    simpa [qf, Q, mAR] using
      quotientClass_mem_pow_smul_of_eq_mod_mapPow
        (A₀ := ↥A) (B₀ := ↥R) (maximalIdeal ↥A) n fR a hquot
  -- The finite quotient `R / A` is Hausdorff for the maximal-ideal topology of `A`.
  letI : Module.Finite ↥A ↥R :=
    finitePthPowerCoefficientAdjoinSubring_moduleFinite k p f
  letI : Module.Finite ↥A (↥R ⧸ Q) := inferInstance
  have hhaus : IsHausdorff (maximalIdeal ↥A) (↥R ⧸ Q) := inferInstance
  have hqf_zero : qf = 0 := by
    exact hhaus.haus qf (fun n ↦ by
      simpa [SModEq.zero] using hmem_all n)
  -- Vanishing of the quotient class means the generator is in the image of `A`.
  have hfR_mem_range : fR ∈ Q := by
    simpa [qf, Q, Submodule.mkQ_apply] using
      ((Submodule.Quotient.mk_eq_zero Q).mp hqf_zero)
  rcases hfR_mem_range with ⟨a, ha⟩
  have hf_eq : f = (a : PowerSeries k) := by
    simpa [fR] using congrArg (fun z : ↥R ↦ (z : PowerSeries k)) ha.symm
  simpa [hf_eq] using a.2

/-- Helper for Example 10.119.5: if `f ∉ A`, then the maximal-ideal completion of `A[f]`
contains a nonzero element whose `p`th power is zero. -/
lemma completion_exists_nonzero_p_nilpotent_of_not_mem
    (hf : f ∉ A) :
    ∃ z : AdicCompletion (maximalIdeal ↥R) ↥R, z ≠ 0 ∧ z ^ p = 0 := by
  let z : RCompletion :=
    adjoined_completion_generator (k := k) (p := p) (f := f) -
      adjoined_completion_base_lift (k := k) (p := p) (f := f)
  refine ⟨z, ?_, ?_⟩
  · -- If the witness vanished, the completed generator would come from the base completion.
    intro hz
    apply hf
    exact completion_generator_eq_baseLift_imp_mem_base (k := k) (p := p) (f := f) <| by
      simpa [z, sub_eq_zero] using hz
  · -- The explicit witness is `p`-nilpotent by the Frobenius computation above.
    simpa [z] using completion_generator_minus_baseLift_pow_eq_zero
      (k := k) (p := p) (f := f)

-- Proof sketch: if `f ∈ A` then `R = A`, whose Krull dimension is `1`; otherwise apply the
-- one-dimensional Krull-Akizuki argument to the overring `R` of the DVR `A`.
/-- The adjoined ring `R = A[f]` has Krull dimension `1`. -/
theorem finitePthPowerCoefficientAdjoinSubring_ringKrullDim_eq_one
    : ringKrullDim ↥R = 1 := by
  -- The finite integral inclusion `A → R` preserves Krull dimension, and `A` is a DVR.
  letI : Module.Finite ↥A ↥R :=
    finitePthPowerCoefficientAdjoinSubring_moduleFinite k p f
  have hInjective : Function.Injective (algebraMap ↥A ↥R) := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ↥R => (z : PowerSeries k)) h
  have hdim :
      ringKrullDim ↥A = ringKrullDim ↥R :=
    ringKrullDim_eq_of_injective_algebraMap_of_isIntegral hInjective
  rw [← hdim]
  exact finitePthPowerCoefficientSubring_ringKrullDim_eq_one k p


end AdjoinedRing
