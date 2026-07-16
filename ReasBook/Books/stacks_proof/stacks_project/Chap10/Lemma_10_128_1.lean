import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_103_1
import stacks_proof.stacks_project.Chap10.Lemma_10_15_2_Prime_avoidance
import stacks_proof.stacks_project.Chap10.Lemma_10_60_13
import stacks_proof.stacks_project.Chap10.Lemma_10_103_7
import stacks_proof.stacks_project.Chap10.Lemma_10_99_4
import stacks_proof.stacks_project.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion
import stacks_proof.stacks_project.Chap10.Lemma_10_100_2
import stacks_proof.stacks_project.Chap10.Lemma_10_103_5
import stacks_proof.stacks_project.Chap10.Lemma_10_103_6
import stacks_proof.stacks_project.Chap10.Lemma_10_104_2
import stacks_proof.stacks_project.Chap10.Lemma_10_106_3
import stacks_proof.stacks_project.Chap10.Lemma_10_106_6
import stacks_proof.stacks_project.Chap10.Lemma_10_106_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory CategoryTheory.Limits IsLocalRing PrimeSpectrum
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R]
variable [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain-style sampling for the miracle-flatness statement:
* primary domain: local commutative algebra of flat local maps from regular local rings with
  Cohen-Macaulay target and a closed-fiber dimension formula;
* sampled owner declarations:
  `Ideal.Fiber`,
  `Module.CohenMacaulay`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `algebraMap_flat_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the closed fiber should live on the canonical owner
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, while the conclusion belongs on the canonical
  flatness owner `(algebraMap R S).Flat`;
* primitive data: the local map `R → S`, regularity of `R`, the explicit owner hypothesis
  `hCM : Module.CohenMacaulay S S`, and the dimension formula for `S` and the canonical closed
  fiber;
* derived API: the quotient presentation
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` of the closed fiber and the flatness
  conclusion for the algebra map.

Source/core/bridge triage:
* `source-facing`: the Stacks miracle-flatness lemma itself;
* `core/canonical`: `Module.CohenMacaulay`, `Ideal.Fiber`, and `(algebraMap R S).Flat`;
* `bridge/view`: the quotient presentation of `ClosedFiber`.
-/

-- Proof sketch: induct on `ringKrullDim R`. For positive dimension, use prime avoidance to choose
-- `x ∈ maximalIdeal R \ maximalIdeal R ^ 2` avoiding the contractions of the minimal primes of
-- `S`; this makes `x` a nonzerodivisor on the Cohen-Macaulay ring `S`. Quotienting by `x` lowers
-- both dimensions by one and preserves regularity of `R / xR` and Cohen-Macaulayness of `S / xS`,
-- so the induction hypothesis gives flatness modulo `x`. Then apply the variant of the local
-- criterion for flatness to lift flatness from the quotient.
/-- Helper for Chap10 Lemma 10 128 1: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] :
    ∃ n : ℕ, ringKrullDim T = n := by
  -- Proof comment: the local Noetherian hypotheses rule out both `⊥` and `⊤`, so the ENat-valued
  -- dimension comes from an actual natural number.
  have hbot : ringKrullDim T ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim T ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim T).unbot hbot).toNat
  have hneTop : (ringKrullDim T).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim T).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim T = (ringKrullDim T).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim T) hbot).symm
    _ = n := hdim'

/-- Helper for Chap10 Lemma 10 128 1: a zero-dimensional regular local ring is a field. -/
lemma regularLocalRing_isField_of_ringKrullDim_eq_zero
    {T : Type*} [CommRing T] [IsRegularLocalRing T]
    (hdim : ringKrullDim T = 0) :
    IsField T := by
  -- Proof comment: regular-locality identifies `dim T` with the span finrank of the maximal
  -- ideal, so the dimension-zero case forces that maximal ideal to vanish.
  have hspan : (maximalIdeal T).spanFinrank = 0 := by
    simpa [hdim] using IsRegularLocalRing.spanFinrank_maximalIdeal (R := T)
  have hfg : (maximalIdeal T).FG := (maximalIdeal T).fg_of_isNoetherianRing
  have hbot : maximalIdeal T = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hspan
  exact (IsLocalRing.isField_iff_maximalIdeal_eq (R := T)).2 hbot

/-- Helper for Chap10 Lemma 10 128 1: Cohen-Macaulayness is unchanged by a linear equivalence of finite
modules over a Noetherian local ring. -/
private theorem Module.CohenMacaulay.of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) [h : Module.CohenMacaulay A M] :
    Module.CohenMacaulay A N := by
  let _ : Module.Finite A N := Module.Finite.equiv e
  -- Proof comment: both support dimension and depth are invariant under linear equivalence, so
  -- the Cohen-Macaulay equality transports verbatim.
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e,
      h.supportDim_eq_moduleDepth]⟩

/-- Helper for Chap10 Lemma 10 128 1: Cohen-Macaulayness of the self-module is transported
across a ring equivalence. -/
private theorem Module.CohenMacaulay.of_ringEquiv_self
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B]
    (e : A ≃+* B) (hA : Module.CohenMacaulay A A) :
    Module.CohenMacaulay B B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  let eAlg : A ≃ₐ[A] B :=
    AlgEquiv.ofRingEquiv (R := A) (f := e) (by intro x; rfl)
  have hAB : Module.CohenMacaulay A B := by
    letI : Module.CohenMacaulay A A := hA
    exact Module.CohenMacaulay.of_linearEquiv eAlg.toLinearEquiv
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := A) (S := B) (N := B) e.surjective).2 hAB

/-- Helper for Chap10 Lemma 10 128 1: scalar-regularity on the regular module of a
commutative ring gives regularity of the underlying ring element. -/
private lemma isRegular_self_of_isSMulRegular
    {A : Type*} [CommRing A] {a : A} (h : IsSMulRegular A a) :
    IsRegular a := by
  -- Proof comment: on the self-module of a commutative ring, scalar multiplication by `a` is
  -- ordinary multiplication by `a`.
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at h
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Chap10 Lemma 10 128 1: a one-step principal quotient of a Cohen-Macaulay local ring is
again Cohen-Macaulay when the quotient dimension drops by exactly one. -/
private lemma principal_quotient_cohenMacaulay_self_of_dimension_drop
    {a : S} (hCM : Module.CohenMacaulay S S)
    [IsLocalRing (S ⧸ Ideal.span ({a} : Set S))]
    [IsNoetherianRing (S ⧸ Ideal.span ({a} : Set S))]
    (hdrop : ringKrullDim (S ⧸ Ideal.span ({a} : Set S)) + 1 = ringKrullDim S) :
    Module.CohenMacaulay (S ⧸ Ideal.span ({a} : Set S)) (S ⧸ Ideal.span ({a} : Set S)) := by
  letI : Module.CohenMacaulay S S := hCM
  have ha_mem : a ∈ maximalIdeal S := by
    -- Proof comment: the quotient is local, hence nontrivial, so the principal ideal is proper
    -- and its generator is a nonunit in the local ring.
    have hproper : Ideal.span ({a} : Set S) ≠ ⊤ :=
      Ideal.Quotient.nontrivial_iff.mp inferInstance
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro ha_unit
    exact hproper (Ideal.span_singleton_eq_top.mpr ha_unit)
  have hreg : RingTheory.Sequence.IsRegular S [a] := by
    -- Proof comment: Lemma 10.104.2 converts the one-step dimension drop into regularity of the
    -- singleton sequence.
    refine
      (isRegular_iff_ringKrullDim_quotient_add_length_eq (R := S) (xs := [a]) ?_).2 ?_
    · intro b hb
      simpa [List.mem_singleton.mp hb] using ha_mem
    · have hOfList :
          Ideal.ofList [a] = Ideal.span ({a} : Set S) := by
        simp
      rw [hOfList]
      exact hdrop
  have hOfList : Ideal.ofList [a] = Ideal.span ({a} : Set S) := by
    simp
  letI : IsLocalRing (S ⧸ Ideal.ofList [a]) := by
    rw [hOfList]
    infer_instance
  letI : IsNoetherianRing (S ⧸ Ideal.ofList [a]) := by
    rw [hOfList]
    infer_instance
  have hCM_ofList :
      Module.CohenMacaulay (S ⧸ Ideal.ofList [a]) (S ⧸ Ideal.ofList [a]) := by
    -- Proof comment: quotienting a Cohen-Macaulay local ring by a regular prefix remains
    -- Cohen-Macaulay.
    simpa using
      (selfModule_cohenMacaulay_quotient_take_of_isRegular
        (R := S) (xs := [a]) hreg (i := 1))
  exact
    Module.CohenMacaulay.of_ringEquiv_self
      (Ideal.quotEquivOfEq hOfList) hCM_ofList

/-- Helper for Chap10 Lemma 10 128 1: every minimal prime of a Cohen-Macaulay local ring has quotient of
full Krull dimension. -/
lemma ringKrullDim_quotient_eq_of_mem_minimalPrimes_of_cohenMacaulay
    (hCM : Module.CohenMacaulay S S) (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    ringKrullDim (S ⧸ q) = ringKrullDim S := by
  letI : Module.CohenMacaulay S S := hCM
  let 𝔮 : PrimeSpectrum S := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
  have hq_ann : q ∈ (Module.annihilator S S).minimalPrimes := by
    -- Proof comment: the self-module `S` has zero annihilator, so minimal primes are exactly the
    -- minimal primes over the annihilator.
    simpa [Module.annihilator_eq_bot.mpr inferInstance] using hq
  have hq_assoc : q ∈ associatedPrimes S S :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes S S hq_ann
  have hdim_support :
      ringKrullDim (S ⧸ 𝔮.asIdeal) = Module.supportDim S S := by
    -- Proof comment: Lemma `10.103.7` identifies associated-prime quotients in a
    -- Cohen-Macaulay ring with the full support dimension.
    exact
      (ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
        (R := S) (M := S) 𝔮 (by simpa [𝔮] using hq_assoc)).1
  simpa [𝔮, Module.supportDim_self_eq_ringKrullDim] using hdim_support

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 128 1: the image of the chosen head element already lies in the closed
fiber ideal, so adjoining its principal ideal does not change that ideal. -/
lemma head_image_sup_closedFiberIdeal_eq_closedFiberIdeal (x : maximalIdeal R) :
    Ideal.span ({algebraMap R S (x : R)} : Set S) ⊔
        Ideal.map (algebraMap R S) (maximalIdeal R) =
      Ideal.map (algebraMap R S) (maximalIdeal R) := by
  -- Proof comment: the generator of the left-hand principal ideal is already an element of the
  -- mapped maximal ideal.
  refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
  rw [Ideal.span_le]
  intro y hy
  rcases Set.mem_singleton_iff.mp hy with rfl
  exact Ideal.mem_map_of_mem (algebraMap R S) x.2

/-- Helper for Chap10 Lemma 10 128 1: the positive-dimensional regular-local source has a maximal-ideal
element whose cotangent class is nonzero, equivalently an element outside `𝔪_R²`. -/
private lemma exists_mem_maximalIdeal_not_mem_sq_of_positive_dimension
    (hRpos : 0 < ringKrullDim R) :
    ∃ x : maximalIdeal R, (x : R) ∉ maximalIdeal R ^ 2 := by
  -- Proof comment: positive regular-local dimension is positive cotangent-space dimension, so a
  -- nonzero cotangent vector lifts to the desired maximal-ideal element.
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hd : ringKrullDim R = d := by
    simpa [d] using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hspan_pos : 0 < d := by
    exact_mod_cast (show (0 : WithBot ℕ∞) < (d : WithBot ℕ∞) by simpa [hd] using hRpos)
  have hcot_pos : 0 < Module.finrank (ResidueField R) (CotangentSpace R) := by
    simpa [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R), d] using hspan_pos
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hcot_pos
  obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
  refine ⟨x, ?_⟩
  intro hx_sq
  exact hv <| ((maximalIdeal R).toCotangent_eq_zero x).2 hx_sq

/-- Helper for Chap10 Lemma 10 128 1: a minimal prime of `S` cannot lie over `maximalIdeal R` under the
dimension formula of the miracle-flatness hypothesis. -/
private lemma minimalPrime_contraction_ne_maximal_of_dimension_formula
    (hCM : Module.CohenMacaulay S S) (hRpos : 0 < ringKrullDim R)
    (hdim : ringKrullDim S = ringKrullDim R + ringKrullDim ClosedFiber)
    {q : Ideal S} (hq : q ∈ minimalPrimes S) :
    Ideal.comap (algebraMap R S) q ≠ maximalIdeal R := by
  -- Proof comment: if `q` lay over `maximalIdeal R`, then the closed-fiber quotient would
  -- surject onto `S / q`, forcing `dim(S / q) ≤ dim ClosedFiber`, which contradicts the
  -- dimension formula because `dim(S / q) = dim S`.
  intro hcomap
  let 𝔪S : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  have h𝔪S_le_max : 𝔪S ≤ maximalIdeal S := IsLocalRing.map_maximalIdeal_le (algebraMap R S)
  have h𝔪S_ne_top : 𝔪S ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top h𝔪S_le_max
  letI : Nontrivial (S ⧸ 𝔪S) := Ideal.Quotient.nontrivial_iff.mpr h𝔪S_ne_top
  letI : IsLocalRing (S ⧸ 𝔪S) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔪S) Ideal.Quotient.mk_surjective
  have h𝔪S_le_q : 𝔪S ≤ q := by
    exact (Ideal.map_le_iff_le_comap).2 <| by simpa [𝔪S, hcomap]
  have hfiber_eq :
      ringKrullDim (S ⧸ 𝔪S) = ringKrullDim ClosedFiber := by
    exact ringKrullDim_eq_of_ringEquiv
      (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv
  have hquot_le :
      ringKrullDim (S ⧸ q) ≤ ringKrullDim ClosedFiber := by
    calc
      ringKrullDim (S ⧸ q) ≤ ringKrullDim (S ⧸ 𝔪S) := by
        exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor h𝔪S_le_q)
          (Ideal.Quotient.factor_surjective h𝔪S_le_q)
      _ = ringKrullDim ClosedFiber := hfiber_eq
  have hq_dim : ringKrullDim (S ⧸ q) = ringKrullDim S :=
    ringKrullDim_quotient_eq_of_mem_minimalPrimes_of_cohenMacaulay (S := S) hCM q hq
  obtain ⟨dR, hdR⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (T := R)
  obtain ⟨e, he⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (T := S ⧸ 𝔪S)
  have hdR_pos : 0 < dR := by
    exact_mod_cast (show (0 : WithBot ℕ∞) < (dR : WithBot ℕ∞) by simpa [hdR] using hRpos)
  have hsum_le : ringKrullDim R + ringKrullDim ClosedFiber ≤ ringKrullDim ClosedFiber := by
    calc
      ringKrullDim R + ringKrullDim ClosedFiber = ringKrullDim S := hdim.symm
      _ = ringKrullDim (S ⧸ q) := hq_dim.symm
      _ ≤ ringKrullDim ClosedFiber := hquot_le
  have hfiber_nat : ringKrullDim ClosedFiber = e := by
    calc
      ringKrullDim ClosedFiber = ringKrullDim (S ⧸ 𝔪S) := hfiber_eq.symm
      _ = e := he
  have hsum_nat : dR + e ≤ e := by
    exact_mod_cast (show ((dR + e : ℕ) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) by
      simpa [hdR, hfiber_nat] using hsum_le)
  omega

/-- Helper for Chap10 Lemma 10 128 1: prime avoidance chooses a head element in `maximalIdeal R`
outside `𝔪_R²` and outside the contractions of every minimal prime of `S`. -/
private lemma exists_head_element_not_mem_sq_avoiding_minimalPrimes
    (hCM : Module.CohenMacaulay S S) (hRpos : 0 < ringKrullDim R)
    (hdim : ringKrullDim S = ringKrullDim R + ringKrullDim ClosedFiber) :
    ∃ x : maximalIdeal R,
      (x : R) ∉ maximalIdeal R ^ 2 ∧
        ∀ q ∈ minimalPrimes S, algebraMap R S (x : R) ∉ q := by
  let comapMin : Set (Ideal R) := Ideal.comap (algebraMap R S) '' minimalPrimes S
  let s : Set (Ideal R) := insert (maximalIdeal R ^ 2) comapMin
  have hsfinite : s.Finite := by
    exact (minimalPrimes.finite_of_isNoetherianRing S).image _ |>.insert _
  have hnot_subset : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ I ∈ s, (I : Set R)) := by
    intro hsubset
    obtain ⟨I, hIs, hmax_le_I⟩ :=
      ((maximalIdeal R).subset_union_prime_finite hsfinite (f := id)
        (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
        (fun I hI _ _ ↦ by
          rcases Set.mem_insert_iff.mp hI with rfl | hI'
          · exfalso
            contradiction
          · rcases hI' with ⟨q, hq, rfl⟩
            letI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
            exact Ideal.comap_isPrime (algebraMap R S) q)).1 hsubset
    rcases Set.mem_insert_iff.mp hIs with hI_sq | hI_comap
    · obtain ⟨x, hx_not_mem_sq⟩ :=
        exists_mem_maximalIdeal_not_mem_sq_of_positive_dimension (R := R) hRpos
      exact hx_not_mem_sq <| by simpa [hI_sq] using hmax_le_I x.2
    · rcases hI_comap with ⟨q, hq, rfl⟩
      letI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
      have hcontra :
          Ideal.comap (algebraMap R S) q = maximalIdeal R := by
        refine le_antisymm ?_ hmax_le_I
        exact le_maximalIdeal Ideal.IsPrime.ne_top'
      exact
        minimalPrime_contraction_ne_maximal_of_dimension_formula
          (R := R) (S := S) hCM hRpos hdim hq hcontra
  obtain ⟨x, hx_mem, hx_avoid⟩ := Set.not_subset.mp hnot_subset
  refine ⟨⟨x, hx_mem⟩, ?_, ?_⟩
  · -- Proof comment: if `x` landed in `𝔪_R²`, it would lie in the avoided union through the
    -- distinguished non-prime member of the finite family.
    intro hx_sq
    exact hx_avoid <| Set.mem_iUnion.2 ⟨maximalIdeal R ^ 2, Set.mem_iUnion.2 ⟨by simp [s], hx_sq⟩⟩
  · -- Proof comment: membership of `algebraMap x` in a minimal prime would place `x` inside the
    -- corresponding contracted prime from the avoided family.
    intro q hq hqx
    exact hx_avoid <| Set.mem_iUnion.2
      ⟨Ideal.comap (algebraMap R S) q, Set.mem_iUnion.2 ⟨by
          right
          exact ⟨q, hq, rfl⟩, hqx⟩⟩

/-- Helper for Chap10 Lemma 10 128 1: quotienting the regular local source by the chosen head element
preserves regular-locality and drops the Krull dimension by exactly one. -/
private lemma head_quotient_regularLocalRing_and_dimension_drop_of_not_mem_sq
    (x : maximalIdeal R) (hx : (x : R) ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({(x : R)} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({(x : R)} : Set R)) + 1 = ringKrullDim R := by
  let d : ℕ := (maximalIdeal R).spanFinrank - 1
  obtain ⟨y, hy⟩ :=
    Ring.DirectLimit.prescribed_head_parameterIdeal_eq_maximalIdeal_of_not_mem_sq
      (A := R) x hx
  have hpos : 0 < (maximalIdeal R).spanFinrank := by
    exact Ring.DirectLimit.spanFinrank_pos_of_not_mem_sq (A := R) (x := x) hx
  let xs : Fin (d + 1) → maximalIdeal R := Fin.cons x y
  have hxs_parameter : parameterIdeal xs = maximalIdeal R := by
    -- Proof comment: rewrite the prescribed-head generating family from the append presentation to
    -- the canonical `Fin.cons` presentation expected by the quotient API.
    calc
      parameterIdeal xs = parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) y) := by
        symm
        simpa [xs] using Ring.DirectLimit.parameterIdeal_append_eq_cons (A := R) x y
      _ = maximalIdeal R := hy
  have hdim : ringKrullDim R = d + 1 := by
    -- Proof comment: the chosen head element has nonzero cotangent class, so the regular-local
    -- dimension is a positive successor matching the head-plus-tail parameter family.
    have hd_nat : (maximalIdeal R).spanFinrank = d + 1 := by
      simpa [d, Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.succ_pred_eq_of_pos hpos).symm
    calc
      ringKrullDim R = ((maximalIdeal R).spanFinrank : ℕ∞) := by
        simpa using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
      _ = ((d + 1 : ℕ) : ℕ∞) := by
        exact congrArg (fun n : ℕ ↦ (((n : ℕ∞) : WithBot ℕ∞))) hd_nat
  have hxs : IsRegularSystemOfParameters xs := by
    -- Proof comment: once the completed family generates the maximal ideal, the regular-local
    -- dimension equality upgrades it to a regular system of parameters.
    exact
      (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := R) hdim xs).2 hxs_parameter
  have hquot :
      IsRegularLocalRing (R ⧸ Ideal.span ({((xs 0 : maximalIdeal R) : R)} : Set R)) ∧
        ringKrullDim (R ⧸ Ideal.span ({((xs 0 : maximalIdeal R) : R)} : Set R)) = d := by
    -- Proof comment: this is exactly the one-head quotient step for a regular system of
    -- parameters, specialized to the family whose head is the chosen element `x`.
    simpa [xs] using head_parameter_quotient_regular_local_and_dim (R := R) (x := xs) hxs
  refine ⟨hquot.1, ?_⟩
  -- Proof comment: rewrite the quotient dimension `= d` as the additive drop-by-one statement.
  calc
    ringKrullDim (R ⧸ Ideal.span ({(x : R)} : Set R)) + 1 = d + 1 := by
      simpa [xs] using congrArg (fun t : WithBot ℕ∞ ↦ t + 1) hquot.2
    _ = ringKrullDim R := hdim.symm

/-- Helper for Chap10 Lemma 10 128 1: an element of `maximalIdeal R \ maximalIdeal R²` is a regular
element of the regular local ring `R`. -/
private lemma head_isRegular_of_not_mem_sq
    (x : maximalIdeal R) (hx : (x : R) ∉ maximalIdeal R ^ 2) :
    IsRegular (x : R) := by
  -- Proof comment: the already proved head-quotient dimension drop is exactly the singleton
  -- regular-sequence criterion in the Cohen-Macaulay regular-local source.
  letI : Module.CohenMacaulay R R := inferInstance
  have hdrop :
      ringKrullDim (R ⧸ Ideal.span ({(x : R)} : Set R)) + 1 = ringKrullDim R :=
    (head_quotient_regularLocalRing_and_dimension_drop_of_not_mem_sq
      (R := R) x hx).2
  have hregList : RingTheory.Sequence.IsRegular R [(x : R)] := by
    refine
      (isRegular_iff_ringKrullDim_quotient_add_length_eq
        (R := R) (xs := [(x : R)]) ?_).2 ?_
    · intro y hy
      simpa [List.mem_singleton.mp hy] using x.2
    · have hOfList :
          Ideal.ofList [(x : R)] = Ideal.span ({(x : R)} : Set R) := by
        simp
      rw [hOfList]
      exact hdrop
  have hsmul : IsSMulRegular R (x : R) := by
    -- Proof comment: a regular singleton is precisely injectivity of multiplication by its head.
    simpa using ((RingTheory.Sequence.isRegular_cons_iff (M := R) (x : R) []).1 hregList).1
  exact isRegular_self_of_isSMulRegular hsmul

omit [IsNoetherianRing S] in
/-- Helper for Chap10 Lemma 10 128 1: killing the chosen head element on both source and target leaves
the closed fiber with the same Krull dimension. -/
private lemma closedFiber_dimension_eq_after_head_quotient (x : maximalIdeal R)
    :
    let I : Ideal R := Ideal.span ({(x : R)} : Set R)
    let J : Ideal S := Ideal.span ({algebraMap R S (x : R)} : Set S)
    let R' : Type u := R ⧸ I
    let S' : Type v := S ⧸ J
    let hI_ne_top : I ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top <|
        by
          simpa [I] using
            (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := (x : R))).2 x.2
    letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
    letI : IsLocalRing R' :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let 𝔪S : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
    let hJ_le_closedFiberIdeal : J ≤ 𝔪S :=
      by
        simpa [J] using
          (Ideal.span_singleton_le_iff_mem (I := 𝔪S)
            (x := algebraMap R S (x : R))).2
            (Ideal.mem_map_of_mem (algebraMap R S) x.2)
    let hJ_ne_top : J ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top <|
        hJ_le_closedFiberIdeal.trans (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
    letI : Nontrivial S' := Ideal.Quotient.nontrivial_iff.mpr hJ_ne_top
    letI : IsLocalRing S' :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let hI_le_comap_J : I ≤ Ideal.comap (algebraMap R S) J :=
      by
        simpa [I, J] using
          (Ideal.span_singleton_le_iff_mem (I := Ideal.comap (algebraMap R S) J)
            (x := (x : R))).2
            (Ideal.subset_span (by simp))
    letI : Algebra R' S' :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (R := R) (A := S) (p := I) (P := J) hI_le_comap_J
    ringKrullDim
        (Ideal.Fiber
          (maximalIdeal (R ⧸ Ideal.span ({(x : R)} : Set R)))
          (S ⧸ Ideal.span ({algebraMap R S (x : R)} : Set S))) =
      ringKrullDim ClosedFiber := by
  dsimp
  let I : Ideal R := Ideal.span ({(x : R)} : Set R)
  let J : Ideal S := Ideal.span ({algebraMap R S (x : R)} : Set S)
  let R' : Type u := R ⧸ I
  let S' : Type v := S ⧸ J
  let 𝔪S : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  have hI_le : I ≤ maximalIdeal R := by
    simpa [I] using
      (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := (x : R))).2 x.2
  have hI_ne_top : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI_le
  letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  letI : IsLocalRing R' :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hJ_le_closedFiberIdeal : J ≤ 𝔪S := by
    simpa [J] using
      (Ideal.span_singleton_le_iff_mem (I := 𝔪S)
        (x := algebraMap R S (x : R))).2
        (Ideal.mem_map_of_mem (algebraMap R S) x.2)
  have hJ_le_max : J ≤ maximalIdeal S := by
    exact hJ_le_closedFiberIdeal.trans (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  have hJ_ne_top : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hJ_le_max
  letI : Nontrivial S' := Ideal.Quotient.nontrivial_iff.mpr hJ_ne_top
  letI : IsLocalRing S' :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hI_le_comap_J : I ≤ Ideal.comap (algebraMap R S) J := by
    simpa [I, J] using
      (Ideal.span_singleton_le_iff_mem (I := Ideal.comap (algebraMap R S) J)
        (x := (x : R))).2
        (Ideal.subset_span (by simp))
  letI : Algebra R' S' :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) hI_le_comap_J
  have hmap_maximalIdeal_source :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal R' := by
    -- Proof comment: quotienting a local ring by a proper ideal carries the maximal ideal to the
    -- maximal ideal of the quotient.
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap_closedFiberIdeal :
      Ideal.map (algebraMap R' S') (maximalIdeal R') =
        Ideal.map (Ideal.Quotient.mk J) 𝔪S := by
    -- Proof comment: for the canonical quotient algebra, the new closed-fiber ideal is simply the
    -- image of the old one under the target quotient map.
    calc
      Ideal.map (algebraMap R' S') (maximalIdeal R') =
          Ideal.map (algebraMap R' S')
            (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) := by
              rw [hmap_maximalIdeal_source.symm]
      _ = Ideal.map ((algebraMap R' S').comp (Ideal.Quotient.mk I)) (maximalIdeal R) := by
            rw [Ideal.map_map]
      _ = Ideal.map ((Ideal.Quotient.mk J).comp (algebraMap R S)) (maximalIdeal R) := by
            ext r
            rfl
      _ = Ideal.map (Ideal.Quotient.mk J) 𝔪S := by
            rw [Ideal.map_map]
  have hclosedFiberQuot :
      ringKrullDim
          (Ideal.Fiber (maximalIdeal R') S') =
        ringKrullDim
          (S' ⧸ Ideal.map (algebraMap R' S') (maximalIdeal R')) := by
    -- Proof comment: compare the quotient presentation of the quotient closed fiber to the fiber
    -- owner using the canonical quotient equivalence.
    exact
      (ringKrullDim_eq_of_ringEquiv
        (closedFiber_quotient_equiv (R := R') (S := S')).toRingEquiv).symm
  have hdoubleQuot :
      ringKrullDim
          (S' ⧸ Ideal.map (algebraMap R' S') (maximalIdeal R')) =
        ringKrullDim (S ⧸ 𝔪S) := by
    -- Route correction: keep the transport on the quotient side canonical by first rewriting the
    -- quotient closed-fiber ideal, then collapsing the double quotient with `J ≤ 𝔪S`.
    exact
      ringKrullDim_eq_of_ringEquiv <|
        (Ideal.quotEquivOfEq (R := S') hmap_closedFiberIdeal).trans
          (DoubleQuot.quotQuotEquivQuotOfLE hJ_le_closedFiberIdeal)
  have hclosedFiber :
      ringKrullDim (S ⧸ 𝔪S) = ringKrullDim ClosedFiber := by
    -- Proof comment: the original closed fiber is already identified with `S / 𝔪_RS`.
    exact ringKrullDim_eq_of_ringEquiv
      (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv
  calc
    ringKrullDim
        (Ideal.Fiber
          (maximalIdeal (R ⧸ Ideal.span ({(x : R)} : Set R)))
          (S ⧸ Ideal.span ({algebraMap R S (x : R)} : Set S))) =
      ringKrullDim
        (Ideal.Fiber (maximalIdeal R') S') := by
          rfl
    _ =
      ringKrullDim
        (S' ⧸ Ideal.map (algebraMap R' S') (maximalIdeal R')) := hclosedFiberQuot
    _ = ringKrullDim (S ⧸ 𝔪S) := hdoubleQuot
    _ = ringKrullDim ClosedFiber := hclosedFiber

/-- Helper for Chap10 Lemma 10 128 1: if the chosen head element avoids every minimal prime of `S`, then
its image is a nonzerodivisor on `S` and quotienting the target by that element drops the Krull
dimension by one. -/
private lemma target_head_regular_and_dimension_drop_of_avoids_minimalPrimes
    (hCM : Module.CohenMacaulay S S) (x : maximalIdeal R)
    (hx_avoid : ∀ q ∈ minimalPrimes S, algebraMap R S (x : R) ∉ q) :
    let a : S := algebraMap R S (x : R)
    IsSMulRegular S a ∧
      ringKrullDim (S ⧸ Ideal.span ({a} : Set S)) + 1 = ringKrullDim S := by
  dsimp
  let a : S := algebraMap R S (x : R)
  have ha_mem : a ∈ maximalIdeal S := by
    -- Proof comment: the chosen source head already lies in the target maximal ideal because the
    -- algebra map is local.
    exact
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S)) <|
        by simpa [a] using Ideal.mem_map_of_mem (algebraMap R S) x.2
  let _ : Module.CohenMacaulay S S := hCM
  have hdim_drop : ringKrullDim S = ringKrullDim (S ⧸ Ideal.span ({a} : Set S)) + 1 := by
    -- Proof comment: avoiding all minimal primes is exactly the textbook hypothesis forcing a
    -- one-step dimension drop on the target quotient.
    simpa [a] using
      ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
        (R := S) a ha_mem hx_avoid
  have hreg_list : RingTheory.Sequence.IsRegular S [a] := by
    -- Proof comment: in the Cohen-Macaulay target, the one-step dimension drop is exactly the
    -- singleton regular-sequence criterion from Lemma `10.104.2`.
    refine
      (isRegular_iff_ringKrullDim_quotient_add_length_eq (R := S) (xs := [a]) ?_).2 ?_
    · intro b hb
      simpa [List.mem_singleton.mp hb] using ha_mem
    · have hOfList : Ideal.ofList [a] = Ideal.span ({a} : Set S) := by
        simpa using
          (Submodule.ideal_span_singleton_smul
            (R := S) (M := S) a (⊤ : Submodule S S)).symm
      rw [hOfList]
      simpa using hdim_drop.symm
  have hreg : IsSMulRegular S a := by
    -- Proof comment: a regular singleton records exactly that its head acts injectively on the
    -- ring viewed as a module over itself.
    simpa using ((RingTheory.Sequence.isRegular_cons_iff (M := S) a []).1 hreg_list).1
  exact ⟨hreg, hdim_drop.symm⟩

/-- Helper for Chap10 Lemma 10 128 1: ordinary regularity of a ring element gives
scalar-regularity on the regular module. -/
private lemma isSMulRegular_self_of_isRegular
    {A : Type u} [CommRing A] {a : A} (h : IsRegular a) :
    IsSMulRegular A a := by
  -- Proof comment: on the self-module, scalar multiplication by `a` is ordinary multiplication.
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left] at h
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Chap10 Lemma 10 128 1: quotienting a lifted module by `J • ⊤` is canonically the
same as quotienting the original module by `J • ⊤`. -/
private lemma ulift_module_quotient_equiv_exists
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N] :
    Nonempty ((((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))))) := by
  let eA :
      ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A]
        (N ⧸ (J • (⊤ : Submodule A N))) :=
    Submodule.Quotient.equiv
      (J • (⊤ : Submodule A (ULift.{u} N)))
      (J • (⊤ : Submodule A N))
      (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
      (by
        -- Proof comment: `ULift.moduleEquiv` preserves the quotient denominator `J • ⊤`.
        simpa [Submodule.map_smul''])
  -- Proof comment: both quotient modules carry the canonical `A ⧸ J`-action.
  exact ⟨eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Chap10 Lemma 10 128 1: choose the quotient-module equivalence induced by
`ULift.moduleEquiv`. -/
private noncomputable def ulift_module_quotient_equiv
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N] :
    ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
  Classical.choice ulift_module_quotient_equiv_exists

/-- Helper for Chap10 Lemma 10 128 1: regularity of `f` on both the source ring and a
same-universe module forces the principal quotient `Tor₁` to vanish. -/
private lemma tor_one_module_quotient_by_regular_element_vanishes
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A))))) := by
  let _ := hfM
  let I : Ideal A := Ideal.span ({f} : Set A)
  let φ : A →ₗ[A] I :=
    { toFun := fun a ↦ ⟨a * f, (Ideal.mem_span_singleton').2 ⟨a, rfl⟩⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simpa [add_mul]
      map_smul' := by
        intro a b
        apply Subtype.ext
        simp [mul_left_comm, mul_comm] }
  let hspan : A ≃ₗ[A] I := by
    -- Proof comment: multiplication by `f` identifies `A` with `(f)`, using regularity for
    -- injectivity and the principal-span characterization for surjectivity.
    refine LinearEquiv.ofBijective φ ?_
    constructor
    · intro a b hab
      apply Subtype.ext_iff.mp at hab
      exact hfA.right hab
    · intro x
      rcases (Ideal.mem_span_singleton').1 x.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext_iff.mpr
      simpa [φ] using ha
  let μ : I ⊗[A] M →ₗ[A] M :=
    TensorProduct.lift ((LinearMap.lsmul A M).comp I.subtype)
  let e : I ⊗[A] M ≃ₗ[A] A ⊗[A] M :=
    TensorProduct.congr hspan.symm (LinearEquiv.refl A M)
  have hμ :
      μ =
        (LinearMap.lsmul A M f).comp
          ((TensorProduct.lid A M).toLinearMap.comp e.toLinearMap) := by
    -- Proof comment: after identifying `(f)` with `A`, the tensor multiplication map is
    -- multiplication by `f` on `M`.
    ext a m
    change a.1 • m = f • ((hspan.symm a : A) • m)
    rw [← mul_smul]
    have ha : (hspan.symm a : A) * f = a.1 := by
      exact congrArg Subtype.val (hspan.apply_symm_apply a)
    calc
      a.1 • m = ((hspan.symm a : A) * f) • m := by simpa [ha]
      _ = (f * hspan.symm a) • m := by rw [mul_comm]
  have hμ_injective : Function.Injective μ := by
    rw [hμ]
    exact hfM.comp ((TensorProduct.lid A M).injective.comp e.injective)
  have hker : LinearMap.ker μ = ⊥ := by
    exact LinearMap.ker_eq_bot.mpr hμ_injective
  -- Proof comment: the principal-ideal kernel now vanishes, so the imported kernel-to-Tor bridge
  -- kills the quotient `Tor₁` owner.
  simpa [I] using
    tor_one_module_quotient_vanishes_of_ker_eq_bot (A := A) (I := I) (N := M) hker

/-- Helper for Chap10 Lemma 10 128 1: quotienting by the image ideal in a `ULift` ring recovers
the original quotient ring. -/
private lemma ulift_quotient_ring_equiv_aux
    {A : Type u} [CommRing A] (K : Ideal A) :
    K =
      (K.map (algebraMap A (ULift.{v} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{v} A ≃ₐ[A] A) : ULift.{v} A →+* A) := by
  let eu : ULift.{v} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  -- Proof comment: the `ULift` algebra equivalence is inverse to the canonical lift.
  calc
    K = K.map (RingHom.id A) := by simp
    _ = K.map ((eu : ULift.{v} A →+* A).comp (algebraMap A (ULift.{v} A))) := by
          ext a
          rfl
    _ = (K.map (algebraMap A (ULift.{v} A))).map (eu : ULift.{v} A →+* A) := by
          rw [Ideal.map_map]

/-- Helper for Chap10 Lemma 10 128 1: the canonical `ULift` presentation of a quotient ring is
ring-equivalent to the original quotient ring. -/
private noncomputable def ulift_quotient_ring_equiv
    {A : Type u} [CommRing A] (K : Ideal A) :
    ((ULift.{v} A) ⧸ K.map (algebraMap A (ULift.{v} A))) ≃+* (A ⧸ K) :=
  (Ideal.quotientEquivAlg _ _ (ULift.algEquiv (R := A) (A := A))
    (ulift_quotient_ring_equiv_aux (A := A) K)).toRingEquiv

/-- Helper for Chap10 Lemma 10 128 1: the `ULift` of a local homomorphism is again local. -/
private lemma ringHom_ulift_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (g : A →+* B) [IsLocalHom g] :
    IsLocalHom (RingHom.ulift g) := by
  letI : IsLocalRing (ULift A) :=
    by
      exact IsLocalRing.of_surjective'
        (ULift.ringEquiv.symm.toRingHom : A →+* ULift A)
        (by
          intro x
          exact ⟨ULift.down x, by cases x; rfl⟩)
  letI : IsLocalRing (ULift B) :=
    by
      exact IsLocalRing.of_surjective'
        (ULift.ringEquiv.symm.toRingHom : B →+* ULift B)
        (by
          intro x
          exact ⟨ULift.down x, by cases x; rfl⟩)
  letI : IsLocalHom (ULift.ringEquiv.toRingHom : ULift A →+* A) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.surjective
  letI : IsLocalHom (ULift.ringEquiv.symm.toRingHom : B →+* ULift B) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.symm.surjective
  -- Proof comment: the lifted map is the original local map conjugated by the two canonical
  -- `ULift` ring equivalences.
  simpa [RingHom.ulift] using
    (RingHom.isLocalHom_comp (ULift.ringEquiv.symm.toRingHom)
      (g.comp ULift.ringEquiv.toRingHom))

/-- Helper for Chap10 Lemma 10 128 1: a principal-quotient flatness step can be checked after
lifting the source ring and target ring to a common universe. -/
private lemma flat_of_regular_element_and_flat_mod_ideal_self_univ
    (f : R) (hI : Ideal.span ({f} : Set R) ≠ ⊤)
    (hf_source : IsRegular f) (hf_target : IsSMulRegular S f)
    (hflat :
      Module.Flat (R ⧸ Ideal.span ({f} : Set R))
        (S ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R S)))) :
    Module.Flat R S := by
  let I : Ideal R := Ideal.span ({f} : Set R)
  let Ru : Type max u v := ULift.{v} R
  let Su : Type max u v := ULift.{u} S
  let fu : Ru := algebraMap R Ru f
  let Iu : Ideal Ru := Ideal.map (algebraMap R Ru) I
  let Tu : Type max u v := Ru ⧸ Iu
  let B : Type u := R ⧸ I
  let eRing : Tu ≃+* B := ulift_quotient_ring_equiv (A := R) I
  let _ : Algebra R Su := ULift.algebra
  let _ : Algebra Ru Su := ULift.algebra' R Su
  letI : IsRegularLocalRing Ru := by
    exact IsRegularLocalRing.of_ringEquiv (R := R) (ULift.ringEquiv : Ru ≃+* R).symm
  letI : IsLocalRing Su := by
    exact IsLocalRing.of_surjective'
      (ULift.ringEquiv.symm.toRingHom : S →+* Su)
      (by
        intro x
        exact ⟨ULift.down x, by cases x; rfl⟩)
  letI : IsNoetherianRing Ru := by
    exact isNoetherianRing_of_ringEquiv R (ULift.ringEquiv : Ru ≃+* R).symm
  letI : IsNoetherianRing Su := by
    exact isNoetherianRing_of_ringEquiv S (ULift.ringEquiv : Su ≃+* S).symm
  letI : IsLocalHom (algebraMap Ru Su) := by
    simpa [Ru, Su] using ringHom_ulift_isLocalHom (g := algebraMap R S)
  have hIu : Iu ≠ ⊤ := by
    let _ : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hI
    let _ : Nontrivial Tu := eRing.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp inferInstance
  letI : Algebra Ru R := (ULift.ringEquiv : Ru ≃+* R).toRingHom.toAlgebra
  letI : Module Ru S := Module.compHom S (algebraMap Ru R)
  have hf_source_Ru_on_R : IsSMulRegular R fu := by
    -- Proof comment: via the canonical map `Ru → R`, the lifted source element acts as `f`.
    simpa [fu] using isSMulRegular_self_of_isRegular (A := R) hf_source
  have hf_source_Ru : IsSMulRegular Ru fu := by
    let eRu : Ru ≃ₗ[Ru] R := ULift.moduleEquiv
    exact (LinearEquiv.isSMulRegular_congr eRu fu).2 hf_source_Ru_on_R
  have hfRu : IsRegular fu := isRegular_self_of_isSMulRegular hf_source_Ru
  have hf_target_Ru_on_S : IsSMulRegular S fu := by
    -- Proof comment: after restricting scalars along `Ru → R`, the lifted source element still
    -- acts as the original `f` on `S`.
    simpa [fu] using hf_target
  have hfSu : IsSMulRegular Su fu := by
    let eSu : Su ≃ₗ[Ru] S := ULift.moduleEquiv
    exact (LinearEquiv.isSMulRegular_congr eSu fu).2 hf_target_Ru_on_S
  have hIu_eq : Iu = Ideal.span ({fu} : Set Ru) := by
    simpa [Iu, I, fu, Ideal.map_span, Set.image_singleton]
  have hTor_u :
      IsZero (Tor₁[Ru](Su, Ru ⧸ Iu)) := by
    -- Proof comment: in the common-universe model, same-universe principal quotient vanishing
    -- applies directly.
    rw [hIu_eq]
    exact
      tor_one_module_quotient_by_regular_element_vanishes
        (A := Ru) (M := Su) fu hfRu hfSu
  letI : Algebra Tu B := eRing.toRingHom.toAlgebra
  letI : Module Tu (S ⧸ (I • (⊤ : Submodule R S))) :=
    Module.compHom (S ⧸ (I • (⊤ : Submodule R S))) (algebraMap Tu B)
  letI : IsScalarTower R Tu (S ⧸ (I • (⊤ : Submodule R S))) :=
    IsScalarTower.of_compHom R Tu (S ⧸ (I • (⊤ : Submodule R S)))
  letI : IsScalarTower Tu B (S ⧸ (I • (⊤ : Submodule R S))) :=
    IsScalarTower.of_compHom Tu B (S ⧸ (I • (⊤ : Submodule R S)))
  have hIu_restrict :
      ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R) =
        (I • (⊤ : Submodule R Su)) := by
    -- Proof comment: restricting the lifted denominator from `Ru` back to `R` recovers the
    -- original denominator generated by `f`.
    simpa [Iu] using
      (Ideal.smul_restrictScalars
        (R := R) (S := Ru) (M := Su) (I := I) (N := (⊤ : Submodule Ru Su)))
  have hsurjRT : Function.Surjective (algebraMap R Tu) := by
    -- Proof comment: every quotient class upstairs has a representative coming from `R`.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rcases x with ⟨x⟩
    exact ⟨x, rfl⟩
  have eOwnerA :
      (Su ⧸ (Iu • (⊤ : Submodule Ru Su))) ≃ₗ[R]
        S ⧸ (I • (⊤ : Submodule R S)) := by
    let eRestrict :
        (Su ⧸ ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R)) ≃ₗ[R]
          Su ⧸ (Iu • (⊤ : Submodule Ru Su)) :=
      Submodule.Quotient.restrictScalarsEquiv R (Iu • (⊤ : Submodule Ru Su))
    let eDenom :
        (Su ⧸ ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R)) ≃ₗ[R]
          Su ⧸ (I • (⊤ : Submodule R Su)) :=
      Submodule.quotEquivOfEq
        ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R)
        (I • (⊤ : Submodule R Su))
        hIu_restrict
    let eULift :
        (Su ⧸ (I • (⊤ : Submodule R Su))) ≃ₗ[R]
          S ⧸ (I • (⊤ : Submodule R S)) :=
      (ulift_module_quotient_equiv (A := R) (J := I) (N := S)).restrictScalars R
    -- Proof comment: compare the lifted quotient to the original one by restricting scalars,
    -- normalizing the denominator, and removing the `ULift`.
    exact eRestrict.symm.trans (eDenom.trans eULift)
  let eOwner :
      (Su ⧸ (Iu • (⊤ : Submodule Ru Su))) ≃ₗ[Tu]
        S ⧸ (I • (⊤ : Submodule R S)) :=
    eOwnerA.extendScalarsOfSurjective hsurjRT
  have hflatTB : Module.Flat Tu B := by
    let eAlg : B ≃ₐ[Tu] Tu :=
      AlgEquiv.ofRingEquiv (R := Tu) (f := eRing.symm) (by
        intro x
        change eRing.symm (eRing x) = x
        exact eRing.symm_apply_apply x)
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatTarget : Module.Flat Tu (S ⧸ (I • (⊤ : Submodule R S))) := by
    letI : Module.Flat Tu B := hflatTB
    letI : Module.Flat B (S ⧸ (I • (⊤ : Submodule R S))) := hflat
    exact Module.Flat.trans Tu B (S ⧸ (I • (⊤ : Submodule R S)))
  have hflat_uquot :
      Module.Flat Tu (Su ⧸ (Iu • (⊤ : Submodule Ru Su))) := by
    letI : Module.Flat Tu (S ⧸ (I • (⊤ : Submodule R S))) := hflatTarget
    exact Module.Flat.of_linearEquiv eOwner
  have hflatRuSu : Module.Flat Ru Su := by
    -- Proof comment: all lifted hypotheses now match the exact common-universe owner expected by
    -- the imported variant local criterion.
    exact
      flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
        (R := Ru) (S := Su) (M := Su) Iu hIu hTor_u hflat_uquot
  have hflatRSu : Module.Flat R Su := by
    have hflatRRu : Module.Flat R Ru := by
      exact Module.Flat.of_linearEquiv (ULift.algEquiv (R := R) (A := R)).toLinearEquiv
    letI : Module.Flat R Ru := hflatRRu
    letI : Module.Flat Ru Su := hflatRuSu
    exact Module.Flat.trans R Ru Su
  letI : Module.Flat R Su := hflatRSu
  -- Proof comment: remove the remaining `ULift` on the target module.
  exact Module.Flat.of_linearEquiv (ULift.moduleEquiv (R := R) (M := S)).symm

/-- Chap10 Lemma 10 128 1: flatness of the head quotient, together with regularity of the head
element on both source and target, lifts to flatness of the original local map. -/
private lemma flat_of_head_quotient_flat_of_regular_pair
    (x : maximalIdeal R) (hsource : IsRegular (x : R))
    (htarget : IsSMulRegular S (x : R)) :
    let I : Ideal R := Ideal.span ({(x : R)} : Set R)
    let J : Ideal S := Ideal.span ({algebraMap R S (x : R)} : Set S)
    let R' : Type u := R ⧸ I
    let S' : Type v := S ⧸ J
    let hI_ne_top : I ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top <|
        by
          simpa [I] using
            (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := (x : R))).2 x.2
    letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
    letI : IsLocalRing R' :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let hJ_le_closedFiberIdeal : J ≤ Ideal.map (algebraMap R S) (maximalIdeal R) :=
      by
        simpa [J] using
          (Ideal.span_singleton_le_iff_mem (I := Ideal.map (algebraMap R S) (maximalIdeal R))
            (x := algebraMap R S (x : R))).2
            (Ideal.mem_map_of_mem (algebraMap R S) x.2)
    let hJ_ne_top : J ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top <|
        hJ_le_closedFiberIdeal.trans (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
    letI : Nontrivial S' := Ideal.Quotient.nontrivial_iff.mpr hJ_ne_top
    letI : IsLocalRing S' :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let hI_le_comap_J : I ≤ Ideal.comap (algebraMap R S) J :=
      by
        simpa [I, J] using
          (Ideal.span_singleton_le_iff_mem (I := Ideal.comap (algebraMap R S) J)
            (x := (x : R))).2
            (Ideal.subset_span (by simp))
    letI : Algebra R' S' :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (R := R) (A := S) (p := I) (P := J) hI_le_comap_J
    (algebraMap R' S').Flat →
      (algebraMap R S).Flat := by
  dsimp
  intro hflatQuot
  let I : Ideal R := Ideal.span ({(x : R)} : Set R)
  let J : Ideal S := Ideal.span ({algebraMap R S (x : R)} : Set S)
  let R' : Type u := R ⧸ I
  let S' : Type v := S ⧸ J
  have hI_le : I ≤ maximalIdeal R := by
    simpa [I] using
      (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := (x : R))).2 x.2
  have hI_ne_top : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI_le
  letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  letI : IsLocalRing R' :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hJ_le_closedFiberIdeal :
      J ≤ Ideal.map (algebraMap R S) (maximalIdeal R) := by
    simpa [J] using
      (Ideal.span_singleton_le_iff_mem (I := Ideal.map (algebraMap R S) (maximalIdeal R))
        (x := algebraMap R S (x : R))).2
        (Ideal.mem_map_of_mem (algebraMap R S) x.2)
  have hJ_ne_top : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top <|
      hJ_le_closedFiberIdeal.trans (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  letI : Nontrivial S' := Ideal.Quotient.nontrivial_iff.mpr hJ_ne_top
  letI : IsLocalRing S' :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hI_le_comap_J : I ≤ Ideal.comap (algebraMap R S) J := by
    simpa [I, J] using
      (Ideal.span_singleton_le_iff_mem (I := Ideal.comap (algebraMap R S) J)
        (x := (x : R))).2
        (Ideal.subset_span (by simp))
  letI : Algebra R' S' :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) hI_le_comap_J
  have hJ_eq : Ideal.map (algebraMap R S) I = J := by
    -- Proof comment: the principal target quotient is the mapped source principal ideal.
    simp [I, J, Ideal.map_span, Set.image_singleton]
  have hflatS' : Module.Flat R' S' := by
    -- Proof comment: read ring-map flatness as flatness of the target quotient module.
    exact (RingHom.flat_algebraMap_iff).mp hflatQuot
  have hflat_mapped :
      Module.Flat R' ((S ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S S))) : Type v) := by
    let K : Ideal S := Ideal.map (algebraMap R S) I
    let T : Type v := S ⧸ K
    letI : Algebra R' T :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (R := R) (A := S) (p := I) (P := K) Ideal.le_comap_map
    have hflatT : Module.Flat R' T := by
      -- Proof comment: the principal quotient owner and mapped-ideal quotient owner agree because
      -- the target element is the image of the source head.
      let eT : T ≃ₐ[R'] S' :=
        AlgEquiv.ofRingEquiv (R := R') (f := Ideal.quotEquivOfEq (by simpa [K] using hJ_eq))
          (by
            intro y
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
            rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
            rw [Ideal.quotEquivOfEq_mk]
            rfl)
      letI : Module.Flat R' S' := hflatS'
      exact Module.Flat.of_linearEquiv eT.toLinearEquiv
    have hK_top : (K • (⊤ : Submodule S S)) = (K : Submodule S S) := by
      simpa [Ideal.smul_eq_mul] using (Ideal.mul_top K)
    let eK :
        ((S ⧸ (K • (⊤ : Submodule S S))) : Type v) ≃ₗ[S] (S ⧸ K) :=
      Submodule.quotEquivOfEq _ _ hK_top
    let eK' : ((S ⧸ (K • (⊤ : Submodule S S))) : Type v) ≃ₗ[T] (S ⧸ K) :=
      eK.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    have hflat_over_T :
        Module.Flat T ((S ⧸ (K • (⊤ : Submodule S S))) : Type v) := by
      letI : Module.Flat T (S ⧸ K) := inferInstance
      exact Module.Flat.of_linearEquiv eK'
    letI : IsScalarTower R' T ((S ⧸ (K • (⊤ : Submodule S S))) : Type v) :=
      IsScalarTower.of_compHom R' T ((S ⧸ (K • (⊤ : Submodule S S))) : Type v)
    letI : Module.Flat R' T := hflatT
    letI : Module.Flat T ((S ⧸ (K • (⊤ : Submodule S S))) : Type v) := hflat_over_T
    simpa [K] using Module.Flat.trans R' T ((S ⧸ (K • (⊤ : Submodule S S))) : Type v)
  have hflat_mod :
      Module.Flat R' (S ⧸ (I • (⊤ : Submodule R S))) := by
    -- Proof comment: switch from the mapped target ideal quotient to the source quotient owner
    -- expected by the principal flatness bridge.
    let e :=
      quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := S) I
    letI :
        Module.Flat R'
          ((S ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S S))) : Type v) :=
      hflat_mapped
    exact Module.Flat.of_linearEquiv e.symm
  have hflatRS : Module.Flat R S :=
    flat_of_regular_element_and_flat_mod_ideal_self_univ
      (R := R) (S := S) (x : R) hI_ne_top hsource htarget hflat_mod
  -- Proof comment: return to the public ring-hom flatness owner.
  exact (RingHom.flat_algebraMap_iff).mpr hflatRS

omit [IsRegularLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 1: a one-step source quotient with dimension drop
`ringKrullDim R' + 1 = ringKrullDim R = n + 1` has dimension `n`. -/
private lemma head_quotient_source_dimension_eq_pred
    {R' : Type*} [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    {n : ℕ} (hdimR : ringKrullDim R = n + 1)
    (hdrop : ringKrullDim R' + 1 = ringKrullDim R) :
    ringKrullDim R' = n := by
  obtain ⟨m, hm⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (T := R')
  have hm_succ : m + 1 = n + 1 := by
    -- Proof comment: represent both source dimensions by naturals and compare the exact
    -- one-step quotient drop on the natural-number side.
    have hm_succ' : (((m + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) := by
      simpa [hm, hdimR] using hdrop
    exact_mod_cast hm_succ'
  have hm_eq : m = n := by
    omega
  simpa [hm, hm_eq]

/-- Helper for Chap10 Lemma 10 128 1: the source dimension formula descends to the one-head quotient
local map. -/
private lemma head_quotient_dimension_formula_of_dimension_formula
    {R' : Type u} {S' : Type v}
    [CommRing R'] [CommRing S'] [Algebra R' S']
    [IsLocalRing R'] [IsLocalRing S'] [IsNoetherianRing S']
    [IsLocalHom (algebraMap R' S')]
    {n : ℕ}
    (hdimR : ringKrullDim R = n + 1)
    (hR' : ringKrullDim R' = n)
    (hS' : ringKrullDim S' + 1 = ringKrullDim S)
    (hclosedFiber :
      ringKrullDim (Ideal.Fiber (maximalIdeal R') S') = ringKrullDim ClosedFiber)
    (hdim : ringKrullDim S = ringKrullDim R + ringKrullDim ClosedFiber) :
    ringKrullDim S' = ringKrullDim R' + ringKrullDim (Ideal.Fiber (maximalIdeal R') S') := by
  -- Proof comment: choose natural-number representatives for the target quotient and its closed
  -- fiber, then cancel the common successor in the descended dimension formula.
  obtain ⟨m, hm⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (T := S')
  let 𝔪S : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  letI : IsLocalRing ClosedFiber := by
    letI : IsLocalRing (S ⧸ 𝔪S) := by
      have h𝔪S_lt_top : 𝔪S < (⊤ : Ideal S) :=
        IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
      letI : Nontrivial (S ⧸ 𝔪S) := Ideal.Quotient.nontrivial_iff.mpr h𝔪S_lt_top.ne
      exact IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔪S) Ideal.Quotient.mk_surjective
    exact (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv.isLocalRing
  letI : IsNoetherianRing ClosedFiber :=
    isNoetherianRing_of_ringEquiv (S ⧸ 𝔪S)
      (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv
  obtain ⟨e, he⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (T := ClosedFiber)
  have hsucc :
      m + 1 = (n + 1) + e := by
    have hsucc_cast :
        (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) =
          (((n + 1 + e : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      calc
        (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) =
            ringKrullDim S' + 1 := by simp [hm]
        _ = ringKrullDim S := hS'
        _ = ringKrullDim R + ringKrullDim ClosedFiber := hdim
        _ =
            (n : WithBot ℕ∞) + 1 +
              ringKrullDim ClosedFiber := by
              rw [hdimR]
        _ =
            (n : WithBot ℕ∞) + 1 + (e : WithBot ℕ∞) := by
              rw [he]
        _ = (((n + 1 + e : ℕ) : ℕ∞) : WithBot ℕ∞) := by norm_num [add_assoc]
    exact_mod_cast hsucc_cast
  have hm_eq : m = n + e := by
    omega
  calc
    ringKrullDim S' = m := hm
    _ = n + e := by exact_mod_cast hm_eq
    _ =
        ringKrullDim R' + ringKrullDim (Ideal.Fiber (maximalIdeal R') S') := by
          simp [hR', hclosedFiber, he]

/-- Helper for Chap10 Lemma 10 128 1: own the induction on `dim R` for the miracle-flatness dimension
formula, so the recursive call can run on the canonical quotient local map. -/
private theorem flat_dimension_formula_aux
    (n : ℕ) :
    ∀ {R : Type u} {S : Type v}
      [CommRing R] [CommRing S] [Algebra R S]
      [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
      [IsLocalHom (algebraMap R S)],
      ringKrullDim R = n →
      Module.CohenMacaulay S S →
      ringKrullDim S = ringKrullDim R + ringKrullDim (Ideal.Fiber (maximalIdeal R) S) →
      (algebraMap R S).Flat := by
  induction n with
  | zero =>
      intro R S _ _ _ _ _ _ _ hdimR hCM hdim
      have hField : IsField R :=
        regularLocalRing_isField_of_ringKrullDim_eq_zero (T := R) hdimR
      -- Proof comment: the zero-dimensional regular local source is a field, so every algebra is
      -- flat over it.
      exact RingHom.Flat.of_isField (R := R) (S := S) hField (algebraMap R S)
  | succ n ih =>
      intro R S _ _ _ _ _ _ _ hdimR hCM hdim
      have hR_pos : 0 < ringKrullDim R := by
        -- Proof comment: the successor-dimension branch is the source-faithful positive-dimension
        -- case where we choose one head element and recurse on the quotient map.
        simpa [hdimR] using
          (show (0 : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) from by
            exact_mod_cast Nat.succ_pos n)
      obtain ⟨x, hx_not_mem_sq, hx_avoid⟩ :=
        exists_head_element_not_mem_sq_avoiding_minimalPrimes
          (R := R) (S := S) hCM hR_pos hdim
      have hRquot :
          IsRegularLocalRing (R ⧸ Ideal.span ({(x : R)} : Set R)) ∧
            ringKrullDim (R ⧸ Ideal.span ({(x : R)} : Set R)) + 1 = ringKrullDim R :=
        head_quotient_regularLocalRing_and_dimension_drop_of_not_mem_sq
          (R := R) x hx_not_mem_sq
      let I : Ideal R := Ideal.span ({(x : R)} : Set R)
      let J : Ideal S := Ideal.span ({algebraMap R S (x : R)} : Set S)
      let R' : Type u := R ⧸ I
      let S' : Type v := S ⧸ J
      have hI_le_max : I ≤ maximalIdeal R := by
        simpa [I] using
          (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := (x : R))).2 x.2
      have hI_ne_top : I ≠ ⊤ := by
        exact ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI_le_max
      letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
      letI : IsLocalRing R' :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      -- Proof comment: install the quotient source as the new regular-local owner for recursion.
      letI : IsRegularLocalRing R' := by
        simpa [R', I] using hRquot.1
      have hJ_le_closedFiberIdeal :
          J ≤ Ideal.map (algebraMap R S) (maximalIdeal R) := by
        simpa [J] using
          (Ideal.span_singleton_le_iff_mem (I := Ideal.map (algebraMap R S) (maximalIdeal R))
            (x := algebraMap R S (x : R))).2
            (Ideal.mem_map_of_mem (algebraMap R S) x.2)
      have hJ_lt_top : J < ⊤ := by
        exact lt_of_le_of_lt hJ_le_closedFiberIdeal
          (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
      letI : Nontrivial S' := Ideal.Quotient.nontrivial_iff.mpr hJ_lt_top.ne
      letI : IsLocalRing S' :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
          Ideal.Quotient.mk_surjective
      have hI_le_comap_J : I ≤ Ideal.comap (algebraMap R S) J := by
        simpa [I, J] using
          (Ideal.span_singleton_le_iff_mem (I := Ideal.comap (algebraMap R S) J)
            (x := (x : R))).2
            (Ideal.subset_span (by simp))
      letI : Algebra R' S' :=
        Ideal.Quotient.algebraQuotientOfLEComap
          (R := R) (A := S) (p := I) (P := J) hI_le_comap_J
      letI : IsLocalHom (algebraMap R' S') := by
        -- Proof comment: the quotient map remains local because `J` is a proper ideal in the
        -- target maximal ideal, and units reflect along the original local homomorphism.
        letI : IsLocalHom (algebraMap S S') :=
          IsLocalHom.of_surjective (algebraMap S S')
            (by simpa [S', J] using Ideal.Quotient.mk_surjective (I := J))
        letI : IsLocalHom (algebraMap R S') := by
          change IsLocalHom ((algebraMap S S').comp (algebraMap R S))
          infer_instance
        refine ⟨?_⟩
        intro y hy
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hrS'_quot : IsUnit ((algebraMap R' S') (Ideal.Quotient.mk I r)) := by
          simpa using hy
        have hrS' : IsUnit (algebraMap R S' r) := by
          have hmap :
              (algebraMap R' S') (Ideal.Quotient.mk I r) = algebraMap R S' r := by
            rfl
          simpa [hmap] using hrS'_quot
        have hrR : IsUnit r := (isUnit_map_iff (algebraMap R S') r).mp hrS'
        letI : IsLocalHom (algebraMap R R') :=
          IsLocalHom.of_surjective (algebraMap R R')
            (by simpa [R'] using Ideal.Quotient.mk_surjective (I := I))
        simpa [R'] using (isUnit_map_iff (algebraMap R R') r).mpr hrR
      have hRquotDim : ringKrullDim R' = n := by
        -- Proof comment: the source quotient has dimension one less than the original source.
        simpa [R', I] using
          head_quotient_source_dimension_eq_pred
            (R := R) (R' := R') hdimR (by simpa [R', I] using hRquot.2)
      have hclosedFiberQuot :
          ringKrullDim (Ideal.Fiber (maximalIdeal R') S') =
            ringKrullDim (Ideal.Fiber (maximalIdeal R) S) := by
        -- Proof comment: killing the same head element on both sides preserves the closed fiber.
        simpa [R', S', I, J] using
          closedFiber_dimension_eq_after_head_quotient (R := R) (S := S) x
      have htargetHead :
          IsSMulRegular S (algebraMap R S (x : R)) ∧ ringKrullDim S' + 1 = ringKrullDim S := by
        -- Proof comment: the avoided-minimal-primes choice makes the target head regular and
        -- lowers the target dimension by exactly one.
        simpa [S', J] using
          target_head_regular_and_dimension_drop_of_avoids_minimalPrimes
            (R := R) (S := S) hCM x hx_avoid
      have hSreg : IsSMulRegular S (algebraMap R S (x : R)) := htargetHead.1
      have hSquotDim : ringKrullDim S' + 1 = ringKrullDim S := htargetHead.2
      have hSquotCM : Module.CohenMacaulay S' S' := by
        -- Proof comment: source-faithfully transport the Cohen-Macaulay quotient owner from the
        -- principal quotient `S / xS` supplied by the textbook route.
        simpa [S', J] using
          principal_quotient_cohenMacaulay_self_of_dimension_drop
            (S := S) hCM hSquotDim
      have hdimQuot :
          ringKrullDim S' =
            ringKrullDim R' + ringKrullDim (Ideal.Fiber (maximalIdeal R') S') := by
        -- Proof comment: combine the two one-step dimension drops with the preserved closed fiber.
        exact
          head_quotient_dimension_formula_of_dimension_formula
            (R := R) (S := S) (R' := R') (S' := S')
            hdimR hRquotDim hSquotDim hclosedFiberQuot hdim
      have hsourceHead : IsRegular (x : R) :=
        head_isRegular_of_not_mem_sq (R := R) x hx_not_mem_sq
      have htargetHeadR : IsSMulRegular S (x : R) :=
        (isSMulRegular_algebraMap_iff S).1 hSreg
      have hflatQuot : (algebraMap R' S').Flat :=
        ih (R := R') (S := S') hRquotDim hSquotCM hdimQuot
      -- Route correction: the earlier proof got stuck because recursion still lived in the public
      -- theorem. Recurse on the canonical quotient owner first, then lift flatness back upstairs.
      exact
        flat_of_head_quotient_flat_of_regular_pair
          (R := R) (S := S) x hsourceHead htargetHeadR hflatQuot

/-- Public wrapper for Chap10 Lemma 10 128 1: let `R → S` be a local homomorphism of Noetherian local rings. If `R` is a
regular local ring, `S` is Cohen-Macaulay, and the dimension formula
`dim S = dim R + dim ((maximalIdeal R).Fiber S)`, equivalently
`dim S = dim R + dim (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))`, holds, then `R → S` is
flat. -/
@[stacks 00R4]
theorem algebraMap_flat_of_isRegularLocalRing_of_cohenMacaulay_of_dimension_formula
    (hCM : Module.CohenMacaulay S S)
    (hdim : ringKrullDim S = ringKrullDim R + ringKrullDim ClosedFiber) :
    (algebraMap R S).Flat := by
  obtain ⟨dR, hdR⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (T := R)
  -- Proof comment: the public theorem is now a thin wrapper around the private induction owner on
  -- the natural-number source dimension.
  exact flat_dimension_formula_aux dR (R := R) (S := S) hdR hCM hdim

end
