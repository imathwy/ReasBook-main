import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_106_1
import stacks_proof.stacks_project.Chap10.Lemma_10_106_2
import stacks_proof.stacks_project.Chap15.Lemma_15_48_2

-- Shared support for Lemmas 15.122.1 and 15.122.2.

universe u

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open IsLocalRing

/-- Helper for Lemmas 15.122.1 and 15.122.2: positive Krull dimension lets us choose a parameter
outside `𝔪²` whose principal ideal is prime. This is the source-level global parameter used in the
inductive step. -/
theorem exists_prime_parameter_of_positive_dim (hdim_pos : 0 < ringKrullDim R) :
    ∃ x : R,
      x ∈ maximalIdeal R ∧
        x ∉ maximalIdeal R ^ 2 ∧
        (Ideal.span ({x} : Set R)).IsPrime := by
  -- Convert regularity into the cotangent-space dimension formula for the maximal ideal.
  have hregdim : ringKrullDim R = (maximalIdeal R).spanFinrank := by
    simpa using ((isRegularLocalRing_iff R).1 inferInstance).symm
  have hspan_pos : 0 < (maximalIdeal R).spanFinrank := by
    -- A zero-dimensional cotangent space would force `ringKrullDim R = 0`, contradicting the
    -- positive-dimension hypothesis.
    by_contra hspan_zero
    have hdim0 : ringKrullDim R = 0 := by
      simpa [Nat.eq_zero_of_not_pos hspan_zero] using hregdim
    exact (lt_irrefl (0 : WithBot ℕ∞)) (hdim0 ▸ hdim_pos)
  -- Choose a regular system of parameters of full length and take its first parameter.
  obtain ⟨z, hz⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters
      (R := R) (d := (maximalIdeal R).spanFinrank) hregdim).1 inferInstance
  let i0 : Fin ((maximalIdeal R).spanFinrank) := ⟨0, hspan_pos⟩
  have hcot_ne_zero : (maximalIdeal R).toCotangent (z i0) ≠ 0 := by
    simpa [regularSystemOfParameters_cotangentBasis_apply] using
      (regularSystemOfParameters_cotangentBasis hz).ne_zero i0
  refine ⟨z i0, (z i0).2, ?_, ?_⟩
  · -- A nonzero cotangent class is exactly the statement that the chosen parameter avoids `𝔪²`.
    intro hx_sq
    exact hcot_ne_zero ((Ideal.toCotangent_eq_zero (maximalIdeal R) (z i0)).2 hx_sq)
  · -- Quotienting by a single parameter stays regular local, hence the principal ideal is prime.
    have hpart :
        IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank
          (fun _ : Fin 1 ↦ z i0) :=
      isPartOfRegularSystemOfParameters_singleton_of_not_mem_maximalIdeal_sq
        (A := R) (z i0) (by
          intro hx_sq
          exact hcot_ne_zero ((Ideal.toCotangent_eq_zero (maximalIdeal R) (z i0)).2 hx_sq))
    have hquot_param :
        IsRegularLocalRing (R ⧸ parameterIdeal (fun _ : Fin 1 ↦ z i0)) :=
      IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal hpart
    let eParam :
        (R ⧸ parameterIdeal (fun _ : Fin 1 ↦ z i0)) ≃ₐ[R]
          (R ⧸ principalIdeal (z i0 : R)) :=
      Ideal.quotientEquivAlgOfEq R (parameterIdeal_fin1_eq_principalIdeal (A := R) (z i0))
    have hquot_principal : IsRegularLocalRing (R ⧸ principalIdeal (z i0 : R)) :=
      IsRegularLocalRing.of_ringEquiv eParam.toRingEquiv
    have hquot_domain : IsDomain (R ⧸ principalIdeal (z i0 : R)) := by
      let _ : IsRegularLocalRing (R ⧸ principalIdeal (z i0 : R)) := hquot_principal
      infer_instance
    -- Kernels of quotient maps to domains are prime; here the kernel is the principal ideal.
    change (principalIdeal (z i0 : R)).IsPrime
    refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
    · intro htop
      have hle : principalIdeal (z i0 : R) ≤ maximalIdeal R := by
        rw [principalIdeal, Ideal.span_le]
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact (z i0).2
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (htop ▸ hle))
    · intro a b hab
      have hmul_zero : Ideal.Quotient.mk (principalIdeal (z i0 : R)) (a * b) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 hab
      have hmul_zero' :
          Ideal.Quotient.mk (principalIdeal (z i0 : R)) a *
            Ideal.Quotient.mk (principalIdeal (z i0 : R)) b = 0 := by
        simpa using hmul_zero
      have hzero :
          Ideal.Quotient.mk (principalIdeal (z i0 : R)) a = 0 ∨
            Ideal.Quotient.mk (principalIdeal (z i0 : R)) b = 0 :=
        eq_zero_or_eq_zero_of_mul_eq_zero hmul_zero'
      rcases hzero with ha0 | hb0
      · left
        exact Ideal.Quotient.eq_zero_iff_mem.1 ha0
      · right
        exact Ideal.Quotient.eq_zero_iff_mem.1 hb0

/-- Helper for Lemmas 15.122.1 and 15.122.2: a zero-dimensional regular local ring has vanishing
maximal ideal, hence is a field. -/
private theorem isField_of_regularLocalRing_ringKrullDim_eq_zero
    (hdim : ringKrullDim R = 0) : IsField R := by
  -- Convert regularity into a cotangent-space dimension statement at the maximal ideal.
  have hspan' : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = 0 := by
    exact ((isRegularLocalRing_iff R).mp inferInstance).trans hdim
  have hspan : (IsLocalRing.maximalIdeal R).spanFinrank = 0 := by
    exact_mod_cast hspan'
  have hfg : (IsLocalRing.maximalIdeal R).FG := by
    exact Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R)
  -- A finitely generated ideal with zero span rank is the zero ideal.
  have hmax : IsLocalRing.maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hspan
  -- A local ring with zero maximal ideal is a field.
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax

/-- Helper for Lemmas 15.122.1 and 15.122.2: the shared package is explicit in dimension `0`.
Here the ring is a field, so every away localization is either trivial or local, and the ring is
automatically factorial. -/
private noncomputable def regularLocalRing_factoriality_and_away_picard_of_ringKrullDim_le_zero
    (hdim : ringKrullDim R ≤ 0) :
    Σ' (_ : ∀ f : R, Subsingleton (CommRing.Pic (Localization.Away f))),
      UniqueFactorizationMonoid R := by
  have hdim0 : ringKrullDim R = 0 := by
    apply le_antisymm hdim
    exact ringKrullDim_nonneg_of_nontrivial
  let _ : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
  have hfield : IsField R :=
    isField_of_regularLocalRing_ringKrullDim_eq_zero (R := R) hdim0
  letI : Field R := hfield.toField
  refine ⟨?_, inferInstance⟩
  intro f
  by_cases hf : f = 0
  · subst hf
    let _ : Subsingleton (Localization.Away (0 : R)) :=
      IsLocalization.subsingleton
        (show (0 : R) ∈ Submonoid.powers (0 : R) from ⟨1, by simp⟩)
    infer_instance
  · -- Over a field, any nonzero element is a unit, so the away localization stays local.
    have hfu : IsUnit f := by
      simpa using (isUnit_iff_ne_zero.mpr hf)
    let e := IsLocalization.atUnit R (Localization.Away f) f hfu
    let _ : IsLocalRing (Localization.Away f) := e.toRingEquiv.isLocalRing
    exact CommRing.Pic.instSubsingletonOfIsLocalRing (Localization.Away f)

/-- Shared owner for Lemmas 15.122.1 and 15.122.2: the source-faithful induction packages the two
outputs used later in the chapter, namely trivial Picard groups for away localizations and
factoriality of the original regular local ring. -/
noncomputable def regularLocalRing_factoriality_and_away_picard_of_ringKrullDim_le
    (n : ℕ) (_hdim : ringKrullDim R ≤ n) :
    Σ' (_ : ∀ f : R, Subsingleton (CommRing.Pic (Localization.Away f))),
      UniqueFactorizationMonoid R := by
  -- Route correction: this theorem is the canonical acyclic owner for the paired induction on the
  -- Krull-dimension bound. The source order is to prove away-localization Picard triviality first
  -- and then extract factoriality from that same induction package.
  cases n with
  | zero =>
      -- The base case is the zero-dimensional regular local ring calculation above.
      exact regularLocalRing_factoriality_and_away_picard_of_ringKrullDim_le_zero
        (R := R) _hdim
  | succ n =>
      -- TODO: prove the inductive step `A_(n+1)` then `B_(n+1)` using the away-localization
      -- dimension drop and Nagata descent from the rescue plan.
      sorry

/-- Helper for Lemmas 15.122.1 and 15.122.2: the Picard-triviality half of the shared induction
package applies to every away localization once the dimension bound is fixed. -/
theorem subsingleton_picardGroup_localizationAway_of_isRegularLocalRing_of_ringKrullDim_le
    (n : ℕ) (hdim : ringKrullDim R ≤ n) (f : R) :
    Subsingleton (CommRing.Pic (Localization.Away f)) := by
  -- The first projection of the shared package is exactly the away-localization statement.
  exact
    (regularLocalRing_factoriality_and_away_picard_of_ringKrullDim_le
      (R := R) n hdim).1 f

/-- Helper for Lemmas 15.122.1 and 15.122.2: the factoriality half of the shared induction package
specializes directly to the bounded-dimension regular local ring. -/
noncomputable abbrev regularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le
    (n : ℕ) (hdim : ringKrullDim R ≤ n) : UniqueFactorizationMonoid R := by
  -- The second projection of the shared package is the desired owner instance.
  exact
    (regularLocalRing_factoriality_and_away_picard_of_ringKrullDim_le
      (R := R) n hdim).2

end
