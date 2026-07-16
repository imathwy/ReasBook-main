import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_77_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Ideal R} [I.IsTwoSided] (hI : IsNilpotent I)
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]

/-- Helper for Lemma 10.77.5: coefficientwise reduction modulo `I` on finitely supported functions,
viewed as an `R`-linear map by restriction of scalars. -/
abbrev finsupp_quotientMapLinear (ι : Type v) :
    (ι →₀ R) →ₗ[R] ι →₀ (R ⧸ I) :=
  { toFun := fun f => Finsupp.mapRange (Ideal.Quotient.mk I) (by simp) f
    map_add' := by
      intro f g
      ext i
      simp
    map_smul' := by
      intro r f
      ext i
      change (Ideal.Quotient.mk I) (r * f i) = r • (Ideal.Quotient.mk I) (f i)
      rfl }

/-- Helper for Lemma 10.77.5: coefficientwise reduction from the free `R`-module to the free
`R ⧸ I`-module is surjective. -/
lemma finsupp_quotientMap_surjective (ι : Type v) :
    Function.Surjective (finsupp_quotientMapLinear (R := R) (I := I) ι) := by
  -- Surjectivity is coefficientwise surjectivity of the quotient map `R → R ⧸ I`.
  simpa [finsupp_quotientMapLinear] using
    (Finsupp.mapRange_surjective (α := ι) (Ideal.Quotient.mk I)
      (by simp) (Ideal.Quotient.mk_surjective (I := I)))

/-- Helper for Lemma 10.77.5: the quotient projector on the free quotient module lifts to an
endomorphism of the free module before imposing idempotency. -/
lemma lift_projector_across_nilpotent_quotient_on_finsupp
    (pbar : Module.End (R ⧸ I) (Pbar →₀ (R ⧸ I))) :
    ∃ p0 : Module.End R (Pbar →₀ R),
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp p0 = (pbar.restrictScalars R).comp qF := by
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hqF : Function.Surjective qF :=
    finsupp_quotientMap_surjective (R := R) (I := I) Pbar
  -- The free source module is projective, so the quotient projector lifts along the surjection.
  obtain ⟨p0, hp0⟩ :=
    Module.projective_lifting_property qF ((pbar.restrictScalars R).comp qF) hqF
  exact ⟨p0, hp0⟩

/-- Helper for Lemma 10.77.5: if a lifted endomorphism reduces to an idempotent projector, then
its idempotency defect is killed by coefficientwise reduction modulo `I`. -/
lemma lifted_projector_defect_comp_eq_zero
    (pbarR : Module.End R (Pbar →₀ (R ⧸ I)))
    (hpbarR : pbarR.comp pbarR = pbarR)
    (p0 : Module.End R (Pbar →₀ R))
    (hp0 :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp p0 = pbarR.comp qF) :
    let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
      finsupp_quotientMapLinear (R := R) (I := I) Pbar
    qF.comp (p0.comp p0 - p0) = 0 := by
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hp0' : qF.comp p0 = pbarR.comp qF := hp0
  have hcomp :
      qF.comp (p0.comp p0) = (pbarR.comp pbarR).comp qF := by
    calc
      qF.comp (p0.comp p0) = (qF.comp p0).comp p0 := by rw [LinearMap.comp_assoc]
      _ = (pbarR.comp qF).comp p0 := by rw [hp0']
      _ = pbarR.comp (qF.comp p0) := by rw [← LinearMap.comp_assoc]
      _ = pbarR.comp (pbarR.comp qF) := by rw [hp0']
      _ = (pbarR.comp pbarR).comp qF := by rw [LinearMap.comp_assoc]
  -- After two reductions we see the same projector square as in the quotient module.
  calc
    qF.comp (p0.comp p0 - p0) = qF.comp (p0.comp p0) - qF.comp p0 := by
      rw [LinearMap.comp_sub]
    _ = (pbarR.comp pbarR).comp qF - pbarR.comp qF := by rw [hcomp, hp0']
    _ = pbarR.comp qF - pbarR.comp qF := by rw [hpbarR]
    _ = 0 := by
      ext x i
      simp

/-- Helper for Lemma 10.77.5: the explicit coefficientwise reduction map agrees with the standard
`Finsupp.mapRange.linearMap` attached to `I.mkQ`. -/
lemma finsupp_quotientMapLinear_eq_mapRangeLinear (ι : Type v) :
    finsupp_quotientMapLinear (R := R) (I := I) ι =
      Finsupp.mapRange.linearMap (I.mkQ : R →ₗ[R] R ⧸ I) := by
  -- Both maps reduce every coefficient modulo `I`.
  ext f i
  rfl

/-- Helper for Lemma 10.77.5: membership in `I • ⊤` on a finitely supported free module forces
every coefficient to lie in `I`. -/
lemma coeff_mem_ideal_of_mem_ideal_smul_top
    {ι : Type v} {x : ι →₀ R}
    (hx : x ∈ I • (⊤ : Submodule R (ι →₀ R))) (i : ι) :
    x i ∈ I := by
  -- Evaluate the submodule-membership statement at the chosen basis coordinate.
  have h_eval :
      (Finsupp.lapply (R := R) (M := R) i) x ∈ I • (⊤ : Submodule R R) := by
    exact
      (Submodule.smul_top_le_comap_smul_top I
        (Finsupp.lapply (R := R) (M := R) i)) hx
  simpa using h_eval

/-- Helper for Lemma 10.77.5: the finitely supported vectors whose coefficients lie in `I`
are exactly the submodule `I • ⊤` of the free module. -/
lemma finsupp_submodule_eq_ideal_smul_top (ι : Type v) :
    Finsupp.submodule (fun _ : ι => I) = I • (⊤ : Submodule R (ι →₀ R)) := by
  ext x
  constructor
  · intro hx
    -- Expand the finitely supported vector in the standard basis and use the ideal coefficients.
    have hsum : x = x.sum fun i a => a • Finsupp.single i (1 : R) := by
      ext i
      simp
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem_smul (hx i) (by simp : Finsupp.single i (1 : R) ∈
      (⊤ : Submodule R (ι →₀ R)))
  · intro hx
    -- Coefficient evaluation detects membership in `I • ⊤`.
    intro i
    exact coeff_mem_ideal_of_mem_ideal_smul_top (R := R) (I := I) hx i

/-- Helper for Lemma 10.77.5: the coefficientwise quotient map has kernel `I • ⊤`. -/
lemma finsupp_quotientMap_ker_eq_ideal_smul_top (ι : Type v) :
    LinearMap.ker (finsupp_quotientMapLinear (R := R) (I := I) ι) =
      I • (⊤ : Submodule R (ι →₀ R)) := by
  -- Rewrite the kernel through `Finsupp.ker_mapRange`, then identify the coefficientwise ideal
  -- submodule with the abstract `I • ⊤`.
  rw [finsupp_quotientMapLinear_eq_mapRangeLinear (R := R) (I := I) (ι := ι)]
  rw [Finsupp.ker_mapRange]
  simpa [Ideal.Quotient.eq_zero_iff_mem] using
    finsupp_submodule_eq_ideal_smul_top (R := R) (I := I) ι

/-- Helper for Lemma 10.77.5: if an endomorphism of the free module vanishes after coefficientwise
reduction modulo `I`, then its image lands in `I • ⊤`, so nilpotence of `I` forces nilpotence of
the endomorphism itself. -/
lemma endomorphism_defect_isNilpotent_of_comp_quotient_zero
    (hI : IsNilpotent I)
    (d : Module.End R (Pbar →₀ R))
    (hd :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp d = 0) :
    IsNilpotent d := by
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hd' : qF.comp d = 0 := hd
  have hrange :
      LinearMap.range d ≤ I • (⊤ : Submodule R (Pbar →₀ R)) := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    have hker : d y ∈ LinearMap.ker qF := by
      rw [LinearMap.mem_ker]
      simpa [LinearMap.comp_apply] using DFunLike.congr_fun hd' y
    have hker_eq : LinearMap.ker qF = Finsupp.submodule (fun _ : Pbar => I) := by
      calc
        LinearMap.ker qF = I • (⊤ : Submodule R (Pbar →₀ R)) := by
          simpa [qF] using finsupp_quotientMap_ker_eq_ideal_smul_top (R := R) (I := I) Pbar
        _ = Finsupp.submodule (fun _ : Pbar => I) := by
          rw [finsupp_submodule_eq_ideal_smul_top (R := R) (I := I) Pbar]
    have hker' : d y ∈ Finsupp.submodule (fun _ : Pbar => I) := by
      exact hker_eq ▸ hker
    have hcoeff : ∀ i : Pbar, (d y) i ∈ I := fun i => hker' i
    -- Re-expand the finitely supported vector in the standard basis and use the ideal
    -- coefficients one basis vector at a time.
    have hsum : d y = (d y).sum fun i a => a • Finsupp.single i (1 : R) := by
      ext i
      simp
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem_smul (hcoeff i) (by simp : Finsupp.single i (1 : R) ∈
      (⊤ : Submodule R (Pbar →₀ R)))
  have hmap :
      ∀ {J : Ideal R} {x : Pbar →₀ R},
        x ∈ J • (⊤ : Submodule R (Pbar →₀ R)) →
          d x ∈ J • (I • (⊤ : Submodule R (Pbar →₀ R))) := by
    intro J x hx
    -- Apply linearity of `d` termwise across an `Ideal`-smul expression.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      have hdm : d m ∈ I • (⊤ : Submodule R (Pbar →₀ R)) := hrange ⟨m, rfl⟩
      rw [map_smul]
      exact Submodule.smul_mem_smul hr hdm
    · intro y z hy hz
      simpa [map_add] using
        Submodule.add_mem (J • (I • (⊤ : Submodule R (Pbar →₀ R)))) hy hz
  have hpow :
      ∀ n : ℕ, LinearMap.range (d ^ n) ≤ I ^ n • (⊤ : Submodule R (Pbar →₀ R)) := by
    intro n
    induction n with
    | zero =>
        intro x hx
        rcases hx with ⟨y, rfl⟩
        simpa [Submodule.pow_zero, Submodule.top_smul] using
          (show y ∈ (⊤ : Submodule R (Pbar →₀ R)) by simp)
    | succ n ihn =>
        intro x hx
        rcases hx with ⟨y, rfl⟩
        have hy : (d ^ n) y ∈ I ^ n • (⊤ : Submodule R (Pbar →₀ R)) := ihn ⟨y, rfl⟩
        have hy' : d ((d ^ n) y) ∈ I ^ n • (I • (⊤ : Submodule R (Pbar →₀ R))) :=
          hmap (J := I ^ n) hy
        have hpowEq : I ^ (n + 1) = I ^ n * I := by
          simpa using (Submodule.pow_succ (M := I) (n := n))
        rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
        rw [hpowEq]
        simpa [Submodule.mul_smul] using hy'
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  apply LinearMap.ext
  intro x
  ext i
  -- Once `I ^ n = 0`, the image control above forces the `n`-th power to vanish.
  have hx : (d ^ n) x ∈ I ^ n • (⊤ : Submodule R (Pbar →₀ R)) := hpow n ⟨x, rfl⟩
  have hx0 : (d ^ n) x = 0 := by
    simpa [hn] using hx
  simpa using congrArg (fun z : Pbar →₀ R => z i) hx0

/-- Helper for Lemma 10.77.5: every endomorphism of the free module preserves `I • ⊤`, so it
induces an endomorphism on the quotient by `I • ⊤`. -/
lemma ideal_smul_top_le_comap_endomorphism
    (d : Module.End R (Pbar →₀ R)) :
    I • (⊤ : Submodule R (Pbar →₀ R)) ≤
      (I • (⊤ : Submodule R (Pbar →₀ R))).comap d := by
  -- This is the standard ideal-stability statement `f (I • M) ⊆ I • M`.
  simpa using (Submodule.smul_top_le_comap_smul_top I d)

/-- Helper for Lemma 10.77.5: once the lifted idempotency defect reduces to zero modulo `I`,
every correction term with that defect as a left factor also reduces to zero. -/
lemma lifted_projector_defect_left_mul_comp_eq_zero
    (d t : Module.End R (Pbar →₀ R))
    (hd :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp d = 0) :
    let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
      finsupp_quotientMapLinear (R := R) (I := I) Pbar
    qF.comp (d * t) = 0 := by
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hd' : qF.comp d = 0 := hd
  -- The left factor `d` already dies after reduction, so composing further on the right changes
  -- nothing modulo `I`.
  apply LinearMap.ext
  intro x
  ext i
  have hpoint : qF (d (t x)) = 0 := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hd' (t x)
  simpa [Module.End.mul_eq_comp, LinearMap.comp_apply] using congrArg (fun y => y i) hpoint

namespace LinearMap

/-- Helper for Lemma 10.77.5: quotienting an `R`-linear map by `I • ⊤` on both sides produces an
`R ⧸ I`-linear map. This keeps the final range comparison inside the current dependency closure. -/
abbrev quotientMapByIdeal_over_quotient
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R ⧸ I] M' ⧸ (I • (⊤ : Submodule R M')) :=
  { toFun :=
      (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M')) f
        (Submodule.smul_top_le_comap_smul_top I f)
    map_add' := by
      intro x y
      -- Work with quotient representatives so additivity reduces to the defining `mapQ` formula.
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
      obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) y
      simp
    map_smul' := by
      intro c x
      -- Unpack the quotient-ring scalar and the quotient representative simultaneously.
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
      simp [Module.Quotient.mk_smul_mk] }

end LinearMap

/-- Helper for Lemma 10.77.5: after restricting scalars along `R → R ⧸ I`, the original
`R`-action agrees with the quotient-ring scalar action. -/
lemma ideal_scalar_action_eq_quotient_scalar_action
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N]
    (r : R) (n : N) :
    r • n = ((Ideal.Quotient.mk I) r : R ⧸ I) • n := by
  -- Rewrite the restricted scalar action through the quotient-ring unit.
  calc
    r • n = r • ((1 : R ⧸ I) • n) := by simp
    _ = (r • (1 : R ⧸ I)) • n := by rw [smul_assoc]
    _ = ((Ideal.Quotient.mk I) r : R ⧸ I) • n := by
      change ((((Ideal.Quotient.mk I) r : R ⧸ I) * 1) : R ⧸ I) • n =
        ((Ideal.Quotient.mk I) r : R ⧸ I) • n
      simp

/-- Helper for Lemma 10.77.5: if an `R`-module already comes from an `R ⧸ I`-module, then every
scalar from `I` acts trivially, so `I • ⊤ = ⊥`. -/
lemma ideal_smul_top_eq_bot_of_quotient_module
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N] :
    I • (⊤ : Submodule R N) = ⊥ := by
  -- Every element of `I` acts trivially after passing to the quotient ring.
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
  intro r hr
  exact Module.mem_annihilator.mpr fun n => by
    -- Normalize the restricted action to the quotient action and use `r ∈ I`.
    rw [ideal_scalar_action_eq_quotient_scalar_action (R := R) (I := I) r n]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]

/-- Helper for Lemma 10.77.5: an `R`-linear equivalence between modules already defined over
`R ⧸ I` automatically respects the quotient-ring scalar action. -/
lemma linearEquiv_map_smul_over_quotient
    {M : Type*} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M]
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) (c : R ⧸ I) (x : M) :
    e (c • x) = c • e x := by
  -- Reduce quotient scalars to representatives in `R` and use `R`-linearity of `e`.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← ideal_scalar_action_eq_quotient_scalar_action (R := R) (I := I) r x]
  rw [e.map_smul]
  rw [ideal_scalar_action_eq_quotient_scalar_action (R := R) (I := I) r (e x)]

/-- Helper for Lemma 10.77.5: an `R`-linear equivalence between modules already defined over
`R ⧸ I` can be promoted to an `(R ⧸ I)`-linear equivalence. -/
def linearEquiv_over_quotient
    {M : Type*} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M]
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) : M ≃ₗ[R ⧸ I] N :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := linearEquiv_map_smul_over_quotient (R := R) (I := I) e }

/-- Helper for Lemma 10.77.5: quotienting an `R ⧸ I`-module by `I • ⊤` gives the same module,
because the quotient ideal already acts by zero. -/
def quotient_by_ideal_smul_top_linearEquiv
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N] :
    (N ⧸ (I • (⊤ : Submodule R N))) ≃ₗ[R ⧸ I] N :=
  -- First collapse the quotient as an `R`-module, then promote the equivalence to `R ⧸ I`.
  linearEquiv_over_quotient (R := R) (I := I)
    ((I • (⊤ : Submodule R N)).quotEquivOfEqBot
      (ideal_smul_top_eq_bot_of_quotient_module (R := R) (I := I)))

/-- Helper for Lemma 10.77.5: Lemma `10.32.7` corrects the lifted pre-projector on the free
module to an actual idempotent, and the correction still reduces to the same quotient projector
because it is divisible by the idempotency defect. -/
lemma idempotent_correction_of_lifted_projector
    (hI : IsNilpotent I)
    (pbarR : Module.End R (Pbar →₀ (R ⧸ I)))
    (hpbarR : pbarR.comp pbarR = pbarR)
    (p0 : Module.End R (Pbar →₀ R))
    (hp0 :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp p0 = pbarR.comp qF) :
    ∃ p : Module.End R (Pbar →₀ R),
      IsIdempotentElem p ∧
        let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
          finsupp_quotientMapLinear (R := R) (I := I) Pbar
        qF.comp p = pbarR.comp qF := by
  -- Route correction: the source proof corrects `p0` directly in `Module.End R (Pbar →₀ R)`
  -- via Lemma `10.32.7`, using the defect `d := p0.comp p0 - p0`.
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  let d : Module.End R (Pbar →₀ R) := p0.comp p0 - p0
  have hd_zero : qF.comp d = 0 := by
    -- The lifted defect already vanishes after reduction to the quotient module.
    simpa [qF, d] using
      lifted_projector_defect_comp_eq_zero
        (R := R) (I := I) (Pbar := Pbar) pbarR hpbarR p0 hp0
  have hd_nilpotent : IsNilpotent d := by
    -- Nilpotence of `I` makes every endomorphism with image in `I • ⊤` nilpotent.
    exact
      endomorphism_defect_isNilpotent_of_comp_quotient_zero
        (R := R) (I := I) (Pbar := Pbar) hI d (by simpa [qF] using hd_zero)
  have hd_pow_nilpotent : IsNilpotent (p0 ^ 2 - p0) := by
    -- Rewrite the defect in the multiplicative notation expected by the correction lemma.
    simpa [d, pow_two, Module.End.mul_eq_comp] using hd_nilpotent
  obtain ⟨q, hq⟩ :=
    exists_idempotent_eq_add_defect_mul_aeval (A := Module.End R (Pbar →₀ R)) p0 hd_pow_nilpotent
  refine ⟨p0 + d * Polynomial.aeval p0 q, ?_, ?_⟩
  · -- The local support copy of Lemma `10.32.7` gives an actual idempotent correction.
    simpa [d, pow_two, Module.End.mul_eq_comp] using hq
  · have hcorr_zero : qF.comp (d * Polynomial.aeval p0 q) = 0 := by
      -- Any term with the defect on the left still dies after reduction modulo `I`.
      simpa [qF] using
        lifted_projector_defect_left_mul_comp_eq_zero
          (R := R) (I := I) (Pbar := Pbar) d (Polynomial.aeval p0 q) (by simpa [qF] using hd_zero)
    -- The corrected projector has the same reduction because the correction term is defect-divisible.
    calc
      qF.comp (p0 + d * Polynomial.aeval p0 q)
          = qF.comp p0 + qF.comp (d * Polynomial.aeval p0 q) := by
              rw [LinearMap.comp_add]
      _ = pbarR.comp qF + 0 := by rw [hp0, hcorr_zero]
      _ = pbarR.comp qF := by simp

/-- Helper for Lemma 10.77.5: a split summand is linearly equivalent to the range of the
associated projector. -/
lemma projective_summand_linearEquiv_range_projector
    {S : Type u} [Ring S] {P : Type v} [AddCommGroup P] [Module S P]
    {F : Type w} [AddCommGroup F] [Module S F]
    (i : P →ₗ[S] F) (s : F →ₗ[S] P) (hs : s.comp i = LinearMap.id) :
    Nonempty (P ≃ₗ[S] LinearMap.range (i.comp s)) := by
  let iRange : P →ₗ[S] LinearMap.range (i.comp s) :=
    i.codRestrict (LinearMap.range (i.comp s)) fun x => by
      -- The split relation shows that every point of `i(Pbar)` is fixed by the projector.
      refine ⟨i x, ?_⟩
      simpa using congrArg i (LinearMap.congr_fun hs x)
  refine ⟨LinearEquiv.ofBijective iRange ?_⟩
  constructor
  · intro x y hxy
    -- Applying the retraction to equal images recovers equality on the summand.
    have hxy' : i x = i y := congrArg Subtype.val hxy
    calc
      x = s (i x) := by simpa using (LinearMap.congr_fun hs x).symm
      _ = s (i y) := by rw [hxy']
      _ = y := by simpa using LinearMap.congr_fun hs y
  · intro x
    -- Every point in the range is represented by a projected ambient vector.
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨y, rfl⟩
    refine ⟨s y, ?_⟩
    apply Subtype.ext
    simp [iRange, LinearMap.comp_apply]

/-- Helper for Lemma 10.77.5: the range of an idempotent endomorphism of a free module is
projective. -/
lemma projective_of_idempotent_range
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] (p : Module.End R M)
    (hp : IsIdempotentElem p) :
    Module.Projective R (LinearMap.range p) := by
  let hpProj : LinearMap.IsProj (LinearMap.range p) p :=
    LinearMap.IsIdempotentElem.isProj_range _ hp
  -- The codomain restriction of an idempotent provides the splitting of the range inclusion.
  exact Module.Projective.of_split (LinearMap.range p).subtype hpProj.codRestrict <| by
    ext x
    simpa using hpProj.codRestrict_apply_cod x

/-- Helper for Lemma 10.77.5: the endomorphism attached to a split summand is idempotent. -/
lemma split_projector_isIdempotentElem
    {S : Type u} [Ring S] {P : Type v} [AddCommGroup P] [Module S P]
    {F : Type w} [AddCommGroup F] [Module S F]
    (i : P →ₗ[S] F) (s : F →ₗ[S] P) (hs : s.comp i = LinearMap.id) :
    IsIdempotentElem (i.comp s) := by
  -- The split relation collapses the middle composite in the square of the projector.
  rw [IsIdempotentElem]
  ext x
  have hmid : s (i (s x)) = s x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs (s x)
  exact congrArg i hmid

/-- Helper for Lemma 10.77.5: a projective quotient module is the range of an idempotent on its
canonical free cover `Pbar →₀ (R ⧸ I)`. -/
lemma projective_split_projector_on_canonical_free_cover
    (hPbar : Module.Projective (R ⧸ I) Pbar) :
    ∃ (pbar : Module.End (R ⧸ I) (Pbar →₀ (R ⧸ I))),
      IsIdempotentElem pbar ∧ Nonempty (Pbar ≃ₗ[R ⧸ I] LinearMap.range pbar) := by
  let πbar : (Pbar →₀ (R ⧸ I)) →ₗ[R ⧸ I] Pbar :=
    Finsupp.linearCombination (R ⧸ I) (id : Pbar → Pbar)
  obtain ⟨ιbar, hsplit⟩ :=
    (Module.projective_def' (R := R ⧸ I) (P := Pbar)).1 hPbar
  refine ⟨ιbar.comp πbar, ?_, ?_⟩
  · -- The splitting turns the canonical free-cover endomorphism into a projector.
    exact
      split_projector_isIdempotentElem
        (S := R ⧸ I) (P := Pbar) (F := Pbar →₀ (R ⧸ I)) ιbar πbar hsplit
  · -- The split summand is linearly equivalent to the range of its projector.
    exact
      projective_summand_linearEquiv_range_projector
        (S := R ⧸ I) (P := Pbar) (F := Pbar →₀ (R ⧸ I)) ιbar πbar hsplit

/-- Helper for Lemma 10.77.5: under a same-universe smallness hypothesis on `R`, a projective
`R ⧸ I`-module is the range of an idempotent on a free `R ⧸ I`-module in `Type v`. -/
lemma exists_small_free_projector_of_projective [Small.{v} R]
    (hPbar : Module.Projective (R ⧸ I) Pbar) :
    ∃ (Fbar : Type v) (_ : AddCommGroup Fbar) (_ : Module (R ⧸ I) Fbar)
      (_ : Module.Free (R ⧸ I) Fbar) (pbar : Module.End (R ⧸ I) Fbar),
      IsIdempotentElem pbar ∧ Nonempty (Pbar ≃ₗ[R ⧸ I] LinearMap.range pbar) := by
  obtain ⟨Fbar, hFbarAdd, hFbarModule, hFbarFree, i, s, hs⟩ :=
    (Module.Projective.iff_split' (R := R ⧸ I) (P := Pbar)).1 hPbar
  letI : AddCommMonoid Fbar := hFbarAdd
  letI : Module (R ⧸ I) Fbar := hFbarModule
  letI : Module.Free (R ⧸ I) Fbar := hFbarFree
  letI : AddCommGroup Fbar := Module.addCommMonoidToAddCommGroup (R ⧸ I) (M := Fbar)
  refine ⟨Fbar, inferInstance, inferInstance, inferInstance, i.comp s, ?_, ?_⟩
  · -- The projector associated to a split summand is idempotent.
    simpa using
      split_projector_isIdempotentElem (S := R ⧸ I) (P := Pbar) (F := Fbar) i s hs
  · -- The original projective module is linearly equivalent to the projector range.
    simpa using
      projective_summand_linearEquiv_range_projector
        (S := R ⧸ I) (P := Pbar) (F := Fbar) i s hs

/-- Helper for Lemma 10.77.5: for the image of an idempotent projector, ambient membership in
`I • ⊤` is equivalent to intrinsic membership in `I • ⊤` on the image. -/
lemma ideal_smul_top_comap_projector_range_eq
    (p : Module.End R (Pbar →₀ R))
    (hp : IsIdempotentElem p) :
    Submodule.comap (LinearMap.range p).subtype (I • (⊤ : Submodule R (Pbar →₀ R))) =
      I • (⊤ : Submodule R (LinearMap.range p)) := by
  let hpProj : LinearMap.IsProj (LinearMap.range p) p :=
    LinearMap.IsIdempotentElem.isProj_range _ hp
  refine le_antisymm ?_ ?_
  · intro x hx
    -- Apply the retraction of the projector range to move ambient `I`-multiples back into the
    -- range itself.
    have hx' : x.1 ∈ I • (⊤ : Submodule R (Pbar →₀ R)) := hx
    have hcod :
        hpProj.codRestrict x.1 ∈ I • (⊤ : Submodule R (LinearMap.range p)) := by
      exact (Submodule.smul_top_le_comap_smul_top I hpProj.codRestrict) hx'
    simpa using hcod
  · -- The subtype inclusion obviously sends intrinsic `I`-multiples to ambient ones.
    exact Submodule.smul_top_le_comap_smul_top I (LinearMap.range p).subtype

/-- Helper for Lemma 10.77.5: if `x` lies in the image of the corrected projector `p`, then its
coefficientwise reduction lies in the image of the quotient projector `pbar`. -/
lemma quotient_map_mem_range_of_mem_projector_range
    (p : Module.End R (Pbar →₀ R))
    (pbar : Module.End (R ⧸ I) (Pbar →₀ (R ⧸ I)))
    (hpq :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp p = (pbar.restrictScalars R).comp qF)
    {x : Pbar →₀ R} (hx : x ∈ LinearMap.range p) :
    finsupp_quotientMapLinear (R := R) (I := I) Pbar x ∈ LinearMap.range (pbar.restrictScalars R) := by
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hpq' : qF.comp p = (pbar.restrictScalars R).comp qF := hpq
  rcases hx with ⟨y, rfl⟩
  -- The intertwining relation identifies `qF (p y)` with `pbar (qF y)`.
  refine ⟨qF y, ?_⟩
  simpa [LinearMap.comp_apply] using (congrArg (fun f => f y) hpq').symm

/-- Helper for Lemma 10.77.5: the reduction map from `range p` to `range pbar` is surjective. -/
lemma restricted_range_reduction_surjective
    (p : Module.End R (Pbar →₀ R))
    (pbar : Module.End (R ⧸ I) (Pbar →₀ (R ⧸ I)))
    (hpq :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp p = (pbar.restrictScalars R).comp qF) :
    let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
      finsupp_quotientMapLinear (R := R) (I := I) Pbar
    let g : LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) :=
      show LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) from
        LinearMap.codRestrict (LinearMap.range (pbar.restrictScalars R))
          (qF.comp (LinearMap.range p).subtype : LinearMap.range p →ₗ[R] Pbar →₀ (R ⧸ I))
          (fun x : LinearMap.range p =>
            quotient_map_mem_range_of_mem_projector_range
              (R := R) (I := I) (Pbar := Pbar) p pbar hpq (x := x.1) x.2)
    Function.Surjective g := by
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hmem :
      ∀ x : LinearMap.range p,
        (qF.comp (LinearMap.range p).subtype) x ∈ LinearMap.range (pbar.restrictScalars R) := by
    intro x
    simpa [LinearMap.comp_apply] using
      quotient_map_mem_range_of_mem_projector_range
        (R := R) (I := I) (Pbar := Pbar) p pbar hpq (x := x.1) x.2
  let g : LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) :=
    show LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) from
      LinearMap.codRestrict (LinearMap.range (pbar.restrictScalars R))
        (qF.comp (LinearMap.range p).subtype : LinearMap.range p →ₗ[R] Pbar →₀ (R ⧸ I)) hmem
  have hpq' : qF.comp p = (pbar.restrictScalars R).comp qF := hpq
  have hqF : Function.Surjective qF :=
    finsupp_quotientMap_surjective (R := R) (I := I) Pbar
  change ∀ y : LinearMap.range (pbar.restrictScalars R), ∃ x : LinearMap.range p, g x = y
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨z, rfl⟩
  rcases hqF z with ⟨x, rfl⟩
  refine ⟨⟨p x, ⟨x, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  -- The textbook preimage is `p x`; its image reduces to `pbar (qF x)`.
  change qF (p x) = pbar (qF x)
  simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hpq'

/-- Helper for Lemma 10.77.5: the kernel of the restricted reduction map on `range p` is exactly
`I • ⊤`. -/
lemma ker_restricted_range_reduction_eq_ideal_smul_top
    (p : Module.End R (Pbar →₀ R))
    (hp : IsIdempotentElem p)
    (pbar : Module.End (R ⧸ I) (Pbar →₀ (R ⧸ I)))
    (hpq :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp p = (pbar.restrictScalars R).comp qF) :
    let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
      finsupp_quotientMapLinear (R := R) (I := I) Pbar
    let g : LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) :=
      show LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) from
        LinearMap.codRestrict (LinearMap.range (pbar.restrictScalars R))
          (qF.comp (LinearMap.range p).subtype : LinearMap.range p →ₗ[R] Pbar →₀ (R ⧸ I))
          (fun x : LinearMap.range p =>
            quotient_map_mem_range_of_mem_projector_range
              (R := R) (I := I) (Pbar := Pbar) p pbar hpq (x := x.1) x.2)
    LinearMap.ker g = I • (⊤ : Submodule R (LinearMap.range p)) := by
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hmem :
      ∀ x : LinearMap.range p,
        (qF.comp (LinearMap.range p).subtype) x ∈ LinearMap.range (pbar.restrictScalars R) := by
    intro x
    simpa [LinearMap.comp_apply] using
      quotient_map_mem_range_of_mem_projector_range
        (R := R) (I := I) (Pbar := Pbar) p pbar hpq (x := x.1) x.2
  let g : LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) :=
    show LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) from
      LinearMap.codRestrict (LinearMap.range (pbar.restrictScalars R))
        (qF.comp (LinearMap.range p).subtype : LinearMap.range p →ₗ[R] Pbar →₀ (R ⧸ I)) hmem
  have hgker :
      LinearMap.ker g = LinearMap.ker (qF.comp (LinearMap.range p).subtype) := by
    -- Codomain restriction does not change the kernel.
    simpa [g] using
      (LinearMap.ker_codRestrict (LinearMap.range (pbar.restrictScalars R))
        (qF.comp (LinearMap.range p).subtype) hmem)
  calc
    LinearMap.ker g = LinearMap.ker (qF.comp (LinearMap.range p).subtype) := hgker
    _ = Submodule.comap (LinearMap.range p).subtype (LinearMap.ker qF) := by
      rw [LinearMap.ker_comp]
    _ = Submodule.comap (LinearMap.range p).subtype (I • (⊤ : Submodule R (Pbar →₀ R))) := by
      rw [finsupp_quotientMap_ker_eq_ideal_smul_top (R := R) (I := I) (ι := Pbar)]
    _ = I • (⊤ : Submodule R (LinearMap.range p)) := by
      exact ideal_smul_top_comap_projector_range_eq (R := R) (I := I) (Pbar := Pbar) p hp

/-- Helper for Lemma 10.77.5: the image of the corrected projector is the large projective lift,
and its quotient modulo `I` is linearly equivalent to `Pbar`. -/
lemma projective_range_lift_with_quotient_equiv_large
    (p : Module.End R (Pbar →₀ R))
    (hp : IsIdempotentElem p)
    (pbar : Module.End (R ⧸ I) (Pbar →₀ (R ⧸ I)))
    (hpq :
      let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
        finsupp_quotientMapLinear (R := R) (I := I) Pbar
      qF.comp p = (pbar.restrictScalars R).comp qF)
    (hPbar_range : Nonempty (Pbar ≃ₗ[R ⧸ I] LinearMap.range pbar)) :
    ∃ e :
        ((LinearMap.range p) ⧸ (I • (⊤ : Submodule R (LinearMap.range p)))) ≃ₗ[R ⧸ I] Pbar,
      Module.Projective R (LinearMap.range p) := by
  have hprojective : Module.Projective R (LinearMap.range p) := by
    exact projective_of_idempotent_range (R := R) p hp
  let qF : (Pbar →₀ R) →ₗ[R] Pbar →₀ (R ⧸ I) :=
    finsupp_quotientMapLinear (R := R) (I := I) Pbar
  have hmem :
      ∀ x : LinearMap.range p,
        (qF.comp (LinearMap.range p).subtype) x ∈ LinearMap.range (pbar.restrictScalars R) := by
    intro x
    simpa [qF, LinearMap.comp_apply] using
      quotient_map_mem_range_of_mem_projector_range
        (R := R) (I := I) (Pbar := Pbar) p pbar hpq (x := x.1) x.2
  let g : LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) :=
    show LinearMap.range p →ₗ[R] LinearMap.range (pbar.restrictScalars R) from
      LinearMap.codRestrict (LinearMap.range (pbar.restrictScalars R))
        (qF.comp (LinearMap.range p).subtype : LinearMap.range p →ₗ[R] Pbar →₀ (R ⧸ I))
        hmem
  have hsurj : Function.Surjective g := by
    -- Surjectivity descends from the coefficientwise quotient map on the ambient free module.
    simpa [qF, g] using
      restricted_range_reduction_surjective
        (R := R) (I := I) (Pbar := Pbar) p pbar hpq
  have hker :
      LinearMap.ker g = I • (⊤ : Submodule R (LinearMap.range p)) := by
    -- The only relations introduced by reduction are the `I`-multiples inside the range.
    simpa [qF, g] using
      ker_restricted_range_reduction_eq_ideal_smul_top
        (R := R) (I := I) (Pbar := Pbar) p hp pbar hpq
  let eR :
      ((LinearMap.range p) ⧸ (I • (⊤ : Submodule R (LinearMap.range p)))) ≃ₗ[R]
        LinearMap.range (pbar.restrictScalars R) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)
  have eRange :
      LinearMap.range (pbar.restrictScalars R) ≃ₗ[R] LinearMap.range pbar := by
    -- Forgetting from `R ⧸ I` to `R` does not change the underlying range.
    simpa [LinearMap.range_restrictScalars] using
      ((Submodule.restrictScalarsEquiv (S := R) (p := LinearMap.range pbar)).restrictScalars R)
  rcases hPbar_range with ⟨ePbar⟩
  refine ⟨?_, hprojective⟩
  -- Compose the first-isomorphism identification with the stored quotient-side splitting.
  exact
    linearEquiv_over_quotient (R := R) (I := I) (eR.trans eRange) ≪≫ₗ
      ePbar.symm

/-- Helper for Lemma 10.77.5: once a large witness is known to be small in universe `v`, shrinking
its carrier transports both projectivity and the quotient equivalence into `Type v`. -/
lemma projective_range_descent_of_small
    {Q : Type _} [AddCommGroup Q] [Module R Q] [Small.{v} Q]
    (hQ : Module.Projective R Q)
    (eQ : (Q ⧸ (I • (⊤ : Submodule R Q))) ≃ₗ[R ⧸ I] Pbar) :
    ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P)
      (_ : (P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar), Module.Projective R P := by
  let eShrink : Shrink.{v} Q ≃ₗ[R] Q := Shrink.linearEquiv R Q
  have hmap :
      (I • (⊤ : Submodule R (Shrink.{v} Q))).map (eShrink : Shrink.{v} Q →ₗ[R] Q) =
        I • (⊤ : Submodule R Q) := by
    -- The shrink equivalence preserves both the top submodule and ideal scalar multiplication.
    simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 eShrink.surjective] using
      (Submodule.map_smul'' (I := I) (N := (⊤ : Submodule R (Shrink.{v} Q)))
        (f := (eShrink : Shrink.{v} Q →ₗ[R] Q)))
  let eQuotR :
      ((Shrink.{v} Q) ⧸ (I • (⊤ : Submodule R (Shrink.{v} Q)))) ≃ₗ[R]
        (Q ⧸ (I • (⊤ : Submodule R Q))) :=
    Submodule.Quotient.equiv
      (I • (⊤ : Submodule R (Shrink.{v} Q)))
      (I • (⊤ : Submodule R Q))
      eShrink
      hmap
  let eP :
      ((Shrink.{v} Q) ⧸ (I • (⊤ : Submodule R (Shrink.{v} Q)))) ≃ₗ[R ⧸ I] Pbar :=
    linearEquiv_over_quotient (R := R) (I := I) eQuotR ≪≫ₗ eQ
  have hShrink : Module.Projective R (Shrink.{v} Q) := by
    -- Projectivity is invariant under linear equivalence.
    exact Module.Projective.of_equiv' (M := Q) eShrink.symm
  refine ⟨Shrink.{v} Q, inferInstance, inferInstance, eP, hShrink⟩

/- 
Domain triage:
- primary domain: projective modules over a quotient ring and lifting across a nilpotent ideal;
- sampled owner-style declarations of the same kind:
  `Module.Projective`,
  `Module.Projective.iff_split`,
  `Module.projective_lifting_property`,
  `RingHom.exists_isIdempotentElem_eq_of_ker_isNilpotent`;
- owner abstraction: `Module.Projective R P`;
- primitive data: the quotient module `Pbar` over `R ⧸ I` and the nilpotent ideal `I`;
- derived API: existence of a projective `R`-module whose reduction modulo `I` is linearly
  equivalent to `Pbar`.

This item remains `source-facing`: the theorem genuinely constructs a lift, so the quotient
comparison stays as an explicit witness. The refinement here is only to expose that witness
directly, instead of hiding it behind `Nonempty`.
-/
/-- Lemma 10.77.5: a projective `R ⧸ I`-module lifts across a nilpotent ideal `I` to a
projective `R`-module whose quotient modulo `I` is linearly isomorphic to the original module. -/
-- Proof sketch: choose a free `R ⧸ I`-module containing `Pbar` as a direct summand, lift the
-- corresponding projector to an endomorphism of the free `R`-module on the same basis, and use
-- the nilpotence of `I` together with Lemma 10.32.7 to correct this lift to an idempotent. The
-- image of the resulting idempotent is the desired projective lift.
@[stacks 07LV]
theorem exists_projective_lift_of_projective_quotient_of_isNilpotent
    (hI : IsNilpotent I)
    (hPbar : Module.Projective (R ⧸ I) Pbar) :
    ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : Module R P)
      (_ : (P ⧸ (I • ⊤ : Submodule R P)) ≃ₗ[R ⧸ I] Pbar), Module.Projective R P := by
  -- Route correction: keep the source proof on the canonical free cover `Pbar →₀ (R ⧸ I)` and
  -- its lift `Pbar →₀ R`, rather than detouring through an abstract small free module.
  obtain ⟨pbar, hpbar, hPbar_range⟩ :=
    projective_split_projector_on_canonical_free_cover
      (R := R) (I := I) (Pbar := Pbar) hPbar
  have hpbarR :
      (pbar.restrictScalars R).comp (pbar.restrictScalars R) = pbar.restrictScalars R := by
    -- The quotient-side projector stays idempotent after restricting scalars to `R`.
    simpa [IsIdempotentElem, pow_two, Module.End.mul_eq_comp] using
      congrArg (LinearMap.restrictScalars R) (show pbar * pbar = pbar from hpbar)
  obtain ⟨p0, hp0⟩ :=
    lift_projector_across_nilpotent_quotient_on_finsupp
      (R := R) (I := I) (Pbar := Pbar) pbar
  obtain ⟨p, hp, hpq⟩ :=
    idempotent_correction_of_lifted_projector
      (R := R) (I := I) (Pbar := Pbar) hI (pbar.restrictScalars R) hpbarR p0 hp0
  obtain ⟨e, hprojective⟩ :=
    projective_range_lift_with_quotient_equiv_large
      (R := R) (I := I) (Pbar := Pbar) p hp pbar hpq hPbar_range
  refine ⟨LinearMap.range p, inferInstance, inferInstance, e, hprojective⟩

end
