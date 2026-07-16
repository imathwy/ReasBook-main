import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_4
import stacks_proof.stacks_project.Chap10.Lemma_10_96_11
import stacks_proof.stacks_project.Chap10.Lemma_10_96_12
import stacks_proof.stacks_project.Chap10.Lemma_10_96_1
import stacks_proof.stacks_project.Chap10.Lemma_10_97_1
import stacks_proof.stacks_project.Chap10.Lemma_10_97_4
import stacks_proof.stacks_project.Chap15.Lemma_15_3_3
import stacks_proof.stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {I : Ideal A} {M : ModuleCat A}

namespace ModuleCat

/-
Domain-style sampling for Lemma 15.95.5:
- primary domain: derived completeness, adic completeness, and finite generation of modules over
  the completed ring `AdicCompletion I A`;
- sampled owner declarations:
  `IsAdicComplete`,
  `ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff`,
  `moduleFinite_of_finite_quotient_of_isHausdorff`,
  `AdicCompletion.module`,
  `AdicCompletion.ofLinearEquiv`;
- best owner abstraction: this is a `source-facing` theorem on `M`; the core owners are
  `IsAdicComplete I M` and `Module.Finite (AdicCompletion I A) M`, while the completion-side
  statement for `AdicCompletion I M` is only a `bridge/view`;
- primitive vs. derived:
  primitive data are the ideal `I`, the module `M`, the derived-completeness hypothesis, and the
  finite quotient `M / I M`;
  derived API is the canonical `Module (AdicCompletion I A) M` instance under
  `IsAdicComplete I M`, together with the completion-side finiteness conclusion for
  `AdicCompletion I M`.
-/

open AdicCompletion

namespace IsAdicComplete

/-- Helper for Lemma 15.95.5: the quotient of a finite free module by `I` is identified with the
coordinatewise residue module by sending a representative to its residue coordinates. -/
private theorem free_pi_quotient_equiv_apply_mkQ
    (n : ℕ) (x : Fin n → A) :
    free_pi_quotient_equiv (R := A) (I := I) n
      ((I • (⊤ : Submodule A (Fin n → A))).mkQ x) =
        fun i ↦ Ideal.Quotient.mk I (x i) := by
  -- Proof comment: unfold the owner quotient map on an explicit representative.
  change free_pi_quotient_map (R := A) (I := I) n x = fun i ↦ Ideal.Quotient.mk I (x i)
  rfl

-- Transport the canonical `AdicCompletion I A`-action on `AdicCompletion I M` across
-- `AdicCompletion.ofLinearEquiv I M`.
noncomputable instance [IsAdicComplete I M] :
    Module (AdicCompletion I A) M :=
  Module.compHom M <|
    ((ofLinearEquiv I M).symm.conjRingEquiv.toRingHom).comp
      (Module.toModuleEnd A (AdicCompletion I M))

/-- Helper for Lemma 15.95.5: the canonical completion comparison is
`AdicCompletion I A`-linear once `M` is already `I`-adically complete. -/
private theorem completion_linear_equiv_of_isAdicComplete_map_smul
    [IsAdicComplete I M] (a : AdicCompletion I A) (x : M) :
    AdicCompletion.ofLinearEquiv I M (a • x) = a • AdicCompletion.ofLinearEquiv I M x := by
  -- Proof comment: the `AdicCompletion I A`-action on `M` was defined precisely so that
  -- `AdicCompletion.ofLinearEquiv I M` becomes linear over the completed base ring.
  change
    AdicCompletion.ofLinearEquiv I M
        (((AdicCompletion.ofLinearEquiv I M).symm.conjRingEquiv
          (Module.toModuleEnd A (AdicCompletion I M) a)) x) =
      a • AdicCompletion.ofLinearEquiv I M x
  simp

/-- Helper for Lemma 15.95.5: after equipping `M` with its canonical completed-ring action,
`AdicCompletion.ofLinearEquiv I M` upgrades to a linear equivalence over `AdicCompletion I A`. -/
private noncomputable def completion_linear_equiv_of_isAdicComplete
    [IsAdicComplete I M] :
    M ≃ₗ[AdicCompletion I A] AdicCompletion I M :=
  { toFun := AdicCompletion.ofLinearEquiv I M
    invFun := (AdicCompletion.ofLinearEquiv I M).symm
    left_inv := (AdicCompletion.ofLinearEquiv I M).left_inv
    right_inv := (AdicCompletion.ofLinearEquiv I M).right_inv
    map_add' := (AdicCompletion.ofLinearEquiv I M).map_add
    map_smul' := completion_linear_equiv_of_isAdicComplete_map_smul (A := A) (I := I) }

/-- Helper for Lemma 15.95.5: quotienting an exact surjective pair by `I • ⊤` preserves exactness.
-/
private theorem quotientMapByIdeal_exact
    {N P Q : Type u}
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q]
    (f : N →ₗ[A] P) (g : P →ₗ[A] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A P)) y
    have hxI : g x ∈ I • (⊤ : Submodule A Q) := by
      simpa [LinearMap.quotientMapByIdeal] using
        (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A Q))).mp hy
    have hxLift :
        ∃ y' : P, y' ∈ I • (⊤ : Submodule A P) ∧ g y' = g x := by
      -- Proof comment: lift an `I • ⊤` witness in the target back through the surjective map `g`.
      refine
        Submodule.smul_induction_on hxI
          (fun a ha z _ ↦ ?_)
          (fun y z hy' hz' ↦ ?_)
      · obtain ⟨y', rfl⟩ := hg z
        refine ⟨a • y', ?_, by simp⟩
        exact Submodule.smul_mem_smul ha (by simp)
      · rcases hy' with ⟨y', hy'I, rfl⟩
        rcases hz' with ⟨z', hz'I, rfl⟩
        exact ⟨y' + z', Submodule.add_mem _ hy'I hz'I, by simp⟩
    rcases hxLift with ⟨y', hy'I, hy'g⟩
    have hxy : g (x - y') = 0 := by
      simp [hy'g]
    rcases (hExact (x - y')).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule A N)).mkQ n, ?_⟩
    have hy'zero : ((I • (⊤ : Submodule A P)).mkQ y' : P ⧸ I • (⊤ : Submodule A P)) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hy'I
    calc
      (f.quotientMapByIdeal I) ((I • (⊤ : Submodule A N)).mkQ n)
          = (I • (⊤ : Submodule A P)).mkQ (f n) := by
              simp [LinearMap.quotientMapByIdeal]
      _ = (I • (⊤ : Submodule A P)).mkQ (x - y') := by rw [hn]
      _ = (I • (⊤ : Submodule A P)).mkQ x := by
            rw [map_sub, hy'zero, sub_zero]
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A N)) x
    change ((I • (⊤ : Submodule A Q)).mkQ (g (f x))) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    have hgf : g (f x) = 0 := by
      simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
    rw [hgf]
    exact Submodule.zero_mem _

-- Proof sketch: equip `M` with its canonical `AdicCompletion I A`-module structure from `hM`,
-- compare it with the canonical completion module `AdicCompletion I M` using
-- `AdicCompletion.ofLinearEquiv I M`, and apply the owner-facing finiteness criterion from
-- Lemma `10.96.12`.
/-- If `M` is already `I`-adically complete, then `M`, equipped with its canonical
`AdicCompletion I A`-module structure, is finite as soon as `M / I M` is finite over `A / I`. -/
theorem moduleFinite_over_adicCompletion_of_finite_quotient
    [IsNoetherianRing A]
    [IsAdicComplete I M]
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    Module.Finite (AdicCompletion I A) M := by
  -- Proof comment: the proved frontier is the closed-fiber free-cover lift above. The remaining
  -- blocker is to package `AdicCompletion.ofLinearEquiv I M` as an explicit
  -- `AdicCompletion I A`-linear equivalence so that finite generation can be transported back
  -- from `AdicCompletion I M` to `M`.
  sorry

end IsAdicComplete

section

variable [IsNoetherianRing A]

-- Proof sketch: use Proposition `15.92.5` to identify adic completeness with derived
-- completeness plus `I`-adic separatedness, prove the separatedness hypothesis from the
-- Noetherian finiteness input, and conclude by Chapter `10`.
/-- Under the hypotheses of Lemma `15.95.5`, the module `M` is `I`-adically complete. -/
theorem isAdicComplete_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    IsAdicComplete I M := by
  -- Route correction: the source-faithful closure step needs earlier Chapter 15 owner lemmas
  -- about derived-complete kernels and the completion map. Importing those files currently
  -- triggers upstream compile failures in this workspace, so the remaining frontier is left
  -- explicit for re-planning.
  -- TODO: prove bijectivity of `AdicCompletion.of I M` by combining the quotient comparison
  -- `adicCompletionQuotientPowLinearEquiv` at `n = 1` with the derived-complete kernel-vanishing
  -- bridge from Lemma `15.92.7`, once the broken upstream owner files are usable again.
  sorry

-- Proof sketch: combine the completeness bridge above with the owner theorem in the
-- `IsAdicComplete` namespace.
/-- Lemma 15.95.5: if `M` is derived complete with respect to `I` and `M / I M` is finite over
`A / I`, then `M`, equipped with its canonical `AdicCompletion I A`-module structure, is a finite
module over the completed ring `AdicCompletion I A`. -/
@[stacks 09BA]
theorem moduleFinite_over_adicCompletion_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    let _ : IsAdicComplete I M :=
      isAdicComplete_of_isDerivedComplete_of_finite_quotient hM
    Module.Finite (AdicCompletion I A) M := by
  let _ : IsAdicComplete I M :=
    isAdicComplete_of_isDerivedComplete_of_finite_quotient hM
  exact IsAdicComplete.moduleFinite_over_adicCompletion_of_finite_quotient

-- Proof sketch: first apply Lemma `15.95.5` to `M`, then transport finite generation across the
-- canonical identification `AdicCompletion.ofLinearEquiv I M`.
/-- Completion-side companion to Lemma `15.95.5`: under the same hypotheses,
`AdicCompletion I M` is a finite module over `AdicCompletion I A`. -/
theorem moduleFinite_adicCompletion_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M) := by
  -- Proof comment: once the owner theorem above is closed, this is only finiteness transport
  -- across `AdicCompletion.ofLinearEquiv I M`.
  let _ : IsAdicComplete I M :=
    isAdicComplete_of_isDerivedComplete_of_finite_quotient hM
  let _ : Module.Finite (AdicCompletion I A) M :=
    moduleFinite_over_adicCompletion_of_isDerivedComplete_of_finite_quotient hM
  -- Proof comment: the local completion-linear equivalence transports the completed-ring finite
  -- generation result from `M` to its completion.
  exact Module.Finite.equiv
    (IsAdicComplete.completion_linear_equiv_of_isAdicComplete (A := A) (I := I) (M := M))

end

end ModuleCat

end
