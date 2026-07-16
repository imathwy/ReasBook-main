import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_12

universe u

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/-- Helper for Lemma 10.97.5: after restricting scalars to `R`, the kernel of the algebra-valued
stage-one evaluation map agrees with the kernel of the underlying linear evaluation map. -/
lemma ker_evalOneₐ_restrictScalars_eq_ker_eval :
    (((RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom : Ideal (AdicCompletion I R)) :
        Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) =
      (AdicCompletion.eval I R 1).ker := by
  have hle₁ : I ^ 1 ≤ I ^ 1 • (⊤ : Submodule R R) := by
    simpa [pow_one, Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top I).symm
  have hle₂ : I ^ 1 • (⊤ : Submodule R R) ≤ I ^ 1 := by
    simpa [pow_one, Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top I)
  -- Compare the two kernels by transporting vanishing across the quotient identifications.
  ext x
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    have hfactor :
        Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) = 0 := by
      calc
        Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) =
            (AdicCompletion.evalOneₐ I) x := AdicCompletion.factorₐ_evalₐ_one (I := I) x
        _ = 0 := hx
    have hx' : (AdicCompletion.evalₐ I 1) x = 0 := by
      have hf :
          Function.Injective
            (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) : R ⧸ I ^ 1 →+* R ⧸ I) := by
        let e : (R ⧸ I ^ 1) ≃+* (R ⧸ I) := (Ideal.quotientEquivAlgOfEq R (by simp)).toRingEquiv
        simpa [e, pow_one] using e.injective
      apply hf
      simpa using hfactor
    calc
      (AdicCompletion.eval I R 1) x =
          Ideal.Quotient.factor hle₁ ((AdicCompletion.evalₐ I 1) x) := by
            symm
            exact AdicCompletion.factor_evalₐ_eq_eval (I := I) (n := 1) x hle₁
      _ = 0 := by simpa [hx']
  · intro hx
    have hx' : (AdicCompletion.evalₐ I 1) x = 0 := by
      calc
        (AdicCompletion.evalₐ I 1) x =
            Submodule.factor hle₂ ((AdicCompletion.eval I R 1) x) := by
              symm
              exact AdicCompletion.factor_eval_eq_evalₐ (I := I) (n := 1) x hle₂
        _ = 0 := by simpa [hx]
    calc
      (AdicCompletion.evalOneₐ I) x =
          Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) := by
            symm
            exact AdicCompletion.factorₐ_evalₐ_one (I := I) x
      _ = 0 := by simpa [hx']

/-- Helper for Lemma 10.97.5: the extended ideal on the completion is the kernel of the canonical
map to `R ⧸ I`. -/
lemma completion_ideal_eq_ker_evalOneA (hI : I.FG) :
    Ideal.map (algebraMap R (AdicCompletion I R)) I =
      RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom := by
  -- Reduce the ideal equality to the module-side kernel formula for adic completions.
  apply Submodule.restrictScalars_injective R (AdicCompletion I R) (AdicCompletion I R)
  calc
    (((Ideal.map (algebraMap R (AdicCompletion I R)) I : Ideal (AdicCompletion I R)) :
        Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) =
        I • (⊤ : Submodule R (AdicCompletion I R)) := by
          simpa [Ideal.smul_top_eq_map]
    _ = (AdicCompletion.eval I R 1).ker := by
      -- Finite generation identifies the first adic-step kernel with `I • ⊤`.
      simpa using (AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := R) (n := 1) hI)
    _ =
        (((RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom : Ideal (AdicCompletion I R)) :
          Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) := by
      -- The algebra-valued and linear stage-one evaluations have the same restricted kernel.
      symm
      exact ker_evalOneₐ_restrictScalars_eq_ker_eval (I := I)

/-- Helper for Lemma 10.97.5: the completion is complete for the adic topology of the extended
ideal. -/
lemma completion_ideal_isAdicComplete (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) := by
  -- Transport the owner completeness theorem across the standard map-ideal equivalence.
  have hmap :
      IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) ↔
        IsAdicComplete I (AdicCompletion I R) :=
    IsAdicComplete.map_algebraMap_iff I (AdicCompletion I R)
  exact hmap.2 (AdicCompletion.isAdicComplete hI)

variable [IsNoetherianRing (R ⧸ I)]

/-- Helper for Lemma 10.97.5: the quotient of the completion by the extended ideal is Noetherian
because it is canonically identified with `R ⧸ I`. -/
lemma completion_quotient_isNoetherianRing (hI : I.FG) :
    IsNoetherianRing ((AdicCompletion I R) ⧸ Ideal.map (algebraMap R (AdicCompletion I R)) I) := by
  let e :
      ((AdicCompletion I R) ⧸ RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom) ≃+* (R ⧸ I) :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := AdicCompletion.evalOneₐ I) (AdicCompletion.evalOneₐ_surjective I)).toRingEquiv
  have hquot :
      IsNoetherianRing
        ((AdicCompletion I R) ⧸ RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom) :=
    isNoetherianRing_of_ringEquiv (R ⧸ I) e.symm
  -- Rewrite the kernel quotient using the first-stage kernel description above.
  rw [completion_ideal_eq_ker_evalOneA (I := I) hI]
  exact hquot

end
