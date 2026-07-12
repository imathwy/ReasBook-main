import StacksProject_2024.Chap10.Lemma_10_99_16.PrincipalQuotients

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Pointwise
open scoped TensorProduct

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Helper for Lemma 10.99.16: if `J • M = M`, then after localizing away from `f` the image ideal
still acts surjectively on `M[1/f]`. -/
lemma away_localized_ideal_smul_top_eq_top
    (f : A) (J : Ideal A) (hJ : J • (⊤ : Submodule A M) = ⊤) :
    (Ideal.map (algebraMap A (Localization.Away f)) J) •
      (⊤ : Submodule (Localization.Away f) (LocalizedModule.Away f M)) = ⊤ := by
  refine eq_top_iff.2 ?_
  intro x _
  induction x using LocalizedModule.induction_on with
  | h m s =>
      have hm : m ∈ J • (⊤ : Submodule A M) := by simpa [hJ]
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro r hr y hy
        have hr' :
            algebraMap A (Localization.Away f) r ∈
              Ideal.map (algebraMap A (Localization.Away f)) J :=
          Ideal.mem_map_of_mem _ hr
        have hy' :
            LocalizedModule.mk y s ∈
              (⊤ : Submodule (Localization.Away f) (LocalizedModule.Away f M)) := by
          simp
        simpa [LocalizedModule.smul'_mk] using
          (Submodule.smul_mem_smul hr' hy' :
            algebraMap A (Localization.Away f) r • LocalizedModule.mk y s ∈
              (Ideal.map (algebraMap A (Localization.Away f)) J) •
                (⊤ : Submodule (Localization.Away f) (LocalizedModule.Away f M)))
      · intro y z hy hz
        have hadd :
            LocalizedModule.mk y s + LocalizedModule.mk z s =
              LocalizedModule.mk (y + z) s := by
          calc
            LocalizedModule.mk y s + LocalizedModule.mk z s
                = LocalizedModule.mk ((s : A) • y + (s : A) • z) (s * s) := by
                    simpa [Submonoid.smul_def] using
                      (LocalizedModule.mk_add_mk (m1 := y) (m2 := z) (s1 := s) (s2 := s))
            _ = LocalizedModule.mk ((s : A) • (y + z)) (s * s) := by
                  simp [smul_add]
            _ = LocalizedModule.mk (y + z) s := by
                  simpa using LocalizedModule.mk_cancel_common_left s s (y + z)
        rw [← hadd]
        exact add_mem hy hz

/-- Helper for Lemma 10.99.16: if `J • M = M`, then after quotienting by `fM` the image ideal in
`A / (f)` still acts surjectively on `M / fM`. -/
lemma quotient_ideal_smul_top_eq_top
    (f : A) (J : Ideal A) (hJ : J • (⊤ : Submodule A M) = ⊤) :
    (Ideal.map (algebraMap A (A ⧸ Ideal.span ({f} : Set A))) J) •
      (⊤ : Submodule (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M)) = ⊤ := by
  let hQset : Module.IsTorsionBySet A (QuotSMulTop f M) (Ideal.span ({f} : Set A)) :=
    quotSMulTop_isTorsionBySet_span_singleton (A := A) (M := M) f
  let _ : IsScalarTower A (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M) :=
    Module.IsTorsionBySet.isScalarTower
      (R := A) (M := QuotSMulTop f M) (I := Ideal.span ({f} : Set A)) hQset
  rw [← (Submodule.restrictScalars_injective
    A (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M)).eq_iff]
  -- Proof comment: identify reduction modulo `fM` with the quotient map on `J • M`, then rewrite
  -- the induced `A`-action through the canonical `A / (f)`-module structure.
  calc
    ((Ideal.map (algebraMap A (A ⧸ Ideal.span ({f} : Set A))) J) •
        (⊤ : Submodule (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M))).restrictScalars A
        = (J • (⊤ : Submodule A M)).map
            (Submodule.mkQ (f • (⊤ : Submodule A M))) := by
              symm
              calc
                (J • (⊤ : Submodule A M)).map
                    (Submodule.mkQ (f • (⊤ : Submodule A M)))
                    = J • (⊤ : Submodule A (QuotSMulTop f M)) := by
                        simp [QuotSMulTop, Submodule.map_smul'', Submodule.range_mkQ]
                _ = (((Ideal.map (algebraMap A (A ⧸ Ideal.span ({f} : Set A))) J) •
                      (⊤ : Submodule (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M)))
                        ).restrictScalars A := by
                      symm
                      simpa [Ideal.Quotient.algebraMap_eq] using
                        (Ideal.smul_restrictScalars
                          (R := A) (S := A ⧸ Ideal.span ({f} : Set A)) (M := QuotSMulTop f M) J
                          (⊤ : Submodule (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M)))
    _ = ⊤ := by
          simpa [hJ]

end
