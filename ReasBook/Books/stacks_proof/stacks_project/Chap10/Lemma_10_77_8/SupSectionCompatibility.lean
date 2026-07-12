import StacksProject_2024.Chap10.Lemma_10_77_8.QuotientFreeCover

universe u v

namespace Chap10Lemma10778

open Chap10Lemma10778

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Helper for Chap10 Lemma 10 77 8: a class modulo `(I ⊔ J)F` whose image in `(I ⊔ J)P`
vanishes can be corrected to a class modulo `JF` whose image in `P / JP` is zero. -/
theorem existsModJLiftOfZeroImageInSupQuotient
    [(I ⊔ J).IsTwoSided]
    (uK : (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
    (huK :
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal (I ⊔ J)) uK = 0) :
    ∃ v : (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))),
      Submodule.factor
          (by
            simpa using
              (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                  J • (⊤ : Submodule R (P →₀ R)) ≤ (I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
          v = uK ∧
        ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal J) v = 0 := by
  let π : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let pK : Submodule R P := (I ⊔ J) • (⊤ : Submodule R P)
  let pFJ : Submodule R (P →₀ R) := J • (⊤ : Submodule R (P →₀ R))
  let pFK : Submodule R (P →₀ R) := (I ⊔ J) • (⊤ : Submodule R (P →₀ R))
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective pFK uK
  change (Submodule.mkQ pK) (π c) = 0 at huK
  have hπc : π c ∈ pK := by
    simpa using (Submodule.Quotient.eq pK).mp huK
  -- Correct the chosen representative inside `(I ⊔ J)F` until its image under the free cover
  -- vanishes exactly.
  obtain ⟨e, heFK, heπ⟩ :=
    exists_overlap_correction_in_sup_smul (R := R) (I := I) (J := J) (P := P)
      (c := c) (y := 0) (by simpa [pK, sub_eq_add_neg] using hπc)
  refine ⟨Submodule.mkQ pFJ (c - e), ?_, ?_⟩
  · apply (Submodule.Quotient.eq pFK).2
    have hneg : -e ∈ pFK := by
      simpa using pFK.neg_mem heFK
    have hsub : (c - e) - c = -e := by
      abel
    exact hsub ▸ hneg
  · change (Submodule.mkQ (J • (⊤ : Submodule R P))) (π (c - e)) = 0
    have hπzero : π (c - e) = 0 := by
      have heπ' : π e = π c := by
        simpa [π] using heπ
      calc
        π (c - e) = π c - π e := by
          simp [π]
        _ = π c - π c := by
          rw [heπ']
        _ = 0 := by
          simp
    simpa [hπzero]

set_option maxHeartbeats 400000 in
/-- Helper for Chap10 Lemma 10 77 8: projectivity of `P / JP` lifts the modulo-`K` section and the
modulo-`J` section to a single section modulo `J` compatible with both quotient maps. -/
theorem existsModJSectionCompatibleWithSupSection
    [(I ⊔ J).IsTwoSided]
    [Module (R ⧸ J) (P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)))]
    [Module (R ⧸ J) ((P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))]
    (qP :
      P ⧸ (J • (⊤ : Submodule R P)) →ₗ[R ⧸ J]
        P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)))
    (qF :
      (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))) →ₗ[R ⧸ J]
        (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
    (πJ :
      (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))) →ₗ[R ⧸ J]
        P ⧸ (J • (⊤ : Submodule R P)))
    (πK :
      (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))) →ₗ[R ⧸ J]
        P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)))
    (hq_π : πK.comp qF = qP.comp πJ)
    (fKJ :
      P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)) →ₗ[R ⧸ J]
        (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
    (hfKJ_section : πK.comp fKJ = LinearMap.id)
    (sJ :
      P ⧸ (J • (⊤ : Submodule R P)) →ₗ[R ⧸ J]
        (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))
    (hsJ : πJ.comp sJ = LinearMap.id)
    (hOverlap :
      ∀ uK : (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))),
        πK uK = 0 →
          ∃ v : (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))),
            qF v = uK ∧ πJ v = 0)
    [Module.Projective (R ⧸ J) (P ⧸ (J • (⊤ : Submodule R P)))] :
    ∃ gJ :
        P ⧸ (J • (⊤ : Submodule R P)) →ₗ[R ⧸ J]
          (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))),
      qF.comp gJ = fKJ.comp qP ∧
        πJ.comp gJ = LinearMap.id := by
  let T : Submodule (R ⧸ J)
      (((P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R)))) ×
        (P ⧸ (J • (⊤ : Submodule R P)))) :=
    { carrier := { z : (((P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R)))) ×
          (P ⧸ (J • (⊤ : Submodule R P)))) | πK z.1 = qP z.2 },
      zero_mem' := by
        change πK 0 = qP 0
        simp
      add_mem' := by
        intro x y hx hy
        change πK (x.1 + y.1) = qP (x.2 + y.2)
        calc
          πK (x.1 + y.1) = πK x.1 + πK y.1 := by
            simp
          _ = qP x.2 + qP y.2 := by
            rw [hx, hy]
          _ = qP (x.2 + y.2) := by
            simp
      smul_mem' := by
        intro c x hx
        change πK (c • x.1) = qP (c • x.2)
        calc
          πK (c • x.1) = c • πK x.1 := by
            simp
          _ = c • qP x.2 := by
            rw [hx]
          _ = qP (c • x.2) := by
            simp }
  have hq_mem :
      ∀ x : (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))),
        πK (qF x) = qP (πJ x) := by
    intro x
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hq_π x
  let q :
      ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R)))) →ₗ[R ⧸ J] T :=
    { toFun := fun x =>
        ⟨(qF x, πJ x), hq_mem x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp }
  have hq_surj : Function.Surjective q := by
    -- Route correction: keep the pullback-surjectivity proof local so Lean does not have to
    -- re-elaborate the large pullback subtype as a separate theorem type.
    intro t
    let δ := t.1.1 - qF (sJ t.1.2)
    have hsJ_apply : πJ (sJ t.1.2) = t.1.2 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hsJ t.1.2
    have hδ_zero : πK δ = 0 := by
      -- The defect vanishes after applying `πK`, so the overlap correction applies.
      calc
        πK δ = πK t.1.1 - πK (qF (sJ t.1.2)) := by
            simp [δ, map_sub]
        _ = qP t.1.2 - qP (πJ (sJ t.1.2)) := by
            rw [t.2, hq_mem]
        _ = qP t.1.2 - qP t.1.2 := by
            rw [hsJ_apply]
        _ = 0 := by
            simp
    obtain ⟨v, hvqF, hvπJ⟩ := hOverlap δ hδ_zero
    refine ⟨v + sJ t.1.2, ?_⟩
    apply Subtype.ext
    change (qF (v + sJ t.1.2), πJ (v + sJ t.1.2)) = (t.1.1, t.1.2)
    apply Prod.ext
    · -- The overlap correction fixes exactly the first-coordinate defect.
      calc
        qF (v + sJ t.1.2) = qF v + qF (sJ t.1.2) := by
            exact qF.map_add v (sJ t.1.2)
        _ = δ + qF (sJ t.1.2) := by
            rw [hvqF]
        _ = t.1.1 := by
            dsimp [δ]
            abel
    · -- The correction term has zero image in `P / JP`, so the second coordinate is unchanged.
      calc
        πJ (v + sJ t.1.2) = πJ v + πJ (sJ t.1.2) := by
            exact πJ.map_add v (sJ t.1.2)
        _ = 0 + t.1.2 := by
            rw [hvπJ, hsJ_apply]
        _ = t.1.2 := by
            simp
  let f' :
      (P ⧸ (J • (⊤ : Submodule R P))) →ₗ[R ⧸ J] T :=
    { toFun := fun x =>
        ⟨(fKJ (qP x), x), by
          -- The chosen modulo-`K` section lands in the pullback because it is a genuine section.
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun hfKJ_section (qP x)⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp }
  obtain ⟨gJ, hgJ⟩ := Module.projective_lifting_property q f' hq_surj
  refine ⟨gJ, ?_, ?_⟩
  · -- Project the lifted pullback identity to the modulo-`K` coordinate.
    refine DFunLike.ext _ _ fun x ↦ ?_
    have hx : q (gJ x) = f' x := LinearMap.congr_fun hgJ x
    exact congrArg Prod.fst (congrArg Subtype.val hx)
  · -- Project the lifted pullback identity to the modulo-`J` coordinate.
    refine DFunLike.ext _ _ fun x ↦ ?_
    have hx : q (gJ x) = f' x := LinearMap.congr_fun hgJ x
    exact congrArg Prod.snd (congrArg Subtype.val hx)

end

end Chap10Lemma10778
