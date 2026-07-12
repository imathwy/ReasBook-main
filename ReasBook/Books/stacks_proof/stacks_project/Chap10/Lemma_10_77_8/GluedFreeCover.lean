import StacksProject_2024.Chap10.Lemma_10_77_8.QuotientFreeCover
import StacksProject_2024.Chap10.Lemma_10_77_8.FiberProduct
import StacksProject_2024.Chap10.Lemma_10_77_8.EndomorphismCriterion
import StacksProject_2024.Chap10.Lemma_10_77_8.SupSectionCompatibility

universe u v

namespace Chap10Lemma10778

open Chap10Lemma10778

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Helper for Chap10 Lemma 10 77 8: once the modulo-`J` section has been made compatible with the
modulo-`(I ⊔ J)` section, the paired quotient map on the canonical free cover yields an actual
lift `P → P →₀ R` inducing the identity modulo both ideals. -/
theorem pairedQuotientRangeMapOfCompatibleSections
    (hIJ : I ⊓ J = ⊥)
    (uI :
      P →ₗ[R]
        ((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))))
    (uJ :
      P →ₗ[R]
        ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R)))))
    (hcompat :
      ∀ x : P,
        Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show I ≤ I ⊔ J by exact le_sup_left)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    I • (⊤ : Submodule R (P →₀ R)) ≤
                      (I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
            (uI x) =
          Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    J • (⊤ : Submodule R (P →₀ R)) ≤
                      (I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
            (uJ x)) :
    let σ :
        (P →₀ R) →ₗ[R]
          (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
            ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
          (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
    ∃ pairMap : P →ₗ[R] σ.range,
      ∀ x : P,
        ((pairMap x : σ.range) :
            (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
              ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R)))))) =
          (uI x, uJ x) := by
  let σ :
      (P →₀ R) →ₗ[R]
        (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
          ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
    (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
      (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
  change ∃ pairMap : P →ₗ[R] σ.range,
      ∀ x : P,
        ((pairMap x : σ.range) :
            (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
              ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R)))))) =
          (uI x, uJ x)
  have hpair_mem : ∀ x : P, (uI x, uJ x) ∈ LinearMap.range σ := by
    intro x
    -- Each compatible pair of quotient classes comes from the canonical free cover.
    simpa [σ] using
      (freeCoverPair_mem_range_of_compatible_quotients
        (R := R) (I := I) (J := J) (P := P) hIJ (uI := uI x) (uJ := uJ x) (hcompat x))
  let pairFun : P → σ.range := fun x => ⟨(uI x, uJ x), hpair_mem x⟩
  have hpairFun_add : ∀ x y : P, pairFun (x + y) = pairFun x + pairFun y := by
    intro x y
    -- Equality in the range subtype is determined by the underlying quotient pair.
    apply Subtype.ext
    simp [pairFun, map_add]
  have hpairFun_smul : ∀ c : R, ∀ x : P, pairFun (c • x) = c • pairFun x := by
    intro c x
    -- The same extensionality argument handles scalar compatibility.
    apply Subtype.ext
    simp [pairFun, map_smul]
  refine ⟨{ toFun := pairFun, map_add' := hpairFun_add, map_smul' := hpairFun_smul }, ?_⟩
  intro x
  rfl

set_option maxHeartbeats 400000 in
/-- Helper for Chap10 Lemma 10 77 8: once the modulo-`J` section has been made compatible with the
modulo-`(I ⊔ J)` section, the paired quotient map on the canonical free cover yields an actual
lift `P → P →₀ R` inducing the identity modulo both ideals. -/
theorem existsGluedLiftOfCompatibleSections
    (hIJ : I ⊓ J = ⊥)
    (fI :
      P ⧸ (I • (⊤ : Submodule R P)) →ₗ[R ⧸ I]
        (P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R))))
    (hfI :
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient I).comp fI =
        LinearMap.id)
    (fK :
      P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)) →ₗ[R]
        (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
    (hfK_compat :
      fK.comp
          (Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show I ≤ I ⊔ J by exact le_sup_left)
                  (show (⊤ : Submodule R P) ≤ ⊤ by rfl) :
                    I • (⊤ : Submodule R P) ≤ (I ⊔ J) • (⊤ : Submodule R P)))) =
        ((Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show I ≤ I ⊔ J by exact le_sup_left)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    I • (⊤ : Submodule R (P →₀ R)) ≤
                      (I ⊔ J) • (⊤ : Submodule R (P →₀ R))))).comp (fI.restrictScalars R)))
    [Module (R ⧸ J) (P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)))]
    [Module (R ⧸ J) ((P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))]
    (qP :
      P ⧸ (J • (⊤ : Submodule R P)) →ₗ[R ⧸ J]
        P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)))
    (qF :
      (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))) →ₗ[R ⧸ J]
        (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
    (fKJ :
      P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)) →ₗ[R ⧸ J]
        (P →₀ R) ⧸ ((I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
    (gJ :
      P ⧸ (J • (⊤ : Submodule R P)) →ₗ[R ⧸ J]
        (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))
    (hqF_gJ : qF.comp gJ = fKJ.comp qP)
    (hqP_eq :
      ∀ x : P ⧸ (J • (⊤ : Submodule R P)),
        qP x =
          Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R P) ≤ ⊤ by rfl) :
                    J • (⊤ : Submodule R P) ≤ (I ⊔ J) • (⊤ : Submodule R P)))
            x)
    (hqF_eq :
      ∀ x : (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))),
        qF x =
          Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    J • (⊤ : Submodule R (P →₀ R)) ≤
                      (I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
            x)
    (hfKJ_eq :
      ∀ x : P ⧸ ((I ⊔ J) • (⊤ : Submodule R P)), fKJ x = fK x)
    (hπJ_gJ :
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient J).comp gJ =
        LinearMap.id) :
    ∃ h : P →ₗ[R] (P →₀ R),
      let a : P →ₗ[R] P := (Finsupp.linearCombination R (id : P → P)).comp h
      (∀ x : P,
        (Submodule.mkQ (I • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (I • (⊤ : Submodule R P))) x) ∧
      (∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (J • (⊤ : Submodule R P))) x) := by
  let π : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let pPI : Submodule R P := I • (⊤ : Submodule R P)
  let pPJ : Submodule R P := J • (⊤ : Submodule R P)
  let pPK : Submodule R P := (I ⊔ J) • (⊤ : Submodule R P)
  let pFI : Submodule R (P →₀ R) := I • (⊤ : Submodule R (P →₀ R))
  let pFJ : Submodule R (P →₀ R) := J • (⊤ : Submodule R (P →₀ R))
  let pFK : Submodule R (P →₀ R) := (I ⊔ J) • (⊤ : Submodule R (P →₀ R))
  let uI : P →ₗ[R] ((P →₀ R) ⧸ pFI) := (fI.restrictScalars R).comp (Submodule.mkQ pPI)
  let uJ : P →ₗ[R] ((P →₀ R) ⧸ pFJ) := (gJ.restrictScalars R).comp (Submodule.mkQ pPJ)
  have hπI_section : (π.quotientMapByIdeal I).comp (fI.restrictScalars R) = LinearMap.id := by
    -- Forgetting the quotient-ring scalars preserves the chosen section modulo `I`.
    refine DFunLike.ext _ _ fun x ↦ ?_
    simpa [π, LinearMap.comp_apply, LinearMap.quotientMapByIdeal_over_quotient,
      LinearMap.quotientMapByIdeal] using LinearMap.congr_fun hfI x
  have hcompat :
      ∀ x : P,
        Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show I ≤ I ⊔ J by exact le_sup_left)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    pFI ≤ pFK))
            (uI x) =
          Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    pFJ ≤ pFK))
            (uJ x) := by
    intro x
    have hI_to_K :
        Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show I ≤ I ⊔ J by exact le_sup_left)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    pFI ≤ pFK))
            (uI x) =
          fK ((Submodule.mkQ pPK) x) := by
      have hx := LinearMap.congr_fun hfK_compat ((Submodule.mkQ pPI) x)
      simpa [uI, pPI, pPK, pFI, pFK, LinearMap.comp_apply, factorToSup_mk] using hx.symm
    have hJ_to_K :
        Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    pFJ ≤ pFK))
            (uJ x) =
          fK ((Submodule.mkQ pPK) x) := by
      have hx := LinearMap.congr_fun hqF_gJ ((Submodule.mkQ pPJ) x)
      calc
        Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    pFJ ≤ pFK))
            (uJ x) = qF (uJ x) := by
              rw [hqF_eq]
        _ = qF (gJ ((Submodule.mkQ pPJ) x)) := by
              rfl
        _ = fKJ (qP ((Submodule.mkQ pPJ) x)) := by
              simpa [LinearMap.comp_apply] using hx
        _ = fKJ ((Submodule.mkQ pPK) x) := by
              rw [hqP_eq]
              simp [pPJ, pPK, factorToSup_mk]
        _ = fK ((Submodule.mkQ pPK) x) := by
              rw [hfKJ_eq]
    exact hI_to_K.trans hJ_to_K.symm
  obtain ⟨pairMap, hpairMap⟩ :=
    pairedQuotientRangeMapOfCompatibleSections (R := R) (I := I) (J := J) (P := P) hIJ uI uJ
      hcompat
  let σ :
      (P →₀ R) →ₗ[R]
        (((P →₀ R) ⧸ pFI) × ((P →₀ R) ⧸ pFJ)) :=
    (Submodule.mkQ pFI).prod (Submodule.mkQ pFJ)
  have hσbij : Function.Bijective σ.rangeRestrict := by
    -- Injectivity is the coefficientwise separation proved earlier, and surjectivity is built in.
    simpa [σ, pFI, pFJ] using
      (free_cover_pair_rangeRestrict_bijective_of_inf_eq_bot
        (R := R) (I := I) (J := J) (P := P) hIJ)
  let eσ : (P →₀ R) ≃ₗ[R] σ.range := LinearEquiv.ofBijective σ.rangeRestrict hσbij
  let h : P →ₗ[R] (P →₀ R) := eσ.symm.toLinearMap.comp pairMap
  refine ⟨h, ?_⟩
  constructor
  · intro x
    have hrange :
        σ.rangeRestrict (h x) = pairMap x := by
      calc
        σ.rangeRestrict (h x) = eσ (h x) := by
            symm
            simpa [eσ] using
              (LinearEquiv.ofBijective_apply σ.rangeRestrict (hf := hσbij) (h x))
        _ = pairMap x := by
            simpa [h, eσ, LinearMap.comp_apply] using eσ.apply_symm_apply (pairMap x)
    have hσhx : σ (h x) = (uI x, uJ x) := by
      exact (congrArg Subtype.val hrange).trans (hpairMap x)
    have hIcoord : (Submodule.mkQ pFI) (h x) = uI x := by
      simpa [σ] using congrArg Prod.fst hσhx
    -- Project the glued free-cover lift to the modulo-`I` quotient and use the chosen section.
    have hquot :
        (Submodule.mkQ pPI) ((π.comp h) x) =
          (π.quotientMapByIdeal I) ((Submodule.mkQ pFI) (h x)) := by
      rfl
    calc
      (Submodule.mkQ pPI) ((π.comp h) x) = (π.quotientMapByIdeal I) ((Submodule.mkQ pFI) (h x)) := hquot
      _ = (π.quotientMapByIdeal I) (uI x) := by
          rw [hIcoord]
      _ = (Submodule.mkQ pPI) x := by
          simpa [uI, LinearMap.comp_apply] using
            LinearMap.congr_fun hπI_section ((Submodule.mkQ pPI) x)
  · intro x
    have hrange :
        σ.rangeRestrict (h x) = pairMap x := by
      calc
        σ.rangeRestrict (h x) = eσ (h x) := by
            symm
            simpa [eσ] using
              (LinearEquiv.ofBijective_apply σ.rangeRestrict (hf := hσbij) (h x))
        _ = pairMap x := by
            simpa [h, eσ, LinearMap.comp_apply] using eσ.apply_symm_apply (pairMap x)
    have hσhx : σ (h x) = (uI x, uJ x) := by
      exact (congrArg Subtype.val hrange).trans (hpairMap x)
    have hJcoord : (Submodule.mkQ pFJ) (h x) = uJ x := by
      simpa [σ] using congrArg Prod.snd hσhx
    -- The modulo-`J` projection is read off from the second coordinate of the glued pair.
    have hquot :
        (Submodule.mkQ pPJ) ((π.comp h) x) =
          (π.quotientMapByIdeal J) ((Submodule.mkQ pFJ) (h x)) := by
      rfl
    calc
      (Submodule.mkQ pPJ) ((π.comp h) x) = (π.quotientMapByIdeal J) ((Submodule.mkQ pFJ) (h x)) := hquot
      _ = (π.quotientMapByIdeal J) (uJ x) := by
          rw [hJcoord]
      _ = (Submodule.mkQ pPJ) x := by
          simpa [uJ, π, LinearMap.comp_apply, LinearMap.quotientMapByIdeal_over_quotient,
            LinearMap.quotientMapByIdeal] using
            LinearMap.congr_fun hπJ_gJ ((Submodule.mkQ pPJ) x)

set_option maxHeartbeats 400000 in
/-- Helper for Lemma 10.77.8: once the modulo `I` and modulo `J` splittings of the canonical free
cover are glued source-faithfully, the induced endomorphism of `P` is the identity modulo both
ideals. -/
theorem exists_glued_free_cover_endomorphism
    (hIJ : I ⊓ J = ⊥)
    (hPI : Module.Projective (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P)))
    (hPJ : Module.Projective (R ⧸ J) (P ⧸ (J • ⊤ : Submodule R P))) :
    ∃ h : P →ₗ[R] (P →₀ R),
      let a : P →ₗ[R] P := (Finsupp.linearCombination R (id : P → P)).comp h
      (∀ x : P,
        (Submodule.mkQ (I • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (I • (⊤ : Submodule R P))) x) ∧
      (∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (J • (⊤ : Submodule R P))) x) := by
  let π : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  letI : (I ⊔ J).IsTwoSided := by
    simpa using (isTwoSided_sup (R := R) (I := I) (J := J))
  let pPJ : Submodule R P := J • (⊤ : Submodule R P)
  let pPK : Submodule R P := (I ⊔ J) • (⊤ : Submodule R P)
  let pFJ : Submodule R (P →₀ R) := J • (⊤ : Submodule R (P →₀ R))
  let pFK : Submodule R (P →₀ R) := (I ⊔ J) • (⊤ : Submodule R (P →₀ R))
  obtain ⟨fI, hfI⟩ :=
    exists_free_cover_section_of_projective_quotient (R := R) (P := P) (K := I) hPI
  obtain ⟨fK, hfK_section, hfK_compat⟩ :=
    mod_i_section_descends_to_sup (R := R) (I := I) (P := P) (K := I ⊔ J)
      (show I ≤ I ⊔ J by exact le_sup_left) fI hfI
  let φJ : R ⧸ J →+* R ⧸ (I ⊔ J) :=
    Ideal.Quotient.factor (show J ≤ I ⊔ J by exact le_sup_right)
  letI : Module (R ⧸ J) (P ⧸ pPK) := Module.compHom (P ⧸ pPK) φJ
  letI : Module (R ⧸ J) ((P →₀ R) ⧸ pFK) := Module.compHom ((P →₀ R) ⧸ pFK) φJ
  let qP :
      P ⧸ pPJ →ₗ[R ⧸ J] P ⧸ pPK :=
    { toFun :=
        Submodule.factor
          (by
            simpa [pPJ, pPK] using
              (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                (show (⊤ : Submodule R P) ≤ ⊤ by rfl) :
                  pPJ ≤ pPK))
      map_add' := by
        intro x y
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective pPJ x
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pPJ y
        simp [pPJ, pPK, factorToSup_mk]
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pPJ x
        change (Submodule.mkQ pPK) (r • y) =
          (Ideal.Quotient.mk (I ⊔ J) r) • (Submodule.mkQ pPK) y
        exact (Module.Quotient.mk_smul_mk P (I ⊔ J) r y).symm }
  let qF :
      (P →₀ R) ⧸ pFJ →ₗ[R ⧸ J] (P →₀ R) ⧸ pFK :=
    { toFun :=
        Submodule.factor
          (by
            simpa [pFJ, pFK] using
              (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                  pFJ ≤ pFK))
      map_add' := by
        intro x y
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective pFJ x
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pFJ y
        simp [pFJ, pFK, factorToSup_mk]
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pFJ x
        change (Submodule.mkQ pFK) (r • y) =
          (Ideal.Quotient.mk (I ⊔ J) r) • (Submodule.mkQ pFK) y
        exact (Module.Quotient.mk_smul_mk (P →₀ R) (I ⊔ J) r y).symm }
  let πJ :
      (P →₀ R) ⧸ pFJ →ₗ[R ⧸ J] P ⧸ pPJ :=
    π.quotientMapByIdeal_over_quotient J
  let πK0 :
      (P →₀ R) ⧸ pFK →ₗ[R ⧸ (I ⊔ J)] P ⧸ pPK :=
    π.quotientMapByIdeal_over_quotient (I ⊔ J)
  let πK :
      (P →₀ R) ⧸ pFK →ₗ[R ⧸ J] P ⧸ pPK :=
    { toFun := πK0
      map_add' := by
        intro x y
        exact πK0.map_add x y
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        change πK0 ((Ideal.Quotient.mk (I ⊔ J) r) • x) =
          (Ideal.Quotient.mk (I ⊔ J) r) • πK0 x
        exact πK0.map_smul (Ideal.Quotient.mk (I ⊔ J) r) x }
  obtain ⟨sJ, hsJ⟩ :=
    exists_free_cover_section_of_projective_quotient (R := R) (P := P) (K := J) hPJ
  have hq_π : πK.comp qF = qP.comp πJ := by
    -- Both quotient paths send a representative to its image modulo `(I ⊔ J)P`.
    refine DFunLike.ext _ _ fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pFJ x
    change πK0 ((Submodule.mkQ pFK) y) = (Submodule.mkQ pPK) (π y)
    rfl
  let fKJ :
      P ⧸ pPK →ₗ[R ⧸ J] (P →₀ R) ⧸ pFK :=
    { toFun := fK
      map_add' := by
        intro x y
        exact fK.map_add x y
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pPK x
        change fK ((Ideal.Quotient.mk (I ⊔ J) r) • (Submodule.mkQ pPK) y) =
          (Ideal.Quotient.mk (I ⊔ J) r) • fK ((Submodule.mkQ pPK) y)
        rw [← quotient_smul_eq_quotient_mk_smul (K := I ⊔ J) (M := P) r
          ((Submodule.mkQ pPK) y)]
        rw [← quotient_smul_eq_quotient_mk_smul (K := I ⊔ J) (M := P →₀ R) r
          (fK ((Submodule.mkQ pPK) y))]
        exact fK.map_smul r ((Submodule.mkQ pPK) y) }
  have hfKJ_section : πK.comp fKJ = LinearMap.id := by
    -- The descended modulo-`K` section stays a section after viewing scalars through `R ⧸ J`.
    refine DFunLike.ext _ _ fun x ↦ ?_
    simpa [πK, fKJ, LinearMap.comp_apply, LinearMap.quotientMapByIdeal_over_quotient,
      LinearMap.quotientMapByIdeal] using LinearMap.congr_fun hfK_section x
  have hOverlap :
      ∀ uK : (P →₀ R) ⧸ pFK,
        πK uK = 0 →
          ∃ v : (P →₀ R) ⧸ pFJ, qF v = uK ∧ πJ v = 0 := by
    intro uK huK
    have huK' : ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal (I ⊔ J)) uK = 0 := by
      change πK0 uK = 0 at huK
      simpa [πK0, LinearMap.quotientMapByIdeal_over_quotient,
        LinearMap.quotientMapByIdeal] using huK
    simpa [qF, πJ, pFJ, pFK] using
      (existsModJLiftOfZeroImageInSupQuotient (R := R) (I := I) (J := J) (P := P) uK huK')
  letI : Module.Projective (R ⧸ J) (P ⧸ (J • (⊤ : Submodule R P))) := hPJ
  obtain ⟨gJ, hqF_gJ, hπJ_gJ⟩ :=
    existsModJSectionCompatibleWithSupSection (R := R) (I := I) (J := J) (P := P)
      qP qF πJ πK hq_π fKJ hfKJ_section sJ hsJ hOverlap
  have hqP_eq :
      ∀ x : P ⧸ pPJ,
        qP x =
          Submodule.factor
            (by
              simpa [pPJ, pPK] using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R P) ≤ ⊤ by rfl) :
                    pPJ ≤ pPK))
            x := by
    intro x
    rfl
  have hqF_eq :
      ∀ x : (P →₀ R) ⧸ pFJ,
        qF x =
          Submodule.factor
            (by
              simpa [pFJ, pFK] using
                (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                  (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                    pFJ ≤ pFK))
            x := by
    intro x
    rfl
  have hfKJ_eq :
      ∀ x : P ⧸ pPK, fKJ x = fK x := by
    intro x
    rfl
  exact
    existsGluedLiftOfCompatibleSections (R := R) (I := I) (J := J) (P := P) hIJ
      fI hfI fK hfK_compat qP qF fKJ gJ hqF_gJ hqP_eq hqF_eq hfKJ_eq hπJ_gJ

/-- Helper for Lemma 10.77.8: a glued lift whose induced endomorphism is the identity modulo `I`
and `J` already splits the canonical free cover of `P`. -/
theorem projective_of_glued_free_cover_endomorphism
    (hIJ : I ⊓ J = ⊥)
    (h : P →ₗ[R] (P →₀ R))
    (hQI :
      ∀ x : P,
        (Submodule.mkQ (I • (⊤ : Submodule R P)))
          ((Finsupp.linearCombination R (id : P → P)).comp h x) =
            (Submodule.mkQ (I • (⊤ : Submodule R P))) x)
    (hQJ :
      ∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P)))
          ((Finsupp.linearCombination R (id : P → P)).comp h x) =
            (Submodule.mkQ (J • (⊤ : Submodule R P))) x) :
    Module.Projective R P := by
  let π : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let a : P →ₗ[R] P := π.comp h
  have hfixI : ∀ x ∈ (I • (⊤ : Submodule R P)), a x = x := by
    -- The quotient identity modulo `J` forces the endomorphism to fix `IP`.
    exact eq_on_left_smul_top_of_right_quotient_identity hIJ a hQJ
  have hbij : Function.Bijective a := by
    -- Once `a` is the identity on `IP` and on `P / IP`, it is an automorphism.
    exact bijective_of_id_on_submodule_and_quotient a (I • (⊤ : Submodule R P)) hfixI hQI
  let e : P ≃ₗ[R] P := LinearEquiv.ofBijective a hbij
  let s : P →ₗ[R] (P →₀ R) := h.comp e.symm.toLinearMap
  have hs : π.comp s = LinearMap.id := by
    -- Correct the glued lift by the inverse of the resulting automorphism.
    ext x
    change a (e.symm x) = x
    exact e.apply_symm_apply x
  -- A split surjection from a free module exhibits `P` as projective.
  exact Module.Projective.of_split s π hs

end

end Chap10Lemma10778
