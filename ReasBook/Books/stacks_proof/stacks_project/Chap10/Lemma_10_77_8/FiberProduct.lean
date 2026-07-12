import StacksProject_2024.Chap10.Lemma_10_77_8.QuotientFreeCover

universe u v

namespace Chap10Lemma10778

open Chap10Lemma10778

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Helper for Lemma 10.77.8: the sum of two two-sided ideals is again two-sided. -/
theorem isTwoSided_sup : (I ⊔ J).IsTwoSided := by
  refine ⟨?_⟩
  intro a b ha
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ha
  exact Submodule.mem_sup.mpr
    ⟨i * b, I.mul_mem_right _ hi, j * b, J.mul_mem_right _ hj, by rw [← add_mul, hij]⟩

/-- Helper for Lemma 10.77.8: compatible classes modulo `I` and `J` admit a common lift in `R`.
This is the coefficient-level Chinese-remainder step used later for the free-cover gluing. -/
theorem exists_ring_lift_of_compatible_quotients
    [(I ⊔ J).IsTwoSided]
    {aI : R ⧸ I} {aJ : R ⧸ J}
    (hcompat :
      Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J) aI =
        Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J) aJ) :
    ∃ r : R, Ideal.Quotient.mk I r = aI ∧ Ideal.Quotient.mk J r = aJ := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective aI
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective aJ
  -- Unpack compatibility in the quotient by `I ⊔ J` and split the discrepancy into `I`- and
  -- `J`-parts.
  change Ideal.Quotient.mk (I ⊔ J) x = Ideal.Quotient.mk (I ⊔ J) y at hcompat
  have hxy : x - y ∈ I ⊔ J := by
    exact
      (show Ideal.Quotient.mk (I ⊔ J) x = Ideal.Quotient.mk (I ⊔ J) y ↔ x - y ∈ I ⊔ J
        from Ideal.Quotient.eq).mp hcompat
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hxy
  refine ⟨x - i, ?_, ?_⟩
  · -- Correcting the `I`-representative by an element of `I` does not change its class modulo `I`.
    apply
      (show Ideal.Quotient.mk I (x - i) = Ideal.Quotient.mk I x ↔ (x - i) - x ∈ I
        from Ideal.Quotient.eq).2
    have hdiff : (x - i) - x = -i := by
      abel
    exact hdiff ▸ I.neg_mem hi
  · -- The same corrected element has the prescribed class modulo `J` because the discrepancy is `j`.
    apply
      (show Ideal.Quotient.mk J (x - i) = Ideal.Quotient.mk J y ↔ (x - i) - y ∈ J
        from Ideal.Quotient.eq).2
    have hdiff : (x - i) - y = j := by
      calc
        (x - i) - y = (x - y) - i := by abel
        _ = (i + j) - i := by rw [hij]
        _ = j := by abel
    exact hdiff ▸ hj

/-- Helper for Lemma 10.77.8: evaluating a vector in the canonical free cover at a basis index
sends membership in `K • ⊤` to membership in `K`. -/
theorem coeff_mem_ideal_of_mem_smul_top
    (K : Ideal R) [K.IsTwoSided]
    {y : P →₀ R}
    (hy : y ∈ K • (⊤ : Submodule R (P →₀ R)))
    (p : P) :
    y p ∈ K := by
  -- Push the submodule-membership statement through coefficient evaluation.
  have h_eval :
      (Finsupp.lapply (R := R) (M := R) p) y ∈ K • (⊤ : Submodule R R) := by
    exact
      (Submodule.smul_top_le_comap_smul_top K (Finsupp.lapply (R := R) (M := R) p)) hy
  simpa using h_eval

/-- Helper for Chap10 Lemma 10 77 8: coefficientwise membership in an ideal promotes a finitely
supported function to membership in the corresponding `K • ⊤` submodule. -/
theorem mem_smul_top_of_forall_coeff_mem_ideal
    (K : Ideal R) [K.IsTwoSided]
    {y : P →₀ R}
    (hy : ∀ p : P, y p ∈ K) :
    y ∈ K • (⊤ : Submodule R (P →₀ R)) := by
  classical
  -- Expand `y` as a finite sum of basis vectors and place each term in `K • ⊤` coefficientwise.
  rw [← Finsupp.sum_single y]
  refine Submodule.sum_mem _ ?_
  intro p hp
  have hone : Finsupp.single p (1 : R) ∈ (⊤ : Submodule R (P →₀ R)) := by
    simp
  have hsingle : Finsupp.single p (y p) = y p • Finsupp.single p (1 : R) := by
    simp
  rw [hsingle]
  exact Submodule.smul_mem_smul (hy p) hone

/-- Helper for Lemma 10.77.8: when `I ∩ J = 0`, the paired quotient map on the canonical free
cover is injective. This is the coefficientwise separation needed for the final gluing inverse. -/
theorem free_cover_pair_injective_of_inf_eq_bot
    (hIJ : I ⊓ J = ⊥) :
    let σ :
        (P →₀ R) →ₗ[R]
          (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
            ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
          (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
    Function.Injective σ := by
  let σ :
      (P →₀ R) →ₗ[R]
        (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
          ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
      (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
        (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
  change Function.Injective σ
  intro y z hyz
  refine Finsupp.ext fun p ↦ ?_
  -- Projecting the paired quotient equality gives congruent classes modulo `I` and modulo `J`.
  have hI :
      (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))) y =
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))) z := by
    simpa [σ] using congrArg Prod.fst hyz
  have hJ :
      (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R)))) y =
        (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R)))) z := by
    simpa [σ] using congrArg Prod.snd hyz
  have hyzI : y - z ∈ I • (⊤ : Submodule R (P →₀ R)) := by
    exact (Submodule.Quotient.eq _).mp hI
  have hyzJ : y - z ∈ J • (⊤ : Submodule R (P →₀ R)) := by
    exact (Submodule.Quotient.eq _).mp hJ
  -- Each coefficient of `y - z` lies in both ideals, hence vanishes by `I ⊓ J = 0`.
  have hpI : (y - z) p ∈ I :=
    coeff_mem_ideal_of_mem_smul_top (R := R) (P := P) (K := I) hyzI p
  have hpJ : (y - z) p ∈ J :=
    coeff_mem_ideal_of_mem_smul_top (R := R) (P := P) (K := J) hyzJ p
  have hpIJ : (y - z) p ∈ I ⊓ J := by
    exact ⟨hpI, hpJ⟩
  have hpzero : (y - z) p = 0 := by
    have : (y - z) p ∈ (⊥ : Ideal R) := by
      simpa [hIJ] using hpIJ
    simpa using this
  exact sub_eq_zero.mp hpzero

/-- Helper for Lemma 10.77.8: when `I ∩ J = 0`, the range-restriction of the paired quotient map
on the canonical free cover is bijective. The remaining source-faithful work is therefore only to
hit the compatible pairs inside that range. -/
theorem free_cover_pair_rangeRestrict_bijective_of_inf_eq_bot
    (hIJ : I ⊓ J = ⊥) :
    let σ :
        (P →₀ R) →ₗ[R]
          (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
            ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
          (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
    Function.Bijective σ.rangeRestrict := by
  let σ :
      (P →₀ R) →ₗ[R]
        (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
          ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
      (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
        (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
  have hσinj : Function.Injective σ := by
    -- Reuse the coefficientwise injectivity proof for the concrete paired quotient map.
    simpa [σ] using (free_cover_pair_injective_of_inf_eq_bot (R := R) (I := I) (J := J) (P := P) hIJ)
  change Function.Bijective σ.rangeRestrict
  constructor
  · intro y z hyz
    -- Forgetting the range subtype reduces to injectivity of the paired quotient map itself.
    exact hσinj (congrArg Subtype.val hyz)
  · -- Surjectivity is built into `rangeRestrict`.
    exact σ.surjective_rangeRestrict

/-- Helper for Chap10 Lemma 10 77 8: compatible quotient classes modulo `I` and `J` in the
canonical free cover come from an actual finitely supported vector. -/
theorem freeCoverPair_mem_range_of_compatible_quotients
    (hIJ : I ⊓ J = ⊥)
    {uI : (P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))}
    {uJ : (P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R)))}
    (hcompat :
      Submodule.factor
          (by
            simpa using
              (Submodule.smul_mono (show I ≤ I ⊔ J by exact le_sup_left)
                (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                  I • (⊤ : Submodule R (P →₀ R)) ≤ (I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
          uI =
        Submodule.factor
          (by
            simpa using
              (Submodule.smul_mono (show J ≤ I ⊔ J by exact le_sup_right)
                (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl) :
                  J • (⊤ : Submodule R (P →₀ R)) ≤ (I ⊔ J) • (⊤ : Submodule R (P →₀ R))))
          uJ) :
    let σ :
        (P →₀ R) →ₗ[R]
          (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
            ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
          (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
    (uI, uJ) ∈ LinearMap.range σ := by
  classical
  letI : (I ⊔ J).IsTwoSided := by
    simpa using (isTwoSided_sup (R := R) (I := I) (J := J))
  let pFI : Submodule R (P →₀ R) := I • (⊤ : Submodule R (P →₀ R))
  let pFJ : Submodule R (P →₀ R) := J • (⊤ : Submodule R (P →₀ R))
  let pFK : Submodule R (P →₀ R) := (I ⊔ J) • (⊤ : Submodule R (P →₀ R))
  let σ :
      (P →₀ R) →ₗ[R]
        (((P →₀ R) ⧸ pFI) × ((P →₀ R) ⧸ pFJ)) :=
    (Submodule.mkQ pFI).prod (Submodule.mkQ pFJ)
  obtain ⟨aI, rfl⟩ := Submodule.mkQ_surjective pFI uI
  obtain ⟨aJ, rfl⟩ := Submodule.mkQ_surjective pFJ uJ
  have hcompat' : (Submodule.mkQ pFK) aI = (Submodule.mkQ pFK) aJ := by
    simpa [pFI, pFJ, pFK, factorToSup_mk] using hcompat
  have hdiff : aI - aJ ∈ pFK := by
    exact (Submodule.Quotient.eq pFK).mp hcompat'
  have hcoeffCompat :
      ∀ p : P,
        Ideal.Quotient.factor (show I ≤ I ⊔ J by exact le_sup_left) (Ideal.Quotient.mk I (aI p)) =
          Ideal.Quotient.factor (show J ≤ I ⊔ J by exact le_sup_right)
            (Ideal.Quotient.mk J (aJ p)) := by
    intro p
    -- Coefficientwise compatibility follows from compatibility in the quotient by `I ⊔ J`.
    change Ideal.Quotient.mk (I ⊔ J) (aI p) = Ideal.Quotient.mk (I ⊔ J) (aJ p)
    exact
      (show
          Ideal.Quotient.mk (I ⊔ J) (aI p) = Ideal.Quotient.mk (I ⊔ J) (aJ p) ↔
            aI p - aJ p ∈ I ⊔ J
        from Ideal.Quotient.eq).2 <| by
          have hdiff' : aI - aJ ∈ (I ⊔ J) • (⊤ : Submodule R (P →₀ R)) := by
            simpa [pFK] using hdiff
          have hp :
              (aI - aJ) p ∈ I ⊔ J :=
            coeff_mem_ideal_of_mem_smul_top
              (R := R) (P := P) (K := I ⊔ J) hdiff' p
          simpa using hp
  let s : Finset P := aI.support ∪ aJ.support
  let liftCoeff : P → R := fun p =>
    if hp : p ∈ s then
      Classical.choose
        (exists_ring_lift_of_compatible_quotients
          (R := R) (I := I) (J := J) (aI := Ideal.Quotient.mk I (aI p))
          (aJ := Ideal.Quotient.mk J (aJ p)) (hcoeffCompat p))
    else
      0
  let c : P →₀ R :=
    Finsupp.onFinset s liftCoeff <| by
      intro p hp
      by_cases hs : p ∈ s
      · exact hs
      · simp [liftCoeff, hs] at hp
  have hmkI : (Submodule.mkQ pFI) c = Submodule.mkQ pFI aI := by
    apply (Submodule.Quotient.eq pFI).2
    -- The chosen coefficients agree with `aI` modulo `I`, so the whole difference lies in `I • ⊤`.
    refine mem_smul_top_of_forall_coeff_mem_ideal (R := R) (P := P) (K := I) ?_
    intro p
    by_cases hs : p ∈ s
    · have hchoose :=
        (Classical.choose_spec
          (exists_ring_lift_of_compatible_quotients
            (R := R) (I := I) (J := J) (aI := Ideal.Quotient.mk I (aI p))
            (aJ := Ideal.Quotient.mk J (aJ p)) (hcoeffCompat p))).1
      have hc : c p = liftCoeff p := by
        simp [c]
      have hmem : liftCoeff p - aI p ∈ I := by
        exact
          (show Ideal.Quotient.mk I (liftCoeff p) = Ideal.Quotient.mk I (aI p) ↔
              liftCoeff p - aI p ∈ I
            from Ideal.Quotient.eq).mp (by simpa [liftCoeff, hs] using hchoose)
      simpa [show (c - aI) p = c p - aI p by rfl, hc] using hmem
    · have hc : c p = 0 := by
        simp [c, liftCoeff, hs]
      have haI : aI p = 0 := by
        by_contra hne
        exact hs (Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hne)))
      simp [hc, haI]
  have hmkJ : (Submodule.mkQ pFJ) c = Submodule.mkQ pFJ aJ := by
    apply (Submodule.Quotient.eq pFJ).2
    -- The same coefficientwise argument works modulo `J`.
    refine mem_smul_top_of_forall_coeff_mem_ideal (R := R) (P := P) (K := J) ?_
    intro p
    by_cases hs : p ∈ s
    · have hchoose :=
        (Classical.choose_spec
          (exists_ring_lift_of_compatible_quotients
            (R := R) (I := I) (J := J) (aI := Ideal.Quotient.mk I (aI p))
            (aJ := Ideal.Quotient.mk J (aJ p)) (hcoeffCompat p))).2
      have hc : c p = liftCoeff p := by
        simp [c]
      have hmem : liftCoeff p - aJ p ∈ J := by
        exact
          (show Ideal.Quotient.mk J (liftCoeff p) = Ideal.Quotient.mk J (aJ p) ↔
              liftCoeff p - aJ p ∈ J
            from Ideal.Quotient.eq).mp (by simpa [liftCoeff, hs] using hchoose)
      simpa [show (c - aJ) p = c p - aJ p by rfl, hc] using hmem
    · have hc : c p = 0 := by
        simp [c, liftCoeff, hs]
      have haJ : aJ p = 0 := by
        by_contra hne
        exact hs (Finset.mem_union.mpr (Or.inr (Finsupp.mem_support_iff.mpr hne)))
      simp [hc, haJ]
  change (Submodule.mkQ pFI aI, Submodule.mkQ pFJ aJ) ∈ LinearMap.range σ
  refine ⟨c, ?_⟩
  -- The chosen lift realizes the prescribed compatible pair in the product of quotients.
  ext <;> simp [σ, hmkI, hmkJ]

end

end Chap10Lemma10778
