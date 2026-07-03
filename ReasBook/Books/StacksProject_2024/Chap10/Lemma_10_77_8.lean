import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

namespace LinearMap

/-- The map on quotients by `K • ⊤` induced by an `R`-linear map. This local abbreviation keeps
Lemma 10.77.8 source-faithful without importing later chapter API. -/
private abbrev quotientMapByIdeal
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (K : Ideal R) [K.IsTwoSided] :
    M ⧸ (K • (⊤ : Submodule R M)) →ₗ[R] M' ⧸ (K • (⊤ : Submodule R M')) :=
  (K • (⊤ : Submodule R M)).mapQ (K • (⊤ : Submodule R M')) f
    (Submodule.smul_top_le_comap_smul_top K f)

/-- Helper for Lemma 10.77.8: the quotient map induced by `f` is also linear over the quotient
ring `R ⧸ K`. This is the scalar adapter needed before applying projectivity modulo `K`. -/
private abbrev quotientMapByIdeal_over_quotient
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (K : Ideal R) [K.IsTwoSided] :
    M ⧸ (K • (⊤ : Submodule R M)) →ₗ[R ⧸ K] M' ⧸ (K • (⊤ : Submodule R M')) :=
  { toFun := f.quotientMapByIdeal K
    map_add' := by
      intro x y
      -- Work with quotient representatives so the induced additivity is visible to `simp`.
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) x
      obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) y
      simp [LinearMap.quotientMapByIdeal]
    map_smul' := by
      intro c x
      -- Unpack both the scalar and the quotient class to reduce to the defining quotient action.
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) x
      simp [LinearMap.quotientMapByIdeal, Module.Quotient.mk_smul_mk] }

end LinearMap

/-- Helper for Lemma 10.77.8: a surjective linear map induces a surjective map on compatible
quotients. -/
private theorem mapQ_surjective_of_surjective
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (hφ : Function.Surjective φ)
    (p : Submodule R M)
    (q : Submodule R N)
    (hpq : p ≤ Submodule.comap φ q) :
    Function.Surjective (p.mapQ q φ hpq) := by
  intro y
  -- Choose a representative in `N`, then lift it along the original surjection.
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective q y
  obtain ⟨x, rfl⟩ := hφ y
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rfl

/-- Helper for Lemma 10.77.8: the canonical free cover `P →₀ R → P` is surjective. -/
private theorem canonical_free_cover_surjective :
    Function.Surjective (Finsupp.linearCombination R (id : P → P)) := by
  -- Every `x : P` is hit by the singleton basis vector at `x`.
  simpa using Finsupp.linearCombination_surjective R Function.surjective_id

/-- Helper for Lemma 10.77.8: the canonical free cover stays surjective after reducing modulo an
ideal. -/
private theorem canonical_free_cover_quotient_surjective
    (K : Ideal R) [K.IsTwoSided] :
    Function.Surjective ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal K) := by
  -- Quotienting preserves surjectivity for the canonical free cover via `Submodule.mapQ`.
  simpa [LinearMap.quotientMapByIdeal] using
    (mapQ_surjective_of_surjective
      (Finsupp.linearCombination R (id : P → P))
      (canonical_free_cover_surjective (R := R) (P := P))
      (K • (⊤ : Submodule R (P →₀ R)))
      (K • (⊤ : Submodule R P))
      (Submodule.smul_top_le_comap_smul_top K (Finsupp.linearCombination R (id : P → P))))

/-- Helper for Lemma 10.77.8: an element of `K • P` comes from an element of `K • (P →₀ R)` under
the canonical free cover. -/
private theorem canonical_free_cover_preimage_mem_smul_top
    (K : Ideal R) [K.IsTwoSided]
    {x : P}
    (hx : x ∈ K • (⊤ : Submodule R P)) :
    ∃ y : P →₀ R,
      y ∈ K • (⊤ : Submodule R (P →₀ R)) ∧
        Finsupp.linearCombination R (id : P → P) y = x := by
  -- Follow the source proof: write an element of `K • P` as a sum of generators `r • m`, then
  -- lift each generator to the singleton basis vector in the canonical free module.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m hm
    refine ⟨r • Finsupp.single m (1 : R), ?_, ?_⟩
    · have hsingle : Finsupp.single m (1 : R) ∈ (⊤ : Submodule R (P →₀ R)) := by
        simp
      exact Submodule.smul_mem_smul hr hsingle
    · -- The canonical free cover sends the singleton basis vector at `m` back to `m`.
      calc
        Finsupp.linearCombination R (id : P → P) (r • Finsupp.single m (1 : R))
            = r • Finsupp.linearCombination R (id : P → P) (Finsupp.single m (1 : R)) := by
                simp
        _ = r • m := by
              simp [Finsupp.linearCombination_single]
  · intro y z hy hz
    rcases hy with ⟨fy, hfy, hfy_eq⟩
    rcases hz with ⟨fz, hfz, hfz_eq⟩
    refine ⟨fy + fz, Submodule.add_mem _ hfy hfz, ?_⟩
    -- Additivity of the free cover glues the lifted summands.
    calc
      Finsupp.linearCombination R (id : P → P) (fy + fz)
          = Finsupp.linearCombination R (id : P → P) fy +
              Finsupp.linearCombination R (id : P → P) fz := by
                simp
      _ = y + z := by rw [hfy_eq, hfz_eq]

/-- Helper for Lemma 10.77.8: the overlap correction term inside `(I ⊔ J) • P` lifts to the
canonical free cover inside `(I ⊔ J) • (P →₀ R)`. -/
private theorem exists_overlap_correction_in_sup_smul
    {c : P →₀ R} {y : P}
    (hcy :
      Finsupp.linearCombination R (id : P → P) c - y ∈
        (I ⊔ J) • (⊤ : Submodule R P)) :
    ∃ e : P →₀ R,
      e ∈ (I ⊔ J) • (⊤ : Submodule R (P →₀ R)) ∧
        Finsupp.linearCombination R (id : P → P) e =
          Finsupp.linearCombination R (id : P → P) c - y := by
  -- This is exactly the source correction step, now named separately from later quotient transport.
  letI : (I ⊔ J).IsTwoSided := by
    refine ⟨?_⟩
    intro a b ha
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ha
    exact Submodule.mem_sup.mpr
      ⟨i * b, I.mul_mem_right _ hi, j * b, J.mul_mem_right _ hj, by rw [← add_mul, hij]⟩
  exact canonical_free_cover_preimage_mem_smul_top
    (R := R) (P := P) (K := I ⊔ J) hcy

/-- Helper for Lemma 10.77.8: if `P / KP` is projective over `R / K`, then the canonical free
cover admits a section modulo `K`. -/
private theorem exists_free_cover_section_of_projective_quotient
    (K : Ideal R) [K.IsTwoSided]
    (hPK : Module.Projective (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P)))) :
    ∃ s :
        P ⧸ (K • (⊤ : Submodule R P)) →ₗ[R ⧸ K]
          (P →₀ R) ⧸ (K • (⊤ : Submodule R (P →₀ R))),
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient K).comp s =
        LinearMap.id := by
  let πK :
      (P →₀ R) ⧸ (K • (⊤ : Submodule R (P →₀ R))) →ₗ[R ⧸ K]
        P ⧸ (K • (⊤ : Submodule R P)) :=
    (Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient K
  have hπK_surj : Function.Surjective πK := by
    -- Forgetting the quotient-ring scalar structure reduces to the already-proved `R`-linear
    -- surjectivity of the quotient free cover.
    simpa [πK, LinearMap.quotientMapByIdeal_over_quotient] using
      canonical_free_cover_quotient_surjective (R := R) (P := P) (K := K)
  letI : Module.Projective (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P))) := hPK
  -- Projectivity of `P / KP` now gives the desired right inverse over `R ⧸ K`.
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective πK
    (LinearMap.range_eq_top.2 hπK_surj)
  exact ⟨s, hs⟩

/-- Helper for Lemma 10.77.8: after choosing a section modulo `I`, the source proof's map reduced
modulo `K` is an honest `R`-linear section of the canonical free cover modulo `K`. -/
private theorem mod_i_section_descends_to_sup
    {K : Ideal R} [K.IsTwoSided]
    (hIK : I ≤ K)
    (fI :
      P ⧸ (I • (⊤ : Submodule R P)) →ₗ[R ⧸ I]
        (P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R))))
    (hfI :
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient I).comp fI =
        LinearMap.id) :
    ∃ fK :
        P ⧸ (K • (⊤ : Submodule R P)) →ₗ[R]
          (P →₀ R) ⧸ (K • (⊤ : Submodule R (P →₀ R))),
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal K).comp fK =
        LinearMap.id := by
  let π : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let pPI : Submodule R P := I • (⊤ : Submodule R P)
  let pPK : Submodule R P := K • (⊤ : Submodule R P)
  let pFI : Submodule R (P →₀ R) := I • (⊤ : Submodule R (P →₀ R))
  let pFK : Submodule R (P →₀ R) := K • (⊤ : Submodule R (P →₀ R))
  let hPIK : pPI ≤ pPK := by
    simpa [pPI, pPK] using
      (Submodule.smul_mono hIK (show (⊤ : Submodule R P) ≤ ⊤ by rfl))
  let hFIK : pFI ≤ pFK := by
    simpa [pFI, pFK] using
      (Submodule.smul_mono hIK (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl))
  let qPIK : P ⧸ pPI →ₗ[R] P ⧸ pPK := Submodule.factor hPIK
  let qFIK : (P →₀ R) ⧸ pFI →ₗ[R] (P →₀ R) ⧸ pFK := Submodule.factor hFIK
  let fIR : P ⧸ pPI →ₗ[R] (P →₀ R) ⧸ pFI := fI.restrictScalars R
  let raw : P →ₗ[R] (P →₀ R) ⧸ pFK := (qFIK.comp fIR).comp (Submodule.mkQ pPI)
  have hK_smul_zero :
      ∀ {r : R}, r ∈ K → ∀ z : (P →₀ R) ⧸ pFK, r • z = 0 := by
    intro r hr z
    -- Any scalar from `K` acts trivially on the quotient by `K • ⊤`.
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pFK z
    change (Submodule.mkQ pFK) (r • y) = 0
    have hy : y ∈ (⊤ : Submodule R (P →₀ R)) := by
      simp
    have hmem : r • y ∈ pFK := by
      exact Submodule.smul_mem_smul hr hy
    exact (Submodule.Quotient.eq pFK).2 (by simpa using hmem)
  have hraw_ker : pPK ≤ LinearMap.ker raw := by
    intro x hx
    change raw x = 0
    -- The raw composite is `R`-linear, so generators `r • m` with `r ∈ K` already map to zero.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      calc
        raw (r • m) = r • raw m := by simp [raw]
        _ = 0 := hK_smul_zero hr (raw m)
    · intro y z hy hz
      simpa [raw] using congrArg₂ (· + ·) hy hz
  have hπI_section : (π.quotientMapByIdeal I).comp fIR = LinearMap.id := by
    -- Forgetting the quotient-ring scalar structure leaves the same section identity.
    refine DFunLike.ext _ _ fun x ↦ ?_
    simpa [π, fIR, LinearMap.quotientMapByIdeal_over_quotient, LinearMap.quotientMapByIdeal] using
      LinearMap.congr_fun hfI x
  have hquot_comm :
      (π.quotientMapByIdeal K).comp qFIK = qPIK.comp (π.quotientMapByIdeal I) := by
    -- Both sides send a class modulo `I` to the class of `π` modulo `K`.
    refine DFunLike.ext _ _ fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pFI x
    rfl
  refine ⟨pPK.liftQ raw hraw_ker, ?_⟩
  have hcomp_mk :
      (((π.quotientMapByIdeal K).comp (pPK.liftQ raw hraw_ker)).comp (Submodule.mkQ pPK)) =
        Submodule.mkQ pPK := by
    -- Compose with `mkQ` so the identity reduces to the raw map on representatives.
    calc
      (((π.quotientMapByIdeal K).comp (pPK.liftQ raw hraw_ker)).comp (Submodule.mkQ pPK))
          = (π.quotientMapByIdeal K).comp raw := by
              ext x
              rfl
      _ = (((π.quotientMapByIdeal K).comp qFIK).comp fIR).comp (Submodule.mkQ pPI) := by
            rfl
      _ = ((qPIK.comp (π.quotientMapByIdeal I)).comp fIR).comp (Submodule.mkQ pPI) := by
            rw [hquot_comm]
      _ = (qPIK.comp ((π.quotientMapByIdeal I).comp fIR)).comp (Submodule.mkQ pPI) := by
            rw [← LinearMap.comp_assoc]
      _ = (qPIK.comp LinearMap.id).comp (Submodule.mkQ pPI) := by
            rw [hπI_section]
      _ = qPIK.comp (Submodule.mkQ pPI) := by
            rw [LinearMap.comp_id]
      _ = Submodule.mkQ pPK := by
            simpa [qPIK] using (Submodule.factor_comp_mk hPIK : qPIK.comp (Submodule.mkQ pPI) =
              Submodule.mkQ pPK)
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pPK x
  exact LinearMap.congr_fun hcomp_mk y

/-- Helper for Lemma 10.77.8: the sum of two two-sided ideals is again two-sided. -/
private theorem isTwoSided_sup : (I ⊔ J).IsTwoSided := by
  refine ⟨?_⟩
  intro a b ha
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ha
  exact Submodule.mem_sup.mpr
    ⟨i * b, I.mul_mem_right _ hi, j * b, J.mul_mem_right _ hj, by rw [← add_mul, hij]⟩

/-- Helper for Lemma 10.77.8: compatible classes modulo `I` and `J` admit a common lift in `R`.
This is the coefficient-level Chinese-remainder step used later for the free-cover gluing. -/
private theorem exists_ring_lift_of_compatible_quotients
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
private theorem coeff_mem_ideal_of_mem_smul_top
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

/-- Helper for Lemma 10.77.8: when `I ∩ J = 0`, the paired quotient map on the canonical free
cover is injective. This is the coefficientwise separation needed for the final gluing inverse. -/
private theorem free_cover_pair_injective_of_inf_eq_bot
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
private theorem free_cover_pair_rangeRestrict_bijective_of_inf_eq_bot
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

/-- Helper for Lemma 10.77.8: if an endomorphism is the identity modulo `J`, then it fixes the
submodule `I • ⊤` whenever `I ∩ J = 0`. -/
private theorem eq_on_left_smul_top_of_right_quotient_identity
    (hIJ : I ⊓ J = ⊥)
    (a : P →ₗ[R] P)
    (hQJ :
      ∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (J • (⊤ : Submodule R P))) x) :
    ∀ x ∈ (I • (⊤ : Submodule R P)), a x = x := by
  intro x hx
  -- Reduce to generators `r • m` with `r ∈ I`; the quotient hypothesis makes the error term lie
  -- in `J • ⊤`, so multiplying by `r` lands in `(I * J) • ⊤ = 0`.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    have hdiff :
        a m - m ∈ J • (⊤ : Submodule R P) := by
      exact (Submodule.Quotient.eq (J • (⊤ : Submodule R P))).mp (hQJ m)
    have hsmul :
        r • (a m - m) ∈ I • (J • (⊤ : Submodule R P)) := by
      exact Submodule.smul_mem_smul hr hdiff
    have hzeroSub : I • (J • (⊤ : Submodule R P)) = ⊥ := by
      apply le_antisymm
      · calc
          I • (J • (⊤ : Submodule R P)) = (I * J) • (⊤ : Submodule R P) := by
            simpa using (Submodule.mul_smul I J (⊤ : Submodule R P)).symm
          _ ≤ (I ⊓ J) • (⊤ : Submodule R P) := by
            simpa using
              (Submodule.smul_mono (N := (⊤ : Submodule R P)) Ideal.mul_le_inf le_rfl)
          _ = ⊥ := by simpa [hIJ]
      · exact bot_le
    have hsmul_zero : r • (a m - m) = 0 := by
      have : r • (a m - m) ∈ (⊥ : Submodule R P) := by
        simpa [hzeroSub] using hsmul
      simpa using this
    apply sub_eq_zero.mp
    calc
      a (r • m) - r • m = r • a m - r • m := by simp [map_smul]
      _ = r • (a m - m) := by rw [smul_sub]
      _ = 0 := hsmul_zero
  · intro y z hy hz
    -- The induction closes because the fixed-point condition is additive.
    simp [map_add, hy, hz]

/-- Helper for Lemma 10.77.8: an endomorphism that is the identity on a submodule and on the
quotient by that submodule is bijective. -/
private theorem bijective_of_id_on_submodule_and_quotient
    {M : Type*} [AddCommGroup M] [Module R M]
    (a : M →ₗ[R] M)
    (N : Submodule R M)
    (hN : ∀ x ∈ N, a x = x)
    (hQ : ∀ x : M, (Submodule.mkQ N) (a x) = (Submodule.mkQ N) x) :
    Function.Bijective a := by
  constructor
  · intro x y hxy
    have hxyQ : (Submodule.mkQ N) x = (Submodule.mkQ N) y := by
      calc
        (Submodule.mkQ N) x = (Submodule.mkQ N) (a x) := by simpa using (hQ x).symm
        _ = (Submodule.mkQ N) (a y) := by simpa [hxy]
        _ = (Submodule.mkQ N) y := by simpa using hQ y
    have hsub : x - y ∈ N := by
      exact (Submodule.Quotient.eq N).mp hxyQ
    have hfix : a (x - y) = x - y := hN (x - y) hsub
    have hz : a (x - y) = 0 := by
      simp [hxy]
    have : x - y = 0 := by simpa [hfix] using hz
    exact sub_eq_zero.mp this
  · intro y
    have hdiff : y - a y ∈ N := by
      exact (Submodule.Quotient.eq N).mp (hQ y).symm
    let n : N := ⟨y - a y, hdiff⟩
    refine ⟨y + n, ?_⟩
    -- Correct `y` by the discrepancy term living in `N`.
    calc
      a (y + n) = a y + a n := by simp [map_add]
      _ = a y + n := by rw [hN _ n.property]
      _ = y := by
        simp [n, sub_eq_add_neg, add_left_comm]

/-- Helper for Lemma 10.77.8: once the modulo `I` and modulo `J` splittings of the canonical free
cover are glued source-faithfully, the induced endomorphism of `P` is the identity modulo both
ideals. -/
private theorem exists_glued_free_cover_endomorphism
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
  -- Route correction: the remaining obstruction is the overlap-compatible gluing step, not the
  -- automorphism tail after the endomorphism of `P` has been constructed.
  let K : Ideal R := I ⊔ J
  letI : K.IsTwoSided := by
    simpa [K] using (isTwoSided_sup (R := R) (I := I) (J := J))
  obtain ⟨fI, hfI⟩ :=
    exists_free_cover_section_of_projective_quotient (R := R) (P := P) (K := I) hPI
  obtain ⟨fK, hfK⟩ :=
    mod_i_section_descends_to_sup (R := R) (I := I) (P := P)
      (K := K) (show I ≤ K by exact le_sup_left) fI hfI
  obtain ⟨sJ, hsJ⟩ :=
    exists_free_cover_section_of_projective_quotient (R := R) (P := P) (K := J) hPJ
  -- Step 1 is now in place: the source proof has an explicit descended section modulo
  -- `K = I ⊔ J`, and we also have an auxiliary section modulo `J` available to correct on the
  -- overlap quotient.
  let _ := fI
  let _ := hfI
  let _ := fK
  let _ := hfK
  let _ := sJ
  let _ := hsJ
  let _ := hIJ
  let _ := K
  let _ :=
    free_cover_pair_rangeRestrict_bijective_of_inf_eq_bot (R := R) (P := P) (I := I) (J := J) hIJ
  -- The correction lemma now handles the only source-level lifting inside `K • P`, and the
  -- explicit descended section `fK` removes the earlier quotient-of-quotient ambiguity. The
  -- remaining work is exactly the overlap-compatible mod-`J` section and the final free-cover
  -- fiber-product gluing over `K = I ⊔ J`.
  -- TODO: define the overlap map `q : F/JF → F/KF ×_{P/KP} P/JP`, prove its surjectivity by
  -- correcting a chosen lift with `exists_overlap_correction_in_sup_smul`, use projectivity of
  -- `P/JP` to obtain an overlap-compatible section `gJ`, and then glue `(fI, gJ)` coefficientwise
  -- with `exists_ring_lift_of_compatible_quotients` to hit the paired quotient range.
  sorry

/-- Helper for Lemma 10.77.8: a glued lift whose induced endomorphism is the identity modulo `I`
and `J` already splits the canonical free cover of `P`. -/
private theorem projective_of_glued_free_cover_endomorphism
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

/- 
Domain triage:
- primary domain: projective modules over a ring, glued from projective reductions modulo ideals;
- sampled owner-style declarations of the same kind:
  `Module.Projective.of_split`,
  `Module.Projective.iff_split_of_projective`,
  `Module.projective_of_localization_maximal`,
  `Ideal.pi_tensorProductMk_quotient_surjective`;
- owner abstraction: `Module.Projective R P`;
- primitive data: the ring `R`, module `P`, ideals `I`, `J` with `I ⊓ J = ⊥`, and projectivity of
  the two reductions modulo `I` and `J`;
- derived API: the resulting projectivity of `P`.

This item stays at the `source-facing` layer: it is a patching criterion whose natural public
conclusion is the owner predicate `Module.Projective`, not a renamed wrapper around an existing
owner theorem.
-/

-- Proof sketch: choose a surjection from a free `R`-module onto `P`, split it modulo `I` and
-- modulo `J` using the projectivity assumptions on the two quotients, and glue the two splittings
-- through the fiber-product description coming from `I ⊓ J = ⊥`. The resulting endomorphism of
-- `P` is the identity modulo `I` and modulo `J`, hence is an automorphism, so `P` is a direct
-- summand of a free module.
/-- Lemma 10.77.8: if ideals `I` and `J` of a ring `R` satisfy `I ∩ J = 0`, and the quotient
modules `P / IP` and `P / JP` are projective over `R / I` and `R / J` respectively, then `P` is a
projective `R`-module. -/
theorem projective_of_projective_quotients_of_inf_eq_bot (hIJ : I ⊓ J = ⊥)
    (hPI : Module.Projective (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P)))
    (hPJ : Module.Projective (R ⧸ J) (P ⧸ (J • ⊤ : Submodule R P))) :
    Module.Projective R P := by
  obtain ⟨h, hQI, hQJ⟩ := exists_glued_free_cover_endomorphism hIJ hPI hPJ
  -- Once the source-faithful gluing step is available, the rest is the stable automorphism
  -- correction proved in the helper above.
  exact projective_of_glued_free_cover_endomorphism hIJ h hQI hQJ

end
