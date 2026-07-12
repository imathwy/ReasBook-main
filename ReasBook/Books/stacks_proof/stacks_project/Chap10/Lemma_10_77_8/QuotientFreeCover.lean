import Mathlib

universe u v

namespace Chap10Lemma10778

open Chap10Lemma10778

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

namespace LinearMap

/-- The map on quotients by `K • ⊤` induced by an `R`-linear map. This local abbreviation keeps
Lemma 10.77.8 source-faithful without importing later chapter API. -/
abbrev quotientMapByIdeal
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (K : Ideal R) [K.IsTwoSided] :
    M ⧸ (K • (⊤ : Submodule R M)) →ₗ[R] M' ⧸ (K • (⊤ : Submodule R M')) :=
  (K • (⊤ : Submodule R M)).mapQ (K • (⊤ : Submodule R M')) f
    (Submodule.smul_top_le_comap_smul_top K f)

/-- Helper for Lemma 10.77.8: the quotient map induced by `f` is also linear over the quotient
ring `R ⧸ K`. This is the scalar adapter needed before applying projectivity modulo `K`. -/
abbrev quotientMapByIdeal_over_quotient
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

/-- Helper for Chap10 Lemma 10 77 8: on `M ⧸ K • ⊤`, scalar multiplication by `r : R`
agrees with scalar multiplication by its class in `R ⧸ K`. -/
theorem quotient_smul_eq_quotient_mk_smul
    (K : Ideal R) [K.IsTwoSided]
    {M : Type*} [AddCommGroup M] [Module R M]
    (r : R) (x : M ⧸ (K • (⊤ : Submodule R M))) :
    r • x = (Ideal.Quotient.mk K r) • x := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) x
  change (Submodule.mkQ (K • (⊤ : Submodule R M))) (r • m) =
    (Ideal.Quotient.mk K r) • (Submodule.mkQ (K • (⊤ : Submodule R M))) m
  exact (Module.Quotient.mk_smul_mk M K r m).symm

/-- Helper for Lemma 10.77.8: a surjective linear map induces a surjective map on compatible
quotients. -/
theorem mapQ_surjective_of_surjective
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
theorem canonical_free_cover_surjective :
    Function.Surjective (Finsupp.linearCombination R (id : P → P)) := by
  -- Every `x : P` is hit by the singleton basis vector at `x`.
  simpa using Finsupp.linearCombination_surjective R Function.surjective_id

/-- Helper for Lemma 10.77.8: the canonical free cover stays surjective after reducing modulo an
ideal. -/
theorem canonical_free_cover_quotient_surjective
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
theorem canonical_free_cover_preimage_mem_smul_top
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
theorem exists_overlap_correction_in_sup_smul
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
theorem exists_free_cover_section_of_projective_quotient
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
theorem mod_i_section_descends_to_sup
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
        LinearMap.id ∧
      fK.comp
          (Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono hIK (show (⊤ : Submodule R P) ≤ ⊤ by rfl)) :
                  I • (⊤ : Submodule R P) ≤ K • (⊤ : Submodule R P))) =
        ((Submodule.factor
            (by
              simpa using
                (Submodule.smul_mono hIK (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl)) :
                  I • (⊤ : Submodule R (P →₀ R)) ≤
                    K • (⊤ : Submodule R (P →₀ R)))).comp (fI.restrictScalars R)) := by
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
  refine ⟨pPK.liftQ raw hraw_ker, ?_, ?_⟩
  · refine DFunLike.ext _ _ fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pPK x
    exact LinearMap.congr_fun hcomp_mk y
  · -- Both composites send a class modulo `I` to the same reduced free-cover section modulo `K`.
    refine DFunLike.ext _ _ fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pPI x
    rfl

/-- Helper for Chap10 Lemma 10 77 8: the quotient factor map from modulo `J` to modulo a larger
ideal `K` sends a representative to the same representative modulo `K`. -/
@[simp] theorem factorToSup_mk
    {K : Ideal R} [K.IsTwoSided]
    (hJK : J ≤ K)
    {M : Type*} [AddCommGroup M] [Module R M]
    (x : M) :
    Submodule.factor
        (by
          simpa using
            (Submodule.smul_mono hJK (show (⊤ : Submodule R M) ≤ ⊤ by rfl) :
              J • (⊤ : Submodule R M) ≤ K • (⊤ : Submodule R M)))
        (Submodule.mkQ (J • (⊤ : Submodule R M)) x) =
      Submodule.mkQ (K • (⊤ : Submodule R M)) x := by
  simpa using
    (Submodule.factor_mk
      (by
        simpa using
          (Submodule.smul_mono hJK (show (⊤ : Submodule R M) ≤ ⊤ by rfl) :
            J • (⊤ : Submodule R M) ≤ K • (⊤ : Submodule R M)))
      x)

/-- Helper for Chap10 Lemma 10 77 8: the quotient factor map from modulo `J` to modulo a larger
ideal `K` is surjective. -/
theorem factorToSup_surjective
    {K : Ideal R} [K.IsTwoSided]
    (hJK : J ≤ K)
    {M : Type*} [AddCommGroup M] [Module R M] :
    Function.Surjective
      (Submodule.factor
        (by
          simpa using
            (Submodule.smul_mono hJK (show (⊤ : Submodule R M) ≤ ⊤ by rfl) :
              J • (⊤ : Submodule R M) ≤ K • (⊤ : Submodule R M)))) := by
  intro y
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) y
  refine ⟨Submodule.mkQ (J • (⊤ : Submodule R M)) m, ?_⟩
  simp [factorToSup_mk]

end

end Chap10Lemma10778
