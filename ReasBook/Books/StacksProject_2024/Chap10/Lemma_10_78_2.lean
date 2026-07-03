import Mathlib
import StacksProject_2024.Chap10.Definition_10_78_1
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_20_2
import StacksProject_2024.Chap10.Lemma_10_23_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped TensorProduct

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: commutative algebra of finite projective modules, finite free splittings, and
  Zariski-local freeness on `Spec R`;
- sampled owner declarations of the same kind:
  `Module.Projective.iff_split`,
  `Module.freeLocus_eq_univ_iff`,
  `Module.freeLocus_eq_univ`,
  `Module.isLocallyConstant_rankAtStalk`;
- owner abstraction: the chapter owner `Module.FiniteLocallyFree R M`, together with the canonical
  mathlib owners `Module.Projective R M` and `Module.freeLocus R M`;
- primitive data: only the ring `R` and the module `M`;
- derived API: the finite-free direct-summand clause, the free-locus formulations, and the
  finite-locally-free bridge theorem below.

Source/core/bridge triage:
- `module_finite_projective_tfae` is `source-facing`: it records the textbook list of equivalent
  criteria, but each clause should use the most canonical available owner surface;
- `Module.finiteLocallyFree_of_finitePresentation_of_flat` is `bridge/view`: it extracts the
  chapter owner `Module.FiniteLocallyFree` from the source-facing TFAE.

Refinement note:
- clause `(3)` is stated using the canonical finite free model `ι → R` with `[Finite ι]`, rather
  than existentially packaging an arbitrary free finite ambient module and its instance data.
-/

-- Proof sketch: the implications use the standard chain of results for finitely presented flat
-- modules: `Module.Flat.projective_of_finitePresentation`, the direct-summand characterization
-- `Module.Projective.iff_split`, local freeness over local rings via
-- `Module.free_of_flat_of_isLocalRing`, descent of projectivity from maximal localizations by
-- `Module.projective_of_localization_maximal`, and the canonical local-constancy theorem for the
-- rank function `Module.isLocallyConstant_rankAtStalk`. The textbook clauses (6) and (7) are
-- expressed directly by Zariski-local freeness on a standard-open cover.
/-- Helper for Lemma 10.78.2: a finite locally free module is finite. -/
theorem Module.finite_of_finiteLocallyFree [Module.FiniteLocallyFree R M] :
    Module.Finite R M := by
  rcases Module.FiniteLocallyFree.exists_standardOpen_cover (R := R) (M := M) with
    ⟨s, hs, hloc⟩
  -- Descend finite generation from the chosen standard-open cover.
  exact Module.Finite.of_localizationSpan s hs fun f ↦ (hloc f.1 f.2).2

/-- Helper for Lemma 10.78.2: a finite module that is locally free is finite locally free. -/
theorem Module.finiteLocallyFree_of_finite_and_locallyFree
    [Module.Finite R M] [Module.LocallyFree R M] :
    Module.FiniteLocallyFree R M := by
  rcases Module.LocallyFree.exists_standardOpen_cover (R := R) (M := M) with ⟨s, hs, hloc⟩
  refine ⟨⟨s, hs, ?_⟩⟩
  -- Keep the same free cover and localize the global finite-generation witness.
  intro f hf
  exact ⟨hloc f hf, inferInstance⟩

/-- Helper for Lemma 10.78.2: finite presentation plus `freeLocus = univ` yields finite local
freeness. -/
theorem Module.finiteLocallyFree_of_finitePresentation_of_freeLocus_eq_univ
    [Module.FinitePresentation R M] (hfree : Module.freeLocus R M = Set.univ) :
    Module.FiniteLocallyFree R M := by
  let t : Set R := { f : R |
    Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) }
  have ht_span : Ideal.span t = ⊤ := by
    -- Every prime lies in the free locus, so some basic open around it trivializes `M`.
    by_contra htop
    obtain ⟨m, hm, hle⟩ := (Ideal.span t).exists_le_maximal htop
    let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    have hp_free : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
      simpa [Module.freeLocus, hfree] using (show p ∈ Module.freeLocus R M by simp [hfree])
    letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :=
      hp_free
    obtain ⟨f, hf, hffree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (Localization.AtPrime p.asIdeal)
    have hft : f ∈ t := by
      exact ⟨hffree, inferInstance⟩
    have hfmem : f ∈ m := hle (Ideal.subset_span hft)
    exact hf hfmem
  -- Package the local finite free trivializations as a `FiniteLocallyFree` witness.
  refine ⟨⟨t, ht_span, ?_⟩⟩
  intro f hf
  exact hf

/-- Helper for Lemma 10.78.2: a finite locally free module is finitely presented. -/
theorem Module.finitePresentation_of_finiteLocallyFree [Module.FiniteLocallyFree R M] :
    Module.FinitePresentation R M := by
  rcases Module.FiniteLocallyFree.exists_standardOpen_cover (R := R) (M := M) with
    ⟨s, hs, hloc⟩
  have hone : (1 : R) ∈ Ideal.span s := (Ideal.eq_top_iff_one _).mp hs
  obtain ⟨t, hts, h1⟩ := Submodule.mem_span_finite_of_mem_span hone
  have ht : Ideal.span (t : Set R) = ⊤ := by
    exact (Ideal.eq_top_iff_one _).mpr h1
  -- Reduce to a finite subcover, then apply the standard finite-presentation descent theorem.
  exact module_finitePresentation_of_localizationAway (R := R) (M := M) t ht fun f ↦ by
    letI : Module.Free (Localization.Away f.1) (LocalizedModule.Away f.1 M) :=
      (hloc f.1 (hts f.2)).1
    letI : Module.Finite (Localization.Away f.1) (LocalizedModule.Away f.1 M) :=
      (hloc f.1 (hts f.2)).2
    exact Module.finitePresentation_of_projective _ _

/-- Helper for Lemma 10.78.2: a finite locally free module has free stalks everywhere. -/
theorem Module.freeLocus_eq_univ_of_finiteLocallyFree [Module.FiniteLocallyFree R M] :
    Module.freeLocus R M = Set.univ := by
  letI : Module.FinitePresentation R M :=
    Module.finitePresentation_of_finiteLocallyFree (R := R) (M := M)
  rcases Module.FiniteLocallyFree.exists_standardOpen_cover (R := R) (M := M) with
    ⟨s, hs, hloc⟩
  ext p
  constructor
  · intro _
    simp
  · intro _
    have hbasic : ∃ f ∈ s, f ∉ p.asIdeal := by
      by_contra h
      have hs_le : Ideal.span s ≤ p.asIdeal := by
        refine Ideal.span_le.mpr ?_
        intro f hf
        by_contra hf'
        exact h ⟨f, hf, hf'⟩
      have hp_top : p.asIdeal = ⊤ := top_le_iff.mp (hs ▸ hs_le)
      exact p.isPrime.ne_top hp_top
    rcases hbasic with ⟨f, hf, hfp⟩
    have hsubset : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R M := by
      rw [Module.basicOpen_subset_freeLocus_iff]
      letI : Module.Free (Localization.Away f) (LocalizedModule.Away f M) := (hloc f hf).1
      infer_instance
    exact hsubset ((PrimeSpectrum.mem_basicOpen f p).2 hfp)

/-- Helper for Lemma 10.78.2: a locally constant stalk-rank function is constant on some
basic-open neighborhood of each prime. -/
theorem Module.exists_basicOpen_eq_rankAtStalk
    (hrank :
      IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ)))
    (p : PrimeSpectrum R) :
    ∃ g : R, g ∉ p.asIdeal ∧
      ∀ q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)),
        Module.rankAtStalk (R := R) M q = Module.rankAtStalk (R := R) M p := by
  rcases hrank.exists_open p with ⟨U, hU, hpU, hconst⟩
  obtain ⟨V, ⟨g, rfl⟩, hpV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU p hpU
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g p).1 hpV, ?_⟩
  intro q hq
  exact Int.ofNat.inj (hconst q (hVU hq))

/-- Helper for Lemma 10.78.2: a surjective map from a rank-`r` finite free module to another
finite free module of finrank `r` is bijective. -/
theorem linearMap_bijective_of_surjective_fin_fun_of_finrank_eq
    {A : Type*} [CommRing A] [Nontrivial A] {N : Type*} [AddCommGroup N] [Module A N] {r : ℕ}
    (φ : (Fin r → A) →ₗ[A] N) (hφ : Function.Surjective φ)
    [Module.Free A N] [Module.Finite A N] (hr : Module.finrank A N = r) :
    Function.Bijective φ := by
  let e : N ≃ₗ[A] (Fin r → A) :=
    (Module.finBasisOfFinrankEq A N hr).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A (Fin r)
  let ψ : Module.End A (Fin r → A) := e.toLinearMap.comp φ
  have hψ_surj : Function.Surjective ψ := e.surjective.comp hφ
  have hψ_inj : Function.Injective ψ :=
    Module.End.injective_of_surjective_fin (f := ψ) hψ_surj
  refine ⟨fun x y hxy ↦ ?_, hφ⟩
  exact hψ_inj (by simpa [ψ] using hxy)

/-- Helper for Lemma 10.78.2: a surjective map between finite free modules of the same finite
rank is bijective. -/
private theorem linearMap_bijective_of_surjective_of_free_of_finrank_eq
    {A : Type*} [CommRing A] [Nontrivial A]
    {P : Type*} [AddCommGroup P] [Module A P]
    {N : Type*} [AddCommGroup N] [Module A N]
    (φ : P →ₗ[A] N) (hφ : Function.Surjective φ)
    [Module.Free A P] [Module.Finite A P] [Module.Free A N] [Module.Finite A N]
    {r : ℕ} (hP : Module.finrank A P = r) (hN : Module.finrank A N = r) :
    Function.Bijective φ := by
  let eP : P ≃ₗ[A] (Fin r → A) :=
    (Module.finBasisOfFinrankEq A P hP).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A (Fin r)
  let ψ : (Fin r → A) →ₗ[A] N := φ.comp eP.symm.toLinearMap
  have hψ : Function.Surjective ψ := hφ.comp eP.symm.surjective
  have hψ_bij :
      Function.Bijective ψ :=
    linearMap_bijective_of_surjective_fin_fun_of_finrank_eq
      (A := A) (N := N) (r := r) ψ hψ hN
  refine ⟨fun x y hxy ↦ ?_, hφ⟩
  exact eP.injective (hψ_bij.1 (by simpa [ψ] using hxy))

/-- Helper for Lemma 10.78.2: at a maximal ideal, reducing modulo `m` computes the same fiber
rank as `Module.rankAtStalk`. -/
private theorem Module.finrank_quotient_smul_top_eq_rankAtStalk_at_maximal
    [Module.Finite R M] [Module.Flat R M]
    (m : Ideal R) [m.IsMaximal] :
    Module.finrank (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M)) =
      Module.rankAtStalk (R := R) M ⟨m, inferInstance⟩ := by
  let e : (R ⧸ m) ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  let j : ((R ⧸ m) ⊗[R] M) ≃ₗ[R] m.ResidueField ⊗[R] M :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  let eQ : ((R ⧸ m) ⊗[R] M) ≃ₗ[R ⧸ m] (M ⧸ m • (⊤ : Submodule R M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M m).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  have hj :
      ∀ (r : R ⧸ m) (x : TensorProduct R (R ⧸ m) M),
        j (r • x) = e r • j x := by
    intro r x
    -- Compare the scalar actions before transporting finrank across the quotient-residue-field
    -- equivalence.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a y
      change e (r * a) ⊗ₜ[R] y = e r • (e a ⊗ₜ[R] y)
      rw [map_mul]
      rfl
    · intro x y hx hy
      simp [smul_add, hx, hy]
  have htensor :
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) =
        Module.finrank m.ResidueField (m.ResidueField ⊗[R] M) := by
    have hrank :
        Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] M) =
          Module.rank m.ResidueField (m.ResidueField ⊗[R] M) :=
      rank_eq_of_equiv_equiv e.toRingEquiv j.toAddEquiv e.toRingEquiv.bijective hj
    change
      Cardinal.toNat (Module.rank (R ⧸ m) (TensorProduct R (R ⧸ m) M)) =
        Cardinal.toNat (Module.rank m.ResidueField (TensorProduct R m.ResidueField M))
    exact congrArg Cardinal.toNat hrank
  -- First identify the quotient with the tensor over `R ⧸ m`, then pass from `R ⧸ m` to the
  -- residue field, and finally rewrite by the canonical stalk-rank formula.
  calc
    Module.finrank (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M)) =
        Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) := by
          exact eQ.finrank_eq.symm
    _ = Module.finrank m.ResidueField (m.ResidueField ⊗[R] M) := htensor
    _ = Module.rankAtStalk (R := R) M ⟨m, inferInstance⟩ := by
          symm
          exact Module.rankAtStalk_eq (R := R) (M := M) ⟨m, inferInstance⟩

/-- Helper for Lemma 10.78.2: localizing a linear map is injective exactly when the localized
kernel module is trivial. -/
private theorem localized_map_injective_iff_subsingleton_kernel
    {P : Type*} [AddCommGroup P] [Module R P] {N : Type*} [AddCommGroup N] [Module R N]
    (φ : P →ₗ[R] N) (S : Submonoid R) :
    Function.Injective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (LinearMap.ker φ)) := by
  let κ : LinearMap.ker φ →ₗ[R] LinearMap.ker (LocalizedModule.map S φ) :=
    LinearMap.toKerIsLocalized
      (p := S)
      (f := LocalizedModule.mkLinearMap S P)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  let _ : IsLocalizedModule S κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization S)
      (p := S)
      (f := LocalizedModule.mkLinearMap S P)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  -- Compare the localized kernel module with the actual kernel after localizing the map.
  constructor
  · intro hφ
    have hker :
        LinearMap.ker (LocalizedModule.map S φ) = ⊥ :=
      LinearMap.ker_eq_bot.2 hφ
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      Submodule.subsingleton_iff_eq_bot.2 hker
    exact ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).2 hsub
  · intro hker
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).1 hker
    exact LinearMap.ker_eq_bot.1 (Submodule.subsingleton_iff_eq_bot.1 hsub)

/-- Helper for Lemma 10.78.2: localizing a linear map is surjective exactly when the localized
cokernel module is trivial. -/
private theorem localized_map_surjective_iff_subsingleton_cokernel
    {P : Type*} [AddCommGroup P] [Module R P] {N : Type*} [AddCommGroup N] [Module R N]
    (φ : P →ₗ[R] N) (S : Submonoid R) :
    Function.Surjective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (N ⧸ LinearMap.range φ)) := by
  let ψ : LocalizedModule S P →ₗ[Localization S] LocalizedModule S N := LocalizedModule.map S φ
  have hRange :
      LinearMap.range ψ = (LinearMap.range φ).localized S := by
    -- Rewrite the localized range through the canonical range-localization compatibility theorem.
    symm
    simpa [ψ, Submodule.localized] using
      (LinearMap.localized'_range_eq_range_localizedMap
        (S := Localization S)
        (p := S)
        (f := LocalizedModule.mkLinearMap S P)
        (f' := LocalizedModule.mkLinearMap S N)
        φ)
  let eQuot :
      (LocalizedModule S N ⧸ (LinearMap.range φ).localized S) ≃ₗ[Localization S]
        LocalizedModule S (N ⧸ LinearMap.range φ) :=
    localizedQuotientEquiv
      (p := S)
      (M' := LinearMap.range φ)
  let e :
      (LocalizedModule S N ⧸ LinearMap.range ψ) ≃ₗ[Localization S]
        LocalizedModule S (N ⧸ LinearMap.range φ) :=
    (Submodule.quotEquivOfEq _ _ hRange).trans eQuot
  constructor
  · intro hφ
    have hsub :
        Subsingleton (LocalizedModule S N ⧸ LinearMap.range ψ) := by
      -- A surjective localized map has quotient by its range equal to the zero module.
      exact (Submodule.Quotient.subsingleton_iff).2 (LinearMap.range_eq_top.2 hφ)
    exact (e.toEquiv.subsingleton_congr).1 hsub
  · intro hsub
    have hsub' :
        Subsingleton (LocalizedModule S N ⧸ LinearMap.range ψ) :=
      (e.toEquiv.subsingleton_congr).2 hsub
    -- Triviality of the localized cokernel says that the localized range is all of the codomain.
    exact LinearMap.range_eq_top.1 ((Submodule.Quotient.subsingleton_iff).1 hsub')

/-- Helper for Lemma 10.78.2: if a linear map is injective after localizing at every prime of the
basic open `D(a)`, then it is already injective after inverting `a`. -/
private theorem map_injective_away_of_basicOpen_localized_injective
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P]
    {N : Type*} [AddCommGroup N] [Module R N]
    (φ : P →ₗ[R] N) (a : R)
    (hlocal :
      ∀ q ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)),
        Function.Injective (LocalizedModule.map q.asIdeal.primeCompl φ)) :
    Function.Injective (LocalizedModule.map (.powers a) φ) := by
  -- Descend injectivity by showing that the kernel support misses the whole basic open `D(a)`.
  have hsub :
      Subsingleton (LocalizedModule (.powers a) (LinearMap.ker φ)) := by
    rw [LocalizedModule.subsingleton_iff_disjoint]
    refine Set.disjoint_left.2 ?_
    intro q hq_basic hq_support
    have hqKernel :
        Subsingleton (LocalizedModule q.asIdeal.primeCompl (LinearMap.ker φ)) :=
      (localized_map_injective_iff_subsingleton_kernel
        (R := R) (P := P) (N := N) φ q.asIdeal.primeCompl).mp
        (hlocal q hq_basic)
    -- A trivial localized kernel means that `q` is outside the kernel support, contradicting
    -- the assumed support membership.
    exact ((Module.notMem_support_iff).2 hqKernel) hq_support
  -- Convert the vanishing of the away-localized kernel back into injectivity of the away map.
  exact
    (localized_map_injective_iff_subsingleton_kernel
      (R := R) (P := P) (N := N) φ (.powers a)).mpr hsub

/-- Helper for Lemma 10.78.2: if a linear map is surjective after localizing at every prime of the
basic open `D(a)`, then it is already surjective after inverting `a`. -/
private theorem map_surjective_away_of_basicOpen_localized_surjective
    {P : Type*} [AddCommGroup P] [Module R P]
    {N : Type*} [AddCommGroup N] [Module R N]
    (φ : P →ₗ[R] N) (a : R)
    (hlocal :
      ∀ q ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)),
        Function.Surjective (LocalizedModule.map q.asIdeal.primeCompl φ)) :
    Function.Surjective (LocalizedModule.map (.powers a) φ) := by
  -- Descend surjectivity by showing that the cokernel support misses the whole basic open `D(a)`.
  have hsub :
      Subsingleton (LocalizedModule (.powers a) (N ⧸ LinearMap.range φ)) := by
    rw [LocalizedModule.subsingleton_iff_disjoint]
    refine Set.disjoint_left.2 ?_
    intro q hq_basic hq_support
    have hqCoker :
        Subsingleton (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range φ)) :=
      (localized_map_surjective_iff_subsingleton_cokernel
        (R := R) (P := P) (N := N) φ q.asIdeal.primeCompl).mp
        (hlocal q hq_basic)
    -- A trivial localized cokernel means that `q` is outside the cokernel support.
    exact ((Module.notMem_support_iff).2 hqCoker) hq_support
  -- Convert the vanishing of the away-localized cokernel back into surjectivity of the away map.
  exact
    (localized_map_surjective_iff_subsingleton_cokernel
      (R := R) (P := P) (N := N) φ (.powers a)).mpr hsub

/-- Helper for Lemma 10.78.2: localizing the free module `(Fin r → R)` yields the canonical
`Fin r`-indexed free module over the localized ring. -/
private noncomputable def localized_fin_fun_equiv
    (S : Submonoid R) (r : ℕ) :
    LocalizedModule S (Fin r → R) ≃ₗ[Localization S] (Fin r → Localization S) :=
  let fS : (Fin r → R) →ₗ[R] (Fin r → Localization S) :=
    .pi fun i : Fin r ↦ (LocalizedModule.mkLinearMap S R) ∘ₗ LinearMap.proj i
  (IsLocalizedModule.iso S fS).extendScalarsOfIsLocalization S (Localization S)

/-- Helper for Lemma 10.78.2: at a prime, the localized source `(Fin r → R)` is canonically the
standard free `Fin r`-module over the local ring. -/
private noncomputable def localized_fin_fun_equiv_atPrime
    (q : PrimeSpectrum R) (r : ℕ) :
    LocalizedModule q.asIdeal.primeCompl (Fin r → R) ≃ₗ[Localization.AtPrime q.asIdeal]
      (Fin r → Localization.AtPrime q.asIdeal) :=
  localized_fin_fun_equiv (R := R) q.asIdeal.primeCompl r

/-- Helper for Lemma 10.78.2: if the family `x` generates after inverting `f`, then the
comparison map is surjective over `R_f`. -/
private theorem comparisonMap_surjective_away_of_span_localized_eq_top
    {r : ℕ} (x : Fin r → M) {f : R}
    (hspan : (Submodule.span R (Set.range x)).localized (.powers f) = ⊤) :
    Function.Surjective (LocalizedModule.map (.powers f) (Fintype.linearCombination R x)) := by
  let φx : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R x
  have hrange :
      LinearMap.range (LocalizedModule.map (.powers f) φx) =
        (Submodule.span R (Set.range x)).localized (.powers f) := by
    calc
      LinearMap.range (LocalizedModule.map (.powers f) φx)
          = (LinearMap.range φx).localized (.powers f) := by
              symm
              simpa [Submodule.localized] using
                (LinearMap.localized'_range_eq_range_localizedMap
                  (S := Localization (.powers f))
                  (p := .powers f)
                  (f := LocalizedModule.mkLinearMap (.powers f) (Fin r → R))
                  (f' := LocalizedModule.mkLinearMap (.powers f) M)
                  φx)
      _ = (Submodule.span R (Set.range x)).localized (.powers f) := by
            rw [Fintype.range_linearCombination]
  -- Surjectivity is equivalent to the localized range being all of `M_f`.
  exact LinearMap.range_eq_top.1 (hrange.trans hspan)

/-- Helper for Lemma 10.78.2: if the family `x` generates after inverting `f`, then at every prime
of `D(f)` the localized comparison map is surjective. -/
private theorem comparisonMap_surjective_atPrime_of_span_localized_eq_top
    {r : ℕ} (x : Fin r → M) {f : R}
    (hspan : (Submodule.span R (Set.range x)).localized (.powers f) = ⊤)
    (q : PrimeSpectrum R) (hfq : f ∉ q.asIdeal) :
    Function.Surjective (LocalizedModule.map q.asIdeal.primeCompl (Fintype.linearCombination R x)) := by
  let N : Submodule R M := Submodule.span R (Set.range x)
  have hpq : Submonoid.powers f ≤ q.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl] using hfq
  have hNq : N.localized q.asIdeal.primeCompl = ⊤ := by
    refine top_unique ?_
    intro z _
    induction z using LocalizedModule.induction_on with
    | _ m s =>
        have hm_f :
            LocalizedModule.mkLinearMap (.powers f) M m ∈ N.localized (.powers f) := by
          rw [hspan]
          simp [LocalizedModule.mkLinearMap_apply]
        rcases (Submodule.mem_localized'
            (S := Localization (.powers f))
            (p := .powers f)
            (f := LocalizedModule.mkLinearMap (.powers f) M)
            (M' := N)
            (LocalizedModule.mkLinearMap (.powers f) M m)).1 hm_f with
          ⟨n, hn, t, ht⟩
        let l :
            LocalizedModule.Away f M →ₗ[R] LocalizedModule.AtPrime q.asIdeal M :=
          IsLocalizedModule.liftOfLE (.powers f) q.asIdeal.primeCompl hpq
            (LocalizedModule.mkLinearMap (.powers f) M)
            (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
        have hlm :
            l (LocalizedModule.mk m (1 : Submonoid.powers f)) =
              IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m
                (1 : q.asIdeal.primeCompl) := by
          change l (LocalizedModule.mkLinearMap (.powers f) M m) =
            IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m
              (1 : q.asIdeal.primeCompl)
          simpa [IsLocalizedModule.mk'_one, l] using
            (IsLocalizedModule.liftOfLE_apply
              (S₁ := .powers f)
              (S₂ := q.asIdeal.primeCompl)
              (h := hpq)
              (f₁ := LocalizedModule.mkLinearMap (.powers f) M)
              (f₂ := LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
              (x := m))
        have hnum :
            IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) n
                ⟨t.1, hpq t.2⟩ =
              IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m
                (1 : q.asIdeal.primeCompl) := by
          calc
            IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) n
                ⟨t.1, hpq t.2⟩ =
                  l (LocalizedModule.mk m (1 : Submonoid.powers f)) := by
                    simpa [LocalizedModule.mkLinearMap_apply, l] using congrArg l ht
            _ =
                IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m
                  (1 : q.asIdeal.primeCompl) := hlm
        have hm_one :
            IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m
                (1 : q.asIdeal.primeCompl) ∈ N.localized q.asIdeal.primeCompl := by
          refine (Submodule.mem_localized'
            (S := Localization.AtPrime q.asIdeal)
            (p := q.asIdeal.primeCompl)
            (f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
            (M' := N)
            (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m
              (1 : q.asIdeal.primeCompl))).2 ?_
          exact ⟨n, hn, ⟨t.1, hpq t.2⟩, by simpa using hnum⟩
        have hmk :
            LocalizedModule.mk m s =
              IsLocalization.mk' (Localization.AtPrime q.asIdeal) 1 s •
                IsLocalizedModule.mk'
                  (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m
                  (1 : q.asIdeal.primeCompl) := by
          rw [IsLocalizedModule.mk_eq_mk']
          symm
          simpa using
            (IsLocalizedModule.mk'_smul_mk'
              (A := Localization.AtPrime q.asIdeal)
              (f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
              1 m s (1 : q.asIdeal.primeCompl))
        rw [hmk]
        exact Submodule.smul_mem _ _ hm_one
  let φx : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R x
  have hrange :
      LinearMap.range (LocalizedModule.map q.asIdeal.primeCompl φx) =
        N.localized q.asIdeal.primeCompl := by
    calc
      LinearMap.range (LocalizedModule.map q.asIdeal.primeCompl φx)
          = (LinearMap.range φx).localized q.asIdeal.primeCompl := by
              symm
              simpa [Submodule.localized] using
                (LinearMap.localized'_range_eq_range_localizedMap
                  (S := Localization.AtPrime q.asIdeal)
                  (p := q.asIdeal.primeCompl)
                  (f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl (Fin r → R))
                  (f' := LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
                  φx)
      _ = N.localized q.asIdeal.primeCompl := by
            rw [Fintype.range_linearCombination]
  -- Once the localized span is all of `M_q`, the localized comparison map is surjective.
  exact LinearMap.range_eq_top.1 (hrange.trans hNq)

/-- Helper for Lemma 10.78.2: the canonical map `M_f → M_{fg}` used to pass from the generator
chart on `D(f)` to the smaller chart on `D(fg)`. -/
private theorem away_moduleEnd_isUnit_of_dvd
    {K : Type*} [AddCommGroup K] [Module R K]
    (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule.Away x K)) r) := by
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (LocalizedModule.Away x K) :=
    Algebra.lsmul R R (LocalizedModule.Away x K)
  simpa [Algebra.smul_def] using h'.map lsmulAway

/-- Helper for Lemma 10.78.2: the canonical map `M_f → M_{fg}` used to pass from the generator
chart on `D(f)` to the smaller chart on `D(fg)`. -/
private noncomputable def away_product_right_linear_map
    {K : Type*} [AddCommGroup K] [Module R K]
    (f g : R) :
    LocalizedModule.Away f K →ₗ[R] LocalizedModule.Away (f * g) K :=
  LocalizedModule.lift (.powers f)
    (LocalizedModule.mkLinearMap (.powers (f * g)) K)
    (fun x ↦ by
      rcases (Submonoid.mem_powers_iff x.1 f).1 x.2 with ⟨n, hn⟩
      have hf_unit :
          IsUnit (algebraMap R (Module.End R (LocalizedModule.Away (f * g) K)) f) :=
        away_moduleEnd_isUnit_of_dvd (R := R) (K := K) (f * g) f (dvd_mul_right f g)
      rw [← hn]
      simpa using hf_unit.pow n)

/-- Helper for Lemma 10.78.2: the away-`f` to away-`fg` map sends canonical numerators to their
obvious direct images. -/
private theorem away_product_right_linear_map_apply_mk
    {K : Type*} [AddCommGroup K] [Module R K]
    (f g : R) (m : K) :
    away_product_right_linear_map (R := R) (K := K) f g
      (LocalizedModule.mkLinearMap (.powers f) K m) =
        LocalizedModule.mkLinearMap (.powers (f * g)) K m := by
  -- This is the defining computation rule for the localization lift.
  simpa [away_product_right_linear_map] using
    (LocalizedModule.lift_mk_one
      (S := .powers f)
      (g := LocalizedModule.mkLinearMap (.powers (f * g)) K)
      (h := fun x ↦ by
        rcases (Submonoid.mem_powers_iff x.1 f).1 x.2 with ⟨n, hn⟩
        have hf_unit :
            IsUnit (algebraMap R (Module.End R (LocalizedModule.Away (f * g) K)) f) :=
          away_moduleEnd_isUnit_of_dvd (R := R) (K := K) (f * g) f (dvd_mul_right f g)
        rw [← hn]
        simpa using hf_unit.pow n)
      (m := m))

/-- Helper for Lemma 10.78.2: on `D(f * g)`, the localized comparison map is injective once the
`D(f)` generator chart and the constant stalk-rank chart on `D(g)` are fixed. -/
private theorem comparisonMap_injective_atPrime_of_span_localized_eq_top_and_rank_const
    [Module.Finite R M]
    {r : ℕ} (x : Fin r → M) {f g : R}
    (hspan : (Submodule.span R (Set.range x)).localized (.powers f) = ⊤)
    (hfree : Module.freeLocus R M = Set.univ)
    (hrank :
      ∀ q ∈ (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)),
        Module.rankAtStalk (R := R) M q = r)
    (q : PrimeSpectrum R) (hq : q ∈ (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R))) :
    Function.Injective (LocalizedModule.map q.asIdeal.primeCompl (Fintype.linearCombination R x)) := by
  let φq :
      LocalizedModule q.asIdeal.primeCompl (Fin r → R) →ₗ[Localization.AtPrime q.asIdeal]
        LocalizedModule.AtPrime q.asIdeal M :=
    LocalizedModule.map q.asIdeal.primeCompl (Fintype.linearCombination R x)
  have hfgq : f * g ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen (f * g) q).1 hq
  have hfq : f ∉ q.asIdeal := by
    intro hf
    exact hfgq (q.asIdeal.mul_mem_right g hf)
  have hq_free_mem : q ∈ Module.freeLocus R M := by
    simpa [hfree]
  letI : Module.Free (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal M) := by
    simpa [Module.freeLocus] using hq_free_mem
  have hφq_surj : Function.Surjective φq :=
    comparisonMap_surjective_atPrime_of_span_localized_eq_top
      (R := R) (M := M) x hspan q hfq
  have hfinrank :
      Module.finrank (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal M) = r := by
    -- On `D(f * g)`, the codomain finrank is exactly the constant stalk rank prescribed by `hrank`.
    simpa [Module.rankAtStalk] using hrank q hq
  let e :
      LocalizedModule q.asIdeal.primeCompl (Fin r → R) ≃ₗ[Localization.AtPrime q.asIdeal]
        (Fin r → Localization.AtPrime q.asIdeal) :=
    localized_fin_fun_equiv_atPrime (R := R) q r
  let ψ :
      (Fin r → Localization.AtPrime q.asIdeal) →ₗ[Localization.AtPrime q.asIdeal]
        LocalizedModule.AtPrime q.asIdeal M :=
    φq.comp e.symm.toLinearMap
  have hψ_surj : Function.Surjective ψ := hφq_surj.comp e.symm.surjective
  have hψ_bij : Function.Bijective ψ :=
    linearMap_bijective_of_surjective_fin_fun_of_finrank_eq
      (A := Localization.AtPrime q.asIdeal)
      (N := LocalizedModule.AtPrime q.asIdeal M)
      (r := r) ψ hψ_surj hfinrank
  -- Normalize the localized source to the standard free `Fin r`-module and read injectivity back.
  intro u v huv
  apply e.injective
  exact hψ_bij.1 (by simpa [ψ, φq] using huv)

/-- Helper for Lemma 10.78.2: a basis of `M / mM` lifts to generators on some basic open missing
`m`. -/
private theorem exists_away_span_eq_top_of_basis_mod_maximal
    [Module.Finite R M] (m : Ideal R) [m.IsMaximal] {r : ℕ} (x : Fin r → M)
    (hspan :
      Submodule.span (R ⧸ m)
        (Set.range ((Submodule.mkQ (m • (⊤ : Submodule R M))) ∘ x)) = ⊤) :
    ∃ f : R, f ∉ m ∧
      (Submodule.span R (Set.range x)).localized (.powers f) = ⊤ := by
  let N : Submodule R M := m • (⊤ : Submodule R M)
  have hgen :
      (Submodule.span (R ⧸ m) (Set.range ((Submodule.mkQ N) ∘ x))).localized
        (Algebra.algebraMapSubmonoid (R ⧸ m) (.powers (1 : R))) = ⊤ := by
    -- Localizing the quotient span at powers of `1` does not change the top submodule.
    rw [hspan]
    simp
  obtain ⟨f, hfmem, htop⟩ :=
    exists_mem_submonoid_add_ideal_and_span_localizedAway_eq_top_of_quotient_span_eq_top
      (R := R) (M := M) (I := m) (S := .powers (1 : R)) x (by simpa [N] using hgen)
  have hf : f ∉ m := by
    -- An element of `{1} + m` cannot lie in the maximal ideal `m`.
    intro hfm
    rcases hfmem with ⟨s, hs, t, ht, hst⟩
    have hs1 : s = 1 := by
      simpa using hs
    subst s
    have hone : (1 : R) ∈ m := by
      have hsub : f - t ∈ m := m.sub_mem hfm ht
      rw [← hst, add_sub_cancel_right] at hsub
      simpa using hsub
    have hmne : m ≠ ⊤ := Ideal.IsMaximal.ne_top (show m.IsMaximal from inferInstance)
    exact hmne (m.eq_top_of_isUnit_mem hone (by simpa using (isUnit_one : IsUnit (1 : R))))
  exact ⟨f, hf, htop⟩

/-- Helper for Lemma 10.78.2: the source comparison map becomes an isomorphism after inverting
`f * g` once the generators on `D(f)` and the constant-rank chart on `D(g)` are fixed. -/
private theorem comparisonMap_bijective_away_of_span_and_rank_const
    [Module.Finite R M] {r : ℕ} (x : Fin r → M) {f g : R}
    (hspan : (Submodule.span R (Set.range x)).localized (.powers f) = ⊤)
    (hfree : Module.freeLocus R M = Set.univ)
    (hrank :
      ∀ q ∈ (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)),
        Module.rankAtStalk (R := R) M q = r) :
    Function.Bijective (LocalizedModule.map (.powers (f * g)) (Fintype.linearCombination R x)) := by
  let φ : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R x
  have hsurj_local :
      ∀ q ∈ (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)),
        Function.Surjective (LocalizedModule.map q.asIdeal.primeCompl φ) := by
    intro q hq
    have hfgq : f * g ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen (f * g) q).1 hq
    have hfq : f ∉ q.asIdeal := by
      intro hfq
      exact hfgq (q.asIdeal.mul_mem_right g hfq)
    -- The generator chart on `D(f)` stays surjective after localizing further to `q`.
    exact comparisonMap_surjective_atPrime_of_span_localized_eq_top
      (R := R) (M := M) x hspan q hfq
  have hsurj :
      Function.Surjective (LocalizedModule.map (.powers (f * g)) φ) :=
    map_surjective_away_of_basicOpen_localized_surjective
      (R := R) (P := (Fin r → R)) (N := M) φ (f * g) hsurj_local
  have hinj_local :
      ∀ q ∈ (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)),
        Function.Injective (LocalizedModule.map q.asIdeal.primeCompl φ) := by
    intro q hq
    -- The constant-rank hypothesis upgrades the prime-local surjection to a bijection.
    exact comparisonMap_injective_atPrime_of_span_localized_eq_top_and_rank_const
      (R := R) (M := M) x hspan hfree hrank q hq
  have hinj :
      Function.Injective (LocalizedModule.map (.powers (f * g)) φ) :=
    map_injective_away_of_basicOpen_localized_injective
      (R := R) (P := (Fin r → R)) (N := M) φ (f * g) hinj_local
  exact ⟨hinj, hsurj⟩

/-- Helper for Lemma 10.78.2: under the clause `(8)` hypotheses, every maximal ideal admits a
basic-open neighborhood on which the localized module is finite free. -/
-- TODO: follow the source proof at a maximal ideal `m`: choose generators from a residue-field
-- basis, shrink to a basic open of constant rank via `Module.exists_basicOpen_eq_rankAtStalk`,
-- Route correction: keep the comparison map over `R`, prove injectivity on each stalk of
-- `D(f * g)`, and then descend that kernel vanishing to `R_(f * g)` via
-- `map_injective_away_of_basicOpen_localized_injective`.
-- build the comparison map on the away-localized module, and prove it is stalkwise bijective.
theorem Module.exists_away_free_finite_of_isLocallyConstant_rankAtStalk_at_maximal
    [Module.Finite R M] (hfree : Module.freeLocus R M = Set.univ)
    (hrank :
      IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ)))
    (m : Ideal R) [m.IsMaximal] :
    ∃ f : R, f ∉ m ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) := by
  classical
  -- First recover flatness from the stalkwise freeness hypothesis so the source proof can measure
  -- the residue-field basis size by `Module.rankAtStalk`.
  have hflat : Module.Flat R M := by
    apply Module.flat_of_localized_maximal
    intro I hI
    have hmem : (⟨I, hI.isPrime⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M := by
      simpa [hfree]
    letI : Module.Free (Localization.AtPrime I) (LocalizedModule.AtPrime I M) := by
      simpa [Module.freeLocus] using hmem
    have : Module.Flat (Localization.AtPrime I) (LocalizedModule.AtPrime I M) := inferInstance
    exact
      (Module.flat_iff_of_isLocalization (Localization.AtPrime I) I.primeCompl
        (M := LocalizedModule.AtPrime I M)).mp this
  have hrank_m :
      Module.finrank (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M)) =
        Module.rankAtStalk (R := R) M ⟨m, inferInstance⟩ :=
    Module.finrank_quotient_smul_top_eq_rankAtStalk_at_maximal
      (R := R) (M := M) m
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let r : ℕ := Module.rankAtStalk (R := R) M ⟨m, inferInstance⟩
  let N : Submodule R M := m • (⊤ : Submodule R M)
  haveI : Module.Finite (R ⧸ m) (M ⧸ N) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ m) (M ⧸ N)
  letI : Module.Free (R ⧸ m) (M ⧸ N) :=
    Module.Free.of_basis (Basis.ofVectorSpace (R ⧸ m) (M ⧸ N))
  let b : Basis (Fin r) (R ⧸ m) (M ⧸ N) :=
    Module.finBasisOfFinrankEq (R ⧸ m) (M ⧸ N) (by simpa [r, N] using hrank_m)
  choose x hx using fun i : Fin r ↦ Submodule.mkQ_surjective N (b i)
  have hspan_q :
      Submodule.span (R ⧸ m) (Set.range ((Submodule.mkQ N) ∘ x)) = ⊤ := by
    -- The lifted family has the same quotient images as the chosen basis.
    have hrange : Set.range ((Submodule.mkQ N) ∘ x) = Set.range b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, by simpa [Function.comp_def, hx i]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, by simpa [Function.comp_def, hx i]⟩
    rw [hrange, b.span_eq]
  obtain ⟨f, hf, hspan⟩ :=
    exists_away_span_eq_top_of_basis_mod_maximal
      (R := R) (M := M) m x (by simpa [N] using hspan_q)
  obtain ⟨g, hg, hgrank⟩ :=
    Module.exists_basicOpen_eq_rankAtStalk (R := R) (M := M) hrank ⟨m, inferInstance⟩
  have hrank_fg :
      ∀ q ∈ (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)),
        Module.rankAtStalk (R := R) M q = r := by
    intro q hq
    have hfgq : f * g ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen (f * g) q).1 hq
    have hgq : g ∉ q.asIdeal := by
      intro hgq
      exact hfgq (q.asIdeal.mul_mem_left f hgq)
    -- Restrict the constant-rank chart from `D(g)` to the smaller basic open `D(f * g)`.
    simpa [r] using hgrank q ((PrimeSpectrum.mem_basicOpen g q).2 hgq)
  let φ : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R x
  have hbij :
      Function.Bijective (LocalizedModule.map (.powers (f * g)) φ) :=
    comparisonMap_bijective_away_of_span_and_rank_const
      (R := R) (M := M) x hspan hfree hrank_fg
  let e :
      LocalizedModule.Away (f * g) M ≃ₗ[Localization.Away (f * g)]
        (Fin r → Localization.Away (f * g)) :=
    (LinearEquiv.ofBijective (LocalizedModule.map (.powers (f * g)) φ) hbij).symm.trans
      (localized_fin_fun_equiv (R := R) (.powers (f * g)) r)
  have hfg : f * g ∉ m := by
    have hmprime : m.IsPrime := Ideal.IsMaximal.isPrime (show m.IsMaximal from inferInstance)
    intro hfg
    exact hg ((hmprime.mem_or_mem hfg).resolve_left hf)
  have hffree :
      Module.Free (Localization.Away (f * g)) (LocalizedModule.Away (f * g) M) :=
    (Module.free_and_finite_of_equiv_fin_fun e).1
  have hffin :
      Module.Finite (Localization.Away (f * g)) (LocalizedModule.Away (f * g) M) :=
    (Module.free_and_finite_of_equiv_fin_fun e).2
  exact ⟨f * g, hfg, hffree, hffin⟩

/-- Helper for Lemma 10.78.2: a finite module whose stalks are free everywhere and whose rank
function is locally constant is finite locally free. -/
theorem Module.finiteLocallyFree_of_freeLocus_eq_univ_of_isLocallyConstant_rankAtStalk
    [Module.Finite R M] (hfree : Module.freeLocus R M = Set.univ)
    (hrank :
      IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ))) :
    Module.FiniteLocallyFree R M := by
  -- Free maximal localizations imply global flatness by the standard maximal-local criterion.
  have hflat : Module.Flat R M := by
    apply Module.flat_of_localized_maximal
    intro I hI
    have hmem : (⟨I, hI.isPrime⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M := by
      simpa [hfree]
    letI : Module.Free (Localization.AtPrime I) (LocalizedModule.AtPrime I M) := by
      simpa [Module.freeLocus] using hmem
    have : Module.Flat (Localization.AtPrime I) (LocalizedModule.AtPrime I M) := inferInstance
    exact
      (Module.flat_iff_of_isLocalization (Localization.AtPrime I) I.primeCompl
        (M := LocalizedModule.AtPrime I M)).mp this
  let t : Set R := { f : R |
    Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) }
  have ht_span : Ideal.span t = ⊤ := by
    -- It suffices to show that every maximal ideal misses one finite-free chart.
    by_contra htop
    obtain ⟨m, hm, hle⟩ := (Ideal.span t).exists_le_maximal htop
    letI : m.IsMaximal := hm
    obtain ⟨f, hf, hffree, hffin⟩ :=
      Module.exists_away_free_finite_of_isLocallyConstant_rankAtStalk_at_maximal
        (R := R) (M := M) hfree hrank m
    exact hf (hle (Ideal.subset_span ⟨hffree, hffin⟩))
  -- Package the maximal-local charts into the `FiniteLocallyFree` cover.
  refine ⟨⟨t, ht_span, ?_⟩⟩
  intro f hf
  exact hf

/-- Lemma 10.78.2: for an `R`-module `M`, the following are equivalent: `M` is finitely presented
and flat; `M` is finite projective; `M` is a direct summand of a finite free `R`-module; `M` is
finitely presented and all prime localizations are free; `M` is finitely presented and all maximal
localizations are free; `M` is finite and locally free; `M` is finite locally free; and `M` is
finite, all prime localizations are free, and the fiber-rank function `ρ_M` is locally constant on
`Spec R`. -/
theorem module_finite_projective_tfae :
    List.TFAE [
      Module.FinitePresentation R M ∧ Module.Flat R M,
      Module.Finite R M ∧ Module.Projective R M,
      ∃ (ι : Type (max u v)) (_ : Finite ι) (i : M →ₗ[R] (ι → R)) (s : (ι → R) →ₗ[R] M),
        s.comp i = LinearMap.id,
      Module.FinitePresentation R M ∧ Module.freeLocus R M = Set.univ,
      Module.FinitePresentation R M ∧
        ∀ (P : Ideal R) [P.IsMaximal],
          Module.Free (Localization.AtPrime P) (LocalizedModule.AtPrime P M),
      Module.Finite R M ∧ Module.LocallyFree R M,
      Module.FiniteLocallyFree R M,
      Module.Finite R M ∧
        Module.freeLocus R M = Set.univ ∧
          IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk M p : ℤ))
    ] := by
  -- Use the finite projective clause as the algebraic hub, then bridge the local freeness clauses
  -- by packaging standard-open covers.
  tfae_have 1 → 2 := by
    rintro ⟨hfp, hflat⟩
    letI : Module.FinitePresentation R M := hfp
    letI : Module.Flat R M := hflat
    -- Finitely presented flat modules are projective, and finite presentation already implies
    -- finiteness.
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation (R := R) (M := M)⟩
  tfae_have 2 → 1 := by
    rintro ⟨hfin, hproj⟩
    letI : Module.Finite R M := hfin
    letI : Module.Projective R M := hproj
    -- Finite projective modules are finitely presented and flat.
    exact ⟨Module.finitePresentation_of_projective R M, inferInstance⟩
  tfae_have 2 → 3 := by
    rintro ⟨hfin, hproj⟩
    letI : Module.Finite R M := hfin
    letI : Module.Projective R M := hproj
    -- Choose a finite free cover of `M` together with a section.
    obtain ⟨n, s, i, _, _, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
    let ι := ULift.{max u v} (Fin n)
    let e : (ι → R) ≃ₗ[R] (Fin n → R) :=
      LinearEquiv.piCongrLeft R (fun _ ↦ R) Equiv.ulift
    let i' : M →ₗ[R] (ι → R) := e.symm.toLinearMap.comp i
    let s' : (ι → R) →ₗ[R] M := s.comp e.toLinearMap
    have hs' : s'.comp i' = LinearMap.id := by
      ext x
      simpa [i', s', e] using LinearMap.congr_fun hs x
    exact ⟨ι, inferInstance, i', s', hs'⟩
  tfae_have 3 → 2 := by
    rintro ⟨ι, hι, i, s, hs⟩
    letI : Finite ι := hι
    have hsurj : Function.Surjective s := by
      intro x
      refine ⟨i x, ?_⟩
      simpa using LinearMap.congr_fun hs x
    -- A split summand of a finite free module is finite and projective.
    exact ⟨Module.Finite.of_surjective s hsurj, Module.Projective.of_split i s hs⟩
  tfae_have 2 → 4 := by
    rintro ⟨hfin, hproj⟩
    letI : Module.Finite R M := hfin
    letI : Module.Projective R M := hproj
    -- Finite projective modules are finitely presented and have free stalks everywhere.
    exact ⟨Module.finitePresentation_of_projective R M, Module.freeLocus_eq_univ (R := R) (M := M)⟩
  tfae_have 4 → 2 := by
    rintro ⟨hfp, hfree⟩
    letI : Module.FinitePresentation R M := hfp
    -- The free locus equals the whole spectrum exactly for finitely presented projective modules.
    exact ⟨inferInstance, (Module.freeLocus_eq_univ_iff (R := R) (M := M)).1 hfree⟩
  tfae_have 4 → 5 := by
    rintro ⟨hfp, hfree⟩
    -- Specialize the global free-locus statement to maximal ideals.
    exact ⟨hfp, fun P _ ↦ by
      have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M := by
        simpa [hfree]
      simpa [Module.freeLocus] using hmem⟩
  tfae_have 5 → 4 := by
    rintro ⟨hfp, hmax⟩
    letI : Module.FinitePresentation R M := hfp
    have hproj : Module.Projective R M := by
      -- Projectivity descends from free maximal localizations.
      refine Module.projective_of_localization_maximal (R := R) (M := M) fun I hI ↦ ?_
      letI : Module.Free (Localization.AtPrime I) (LocalizedModule.AtPrime I M) := hmax I
      infer_instance
    exact ⟨hfp, (Module.freeLocus_eq_univ_iff (R := R) (M := M)).2 hproj⟩
  tfae_have 4 → 7 := by
    rintro ⟨hfp, hfree⟩
    letI : Module.FinitePresentation R M := hfp
    -- Convert the free-locus equality into a standard-open finite free cover.
    exact Module.finiteLocallyFree_of_finitePresentation_of_freeLocus_eq_univ
      (R := R) (M := M) hfree
  tfae_have 7 → 4 := by
    intro hff
    letI : Module.FiniteLocallyFree R M := hff
    -- Descend finite presentation from the finite free cover, and use the same cover to see that
    -- every stalk is free.
    exact ⟨Module.finitePresentation_of_finiteLocallyFree (R := R) (M := M),
      Module.freeLocus_eq_univ_of_finiteLocallyFree (R := R) (M := M)⟩
  tfae_have 7 → 6 := by
    intro hff
    letI : Module.FiniteLocallyFree R M := hff
    -- Forgetting the finite-generation part gives local freeness, and finiteness descends from
    -- the same cover.
    exact ⟨Module.finite_of_finiteLocallyFree (R := R) (M := M), inferInstance⟩
  tfae_have 6 → 7 := by
    rintro ⟨hfin, hloc⟩
    letI : Module.Finite R M := hfin
    letI : Module.LocallyFree R M := hloc
    -- Reuse the local free cover and localize the global finite-generation witness.
    exact Module.finiteLocallyFree_of_finite_and_locallyFree (R := R) (M := M)
  tfae_have 2 → 8 := by
    rintro ⟨hfin, hproj⟩
    letI : Module.Finite R M := hfin
    letI : Module.Projective R M := hproj
    letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    letI : Module.Flat R M := inferInstance
    -- Finite projective modules are flat with everywhere-free stalks and locally constant rank.
    exact ⟨hfin, Module.freeLocus_eq_univ (R := R) (M := M), by
      simpa using
        (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).comp
          (fun n : ℕ ↦ (n : ℤ))⟩
  tfae_have 8 → 7 := by
    rintro ⟨hfin, hfree, hrank⟩
    letI : Module.Finite R M := hfin
    -- Use local constancy of the rank function to trivialize the module on a basic-open cover.
    exact Module.finiteLocallyFree_of_freeLocus_eq_univ_of_isLocallyConstant_rankAtStalk
      (R := R) (M := M) hfree hrank
  tfae_finish

namespace Module

/-- A finitely presented flat module is finite locally free. -/
theorem finiteLocallyFree_of_finitePresentation_of_flat
    [FinitePresentation R M] [Flat R M] :
    FiniteLocallyFree R M := by
  simpa using (module_finite_projective_tfae.out 0 6).mp
    (show FinitePresentation R M ∧ Flat R M from ⟨inferInstance, inferInstance⟩)

end Module

end
