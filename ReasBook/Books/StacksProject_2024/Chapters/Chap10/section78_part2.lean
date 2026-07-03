import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_78_3 (from Chap10) -/
open scoped TensorProduct

universe u v

section

variable {R : Type u} [CommRing R] [IsReduced R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.78.3: every minimal prime carries its canonical prime-ideal instance. -/
local instance minimalPrime_isPrime {A : Type*} [CommRing A] (p : minimalPrimes A) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/- Domain triage:
- primary domain: finite projective modules and the fiber-rank function on `Spec R`;
- sampled owner-style declarations of the same kind:
  `Module.Projective`,
  residue-field fiber ranks `dim_{κ(p)} (κ(p) ⊗[R] M)`,
  `module_finite_projective_tfae`;
- owner abstraction: `Module.Projective R M` together with `Module.Finite R M`;
- primitive data: the reduced ring `R` and the module `M`;
- derived API: local constancy of the integer-valued fiber-rank function.

This item is a `bridge/view` lemma: under the reducedness hypothesis, it removes the extra
`Module.freeLocus R M = Set.univ` clause that appears in the owner-level TFAE from Lemma `10.78.2`.
Its public statement therefore uses the owner predicates directly, rather than parallel local
wrapper abbreviations for the same conditions.
-/

-- Proof sketch: after assuming `Module.Finite R M`, the forward implication is local constancy
-- of the residue-field fiber dimension for a finite projective module. Conversely, over a reduced
-- ring a finite module with locally constant fiber rank is locally free on a standard-open
-- neighborhood of every prime, so Lemma `10.78.2` yields projectivity.
/-- Helper for Lemma 10.78.3: the source fiber dimension agrees with `Module.rankAtStalk`,
after coercing both sides to `ℤ`. -/
private theorem fiberRank_int_eq_rankAtStalk_int [Module.Finite R M] [Module.Flat R M]
    (p : PrimeSpectrum R) :
    (Module.finrank p.asIdeal.ResidueField
      (TensorProduct R p.asIdeal.ResidueField M) : ℤ) =
      (Module.rankAtStalk (R := R) M p : ℤ) := by
  -- Rewrite the source-facing fiber dimension by the canonical stalk-rank formula.
  simpa using congrArg (fun n : ℕ ↦ (n : ℤ))
    ((Module.rankAtStalk_eq (R := R) (M := M) p).symm)

/-- Helper for Lemma 10.78.3: finite projective modules have locally constant fiber rank. -/
private theorem isLocallyConstant_fiberRank_of_projective
    (hM : Module.Finite R M) (hproj : Module.Projective R M) :
    IsLocallyConstant (fun p : PrimeSpectrum R ↦
      (Module.finrank p.asIdeal.ResidueField
        (TensorProduct R p.asIdeal.ResidueField M) : ℤ)) := by
  letI : Module.Finite R M := hM
  letI : Module.Projective R M := hproj
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  letI : Module.Flat R M := inferInstance
  -- Transport the owner-level locally constant stalk rank to the source fiber-rank function.
  simpa [fiberRank_int_eq_rankAtStalk_int] using
    (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).comp
      (fun n : ℕ ↦ (n : ℤ))

/-- Helper for Lemma 10.78.3: at a maximal ideal, the quotient `M / mM` has the same finite
dimension as the residue-field fiber `κ(m) ⊗[R] M`. -/
private theorem quotient_finrank_eq_fiber_finrank_at_maximal
    [Module.Finite R M] (m : Ideal R) [m.IsMaximal] :
    Module.finrank (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M)) =
      Module.finrank m.ResidueField (TensorProduct R m.ResidueField M) := by
  let e : (R ⧸ m) ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  let j : TensorProduct R (R ⧸ m) M ≃ₗ[R] TensorProduct R m.ResidueField M :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  let eQ : TensorProduct R (R ⧸ m) M ≃ₗ[R ⧸ m] (M ⧸ m • (⊤ : Submodule R M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M m).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  have hj :
      ∀ (r : R ⧸ m) (x : TensorProduct R (R ⧸ m) M),
        j (r • x) = e r • j x := by
    -- Compare the scalar actions before transporting finrank across the quotient-residue-field
    -- equivalence.
    intro r x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a y
      change e (r * a) ⊗ₜ[R] y = e r • (e a ⊗ₜ[R] y)
      rw [map_mul]
      rfl
    · intro x y hx hy
      simp [smul_add, hx, hy]
  have htensor :
      Module.finrank (R ⧸ m) (TensorProduct R (R ⧸ m) M) =
        Module.finrank m.ResidueField (TensorProduct R m.ResidueField M) := by
    -- Transport rank across the quotient-residue-field equivalence and then convert to finrank.
    have hrank :
        Module.rank (R ⧸ m) (TensorProduct R (R ⧸ m) M) =
          Module.rank m.ResidueField (TensorProduct R m.ResidueField M) :=
      rank_eq_of_equiv_equiv e.toRingEquiv j.toAddEquiv e.toRingEquiv.bijective hj
    change
      Cardinal.toNat (Module.rank (R ⧸ m) (TensorProduct R (R ⧸ m) M)) =
        Cardinal.toNat (Module.rank m.ResidueField (TensorProduct R m.ResidueField M))
    exact congrArg Cardinal.toNat hrank
  -- First identify the quotient with the tensor over `R ⧸ m`, then pass from `R ⧸ m` to the
  -- residue field.
  calc
    Module.finrank (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M)) =
        Module.finrank (R ⧸ m) (TensorProduct R (R ⧸ m) M) := by
          exact eQ.finrank_eq.symm
    _ = Module.finrank m.ResidueField (TensorProduct R m.ResidueField M) := htensor

/-- Helper for Lemma 10.78.3: a locally constant integer-valued fiber-rank function is constant on
some basic-open neighborhood of any given prime. -/
private theorem exists_basicOpen_eq_fiberRank
    (hrank : IsLocallyConstant (fun p : PrimeSpectrum R ↦
      (Module.finrank p.asIdeal.ResidueField
        (TensorProduct R p.asIdeal.ResidueField M) : ℤ)))
    (p : PrimeSpectrum R) :
    ∃ g : R, g ∉ p.asIdeal ∧
      ∀ q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)),
        Module.finrank q.asIdeal.ResidueField
          (TensorProduct R q.asIdeal.ResidueField M) =
            Module.finrank p.asIdeal.ResidueField
              (TensorProduct R p.asIdeal.ResidueField M) := by
  rcases hrank.exists_open p with ⟨U, hU, hpU, hconst⟩
  obtain ⟨V, ⟨g, rfl⟩, hpV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU p hpU
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g p).1 hpV, ?_⟩
  intro q hq
  exact Int.ofNat.inj (hconst q (hVU hq))

/-- Helper for Lemma 10.78.3: localizing a linear map is surjective exactly when the localized
cokernel is trivial. -/
private theorem localized_map_surjective_iff_subsingleton_cokernel
    {P : Type*} [AddCommGroup P] [Module R P]
    {N : Type*} [AddCommGroup N] [Module R N]
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
      -- A surjective localized map has trivial quotient by its range.
      exact (Submodule.Quotient.subsingleton_iff).2 (LinearMap.range_eq_top.2 hφ)
    exact (e.toEquiv.subsingleton_congr).1 hsub
  · intro hsub
    have hsub' :
        Subsingleton (LocalizedModule S N ⧸ LinearMap.range ψ) :=
      (e.toEquiv.subsingleton_congr).2 hsub
    -- Triviality of the localized cokernel says that the localized range is the whole codomain.
    exact LinearMap.range_eq_top.1 ((Submodule.Quotient.subsingleton_iff).1 hsub')

/-- Helper for Lemma 10.78.3: if a linear map is surjective after localizing at every prime of the
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

/-- Helper for Lemma 10.78.3: localizing the free module `(Fin r → R)` yields the canonical
`Fin r`-indexed free module over the localized ring. -/
private noncomputable def localized_fin_fun_equiv
    (S : Submonoid R) (r : ℕ) :
    LocalizedModule S (Fin r → R) ≃ₗ[Localization S] (Fin r → Localization S) :=
  let fS : (Fin r → R) →ₗ[R] (Fin r → Localization S) :=
    .pi fun i : Fin r ↦ (LocalizedModule.mkLinearMap S R) ∘ₗ LinearMap.proj i
  (IsLocalizedModule.iso S fS).extendScalarsOfIsLocalization S (Localization S)

/-- Helper for Lemma 10.78.3: at a prime, the localized source `(Fin r → R)` is canonically the
standard free `Fin r`-module over the local ring. -/
private noncomputable def localized_fin_fun_equiv_atPrime
    (q : PrimeSpectrum R) (r : ℕ) :
    LocalizedModule q.asIdeal.primeCompl (Fin r → R) ≃ₗ[Localization.AtPrime q.asIdeal]
      (Fin r → Localization.AtPrime q.asIdeal) :=
  localized_fin_fun_equiv (R := R) q.asIdeal.primeCompl r

/-- Helper for Lemma 10.78.3: localizing first away from `t` and then at a prime `I` identifies
the two local rings. -/
private noncomputable def away_atPrime_algEquiv_to_contracted
    {A : Type*} [CommRing A] {t : A} (I : Ideal (Localization.Away t)) [I.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) I) ≃ₐ[A]
      Localization.AtPrime I :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := Submonoid.powers t) I

/-- Helper for Lemma 10.78.3: the iterated stalk of `M_t` at `I` is the localization of `M` at
the contracted prime. -/
private theorem localizedAway_stalk_isLocalizedModule_of_contracted_prime
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {t : A} (I : Ideal (Localization.Away t)) [I.IsPrime] :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) I
    let κ :
      N →ₗ[A] LocalizedModule.AtPrime I (LocalizedModule.Away t N) :=
      ((LocalizedModule.mkLinearMap I.primeCompl (LocalizedModule.Away t N)).restrictScalars A).comp
        (LocalizedModule.mkLinearMap (.powers t) N)
    IsLocalizedModule J.primeCompl κ := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) I
  let B := Localization.AtPrime I
  let κ :
      N →ₗ[A] LocalizedModule.AtPrime I (LocalizedModule.Away t N) :=
    ((LocalizedModule.mkLinearMap I.primeCompl (LocalizedModule.Away t N)).restrictScalars A).comp
      (LocalizedModule.mkLinearMap (.powers t) N)
  let eOuter :
      LocalizedModule.AtPrime I (LocalizedModule.Away t N) ≃ₗ[B]
        (B ⊗[Localization.Away t] (LocalizedModule.Away t N)) :=
    LocalizedModule.equivTensorProduct I.primeCompl (LocalizedModule.Away t N)
  let eInner :
      (B ⊗[Localization.Away t] (LocalizedModule.Away t N)) ≃ₗ[B] (B ⊗[A] N) :=
    (LinearEquiv.baseChange
      (R := Localization.Away t) (A := B)
      (M := LocalizedModule.Away t N) (N := Localization.Away t ⊗[A] N)
      (LocalizedModule.equivTensorProduct (.powers t) N)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) B B N)
  let e :
      LocalizedModule.AtPrime I (LocalizedModule.Away t N) ≃ₗ[A] B ⊗[A] N :=
    (eOuter.trans eInner).restrictScalars A
  have hcomp :
      e.toLinearMap.comp κ = TensorProduct.mk A B N 1 := by
    -- Route correction: collapse the iterated localization to the tensor model before proving the
    -- `IsLocalizedModule` instance, so the comparison map is the standard tensor generator.
    ext x
    change (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) B B N)
        ((LinearEquiv.baseChange
          (R := Localization.Away t) (A := B)
          (M := LocalizedModule.Away t N) (N := Localization.Away t ⊗[A] N)
          (LocalizedModule.equivTensorProduct (Submonoid.powers t) N))
          ((LocalizedModule.equivTensorProduct I.primeCompl (LocalizedModule.Away t N))
            (LocalizedModule.mk (LocalizedModule.mk x 1) 1))) =
      1 ⊗ₜ[A] x
    rw [LocalizedModule.equivTensorProduct_apply_mk, LinearEquiv.baseChange_tmul,
      LocalizedModule.equivTensorProduct_apply_mk,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    congr 1
    rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap, Algebra.smul_def,
      map_one, map_one, one_mul]
  letI : IsLocalization.AtPrime B J := by
    dsimp [B, J]
    infer_instance
  have hκ :
      e.symm.toLinearMap.comp (TensorProduct.mk A B N 1) = κ := by
    -- Pull the standard tensor localization map back through the comparison equivalence.
    ext x
    apply e.injective
    simpa [LinearMap.comp_assoc] using
      (congrArg (fun f : N →ₗ[A] B ⊗[A] N => f x) hcomp).symm
  -- Transport the canonical tensor-product localization model to the iterated away-then-prime
  -- stalk.
  convert
    (inferInstance : IsLocalizedModule J.primeCompl
      (e.symm.toLinearMap.comp (TensorProduct.mk A B N 1))) using 1
  exact hκ.symm

/-- Helper for Lemma 10.78.3: on a localized free module, the canonical `Fin r`-equivalence sends
`mk v 1` to the coordinatewise localization of `v`. -/
private theorem localized_fin_fun_equiv_atPrime_mk_one
    {A : Type*} [CommRing A] (q : PrimeSpectrum A) (r : ℕ) (v : Fin r → A) :
    localized_fin_fun_equiv_atPrime (R := A) q r
      (LocalizedModule.mk v (1 : q.asIdeal.primeCompl)) =
        fun i ↦ algebraMap A (Localization.AtPrime q.asIdeal) (v i) := by
  -- Evaluate the canonical localization/free-module comparison on the numerator `v` with trivial
  -- denominator, then read off each coordinate.
  ext i
  simp [localized_fin_fun_equiv_atPrime, localized_fin_fun_equiv, LinearMap.proj_apply,
    LinearMap.comp_apply]
  exact Localization.mk_one_eq_algebraMap (M := q.asIdeal.primeCompl) (v i)

/-- Helper for Lemma 10.78.3: a vector over a reduced ring is zero once all of its coordinates
vanish in every minimal-prime localization. -/
private theorem fin_fun_eq_zero_of_forall_minimalPrime_localization_eq_zero
    {A : Type*} [CommRing A] [IsReduced A] {r : ℕ} (v : Fin r → A)
    (hzero :
      ∀ q : minimalPrimes A, ∀ i : Fin r,
        algebraMap A (Localization.AtPrime q.1) (v i) = 0) :
    v = 0 := by
  ext i
  -- Descend coefficientwise through the injective map into the product of minimal-prime fields.
  exact (algebraMap_embedding_into_product_of_fields (R := A)).1 <| by
    ext q
    simpa using hzero q i

/-- Helper for Lemma 10.78.3: injectivity on all minimal-prime localizations descends to the
original map out of the free source `A^r`. -/
private theorem injective_of_minimalPrime_localizations_for_fin_fun_source
    {A : Type*} [CommRing A] [IsReduced A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {r : ℕ} (φ : (Fin r → A) →ₗ[A] N)
    (hlocal :
      ∀ q : minimalPrimes A, Function.Injective (LocalizedModule.map q.1.primeCompl φ)) :
    Function.Injective φ := by
  intro v w hvw
  have hzero :
      v - w = 0 := by
    apply fin_fun_eq_zero_of_forall_minimalPrime_localization_eq_zero (A := A) (r := r) (v - w)
    intro q i
    let qSpec : PrimeSpectrum A := ⟨q.1, inferInstance⟩
    have hvq :
        LocalizedModule.map q.1.primeCompl φ
          (LocalizedModule.mk (v - w) (1 : q.1.primeCompl)) =
            LocalizedModule.map q.1.primeCompl φ 0 := by
      simpa [map_sub, hvw] using
        congrArg (LocalizedModule.map q.1.primeCompl φ)
          (show φ (v - w) = φ 0 by simp [map_sub, hvw])
    have hz :
        LocalizedModule.mk (v - w) (1 : q.1.primeCompl) = 0 := hlocal q hvq
    have hz' := congrArg
      (fun z ↦ localized_fin_fun_equiv_atPrime (R := A) qSpec r z i) hz
    simpa [Pi.sub_apply, localized_fin_fun_equiv_atPrime_mk_one] using hz'
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 10.78.3: at a minimal prime of the away localization, the localized
comparison map is bijective. -/
private theorem minimal_prime_localized_away_comparison_bijective
    [Module.Finite R M] {r : ℕ} {t : R}
    (φA : (Fin r → Localization.Away t) →ₗ[Localization.Away t] LocalizedModule.Away t M)
    (hφA_surj : Function.Surjective φA)
    (hrank :
      ∀ q ∈ (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)),
        Module.finrank q.asIdeal.ResidueField
          (TensorProduct R q.asIdeal.ResidueField M) = r)
    (q : minimalPrimes (Localization.Away t)) :
    Function.Bijective (LocalizedModule.map q.1.primeCompl φA) := by
  -- TODO: prove the source-local step from the text by passing to the contracted minimal prime of
  -- `R`, identifying the iterated localization with the contracted stalk, and comparing vector
  -- space dimensions there.
  sorry

/-- Helper for Lemma 10.78.3: if the family `x` generates after inverting `f`, then the
comparison map is surjective over `R_f`. -/
private theorem comparisonMap_surjective_away_of_span_localized_eq_top
    {r : ℕ} (x : Fin r → M) {f : R}
    (hspan : (Submodule.span R (Set.range x)).localized (.powers f) = ⊤) :
    Function.Surjective (LocalizedModule.map (.powers f) (Fintype.linearCombination R x)) := by
  let φx : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R x
  have hrange :
      LinearMap.range (LocalizedModule.map (.powers f) φx) =
        (Submodule.span R (Set.range x)).localized (.powers f) := by
    -- Rewrite the range of the localized comparison map as the localization of the original span.
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

/-- Helper for Lemma 10.78.3: if the family `x` generates after inverting `f`, then at every
prime of `D(f)` the localized comparison map is surjective. -/
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
    -- Rewrite the localized range and identify the original range with the span of the generators.
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

/-- Helper for Lemma 10.78.3: a basis of `M / mM` lifts to generators on some basic open missing
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

/-- Helper for Lemma 10.78.3: at each maximal ideal, local constancy of the source fiber-rank
function should produce a basic-open neighborhood where the localized module is finite free. -/
private theorem exists_away_free_finite_of_isLocallyConstant_fiberRank_at_maximal
    [Module.Finite R M]
    (hrank : IsLocallyConstant (fun p : PrimeSpectrum R ↦
      (Module.finrank p.asIdeal.ResidueField
        (TensorProduct R p.asIdeal.ResidueField M) : ℤ)))
    (m : Ideal R) [m.IsMaximal] :
    ∃ f : R, f ∉ m ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) := by
  classical
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let r : ℕ :=
    Module.finrank m.ResidueField (TensorProduct R m.ResidueField M)
  let N : Submodule R M := m • (⊤ : Submodule R M)
  have hrank_m :
      Module.finrank (R ⧸ m) (M ⧸ N) = r := by
    -- Measure the quotient dimension by the residue-field fiber dimension at `m`.
    simpa [r, N] using
      quotient_finrank_eq_fiber_finrank_at_maximal (R := R) (M := M) m
  haveI : Module.Finite (R ⧸ m) (M ⧸ N) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ m) (M ⧸ N)
  letI : Module.Free (R ⧸ m) (M ⧸ N) := by
    infer_instance
  let b :=
    Module.finBasisOfFinrankEq (R ⧸ m) (M ⧸ N) hrank_m
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
    exists_basicOpen_eq_fiberRank (R := R) (M := M) hrank ⟨m, inferInstance⟩
  have hrank_fg :
      ∀ q ∈ (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)),
        Module.finrank q.asIdeal.ResidueField
          (TensorProduct R q.asIdeal.ResidueField M) = r := by
    -- Restrict the constant fiber-rank chart from `D(g)` to the smaller basic open `D(f * g)`.
    intro q hq
    have hfgq : f * g ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen (f * g) q).1 hq
    have hgq : g ∉ q.asIdeal := by
      intro hgq
      exact hfgq (q.asIdeal.mul_mem_left f hgq)
    simpa [r] using hgrank q ((PrimeSpectrum.mem_basicOpen g q).2 hgq)
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
  have hfg : f * g ∉ m := by
    have hmprime : m.IsPrime := Ideal.IsMaximal.isPrime (show m.IsMaximal from inferInstance)
    intro hfg
    exact hg ((hmprime.mem_or_mem hfg).resolve_left hf)
  -- Route correction: the old attempt tried to reuse the stronger free-locus chart from
  -- `Lemma 10.78.2`. Here the remaining work is exactly the reduced minimal-prime injectivity
  -- descent for the away-localized comparison map on `D(f * g)`.
  have hbij :
      Function.Bijective (LocalizedModule.map (.powers (f * g)) φ) := by
    let A := Localization.Away (f * g)
    let eAway :
        LocalizedModule.Away (f * g) (Fin r → R) ≃ₗ[A] (Fin r → A) :=
      localized_fin_fun_equiv (R := R) (.powers (f * g)) r
    let φA : (Fin r → A) →ₗ[A] LocalizedModule.Away (f * g) M :=
      (LocalizedModule.map (.powers (f * g)) φ).comp eAway.symm.toLinearMap
    have hφA_surj : Function.Surjective φA := by
      intro y
      rcases hsurj y with ⟨x, hx⟩
      refine ⟨eAway x, ?_⟩
      simpa [φA, eAway] using hx
    have hφA_inj :
        Function.Injective φA :=
      injective_of_minimalPrime_localizations_for_fin_fun_source
        (A := A) (N := LocalizedModule.Away (f * g) M) (r := r) φA
        (fun q ↦
          (minimal_prime_localized_away_comparison_bijective
            (R := R) (M := M) (r := r) (t := f * g) φA hφA_surj hrank_fg q).1)
    refine ⟨?_ , hsurj⟩
    intro u v huv
    apply eAway.injective
    exact hφA_inj (by simpa [φA, eAway] using huv)
  let e :
      LocalizedModule.Away (f * g) M ≃ₗ[Localization.Away (f * g)]
        (Fin r → Localization.Away (f * g)) :=
    (LinearEquiv.ofBijective (LocalizedModule.map (.powers (f * g)) φ) hbij).symm.trans
      (localized_fin_fun_equiv (R := R) (.powers (f * g)) r)
  have hffree :
      Module.Free (Localization.Away (f * g)) (LocalizedModule.Away (f * g) M) :=
    (Module.free_and_finite_of_equiv_fin_fun e).1
  have hffin :
      Module.Finite (Localization.Away (f * g)) (LocalizedModule.Away (f * g) M) :=
    (Module.free_and_finite_of_equiv_fin_fun e).2
  exact ⟨f * g, hfg, hffree, hffin⟩

/-- Helper for Lemma 10.78.3: maximal finite-free charts package into a finite locally free
structure. -/
private theorem finiteLocallyFree_of_isLocallyConstant_fiberRank
    (hM : Module.Finite R M)
    (hrank : IsLocallyConstant (fun p : PrimeSpectrum R ↦
      (Module.finrank p.asIdeal.ResidueField
        (TensorProduct R p.asIdeal.ResidueField M) : ℤ))) :
    Module.FiniteLocallyFree R M := by
  letI : Module.Finite R M := hM
  let t : Set R := { f : R |
    Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) }
  have ht_span : Ideal.span t = ⊤ := by
    -- If the span were proper, a maximal ideal containing it would miss the required finite-free
    -- chart from the source local argument.
    by_contra htop
    obtain ⟨m, hm, hle⟩ := (Ideal.span t).exists_le_maximal htop
    letI : m.IsMaximal := hm
    obtain ⟨f, hf, hffree, hffin⟩ :=
      exists_away_free_finite_of_isLocallyConstant_fiberRank_at_maximal
        (R := R) (M := M) hrank m
    exact hf (hle (Ideal.subset_span ⟨hffree, hffin⟩))
  -- Package the standard-open finite-free charts into the `FiniteLocallyFree` witness.
  refine ⟨⟨t, ht_span, ?_⟩⟩
  intro f hf
  exact hf

/-- Lemma 10.78.3: if `M` is a finite `R`-module over a reduced ring, then `M` is projective if
and only if the fiber-rank function `ρ_M : Spec(R) → ℤ`, `p ↦ dim_{κ(p)}(M ⊗[R] κ(p))`, is
locally constant. -/
theorem projective_iff_isLocallyConstant_rankAtStalk_of_finite
    (hM : Module.Finite R M) :
    Module.Projective R M ↔
      IsLocallyConstant (fun p : PrimeSpectrum R ↦
        (Module.finrank p.asIdeal.ResidueField
          (TensorProduct R p.asIdeal.ResidueField M) : ℤ)) := by
  constructor
  · intro hproj
    -- The forward implication is the source fiber-rank local-constancy statement.
    exact isLocallyConstant_fiberRank_of_projective (R := R) (M := M) hM hproj
  · intro hrank
    letI : Module.FiniteLocallyFree R M :=
      finiteLocallyFree_of_isLocallyConstant_fiberRank (R := R) (M := M) hM hrank
    letI : Module.FinitePresentation R M :=
      Module.finitePresentation_of_finiteLocallyFree (R := R) (M := M)
    -- Once the source local argument provides a finite free chart near every maximal ideal,
    -- projectivity follows from the standard free-locus criterion.
    exact
      (Module.freeLocus_eq_univ_iff (R := R) (M := M)).1
        (Module.freeLocus_eq_univ_of_finiteLocallyFree (R := R) (M := M))

end

/-! ### Remark_10_78_4 (from Chap10) -/
noncomputable section

open scoped Manifold ContDiff

local notation "SmoothRealFunctionRing" => C^∞⟮𝓘(ℝ), ℝ; ℝ⟯

/-- The ideal of smooth real-valued functions vanishing at the origin. -/
def smoothRealFunctionsVanishingAtZeroIdeal : Ideal SmoothRealFunctionRing :=
  RingHom.ker (ContMDiffMap.evalRingHom (0 : ℝ))

/-- The ideal of smooth real-valued functions that vanish on a neighborhood of the origin. -/
def smoothRealFunctionsVanishingNearZeroIdeal : Ideal SmoothRealFunctionRing where
  carrier := { f | ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f x = 0 }
  zero_mem' := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    rfl
  add_mem' := by
    rintro f g ⟨εf, hεf, hf⟩ ⟨εg, hεg, hg⟩
    refine ⟨min εf εg, lt_min hεf hεg, ?_⟩
    intro x hx
    have hxf : |x| < εf := lt_of_lt_of_le hx (min_le_left _ _)
    have hxg : |x| < εg := lt_of_lt_of_le hx (min_le_right _ _)
    simp [hf x hxf, hg x hxg]
  smul_mem' := by
    rintro f g ⟨ε, hε, hg⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx
    simp [hg x hx]

-- Proof sketch: a smooth function that vanishes on some neighborhood of `0` in particular vanishes
-- at `0`, so it lies in the kernel of evaluation at the origin.
/-- Any smooth function vanishing near the origin also vanishes at the origin. -/
theorem smoothRealFunctionsVanishingNearZeroIdeal_le_vanishingAtZeroIdeal :
    smoothRealFunctionsVanishingNearZeroIdeal ≤ smoothRealFunctionsVanishingAtZeroIdeal := by
  -- Evaluating at `0` turns a neighborhood-vanishing hypothesis into an actual zero.
  intro f hf
  rcases hf with ⟨ε, hε, hvanish⟩
  rw [smoothRealFunctionsVanishingAtZeroIdeal, RingHom.mem_ker]
  exact hvanish 0 (by simpa using hε)

/-- The ideal of functions vanishing at the origin is maximal. -/
theorem smoothRealFunctionsVanishingAtZeroIdeal_isMaximal :
    smoothRealFunctionsVanishingAtZeroIdeal.IsMaximal := by
  -- Evaluation at `0` is onto `ℝ`, so its kernel is maximal.
  rw [smoothRealFunctionsVanishingAtZeroIdeal]
  refine RingHom.ker_isMaximal_of_surjective (ContMDiffMap.evalRingHom (0 : ℝ)) ?_
  intro r
  refine ⟨ContMDiffMap.const r, ?_⟩
  simp [ContMDiffMap.evalRingHom, ContMDiffMap.const]

attribute [instance] smoothRealFunctionsVanishingAtZeroIdeal_isMaximal

instance smoothRealFunctionsVanishingAtZeroIdeal_isPrime :
    smoothRealFunctionsVanishingAtZeroIdeal.IsPrime :=
  smoothRealFunctionsVanishingAtZeroIdeal_isMaximal.isPrime

/-- The source-facing module `M = R_𝔪` from Remark 10.78.4, where `𝔪` is the maximal ideal of
smooth functions vanishing at the origin. -/
abbrev smoothRealFunctionLocalizationAtZero :=
  Localization.AtPrime smoothRealFunctionsVanishingAtZeroIdeal

/-- The quotient model `R / I` from Remark 10.78.4, where `I` consists of smooth functions
vanishing on a neighborhood of the origin. -/
abbrev smoothRealFunctionQuotientAtZero :=
  SmoothRealFunctionRing ⧸ smoothRealFunctionsVanishingNearZeroIdeal

/-- Helper for Remark 10.78.4: bundle the standard smooth cutoff theorem on `ℝ` into the smooth
function ring. -/
lemma smooth_cutoff_support_eq_eq_one {s t : Set ℝ} (hs : IsOpen s) (ht : IsClosed t)
    (h : t ⊆ s) :
    ∃ φ : SmoothRealFunctionRing,
      Function.support (φ : ℝ → ℝ) = s ∧
      Set.range (φ : ℝ → ℝ) ⊆ Set.Icc 0 1 ∧
      ∀ x, x ∈ t ↔ φ x = 1 := by
  -- Repackage the unbundled cutoff theorem as an element of `SmoothRealFunctionRing`.
  rcases exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ)) hs ht h with
    ⟨φ, hφdiff, hφrange, hφsupp, hφone⟩
  refine ⟨⟨φ, hφdiff⟩, ?_, ?_, ?_⟩
  · simpa using hφsupp
  · simpa using hφrange
  · simpa using hφone

/-- Helper for Remark 10.78.4: a smooth function nonzero at the origin stays nonzero on a small
interval around `0`. -/
lemma exists_abs_lt_nonzero_of_eval_ne_zero (f : SmoothRealFunctionRing) (hf0 : f 0 ≠ 0) :
    ∃ ε > 0, ∀ x : ℝ, |x| < ε → f x ≠ 0 := by
  -- Continuity turns the open condition `f x ≠ 0` into a neighborhood of `0`.
  have hpre : {x : ℝ | f x ≠ 0} ∈ nhds (0 : ℝ) := by
    exact f.contMDiff.continuous.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hf0)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hεsub (by simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx)

/-- Helper for Remark 10.78.4: if the support of a smooth numerator has closure inside the
nonvanishing locus of the denominator, then the pointwise quotient extends to a smooth function on
all of `ℝ`. -/
lemma contMDiff_div_of_support_closure_subset (c f : SmoothRealFunctionRing) {s : Set ℝ}
    (hsupp : Function.support (c : ℝ → ℝ) = s) (hcl : closure s ⊆ {x : ℝ | f x ≠ 0}) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun x : ℝ ↦ c x / f x) := by
  -- On the closure of the support, the denominator is nonzero; away from that closure, the
  -- numerator vanishes on a neighborhood, so the quotient is locally constant zero.
  intro x
  by_cases hx : x ∈ closure s
  · exact ContMDiffAt.div₀ (c.contMDiff x) (f.contMDiff x) (hcl hx)
  · refine ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : ℝ ↦ (0 : ℝ))
      (contMDiffAt_const : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun _ : ℝ ↦ (0 : ℝ)) x) ?_
    filter_upwards [IsOpen.mem_nhds isClosed_closure.isOpen_compl hx] with y hy
    have hy_support : y ∉ Function.support (c : ℝ → ℝ) := by
      rw [hsupp]
      intro hy'
      exact hy (subset_closure hy')
    have hcy : c y = 0 := by
      rwa [Function.notMem_support] at hy_support
    simpa [hcy]

/-- Helper for Remark 10.78.4: any smooth function vanishing near `0` is killed by some element of
the complement of the maximal ideal of functions vanishing at `0`. -/
lemma exists_primeCompl_multiplier_eq_zero_of_mem_vanishingNearZeroIdeal
    (h : SmoothRealFunctionRing)
    (hh : h ∈ smoothRealFunctionsVanishingNearZeroIdeal) :
    ∃ c : smoothRealFunctionsVanishingAtZeroIdeal.primeCompl, (c : SmoothRealFunctionRing) * h = 0 := by
  rcases hh with ⟨ε, hε, hvanish⟩
  let s : Set ℝ := Set.Ioo (-(ε / 2)) (ε / 2)
  let t : Set ℝ := Set.Icc (-(ε / 4)) (ε / 4)
  rcases smooth_cutoff_support_eq_eq_one (s := s) (t := t) isOpen_Ioo isClosed_Icc
      (by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) with
    ⟨c, hcsupp, -, hcone⟩
  refine ⟨⟨c, ?_⟩, ?_⟩
  · -- The cutoff is equal to `1` near the origin, so it does not vanish at `0`.
    intro hc
    have hc0' : c 0 = 0 := by
      simpa [smoothRealFunctionsVanishingAtZeroIdeal] using hc
    have hc0 : c 0 = 1 := (hcone 0).1 (by
      constructor <;> linarith [hε])
    have : (1 : ℝ) = 0 := by rw [← hc0, hc0']
    exact one_ne_zero this
  · -- Inside the support of the cutoff, `h` vanishes; outside the support, the cutoff vanishes.
    ext x
    by_cases hx : x ∈ Function.support (c : ℝ → ℝ)
    · have hx' : x ∈ Set.Ioo (-(ε / 2)) (ε / 2) := by simpa [hcsupp] using hx
      have hxε : |x| < ε := by
        have hxabs : |x| < ε / 2 := abs_lt.mpr ⟨by linarith [hx'.1], hx'.2⟩
        linarith
      simp [hvanish x hxε]
    · have hcx : c x = 0 := by
        rwa [Function.notMem_support] at hx
      simp [hcx]

/-- Helper for Remark 10.78.4: a smooth function nonzero at `0` becomes a unit in the quotient by
functions vanishing near `0`. -/
lemma quotient_mk_isUnit_of_eval_ne_zero (f : SmoothRealFunctionRing) (hf0 : f 0 ≠ 0) :
    IsUnit (Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal f) := by
  rcases exists_abs_lt_nonzero_of_eval_ne_zero f hf0 with ⟨ε, hε, hnonzero⟩
  let s : Set ℝ := Set.Ioo (-(ε / 2)) (ε / 2)
  let t : Set ℝ := Set.Icc (-(ε / 4)) (ε / 4)
  rcases smooth_cutoff_support_eq_eq_one (s := s) (t := t) isOpen_Ioo isClosed_Icc
      (by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) with
    ⟨c, hcsupp, -, hcone⟩
  have hcl : closure s ⊆ {x : ℝ | f x ≠ 0} := by
    -- The closure of the cutoff support still lies in the small interval where `f` is nonzero.
    intro x hx
    have hclosure : closure s = Set.Icc (-(ε / 2)) (ε / 2) := by
      have hab : -(ε / 2) ≠ ε / 2 := by linarith
      simpa [s] using (closure_Ioo hab)
    rw [hclosure] at hx
    have hxabs : |x| ≤ ε / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    exact hnonzero x (lt_of_le_of_lt hxabs (by linarith))
  let g : SmoothRealFunctionRing :=
    ⟨fun x : ℝ ↦ c x / f x, contMDiff_div_of_support_closure_subset c f hcsupp hcl⟩
  have hmul : f * g = c := by
    -- Pointwise, the quotient is exact where `f` is nonzero, and the cutoff vanishes elsewhere.
    ext x
    by_cases hfx : f x = 0
    · have hx_support : x ∉ Function.support (c : ℝ → ℝ) := by
        rw [hcsupp]
        intro hx'
        exact (hcl (subset_closure hx')) hfx
      have hcx : c x = 0 := by
        rwa [Function.notMem_support] at hx_support
      simp [g, hfx, hcx]
    · change f x * (c x / f x) = c x
      field_simp [hfx]
  have hc_one : Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal c = 1 := by
    -- The cutoff equals `1` on a neighborhood of `0`, so it is `1` in the quotient.
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal (c - 1) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨ε / 4, by linarith, ?_⟩
    intro x hx
    have hxt : x ∈ t := by
      change x ∈ Set.Icc (-(ε / 4)) (ε / 4)
      have hx' := abs_lt.mp hx
      constructor <;> linarith
    have hcx : c x = 1 := (hcone x).1 hxt
    simp [hcx]
  have hmulq :
      Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal f *
          Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal g = 1 := by
    calc
      Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal f *
          Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal g
          = Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal (f * g) := by
            simp
      _ = Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal c := by
            simpa using congrArg (Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal) hmul
      _ = 1 := hc_one
  refine ⟨Units.mkOfMulEqOne _ _ hmulq, ?_⟩
  simpa using Units.val_mkOfMulEqOne hmulq

/-- The quotient model `R / I` is a localization of `R` at the maximal ideal of functions
vanishing at `0`. -/
instance smoothRealFunctionQuotientAtZero_isLocalizationAtVanishingAtZeroIdeal :
    IsLocalization smoothRealFunctionsVanishingAtZeroIdeal.primeCompl
      smoothRealFunctionQuotientAtZero := by
  rw [isLocalization_iff]
  constructor
  · intro y
    refine quotient_mk_isUnit_of_eval_ne_zero y ?_
    intro hy0
    exact y.2 (by simpa [smoothRealFunctionsVanishingAtZeroIdeal] using hy0)
  constructor
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨⟨x, 1⟩, ?_⟩
    simp
  · intro x y hxy
    have hxy' :
        Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal x =
          Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal y := by
      simpa using hxy
    have hmem : x - y ∈ smoothRealFunctionsVanishingNearZeroIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hxy', sub_self]
    rcases exists_primeCompl_multiplier_eq_zero_of_mem_vanishingNearZeroIdeal (x - y) hmem with
      ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [mul_sub, sub_eq_zero] using hc

/-- The source-facing localization `R_𝔪` and the quotient model `R / I` are canonically
equivalent. -/
noncomputable abbrev smoothRealFunctionLocalizationAtZeroEquivQuotient :
    smoothRealFunctionLocalizationAtZero ≃ₐ[SmoothRealFunctionRing]
      smoothRealFunctionQuotientAtZero :=
  IsLocalization.algEquiv smoothRealFunctionsVanishingAtZeroIdeal.primeCompl _ _

/-- The module `M = R_𝔪` is finite over `R`. -/
instance smoothRealFunctionLocalizationAtZero_finite :
    Module.Finite SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero :=
  Module.Finite.equiv smoothRealFunctionLocalizationAtZeroEquivQuotient.symm.toLinearEquiv

/-- The source-facing localization `M = R_𝔪` is flat over `R = C^\infty(\mathbf R, \mathbf R)`. -/
instance smoothRealFunctionLocalizationAtZero_flat :
    Module.Flat SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero :=
  inferInstance

/-- Helper for Remark 10.78.4: a projective quotient ring comes from an idempotent generator of
the kernel ideal. -/
lemma exists_idempotent_generator_of_projective_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (hproj : Module.Projective R (R ⧸ I)) :
    ∃ e : R, IsIdempotentElem e ∧ e ∈ I ∧ I = Ideal.span {e} := by
  let _ : Module.Projective R (R ⧸ I) := hproj
  obtain ⟨σ, hσ⟩ :=
    (Module.Projective.iff_split_of_projective (R := R)
      ((Ideal.Quotient.mkₐ R I).toLinearMap) Ideal.Quotient.mk_surjective).mp hproj
  let e : R := 1 - σ 1
  -- The section sends `1` to a lift of `1`, so `e = 1 - σ(1)` lands in the kernel ideal.
  have hσ1 : Ideal.Quotient.mk I (σ 1) = 1 := by
    simpa using DFunLike.congr_fun hσ (1 : R ⧸ I)
  have he_mem : e ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp [e, hσ1]
  have hmul_right : ∀ {x : R}, x ∈ I → x = x * e := by
    -- Every kernel element is fixed by right multiplication with `e`.
    intro x hx
    have hxq : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hσx : σ (Ideal.Quotient.mk I x) = x * σ 1 := by
      calc
        σ (Ideal.Quotient.mk I x) = σ (x • (1 : R ⧸ I)) := by simp [Algebra.smul_def]
        _ = x • σ 1 := by rw [map_smul]
        _ = x * σ 1 := by simp [smul_eq_mul]
    have hxσ0 : x * σ 1 = 0 := by
      simpa [hσx] using congrArg σ hxq
    calc
      x = x * 1 := by simp
      _ = x * (e + σ 1) := by simp [e, sub_eq_add_neg, add_comm, add_left_comm]
      _ = x * e + x * σ 1 := by ring
      _ = x * e := by simp [hxσ0]
  have hspan_le : Ideal.span {e} ≤ I := (Ideal.span_singleton_le_iff_mem I).2 he_mem
  have hle : I ≤ Ideal.span {e} := by
    -- Conversely, every kernel element is a multiple of `e`.
    intro x hx
    rw [hmul_right hx]
    exact Ideal.mem_span_singleton'.mpr ⟨x, by simp⟩
  have he_idem : IsIdempotentElem e := by
    simpa [IsIdempotentElem] using (hmul_right he_mem).symm
  exact ⟨e, he_idem, he_mem, le_antisymm hle hspan_le⟩

/-- Helper for Remark 10.78.4: a smooth idempotent that vanishes on a neighborhood of `0` must be
the zero function. -/
lemma smooth_idempotent_eq_zero_of_vanishes_near_zero (f : SmoothRealFunctionRing)
    (hf : IsIdempotentElem f) (hvanish : f ∈ smoothRealFunctionsVanishingNearZeroIdeal) :
    f = 0 := by
  rcases hvanish with ⟨ε, hε, hzero⟩
  -- A nonzero value would have to be `1`, but connectedness forces the intermediate value `1/2`.
  ext x
  have hval : f x = 0 ∨ f x = 1 := by
    have hidx : IsIdempotentElem (f x) := by
      simpa [IsIdempotentElem] using congrArg (fun g : SmoothRealFunctionRing ↦ g x) hf
    exact IsIdempotentElem.iff_eq_zero_or_one.mp hidx
  rcases hval with hfx | hfx
  · exact hfx
  · have h0 : f 0 = 0 := hzero 0 (by simpa using hε)
    have hhalf : (1 / 2 : ℝ) ∈ Set.range (f : ℝ → ℝ) := by
      have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (f 0) (f x) := by
        rw [h0, hfx]
        norm_num
      exact intermediate_value_univ (0 : ℝ) x f.contMDiff.continuous hhalf_mem
    rcases hhalf with ⟨y, hy⟩
    have hy_idem : IsIdempotentElem (f y) := by
      simpa [IsIdempotentElem] using congrArg (fun g : SmoothRealFunctionRing ↦ g y) hf
    have : (1 / 2 : ℝ) = 0 ∨ (1 / 2 : ℝ) = 1 := by
      simpa [hy] using (IsIdempotentElem.iff_eq_zero_or_one.mp hy_idem)
    norm_num at this

/-- Helper for Remark 10.78.4: the near-zero ideal is nontrivial, witnessed by a bump function
supported away from the origin. -/
lemma smoothRealFunctionsVanishingNearZeroIdeal_ne_bot :
    smoothRealFunctionsVanishingNearZeroIdeal ≠ ⊥ := by
  let s : Set ℝ := Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)
  let t : Set ℝ := Set.Icc (1 : ℝ) 1
  rcases smooth_cutoff_support_eq_eq_one (s := s) (t := t) isOpen_Ioo isClosed_Icc
      (by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) with
    ⟨c, hcsupp, -, hcone⟩
  have hc_mem : c ∈ smoothRealFunctionsVanishingNearZeroIdeal := by
    -- The support is disjoint from a neighborhood of `0`, so the cutoff vanishes there.
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro x hx
    have hx_support : x ∉ Function.support (c : ℝ → ℝ) := by
      rw [hcsupp]
      intro hx'
      have hx'' : x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) := hx'
      have hxpos : (1 / 2 : ℝ) < x := hx''.1
      have hxabs' : x ≤ |x| := by exact le_abs_self x
      linarith
    rwa [Function.notMem_support] at hx_support
  intro hbot
  have hc_zero : c = 0 := by simpa [hbot] using hc_mem
  have hc1 : c 1 = 1 := (hcone 1).1 (by simp [t])
  have : (1 : ℝ) = 0 := by simpa [hc_zero] using hc1
  exact one_ne_zero this

-- Proof sketch: use the standard smooth-function counterexample: the localization `R_𝔪`,
-- equivalently the quotient `R / I`, is finite and flat but not projective.
/-- Remark 10.78.4: for `R = C^\infty(\mathbf R, \mathbf R)` and
`M = R_𝔪 = R / I`, where `𝔪` is the maximal ideal of functions vanishing at `0` and `I` consists
of smooth functions vanishing on a neighborhood of `0`, the module `M` is not projective.
Together with the companion instances asserting that `M` is finite and flat, this gives the stated
counterexample to the implication "finite flat implies projective". -/
theorem smoothRealFunctionLocalizationAtZero_not_projective :
    ¬ Module.Projective SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero := by
  -- Route correction: pass to the quotient model `R / I`, then force the kernel ideal to be
  -- idempotent-generated and use connectedness of `ℝ` to show that idempotent must vanish.
  intro hproj
  let _ : Module.Projective SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero := hproj
  have hquot :
      Module.Projective SmoothRealFunctionRing smoothRealFunctionQuotientAtZero :=
    Module.Projective.of_equiv' smoothRealFunctionLocalizationAtZeroEquivQuotient.toLinearEquiv
  obtain ⟨e, he_idem, he_mem, hI⟩ :=
    exists_idempotent_generator_of_projective_quotient
      smoothRealFunctionsVanishingNearZeroIdeal hquot
  have he_zero : e = 0 := smooth_idempotent_eq_zero_of_vanishes_near_zero e he_idem he_mem
  have hbot : smoothRealFunctionsVanishingNearZeroIdeal = ⊥ := by
    rw [hI, he_zero]
    simp
  exact smoothRealFunctionsVanishingNearZeroIdeal_ne_bot hbot

/-! ### Lemma_10_78_5 (from Chap10) -/
universe u v

section

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]

/- Lemma 10.78.5: if `R` is a local ring and `M` is a finite flat `R`-module, then `M` is free.
Together with the hypothesis `Module.Finite R M`, this is exactly the statement that `M` is finite
free, and mathlib provides it as `Module.free_of_flat_of_isLocalRing`. -/
recall Module.free_of_flat_of_isLocalRing

end

/-! ### Lemma_10_78_6 (from Chap10) -/
universe u v w

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
variable [AddCommGroup M] [Module R M]

/-- An `R`-module is finite projective if it is both finite and projective. -/
def Module.FiniteProjective (R : Type u) (M : Type w) [CommRing R] [AddCommMonoid M] [Module R M] :
    Prop :=
  Module.Finite R M ∧ Module.Projective R M

-- Proof sketch: the forward implication uses base change for finite and projective modules, namely
-- `Module.Finite.base_change` and the canonical owner instance `Projective.tensorProduct`. For the
-- converse, a flat local homomorphism is faithfully flat by
-- `Module.FaithfullyFlat.of_flat_of_isLocalHom`, and the canonical descent theorems recover
-- finiteness and flatness of `M` from the base change `S ⊗[R] M`. Over the local ring `R`,
-- finite flat modules are free, hence projective.
omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S] in
/-- Helper for Lemma 10.78.6: finite projective modules remain finite projective after base
change. -/
lemma finite_projective_tensorProduct (hM : Module.FiniteProjective R M) :
    Module.FiniteProjective S (S ⊗[R] M) := by
  rcases hM with ⟨hfinite, hprojective⟩
  let _ : Module.Finite R M := hfinite
  let _ : Module.Projective R M := hprojective
  -- Base change preserves both finite generation and projectivity.
  exact ⟨Module.Finite.base_change (R := R) (A := S) (M := M), inferInstance⟩

/-- Helper for Lemma 10.78.6: if the base change is finite projective over `S`, then faithful
flat descent recovers finiteness and flatness over `R`. -/
lemma finite_and_flat_of_finite_projective_tensor_of_flat_localHom
    (hM : Module.FiniteProjective S (S ⊗[R] M)) :
    Module.Finite R M ∧ Module.Flat R M := by
  let _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rcases hM with ⟨hfinite, hprojective⟩
  let _ : Module.Finite S (S ⊗[R] M) := hfinite
  let _ : Module.Projective S (S ⊗[R] M) := hprojective
  let _ : Module.Flat S (S ⊗[R] M) := Module.Flat.of_projective
  -- Descend finiteness and flatness separately along the faithfully flat local map.
  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S,
    Module.Flat.of_flat_tensorProduct (R := R) (M := M) S⟩

/-- Helper for Lemma 10.78.6: over a local ring, a finite flat module is finite projective. -/
lemma finite_projective_of_finite_flat_local (hfinite : Module.Finite R M) (hflat : Module.Flat R M) :
    Module.FiniteProjective R M := by
  let _ : Module.Finite R M := hfinite
  let _ : Module.Flat R M := hflat
  let _ : Module.Free R M := Module.free_of_flat_of_isLocalRing
  -- Over a local ring, finite flat modules are free, so projectivity follows from freeness.
  exact ⟨hfinite, Module.Projective.of_free⟩

/-- Lemma 10.78.6: for a flat local homomorphism `R → S` of local rings and an `R`-module `M`,
`M` is finite projective over `R` if and only if the base-change `S ⊗[R] M` is finite projective
over `S`. -/
theorem finite_projective_iff_finite_projective_tensor_of_flat_localHom :
    Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M) := by
  constructor
  · intro hM
    -- The easy direction is base change of a finite projective module.
    exact finite_projective_tensorProduct (R := R) (S := S) (M := M) hM
  · intro hMS
    -- First descend finiteness and flatness, then use the local criterion for finite projectives.
    rcases
        finite_and_flat_of_finite_projective_tensor_of_flat_localHom
          (R := R) (S := S) (M := M) hMS with
      ⟨hfinite, hflat⟩
    exact finite_projective_of_finite_flat_local (R := R) (M := M) hfinite hflat

end

/-! ### Lemma_10_78_7 (from Chap10) -/
universe u v

/- Domain-style sampling:
- primary domain: finite locally free modules over a semilocal ring, controlled by the fiber-rank
  function on `Spec R`;
- inspected owner-style declarations:
  `Module.free_of_flat_of_finrank_eq`,
  `Module.isLocallyConstant_rankAtStalk`,
  `Module.rankAtStalk_eq`,
  `Ideal.bijective_algebraMap_quotient_residueField`;
- owner abstraction: the canonical rank function `Module.rankAtStalk` together with the freeness
  criterion `Module.free_of_flat_of_finrank_eq`;
- layer: `source-facing`; the public theorem is the connected-spectrum corollary of the owner API;
- primitive data: the ring `R`, module `M`, and the semilocal/connectedness hypotheses;
- derived API: constancy of maximal fiber dimensions and the resulting `Module.Free R M`.
-/

/- Lemma 10.78.7: over a commutative semilocal ring, a finite locally free module whose fibers
over all maximal residue fields have the same finite dimension is free. -/
recall Module.free_of_flat_of_finrank_eq

variable {R : Type u} {M : Type v} [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup M] [Module R M]

open scoped TensorProduct

omit [Finite (MaximalSpectrum R)] in
private theorem maximalFiber_finrank_eq_rankAtStalk [Module.Finite R M] [Module.Flat R M]
    (P : MaximalSpectrum R) :
    Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      Module.rankAtStalk M P.toPrimeSpectrum := by
  let e : (R ⧸ P.asIdeal) ≃ₐ[R] P.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ P.asIdeal) P.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField P.asIdeal)
  let j := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  have hj : ∀ (r : R ⧸ P.asIdeal) (x : TensorProduct R (R ⧸ P.asIdeal) M),
      j (r • x) = e r • j x := by
    intro r x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a m
      change e (r * a) ⊗ₜ[R] m = e r • (e a ⊗ₜ[R] m)
      rw [map_mul]
      rfl
    · intro x y hx hy
      simp [smul_add, hx, hy]
  have hfinrank : Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      Module.finrank P.asIdeal.ResidueField (P.asIdeal.ResidueField ⊗[R] M) := by
    have hrank : Module.rank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
        Module.rank P.asIdeal.ResidueField (P.asIdeal.ResidueField ⊗[R] M) :=
      rank_eq_of_equiv_equiv e.toRingEquiv j.toAddEquiv e.toRingEquiv.bijective hj
    change Cardinal.toNat (Module.rank (R ⧸ P.asIdeal) (TensorProduct R (R ⧸ P.asIdeal) M)) =
      Cardinal.toNat (Module.rank P.asIdeal.ResidueField (TensorProduct R P.asIdeal.ResidueField M))
    exact congr_arg Cardinal.toNat hrank
  rw [hfinrank]
  exact (Module.rankAtStalk_eq P.toPrimeSpectrum).symm

/-- If a semilocal ring has connected spectrum, then every finite locally free module over it is
free. -/
-- Proof sketch: the rank function on `PrimeSpectrum R` is locally constant for finite flat modules.
-- On a connected spectrum it is therefore constant, so `Module.free_of_flat_of_finrank_eq` applies.
theorem free_of_semilocal_of_connected_spectrum [Module.FinitePresentation R M] [Module.Flat R M]
    [ConnectedSpace (PrimeSpectrum R)] : Module.Free R M := by
  let p₀ : PrimeSpectrum R := Classical.choice inferInstance
  let n := Module.rankAtStalk M p₀
  have hconst : Module.rankAtStalk M = Function.const (PrimeSpectrum R) n :=
    Module.isLocallyConstant_rankAtStalk.eq_const p₀
  refine Module.free_of_flat_of_finrank_eq R M n fun P ↦ ?_
  rw [maximalFiber_finrank_eq_rankAtStalk P]
  exact congrFun hconst P.toPrimeSpectrum
