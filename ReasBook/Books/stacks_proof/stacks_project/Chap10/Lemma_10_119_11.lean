import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_18
import stacks_proof.stacks_project.Chap10.Lemma_10_119_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped Pointwise

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [Ring.KrullDimLE 1 R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

/-- Helper for Chap10 Lemma 10 119 11: over a local one-dimensional Noetherian domain, quotienting an
`R`-submodule of a finite-dimensional fraction-field vector space by a nonzero scalar has finite
length. -/
lemma isFiniteLength_quotSMulTop_local_finiteDimensional
    {S : Type*} {L : Type*} {W : Type*}
    [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup W] [Module S W] [Module L W] [IsScalarTower S L W]
    [FiniteDimensional L W]
    (N : Submodule S W) {x : S} (hx : x ≠ 0) :
    IsFiniteLength S (QuotSMulTop x N) := by
  let s : ℕ := Module.finrank L W
  have hs :
      Module.finrank L W = Module.finrank L (Fin s → L) := by
    simp [s]
  let e : W ≃ₗ[L] (Fin s → L) := LinearEquiv.ofFinrankEq W (Fin s → L) hs
  let eS : W ≃ₗ[S] (Fin s → L) := e.restrictScalars S
  let eN : N ≃ₗ[S] N.map eS.toLinearMap :=
    Submodule.equivMapOfInjective eS.toLinearMap eS.injective N
  have hx_nonZeroDivisor : x ∈ nonZeroDivisors S := mem_nonZeroDivisors_iff_ne_zero.mpr hx
  have hquotient_finite :
      IsFiniteLength S (S ⧸ Ideal.span ({x} : Set S)) :=
    isFiniteLength_quotient_span_singleton S hx_nonZeroDivisor
  have hbound :
      Module.length S (QuotSMulTop x (N.map eS.toLinearMap)) ≤
        s * Module.length S (S ⧸ Ideal.span ({x} : Set S)) :=
    length_quotSMulTop_le_finrank_mul_length_quotient_span_singleton
      (R := S) (K := L) (M := N.map eS.toLinearMap)
  have hfinite_mapped :
      IsFiniteLength S (QuotSMulTop x (N.map eS.toLinearMap)) := by
    -- The coordinate-model bound from Lemma `10.119.9` has finite right-hand side because
    -- `S / xS` already has finite length.
    apply Module.length_ne_top_iff.mp
    have hquotient_ne_top :
        Module.length S (S ⧸ Ideal.span ({x} : Set S)) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr hquotient_finite
    have hrhs_ne_top :
        s * Module.length S (S ⧸ Ideal.span ({x} : Set S)) ≠ ⊤ := by
      exact WithTop.mul_ne_top (ENat.coe_ne_top s) hquotient_ne_top
    exact fun htop ↦ hrhs_ne_top (top_unique (by simpa [htop] using hbound))
  -- Transport the finite-length result back from the coordinate model to the original submodule.
  exact (QuotSMulTop.congr x eN.symm).isFiniteLength hfinite_mapped

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 11: the quotient `QuotSMulTop x M` is naturally annihilated by the
principal ideal `(x)`, so it carries the canonical `R ⧸ (x)`-module structure. -/
private theorem quotSMulTop_isTorsionBySet_span_singleton
    (M : Submodule R V) (x : R) :
    Module.IsTorsionBySet R (QuotSMulTop x M) (Ideal.span ({x} : Set R)) := by
  rw [← Module.isTorsionBySet_iff_is_torsion_by_span (R := R) (M := QuotSMulTop x M)
    ({x} : Set R)]
  rw [Module.isTorsionBySet_singleton_iff]
  change Module.IsTorsionBy R (↥M ⧸ x • (⊤ : Submodule R ↥M)) x
  simpa using (Module.isTorsionBy_quotient_element_smul (R := R) (M := ↥M) x)

/-- Helper for Chap10 Lemma 10 119 11: after equipping `V` with a localized `R_p`-action, localizing the
quotient `M / xM` at `p` agrees with quotienting the localized submodule by the image of `x`. -/
private noncomputable def localized_quotSMulTop_atPrime_equiv_localized_submodule_quotient
    (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [Module (Localization.AtPrime p) V]
    [IsScalarTower R (Localization.AtPrime p) V]
    [IsLocalizedModule p.primeCompl (LinearMap.id : V →ₗ[R] V)]
    (M : Submodule R V) (x : R) :
    LocalizedModule.AtPrime p
        (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)) ≃ₗ[Localization.AtPrime p]
      (↥(Submodule.localized' (Localization.AtPrime p) p.primeCompl
          (LinearMap.id : V →ₗ[R] V) M) ⧸
        Ideal.span ({algebraMap R (Localization.AtPrime p) x} :
          Set (Localization.AtPrime p)) •
          (⊤ : Submodule (Localization.AtPrime p)
            ↥(Submodule.localized' (Localization.AtPrime p) p.primeCompl
              (LinearMap.id : V →ₗ[R] V) M))) := by
  let S := Localization.AtPrime p
  let Mloc : Submodule S V :=
    Submodule.localized' S p.primeCompl (LinearMap.id : V →ₗ[R] V) M
  let IM : Submodule R ↥M := Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)
  let fM : ↥M →ₗ[R] Mloc :=
    Submodule.toLocalized' S p.primeCompl (LinearMap.id : V →ₗ[R] V) M
  have hlocalized :
      Submodule.localized' S p.primeCompl fM IM =
        Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc) := by
    -- Localizing the principal submodule `x • ⊤` inside `M` gives the principal submodule
    -- generated by `algebraMap R S x` inside the localized submodule.
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top]
    simpa [Set.image_singleton] using
      congrArg (fun J : Ideal S => J • (⊤ : Submodule S ↥Mloc))
        (Ideal.map_span (f := algebraMap R S) ({x} : Set R))
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e :
      (↥Mloc ⧸ Submodule.localized' S p.primeCompl fM IM) ≃ₗ[S]
        LocalizedModule.AtPrime p (↥M ⧸ IM) :=
    (IsLocalizedModule.linearEquiv p.primeCompl
      (IM.toLocalizedQuotient' S p.primeCompl fM)
      (LocalizedModule.mkLinearMap p.primeCompl (↥M ⧸ IM))).restrictScalars S
  exact
    e.symm.trans
      (Submodule.quotEquivOfEq _ _ hlocalized)

omit [Ring.KrullDimLE 1 R] [Algebra R K] [IsFractionRing R K] [IsScalarTower R K V] in
/-- Helper for Chap10 Lemma 10 119 11: every prime localization of `M / xM` has finite length over the
localized ring once the ambient finite-dimensional fraction-field action is localized onto `V`. -/
private theorem isFiniteLength_quotSMulTop_atPrime
    (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [Module (Localization.AtPrime p) V]
    [IsScalarTower R (Localization.AtPrime p) V]
    [IsScalarTower (Localization.AtPrime p) K V]
    [Ring.KrullDimLE 1 (Localization.AtPrime p)]
    [IsFractionRing (Localization.AtPrime p) K]
    [IsLocalizedModule p.primeCompl (LinearMap.id : V →ₗ[R] V)]
    (M : Submodule R V) {x : R}
    (hx : algebraMap R (Localization.AtPrime p) x ≠ 0) :
    IsFiniteLength (Localization.AtPrime p)
      (LocalizedModule.AtPrime p (QuotSMulTop x M)) := by
  let S := Localization.AtPrime p
  let Mloc : Submodule S V :=
    Submodule.localized' S p.primeCompl (LinearMap.id : V →ₗ[R] V) M
  have hlocal :
      IsFiniteLength S (QuotSMulTop (algebraMap R S x) Mloc) :=
    isFiniteLength_quotSMulTop_local_finiteDimensional (S := S) (L := K) (W := V) Mloc hx
  have hsmul :
      Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc) =
        algebraMap R S x • (⊤ : Submodule S ↥Mloc) := by
    simpa using
      (Submodule.ideal_span_singleton_smul (algebraMap R S x) (⊤ : Submodule S ↥Mloc))
  let eLocal :
      QuotSMulTop (algebraMap R S x) Mloc ≃ₗ[S]
        (↥Mloc ⧸ Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc)) :=
    Submodule.quotEquivOfEq _ _ hsmul.symm
  have hlocal' :
      IsFiniteLength S
        (↥Mloc ⧸ Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc)) :=
    eLocal.isFiniteLength hlocal
  let e :=
    localized_quotSMulTop_atPrime_equiv_localized_submodule_quotient
      (R := R) (K := K) (V := V) p M x
  have hsource :
      IsFiniteLength S
        (LocalizedModule.AtPrime p
          (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M))) :=
    e.symm.isFiniteLength hlocal'
  have hsmul_source :
      Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M) = x • (⊤ : Submodule R ↥M) := by
    simpa using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R ↥M))
  let eSource₀ : QuotSMulTop x M ≃ₗ[R]
      (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)) :=
    Submodule.quotEquivOfEq _ _ hsmul_source.symm
  let eSource :
      LocalizedModule.AtPrime p (QuotSMulTop x M) ≃ₗ[S]
        LocalizedModule.AtPrime p
          (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)) :=
    LinearEquiv.ofBijective
      (LocalizedModule.map p.primeCompl eSource₀.toLinearMap)
      ⟨LocalizedModule.map_injective p.primeCompl eSource₀.toLinearMap eSource₀.injective,
        LocalizedModule.map_surjective p.primeCompl eSource₀.toLinearMap eSource₀.surjective⟩
  exact eSource.symm.isFiniteLength hsource

/-- Helper for Chap10 Lemma 10 119 11: the principal quotient ring `R / (x)` is Artinian for nonzero
`x`, matching the source proof's ambient quotient-ring owner. -/
private theorem isArtinianRing_quotient_span_singleton_of_nonzero
    {x : R} (hx : x ≠ 0) :
    IsArtinianRing (R ⧸ Ideal.span ({x} : Set R)) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  letI : CommRing A := inferInstance
  have hfinite_R : IsFiniteLength R A :=
    isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  have hlength_eq : Module.length R A = Module.length A A := by
    simpa using
      (Module.length_eq_of_surjective
        (S := R)
        (R := A)
        (M := A)
        (Ideal.Quotient.mk_surjective (I := Ideal.span ({x} : Set R))))
  have hfinite_A : IsFiniteLength A A := by
    rw [← Module.length_ne_top_iff]
    simpa [hlength_eq] using (Module.length_ne_top_iff.mpr hfinite_R)
  exact (isArtinianRing_iff_isFiniteLength (R := A)).2 hfinite_A

/-- Helper for Chap10 Lemma 10 119 11: once `M / xM` is finite over the Artinian quotient ring `R / (x)`,
it has finite length over that quotient ring. -/
private theorem isFiniteLength_quotSMulTop_over_quotient_of_finite
    (M : Submodule R V) {x : R} (hx : x ≠ 0)
    [Module.Finite (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    IsFiniteLength (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  letI : CommRing A := inferInstance
  let hTors : Module.IsTorsionBySet R (QuotSMulTop x M) (Ideal.span ({x} : Set R)) :=
    quotSMulTop_isTorsionBySet_span_singleton (R := R) (V := V) M x
  letI : Module (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) := hTors.module
  letI : IsScalarTower R (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) :=
    Module.IsTorsionBySet.isScalarTower hTors
  letI : IsArtinianRing A := isArtinianRing_quotient_span_singleton_of_nonzero (R := R) hx
  exact (isFiniteLength_iff_isNoetherian_isArtinian).mpr ⟨inferInstance, inferInstance⟩

omit [Ring.KrullDimLE 1 R] [Algebra R K] [IsFractionRing R K] [IsScalarTower R K V] in
/-- Helper for Chap10 Lemma 10 119 11: every maximal localization of `M / xM` is finite over the
corresponding local ring because the localized quotient already has finite length. -/
private theorem moduleFinite_localized_quotSMulTop_atMaximal
    (m : Ideal R) [m.IsMaximal]
    [Algebra (Localization.AtPrime m) K] [Module (Localization.AtPrime m) V]
    [IsScalarTower R (Localization.AtPrime m) V]
    [IsScalarTower (Localization.AtPrime m) K V]
    [Ring.KrullDimLE 1 (Localization.AtPrime m)]
    [IsFractionRing (Localization.AtPrime m) K]
    [IsLocalizedModule m.primeCompl (LinearMap.id : V →ₗ[R] V)]
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.Finite (Localization.AtPrime m)
      (LocalizedModule.AtPrime m (QuotSMulTop x M)) := by
  -- The local finite-length statement already gives the localized quotient a Noetherian module
  -- structure, and finitely generatedness is exactly the top submodule being finitely generated.
  have hfiniteLength :
      IsFiniteLength (Localization.AtPrime m)
        (LocalizedModule.AtPrime m (QuotSMulTop x M)) := by
    have hx_map : algebraMap R (Localization.AtPrime m) x ≠ 0 := by
      intro hx_map
      exact hx <| FaithfulSMul.algebraMap_injective R (Localization.AtPrime m) <| by
        simpa using hx_map
    exact isFiniteLength_quotSMulTop_atPrime (R := R) (K := K) (V := V) m M hx_map
  have hnoetherian :
      IsNoetherian (Localization.AtPrime m)
        (LocalizedModule.AtPrime m (QuotSMulTop x M)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
  rw [Module.finite_def]
  exact hnoetherian.noetherian _

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 11: an element of a quotient ring outside a prime ideal lifts to an
element of the source ring outside the pulled-back prime ideal. -/
private theorem exists_lift_in_comap_prime_compl
    {I : Ideal R} (P : Ideal (R ⧸ I)) [P.IsPrime]
    (a : R ⧸ I) (ha : a ∈ P.primeCompl) :
    ∃ r : R, Ideal.Quotient.mk I r = a ∧
      r ∈ (Ideal.comap (algebraMap R (R ⧸ I)) P).primeCompl := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
  refine ⟨r, rfl, ?_⟩
  change Ideal.Quotient.mk I r ∉ P
  simpa using ha

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 11: the pullback of a maximal ideal along a quotient map is
maximal. -/
private theorem isMaximal_under_quotient
    {I : Ideal R} (P : Ideal (R ⧸ I)) [P.IsMaximal] :
    (P.under R).IsMaximal := by
  -- Maximality pulls back along the surjective quotient map `R → R / I`.
  simpa [Ideal.under_def] using
    (Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      (Ideal.Quotient.mk_surjective (I := I)) (K := P))

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 11: localizing an `R ⧸ I`-module at `P` is also localization
over `R` at the pulled-back prime `P.under R`. -/
private theorem isLocalizedModule_atPrime_quotient_under
    {I : Ideal R} (P : Ideal (R ⧸ I)) [P.IsPrime]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N]
    [IsScalarTower R (R ⧸ I) N] :
    IsLocalizedModule (P.under R).primeCompl
      ((LocalizedModule.mkLinearMap P.primeCompl N).restrictScalars R) := by
  let A := R ⧸ I
  let fA := LocalizedModule.mkLinearMap P.primeCompl N
  refine ⟨?_, ?_, ?_⟩
  · -- A denominator in the pulled-back complement maps to an invertible denominator after
    -- quotient-localization.
    intro s
    have hsA : (algebraMap R A (s : R)) ∈ P.primeCompl := s.2
    have hunitA : IsUnit (algebraMap A (Module.End A (LocalizedModule.AtPrime P N))
        (algebraMap R A (s : R))) :=
      IsLocalizedModule.map_units fA ⟨algebraMap R A (s : R), hsA⟩
    rw [Module.End.isUnit_iff] at hunitA ⊢
    convert hunitA using 1
    ext y
    exact (IsScalarTower.algebraMap_smul (R := R) (A := A)
      (M := LocalizedModule.AtPrime P N) (s : R) y).symm
  · -- Surjectivity over the quotient lifts denominators to representatives outside `P.under R`.
    intro y
    obtain ⟨⟨n, a⟩, ha⟩ := IsLocalizedModule.surj P.primeCompl fA y
    obtain ⟨r, hr, hrq⟩ := exists_lift_in_comap_prime_compl P (a : A) a.2
    have hrq' : r ∈ (P.under R).primeCompl := by
      simpa [Ideal.under_def] using hrq
    refine ⟨⟨n, ⟨r, hrq'⟩⟩, ?_⟩
    calc
      (r : R) • y = (algebraMap R A r) • y :=
        (IsScalarTower.algebraMap_smul (R := R) (A := A)
          (M := LocalizedModule.AtPrime P N) r y).symm
      _ = (a : A) • y := by
        simpa [A] using congrArg (fun t : A => t • y) hr
      _ = fA n := ha
  · -- Equality in the quotient localization similarly clears after a lifted denominator.
    intro x₁ x₂ h
    obtain ⟨a, ha⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) (f := fA) h
    obtain ⟨r, hr, hrq⟩ := exists_lift_in_comap_prime_compl P (a : A) a.2
    have hrq' : r ∈ (P.under R).primeCompl := by
      simpa [Ideal.under_def] using hrq
    refine ⟨⟨r, hrq'⟩, ?_⟩
    calc
      (r : R) • x₁ = (algebraMap R A r) • x₁ :=
        (IsScalarTower.algebraMap_smul (R := R) (A := A) (M := N) r x₁).symm
      _ = (a : A) • x₁ := by
        simpa [A] using congrArg (fun t : A => t • x₁) hr
      _ = (a : A) • x₂ := ha
      _ = (algebraMap R A r) • x₂ := by
        simpa [A] using (congrArg (fun t : A => t • x₂) hr).symm
      _ = (r : R) • x₂ :=
        IsScalarTower.algebraMap_smul (R := R) (A := A) (M := N) r x₂

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 11: finite generation survives the comparison between
localization at `P.under R` and quotient-localization at `P`. -/
private theorem moduleFinite_atPrime_quotient_of_under
    {I : Ideal R} (P : Ideal (R ⧸ I)) [P.IsPrime]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N]
    [IsScalarTower R (R ⧸ I) N] :
    Module.Finite (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime (P.under R) N) →
      Module.Finite (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P N) := by
  intro hfinite
  let q := P.under R
  let S := Localization.AtPrime q
  letI : P.LiesOver q := Ideal.LiesOver.mk rfl
  letI : IsLocalizedModule q.primeCompl
      ((LocalizedModule.mkLinearMap P.primeCompl N).restrictScalars R) :=
    isLocalizedModule_atPrime_quotient_under P N
  -- The two localized modules satisfy the same universal property over `R_q`, so finite
  -- generation transports across the canonical `R_q`-linear equivalence.
  let e : LocalizedModule.AtPrime q N ≃ₗ[S] LocalizedModule.AtPrime P N :=
    IsLocalizedModule.mapEquiv q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl N)
      ((LocalizedModule.mkLinearMap P.primeCompl N).restrictScalars R)
      S (LinearEquiv.refl R N)
  letI : Module.Finite S (LocalizedModule.AtPrime q N) := hfinite
  exact Module.Finite.equiv e

include K

/-- Chap10 Lemma 10 119 11: after pulling a maximal ideal of `R ⧸ (x)` back to `R`, the standard
localization at that maximal ideal controls the quotient localization over `R ⧸ (x)`. -/
private theorem moduleFinite_localized_quotSMulTop_over_principal_quotient_atMaximal
    (M : Submodule R V) {x : R} (hx : x ≠ 0)
    (P : Ideal (R ⧸ Ideal.span ({x} : Set R))) [P.IsMaximal] :
    Module.Finite (Localization.AtPrime P)
      (LocalizedModule.AtPrime P (QuotSMulTop x M)) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  let N := QuotSMulTop x M
  let q := P.under R
  let hTors : Module.IsTorsionBySet R N (Ideal.span ({x} : Set R)) :=
    quotSMulTop_isTorsionBySet_span_singleton (R := R) (V := V) M x
  letI : Module A N := hTors.module
  letI : IsScalarTower R A N := Module.IsTorsionBySet.isScalarTower hTors
  letI : q.IsMaximal :=
    isMaximal_under_quotient (I := Ideal.span ({x} : Set R)) P
  let S := Localization.AtPrime q
  have hUnits : ∀ y : q.primeCompl, IsUnit ((algebraMap R K) (y : R)) := by
    intro y
    -- Elements outside the prime are nonzero in the domain, hence units in the fraction field.
    rw [isUnit_iff_ne_zero]
    exact (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr
      (nonZeroDivisors.ne_zero (q.primeCompl_le_nonZeroDivisors y.2))
  letI : Algebra S K :=
    (IsLocalization.lift (S := S) (P := K) (M := q.primeCompl)
      (g := algebraMap R K) hUnits).toAlgebra
  letI : IsScalarTower R S K :=
    IsScalarTower.of_algebraMap_eq'
      (IsLocalization.lift_comp (S := S) (P := K) (M := q.primeCompl)
        (g := algebraMap R K) hUnits).symm
  letI : Module S V := Module.compHom V (algebraMap S K)
  letI : IsScalarTower S K V := IsScalarTower.of_compHom S K V
  letI : IsScalarTower R S V := by
    -- The localized `R_q`-action on `V` is the one induced by the fraction-field action.
    refine IsScalarTower.of_algebraMap_smul (R := R) (A := S) (M := V) ?_
    intro r v
    calc
      algebraMap R S r • v = algebraMap S K (algebraMap R S r) • v := rfl
      _ = algebraMap R K r • v := by
        rw [← IsScalarTower.algebraMap_apply R S K r]
      _ = r • v := IsScalarTower.algebraMap_smul (R := R) (A := K) (M := V) r v
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl S K
  letI : IsLocalizedModule q.primeCompl (LinearMap.id : V →ₗ[R] V) :=
    isLocalizedModule_id q.primeCompl V S
  letI : Ring.KrullDimLE 1 S := by
    -- The height formula for localization at a prime bounds the local dimension by the ambient
    -- one-dimensional hypothesis.
    rw [Ring.krullDimLE_iff]
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q S]
    have hheight : (q.height : WithBot ℕ∞) ≤ ringKrullDim R := by
      rw [Ideal.height_eq_primeHeight]
      simpa [Ideal.primeHeight, ringKrullDim] using
        (Order.height_le_krullDim (PrimeSpectrum.mk q inferInstance))
    exact hheight.trans ((Ring.krullDimLE_iff (R := R) (n := 1)).mp inferInstance)
  have hfinite_under :
      Module.Finite S (LocalizedModule.AtPrime q N) :=
    moduleFinite_localized_quotSMulTop_atMaximal (R := R) (K := K) (V := V) q M hx
  have hfinite_restrict :
      Module.Finite S (LocalizedModule.AtPrime P N) :=
    moduleFinite_atPrime_quotient_of_under
      (I := Ideal.span ({x} : Set R)) P N hfinite_under
  letI : P.LiesOver q := Ideal.LiesOver.mk rfl
  letI : Module.Finite S (LocalizedModule.AtPrime P N) := hfinite_restrict
  -- Finally, finite generation over `R_q` gives finite generation over the quotient-local ring
  -- `(R / (x))_P` by extension of scalars along the canonical local map.
  exact Module.Finite.of_restrictScalars_finite S (Localization.AtPrime P)
    (LocalizedModule.AtPrime P N)

/-- Helper for Chap10 Lemma 10 119 11: once the localizations of `M / xM` at maximal ideals of
`R ⧸ (x)` are controlled, the source proof globalizes finite generation over the quotient ring
`R ⧸ (x)`. -/
private theorem moduleFinite_quotSMulTop_over_principal_quotient
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.Finite (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  let N := QuotSMulTop x M
  let hTors : Module.IsTorsionBySet R N (Ideal.span ({x} : Set R)) :=
    quotSMulTop_isTorsionBySet_span_singleton (R := R) (V := V) M x
  letI : Module A N := hTors.module
  letI : IsScalarTower R A N := Module.IsTorsionBySet.isScalarTower hTors
  letI : IsArtinianRing A := isArtinianRing_quotient_span_singleton_of_nonzero (R := R) hx
  letI : Finite (MaximalSpectrum A) := inferInstance
  -- The source proof globalizes from maximal localizations over the Artinian quotient ring.
  apply Module.Finite.of_localized_maximal (R := A) (M := N)
  intro P _hP
  simpa using
    moduleFinite_localized_quotSMulTop_over_principal_quotient_atMaximal
      (R := R) (K := K) (V := V) M hx P

/-
Domain triage:
* primary domain: module length for principal quotients of `R`-submodules inside a finite-
  dimensional fraction-field vector space;
* sampled owner API: `QuotSMulTop`, `QuotSMulTop.congr`, `IsFiniteLength`,
  `Module.length_ne_top_iff`, and the finite-dimensional transport API
  `LinearEquiv.ofFinrankEq`;
* source/core/bridge split: Lemma `10.119.11` is `source-facing`, the quotient owner is
  `QuotSMulTop x M`, the finiteness owner is `IsFiniteLength R`, and the ambient owner abstraction
  is an `R`-submodule of a finite-dimensional `K`-vector space `V`;
* primitive data vs. derived API: the primitive inputs are the submodule `M`, the nonzero element
  `x`, and the ambient finite-dimensional `K`-space; any coordinate presentation
  `V ≃ₗ[K] Fin (finrank K V) → K` is derived from a basis and should not remain the public owner.
-/

-- Proof sketch: the support of `R / xR` is the finite set of maximal ideals containing `x`, since
-- a one-dimensional Noetherian domain has only maximal primes above a nonzero principal ideal.
-- Localize `M / xM` at those maximal ideals and, after choosing a `K`-basis of `V`, transport the
-- localized problem via `QuotSMulTop.congr` to the coordinate model `K^{\oplus r}` where the local
-- one-dimensional statement from Lemma `10.119.9` applies. Transporting back, the quotient has a
-- finite filtration with residue-field subquotients, so its `R`-length is finite.
/-- Helper for Chap10 Lemma 10 119 11: if `R` is a Noetherian domain of Krull dimension at most
`1`, `M` is an `R`-submodule of a finite-dimensional `K`-vector space `V`, and `x ∈ R` is
nonzero, then the quotient `M / xM`, written canonically as `QuotSMulTop x M`, has finite length
over `R`. -/
@[stacks 00PF]
theorem isFiniteLength_quotSMulTop_submodule_of_nonzero
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (QuotSMulTop x M) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  let N := QuotSMulTop x M
  let hTors : Module.IsTorsionBySet R N (Ideal.span ({x} : Set R)) :=
    quotSMulTop_isTorsionBySet_span_singleton (R := R) (V := V) M x
  letI : Module A N := hTors.module
  letI : IsScalarTower R A N := Module.IsTorsionBySet.isScalarTower hTors
  letI : Module.Finite A N :=
    moduleFinite_quotSMulTop_over_principal_quotient (K := K) M hx
  have hfiniteA : IsFiniteLength A N := by
    letI : IsArtinianRing A := isArtinianRing_quotient_span_singleton_of_nonzero (R := R) hx
    exact (isFiniteLength_iff_isNoetherian_isArtinian).mpr ⟨inferInstance, inferInstance⟩
  have hlength_eq : Module.length R N = Module.length A N := by
    simpa using
      (Module.length_eq_of_surjective
        (S := R)
        (R := A)
        (M := N)
        (Ideal.Quotient.mk_surjective (I := Ideal.span ({x} : Set R))))
  -- Transfer the finite-length statement back across the surjective quotient map `R → R / (x)`.
  exact Module.length_ne_top_iff.mp <| by
    intro htop
    rw [hlength_eq] at htop
    exact (Module.length_ne_top_iff.mpr hfiniteA) htop

/-- Helper for Chap10 Lemma 10 119 11: source-facing numerical form of the finite-length theorem. -/
theorem length_submodule_quotient_by_nonzero_lt_top
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x M) < ⊤ := by
  exact lt_top_iff_ne_top.mpr <|
    Module.length_ne_top_iff.mpr <|
      isFiniteLength_quotSMulTop_submodule_of_nonzero (K := K) M hx

end
