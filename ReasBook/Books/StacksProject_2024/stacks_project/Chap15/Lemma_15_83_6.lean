import Mathlib
import StacksProject_2024.Chap10.Lemma_10_109_9
import StacksProject_2024.Chap15.Definition_15_33_2
import StacksProject_2024.Chap15.Lemma_15_33_5
import StacksProject_2024.Chap15.Lemma_15_75_3
import StacksProject_2024.Chap15.Lemma_15_75_12
import StacksProject_2024.Chap15.Lemma_15_83_2
import StacksProject_2024.Chap15.Definition_15_83_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped DerivedTensorWithAlgebra

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 15.83.6: localizing a degree-zero module agrees with tensoring its degree-zero
derived object with the away-localization algebra. -/
noncomputable theorem single0_localizationAway_iso
    (g : R) (M : ModuleCat R) :
    ((ModuleCat.single0Functor.obj M) ⊗[R]^L[Localization.Away g]) ≅
      ModuleCat.single0Functor.obj
        (ModuleCat.of (Localization.Away g) (LocalizedModule.Away g M)) := by
  let Rg := Localization.Away g
  letI : Algebra R Rg := inferInstance
  letI : Module.Flat R Rg := inferInstance
  let eSingle :
      (((ModuleCat.extendScalars (algebraMap R Rg)).mapDerivedCategory).obj
        (ModuleCat.single0Functor.obj M)) ≅
        ModuleCat.single0Functor.obj
          ((ModuleCat.extendScalars (algebraMap R Rg)).obj M) :=
    -- Proof comment: exact scalar extension preserves strict degree-zero complexes, so after
    -- passing through `Q` it still lands on a degree-zero object.
    (((ModuleCat.extendScalars (algebraMap R Rg)).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M)) ≪≫
      (ModuleCat.extendScalars (algebraMap R Rg)).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.extendScalars (algebraMap R Rg))
          (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat Rg) (0 : ℤ)).app
        ((ModuleCat.extendScalars (algebraMap R Rg)).obj M)).symm
  -- Proof comment: first replace derived tensor by exact scalar extension using flatness of
  -- `R → R_g`, then identify ordinary scalar extension with the canonical away-localized module.
  exact
    ((extendScalars_mapDerivedCategory_iso (R := R) (R' := Rg)).symm.app
      (ModuleCat.single0Functor.obj M)) ≪≫
      eSingle ≪≫
      ModuleCat.single0Functor.mapIso (extendScalars_to_localizedAway_iso (R := R) g M)

end

end CategoryTheory

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [RingHom.IsLocalCompleteIntersection (algebraMap A B)]

section Auxiliary

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 15.83.6: a linear equivalence of `R`-modules gives an isomorphism in
`ModuleCat R`. -/
private def moduleCat_iso_of_linearEquiv
    {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    ModuleCat.of R M ≅ ModuleCat.of R N where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap

/-- Helper for Lemma 15.83.6: a linear equivalence identifies a submodule with its image. -/
private def submodule_map_linearEquiv
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (K : Submodule R M) :
    K ≃ₗ[R] Submodule.map e.toLinearMap K where
  toFun x := ⟨e x, ⟨x, x.2, rfl⟩⟩
  invFun y := ⟨e.symm y, by
    rcases y.2 with ⟨x, hx, hxy⟩
    have hx' : e.symm y = x := by
      apply e.injective
      simpa using hxy
    simpa [hx'] using hx⟩
  left_inv x := by
    -- Proof comment: after applying `e` and then `e.symm`, the original submodule element is
    -- recovered on the nose.
    ext
    simp
  right_inv y := by
    -- Proof comment: an element of the image submodule is represented by some `x ∈ K`, and the
    -- inverse sends it back to that chosen representative.
    rcases y.2 with ⟨x, hx, hxy⟩
    ext
    exact e.injective (by simpa using hxy)
  map_add' x y := by
    ext
    simp
  map_smul' a x := by
    ext
    simp

/-- Helper for Lemma 15.83.6: localizing the regular module identifies it with the away-localized
ring itself. -/
private noncomputable def localizedAway_ring_linearEquiv (g : R) :
    LocalizedModule.Away g R ≃ₗ[Localization.Away g] Localization.Away g :=
  (LocalizedModule.equivTensorProduct (Submonoid.powers g) R).trans
    (TensorProduct.AlgebraTensorModule.rid R (Localization.Away g) (Localization.Away g))

/-- Helper for Lemma 15.83.6: the canonical map from an ideal to its image in an away
localization. -/
private def ideal_map_away_linearMap (I : Ideal R) (g : R) :
    I →ₗ[R] Ideal.map (algebraMap R (Localization.Away g)) I where
  toFun x := ⟨algebraMap R (Localization.Away g) x.1, Ideal.mem_map_of_mem _ x.2⟩
  map_add' x y := by
    -- Proof comment: the localized image of a sum is the sum of the localized images.
    ext
    simp
  map_smul' a x := by
    -- Proof comment: scalar multiplication commutes with the localization map.
    ext
    simp [Algebra.smul_def]

/-- Helper for Lemma 15.83.6: the mapped ideal in `R_g` is a localization target of `I`. -/
private theorem ideal_map_away_surj
    (I : Ideal R) (g : R)
    (y : Ideal.map (algebraMap R (Localization.Away g)) I) :
    ∃ x : I × Submonoid.powers g,
      x.2 • y = ideal_map_away_linearMap (R := R) I g x.1 := by
  let Rg := Localization.Away g
  have hspan :
      Ideal.map (algebraMap R Rg) I =
        Ideal.span ((algebraMap R Rg) '' (↑I : Set R)) := by
    -- Proof comment: rewrite the mapped ideal as the span of the literal images of elements of
    -- `I`, so denominator clearing can proceed by span induction.
    simpa [Ideal.span_eq] using
      (Ideal.map_span (algebraMap R Rg) (↑I : Set R))
  have hy :
      (y : Rg) ∈ Ideal.span ((algebraMap R Rg) '' (↑I : Set R)) := by
    simpa [hspan] using y.2
  have hclear :
      ∀ z : Rg,
        z ∈ Ideal.span ((algebraMap R Rg) '' (↑I : Set R)) →
          ∃ x : I, ∃ s : Submonoid.powers g,
            (s : R) • z = algebraMap R Rg (x : R) := by
    intro z hz
    refine Submodule.span_induction
      (p := fun z _ ↦
        ∃ x : I, ∃ s : Submonoid.powers g,
          (s : R) • z = algebraMap R Rg (x : R))
      ?_ ?_ ?_ ?_ hz
    · intro z hzmem
      rcases hzmem with ⟨a, ha, rfl⟩
      let x : I := ⟨a, ha⟩
      have hx :
          ((1 : Submonoid.powers g) : R) • algebraMap R Rg a =
            algebraMap R Rg (x : R) := by
        simp [x]
      exact ⟨x, 1, hx⟩
    · let x : I := 0
      have hx : ((1 : Submonoid.powers g) : R) • (0 : Rg) = algebraMap R Rg (x : R) := by
        simp [x]
      exact ⟨x, 1, hx⟩
    · intro z₁ z₂ hz₁ hz₂
      rcases hz₁ with ⟨x₁, s₁, hs₁⟩
      rcases hz₂ with ⟨x₂, s₂, hs₂⟩
      let x : I := s₂.1 • x₁ + s₁.1 • x₂
      have hx :
          (((s₁ * s₂ : Submonoid.powers g) : R) • (z₁ + z₂)) =
            algebraMap R Rg (x : R) := by
        -- Proof comment: clear the two existing denominators simultaneously and package the
        -- resulting numerator back into the ideal.
        calc
          (((s₁ * s₂ : Submonoid.powers g) : R) • (z₁ + z₂))
              = (s₂ : R) • ((s₁ : R) • z₁) + (s₁ : R) • ((s₂ : R) • z₂) := by
                  simp [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
          _ = (s₂ : R) • algebraMap R Rg (x₁ : R) + (s₁ : R) • algebraMap R Rg (x₂ : R) := by
                rw [hs₁, hs₂]
          _ = algebraMap R Rg (x : R) := by
                simp [x, Algebra.smul_def, mul_add, map_add, mul_comm, mul_left_comm, mul_assoc]
      exact ⟨x, s₁ * s₂, hx⟩
    · intro c z hz
      rcases hz with ⟨x, s, hs⟩
      obtain ⟨⟨num, den⟩, hfrac⟩ := IsLocalization.surj (Submonoid.powers g) c
      let x' : I := num • x
      have hx :
          (((den * s : Submonoid.powers g) : R) • (c • z)) =
            algebraMap R Rg (x' : R) := by
        -- Proof comment: rewrite the localization scalar with one numerator and denominator, then
        -- fold the cleared denominator into the existing witness for `z`.
        calc
          (((den * s : Submonoid.powers g) : R) • (c • z))
              = (c * algebraMap R Rg (den : R)) * ((algebraMap R Rg (s : R)) * z) := by
                  simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
          _ = algebraMap R Rg num * algebraMap R Rg (x : R) := by
                rw [hfrac, hs]
          _ = algebraMap R Rg (x' : R) := by
                simp [x', Algebra.smul_def, mul_assoc]
      exact ⟨x', den * s, hx⟩
  rcases hclear y hy with ⟨x, s, hs⟩
  refine ⟨⟨x, s⟩, ?_⟩
  ext
  simpa [ideal_map_away_linearMap] using hs

/-- Helper for Lemma 15.83.6: the mapped ideal in `R_g` is a localization target of `I`. -/
private theorem ideal_map_away_isLocalizedModule
    (I : Ideal R) (g : R) :
    IsLocalizedModule (Submonoid.powers g) (ideal_map_away_linearMap (R := R) I g) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro s
    -- Proof comment: powers of `g` become units in `R_g`, so they act invertibly on the mapped
    -- ideal as well.
    rw [Module.End.isUnit_iff]
    change Function.Bijective
      (fun y : Ideal.map (algebraMap R (Localization.Away g)) I ↦ (↑s : R) • y)
    have hs : IsUnit ((algebraMap R (Localization.Away g)) ↑s) :=
      IsLocalization.map_units (Localization.Away g) s
    rcases hs with ⟨u, hu⟩
    rw [show
      (fun y : Ideal.map (algebraMap R (Localization.Away g)) I ↦ (↑s : R) • y) =
        fun y : Ideal.map (algebraMap R (Localization.Away g)) I ↦
          (↑u : Localization.Away g) • y by
      funext y
      simp [hu, Algebra.smul_def]]
    exact (LinearEquiv.smulOfUnit u).bijective
  · -- Proof comment: the remaining localization axiom is the denominator-clearing statement for
    -- elements of the mapped ideal, now expressed as the dedicated span-induction lemma above.
    intro y
    exact ideal_map_away_surj (R := R) I g y
  · intro x₁ x₂ hEq
    -- Proof comment: equality of two localized ideal elements comes from equality in the ambient
    -- localization, so one common power of `g` clears the denominators.
    rcases
        (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).mp
          (Subtype.ext_iff.mp hEq) with
      ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext
    exact hc

/-- Helper for Lemma 15.83.6: the away-localized ideal module identifies canonically with the
mapped ideal in the away-localized ring. -/
private noncomputable def localizedAway_ideal_map_linearEquiv
    (I : Ideal R) (g : R) :
    LocalizedModule.Away g I ≃ₗ[Localization.Away g]
      Ideal.map (algebraMap R (Localization.Away g)) I := by
  let e :
      LocalizedModule.Away g I ≃ₗ[R]
        Ideal.map (algebraMap R (Localization.Away g)) I :=
    IsLocalizedModule.linearEquiv (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) I)
      (ideal_map_away_linearMap (R := R) I g)
  let _ : Module (Localization.Away g) (Ideal.map (algebraMap R (Localization.Away g)) I) :=
    inferInstance
  let _ :
      IsScalarTower R (Localization.Away g)
        (Ideal.map (algebraMap R (Localization.Away g)) I) :=
    inferInstance
  -- Proof comment: once both targets are recognized as universal localizations of `I`, the
  -- comparison upgrades from an `R`-linear equivalence to the canonical `R_g`-linear one.
  exact
    LinearEquiv.extendScalarsOfIsLocalization
      (Submonoid.powers g) (Localization.Away g) e

/-- Helper for Lemma 15.83.6: the ideal inclusion followed by the quotient map is zero in the
canonical quotient short complex. -/
private theorem ideal_subtype_comp_mkQ_eq_zero (I : Ideal R) :
    ModuleCat.ofHom I.subtype ≫ ModuleCat.ofHom I.mkQ = 0 := by
  -- Proof comment: every element of the ideal maps to zero in the quotient by that same ideal.
  apply ModuleCat.hom_ext
  exact LinearMap.ext fun x ↦ by
    change Submodule.Quotient.mk ((I.subtype x : R)) = Submodule.Quotient.mk (0 : R)
    rw [Submodule.Quotient.eq]
    simpa using x.2

/-- Helper for Lemma 15.83.6: the ideal inclusion and quotient map form the standard short
complex `0 → I → R → R / I → 0` in `ModuleCat R`. -/
private abbrev ideal_quotient_shortComplex (I : Ideal R) :
    CategoryTheory.ShortComplex (ModuleCat R) :=
  CategoryTheory.ShortComplex.mk
    (ModuleCat.ofHom I.subtype)
    (ModuleCat.ofHom I.mkQ)
    (ideal_subtype_comp_mkQ_eq_zero (R := R) I)

/-- Helper for Lemma 15.83.6: the canonical quotient sequence `0 → I → R → R / I → 0` is short
exact in `ModuleCat R`. -/
private theorem ideal_quotient_shortExact (I : Ideal R) :
    (ideal_quotient_shortComplex (R := R) I).ShortExact := by
  -- Proof comment: package the standard quotient sequence using the concrete exactness theorem
  -- `LinearMap.exact_subtype_mkQ` and the usual mono/epi characterizations in `ModuleCat`.
  have hMono : Mono (ideal_quotient_shortComplex (R := R) I).f := by
    rw [ModuleCat.mono_iff_injective]
    exact I.subtype_injective
  have hEpi : Epi (ideal_quotient_shortComplex (R := R) I).g := by
    rw [ModuleCat.epi_iff_surjective]
    exact Submodule.mkQ_surjective I
  have hExact : (ideal_quotient_shortComplex (R := R) I).Exact := by
    rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (ideal_quotient_shortComplex (R := R) I)]
    exact LinearMap.exact_subtype_mkQ I
  exact CategoryTheory.ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Helper for Lemma 15.83.6: if the ideal module `I` is perfect, then the quotient module
`R / I` is perfect as well. -/
private theorem idealQuotient_isPerfect_of_isPerfect_ideal
    (I : Ideal R) [Module.Finite R I]
    (hI : (ModuleCat.of R I).IsPerfect) :
    (ModuleCat.of R (R ⧸ I)).IsPerfect := by
  -- Proof comment: convert perfectness of `I` into a finite projective-dimension bound, feed it
  -- through the short exact sequence `0 → I → R → R / I → 0`, and then convert back.
  rcases
      (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of R I)).1 hI with
    ⟨d, hd⟩
  have h₁ : HasProjectiveDimensionLE (ModuleCat.of R I) d := by
    exact
      (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (R := R) (M := I) d).2 hd
  have h₂ : HasProjectiveDimensionLE (ModuleCat.of R R) (d + 1) := by
    -- The regular module is projective, hence has projective dimension bounded by every
    -- successor.
    letI : Projective (ModuleCat.of R R) := inferInstance
    infer_instance
  have h₃ : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) (d + 1) := by
    exact
      CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₃
        (ideal_quotient_shortExact (R := R) I) d h₁ h₂
  exact
    (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
      (ModuleCat.of R (R ⧸ I))).2
      ⟨d + 1,
        (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
          (R := R) (M := (R ⧸ I)) (d + 1)).1 h₃⟩

/-- Helper for Lemma 15.83.6: a subsingleton module is perfect because it is simultaneously
finite and projective. -/
private theorem isPerfect_of_subsingleton_module
    {M : Type u} [AddCommGroup M] [Module R M] [Subsingleton M] :
    (ModuleCat.of R M).IsPerfect := by
  -- Proof comment: a subsingleton module is free on the empty/singleton basis, hence projective,
  -- and it is isomorphic to the zero module, hence finite.
  refine
    (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
      (ModuleCat.of R M)).2 ?_
  refine ⟨0, ?_⟩
  rw [hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
  constructor
  · letI : Module.Free R M := Module.Free.of_subsingleton (R := R) (N := M)
    exact Module.Projective.of_free
  · have hzero : CategoryTheory.Limits.IsZero (ModuleCat.of R M) :=
      ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)
    exact Module.Finite.equiv hzero.isoZero.toLinearEquiv.symm

/-- Helper for Lemma 15.83.6: the regular module over a commutative ring is perfect. -/
private theorem ring_module_isPerfect_aux (S : Type u) [CommRing S] :
    (ModuleCat.of S S).IsPerfect := by
  -- Proof comment: the regular module is finite projective, so a length-zero projective
  -- resolution already witnesses perfectness.
  refine
    (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
      (ModuleCat.of S S)).2 ?_
  refine ⟨0, ?_⟩
  rw [hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
  constructor
  · infer_instance
  · exact Module.Finite.self S

/-- Helper for Lemma 15.83.6: the principal ideal generated by a regular element is a perfect
module over the ambient ring. -/
private theorem span_singleton_ideal_isPerfect_of_isSMulRegular
    {S : Type u} [CommRing S] {a : S}
    (ha : IsSMulRegular S a) :
    (ModuleCat.of S (Ideal.span ({a} : Set S))).IsPerfect := by
  let μ : S →ₗ[S] Ideal.span ({a} : Set S) :=
    LinearMap.codRestrict (Ideal.span ({a} : Set S))
      (LinearMap.toSpanSingleton S S a) (fun r ↦ by
        change r * a ∈ Ideal.span ({a} : Set S)
        exact Ideal.mem_span_singleton.2 ⟨r, by simp [mul_comm]⟩)
  have hμ_inj : Function.Injective μ := by
    intro x y hxy
    apply ha
    -- Proof comment: forget the codomain restriction to recover the scalar-multiplication map.
    simpa [μ, LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using
      congrArg Subtype.val hxy
  have hμ_surj : Function.Surjective μ := by
    intro y
    rcases Ideal.mem_span_singleton.mp y.2 with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    -- Proof comment: every element of the principal ideal is literally one scalar multiple of
    -- the chosen generator.
    simpa [μ, LinearMap.toSpanSingleton_apply, mul_comm] using hr.symm
  let e : ModuleCat.of S S ≃ₗ[S] ModuleCat.of S (Ideal.span ({a} : Set S)) :=
    LinearEquiv.ofBijective μ ⟨hμ_inj, hμ_surj⟩
  let P : CategoryTheory.ObjectProperty (ModuleCat S) := fun X ↦ X.IsPerfect
  have hS : (ModuleCat.of S S).IsPerfect := by
    -- Proof comment: the regular module is finite projective, hence perfect in length `0`.
    refine
      (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of S S)).2 ?_
    refine ⟨0, ?_⟩
    rw [hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
    constructor
    · infer_instance
    · exact Module.Finite.self S
  exact P.prop_of_iso (moduleCat_iso_of_linearEquiv e).symm hS

/-- Helper for Lemma 15.83.6: the quotient by a principal regular element is a perfect module
over the ambient ring. -/
private theorem span_singleton_quotient_isPerfect_of_isSMulRegular
    {S : Type u} [CommRing S] {a : S}
    (ha : IsSMulRegular S a) :
    (ModuleCat.of S (S ⧸ Ideal.span ({a} : Set S))).IsPerfect := by
  let I : Ideal S := Ideal.span ({a} : Set S)
  letI : Module.Finite S I := Module.Finite.of_fg (Submodule.fg_span_singleton a)
  have hI : (ModuleCat.of S I).IsPerfect :=
    span_singleton_ideal_isPerfect_of_isSMulRegular (S := S) ha
  -- Proof comment: once the principal ideal itself is perfect, the standard quotient short exact
  -- sequence upgrades that to perfectness of the quotient.
  simpa [I] using idealQuotient_isPerfect_of_isPerfect_ideal (R := S) I hI

/-- Helper for Lemma 15.83.6: the ideal generated by a finite Koszul-regular sequence is a
perfect module over the ambient ring. -/
private theorem span_range_ideal_isPerfect_of_isKoszulRegularSequence
    {S : Type u} [CommRing S] {r : ℕ} {f : Fin r → S}
    (hf : RingTheory.Sequence.IsKoszulRegularSequence f) :
    (ModuleCat.of S (Ideal.span (Set.range f))).IsPerfect := by
  let I : Ideal S := Ideal.span (Set.range f)
  have hI : (ModuleCat.of S I).IsPerfect := by
    by_cases htop : I = ⊤
    · let Qprop : CategoryTheory.ObjectProperty (ModuleCat S) := fun M ↦ M.IsPerfect
      let eTop : I ≃ₗ[S] S :=
        (LinearEquiv.ofEq I ⊤ htop).trans Submodule.topEquiv
      -- Proof comment: if the generated ideal is already the whole ring, the ideal module is just
      -- the regular module.
      exact
        Qprop.prop_of_iso
          (moduleCat_iso_of_linearEquiv eTop)
          (ring_module_isPerfect_aux (S := S))
    · cases r with
      | zero =>
          have hbot : I = ⊥ := by
            -- Proof comment: the empty family spans the zero ideal.
            ext x
            simp [I]
          -- Proof comment: the zero ideal is a subsingleton module, hence perfect.
          simpa [hbot] using
            (isPerfect_of_subsingleton_module (R := S) (M := (⊥ : Ideal S)))
      | succ r' =>
          -- Route correction: the easy branches are now discharged explicitly. The remaining
          -- source-faithful blocker is exactly the proper positive-length case, where one needs
          -- the earlier-owner recursion bridge splitting a Koszul-regular `Fin.snoc` family into
          -- a Koszul-regular prefix and a regular last class on the prefix quotient.
          -- TODO(Lemma 15.83.6): combine the missing snoc-prefix bridge with the earlier
          -- quotient-tail theorem `RingTheory.Sequence.isKoszulRegularSequence_quotient_of_append`
          -- to prove quotient-perfectness by snoc induction, then recover ideal-perfectness from
          -- `0 → I → S → S / I → 0`.
          let _ := hf
          let _ : I ≠ ⊤ := htop
          sorry
  simpa [I] using hI

/-- Helper for Lemma 15.83.6: the regular module over any localization-away ring is perfect. -/
private theorem ring_module_isPerfect (S : Type u) [CommRing S] :
    (ModuleCat.of S S).IsPerfect := by
  -- Proof comment: reuse the earlier regular-module perfectness witness.
  exact ring_module_isPerfect_aux (S := S)

/-- Helper for Lemma 15.83.6: a localized Koszul witness makes the away-localized ideal module
perfect. -/
private theorem localizedAway_ideal_isPerfect_of_witness
    (I : Ideal R) (g : R) {r : ℕ} {f : Fin r → Localization.Away g}
    (hf : RingTheory.Sequence.IsKoszulRegularSequence f)
    (hspan :
      Ideal.map (algebraMap R (Localization.Away g)) I = Ideal.span (Set.range f)) :
    (ModuleCat.of (Localization.Away g) (LocalizedModule.Away g I)).IsPerfect := by
  let Rg := Localization.Away g
  let Qprop : CategoryTheory.ObjectProperty (ModuleCat Rg) := fun M ↦ M.IsPerfect
  have hSpan : (ModuleCat.of Rg (Ideal.span (Set.range f))).IsPerfect :=
    span_range_ideal_isPerfect_of_isKoszulRegularSequence (S := Rg) hf
  have hMap : (ModuleCat.of Rg (Ideal.map (algebraMap R Rg) I)).IsPerfect := by
    -- Proof comment: rewrite the mapped ideal by the chosen local generating witness.
    exact
      Qprop.prop_of_iso
        (moduleCat_iso_of_linearEquiv (LinearEquiv.ofEq _ _ hspan)).symm
        hSpan
  -- Proof comment: the canonical away-localized ideal model is linearly equivalent to the mapped
  -- ideal in the localized ring.
  exact
    Qprop.prop_of_iso
      (moduleCat_iso_of_linearEquiv
        (localizedAway_ideal_map_linearEquiv (R := R) I g)).symm
      hMap

/-- Helper for Lemma 15.83.6: after localizing away from an element of the ideal, the localized
ideal module becomes the regular localized ring module, hence is perfect. -/
private theorem localizedAway_ideal_isPerfect_of_mem
    (I : Ideal R) {x : R} (hx : x ∈ I) :
    (ModuleCat.of (Localization.Away x) (LocalizedModule.Away x I)).IsPerfect := by
  let Rx := Localization.Away x
  let Qprop : CategoryTheory.ObjectProperty (ModuleCat Rx) := fun M ↦ M.IsPerfect
  have hxmap : algebraMap R Rx x ∈ Ideal.map (algebraMap R Rx) I :=
    Ideal.mem_map_of_mem _ hx
  have htop : Ideal.map (algebraMap R Rx) I = ⊤ :=
    (Ideal.map (algebraMap R Rx) I).eq_top_of_isUnit_mem hxmap
      (IsLocalization.map_units Rx ⟨x, Submonoid.mem_powers x⟩)
  have hRing : (ModuleCat.of Rx Rx).IsPerfect :=
    ring_module_isPerfect (S := Rx)
  have hMap : (ModuleCat.of Rx (Ideal.map (algebraMap R Rx) I)).IsPerfect := by
    -- Proof comment: once the localized ideal is the whole ring, its module is the regular
    -- localized module.
    exact
      Qprop.prop_of_iso
        (moduleCat_iso_of_linearEquiv
          ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv)).symm
        hRing
  -- Proof comment: transport back from the mapped ideal model to the canonical localized ideal
  -- module.
  exact
    Qprop.prop_of_iso
      (moduleCat_iso_of_linearEquiv
        (localizedAway_ideal_map_linearEquiv (R := R) I x)).symm
      hMap

/-- Helper for Lemma 15.83.6: maximal-local away-perfect witnesses can be reduced to one finite
principal-open cover whose generators span the unit ideal. -/
private theorem exists_finite_unitIdeal_family_of_awayPerfect_of_maximal_witnesses
    {K : DerivedCategory (ModuleCat.{u} R)}
    (hmax :
      ∀ 𝔪 : MaximalSpectrum R,
        ∃ f : R, f ∉ 𝔪.asIdeal ∧
          (K ⊗[R]^L[Localization.Away f]).IsPerfect) :
    ∃ n : ℕ, ∃ g : Fin n → R,
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ j, (K ⊗[R]^L[Localization.Away (g j)]).IsPerfect := by
  classical
  let S : Set R := {f : R | (K ⊗[R]^L[Localization.Away f]).IsPerfect}
  have hspan : Ideal.span S = ⊤ := by
    -- Proof comment: otherwise a maximal ideal above `Ideal.span S` would contain every local
    -- witness, contradicting the chosen element outside that maximal ideal.
    by_contra hspan'
    obtain ⟨mIdeal, hmmax, hSm⟩ := Ideal.exists_le_maximal (Ideal.span S) hspan'
    let 𝔪 : MaximalSpectrum R := ⟨mIdeal, hmmax⟩
    rcases hmax 𝔪 with ⟨f, hfm, hfperfect⟩
    have hfmem : f ∈ Ideal.span S := Ideal.subset_span hfperfect
    exact hfm (hSm hfmem)
  obtain ⟨s, hsS, hsTop⟩ := (Ideal.span_eq_top_iff_finite S).mp hspan
  let t : Finset R := s
  let g : Fin t.card → R := fun i ↦ (t.equivFin.symm i : R)
  have hg_range : Set.range g = (↑t : Set R) := by
    -- Proof comment: reindex the finite spanning subset by a finite type so the localization
    -- descent theorem applies directly.
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (t.equivFin.symm i).2
    · intro hx
      exact ⟨t.equivFin ⟨x, hx⟩, by simp [g]⟩
  refine ⟨t.card, g, ?_, ?_⟩
  · simpa [hg_range] using hsTop
  · intro i
    exact (hsS (t.equivFin.symm i).2 :
      (K ⊗[R]^L[Localization.Away (g i)]).IsPerfect)

/-- Helper for Lemma 15.83.6: a Koszul-regular ideal is perfect as an `R`-module. -/
private theorem ideal_isPerfect_of_isKoszulRegularIdeal
    (I : Ideal R) (hI : I.IsKoszulRegularIdeal) :
    (ModuleCat.of R I).IsPerfect := by
  -- Route correction: the source proof first proves perfectness of the kernel ideal module `I`
  -- itself and only then passes to the quotient `R ⧸ I` through `0 → I → R → R / I → 0`.
  let K := ModuleCat.single0Functor.obj (ModuleCat.of R I)
  have hmax :
      ∀ 𝔪 : MaximalSpectrum R,
        ∃ g : R, g ∉ 𝔪.asIdeal ∧ (K ⊗[R]^L[Localization.Away g]).IsPerfect := by
    intro 𝔪
    by_cases hIm : I ≤ 𝔪.asIdeal
    · rcases (Ideal.isKoszulRegularIdeal_iff I).1 hI 𝔪.asIdeal 𝔪.2 hIm with
        ⟨g, hg, r, f, hf, hspan⟩
      have hLocal :
          (ModuleCat.of (Localization.Away g) (LocalizedModule.Away g I)).IsPerfect :=
        localizedAway_ideal_isPerfect_of_witness (R := R) I g hf hspan
      have hLocalSingle :
          (ModuleCat.single0Functor.obj
            (ModuleCat.of (Localization.Away g) (LocalizedModule.Away g I))).IsPerfect := by
        simpa [ModuleCat.IsPerfect, ModuleCat.single0Functor] using hLocal
      refine ⟨g, hg, ?_⟩
      -- Proof comment: convert module perfectness on the away localization to perfectness of the
      -- corresponding localized degree-zero derived object.
      exact
        CategoryTheory.ObjectProperty.prop_of_iso
          (P := CategoryTheory.PerfectObj)
          (CategoryTheory.single0_localizationAway_iso (R := R) g (ModuleCat.of R I)).symm
          hLocalSingle
    · have hIm' : ∃ x, x ∈ I ∧ x ∉ 𝔪.asIdeal := by
        simpa [SetLike.le_def] using hIm
      rcases hIm' with ⟨x, hxI, hxnot⟩
      have hLocal :
          (ModuleCat.of (Localization.Away x) (LocalizedModule.Away x I)).IsPerfect :=
        localizedAway_ideal_isPerfect_of_mem (R := R) I hxI
      have hLocalSingle :
          (ModuleCat.single0Functor.obj
            (ModuleCat.of (Localization.Away x) (LocalizedModule.Away x I))).IsPerfect := by
        simpa [ModuleCat.IsPerfect, ModuleCat.single0Functor] using hLocal
      refine ⟨x, hxnot, ?_⟩
      -- Proof comment: away from `V(I)`, the localized ideal is the whole localized ring, so the
      -- ideal module is trivially perfect.
      exact
        CategoryTheory.ObjectProperty.prop_of_iso
          (P := CategoryTheory.PerfectObj)
          (CategoryTheory.single0_localizationAway_iso (R := R) x (ModuleCat.of R I)).symm
          hLocalSingle
  rcases
      exists_finite_unitIdeal_family_of_awayPerfect_of_maximal_witnesses
        (K := K) hmax with
    ⟨n, g, hunit, hgperfect⟩
  have hK : K.IsPerfect := by
    -- Proof comment: the finite principal-open cover already produced above is exactly the input
    -- expected by the earlier owner theorem descending perfectness from away-localizations.
    exact
      CategoryTheory.isPerfect_of_localizationAway_unitIdeal
        (R := R) g hunit K hgperfect
  -- Proof comment: unfold the fixed degree-zero derived model `K` back to the module owner
  -- `ModuleCat.IsPerfect`.
  simpa [K, ModuleCat.IsPerfect, ModuleCat.single0Functor] using hK

/-- Helper for Lemma 15.83.6: a Koszul-regular ideal has perfect quotient module. -/
private theorem ideal_quotient_isPerfect_of_isKoszulRegularIdeal
    (I : Ideal R) (hI : I.IsKoszulRegularIdeal) :
    (ModuleCat.of R (R ⧸ I)).IsPerfect := by
  letI : Module.Finite R I :=
    Module.Finite.of_fg (RingHom.fg_of_isKoszulRegularIdeal hI)
  have hIdeal : (ModuleCat.of R I).IsPerfect :=
    ideal_isPerfect_of_isKoszulRegularIdeal (R := R) I hI
  -- Proof comment: once the kernel ideal itself is perfect, the standard quotient short exact
  -- sequence upgrades that ideal-perfectness to perfectness of `R ⧸ I`.
  exact idealQuotient_isPerfect_of_isPerfect_ideal (R := R) I hIdeal

end Auxiliary

-- Route correction: the main proof already follows the source presentation route. The remaining
-- blocker is exactly the source local-global step turning a Koszul-regular kernel ideal into a
-- perfect quotient module over the polynomial presentation ring.
/-- Helper for Lemma 15.83.6: the quotient by the presentation kernel is canonically the target
algebra, viewed as a module over the presentation ring. -/
private noncomputable def presentation_quotient_module_iso
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B P.toAlgHom.toRingHom
    ModuleCat.of P.Ring (P.Ring ⧸ P.ker) ≅ ModuleCat.of P.Ring B :=
  moduleCat_iso_of_linearEquiv
    ((Ideal.quotientKerAlgEquivOfSurjective
      (R₁ := A) (f := P.toAlgHom) P.algebraMap_surjective).toLinearEquiv)

/-- Helper for Lemma 15.83.6: a polynomial presentation whose kernel ideal is Koszul-regular
should make the restricted target module perfect over the presentation ring. -/
private theorem presentation_restrictedModule_isPerfect_of_isKoszulRegularIdeal
    {n : ℕ} (P : Algebra.Generators A B (Fin n))
    (hker : P.ker.IsKoszulRegularIdeal) :
    let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B P.toAlgHom.toRingHom
    (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect := by
  let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B P.toAlgHom.toRingHom
  have hquot : (ModuleCat.of P.Ring (P.Ring ⧸ P.ker)).IsPerfect :=
    ideal_quotient_isPerfect_of_isKoszulRegularIdeal (R := P.Ring) P.ker hker
  let Qprop : CategoryTheory.ObjectProperty (ModuleCat P.Ring) := fun M ↦ M.IsPerfect
  -- Proof comment: the source-faithful route now isolates all remaining work in the kernel-ideal
  -- perfectness step. Once the quotient `P.Ring ⧸ P.ker` is known perfect, the canonical quotient
  -- equivalence transports that perfectness directly to the restricted target module `B`.
  simpa using
    Qprop.prop_of_iso
      (presentation_quotient_module_iso (A := A) (B := B) P)
      hquot

/- Domain-style sampling for Lemma 15.83.6:
- primary domain: commutative algebra of local complete intersection and perfect ring maps;
- sampled owner declarations:
  `RingHom.IsLocalCompleteIntersection`,
  `RingHom.IsPerfectRingMap`,
  `RingHom.IsPseudoCoherentRingMap`,
  `Algebra.isPerfectRingMap_of_flat_of_finitePresentation`;
- best owner abstraction: both the source hypothesis and the target conclusion live on the
  canonical ring-map owners `RingHom.IsLocalCompleteIntersection` and
  `RingHom.IsPerfectRingMap` for `algebraMap A B`; a polynomial presentation from Definition
  `15.33.2` is bridge data only and should not appear in the public API here;
- primitive vs. derived:
  the primitive public datum is only the owner hypothesis
  `[RingHom.IsLocalCompleteIntersection (algebraMap A B)]`;
  the derived API is the perfectness instance and its downstream pseudo-coherence and finite Tor
  dimension consequences.

Source/core/bridge triage:
- `source-facing`: the implication below that a local complete intersection ring map is perfect;
- `core/canonical`: `RingHom.IsLocalCompleteIntersection` and `RingHom.IsPerfectRingMap`;
- `bridge/view`: any chosen finite polynomial presentation witnessing the local complete
  intersection condition, used only in the proof.
-/

-- Proof sketch: apply Definition `15.33.2` to choose a finite polynomial presentation
-- `A[x₁, …, xₙ] ↠ B` whose kernel ideal is Koszul-regular. By Lemma `15.83.2`, it is enough to
-- show that `B` is a perfect module over the polynomial ring. Lemma `15.75.12` reduces this to a
-- local statement on the source polynomial ring, where Definition `15.32.1` lets one replace the
-- kernel ideal by a Koszul-regular generating sequence. Such a sequence gives a finite free, hence
-- finite projective, resolution of the quotient module, so Lemma `15.75.3` yields perfection.
/-- Lemma 15.83.6: a local complete intersection ring map is perfect. -/
instance isPerfectRingMap_of_isLocalCompleteIntersection :
    (algebraMap A B).IsPerfectRingMap := by
  rcases
      (inferInstance : RingHom.IsLocalCompleteIntersection (algebraMap A B))
        .exists_generators_ker_isKoszulRegular with
    ⟨n, P, hker⟩
  -- Proof comment: choose the source-faithful polynomial presentation from the local complete
  -- intersection hypothesis and invoke the perfect-ring-map criterion for polynomial presentations.
  refine
    (isPerfectRingMap_iff_exists_polynomialPresentation_with_perfect_restrictedModule
      (A := A) (B := B)).2 ?_
  refine ⟨n, P.toAlgHom, P.algebraMap_surjective, ?_⟩
  -- Proof comment: the only remaining work is the presentation-side perfectness statement for the
  -- quotient by a Koszul-regular kernel ideal.
  simpa using
    presentation_restrictedModule_isPerfect_of_isKoszulRegularIdeal
      (A := A) (B := B) P hker

end

end Algebra
