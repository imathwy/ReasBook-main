import Mathlib
import StacksProject_2024.Chap10.Definition_10_109_2
import StacksProject_2024.Chap10.Lemma_10_109_6
import StacksProject_2024.Chap10.Lemma_10_72_11
import StacksProject_2024.Chap10.Lemma_10_72_4
import StacksProject_2024.Chap10.Proposition_10_111_1
import StacksProject_2024.Chap15.Lemma_15_75_3
import StacksProject_2024.Chap15.Lemma_15_75_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {E : Type u} [AddCommGroup E] [Module (R ⧸ I) E] [Module.Finite (R ⧸ I) E]

/-- Helper for Lemma 15.103.4: the quotient ring carries its canonical `R`-algebra structure. -/
private instance quotient_algebra : Algebra R (R ⧸ I) :=
  Ideal.Quotient.algebra R

/-
Domain-style sampling:
* primary domain: projective dimension and the Auslander--Buchsbaum formula for finite modules over
  Noetherian local rings, together with restriction of scalars along a quotient map;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `projectiveDimension_le_iff`,
  `projectiveDimension_eq_bot_iff`,
  `ringDepth_eq_projectiveDimension_add_moduleDepth`,
  `ModuleCat.restrictScalars`,
  `ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms`;
* source/core/bridge triage:
  `source-facing`: the additive change-of-rings formula for a finite `(R ⧸ I)`-module;
  `core/canonical`: `projectiveDimension` on `ModuleCat` objects and `moduleDepth`;
  `bridge/view`: the categorical restriction functor `ModuleCat.restrictScalars
    (Ideal.Quotient.mk I)`, used directly through the canonical object
    `((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E))`;
* primitive data: the canonical module-category objects `ModuleCat.of R (R ⧸ I)`,
  `ModuleCat.of (R ⧸ I) E`, and the restricted object
  `((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E))`;
* derived API: the hypotheses `projectiveDimension _ ≠ ⊤`, the zero-module fallback via
  `projectiveDimension_eq_bot_iff`, and the resulting additive equality.
-/

/-- Helper for Lemma 15.103.4: restriction of scalars along an algebra map preserves the
underlying module object up to the canonical identity linear equivalence. -/
private noncomputable abbrev restrictOfIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type u} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M) ≅ ModuleCat.of A M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) ≃ₗ[A] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

/-- Helper for Lemma 15.103.4: restriction of scalars commutes with the degree-zero embedding of a
module into the derived category. -/
private noncomputable def restrictScalars_single0_iso
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat B) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj M) :=
  -- Compute derived restriction on a single complex through the exact cochain-level restriction.
  ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app M) ≪≫
    (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars (algebraMap A B))
          (0 : ℤ)).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M)).symm

/-- Helper for Lemma 15.103.4: finite projective dimension implies perfectness for a finite
module. -/
private lemma module_isPerfect_of_projectiveDimension_ne_top
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : projectiveDimension (ModuleCat.of A M) ≠ ⊤) :
    (ModuleCat.of A M).IsPerfect := by
  -- Translate the finite projective dimension hypothesis into a bounded finite projective
  -- resolution and then invoke the perfectness criterion.
  rcases (projectiveDimension_ne_top_iff (ModuleCat.of A M)).1 hM with ⟨d, hd⟩
  exact
    (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
      (ModuleCat.of A M)).2
      ⟨d, (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (R := A) (M := M) d).1 hd⟩

/-- Helper for Lemma 15.103.4: perfectness gives finite projective dimension for a finite
module. -/
private lemma projectiveDimension_ne_top_of_isPerfect_finite
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : (ModuleCat.of A M).IsPerfect) :
    projectiveDimension (ModuleCat.of A M) ≠ ⊤ := by
  -- Convert the perfect module back to a finite projective resolution of some bounded length.
  rcases
      (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of A M)).1 hM with
    ⟨d, hd⟩
  exact
    (projectiveDimension_ne_top_iff (ModuleCat.of A M)).2
      ⟨d, (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (R := A) (M := M) d).2 hd⟩

/-- Helper for Lemma 15.103.4: a finite module over the quotient ring has the same depth over `R`
as over `R ⧸ I`. -/
private lemma idealQuotient_moduleDepth_eq
    {N : Type u} [AddCommGroup N] [Module (R ⧸ I) N] [Module.Finite (R ⧸ I) N]
    [Nontrivial (R ⧸ I)] :
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    letI : Module R N := Module.compHom N (Ideal.Quotient.mk I)
    letI : IsScalarTower R (R ⧸ I) N :=
      { smul_assoc := fun r a n ↦ by
          change ((Ideal.Quotient.mk I r * a) • n) = (Ideal.Quotient.mk I r) • (a • n)
          rw [mul_smul] }
    letI : Module.Finite R N := Module.Finite.trans (R ⧸ I) N
    moduleDepth R N = moduleDepth (R ⧸ I) N := by
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : Module R N := Module.compHom N (Ideal.Quotient.mk I)
  letI : IsScalarTower R (R ⧸ I) N :=
    { smul_assoc := fun r a n ↦ by
        change ((Ideal.Quotient.mk I r * a) • n) = (Ideal.Quotient.mk I r) • (a • n)
        rw [mul_smul] }
  letI : Module.Finite R (R ⧸ I) := by infer_instance
  letI : Module.Finite R N := Module.Finite.trans (R ⧸ I) N
  have hR :
      (⨅ m : MaximalSpectrum (R ⧸ I),
        moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N)) =
        moduleDepth R N :=
    depth_eq_sInf_depth_localizedModule_at_maximalIdeals_of_finite
      (R := R) (S := R ⧸ I) (N := N)
  have hQuot :
      (⨅ m : MaximalSpectrum (R ⧸ I),
        moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N)) =
        moduleDepth (R ⧸ I) N :=
    depth_eq_sInf_depth_localizedModule_at_maximalIdeals_of_finite
      (R := R ⧸ I) (S := R ⧸ I) (N := N)
  -- Both depths are identified with the same infimum of localized depths.
  exact hR.symm.trans hQuot

/-- Helper for Lemma 15.103.4: a nontrivial module object cannot have projective dimension
`⊥`. -/
private lemma projectiveDimension_ne_bot_of_nontrivial_module
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Nontrivial M] :
    projectiveDimension (ModuleCat.of A M) ≠ ⊥ := by
  -- Bottom projective dimension would make the module object zero, hence its carrier
  -- subsingleton.
  intro hbot
  have hzero : Limits.IsZero (ModuleCat.of A M) :=
    (projectiveDimension_eq_bot_iff (ModuleCat.of A M)).1 hbot
  have hsub : Subsingleton M := by
    refine ⟨fun x y ↦ ?_⟩
    have hid0 : (𝟙 (ModuleCat.of A M)) = 0 :=
      (Limits.IsZero.iff_id_eq_zero (ModuleCat.of A M)).1 hzero
    have hxy : ((𝟙 (ModuleCat.of A M)) : ModuleCat.of A M ⟶ ModuleCat.of A M) (x - y) = 0 := by
      have := congrArg (fun f : ModuleCat.of A M ⟶ ModuleCat.of A M => f (x - y)) hid0
      simpa using this
    exact sub_eq_zero.mp (by simpa using hxy)
  exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance

/-- Helper for Lemma 15.103.4: a nontrivial module over a commutative ring forces the ring to be
nontrivial. -/
private lemma nontrivial_ring_of_nontrivial_module
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Nontrivial M] :
    Nontrivial A := by
  -- If `0 = 1` in the ring, then `0 • x = 1 • x` forces every element of the module to vanish.
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  refine ⟨0, 1, ?_⟩
  intro h01
  apply hx
  calc
    x = (1 : A) • x := by symm; exact one_smul A x
    _ = (0 : A) • x := by rw [h01]
    _ = 0 := zero_smul A x

/-- Helper for Lemma 15.103.4: once a projective dimension is neither `⊥` nor `⊤`, it equals a
natural number. -/
private lemma projectiveDimension_eq_nat_of_ne_bot_ne_top
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (hbot : projectiveDimension (ModuleCat.of A M) ≠ ⊥)
    (htop : projectiveDimension (ModuleCat.of A M) ≠ ⊤) :
    ∃ n : ℕ, projectiveDimension (ModuleCat.of A M) = n := by
  -- First exclude the outer `⊥`, then exclude the inner `⊤ : ℕ∞`.
  rcases WithBot.ne_bot_iff_exists.mp hbot with ⟨d, hd⟩
  have hd_top : d ≠ ⊤ := by
    intro hd'
    apply htop
    rw [← hd, WithBot.coe_eq_top]
    exact hd'
  rcases ENat.ne_top_iff_exists.mp hd_top with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  calc
    projectiveDimension (ModuleCat.of A M) = (d : WithBot ℕ∞) := hd.symm
    _ = n := by
      simpa using congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) hn.symm

-- Proof sketch: reinterpret finite projective dimension as perfectness for finite modules, use the
-- finiteness of `R ⧸ I` over `R` together with the perfectness of `E` over `R ⧸ I`, and then apply
-- the change-of-rings result from the perfect derived category to conclude that `E` is perfect,
-- hence has finite projective dimension over `R` after viewing `E` as an `R`-module by
-- restriction of scalars along `Ideal.Quotient.mk I`.
/- Internal finiteness step used in the additive formula below. -/
theorem projectiveDimension_ne_top_of_idealQuotient_module
    (hRQuot : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hEQuot : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) ≠
      ⊤ := by
  letI : Module R E := Module.compHom E (Ideal.Quotient.mk I)
  letI : IsScalarTower R (R ⧸ I) E :=
    { smul_assoc := fun r a e ↦ by
        change ((Ideal.Quotient.mk I r * a) • e) = (Ideal.Quotient.mk I r) • (a • e)
        rw [mul_smul] }
  letI : Module.Finite R (R ⧸ I) := by infer_instance
  letI : Module.Finite R E := Module.Finite.trans (R ⧸ I) E
  have hRQuotPerfect : (ModuleCat.of R (R ⧸ I)).IsPerfect :=
    module_isPerfect_of_projectiveDimension_ne_top
      (A := R) (M := R ⧸ I) hRQuot
  have hEPerfect : (ModuleCat.of (R ⧸ I) E).IsPerfect :=
    module_isPerfect_of_projectiveDimension_ne_top
      (A := R ⧸ I) (M := E) hEQuot
  have hRestrictedDerived :
      (((ModuleCat.restrictScalars (algebraMap R (R ⧸ I))).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat (R ⧸ I)) (0 : ℤ)).obj
          (ModuleCat.of (R ⧸ I) E)) : DerivedCategory (ModuleCat R))).IsPerfect := by
    -- Apply the derived restriction-of-scalars perfectness theorem to the degree-zero object of
    -- `E`.
    simpa [ModuleCat.IsPerfect] using
      CategoryTheory.isPerfect_restrictScalars_of_module_isPerfect
        (((DerivedCategory.singleFunctor (ModuleCat (R ⧸ I)) (0 : ℤ)).obj
          (ModuleCat.of (R ⧸ I) E)))
        hRQuotPerfect hEPerfect
  let P : CategoryTheory.ObjectProperty (DerivedCategory (ModuleCat R)) :=
    fun K ↦ DerivedCategory.IsPerfect K
  have hRestrictedModulePerfect : (ModuleCat.of R E).IsPerfect := by
    -- Transport the derived perfectness statement to the canonical degree-zero object of the
    -- underlying `R`-module.
    have hsingle :
        P ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj (ModuleCat.of R E)) :=
      P.prop_of_iso
        ((restrictScalars_single0_iso (A := R) (B := R ⧸ I) (ModuleCat.of (R ⧸ I) E)) ≪≫
          (Functor.mapIso
            (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ))
            (restrictOfIso (A := R) (B := R ⧸ I) (M := E))))
        hRestrictedDerived
    simpa [ModuleCat.IsPerfect] using hsingle
  have hEOverR :
      projectiveDimension (ModuleCat.of R E) ≠ ⊤ :=
    projectiveDimension_ne_top_of_isPerfect_finite
      (A := R) (M := E) hRestrictedModulePerfect
  -- Rewrite the plain `R`-module statement back to the restricted object appearing in the target.
  simpa [projectiveDimension_eq_of_iso (restrictOfIso (A := R) (B := R ⧸ I) (M := E))] using
    hEOverR

-- Proof sketch: first use the companion theorem to know that `E` has finite projective dimension
-- over `R`. Then apply Auslander--Buchsbaum to `E` over `R`, to `E` over `R ⧸ I`, and to the
-- quotient ring `R ⧸ I` over `R`; finally use that the depth of `E` computed over `R` agrees with
-- the depth computed over `R ⧸ I` to eliminate the depth terms and obtain the stated sum formula;
-- when `E = 0`, both projective dimensions of `E` are `⊥`, so the identity reduces to the
-- canonical `WithBot` arithmetic.
/-- Lemma 15.103.4: for a finite `(R ⧸ I)`-module `E` over a Noetherian local ring `R`, if `R ⧸ I`
has finite projective dimension as an `R`-module and `E` has finite projective dimension as an
`(R ⧸ I)`-module, then the projective dimension of the restricted `R`-module
`RestrictScalars R (R ⧸ I) E` is the sum of the projective dimension of `R ⧸ I` over `R` and the
projective dimension of `E` over `R ⧸ I`. -/
theorem projectiveDimension_idealQuotient_module_eq_add
    (hRQuot : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hEQuot : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) =
      projectiveDimension (ModuleCat.of R (R ⧸ I)) +
        projectiveDimension (ModuleCat.of (R ⧸ I) E) := by
  letI : Module R E := Module.compHom E (Ideal.Quotient.mk I)
  letI : IsScalarTower R (R ⧸ I) E :=
    { smul_assoc := fun r a e ↦ by
        change ((Ideal.Quotient.mk I r * a) • e) = (Ideal.Quotient.mk I r) • (a • e)
        rw [mul_smul] }
  letI : Module.Finite R (R ⧸ I) := by infer_instance
  letI : Module.Finite R E := Module.Finite.trans (R ⧸ I) E
  have hEOverRTop :
      projectiveDimension (ModuleCat.of R E) ≠ ⊤ := by
    -- First obtain finite projective dimension after restricting scalars.
    have hrestrict :=
      projectiveDimension_ne_top_of_idealQuotient_module
        (R := R) (I := I) (E := E) hRQuot hEQuot
    simpa [projectiveDimension_eq_of_iso (restrictOfIso (A := R) (B := R ⧸ I) (M := E))] using
      hrestrict
  by_cases hEsub : Subsingleton E
  · letI : Subsingleton E := hEsub
    have hEQuotBot : projectiveDimension (ModuleCat.of (R ⧸ I) E) = ⊥ := by
      -- A subsingleton module is the zero object in `ModuleCat (R ⧸ I)`.
      apply (projectiveDimension_eq_bot_iff (ModuleCat.of (R ⧸ I) E)).2
      rw [Limits.IsZero.iff_id_eq_zero]
      ext x
      exact Subsingleton.elim _ _
    have hERBot : projectiveDimension (ModuleCat.of R E) = ⊥ := by
      -- The same carrier remains zero after restricting scalars to `R`.
      apply (projectiveDimension_eq_bot_iff (ModuleCat.of R E)).2
      rw [Limits.IsZero.iff_id_eq_zero]
      ext x
      exact Subsingleton.elim _ _
    calc
      projectiveDimension
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) =
        projectiveDimension (ModuleCat.of R E) :=
          projectiveDimension_eq_of_iso (restrictOfIso (A := R) (B := R ⧸ I) (M := E))
      _ = ⊥ := hERBot
      _ =
          projectiveDimension (ModuleCat.of R (R ⧸ I)) +
            projectiveDimension (ModuleCat.of (R ⧸ I) E) := by
          rw [hEQuotBot]
          simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hEsub
    letI : Nontrivial (R ⧸ I) := nontrivial_ring_of_nontrivial_module
      (A := R ⧸ I) (M := E)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hRQuotBot :
        projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊥ :=
      projectiveDimension_ne_bot_of_nontrivial_module
        (A := R) (M := R ⧸ I)
    have hEQuotBot :
        projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊥ :=
      projectiveDimension_ne_bot_of_nontrivial_module
        (A := R ⧸ I) (M := E)
    have hERBot :
        projectiveDimension (ModuleCat.of R E) ≠ ⊥ :=
      projectiveDimension_ne_bot_of_nontrivial_module
        (A := R) (M := E)
    rcases projectiveDimension_eq_nat_of_ne_bot_ne_top
        (A := R) (M := R ⧸ I) hRQuotBot hRQuot with ⟨a, ha⟩
    rcases projectiveDimension_eq_nat_of_ne_bot_ne_top
        (A := R ⧸ I) (M := E) hEQuotBot hEQuot with ⟨b, hb⟩
    rcases projectiveDimension_eq_nat_of_ne_bot_ne_top
        (A := R) (M := E) hERBot hEOverRTop with ⟨c, hc⟩
    have hERDepth : moduleDepth R R = c + moduleDepth R E :=
      ringDepth_eq_projectiveDimension_add_moduleDepth (R := R) (M := E) hc
    have hEQuotDepth :
        moduleDepth (R ⧸ I) (R ⧸ I) = b + moduleDepth (R ⧸ I) E :=
      ringDepth_eq_projectiveDimension_add_moduleDepth (R := R ⧸ I) (M := E) hb
    have hRQuotDepth : moduleDepth R R = a + moduleDepth R (R ⧸ I) :=
      ringDepth_eq_projectiveDimension_add_moduleDepth (R := R) (M := R ⧸ I) ha
    have hDepthE : moduleDepth R E = moduleDepth (R ⧸ I) E :=
      idealQuotient_moduleDepth_eq (R := R) (I := I) (N := E)
    have hDepthQuot : moduleDepth R (R ⧸ I) = moduleDepth (R ⧸ I) (R ⧸ I) :=
      idealQuotient_moduleDepth_eq (R := R) (I := I) (N := R ⧸ I)
    have hERDepth' : moduleDepth R R = c + moduleDepth (R ⧸ I) E := by
      simpa [hDepthE] using hERDepth
    have hRQuotDepth' : moduleDepth R R = a + moduleDepth (R ⧸ I) (R ⧸ I) := by
      simpa [hDepthQuot] using hRQuotDepth
    have hnat : c = a + b := by
      have hsmulE :
          maximalIdeal (R ⧸ I) • (⊤ : Submodule (R ⧸ I) E) ≠ ⊤ := by
        simpa [ne_comm] using
          (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
            (maximalIdeal_le_jacobson (Module.annihilator (R ⧸ I) E)))
      have hDepthENeTop : moduleDepth (R ⧸ I) E ≠ ⊤ := by
        change Ideal.depth (maximalIdeal (R ⧸ I)) E ≠ ⊤
        exact (Ideal.depth_lt_top_of_smul_top_ne_top
          (R := R ⧸ I) (M := E) (maximalIdeal (R ⧸ I)) hsmulE).ne
      have hsumNat_left_ne_top : ((b : ℕ∞) + moduleDepth (R ⧸ I) E) ≠ ⊤ := by
        intro htop
        rcases WithTop.add_eq_top.mp htop with hbTop | hdTop
        · exact ENat.coe_ne_top b hbTop
        · exact hDepthENeTop hdTop
      have hsumNat_right_ne_top : ((c : ℕ∞) + moduleDepth (R ⧸ I) E) ≠ ⊤ := by
        intro htop
        rcases WithTop.add_eq_top.mp htop with hcTop | hdTop
        · exact ENat.coe_ne_top c hcTop
        · exact hDepthENeTop hdTop
      -- Compare the two expressions for `moduleDepth R R` and pass to `Nat` via `toNat`.
      have hsum : a + (b + moduleDepth (R ⧸ I) E) = c + moduleDepth (R ⧸ I) E := by
        calc
          a + (b + moduleDepth (R ⧸ I) E) =
              a + moduleDepth (R ⧸ I) (R ⧸ I) := by rw [hEQuotDepth]
          _ = moduleDepth R R := hRQuotDepth'.symm
          _ = c + moduleDepth (R ⧸ I) E := hERDepth'
      have hsumNat : a + (b + (moduleDepth (R ⧸ I) E).toNat) =
          c + (moduleDepth (R ⧸ I) E).toNat := by
        simpa [ENat.toNat_add, hDepthENeTop, hsumNat_left_ne_top, hsumNat_right_ne_top] using
          congrArg ENat.toNat hsum
      have hsumNat' : a + b + (moduleDepth (R ⧸ I) E).toNat =
          c + (moduleDepth (R ⧸ I) E).toNat := by
        simpa [Nat.add_assoc] using hsumNat
      exact (Nat.add_right_cancel hsumNat').symm
    have hnat' : (c : WithBot ℕ∞) = a + b := by
      simpa using congrArg (fun n : ℕ ↦ ((n : ℕ∞) : WithBot ℕ∞)) hnat
    calc
      projectiveDimension
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) =
        projectiveDimension (ModuleCat.of R E) :=
          projectiveDimension_eq_of_iso (restrictOfIso (A := R) (B := R ⧸ I) (M := E))
      _ = c := hc
      _ = a + b := hnat'
      _ =
          projectiveDimension (ModuleCat.of R (R ⧸ I)) +
            projectiveDimension (ModuleCat.of (R ⧸ I) E) := by
          rw [ha, hb]

end
