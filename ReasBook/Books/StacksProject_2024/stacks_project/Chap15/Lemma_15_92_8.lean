import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_8
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_3_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_92_6
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

open scoped PrincipalIdeal

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling:
- primary domain: pseudo-coherent objects in `D(A)` and the chapter owner predicate
  `K.IsDerivedCompleteWithRespectTo I`;
- sampled owner-side declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete`,
  `derivedCompleteObjectProperty_isWeakSerreClass`,
  `isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`;
- best owner abstraction: the source-facing statements below should stay on the canonical owner
  `K.IsDerivedCompleteWithRespectTo I`, with module-level adic completeness entering only through
  the bridge theorem from Lemma `15.92.3`;
- primitive data: the ideal `I`, the derived object `K`, and the ring object
  `ModuleCat.of A A`;
- derived API: the weak-Serre owner on derived-complete modules and the cohomology-in-property
  reformulation from Lemma `15.92.6`.

Layer triage:
- `source-facing`: Lemma `15.92.8` itself;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete` and
  `isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`. -/

-- Proof sketch: a pseudo-coherent object of `D(A)` is represented by a bounded-above finite-free
-- complex, so every cohomology module is a subquotient of finite free `A`-modules and hence is
-- pseudo-coherent as an `A`-module. Since `A`, viewed as an `A`-module, is derived complete,
-- pseudo-coherent modules are derived complete by the weak Serre property from Lemma `15.92.6`;
-- apply the cohomological criterion there to conclude that `K` itself is derived complete.
/-- Helper for Lemma 15.92.8: the free rank-`n + 1` module splits as one copy of `A` plus a free
rank-`n` summand. -/
private noncomputable def finSuccArrowLinearEquiv (n : ℕ) :
    (Fin (n + 1) → A) ≃ₗ[A] (A × (Fin n → A)) where
  toEquiv := (Fin.consEquiv fun _ : Fin (n + 1) => A).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper for Lemma 15.92.8: the owner quotient object `leftHomology` of `E.sc i` agrees with
the usual cochain homology of `E` in degree `i`. -/
private noncomputable abbrev sc_leftHomology_iso_homology
    {E : CochainComplex (ModuleCat A) ℤ} (i : ℤ) :
    (E.sc i).leftHomology ≅ E.homology i :=
  (E.sc i).moduleCatLeftHomologyData.leftHomologyIso ≪≫ ((E.sc i).moduleCatHomologyIso).symm

/-- Helper for Lemma 15.92.8: derived homology of a cochain complex is computed by ordinary
cochain homology on that representative. -/
private noncomputable abbrev derived_homology_iso
    (E : CochainComplex (ModuleCat A) ℤ) (i : ℤ) :
    (H i).obj (DerivedCategory.Q.obj E) ≅ E.homology i :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app E

/-- Helper for Lemma 15.92.8: a principal recursive sequence propagates to all higher powers of
the generator. -/
private theorem principal_recursive_sequence_shift
    {M : ModuleCat A} (f : A) (y : ℕ → M)
    (hy : ∀ n : ℕ, y n = f • y (n + 1)) :
    ∀ n m : ℕ, y n = (f ^ m) • y (n + m) := by
  intro n m
  induction m generalizing n with
  | zero =>
      simp
  | succ m ihm =>
      calc
        y n = f • y (n + 1) := hy n
        _ = f • ((f ^ m) • y (n + 1 + m)) := by rw [ihm (n + 1)]
        _ = (f ^ (m + 1)) • y (n + (m + 1)) := by
            rw [smul_smul]
            simp [pow_succ', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Lemma 15.92.8: derived completeness in `D(A)` is stable under the shift by `1`.
-/
private theorem isDerivedCompleteWithRespectTo_shift_local
    {K : DMod} (hK : K.IsDerivedCompleteWithRespectTo I) :
    K⟦(1 : ℤ)⟧.IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  let F :
      DerivedCategory (ModuleCat (Localization.Away f)) ⥤ DMod :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let hsub : Subsingleton (F.obj (E⟦(-1 : ℤ)⟧) ⟶ K) := hK f hf (E⟦(-1 : ℤ)⟧)
  let eK : ((K⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧) ≅ K :=
    (shiftFunctorCompIsoId DMod (1 : ℤ) (-1 : ℤ) (by simp)).app K
  refine ⟨fun u v ↦ ?_⟩
  let u' : F.obj (E⟦(-1 : ℤ)⟧) ⟶ K :=
    ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ u⟦(-1 : ℤ)⟧' ≫ eK.hom
  let v' : F.obj (E⟦(-1 : ℤ)⟧) ⟶ K :=
    ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ v⟦(-1 : ℤ)⟧' ≫ eK.hom
  have hu'v' : u' = v' := hsub.elim _ _
  have huv :
      ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ u⟦(-1 : ℤ)⟧' ≫ eK.hom =
        ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ v⟦(-1 : ℤ)⟧' ≫ eK.hom := by
    simpa [u', v'] using hu'v'
  have hshift :
      u⟦(-1 : ℤ)⟧' = v⟦(-1 : ℤ)⟧' := by
    apply (cancel_epi ((F.commShiftIso (-1 : ℤ)).hom.app E)).1
    exact (cancel_mono eK.hom).1 huv
  exact (shiftFunctor DMod (-1 : ℤ)).map_injective hshift

/-- Helper for Lemma 15.92.8: the kernel of a morphism from a derived-complete module is again
derived complete. -/
private theorem isDerivedCompleteWithRespectTo_kernel_local
    {M N : ModuleCat A} (u : M ⟶ N)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    (kernel u).IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  let E' :
      DerivedCategory (ModuleCat A) :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  let single₀ : ModuleCat A ⥤ DerivedCategory (ModuleCat A) := ModuleCat.single0Functor
  have hsubM : Subsingleton (E' ⟶ single₀.obj M) := hM f hf E
  refine ⟨fun x y ↦ ?_⟩
  apply (cancel_mono (single₀.map (kernel.ι u))).1
  exact hsubM.elim _ _

/-- Helper for Lemma 15.92.8: the cokernel of a monomorphism between derived-complete modules is
again derived complete. -/
private theorem isDerivedCompleteWithRespectTo_cokernel_of_mono_local
    {M N : ModuleCat A} (u : M ⟶ N) [Mono u]
    (hM : M.IsDerivedCompleteWithRespectTo I)
    (hN : N.IsDerivedCompleteWithRespectTo I) :
    (cokernel u).IsDerivedCompleteWithRespectTo I := by
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hS : S.ShortExact := by
    exact ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel u)) inferInstance inferInstance
  let T : Triangle (DerivedCategory (ModuleCat A)) := hS.singleTriangle
  have hsubObj₂ :
      ∀ f ∈ I, ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
        Subsingleton
          (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
            T.obj₂) := by
    intro f hf E
    simpa [T, S] using hN f hf E
  have hsubShiftObj₁ :
      ∀ f ∈ I, ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
        Subsingleton
          (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
            T.obj₁⟦(1 : ℤ)⟧) := by
    intro f hf E
    simpa [T, S] using
      (isDerivedCompleteWithRespectTo_shift_local (A := A) (I := I)
        (K := (ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj M)
        (by simpa [ModuleCat.IsDerivedCompleteWithRespectTo] using hM)) f hf E
  intro f hf E
  let E' :
      DerivedCategory (ModuleCat A) :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  have hsub₂ : Subsingleton (E' ⟶ T.obj₂) := hsubObj₂ f hf E
  have hsub₁shift : Subsingleton (E' ⟶ T.obj₁⟦(1 : ℤ)⟧) := hsubShiftObj₁ f hf E
  refine ⟨fun x y ↦ ?_⟩
  have hxy_zero : (x - y) ≫ T.mor₃ = 0 := by
    have hxy : x ≫ T.mor₃ = y ≫ T.mor₃ := hsub₁shift.elim _ _
    rw [sub_comp, hxy, sub_self]
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₃ (T := T) hS.singleTriangle_distinguished (x - y) hxy_zero
  have hz_zero : z = 0 := hsub₂.elim _ _
  apply sub_eq_zero.mp
  calc
    x - y = z ≫ T.mor₂ := hz
    _ = 0 := by simpa [hz_zero]

/-- Helper for Lemma 15.92.8: in a principal-adically complete module, every principal recursive
sequence is zero. -/
private theorem principal_recursive_sequence_eq_zero_of_isAdicComplete
    {M : ModuleCat A} (f : A) (hcomplete : IsAdicComplete ((f) : Ideal A) M)
    (y : ℕ → M) (hy : ∀ n : ℕ, y n = f • y (n + 1)) :
    ∀ n : ℕ, y n = 0 := by
  intro n
  apply hcomplete.toIsHausdorff.haus
  intro m
  have hshift :
      y n = (f ^ m) • y (n + m) :=
    principal_recursive_sequence_shift (A := A) f y hy n m
  have hpow :
      (((f) : Ideal A) ^ m) = Ideal.span ({f ^ m} : Set A) := by
    rw [principalIdeal, Ideal.span_singleton_pow]
  have hmem : y n ∈ (((f) : Ideal A) ^ m • (⊤ : Submodule A M)) := by
    rw [hshift]
    rw [hpow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact SModEq.zero.2 hmem

/-- Helper for Lemma 15.92.8: principal adic completeness provides the correction recursion for
the constant `f`-tower. -/
private theorem principal_correction_sequence_of_isAdicComplete
    {M : ModuleCat A} (f : A) (δ : ℕ → M)
    (hcomplete : IsAdicComplete ((f) : Ideal A) M) :
    ∃ c : ℕ → M, ∀ n : ℕ, c n = δ n + f • c (n + 1) := by
  let tails : ℕ → ℕ → M := fun n m ↦
    Finset.sum (Finset.range m) (fun k ↦ f ^ k • δ (n + k))
  have smul_top_mono :
      ∀ {m k : ℕ}, m ≤ k →
        (((f) : Ideal A) ^ k) • (⊤ : Submodule A M) ≤
          (((f) : Ideal A) ^ m) • (⊤ : Submodule A M) := by
    intro m k hmk x hx
    exact Submodule.smul_induction_on hx
      (fun r hr y hy ↦
        Submodule.smul_mem_smul (Ideal.pow_le_pow_right hmk hr) hy)
      (fun x y hx hy ↦ by simpa using Submodule.add_mem _ hx hy)
  have htails_cauchy :
      ∀ n m : ℕ,
        tails n m ≡ tails n (m + 1)
          [SMOD ((((f) : Ideal A) ^ m) • (⊤ : Submodule A M))] := by
    intro n m
    rw [SModEq.sub_mem]
    have hpow :
        (((f) : Ideal A) ^ m) = Ideal.span ({f ^ m} : Set A) := by
      rw [principalIdeal, Ideal.span_singleton_pow]
    have hm :
        f ^ m • δ (n + m) ∈ (((f) : Ideal A) ^ m) • (⊤ : Submodule A M) := by
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hpow]
      exact Ideal.mem_span_singleton_self _
    have htaildiff :
        tails n m + -tails n (m + 1) = -(f ^ m • δ (n + m)) := by
      simp [tails, Finset.sum_range_succ, add_comm, add_left_comm]
    rw [sub_eq_add_neg, htaildiff]
    exact Submodule.neg_mem _ hm
  have htails_full :
      ∀ n : ℕ, ∀ {m k : ℕ}, m ≤ k →
        tails n m ≡ tails n k [SMOD ((((f) : Ideal A) ^ m) • (⊤ : Submodule A M))] := by
    intro n m k hmk
    induction k, hmk using Nat.le_induction with
    | base =>
        rfl
    | succ k hmk ih =>
        exact ih.trans <| SModEq.mono (smul_top_mono hmk) (htails_cauchy n k)
  have htails_limit :
      ∀ n : ℕ, ∃ c : M, ∀ m : ℕ,
        tails n m ≡ c [SMOD ((((f) : Ideal A) ^ m) • (⊤ : Submodule A M))] := by
    intro n
    exact hcomplete.toIsPrecomplete.prec (htails_full n)
  choose c hc using htails_limit
  have hshift : ∀ n m : ℕ, tails n (m + 1) = δ n + f • tails (n + 1) m := by
    intro n m
    induction m with
    | zero =>
        simp [tails]
    | succ m ih =>
        simp [tails, Finset.sum_range_succ, ih, pow_succ, smul_add, smul_smul, mul_comm,
          add_comm, add_left_comm]
  have hc_rec : ∀ n : ℕ, c n = δ n + f • c (n + 1) := by
    intro n
    rw [← sub_eq_zero]
    apply hcomplete.toIsHausdorff.haus
    intro m
    have hleft :
        tails n (m + 1) ≡ c n [SMOD ((((f) : Ideal A) ^ m) • (⊤ : Submodule A M))] := by
      exact SModEq.mono (smul_top_mono (Nat.le_succ m)) (hc n (m + 1))
    have hright :
        tails n (m + 1) ≡ δ n + f • c (n + 1)
          [SMOD ((((f) : Ideal A) ^ m) • (⊤ : Submodule A M))] := by
      rw [hshift n m]
      exact SModEq.add SModEq.rfl (SModEq.smul (hc (n + 1) m) f)
    exact (sub_smodEq_zero).2 (hleft.symm.trans hright)
  refine ⟨c, ?_⟩
  exact hc_rec

/-- Helper for Lemma 15.92.8: principal adic completeness kills the inverse limit of the
constant `f`-tower. -/
private abbrev localizationAwayModuleTower (f : A) (M : ModuleCat A) :
    SequentialInverseSystem (ModuleCat A) :=
  let X : ℕ → ModuleCat A := fun _ ↦ M
  let step : (n : ℕ) → X (n + 1) ⟶ X n := fun _ ↦ f • 𝟙 M
  Functor.ofOpSequence step

/-- Helper for Lemma 15.92.8: principal adic completeness kills the inverse limit of the
constant `f`-tower. -/
private theorem principal_limit_isZero_of_isAdicComplete
    {M : ModuleCat A} (f : A) (hcomplete : IsAdicComplete ((f) : Ideal A) M) :
    IsZero (limit (localizationAwayModuleTower (A := A) f M)) := by
  let T := localizationAwayModuleTower (A := A) f M
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply limit.hom_ext
  intro n
  have hπ_zero : limit.π T n = 0 := by
    apply ModuleCat.hom_ext
    ext x
    let y : ℕ → M := fun m ↦ (limit.π T (Opposite.op (n.unop + m))).hom x
    have hy : ∀ m : ℕ, y m = f • y (m + 1) := by
      intro m
      have hw :=
        limit.w T ((homOfLE (Nat.le_succ (n.unop + m))).op)
      simpa [y, localizationAwayModuleTower, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ConcreteCategory.congr_hom hw.symm x
    simpa [y] using
      principal_recursive_sequence_eq_zero_of_isAdicComplete
        (A := A) f hcomplete y hy 0
  simpa using hπ_zero

/-- Helper for Lemma 15.92.8: principal adic completeness kills the Milnor `R¹ lim` term of the
constant `f`-tower. -/
private theorem principal_firstDerivedLimit_isZero_of_isAdicComplete
    {M : ModuleCat A} (f : A) (hcomplete : IsAdicComplete ((f) : Ideal A) M) :
    IsZero
      (CategoryTheory.SequentialInverseSystem.firstDerivedLimit
        (localizationAwayModuleTower (A := A) f M)) := by
  let T := localizationAwayModuleTower (A := A) f M
  have hEpi : Epi (CategoryTheory.derivedLimitDifferenceMap T) := by
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro z
    let δ : ℕ → M := fun n ↦ (Pi.π (fun n ↦ T.obj (Opposite.op n)) n).hom z
    obtain ⟨c, hc⟩ :=
      principal_correction_sequence_of_isAdicComplete (A := A) f δ hcomplete
    let w : ↥(∏ᶜ fun n ↦ T.obj (Opposite.op n)) :=
      (Limits.Concrete.productEquiv (fun n ↦ T.obj (Opposite.op n))).symm c
    refine ⟨w, ?_⟩
    apply Limits.Concrete.Pi.map_ext (F := 𝟭 (ModuleCat A))
    intro n
    change (((CategoryTheory.derivedLimitDifferenceMap T) ≫
        Pi.π (fun n ↦ T.obj (Opposite.op n)) n).hom w) =
      (Pi.π (fun n ↦ T.obj (Opposite.op n)) n).hom z
    rw [CategoryTheory.derivedLimitDifferenceMap_comp_π]
    simp [δ, w, localizationAwayModuleTower]
    calc
      c n - f • c (n + 1) = (δ n + f • c (n + 1)) - f • c (n + 1) := by rw [hc n]
      _ = δ n := by abel

/-- Helper for Lemma 15.92.8: an adically complete module is derived complete with respect to the
same ideal. -/
private theorem isDerivedCompleteWithRespectTo_of_isAdicComplete_local
    {M : ModuleCat A} (hcomplete : IsAdicComplete I M) :
    M.IsDerivedCompleteWithRespectTo I := by
  intro f hf
  have hprincipal_le : ((f) : Ideal A) ≤ I := by
    rw [principalIdeal, Ideal.span_le]
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact hf
  have hprincipal_complete : IsAdicComplete ((f) : Ideal A) M :=
    isAdicComplete_of_le_of_fg hprincipal_le (principalIdeal_fg f) hcomplete
  have hlimZero :
      IsZero (limit (localizationAwayModuleTower (A := A) f M)) :=
    principal_limit_isZero_of_isAdicComplete (A := A) (M := M) f hprincipal_complete
  have hfdlZero :
      IsZero
        (CategoryTheory.SequentialInverseSystem.firstDerivedLimit
          (localizationAwayModuleTower (A := A) f M)) :=
    principal_firstDerivedLimit_isZero_of_isAdicComplete (A := A) (M := M) f hprincipal_complete
  have hmodule :
      ModuleCat.moduleLocalizationAwayTVanishing M f :=
    (DerivedCategory.moduleLocalizationAwayTVanishing_iff_limit_and_firstDerivedLimit_isZero
      (A := A) f M).2 ⟨hlimZero, hfdlZero⟩
  simpa [ModuleCat.moduleLocalizationAwayTVanishing] using hmodule

/-- Helper for Lemma 15.92.8: finite free coordinate modules are derived complete once the ring
module `A` is derived complete. -/
private theorem finite_free_coordinate_module_isDerivedCompleteWithRespectTo
    (hA : ((ModuleCat.of A A : ModuleCat A)).IsDerivedCompleteWithRespectTo I) :
    ∀ n : ℕ, ((ModuleCat.of A (Fin n → A) : ModuleCat A)).IsDerivedCompleteWithRespectTo I
  | 0 => by
      let P : ObjectProperty (ModuleCat A) := ModuleCat.derivedCompleteObjectProperty I
      letI : CategoryTheory.ObjectProperty.IsWeakSerreClass P :=
        derivedCompleteObjectProperty_isWeakSerreClass (A := A) I
      have hzero :
          (ModuleCat.of A (Fin 0 → A) : ModuleCat A) ≅ ModuleCat.of A PUnit := by
        exact (LinearEquiv.ofSubsingleton _ _).toModuleIso
      have hzeroModule : IsZero (ModuleCat.of A PUnit) :=
        ModuleCat.isZero_of_subsingleton (ModuleCat.of A PUnit)
      have hPunit : P (ModuleCat.of A PUnit) := by
        -- Proof comment: the rank-zero free module is zero, so it belongs to every weak Serre
        -- class.
        exact CategoryTheory.ObjectProperty.prop_of_isZero (P := P) hzeroModule
      -- Proof comment: transport the zero-object case across the canonical identification
      -- `A^0 ≅ 0`.
      exact P.prop_of_iso hzero.symm hPunit
  | n + 1 => by
      let P : ObjectProperty (ModuleCat A) := ModuleCat.derivedCompleteObjectProperty I
      letI : CategoryTheory.ObjectProperty.IsWeakSerreClass P :=
        derivedCompleteObjectProperty_isWeakSerreClass (A := A) I
      let eModule :
          (ModuleCat.of A (Fin (n + 1) → A) : ModuleCat A) ≅
            (ModuleCat.of A A) ⊞ (ModuleCat.of A (Fin n → A)) :=
        (finSuccArrowLinearEquiv (A := A) n).toModuleIso ≪≫
          (ModuleCat.biprodIsoProd (ModuleCat.of A A) (ModuleCat.of A (Fin n → A))).symm
      have hbiprod :
          P ((ModuleCat.of A A) ⊞ (ModuleCat.of A (Fin n → A))) := by
        -- Proof comment: weak Serre classes are closed under finite products, hence under the
        -- module biproduct.
        exact P.prop_biprod hA
          (finite_free_coordinate_module_isDerivedCompleteWithRespectTo hA n)
      -- Proof comment: rewrite the rank-`n + 1` free module as one copy of `A` plus a smaller
      -- finite free module, then invoke binary-product closure.
      exact P.prop_of_iso eModule.symm hbiprod

/-- Helper for Lemma 15.92.8: every finite free module is derived complete once the ring module
`A` is derived complete. -/
private theorem isDerivedCompleteWithRespectTo_of_linearEquiv
    {M N : ModuleCat A} (e : M ≃ₗ[A] N)
    (hN : N.IsDerivedCompleteWithRespectTo I) :
    M.IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  let E' :
      DerivedCategory (ModuleCat A) :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  let single₀ : ModuleCat A ⥤ DerivedCategory (ModuleCat A) :=
    ModuleCat.single0Functor
  let m : M ⟶ N := ModuleCat.ofHom e.toLinearMap
  let mInv : N ⟶ M := ModuleCat.ofHom e.symm.toLinearMap
  have hm_hInv : m ≫ mInv = 𝟙 M := by
    ext x
    change e.symm (e x) = x
    exact e.left_inv x
  have hmInv_h : mInv ≫ m = 𝟙 N := by
    ext x
    change e (e.symm x) = x
    exact e.right_inv x
  letI : IsIso m := ⟨⟨mInv, hm_hInv, hmInv_h⟩⟩
  have hsubN : Subsingleton (E' ⟶ single₀.obj N) := hN f hf E
  -- Proof comment: compose maps into `M[0]` with the isomorphism to `N[0]`, where the Hom set is
  -- already subsingleton, and cancel the resulting mono.
  refine ⟨fun u v ↦ ?_⟩
  apply (cancel_mono (single₀.map m)).1
  exact hsubN.elim _ _

/-- Helper for Lemma 15.92.8: every finite free module is derived complete once the ring module
`A` is derived complete. -/
private theorem finite_free_module_isDerivedCompleteWithRespectTo
    (hA : ((ModuleCat.of A A : ModuleCat A)).IsDerivedCompleteWithRespectTo I)
    (M : ModuleCat A) [Module.Free A M] [Module.Finite A M] :
    M.IsDerivedCompleteWithRespectTo I := by
  classical
  by_cases hA_subsingleton : Subsingleton A
  · letI : Subsingleton A := hA_subsingleton
    letI : Subsingleton M := Module.subsingleton A M
    let e : M ≃ₗ[A] (Fin 0 → A) := LinearEquiv.ofSubsingleton _ _
    have hcoord :
        ((ModuleCat.of A (Fin 0 → A) : ModuleCat A)).IsDerivedCompleteWithRespectTo I :=
      finite_free_coordinate_module_isDerivedCompleteWithRespectTo hA 0
    -- Proof comment: over a subsingleton ring every finite free module is the zero module, so
    -- the rank-zero coordinate model suffices.
    exact isDerivedCompleteWithRespectTo_of_linearEquiv e hcoord
  · letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA_subsingleton
    let b : Module.Basis (Module.Free.ChooseBasisIndex A M) A M := Module.Free.chooseBasis A M
    letI : Finite (Module.Free.ChooseBasisIndex A M) := Module.Finite.finite_basis b
    let n : ℕ := Fintype.card (Module.Free.ChooseBasisIndex A M)
    let eIndex : Module.Free.ChooseBasisIndex A M ≃ Fin n :=
      Fintype.equivFin (Module.Free.ChooseBasisIndex A M)
    let e : M ≃ₗ[A] (Fin n → A) :=
      b.equivFun.trans (LinearEquiv.funCongrLeft (R := A) (M := A) eIndex).symm
    have hcoord :
        ((ModuleCat.of A (Fin n → A) : ModuleCat A)).IsDerivedCompleteWithRespectTo I :=
      finite_free_coordinate_module_isDerivedCompleteWithRespectTo hA n
    -- Proof comment: choose a finite basis for `M`, reindex it by `Fin n`, and transport the
    -- coordinate-module result back across the resulting linear equivalence.
    exact isDerivedCompleteWithRespectTo_of_linearEquiv e hcoord

/-- Helper for Lemma 15.92.8: the canonical projection from cycles to left homology is the
cokernel of the boundary-to-cycles map. -/
private noncomputable abbrev leftHomologyπ_isColimitCokernel
    (S : ShortComplex (ModuleCat A)) :
    IsColimit (CokernelCofork.ofπ S.leftHomologyπ S.toCycles_comp_leftHomologyπ) := by
  -- Proof comment: this is exactly the universal property built into the short-complex
  -- left-homology construction.
  exact S.leftHomologyIsCokernel

/-- Helper for Lemma 15.92.8: the cohomology of a termwise finite free complex is derived complete
degreewise once `A` is. -/
private theorem termwiseFiniteFree_homology_isDerivedCompleteWithRespectTo
    {E : CochainComplex (ModuleCat A) ℤ} [E.IsTermwiseFiniteFree]
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) (i : ℤ) :
    (E.homology i).IsDerivedCompleteWithRespectTo I := by
  let P : ObjectProperty (ModuleCat A) := ModuleCat.derivedCompleteObjectProperty I
  letI : CategoryTheory.ObjectProperty.IsWeakSerreClass P :=
    derivedCompleteObjectProperty_isWeakSerreClass (A := A) I
  let S : ShortComplex (ModuleCat A) := E.sc i
  -- Route correction: keep the source short-complex proof on `S := E.sc i`, but use the
  -- universe-polymorphic finite-free base case directly on `S.X₁` and `S.X₂` before taking the
  -- kernel and cokernel steps.
  have hX₁ : P S.X₁ := by
    -- Proof comment: the left term of `E.sc i` is a term of the finite-free representative.
    simpa [P, S] using
      finite_free_module_isDerivedCompleteWithRespectTo (A := A) (I := I) hA S.X₁
  have hX₂ : P S.X₂ := by
    -- Proof comment: the middle term of `E.sc i` is likewise finite free.
    simpa [P, S] using
      finite_free_module_isDerivedCompleteWithRespectTo (A := A) (I := I) hA S.X₂
  have hkernel : P (kernel S.g) :=
    isDerivedCompleteWithRespectTo_kernel_local (A := A) (I := I) S.g hX₂
  have hcycles : P S.cycles := by
    -- Proof comment: cycles are the kernel of the outgoing differential in the owner short
    -- complex.
    exact P.prop_of_iso S.cyclesIsoKernel.symm hkernel
  have hcoker : P (cokernel S.toCycles) :=
    isDerivedCompleteWithRespectTo_cokernel_of_mono_local (A := A) (I := I)
      S.toCycles hX₁ hcycles
  have hleft : P S.leftHomology := by
    -- Proof comment: left homology is the cokernel of the boundary-to-cycles map.
    exact
      P.prop_of_iso
        (IsColimit.coconePointUniqueUpToIso
          (leftHomologyπ_isColimitCokernel (A := A) S)
          (cokernelIsCokernel S.toCycles)).symm
        hcoker
  -- Proof comment: the owner left homology of `E.sc i` is the usual cochain homology of `E`.
  exact P.prop_of_iso (sc_leftHomology_iso_homology (A := A) (E := E) i) hleft

/-- Helper for Lemma 15.92.8: every cohomology module of a pseudo-coherent derived object is
derived complete once `A` is. -/
private theorem homology_isDerivedComplete_of_isPseudoCoherent
    {K : DMod} (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I)
    (hK : K.IsPseudoCoherent) :
    ∀ n : ℤ, ((H n).obj K).IsDerivedCompleteWithRespectTo I := by
  rcases hK with ⟨E, _, hEfree, α, hα⟩
  letI : E.IsTermwiseFiniteFree := hEfree
  let P : ObjectProperty (ModuleCat A) := ModuleCat.derivedCompleteObjectProperty I
  letI : CategoryTheory.ObjectProperty.IsWeakSerreClass P :=
    derivedCompleteObjectProperty_isWeakSerreClass (A := A) I
  let eα : DerivedCategory.Q.obj E ≅ K := asIso α
  intro n
  have hEhomology : P (E.homology n) :=
    termwiseFiniteFree_homology_isDerivedCompleteWithRespectTo (A := A) (I := I) hA n
  have hQhomology : P ((H n).obj (DerivedCategory.Q.obj E)) := by
    -- Proof comment: compute derived homology on the chosen cochain representative `E`.
    exact P.prop_of_iso (derived_homology_iso (A := A) E n).symm hEhomology
  -- Proof comment: transport the degreewise conclusion across the quasi-isomorphism witnessing
  -- pseudo-coherence.
  exact P.prop_of_iso ((H n).mapIso eα) hQhomology

/-- Lemma 15.92.8: if the ring `A`, viewed as an `A`-module, is derived complete with respect to
an ideal `I`, then every pseudo-coherent object of `D(A)` is derived complete with respect to
`I`. -/
theorem isDerivedCompleteWithRespectTo_of_isPseudoCoherent
    {K : DMod} (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I)
    (hK : K.IsPseudoCoherent) :
    K.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: by Lemma `15.92.6`, derived completeness is equivalent to degreewise derived
  -- completeness of cohomology modules.
  rw [DerivedCategory.isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty]
  -- Proof comment: on a pseudo-coherent representative, each cohomology module is a cokernel of
  -- the boundary-to-cycles map between derived-complete modules.
  exact homology_isDerivedComplete_of_isPseudoCoherent (A := A) (I := I) hA hK

-- Proof sketch: by Lemma `15.92.3`, `I`-adic completeness of the `A`-module `A` implies derived
-- completeness with respect to `I`; then apply `isDerivedCompleteWithRespectTo_of_isPseudoCoherent`.
/-- If the ring `A`, viewed as an `A`-module, is `I`-adically complete, then every
pseudo-coherent object of `D(A)` is derived complete with respect to `I`. -/
theorem isDerivedCompleteWithRespectTo_of_isPseudoCoherent_of_isAdicComplete
    {K : DMod} (hA : IsAdicComplete I (ModuleCat.of A A))
    (hK : K.IsPseudoCoherent) :
    K.IsDerivedCompleteWithRespectTo I := by
  have hAderived : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I :=
    isDerivedCompleteWithRespectTo_of_isAdicComplete_local (A := A) (I := I)
      (M := ModuleCat.of A A) hA
  -- Proof comment: first apply Lemma `15.92.3` to the ring module `A`, then invoke the main
  -- pseudo-coherent derived-completeness statement proved above.
  exact isDerivedCompleteWithRespectTo_of_isPseudoCoherent (A := A) (I := I) hAderived hK

end
