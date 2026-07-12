import Mathlib
import StacksProject_2024.Chap12.Lemma_12_6_3
import StacksProject_2024.Chap10.Lemma_10_96_7
import StacksProject_2024.Chap10.Lemma_10_96_8
import StacksProject_2024.Chap15.Lemma_15_87_10
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Lemma_15_92_3.Index
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

open scoped PrincipalIdeal

namespace ModuleCat

variable {I : Ideal A} (M : ModuleCat.{u, u} A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling:
- primary domain: adic completeness and derived completeness for modules over a commutative ring;
- sampled owner-side declarations:
  `IsAdicComplete`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `isAdicComplete_of_le_of_fg`,
  `surjective_adicCompletion_of_span_eq_of_generatorwise_surjective`;
- best owner abstraction: the chapter owner predicate `M.IsDerivedCompleteWithRespectTo I`,
  whose pointwise expansion in terms of `T(M, f)` is already derived API from
`Definition_15_92_4`;
- primitive data: the ideal `I`, the module `M`, and the completion map `AdicCompletion.of I M`;
- derived API: the pointwise `T(M, f)` vanishing criterion for each `f ∈ I` and the
  finitely-generated reduction to principal completion maps.

Layer triage:
- `source-facing`: surjectivity of the completion map `M → lim M / I^n M`;
- `core/canonical`: `IsAdicComplete`, `AdicCompletion.of I M`, and
  `M.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: the generatorwise `T(M, f)` vanishing criterion coming from
  `Definition_15_92_4`. -/

/-- Helper for Lemma 15.92.3: a principal recursive sequence propagates one step to an arbitrary
power of `f`. -/
lemma principal_recursive_sequence_shift
    (f : A) (M : ModuleCat.{u, u} A) (y : ℕ → M)
    (hy : ∀ n : ℕ, y n = f • y (n + 1)) :
    ∀ n m : ℕ, y n = (f ^ m) • y (n + m) := by
  intro n m
  induction m generalizing n with
  | zero =>
      simp
  | succ m ihm =>
      -- Proof comment: unfold one recursive step, then push the remaining `m` steps by induction.
      calc
        y n = f • y (n + 1) := hy n
        _ = f • ((f ^ m) • y (n + 1 + m)) := by rw [ihm (n + 1)]
        _ = (f ^ (m + 1)) • y (n + (m + 1)) := by
              rw [smul_smul]
              simpa [pow_succ', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Lemma 15.92.3: in an `((f))`-adically complete module, every principal recursive
sequence is termwise zero. -/
lemma principal_recursive_sequence_eq_zero_of_isAdicComplete
    (f : A) (M : ModuleCat.{u, u} A) (hcomplete : IsAdicComplete ((f) : Ideal A) M)
    (y : ℕ → M) (hy : ∀ n : ℕ, y n = f • y (n + 1)) :
    ∀ n : ℕ, y n = 0 := by
  intro n
  -- Proof comment: each term is divisible by every power of `f`, so Hausdorffness forces it to
  -- vanish.
  apply hcomplete.toIsHausdorff.haus
  intro m
  have hshift :
      y n = (f ^ m) • y (n + m) :=
    principal_recursive_sequence_shift (A := A) f M y hy n m
  have hmem : y n ∈ (((f) : Ideal A) ^ m • (⊤ : Submodule A M)) := by
    rw [hshift]
    rw [show (((f) : Ideal A) ^ m) = Ideal.span ({f ^ m} : Set A) by
      rw [principalIdeal, Ideal.span_singleton_pow]]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact SModEq.zero.2 hmem

/-- Helper for Lemma 15.92.3: principal adic completeness produces the correction sequences used
to replace the textbook infinite sum `δₙ + fδₙ₊₁ + f²δₙ₊₂ + ⋯`. -/
lemma principal_correction_sequence_of_isAdicComplete
    (f : A) (M : ModuleCat.{u, u} A) (δ : ℕ → M)
    (hcomplete : IsAdicComplete ((f) : Ideal A) M) :
    ∃ c : ℕ → M, ∀ n : ℕ, c n = δ n + f • c (n + 1) := by
  let tails : ℕ → ℕ → M := fun n m ↦
    Finset.sum (Finset.range m) (fun k ↦ f ^ k • δ (n + k))
  have smul_top_mono :
      ∀ {m k : ℕ}, m ≤ k →
        (((f) : Ideal A) ^ k) • (⊤ : Submodule A M) ≤
          (((f) : Ideal A) ^ m) • (⊤ : Submodule A M) := by
    intro m k hmk
    intro x hx
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
    have hm :
        f ^ m • δ (n + m) ∈ (((f) : Ideal A) ^ m) • (⊤ : Submodule A M) := by
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [show (((f) : Ideal A) ^ m) = Ideal.span ({f ^ m} : Set A) by
        rw [principalIdeal, Ideal.span_singleton_pow]]
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
    -- Proof comment: compare the finite tails on both sides modulo every power of `(f)` and use
    -- Hausdorffness to identify their limits.
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
  exact ⟨c, hc_rec⟩

/-- Helper for Lemma 15.92.3: the localization-away vanishing condition on `M[0]` also forces
the shifted localized degree-zero source `A_f[0][-1]` to have a subsingleton Hom-space into
`M[0]`. -/
lemma shifted_subsingleton_hom_from_localizationAway_of_localizationAwayDerivedHomVanishingCondition
    (f : A) (M : ModuleCat.{u, u} A)
    (hvanish : CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
      ((single₀).obj M)) :
    Subsingleton ((((single₀).obj (ModuleCat.of A (Localization.Away f)))⟦(-1 : ℤ)⟧) ⟶
      (single₀).obj M) := by
  let F :=
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory
  let singleAway :
      DerivedCategory (ModuleCat.{u, u} (Localization.Away f)) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).obj
      (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f))
  let source : ModuleCat.{u, u} A :=
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).obj
      (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))
  let sourceIso :
      F.obj singleAway ≅ (single₀).obj source :=
    restrictScalars_localizationAway_single_iso (A := A) f
  have hShifted :
      Subsingleton ((F.obj (singleAway⟦(-1 : ℤ)⟧)) ⟶ (single₀).obj M) :=
    hvanish (singleAway⟦(-1 : ℤ)⟧)
  have hRestricted :
      Subsingleton ((((single₀).obj source)⟦(-1 : ℤ)⟧) ⟶ (single₀).obj M) := by
    letI := hShifted
    let shiftIso :
        F.obj (singleAway⟦(-1 : ℤ)⟧) ≅ (((single₀).obj source)⟦(-1 : ℤ)⟧) :=
      (F.commShiftIso (-1 : ℤ)).app singleAway ≪≫
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat A)) (-1 : ℤ)).mapIso sourceIso
    let e :
        ((F.obj (singleAway⟦(-1 : ℤ)⟧)) ⟶ (single₀).obj M) ≃
          ((((single₀).obj source)⟦(-1 : ℤ)⟧) ⟶ (single₀).obj M) :=
      shiftIso.homCongr (CategoryTheory.eqToIso rfl)
    exact e.symm.injective.subsingleton
  let eLinear : source ≃ₗ[A] Localization.Away f :=
    restrictScalars_selfLinearEquiv (A := A) (B := Localization.Away f)
  let eSource : source ≅ ModuleCat.of A (Localization.Away f) := eLinear.toModuleIso
  let shiftedCanonicalIso :
      (((single₀).obj source)⟦(-1 : ℤ)⟧) ≅
        (((single₀).obj (ModuleCat.of A (Localization.Away f)))⟦(-1 : ℤ)⟧) :=
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat A)) (-1 : ℤ)).mapIso
      ((single₀).mapIso eSource)
  letI := hRestricted
  let e :
      ((((single₀).obj source)⟦(-1 : ℤ)⟧) ⟶ (single₀).obj M) ≃
        ((((single₀).obj (ModuleCat.of A (Localization.Away f)))⟦(-1 : ℤ)⟧) ⟶
          (single₀).obj M) :=
    shiftedCanonicalIso.homCongr (CategoryTheory.eqToIso rfl)
  exact e.symm.injective.subsingleton

/-- Helper for Lemma 15.92.3: the constant tower `M <-f- M <-f- ...` controlling the principal
localization-away object `T(M, f)`. -/
abbrev localizationAwayModuleTower (f : A) (M : ModuleCat.{u, u} A) :
    CategoryTheory.SequentialInverseSystem (ModuleCat A) :=
  let X : ℕ → ModuleCat A := fun _ ↦ M
  let step : (n : ℕ) → X (n + 1) ⟶ X n := fun _ ↦ f • 𝟙 M
  Functor.ofOpSequence step

/-- Helper for Lemma 15.92.3: principal adic completeness kills the inverse limit term of the
constant `f`-tower by forcing every recursive sequence to vanish. -/
lemma principal_limit_isZero_of_isAdicComplete
    (f : A) (M : ModuleCat.{u, u} A) (hcomplete : IsAdicComplete ((f) : Ideal A) M) :
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
      -- Proof comment: the limit compatibility is exactly the principal recursive relation.
      simpa [y, localizationAwayModuleTower, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg (fun t : limit T ⟶ M ↦ t.hom x) hw.symm
    simpa [y] using
      principal_recursive_sequence_eq_zero_of_isAdicComplete
        (A := A) f M hcomplete y hy 0
  simpa using hπ_zero

/-- Helper for Lemma 15.92.3: principal adic completeness kills the Milnor cokernel `R¹ lim`
by solving the correction recursion for every target sequence. -/
lemma principal_firstDerivedLimit_isZero_of_isAdicComplete
    (f : A) (M : ModuleCat.{u, u} A) (hcomplete : IsAdicComplete ((f) : Ideal A) M) :
    IsZero
      (CategoryTheory.SequentialInverseSystem.firstDerivedLimit
        (localizationAwayModuleTower (A := A) f M)) := by
  let T := localizationAwayModuleTower (A := A) f M
  have hEpi : Epi (CategoryTheory.derivedLimitDifferenceMap T) := by
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro z
    let δ : ℕ → M := fun n ↦
      (ConcreteCategory.hom
        (Pi.π (fun n ↦ T.obj (Opposite.op n)) n)) z
    obtain ⟨c, hc⟩ :=
      principal_correction_sequence_of_isAdicComplete (A := A) f M δ hcomplete
    let w :
        ↥(∏ᶜ fun n ↦ T.obj (Opposite.op n)) :=
      (Limits.Concrete.productEquiv (fun n ↦ T.obj (Opposite.op n))).symm c
    refine ⟨w, ?_⟩
    apply Limits.Concrete.Pi.map_ext (F := 𝟭 (ModuleCat A))
    intro n
    have hcoord :
        (ConcreteCategory.hom
            (Pi.π (fun n ↦ T.obj (Opposite.op n)) n))
            ((ConcreteCategory.hom (CategoryTheory.derivedLimitDifferenceMap T)) w) =
          (ConcreteCategory.hom
            (Pi.π (fun n ↦ T.obj (Opposite.op n)) n)) w -
            (ConcreteCategory.hom
              ((Pi.π (fun n ↦ T.obj (Opposite.op n)) (n + 1)) ≫
                T.transitionMap (Nat.le_succ n))) w := by
      simpa [Preadditive.comp_sub, Category.assoc] using
        ConcreteCategory.congr_hom
          (CategoryTheory.derivedLimitDifferenceMap_comp_π T n) w
    calc
      (ConcreteCategory.hom
          (Pi.π (fun n ↦ T.obj (Opposite.op n)) n))
          ((ConcreteCategory.hom (CategoryTheory.derivedLimitDifferenceMap T)) w)
          = c n - f • c (n + 1) := by
            rw [hcoord]
            simp [w, localizationAwayModuleTower]
      _ = δ n := by
            linarith [hc n]
      _ =
        (ConcreteCategory.hom
          (Pi.π (fun n ↦ T.obj (Opposite.op n)) n)) z := rfl
  let _ : Epi (CategoryTheory.derivedLimitDifferenceMap T) := hEpi
  simpa [CategoryTheory.SequentialInverseSystem.firstDerivedLimit] using
    (isZero_cokernel_of_epi (CategoryTheory.derivedLimitDifferenceMap T))

/-- Helper for Lemma 15.92.3: vanishing of the Milnor cokernel `R¹ lim` gives the principal
correction recursion needed in the converse direction. -/
lemma principal_correction_sequence_of_firstDerivedLimit_isZero
    (f : A) (M : ModuleCat.{u, u} A)
    (hfdl :
      IsZero
        (CategoryTheory.SequentialInverseSystem.firstDerivedLimit
          (localizationAwayModuleTower (A := A) f M)))
    (δ : ℕ → M) :
    ∃ c : ℕ → M, ∀ n : ℕ, c n = δ n + f • c (n + 1) := by
  let T := localizationAwayModuleTower (A := A) f M
  have hEpi : Epi (CategoryTheory.derivedLimitDifferenceMap T) := by
    exact CategoryTheory.epi_of_isZero_cokernel
      (CategoryTheory.derivedLimitDifferenceMap T)
      (by simpa [CategoryTheory.SequentialInverseSystem.firstDerivedLimit] using hfdl)
  let _ : Epi (CategoryTheory.derivedLimitDifferenceMap T) := hEpi
  have hsurj :
      Function.Surjective (ConcreteCategory.hom (CategoryTheory.derivedLimitDifferenceMap T)) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  let z :
      ↥(∏ᶜ fun n ↦ T.obj (Opposite.op n)) :=
    (Limits.Concrete.productEquiv (fun n ↦ T.obj (Opposite.op n))).symm δ
  rcases hsurj z with ⟨w, hw⟩
  refine ⟨fun n ↦
      (ConcreteCategory.hom
        (Pi.π (fun n ↦ T.obj (Opposite.op n)) n)) w, ?_⟩
  intro n
  have hwπ :
      (ConcreteCategory.hom
          (Pi.π (fun n ↦ T.obj (Opposite.op n)) n))
          ((ConcreteCategory.hom (CategoryTheory.derivedLimitDifferenceMap T)) w) =
        δ n := by
    simpa [z] using
      congrArg
        (fun u : ↥(∏ᶜ fun n ↦ T.obj (Opposite.op n)) ↦
          (ConcreteCategory.hom
            (Pi.π (fun n ↦ T.obj (Opposite.op n)) n)) u)
        hw
  have hcoord :
      (ConcreteCategory.hom
          (Pi.π (fun n ↦ T.obj (Opposite.op n)) n))
          ((ConcreteCategory.hom (CategoryTheory.derivedLimitDifferenceMap T)) w) =
        (ConcreteCategory.hom
            (Pi.π (fun n ↦ T.obj (Opposite.op n)) n)) w -
          (ConcreteCategory.hom
            ((Pi.π (fun n ↦ T.obj (Opposite.op n)) (n + 1)) ≫
              T.transitionMap (Nat.le_succ n))) w := by
    simpa [Preadditive.comp_sub, Category.assoc] using
      ConcreteCategory.congr_hom
        (CategoryTheory.derivedLimitDifferenceMap_comp_π T n) w
  calc
    (ConcreteCategory.hom
        (Pi.π (fun n ↦ T.obj (Opposite.op n)) n)) w
        = δ n + f •
            (ConcreteCategory.hom
              (Pi.π (fun n ↦ T.obj (Opposite.op n)) (n + 1))) w := by
                rw [hcoord] at hwπ
                simpa [localizationAwayModuleTower] using eq_add_of_sub_eq hwπ
    _ = δ n + f •
          (ConcreteCategory.hom
            (Pi.π (fun n ↦ T.obj (Opposite.op n)) (n + 1))) w := rfl

/-- Helper for Lemma 15.92.3: a module that is complete for the principal ideal `(f)` satisfies
the pointwise localization-away vanishing condition at `f`. -/
lemma principal_localizationAwayDerivedHomVanishingCondition_of_isAdicComplete
    (f : A) (M : ModuleCat.{u, u} A)
    (hcomplete : IsAdicComplete ((f) : Ideal A) M) :
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
      ((single₀).obj M) := by
  -- Route correction: the stable proved frontier now isolates the source recursive-sequence and
  -- correction-sequence arguments as `lim = 0` and `R¹ lim = 0` for the constant `f`-tower on
  -- `M`. The remaining blocker is the degree-zero bridge from those Milnor terms to the literal
  -- localization-away predicate without importing the broken owner file `Lemma_15_92_1`.
  have hlimZero :
      IsZero (limit (localizationAwayModuleTower (A := A) f M)) :=
    principal_limit_isZero_of_isAdicComplete (A := A) f M hcomplete
  have hfdlZero :
      IsZero
        (CategoryTheory.SequentialInverseSystem.firstDerivedLimit
          (localizationAwayModuleTower (A := A) f M)) :=
    principal_firstDerivedLimit_isZero_of_isAdicComplete (A := A) f M hcomplete
  -- TODO: identify the above Milnor vanishings with `T(M, f) = 0`, equivalently with the
  -- degree-zero localization-away derived-Hom vanishing condition.
  sorry

-- Proof sketch: for each `f ∈ I`, the principal ideal `(f)` is finitely generated and contained
-- in `I`, so `M` is also `(f)`-adically complete by `isAdicComplete_of_le_of_fg`. The pointwise
-- vanishing criterion from Definition `15.92.4` then shows that `M` is derived complete with
-- respect to `I`.
/-- Lemma 15.92.3 (1): an `I`-adically complete `A`-module is derived complete with respect to
`I`. Equivalently, for every `f ∈ I` the textbook object `T(M, f)` vanishes. -/
theorem isDerivedCompleteWithRespectTo_of_isAdicComplete
    (hcomplete : IsAdicComplete I M) :
    M.IsDerivedCompleteWithRespectTo I := by
  intro f hf
  -- Proof comment: shrink from `I` to the finitely generated principal ideal `(f)` and then apply
  -- the principal vanishing statement.
  have hprincipal_le : ((f) : Ideal A) ≤ I := by
    rw [principalIdeal, Ideal.span_le]
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact hf
  have hprincipal_complete : IsAdicComplete ((f) : Ideal A) M :=
    isAdicComplete_of_le_of_fg hprincipal_le (principalIdeal_fg f) hcomplete
  -- Proof comment: the principal blocker is exactly the pointwise vanishing statement needed for
  -- the current generator `f`.
  exact
    principal_localizationAwayDerivedHomVanishingCondition_of_isAdicComplete
      f M hprincipal_complete

/-- Helper for Lemma 15.92.3: if the pointwise localization-away vanishing condition holds at
`f`, then the principal completion map for `(f)` is surjective. -/
lemma principal_surjective_adicCompletion_of_localizationAwayDerivedHomVanishingCondition
    (f : A) (M : ModuleCat.{u, u} A)
    (hvanish : CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
      ((single₀).obj M)) :
    Function.Surjective (AdicCompletion.of ((f) : Ideal A) M) := by
  -- Route correction: the stable proved frontier now supplies the correction recursion once one
  -- knows that the Milnor obstruction term `R¹ lim` of the constant `f`-tower vanishes. The
  -- remaining blocker is again the missing bridge from the literal localization-away predicate
  -- `hvanish` to that Milnor vanishing, without importing the broken owner file.
  -- TODO: extract `R¹ lim = 0` from `hvanish`, apply
  -- `principal_correction_sequence_of_firstDerivedLimit_isZero`, and finish the standard
  -- principal precompleteness argument.
  sorry

-- Proof sketch: choose finitely many generators of `I`. The hypothesis gives the vanishing
-- condition `T(M, f_i) = 0` for each chosen generator because
-- `M.IsDerivedCompleteWithRespectTo I` is exactly the generatorwise localization-away vanishing
-- criterion. Lemma `10.96.7` then reduces surjectivity of `M → lim M / I^n M` to the principal
-- generator cases.
/-- Lemma 15.92.3 (2): if `I` is finitely generated and `M` is derived complete with respect to
`I`, then the canonical map `M → lim M / I^n M` is surjective. Equivalently, it is enough that
`T(M, f) = 0` for every `f ∈ I`. -/
theorem surjective_adicCompletion_of_isDerivedCompleteWithRespectTo
    (hfg : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) :
    Function.Surjective (AdicCompletion.of I M) := by
  rcases hfg with ⟨s, hs⟩
  -- Proof comment: apply the finitely generated owner theorem and discharge each generator by the
  -- principal vanishing-to-surjectivity statement.
  refine surjective_adicCompletion_of_span_eq_of_generatorwise_surjective
    (M := M) s hs ?_
  intro f hf
  have hfI : f ∈ I := by
    rw [← hs]
    exact Ideal.subset_span hf
  have hvanish :
      CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
        ((single₀).obj M) := by
    -- Proof comment: derived completeness with respect to `I` is already the required pointwise
    -- vanishing criterion on every generator.
    exact hM f hfI
  -- Proof comment: the principal completion map here is definitional equal to the singleton-span
  -- completion map expected by Lemma `10.96.7`.
  simpa [principalIdeal] using
    principal_surjective_adicCompletion_of_localizationAwayDerivedHomVanishingCondition
      f M hvanish

end ModuleCat

end
