import Mathlib
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap15.Lemma_15_65_3
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_75_3
import StacksProject_2024.Chap15.Lemma_15_75_7

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Bounded" => (t.bounded : ObjectProperty DMod)
local notation:max "H^" i:max => DerivedCategory.homologyFunctor (ModuleCat R) i
local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain-style sampling for Lemma 15.75.14:
- primary domain: perfect objects in derived categories of modules over a regular ring;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `DerivedCategory.IsPerfect`,
  `t.bounded`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction:
  part `(1)` is `source-facing` at the module level, while part `(2)` is `source-facing` on
  `D(R)` with boundedness read through the canonical owner `t.bounded`
  and cohomology read through the canonical owner `DerivedCategory.homologyFunctor`;
- primitive vs. derived:
  primitive data are a module `M` or a derived object `K`;
  derived API is perfectness, boundedness, and the degreewise finiteness condition on the
  cohomology modules;
- source/core/bridge triage:
  `source-facing`: the two equivalences below;
  `core/canonical`: `ModuleCat.IsPerfect`, `DerivedCategory.IsPerfect`, and
    `t.bounded`;
  `bridge/view`: the cohomology functors `H^i` landing in `ModuleCat R`.

This file should therefore keep the textbook equivalences, but phrase boundedness through the
canonical `t`-structure owner directly and avoid depending on the later parallel bounded-derived
API file.
-/

namespace ModuleCat

/-- Helper for Lemma 15.75.14: a monotone family of loci on `Spec R` stabilizes once every prime
admits a basic-open neighborhood contained in some stage. -/
lemma exists_uniform_index_of_basicOpen_cover
    (U : ℕ → Set (PrimeSpectrum R))
    (hmono : Monotone U)
    (hbasic :
      ∀ p : PrimeSpectrum R, ∃ n : ℕ, ∃ f : R,
        p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∧
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ U n) :
    ∃ N : ℕ, U N = Set.univ := by
  classical
  -- Choose one basic-open neighborhood and one stage of the monotone family for each prime.
  choose n f hmem hsub using hbasic
  -- Compactness of `Spec R` turns the primewise open cover into a finite cover.
  obtain ⟨t, htcover⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun p : PrimeSpectrum R ↦ (PrimeSpectrum.basicOpen (f p) : Set (PrimeSpectrum R)))
      (fun p ↦ (PrimeSpectrum.basicOpen (f p)).2)
      (by
        intro p hp
        exact Set.mem_iUnion.mpr ⟨p, hmem p⟩)
  let N := t.sup n
  refine ⟨N, Set.eq_univ_iff_forall.2 ?_⟩
  intro p
  -- Any prime lies in one member of the finite cover, and monotonicity upgrades that stage to `N`.
  rcases Set.mem_iUnion₂.mp (htcover (by simp)) with ⟨q, hqt, hpq⟩
  exact (hmono (Finset.le_sup hqt)) (hsub q hpq)

/-- Helper for Lemma 15.75.14: the kernel of a surjective map onto a projective module is
projective once the source module is projective. -/
private theorem projective_kernel_of_surjective
    {A : Type u} [AddCommGroup A] [Module R A] [Module.Projective R A]
    {B : Type u} [AddCommGroup B] [Module R B] [Module.Projective R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Module.Projective R (LinearMap.ker f) := by
  -- Split the surjection so that the kernel becomes a direct summand of the projective source.
  obtain ⟨σ, hσ⟩ :=
    LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.2 hf)
  let r : A →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - σ.comp f).codRestrict (LinearMap.ker f) (by
      intro x
      -- The correction term lands in the kernel because `σ` is a right inverse of `f`.
      rw [LinearMap.mem_ker]
      have hσ_apply : f (σ (f x)) = f x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ (f x)
      simp [LinearMap.sub_apply, LinearMap.comp_apply, hσ_apply])
  have hr : r.comp (LinearMap.ker f).subtype = LinearMap.id := by
    -- On kernel elements the splitting correction vanishes, so `r` retracts onto the kernel.
    ext x
    simp [r, sub_eq_add_neg, LinearMap.comp_apply]
  exact Module.Projective.of_split (LinearMap.ker f).subtype r hr

/-- Helper for Lemma 15.75.14: in the degree-zero single chain complex, the incoming differential
vanishes after identifying the zeroth term with the underlying module. -/
private theorem single0_objXSelf_comp_d_eq_zero
    (M : ModuleCat R) :
    ((ChainComplex.single₀ (ModuleCat R)).obj M).d 1 0 ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom = 0 := by
  -- The single complex has no nonzero term in degree `1`, so the first differential is zero.
  rw [HomologicalComplex.single_obj_d]
  simp [ChainComplex.single₀ObjXSelf]
  rfl

/-- Helper for Lemma 15.75.14: on a degree-zero single chain complex, the canonical map from
zeroth opcycles to the underlying module is the descended degree-zero term map. -/
private theorem single0_opcycles_self_inv_eq_descOpcycles
    (M : ModuleCat R) :
    (HomologicalComplex.singleObjOpcyclesSelfIso
      (ComplexShape.down ℕ) (0 : ℕ) M).inv =
    ((ChainComplex.single₀ (ModuleCat R)).obj M).descOpcycles
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom
      1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
  -- Both maps out of zeroth opcycles are determined by their composites with `pOpcycles`.
  apply (cancel_epi (((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0)).1
  calc
    ((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
          simpa [ChainComplex.single₀ObjXSelf] using
            (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
              (c := ComplexShape.down ℕ) (j := (0 : ℕ)) (A := M))
    _ =
      ((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0 ≫
        ((ChainComplex.single₀ (ModuleCat R)).obj M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom
          1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
            symm
            simpa using
              (HomologicalComplex.p_descOpcycles
                (K := (ChainComplex.single₀ (ModuleCat R)).obj M)
                (i := (0 : ℕ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.down ℕ) (0 : ℕ) M).hom)
                (j := 1)
                (hj := by simp)
                (hk := single0_objXSelf_comp_d_eq_zero (R := R) M))

/-- Helper for Lemma 15.75.14: the augmentation of a chosen finite free resolution is surjective
and exact at degree `0`. -/
private theorem chosen_resolution_augmentation_exact
    {M : ModuleCat R} {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] M}
    (hπ : ChainComplex.IsFiniteFreeResolution π) :
    Function.Surjective (π.f 0).hom ∧ Function.Exact (F.d 1 0).hom (π.f 0).hom := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let singleX :
      ((moduleSingle[R] M).X 0 ≅ ModuleCat.of R M) :=
    HomologicalComplex.singleObjXSelf
      (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)
  have hcomp_zero :
      F.d 1 0 ≫ (π.f 0 ≫ singleX.hom) = 0 := by
    -- The chain map equation lands in the zero differential of the degree-zero single complex.
    simpa [Category.assoc, single0_objXSelf_comp_d_eq_zero (R := R) (ModuleCat.of R M)] using
      congrArg (fun f => f ≫ singleX.hom) (π.comm 1 0)
  let desc :
      F.opcycles 0 ⟶ ModuleCat.of R M :=
    F.descOpcycles (π.f 0 ≫ singleX.hom) 1 (by simp) hcomp_zero
  have hdesc_eq :
      desc =
        (ChainComplex.isoHomologyι₀ F).inv ≫
          HomologicalComplex.homologyMap π 0 ≫
            ((ChainComplex.isoHomologyι₀ (moduleSingle[R] M)) ≪≫
              HomologicalComplex.singleObjOpcyclesSelfIso
                (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).hom := by
    -- Route correction: identify the descended opcycles map with the quasi-isomorphism on `H₀`
    -- followed by the canonical `H₀(single₀ M) ≅ M` comparison.
    apply (cancel_epi (F.homologyι 0)).1
    calc
      F.homologyι 0 ≫ desc =
        F.homologyι 0 ≫
          HomologicalComplex.opcyclesMap π 0 ≫
            (HomologicalComplex.singleObjOpcyclesSelfIso
              (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).inv := by
              rw [single0_opcycles_self_inv_eq_descOpcycles (R := R) (ModuleCat.of R M)]
              simpa [desc, Category.assoc] using
                (HomologicalComplex.opcyclesMap_comp_descOpcycles
                  (K := F)
                  (L := moduleSingle[R] M)
                  (φ := π)
                  (i := (0 : ℕ))
                  (k := singleX.hom)
                  (j := 1)
                  (hj := by simp)
                  (hk := single0_objXSelf_comp_d_eq_zero (R := R) (ModuleCat.of R M)))
      _ =
        F.homologyι 0 ≫
          (ChainComplex.isoHomologyι₀ F).inv ≫
            HomologicalComplex.homologyMap π 0 ≫
              (ChainComplex.isoHomologyι₀ (moduleSingle[R] M)).hom ≫
                (HomologicalComplex.singleObjOpcyclesSelfIso
                  (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).inv := by
                    rw [← Category.assoc]
                    simp [ChainComplex.isoHomologyι₀_inv_naturality, Category.assoc]
      _ =
        F.homologyι 0 ≫
          ((ChainComplex.isoHomologyι₀ F).inv ≫
            HomologicalComplex.homologyMap π 0 ≫
              ((ChainComplex.isoHomologyι₀ (moduleSingle[R] M)) ≪≫
                HomologicalComplex.singleObjOpcyclesSelfIso
                  (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).hom) := by
                    simp [Category.assoc]
  have hdescIso : IsIso desc := by
    rw [hdesc_eq]
    infer_instance
  have hdesc_exact_epi :
      Function.Exact (F.d 1 0).hom ((π.f 0 ≫ singleX.hom).hom) ∧ Epi (π.f 0 ≫ singleX.hom) := by
    rw [ChainComplex.isIso_descOpcycles_iff] at hdescIso
    exact hdescIso
  constructor
  · -- Surjectivity is unchanged after composing with the degree-zero identification.
    have hsurjComp : Function.Surjective ((π.f 0 ≫ singleX.hom).hom) :=
      (ModuleCat.epi_iff_surjective _).1 hdesc_exact_epi.2
    intro m
    rcases hsurjComp (singleX.hom.hom m) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply singleX.hom.hom.injective
    simpa [Category.assoc] using hx
  · -- Exactness against an isomorphism in the codomain reduces back to exactness of `π.f 0`.
    intro x hx
    have hxComp : ((π.f 0 ≫ singleX.hom).hom) x = 0 := by
      simpa [Category.assoc] using congrArg singleX.hom.hom hx
    rcases hdesc_exact_epi.1 x hxComp with ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- Helper for Lemma 15.75.14: every syzygy in the chosen finite free resolution is finite. -/
private theorem chosen_resolution_syzygy_finite
    {M : ModuleCat R} {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] M}
    (hπ : ChainComplex.IsFiniteFreeResolution π) :
    let Syz : ℕ → Type u
      | 0 => M
      | 1 => LinearMap.ker (π.f 0).hom
      | n + 2 => LinearMap.ker (F.d (n + 1) n).hom
    ∀ n : ℕ, Module.Finite R (Syz n) := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  intro Syz n
  cases n with
  | zero =>
      -- The zeroth syzygy is the original finite module.
      simpa [Syz]
  | succ n =>
      cases n with
      | zero =>
          -- The first syzygy is a kernel inside the finite free term `F₀`.
          let _ : Module.Finite R (F.X 0) :=
            ChainComplex.IsFiniteFreeResolution.finite (R := R) (π := π) 0
          simpa [Syz] using
            (Module.Finite.of_injective
              (LinearMap.ker (π.f 0).hom).subtype
              (Submodule.injective_subtype (LinearMap.ker (π.f 0).hom)))
      | succ m =>
          -- Higher syzygies are kernels inside the higher finite free terms.
          let _ : Module.Finite R (F.X (m + 1)) :=
            ChainComplex.IsFiniteFreeResolution.finite (R := R) (π := π) (m + 1)
          simpa [Syz] using
            (Module.Finite.of_injective
              (LinearMap.ker (F.d (m + 1) m).hom).subtype
              (Submodule.injective_subtype (LinearMap.ker (F.d (m + 1) m).hom)))

/-- Helper for Lemma 15.75.14: over a regular ring, a finite module admits a bounded finite
projective resolution with finite terms. -/
-- TODO: follow the source proof route via a finite free resolution, the ascending free loci of the
-- successive syzygies, and Noetherian stabilization to produce one globally finite projective
-- syzygy. That stabilized syzygy then truncates the resolution to a bounded finite-projective one.
lemma finite_module_has_finite_projective_resolution_of_regularRing
    (M : ModuleCat R) [Module.Finite R M] :
    ∃ d : ℕ, HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d := by
  classical
  -- Route correction: the missing input is not a uniform global-dimension bound on `R`, but the
  -- source-faithful stabilization of the free loci of the syzygies of one chosen finite free
  -- resolution of `M`.
  rcases module_exists_finite_free_resolution (R := R) (M := M) with ⟨F, π, hπ⟩
  let Syz : ℕ → Type u
    | 0 => M
    | 1 => LinearMap.ker (π.f 0).hom
    | n + 2 => LinearMap.ker (F.d (n + 1) n).hom
  let U : ℕ → Set (PrimeSpectrum R) := fun n ↦ Module.freeLocus R (Syz n)
  have hSyzFinite : ∀ n : ℕ, Module.Finite R (Syz n) := by
    -- The finite-term owner gives finiteness of each ambient free term, hence of each syzygy.
    simpa [Syz] using chosen_resolution_syzygy_finite (R := R) (π := π) hπ
  -- TODO: localize the chosen resolution at each prime, use regularity of `R_p` to obtain a
  -- projective syzygy, and then upgrade that local freeness to a basic-open neighborhood inside
  -- the corresponding free locus.
  have hbasic :
      ∀ p : PrimeSpectrum R, ∃ n : ℕ, ∃ f : R,
        p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∧
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ U n := sorry
  -- TODO: localizing the short exact sequence
  -- `0 → Syz (n + 1) → F_{n+1} → Syz n → 0`
  -- should show that the free loci are monotone in `n`.
  have hmono : Monotone U := sorry
  obtain ⟨N, hUN⟩ := exists_uniform_index_of_basicOpen_cover (R := R) U hmono hbasic
  -- TODO: `U N = Set.univ` means the stabilized syzygy `Syz N` is globally free. The remaining
  -- source-faithful step is to truncate the chosen finite free resolution at that stage and read
  -- the resulting bounded finite-projective resolution of `M`.
  have hfiniteProjective :
      Module.Finite R (Syz N) ∧ Module.Projective R (Syz N) := by
    -- Global freeness of the stabilized syzygy implies finite projectivity by Lemma `10.78.2`.
    let _ : Module.Finite R (Syz N) := hSyzFinite N
    let _ : Module.FinitePresentation R (Syz N) := Module.finitePresentation_of_finite R (Syz N)
    exact ((module_finite_projective_tfae (R := R) (M := Syz N)).out 3 1).mp
      ⟨inferInstance, hUN⟩
  letI : ChainComplex.IsFreeResolution π := hπ
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := M) (π := π)
  have hNthSyzygyProjective : P.SyzygyProjective N := by
    -- The `N`th syzygy in the projective resolution attached to `π` is exactly `Syz N`.
    cases N with
    | zero =>
        let _ : Module.Projective R M := by
          simpa [Syz] using hfiniteProjective.2
        simpa [P, CategoryTheory.ProjectiveResolution.SyzygyProjective, Syz]
    | succ n =>
        cases n with
        | zero =>
            let _ : Module.Projective R (LinearMap.ker (π.f 0).hom) := by
              simpa [Syz] using hfiniteProjective.2
            simpa [P, CategoryTheory.ProjectiveResolution.SyzygyProjective, Syz]
        | succ m =>
            let _ : Module.Projective R (LinearMap.ker (F.d (m + 1) m).hom) := by
              simpa [Syz] using hfiniteProjective.2
            simpa [P, CategoryTheory.ProjectiveResolution.SyzygyProjective, Syz]
  have hpd : HasProjectiveDimensionLE M N :=
    (projectiveDimensionLE_tfae_resolution_conditions (M := M) N).out 2 0 ⟨P, hNthSyzygyProjective⟩
  -- The finite-projective-dimension owner now converts to the requested finite-term resolution.
  exact ⟨N, (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    (R := R) (M := M) N).mp hpd⟩

-- Proof sketch: for the forward implication, unwind perfection to a bounded finite-projective
-- representative and note that its degree-zero homology is finite over the Noetherian ring `R`.
-- For the converse, apply Lemma `15.75.3` together with regularity of `R` to obtain a finite
-- projective resolution of a finite module, hence a perfect representative.
/-- Lemma 15.75.14 (1): over a regular ring `R`, an `R`-module is perfect if and only if it is a
finite `R`-module. -/
theorem isPerfect_iff_finite (M : ModuleCat R) :
    M.IsPerfect ↔ Module.Finite R M := by
  constructor
  · intro hM
    rcases
        (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms M).1 hM
      with ⟨d, hd⟩
    cases d with
    | zero =>
        -- In degree `0`, the finite-projective resolution condition already records finiteness.
        exact hd.2
    | succ n =>
        rcases hd with ⟨P, δ, π, hπ, _, _, _⟩
        -- A surjection from the finite projective term `P₀` forces `M` to be finite.
        exact Module.Finite.of_surjective π.hom hπ
  · intro hM
    -- The remaining source-faithful input is the bounded finite-projective resolution from the
    -- helper above; Lemma `15.75.3` then turns that resolution into perfection.
    let _ : Module.Finite R M := hM
    rcases finite_module_has_finite_projective_resolution_of_regularRing M with ⟨d, hd⟩
    exact
      (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms M).2
        ⟨d, hd⟩

end ModuleCat

/-- Helper for Lemma 15.75.14: a bounded finite-projective representative gives a bounded object of
`D(R)`. -/
lemma q_obj_mem_t_bounded_of_isBoundedFiniteProjective
    (L : CochainComplex (ModuleCat R) ℤ)
    [hL : CochainComplex.IsBoundedFiniteProjective L] :
    Bounded (DerivedCategory.Q.obj L) := by
  -- The support bounds built into `IsBoundedFiniteProjective` are exactly the two `t`-structure
  -- bounds needed for `t.bounded`.
  rcases hL.bounded with ⟨a, b, hGE, hLE⟩
  change (∃ n, (DerivedCategory.Q.obj L).IsGE n) ∧ ∃ n, (DerivedCategory.Q.obj L).IsLE n
  constructor
  · refine ⟨a, ?_⟩
    rw [DerivedCategory.isGE_Q_obj_iff]
    let _ : L.IsStrictlyGE a := hGE
    infer_instance
  · refine ⟨b, ?_⟩
    rw [DerivedCategory.isLE_Q_obj_iff]
    let _ : L.IsStrictlyLE b := hLE
    infer_instance

/-- Helper for Lemma 15.75.14: every homology module of a bounded finite-projective complex is
finite. -/
lemma homology_finite_of_isBoundedFiniteProjective
    (L : CochainComplex (ModuleCat R) ℤ)
    [hL : CochainComplex.IsBoundedFiniteProjective L] (i : ℤ) :
    Module.Finite R (L.homology i) := by
  have hcycles : Module.Finite R (L.cycles i) := by
    let _ : Module.Finite R (L.X i) := hL.finite i
    exact Module.Finite.of_injective
      (L.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  let _ : Module.Finite R (L.cycles i) := hcycles
  exact Module.Finite.of_surjective
    (L.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Helper for Lemma 15.75.14: a perfect derived object is bounded and has finite cohomology
modules. -/
lemma perfect_bounded_and_finite_homology
    (K : DMod) (hK : K.IsPerfect) :
    Bounded K ∧
      ∀ i : ℤ, Module.Finite R ((H^i).obj K) := by
  rcases hK with ⟨L, e, hL⟩
  constructor
  · -- A bounded finite-projective representative supplies both `t`-structure bounds on `K`.
    rcases hL.bounded with ⟨a, b, hGE, hLE⟩
    change (∃ n, K.IsGE n) ∧ ∃ n, K.IsLE n
    constructor
    · refine ⟨a, ?_⟩
      have hQ : (DerivedCategory.Q.obj L).IsGE a := by
        rw [DerivedCategory.isGE_Q_obj_iff]
        let _ : L.IsStrictlyGE a := hGE
        infer_instance
      let _ : (DerivedCategory.Q.obj L).IsGE a := hQ
      exact t.isGE_of_iso e.symm a
    · refine ⟨b, ?_⟩
      have hQ : (DerivedCategory.Q.obj L).IsLE b := by
        rw [DerivedCategory.isLE_Q_obj_iff]
        let _ : L.IsStrictlyLE b := hLE
        infer_instance
      let _ : (DerivedCategory.Q.obj L).IsLE b := hQ
      exact t.isLE_of_iso e.symm b
  · -- Derived homology is computed on the bounded finite-projective representative.
    intro i
    have hLhomology : Module.Finite R (L.homology i) :=
      homology_finite_of_isBoundedFiniteProjective (R := R) L i
    have hQ : Module.Finite R ((H^i).obj (DerivedCategory.Q.obj L)) := by
      let eQ : ((H^i).obj (DerivedCategory.Q.obj L)) ≅ L.homology i :=
        CochainComplex.derived_homology_iso (R := R) L i
      let _ : Module.Finite R (L.homology i) := hLhomology
      exact Module.Finite.of_surjective
        eQ.symm.toLinearEquiv.toLinearMap
        eQ.symm.toLinearEquiv.surjective
    let eH : ((H^i).obj (DerivedCategory.Q.obj L)) ≅ ((H^i).obj K) := (H^i).mapIso e.symm
    exact Module.Finite.of_surjective
      eH.toLinearEquiv.toLinearMap
      eH.toLinearEquiv.surjective

-- Proof sketch: if `K` is perfect, represent it by a bounded complex of finite projective
-- modules; this gives bounded cohomology and finite homology modules. Conversely, if `K` lies in
-- `D^b(R)` with finite cohomology, apply part `(1)` degreewise to see that each `H^i(K)` is a
-- perfect module, then use Lemma `15.75.7` to recover perfection of `K`.
/-- Lemma 15.75.14 (2): over a regular ring `R`, a derived `R`-complex is perfect if and only if
it belongs to `D^b(R)` and each cohomology module is finite. -/
theorem isPerfect_iff_bounded_and_finite_homology
    (K : DMod) :
    K.IsPerfect ↔
      Bounded K ∧
        ∀ i : ℤ, Module.Finite R ((H^i).obj K) := by
  constructor
  · intro hK
    exact perfect_bounded_and_finite_homology (R := R) K hK
  · rintro ⟨hKbounded, hHfinite⟩
    -- Package `K` as a bounded-derived object so that Lemma `15.75.7` applies directly.
    let Kb : CategoryTheory.boundedDerivedCategory (ModuleCat R) := ⟨K, hKbounded⟩
    have hHperfect :
        ∀ i : ℤ,
          ((CategoryTheory.boundedDerivedHomologyFunctor (ModuleCat R) i).obj Kb).IsPerfect := by
      intro i
      -- Route correction: first convert degreewise finiteness to module perfectness via part `(1)`,
      -- then rewrite bounded-derived homology back to the ambient `H^i(K)`.
      simpa [Kb, CategoryTheory.boundedDerivedHomologyFunctor] using
        ((ModuleCat.isPerfect_iff_finite (R := R) ((H^i).obj K)).2 (hHfinite i))
    -- Lemma `15.75.7` upgrades perfect cohomology on the bounded object to perfectness of `K`.
    exact CategoryTheory.isPerfect_of_bounded_of_homology_isPerfect (R := R) Kb hHperfect

end
