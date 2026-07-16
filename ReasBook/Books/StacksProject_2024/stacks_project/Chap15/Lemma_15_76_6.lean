import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_8
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_3_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_12
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_17
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open IsLocalRing
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "κ" => ResidueField R
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModκ" => DerivedCategory (ModuleCat κ)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "KModR" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "KModκ" => HomotopyCategory (ModuleCat κ) (ComplexShape.up ℤ)
local notation "QisR" => HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)
local notation "QhR" => (DerivedCategory.Qh : KModR ⥤ DModR)
local notation "Qhκ" => (DerivedCategory.Qh : KModκ ⥤ DModκ)
local notation "FiniteFreeClass" => (fun M : ModuleCat R ↦ Module.Free R M ∧ Module.Finite R M)
local notation "BoundedFiniteFreeCpx" => CochainComplex.MinusWithTermsIn FiniteFreeClass
local notation "ReduceCpx" =>
  (Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R)))
    (ComplexShape.up ℤ))

/-- Helper for Lemma 15.76.6: the quotient functor from cochain complexes to the homotopy
category. -/
private abbrev HoQ : CpxR ⥤ HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/- Domain-style sampling for Lemma 15.76.6:
- primary domain: pseudo-coherent derived complexes over a local ring and bounded-above finite-free
  representatives controlled by residue-field homology;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CochainComplex.MinusWithTermsIn`,
  `exists_boundedAbove_termwiseFiniteFree_quasiIso`;
- best owner abstraction: the bounded-above finite-free model should be carried by the existing
  owner `CochainComplex.MinusWithTermsIn FiniteFreeClass`, while the source-facing residue-field
  homology and prescribed rank function remain bridge data on top of that owner;
- primitive vs. derived:
  primitive data are the derived residue-field homology objects and the rank function `d : ℤ → ℕ`;
  derived API is the existence and uniqueness of owner-level bounded-above finite-free models with
  those prescribed ranks;
- source/core/bridge triage:
  `source-facing`: the three clauses of Lemma `15.76.6`;
  `core/canonical`: `K.IsPseudoCoherent`, `CochainComplex.MinusWithTermsIn`, and
    `CochainComplex.IsTermwiseFiniteFree`;
  `bridge/view`: `residueFieldDerivedHomology` and the pointwise rank condition on the owner
    complex terms.
-/

/-- The degree-`i` homology of the derived residue-field base change `K ⊗_R^L κ`. -/
abbrev residueFieldDerivedHomology (K : DModR) (i : ℤ) : ModuleCat κ :=
  (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj (K ⊗[R]^L[κ])

/-- Helper for Lemma 15.76.6: a module linearly equivalent to a finite coordinate module is finite
free. -/
lemma module_free_and_finite_of_nonempty_linearEquiv_fin
    {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (hM : Nonempty (M ≃ₗ[R] (Fin n → R))) :
    Module.Free R M ∧ Module.Finite R M := by
  rcases hM with ⟨e⟩
  constructor
  · -- Proof comment: transport the standard freeness of `R^n` across the chosen linear
    -- equivalence.
    exact Module.Free.of_equiv e.symm
  · -- Proof comment: finite generation is likewise invariant under linear equivalence.
    exact Module.Finite.equiv e.symm

/-- Helper for Lemma 15.76.6: conjugating a homotopy-category morphism through
`DerivedCategory.quotientCompQhIso` recovers its `DerivedCategory.Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {E K : CpxR} (f : E ⟶ K) :
    (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K))
      (DerivedCategory.Qh.map (HoQ.map f)) =
        DerivedCategory.Q.map f := by
  -- Proof comment: this is the naturality square for the comparison iso
  -- `quotient ⋙ Qh ≅ Q`, rewritten on Hom-sets.
  change
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        DerivedCategory.Qh.map (HoQ.map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map (HoQ.map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
        (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app E ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f
  calc
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        DerivedCategory.Qh.map (HoQ.map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app E ≫
          DerivedCategory.Q.map f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫ k)
                hnat
    _ = DerivedCategory.Q.map f := by
      simpa using
        (Iso.inv_hom_id_assoc
          ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
          (DerivedCategory.Q.map f))

-- Proof sketch: apply pseudo-coherence preservation under derived tensoring with the residue field,
-- then use the standard characterization of pseudo-coherent derived complexes over the field `κ`,
-- where every pseudo-coherent object is represented by a bounded-above complex of finite free
-- `κ`-modules. Such a complex has finite-dimensional homology in each degree and vanishes in all
-- sufficiently large degrees.
/-- Lemma 15.76.6 (1): if `K` is pseudo-coherent over the local ring `R`, then the cohomology of
`K ⊗_R^L κ` is finite-dimensional over the residue field `κ` in every degree and vanishes in
sufficiently large degrees. -/
theorem residueFieldDerivedHomology_finiteDimensional_and_eventually_isZero_of_isPseudoCoherent
    (K : DModR) (hK : K.IsPseudoCoherent) :
    (∀ i : ℤ, FiniteDimensional κ (residueFieldDerivedHomology K i)) ∧
      ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (residueFieldDerivedHomology K i) := by
  -- Proof comment: pseudo-coherence survives derived base change to the residue field.
  have hKκ : (K ⊗[R]^L[κ]).IsPseudoCoherent :=
    derivedTensorWithAlgebra_isPseudoCoherent K hK
  have hchar :=
    (isPseudoCoherent_iff_boundedAbove_and_homology_finite
      (R := κ) (K := K ⊗[R]^L[κ])).1 hKκ
  constructor
  · intro i
    -- Proof comment: over the field `κ`, finite modules are exactly finite-dimensional vector
    -- spaces.
    let _ : Module.Finite κ (residueFieldDerivedHomology K i) := hchar.2 i
    infer_instance
  · -- Proof comment: the bounded-above conclusion is precisely eventual vanishing of homology.
    obtain ⟨b, hb⟩ := (derivedCategory_t_minus_iff (K := K ⊗[R]^L[κ])).1 hchar.1
    refine ⟨b, ?_⟩
    intro i hi
    exact hb i hi

/-- Helper for Lemma 15.76.6: the prescribed ranks vanish in high degrees because the residue-field
homology modules vanish there. -/
lemma prescribed_ranks_eventually_zero
    (K : DModR) (hK : K.IsPseudoCoherent) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ))) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → d i = 0 := by
  obtain ⟨_, ⟨b, hb⟩⟩ :=
    residueFieldDerivedHomology_finiteDimensional_and_eventually_isZero_of_isPseudoCoherent
      (K := K) hK
  refine ⟨b, ?_⟩
  intro i hi
  rcases hd i with ⟨e⟩
  let _ : Subsingleton (residueFieldDerivedHomology K i) :=
    ModuleCat.subsingleton_of_isZero (hb i hi)
  have hsub : Subsingleton (Fin (d i) → κ) := e.symm.toEquiv.subsingleton
  by_contra hdi
  have hpos : 0 < d i := Nat.pos_of_ne_zero hdi
  let z : Fin (d i) := ⟨0, hpos⟩
  have hneq :
      (0 : Fin (d i) → κ) ≠ fun j ↦ if j = z then 1 else 0 := by
    intro hfun
    have hz := congrFun hfun z
    simp [z] at hz
  -- Proof comment: if `d i > 0`, the coordinate module has two distinct vectors, contradicting
  -- the transported subsingleton structure.
  exact hneq (hsub.elim _ _)

/-- Helper for Lemma 15.76.6: conjugating an injective linear map by linear equivalences preserves
injectivity. -/
lemma injective_of_conjugate_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'}
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B')
    (hconj : g ∘ₗ eA = eB ∘ₗ f)
    (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply eA.symm.injective
  apply hf
  apply eB.injective
  calc
    eB (f (eA.symm x)) = g x := by
      simpa using (LinearMap.congr_fun hconj (eA.symm x)).symm
    _ = g y := hxy
    _ = eB (f (eA.symm y)) := by
      simpa using LinearMap.congr_fun hconj (eA.symm y)

/-- Helper for Lemma 15.76.6: on zero-differential cochain complexes, homotopic maps are equal. -/
lemma eq_of_homotopy_of_differential_eq_zero
    {A : Type*} [CommRing A]
    {E F : CochainComplex (ModuleCat A) ℤ} {f g : E ⟶ F}
    (hE : ∀ i : ℤ, E.d i (i + 1) = 0)
    (hF : ∀ i : ℤ, F.d i (i + 1) = 0)
    (hfg : Homotopy f g) :
    f = g := by
  ext i x
  -- Proof comment: in the homotopy commutator formula, both correction terms contain a zero
  -- differential, so only the original map survives.
  calc
    (f.f i).hom x = ((dNext i hfg.hom + prevD i hfg.hom + g.f i).hom) x := by
      simpa using congrArg (fun φ : E.X i ⟶ F.X i ↦ φ.hom x) (hfg.comm i)
    _ = (g.f i).hom x := by
      have hdNext : dNext i hfg.hom = 0 := by
        rw [dNext_eq (f := hfg.hom) (i := i) (i' := i + 1) (w := by simp)]
        simp [hE i]
      have hPrevD : prevD i hfg.hom = 0 := by
        simp [prevD, hF (i - 1)]
      simp [hdNext, hPrevD]

/-- Helper for Lemma 15.76.6: if the incoming and outgoing differentials at degree `i` both
vanish, then the degree-`i` term identifies canonically with degree-`i` homology. -/
noncomputable lemma term_iso_homology_of_differential_eq_zero
    {k : Type*} [Field k]
    {E : CochainComplex (ModuleCat k) ℤ} (i : ℤ)
    (hprev : E.d (i - 1) i = 0)
    (hnext : E.d i (i + 1) = 0) :
    E.X i ≅ E.homology i := by
  let hprev' : (ComplexShape.up ℤ).prev i = i - 1 := by
    simpa using (CochainComplex.prev ℤ i)
  let hnext' : (ComplexShape.up ℤ).next i = i + 1 := by
    simpa [add_assoc] using (CochainComplex.next ℤ i)
  let S : ShortComplex (ModuleCat k) := E.sc' (i - 1) i (i + 1)
  let eKernel :
      S.cycles ≅ ModuleCat.of k (LinearMap.ker (E.d i (i + 1)).hom) := by
    -- Proof comment: on the owner short complex, cycles are exactly the kernel of the outgoing
    -- differential.
    simpa [S, hnext'] using
      (S.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer S.g)
  let hker :
      LinearMap.ker (E.d i (i + 1)).hom = ⊤ := by
    -- Proof comment: the outgoing differential is zero, so every vector lies in the kernel.
    ext x
    simp [hnext', hnext]
  let eTop :
      ModuleCat.of k (LinearMap.ker (E.d i (i + 1)).hom) ≅ E.X i :=
    ((LinearEquiv.ofEq _ _ hker).trans Submodule.topEquiv).toModuleIso
  let eCycles :
      E.X i ≅ S.cycles :=
    (eKernel ≪≫ eTop).symm
  have htoCycles_zero : S.toCycles = 0 := by
    -- Proof comment: the incoming differential is zero, so no nontrivial boundaries reach degree
    -- `i`.
    ext x
    simp [S, hprev', hprev]
  let inv : S.homology ⟶ S.cycles :=
    S.descHomology (𝟙 S.cycles) (by
      -- Proof comment: once boundaries vanish, the identity on cycles descends to homology.
      simpa [S] using htoCycles_zero)
  have hπinv : S.homologyπ ≫ inv = 𝟙 S.cycles := by
    -- Proof comment: this is the defining computation rule for `descHomology`.
    exact
      ShortComplex.π_descHomology (S := S) (k := 𝟙 S.cycles)
        (hk := by simpa [S] using htoCycles_zero)
  let eShort : S.cycles ≅ S.homology :=
    { hom := S.homologyπ
      inv := inv
      hom_inv_id := hπinv
      inv_hom_id := by
        -- Proof comment: `homologyπ` is epi, so a left inverse is automatically two-sided.
        apply (cancel_epi S.homologyπ).1
        calc
          S.homologyπ ≫ (inv ≫ S.homologyπ) = (S.homologyπ ≫ inv) ≫ S.homologyπ := by
            simp [Category.assoc]
          _ = 𝟙 S.cycles ≫ S.homologyπ := by
            rw [hπinv]
          _ = S.homologyπ := by
            simp
          _ = S.homologyπ ≫ 𝟙 S.homology := by
            simp }
  -- Proof comment: pass from the ambient degree term to the owner short-complex cycles, identify
  -- those cycles with short-complex homology, and then return to ambient homology.
  exact
    eCycles ≪≫
      eShort ≪≫
      (E.homologyIsoSc' (i - 1) i (i + 1) hprev' hnext').symm

/-- Helper for Lemma 15.76.6: over a field, equality of term dimensions and homology dimensions
forces every differential to vanish. -/
lemma differential_eq_zero_of_term_finrank_eq_homology_finrank_over_field
    {k : Type*} [Field k]
    {E : CochainComplex (ModuleCat k) ℤ}
    (hfinrank : ∀ i : ℤ, Module.finrank k (E.X i) = Module.finrank k (E.homology i)) :
    ∀ i : ℤ, E.d i (i + 1) = 0 := by
  intro i
  let S : ShortComplex (ModuleCat k) := E.sc i
  have hker_range :
      Module.finrank k (LinearMap.ker S.g.hom) +
          Module.finrank k (LinearMap.range S.g.hom) =
        Module.finrank k (E.X i) := by
    -- Proof comment: the degree-`i` term splits as kernel plus image of the outgoing
    -- differential.
    simpa [S, add_comm] using LinearMap.finrank_range_add_finrank_ker S.g.hom
  let eHomology :
      S.moduleCatLeftHomologyData.leftHomology ≅ E.homology i :=
    S.moduleCatLeftHomologyData.leftHomologyIso ≪≫ (S.moduleCatHomologyIso).symm
  have hquot :
      Module.finrank k (E.homology i) +
          Module.finrank k (LinearMap.range S.moduleCatToCycles) =
        Module.finrank k (LinearMap.ker S.g.hom) := by
    -- Proof comment: the homology is the quotient of cycles by boundaries, so quotient finrank
    -- plus boundary finrank recovers the cycle finrank.
    have hleft :
        Module.finrank k S.moduleCatLeftHomologyData.leftHomology =
          Module.finrank k (LinearMap.ker S.g.hom) -
            Module.finrank k (LinearMap.range S.moduleCatToCycles) := by
      simpa [S] using
        (Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles))
    have hleft' :
        Module.finrank k (E.homology i) =
          Module.finrank k S.moduleCatLeftHomologyData.leftHomology := by
      simpa using eHomology.toLinearEquiv.finrank_eq.symm
    omega
  have hsum :
      Module.finrank k (LinearMap.range S.g.hom) +
          Module.finrank k (LinearMap.range S.moduleCatToCycles) = 0 := by
    -- Proof comment: subtract the common cycle dimension from the term and homology finrank
    -- formulas.
    omega
  have hRangeZero : Module.finrank k (LinearMap.range S.g.hom) = 0 := by
    omega
  have hSubsingleton : Subsingleton (LinearMap.range S.g.hom) := by
    exact (Module.finrank_eq_zero_iff k).1 hRangeZero
  have hMapZero : S.g.hom = 0 := by
    ext x
    have hx : S.g.hom x = 0 := hSubsingleton.elim _ _
    simpa using hx
  -- Proof comment: a linear map with zero image is the zero differential.
  ext x
  exact LinearMap.congr_fun hMapZero x

/-- Helper for Lemma 15.76.6: bounded-above termwise finite free complexes are termwise flat. -/
lemma termwiseFlat_of_boundedFiniteFree
    (P : BoundedFiniteFreeCpx) :
    (P : CpxR).IsTermwiseFlat := by
  intro i
  rcases P.term_mem i with ⟨hfree, _⟩
  let _ : Module.Free R ((P : CpxR).X i) := hfree
  -- Proof comment: free modules are flat, so the chosen bounded-above finite-free model computes
  -- derived tensor termwise.
  infer_instance

/-- Helper for Lemma 15.76.6: a bounded-above termwise-flat complex is `K`-flat, so it computes
derived reduction by the residue field. -/
private theorem isKFlat_of_termwiseFlat_of_isStrictlyLE
    {E : CpxR} (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    E.IsKFlat := by
  have hminus : CochainComplex.minus (ModuleCat R) E :=
    (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hLE⟩
  -- Proof comment: the canonical bounded-above-flat criterion upgrades the strict model to a
  -- `K`-flat complex.
  exact CochainComplex.isKFlat_of_boundedAbove_of_flat E hminus hE

/-- Helper for Lemma 15.76.6: this is the explicit counit comparison from the derived
residue-field reduction of a strict cochain model to its literal termwise reduction. -/
private noncomputable def derivedTensorWithResidueField_complexComparison
    (E : CpxR) :
    ((derivedTensorWithAlgebra (algebraMap R κ)).obj (DerivedCategory.Q.obj E)) ⟶
      DerivedCategory.Q.obj (ReduceCpx.obj E) :=
  let F₀ : ModuleCat R ⥤ ModuleCat κ := ModuleCat.extendScalars (algebraMap R κ)
  letI : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R κ)).left_adjoint_additive
  let F : KModR ⥤ DModκ := F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qhκ
  letI : F.HasLeftDerivedFunctor QisR := by
    change
      ((ModuleCat.extendScalars (algebraMap R κ)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        Qhκ).HasLeftDerivedFunctor QisR
    simpa using extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap R κ)
  -- Proof comment: compose the total-left-derived counit with the canonical comparison from
  -- scalar extension on homotopy complexes to strict reduction on cochain complexes.
  (derivedTensorWithAlgebra (algebraMap R κ)).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E).inv ≫
    (F.totalLeftDerivedCounit QhR QisR).app
      ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj E) ≫
    Qhκ.map
      ((Functor.mapHomotopyCategoryFactors
        (ModuleCat.extendScalars (algebraMap R κ)) (ComplexShape.up ℤ)).inv.app E) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat κ)).app
      (ReduceCpx.obj E)).hom

/-- Helper for Lemma 15.76.6: a bounded-above termwise-flat cochain model computes derived
reduction through the explicit comparison morphism. -/
private theorem derivedTensorWithResidueField_complexComparison_isIso_of_termwiseFlat_of_isStrictlyLE
    {E : CpxR} (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    IsIso (derivedTensorWithResidueField_complexComparison (R := R) E) := by
  let F₀ : ModuleCat R ⥤ ModuleCat κ := ModuleCat.extendScalars (algebraMap R κ)
  letI : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R κ)).left_adjoint_additive
  let F : KModR ⥤ DModκ := F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qhκ
  let qE : KModR := (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj E
  letI : F.HasLeftDerivedFunctor QisR := by
    change
      ((ModuleCat.extendScalars (algebraMap R κ)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        Qhκ).HasLeftDerivedFunctor QisR
    simpa using extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap R κ)
  letI : E.IsKFlat := isKFlat_of_termwiseFlat_of_isStrictlyLE (R := R) hE hLE
  letI : F.ComputesLeftDerivedAt QisR qE := by
    infer_instance
  letI : IsIso ((F.totalLeftDerivedCounit QhR QisR).app qE) :=
    (Functor.computesLeftDerivedAt_iff (F := F) (S := QisR) (X := qE)).1 inferInstance
  -- Proof comment: all other factors in the explicit comparison are canonical isomorphisms, so
  -- invertibility reduces to the counit component.
  simpa [derivedTensorWithResidueField_complexComparison, F, F₀, qE]

/-- Helper for Lemma 15.76.6: the explicit derived residue-field comparison is natural for strict
maps of cochain complexes. -/
private theorem derivedTensorWithResidueField_complexComparison_naturality
    {E L : CpxR} (β : E ⟶ L) :
    (derivedTensorWithAlgebra (algebraMap R κ)).map (DerivedCategory.Q.map β) ≫
        derivedTensorWithResidueField_complexComparison (R := R) L =
      derivedTensorWithResidueField_complexComparison (R := R) E ≫
        DerivedCategory.Q.map (ReduceCpx.map β) := by
  -- TODO: expand the explicit counit comparison, use naturality of `Functor.totalLeftDerivedCounit`
  -- on `(HomotopyCategory.quotient _ _).map β`, and then rewrite the source and target comparison
  -- factors through `DerivedCategory.quotientCompQhIso` and `Functor.mapHomotopyCategoryFactors`.
  sorry

/-- Helper for Lemma 15.76.6: a bounded-above termwise free representative computes residue-field
homology by strict reduction of the representative. -/
lemma residueFieldReduction_homology_iso_of_termwiseFree_representative
    (K : DModR) (P : BoundedFiniteFreeCpx)
    (eK : K ≅ DerivedCategory.Q.obj (P : CpxR)) (i : ℤ) :
    ((ReduceCpx.obj (P : CpxR)).homology i) ≅ residueFieldDerivedHomology K i := by
  obtain ⟨b, hP_le⟩ := P.exists_isStrictlyLE
  have hP_flat : (P : CpxR).IsTermwiseFlat :=
    termwiseFlat_of_boundedFiniteFree (R := R) P
  have hCompute :
      ((DerivedCategory.Q.obj (P : CpxR)) ⊗[R]^L[κ]) ≅
        DerivedCategory.Q.obj (ReduceCpx.obj (P : CpxR)) := by
    -- Proof comment: the bounded-above finite-free representative computes derived tensor with
    -- the residue field termwise.
    simpa [ReduceCpx] using
      (derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
        (A := R) (B := κ) (E := (P : CpxR)) hP_flat hP_le)
  let eReduce :
      (K ⊗[R]^L[κ]) ≅ DerivedCategory.Q.obj (ReduceCpx.obj (P : CpxR)) :=
    (derivedTensorWithAlgebra (algebraMap R κ)).mapIso eK ≪≫ hCompute
  let eFactors :
      ((ReduceCpx.obj (P : CpxR)).homology i) ≅
        (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
          (DerivedCategory.Q.obj (ReduceCpx.obj (P : CpxR))) :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat κ) i).app (ReduceCpx.obj (P : CpxR))
  -- Proof comment: now conjugate strict homology of the reduced complex to the textbook
  -- `residueFieldDerivedHomology`.
  exact eFactors ≪≫ (DerivedCategory.homologyFunctor (ModuleCat κ) i).mapIso eReduce.symm

/-- Helper for Lemma 15.76.6: strict reduction to the residue field preserves the finite rank of
each finite free term. -/
lemma residueFieldReduction_term_finrank_eq
    {E : CpxR} (i : ℤ)
    [Module.Free R (E.X i)] [Module.Finite R (E.X i)] :
    Module.finrank κ (((ReduceCpx.obj E).X i : ModuleCat κ)) =
      Module.finrank R (E.X i) := by
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R κ)).obj (ModuleCat.of κ κ)) ≃ₗ[κ] κ :=
    { __ := AddEquiv.refl κ
      map_smul' := fun _ _ ↦ rfl }
  let _ : IsScalarTower R κ
      ↑((ModuleCat.restrictScalars (algebraMap R κ)).obj (ModuleCat.of κ κ)) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  have eTerm :
      (((ReduceCpx.obj E).X i : ModuleCat κ)) ≃ₗ[κ] (κ ⊗[R] (E.X i)) := by
    -- Proof comment: rewrite the reduced term through the canonical tensor-product model.
    simpa [ReduceCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X,
      ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R (E.X i)))
  calc
    Module.finrank κ (((ReduceCpx.obj E).X i : ModuleCat κ)) =
        Module.finrank κ (κ ⊗[R] (E.X i)) :=
      eTerm.finrank_eq
    _ = Module.finrank R (E.X i) :=
      Module.finrank_baseChange (S := R) (R := κ) (M' := E.X i)

/-- Helper for Lemma 15.76.6: strict residue-field reduction preserves finrank for a finite free
`R`-module. -/
lemma residueFieldReduction_module_finrank_eq
    {M : ModuleCat R}
    [Module.Free R M] [Module.Finite R M] :
    Module.finrank κ ((ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R))).obj M) =
      Module.finrank R M := by
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R κ)).obj (ModuleCat.of κ κ)) ≃ₗ[κ] κ :=
    { __ := AddEquiv.refl κ
      map_smul' := fun _ _ ↦ rfl }
  let _ : IsScalarTower R κ
      ↑((ModuleCat.restrictScalars (algebraMap R κ)).obj (ModuleCat.of κ κ)) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  have eTerm :
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R))).obj M) ≃ₗ[κ] (κ ⊗[R] M) := by
    -- Proof comment: rewrite the reduced module through the canonical tensor-product model.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R M))
  calc
    Module.finrank κ ((ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R))).obj M) =
        Module.finrank κ (κ ⊗[R] M) :=
      eTerm.finrank_eq
    _ = Module.finrank R M :=
      Module.finrank_baseChange (S := R) (R := κ) (M' := M)

/-- Helper for Lemma 15.76.6: if a term is free of rank `n`, then its strict residue-field
reduction has `κ`-dimension `n`. -/
lemma reduced_term_finrank_eq_of_term_linearEquiv_fin
    {E : CpxR} (i : ℤ) {n : ℕ}
    (hE : Nonempty ((E.X i) ≃ₗ[R] (Fin n → R))) :
    Module.finrank κ (((ReduceCpx.obj E).X i : ModuleCat κ)) = n := by
  obtain ⟨e⟩ := hE
  let hfreeFinite :=
    module_free_and_finite_of_nonempty_linearEquiv_fin
      (R := R) (M := E.X i) (n := n) ⟨e⟩
  let _ : Module.Free R (E.X i) := hfreeFinite.1
  let _ : Module.Finite R (E.X i) := hfreeFinite.2
  calc
    Module.finrank κ (((ReduceCpx.obj E).X i : ModuleCat κ)) =
        Module.finrank R (E.X i) :=
      residueFieldReduction_term_finrank_eq (R := R) (E := E) i
    _ = Module.finrank R (Fin n → R) := e.finrank_eq
    _ = n := by
      simpa using Module.finrank_fintype_fun_eq_card (R := R) (α := Fin n)

/-- Helper for Lemma 15.76.6: over a field, a finite-dimensional module of finrank `n` is
linearly equivalent to the standard coordinate module of rank `n`. -/
lemma nonempty_linearEquiv_fin_of_finrank_eq_over_field
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {n : ℕ} (hV : Module.finrank k V = n) :
    Nonempty (V ≃ₗ[k] (Fin n → k)) := by
  let b : Module.Basis (Fin n) k V := Module.finBasisOfFinrankEq k V hV
  -- Proof comment: the chosen `Fin n`-indexed basis gives the coordinate equivalence directly.
  exact ⟨b.equivFun⟩

/-- Helper for Lemma 15.76.6: if a finite free module has strict residue-field reduction of
dimension `n`, then the module itself is free of rank `n`. -/
lemma linearEquiv_fin_of_residueFieldReduction_linearEquiv_fin
    {M : ModuleCat R} {n : ℕ}
    [Module.Free R M] [Module.Finite R M]
    (hMκ :
      Nonempty
        (((ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R))).obj M) ≃ₗ[κ]
          (Fin n → κ))) :
    Nonempty (M ≃ₗ[R] (Fin n → R)) := by
  obtain ⟨eκ⟩ := hMκ
  have hfinrankκ :
      Module.finrank κ ((ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R))).obj M) = n := by
    calc
      Module.finrank κ ((ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R))).obj M) =
          Module.finrank κ (Fin n → κ) :=
        eκ.finrank_eq
      _ = n := by
        simpa using Module.finrank_fintype_fun_eq_card (R := κ) (α := Fin n)
  have hfinrankR : Module.finrank R M = n := by
    calc
      Module.finrank R M =
          Module.finrank κ ((ModuleCat.extendScalars (Ideal.Quotient.mk (maximalIdeal R))).obj M) := by
            symm
            exact residueFieldReduction_module_finrank_eq (R := R) (M := M)
      _ = n := hfinrankκ
  obtain ⟨m, ⟨eM⟩⟩ := finite_free_linearEquiv_fin (R := R) (F := M)
  have hm : m = n := by
    calc
      m = Module.finrank R (Fin m → R) := by
        symm
        simpa using Module.finrank_fintype_fun_eq_card (R := R) (α := Fin m)
      _ = Module.finrank R M := by
        symm
        exact eM.finrank_eq
      _ = n := hfinrankR
  subst hm
  -- Proof comment: after matching ranks, the chosen finite-free basis has exactly the requested
  -- cardinality.
  exact ⟨eM⟩

/-- Helper for Lemma 15.76.6: once a bounded-above free representative has the prescribed ranks,
its strict residue-field reduction has zero differential in every degree. -/
lemma reduced_differential_eq_zero_of_prescribed_ranks
    (K : DModR) {P : BoundedFiniteFreeCpx}
    (eP : K ≅ DerivedCategory.Q.obj (P : CpxR))
    (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ)))
    (hP : ∀ i : ℤ, Nonempty (((P : CpxR).X i) ≃ₗ[R] (Fin (d i) → R))) :
    ∀ i : ℤ, (ReduceCpx.obj (P : CpxR)).d i (i + 1) = 0 := by
  have hfinrank :
      ∀ i : ℤ,
        Module.finrank κ (((ReduceCpx.obj (P : CpxR)).X i : ModuleCat κ)) =
          Module.finrank κ ((ReduceCpx.obj (P : CpxR)).homology i) := by
    intro i
    have hterm :
        Module.finrank κ (((ReduceCpx.obj (P : CpxR)).X i : ModuleCat κ)) = d i :=
      reduced_term_finrank_eq_of_term_linearEquiv_fin
        (R := R) (E := (P : CpxR)) i (n := d i) (hP i)
    have hhomology :
        Module.finrank κ ((ReduceCpx.obj (P : CpxR)).homology i) = d i := by
      obtain ⟨eκ⟩ := hd i
      let eReduce :=
        residueFieldReduction_homology_iso_of_termwiseFree_representative
          (R := R) (K := K) (P := P) eP i
      calc
        Module.finrank κ ((ReduceCpx.obj (P : CpxR)).homology i) =
            Module.finrank κ (residueFieldDerivedHomology K i) :=
          eReduce.toLinearEquiv.finrank_eq
        _ = Module.finrank κ (Fin (d i) → κ) := eκ.finrank_eq
        _ = d i := by
          simpa using Module.finrank_fintype_fun_eq_card (R := κ) (α := Fin (d i))
    exact hterm.trans hhomology.symm
  -- Proof comment: over the field `κ`, equal term and homology dimensions force every
  -- differential to vanish.
  exact differential_eq_zero_of_term_finrank_eq_homology_finrank_over_field
    (k := κ) (E := ReduceCpx.obj (P : CpxR)) hfinrank

/-- Helper for Lemma 15.76.6: a bounded-above projective representative admits a strict cochain
map for every derived morphism out of it. -/
lemma exists_cochainMap_of_projectiveMinus_derived_morphism
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {L : CpxR}
    (α : DerivedCategory.Q.obj (P : CpxR) ⟶ DerivedCategory.Q.obj L) :
    ∃ β : (P : CpxR) ⟶ L, DerivedCategory.Q.map β = α := by
  let HoQ := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  let eHom :
      (DerivedCategory.Qh.obj (HoQ.obj (P : CpxR)) ⟶
        DerivedCategory.Qh.obj (HoQ.obj L)) ≃
        (DerivedCategory.Q.obj (P : CpxR) ⟶
          DerivedCategory.Q.obj L) :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        (P : CpxR))
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
  let αh :
      DerivedCategory.Qh.obj (HoQ.obj (P : CpxR)) ⟶
        DerivedCategory.Qh.obj (HoQ.obj L) :=
    eHom.symm α
  -- Proof comment: use the Chapter 13 bounded-above-projective bijection to lift the derived map
  -- to the homotopy category, then descend to a literal cochain map.
  obtain ⟨βh, hβh⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L).surjective
      αh
  obtain ⟨β, rfl⟩ := HoQ.map_surjective βh
  refine ⟨β, ?_⟩
  calc
    DerivedCategory.Q.map β =
        eHom (DerivedCategory.Qh.map (HoQ.map β)) := by
          simpa using quotientCompQhIso_homCongr_map (R := R) (f := β)
    _ = eHom αh := by rw [hβh]
    _ = α := by simp [αh]

/-- Helper for Lemma 15.76.6: two strict maps out of a bounded-above projective complex are
homotopic once they induce the same derived morphism. -/
lemma nonempty_homotopy_of_projectiveMinus_q_map_eq
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {L : CpxR}
    {f g : (P : CpxR) ⟶ L}
    (hfg : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  let HoQ := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  let eHom :
      (DerivedCategory.Qh.obj (HoQ.obj (P : CpxR)) ⟶
        DerivedCategory.Qh.obj (HoQ.obj L)) ≃
        (DerivedCategory.Q.obj (P : CpxR) ⟶
          DerivedCategory.Q.obj L) :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        (P : CpxR))
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
  have hQh :
      DerivedCategory.Qh.map (HoQ.map f) = DerivedCategory.Qh.map (HoQ.map g) := by
    have hfQ :
        eHom (DerivedCategory.Qh.map (HoQ.map f)) = DerivedCategory.Q.map f := by
      simpa using quotientCompQhIso_homCongr_map (R := R) (f := f)
    have hgQ :
        eHom (DerivedCategory.Qh.map (HoQ.map g)) = DerivedCategory.Q.map g := by
      simpa using quotientCompQhIso_homCongr_map (R := R) (f := g)
    apply eHom.injective
    calc
      eHom (DerivedCategory.Qh.map (HoQ.map f)) = DerivedCategory.Q.map f := hfQ
      _ = DerivedCategory.Q.map g := hfg
      _ = eHom (DerivedCategory.Qh.map (HoQ.map g)) := hgQ.symm
  have hquot : HoQ.map f = HoQ.map g := by
    exact
      (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L)
        .injective hQh
  have hzero : HoQ.map (f - g) = 0 := by
    simpa [Functor.map_sub, hquot] using sub_eq_zero.mpr hquot
  rcases (HomotopyCategory.quotient_map_eq_zero_iff (f - g)).1 hzero with ⟨h⟩
  -- Proof comment: a null-homotopy of `f - g` is exactly a homotopy from `f` to `g`.
  refine ⟨?_⟩
  simpa [sub_eq_add_neg, add_assoc] using Homotopy.add h (Homotopy.refl g)

-- Proof sketch: combine part `(1)` with `hd` to deduce that `d i = 0` for all sufficiently large
-- `i`, then choose the zero-differential complex over `κ` with term `κ^{d i}` in degree `i` and
-- identify it with the derived residue-field base change of `K`. Apply the lifting statement of
-- Lemma `15.76.5` at the maximal ideal of the local ring to obtain a bounded-above free
-- `R`-complex representing `K` with the prescribed ranks.
/-- Lemma 15.76.6 (2): if `d i` is the dimension of the degree-`i` residue-field cohomology of
`K`, then `K` is represented by a bounded-above cochain complex whose degree-`i` term is free of
rank `d i`. -/
theorem exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology
    (K : DModR) (hK : K.IsPseudoCoherent) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ))) :
    ∃ P : BoundedFiniteFreeCpx,
      (∀ i : ℤ, Nonempty (((P : CpxR).X i) ≃ₗ[R] (Fin (d i) → R))) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj (P : CpxR)) := by
  -- Route correction: before lifting through Lemma `15.76.5`, the source proof first forces the
  -- prescribed ranks `d i` to vanish above the residue-field homology cutoff.
  obtain ⟨b, hb⟩ := prescribed_ranks_eventually_zero (K := K) hK d hd
  -- TODO: build the bounded-above zero-differential `κ`-complex with term `κ^{d i}` and use the
  -- cutoff `hb` to show it lies in `Minus`. Then identify it with `K ⊗_R^L κ` in `D(κ)` and
  -- apply Lemma `15.76.5` to lift that model through `maximalIdeal R`.
  let _ := hb
  sorry

-- Proof sketch: let `β : P ⟶ Q` be a morphism in the derived category representing the identity of
-- `K`. After tensoring with `κ`, the complexes `P ⊗_R κ` and `Q ⊗_R κ` have zero differentials
-- because their terms already realize the residue-field homology dimensions `d i`. Hence `β ⊗ 1`
-- is degreewise an isomorphism, so each component `β^i` is an isomorphism by Nakayama's lemma for
-- finite free modules over the local ring `R`.
/-- Lemma 15.76.6 (3): a bounded-above free representative of `K` whose degree-`i` term has rank
equal to the dimension of `H^i(K ⊗_R^L κ)` is unique up to isomorphism of complexes. -/
theorem boundedAbove_termwiseFree_representative_unique_of_residueFieldDerivedHomology
    (K : DModR) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ)))
    {P P' : BoundedFiniteFreeCpx}
    (hP : ∀ i : ℤ, Nonempty (((P : CpxR).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hPK : Nonempty (K ≅ DerivedCategory.Q.obj (P : CpxR)))
    (hP' : ∀ i : ℤ, Nonempty (((P' : CpxR).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hP'K : Nonempty (K ≅ DerivedCategory.Q.obj (P' : CpxR))) :
    Nonempty ((P : CpxR) ≅ (P' : CpxR)) := by
  obtain ⟨eP⟩ := hPK
  obtain ⟨eP'⟩ := hP'K
  let α : DerivedCategory.Q.obj (P : CpxR) ≅ DerivedCategory.Q.obj (P' : CpxR) :=
    eP.symm ≪≫ eP'
  let Pproj : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨(P : CochainComplex.MinusWithTermsIn FiniteFreeClass), fun i ↦ by
      -- Proof comment: each free term is projective, so the bounded-above free owner refines to
      -- the bounded-above projective owner used by Lemma `13.19.8`.
      change Projective ((P : CpxR).X i)
      rcases P.term_mem i with ⟨hfree, _⟩
      let _ : Module.Free R ((P : CpxR).X i) := hfree
      infer_instance⟩
  let P'proj : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨(P' : CochainComplex.MinusWithTermsIn FiniteFreeClass), fun i ↦ by
      -- Proof comment: the same projectivity upgrade applies to the second bounded-above free
      -- representative.
      change Projective ((P' : CpxR).X i)
      rcases P'.term_mem i with ⟨hfree, _⟩
      let _ : Module.Free R ((P' : CpxR).X i) := hfree
      infer_instance⟩
  let αh :
      DerivedCategory.Qh.obj (HoQ.obj (P : CpxR)) ⟶
        DerivedCategory.Qh.obj (HoQ.obj (P' : CpxR)) :=
    (Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : CpxR))
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P' : CpxR))).symm α.hom
  -- Proof comment: lift the derived isomorphism back to a strict chain map between the two
  -- bounded-above projective complexes.
  obtain ⟨β, hQβ⟩ :=
    exists_cochainMap_of_projectiveMinus_derived_morphism
      (P := Pproj) (L := (P' : CpxR)) α.hom
  have hReduceHomology :
      ∀ i : ℤ,
        ((ReduceCpx.obj (P : CpxR)).homology i) ≅ residueFieldDerivedHomology K i := by
    intro i
    -- Proof comment: compute residue-field homology on the first bounded-above free model.
    exact residueFieldReduction_homology_iso_of_termwiseFree_representative
      (R := R) (K := K) (P := P) eP i
  have hReduceHomology' :
      ∀ i : ℤ,
        ((ReduceCpx.obj (P' : CpxR)).homology i) ≅ residueFieldDerivedHomology K i := by
    intro i
    -- Proof comment: the same strict reduction comparison holds for the second model.
    exact residueFieldReduction_homology_iso_of_termwiseFree_representative
      (R := R) (K := K) (P := P') eP' i
  have hReduceDifferentialZero :
      ∀ i : ℤ, (ReduceCpx.obj (P : CpxR)).d i (i + 1) = 0 := by
    -- Proof comment: the reduced terms already have the prescribed `κ`-dimensions, so the
    -- reduced complex on `P` has zero differentials.
    exact reduced_differential_eq_zero_of_prescribed_ranks
      (R := R) (K := K) eP d hd hP
  have hReduceDifferentialZero' :
      ∀ i : ℤ, (ReduceCpx.obj (P' : CpxR)).d i (i + 1) = 0 := by
    -- Proof comment: the same dimension argument applies to the second representative.
    exact reduced_differential_eq_zero_of_prescribed_ranks
      (R := R) (K := K) eP' d hd hP'
  -- TODO: reduce `β` modulo `κ`, compare the reduced homology with
  -- `residueFieldDerivedHomology K i` via the bounded-above free-model computation of derived
  -- tensor, use `hReduceDifferentialZero` and `hReduceDifferentialZero'` to identify homotopies
  -- with equalities on the reduced complexes, and then upgrade the resulting quotient
  -- equivalences of the components `β.f i` to actual `R`-linear equivalences by Lemma `15.3.5`.
  let _ := hReduceHomology
  let _ := hReduceHomology'
  let _ := hReduceDifferentialZero
  let _ := hReduceDifferentialZero'
  let _ := hQβ
  sorry

end

end CategoryTheory
