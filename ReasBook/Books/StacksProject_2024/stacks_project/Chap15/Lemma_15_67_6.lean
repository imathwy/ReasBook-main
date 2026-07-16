import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_14
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

section

variable {R : Type u} [CommRing R]

namespace ModuleCat

attribute [local instance] HasDerivedCategory.standard

variable (M : ModuleCat R)

local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: tor dimension of modules over a commutative ring and its source-facing
  description by finite flat resolutions;
- sampled owner declarations:
  `CategoryTheory.ModuleHasTorDimensionLE`,
  `CategoryTheory.hasTorAmplitudeIn_iff_exists_flat_representative`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLE`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the chapter-level core owner remains
  `CategoryTheory.ModuleHasTorDimensionLE`, while the source-facing finite-resolution notion in
  this file should live alongside the analogous projective-resolution owner
  `ModuleCat.HasFiniteProjectiveResolutionLengthLE` rather than as a parallel global predicate;
- primitive vs. derived:
  primitive data are the flat modules `F i`, the differentials `δ`, the augmentation `π`, and the
  exactness/surjectivity/injectivity conditions expressing a finite flat resolution of `M`;
  derived API are the zero-length characterization and the equivalence with tor dimension at most
  `d`.

Source/core/bridge triage:
- `source-facing`: `ModuleCat.HasFiniteFlatResolutionLengthLE`;
- `core/canonical`: `CategoryTheory.ModuleHasTorDimensionLE`;
- `bridge/view`: the bounded flat representative criterion from Lemma `15.67.3`, which explains
  why the source-facing resolution predicate is equivalent to the tor-dimension owner.
-/

/-- A finite flat resolution of an `R`-module `M` of length at most `d`. For `d = 0` this is
just flatness of `M`; for `d = n + 1` it is an exact sequence
`0 ⟶ F_{n + 1} ⟶ F_n ⟶ ⋯ ⟶ F₀ ⟶ M ⟶ 0`
whose terms `Fᵢ` are flat. -/
def HasFiniteFlatResolutionLengthLE (d : ℕ) : Prop :=
  match d with
  | 0 => Module.Flat R M
  | n + 1 =>
      ∃ (F : Fin (n + 2) → ModuleCat R),
        (∀ i, Module.Flat R (F i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → F i.succ ⟶ F i.castSucc)
            (π : F 0 ⟶ M),
            Function.Surjective π ∧
              Function.Exact (δ 0) π ∧
              (∀ i : Fin n, Function.Exact (δ i.succ) (δ i.castSucc)) ∧
              Function.Injective (δ (Fin.last n))

-- Proof sketch: unfold `HasFiniteFlatResolutionLengthLE`; the `d = 0` branch is defined to be
-- flatness of `M`.
/-- A finite flat resolution of length at most `0` is exactly flatness. -/
theorem hasFiniteFlatResolutionLengthLE_zero_iff :
    HasFiniteFlatResolutionLengthLE M 0 ↔ Module.Flat R M :=
  Iff.rfl

/-- Helper for Lemma 15.67.6: enlarging the tor-amplitude interval preserves tor-amplitude. -/
lemma hasTorAmplitudeIn_mono
    {K : DerivedCategory (ModuleCat R)} {a b a' b' : ℤ}
    (hK : CategoryTheory.HasTorAmplitudeIn K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    CategoryTheory.HasTorAmplitudeIn K a' b' := by
  -- Any degree outside the larger interval is already outside the smaller interval.
  intro N i hi
  exact hK N i <| by
    intro hi'
    exact hi ⟨le_trans ha hi'.1, le_trans hi'.2 hb⟩

/-- Helper for Lemma 15.67.6: tor-amplitude is invariant under isomorphism in the derived
category. -/
lemma hasTorAmplitudeIn_of_iso_local
    {K L : DerivedCategory (ModuleCat R)} {a b : ℤ} (e : K ≅ L) :
    CategoryTheory.HasTorAmplitudeIn K a b ↔ CategoryTheory.HasTorAmplitudeIn L a b := by
  constructor
  · intro h N i hi
    exact
      (h N i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
          ((CategoryTheory.derivedTensorProduct ((single₀).obj N)).mapIso e.symm))
  · intro h N i hi
    exact
      (h N i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
          ((CategoryTheory.derivedTensorProduct ((single₀).obj N)).mapIso e))

/-- Helper for Lemma 15.67.6: tensoring on the right with the degree-zero complex on `R` is
canonically the identity on `D(R)`. -/
private noncomputable def regular_single0_derivedTensor_iso_local
    (L : DMod) :
    L ⊗[R]^L (single₀).obj (ModuleCat.of R R) ≅ L := by
  let eUnit :
      (single₀).obj (ModuleCat.of R R) ≅ 𝟙_ (DerivedCategory (ModuleCat R)) :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
        (ModuleCat.of R R)) ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
            (ModuleCat.of R R))).symm
  -- Proof comment: commute the factors, identify `R[0]` with the tensor unit, and apply the
  -- left unitor on `D(R)`.
  exact
    (derivedTensorProduct_comm L ((single₀).obj (ModuleCat.of R R))) ≪≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct
        ((single₀).obj (ModuleCat.of R R)) L).symm ≪≫
        whiskerRightIso eUnit L ≪≫
          λ_ L

/-- Helper for Lemma 15.67.6: a chosen zero module in `ModuleCat R`. -/
private noncomputable abbrev chosen_zero_module : ModuleCat R :=
  Classical.choose (CategoryTheory.Limits.HasZeroObject.zero (C := ModuleCat R))

/-- Helper for Lemma 15.67.6: the chosen zero module is flat. -/
private lemma chosen_zero_module_flat :
    Module.Flat R ((chosen_zero_module (R := R) : ModuleCat R) : Type u) := by
  -- Transport flatness from the concrete zero module on `PUnit`.
  let Z : ModuleCat R := chosen_zero_module (R := R)
  change Module.Flat R ↑Z
  have hZ : CategoryTheory.Limits.IsZero Z :=
    Classical.choose_spec (CategoryTheory.Limits.HasZeroObject.zero (C := ModuleCat R))
  have hP : CategoryTheory.Limits.IsZero (ModuleCat.of R PUnit) :=
    (ModuleCat.isZero_iff_subsingleton).2 inferInstance
  let e : Z ≅ ModuleCat.of R PUnit := hZ.iso hP
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Helper for Lemma 15.67.6: the degree-zero single complex on a flat module is termwise flat. -/
private lemma single_zero_termwiseFlat
    (hFlat : Module.Flat R M) :
    CochainComplex.IsTermwiseFlat
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) := by
  -- Unfold the single complex degreewise and use flatness at degree `0`.
  intro n
  change Module.Flat R
    (((if n = 0 then M else chosen_zero_module (R := R) : ModuleCat R) : ModuleCat R) : Type u)
  by_cases h : n = 0
  · subst n
    simpa using hFlat
  · rw [if_neg h]
    simpa using chosen_zero_module_flat (R := R)

/-- Helper for Lemma 15.67.6: a flat module already gives the bounded flat representative
required by the source proof in degree `0`. -/
private lemma exists_single_zero_flat_representative
    (hFlat : Module.Flat R M) :
    ∃ (E : CochainComplex (ModuleCat R) ℤ),
      ∃ (_ : (single₀).obj M ≅ DerivedCategory.Q.obj E),
        E.IsStrictlyGE 0 ∧ E.IsStrictlyLE 0 ∧ E.IsTermwiseFlat := by
  refine ⟨(CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the degree-zero single complex is the canonical representative of `M[0]`.
    exact ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).symm
  · -- Proof comment: the single complex has no terms below degree `0`.
    infer_instance
  · -- Proof comment: the single complex has no terms above degree `0`.
    infer_instance
  · -- Proof comment: termwise flatness is exactly the input flatness at degree `0`.
    exact single_zero_termwiseFlat (R := R) (M := M) hFlat

/-- Helper for Lemma 15.67.6: a flat module has tor dimension at most `0`. -/
private lemma moduleHasTorDimensionLE_zero_of_flat
    (hFlat : Module.Flat R M) :
    ModuleHasTorDimensionLE M 0 := by
  -- TODO: proving the base case source-faithfully still needs the ordinary-vs-derived tensor
  -- comparison for the degree-zero flat representative. In this workspace the earlier owner file
  -- carrying that bridge does not compile, so the remaining blocker stays isolated here.
  sorry

/-- Helper for Lemma 15.67.6: the derived degree-zero homology of `M[0]` is canonically `M`. -/
private noncomputable def single_zero_derived_homology_zero_iso :
    (H 0).obj ((single₀).obj M) ≅ M :=
  -- Proof comment: this is exactly the canonical `H⁰(single₀ M) ≅ M` comparison in the derived
  -- category.
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app M

/-- Helper for Lemma 15.67.6: away from degree `0`, the derived homology of `M[0]` vanishes. -/
private theorem single_zero_derived_homology_isZero_of_ne
    {i : ℤ} (hi : i ≠ 0) :
    IsZero ((H i).obj ((single₀).obj M)) := by
  let S := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M
  have hzeroS : IsZero (S.homology i) := by
    simpa using
      HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) (0 : ℤ) M i hi
  have hzeroQ : IsZero ((H i).obj (DerivedCategory.Q.obj S)) :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app S).isZero_iff.2 hzeroS
  exact hzeroQ.of_iso ((H i).mapIso ((DerivedCategory.singleFunctorIsoCompQ
    (ModuleCat R) (0 : ℤ)).app M)).symm

/-- Helper for Lemma 15.67.6: any flat representative of `M[0]` has vanishing ordinary homology
away from degree `0`. -/
private theorem flat_representative_homology_isZero_of_ne
    {E : CochainComplex (ModuleCat R) ℤ}
    (e : (single₀).obj M ≅ DerivedCategory.Q.obj E)
    {i : ℤ} (hi : i ≠ 0) :
    IsZero (E.homology i) := by
  have hzeroSingle : IsZero ((H i).obj ((single₀).obj M)) :=
    single_zero_derived_homology_isZero_of_ne (R := R) (M := M) hi
  have hzeroDerived : IsZero ((H i).obj (DerivedCategory.Q.obj E)) :=
    hzeroSingle.of_iso ((H i).mapIso e.symm)
  -- Proof comment: compute the derived homology of `Q.obj E` on the representative `E`.
  exact ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E).isZero_iff.1 hzeroDerived

/-- Helper for Lemma 15.67.6: the degree-zero homology of a flat representative of `M[0]` is
canonically `M`. -/
private noncomputable def flat_representative_homology_zero_iso
    {E : CochainComplex (ModuleCat R) ℤ}
    (e : (single₀).obj M ≅ DerivedCategory.Q.obj E) :
    E.homology 0 ≅ M :=
  -- Proof comment: convert the representative homology back to the derived degree-zero homology
  -- of `M[0]`, then use the single-complex identification above.
  ((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app E).symm ≪≫
    (H 0).mapIso e.symm ≪≫
      single_zero_derived_homology_zero_iso (R := R) (M := M)

/-- Helper for Lemma 15.67.6: the degree-`0` opcycles of a cochain complex are the cokernel of
the incoming differential. -/
private noncomputable def two_term_opcycles_zero_iso_cokernel
    (E : CochainComplex (ModuleCat R) ℤ) :
    E.opcycles 0 ≅ cokernel (E.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (E.pOpcycles 0) (E.d_pOpcycles (-1) 0)) := by
    simpa using E.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Compare the owner opcycle cokernel with the ordinary categorical cokernel.
  exact
    (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (E.d (-1) 0))
      hOpcycles).symm

/-- Helper for Lemma 15.67.6: the opcycle comparison carries the canonical quotient map to the
categorical cokernel projection. -/
private theorem pOpcycles_comp_two_term_opcycles_zero_iso_cokernel_hom
    (E : CochainComplex (ModuleCat R) ℤ) :
    E.pOpcycles 0 ≫ (two_term_opcycles_zero_iso_cokernel (R := R) E).hom =
      cokernel.π (E.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (E.pOpcycles 0) (E.d_pOpcycles (-1) 0)) := by
    simpa using E.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Both cokernel presentations represent the same cofork.
  simpa [two_term_opcycles_zero_iso_cokernel, hOpcycles] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      hOpcycles
      (cokernelIsCokernel (E.d (-1) 0))
      WalkingParallelPair.one

/-- Helper for Lemma 15.67.6: if a representative is supported in degrees `≤ 0`, then its
degree-zero homology is the cokernel of `d^{-1}`. -/
private noncomputable def two_term_homology_zero_iso_cokernel
    (E : CochainComplex (ModuleCat R) ℤ)
    (hLE : E.IsStrictlyLE 0) :
    E.homology 0 ≅ cokernel (E.d (-1) 0) := by
  letI : E.IsStrictlyLE 0 := hLE
  have hzero_next : E.d 0 1 = 0 := by
    -- The target term in degree `1` vanishes, so the outgoing differential is zero.
    exact (E.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  let eHomology : E.homology 0 ≅ E.opcycles 0 :=
    E.isoHomologyι 0 1 (by simp) hzero_next
  -- First identify `H^0` with the degree-zero opcycles, then rewrite those opcycles as a
  -- cokernel.
  exact eHomology ≪≫ two_term_opcycles_zero_iso_cokernel (R := R) E

/-- Helper for Lemma 15.67.6: the degree-zero cokernel of a flat representative of `M[0]`
recovers `M`. -/
private noncomputable def flat_representative_zero_cokernel_iso
    {E : CochainComplex (ModuleCat R) ℤ}
    (e : (single₀).obj M ≅ DerivedCategory.Q.obj E)
    (hLE : E.IsStrictlyLE 0) :
    cokernel (E.d (-1) 0) ≅ M :=
  (two_term_homology_zero_iso_cokernel (R := R) E hLE).symm ≪≫
    flat_representative_homology_zero_iso (R := R) (M := M) e

/-- Helper for Lemma 15.67.6: the `dFrom` cokernel at degree `-1` agrees with the ordinary
degree `-1 → 0` cokernel. -/
private noncomputable def cokernel_d_negOne_zero_iso_dFrom
    (E : CochainComplex (ModuleCat R) ℤ) :
    cokernel (E.d (-1) 0) ≅ cokernel (E.dFrom (-1)) := by
  let hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  let eCurr : E.X 0 ≅ E.xNext (-1) := (E.xNextIso hrel).symm
  -- Proof comment: `dFrom (-1)` is just `d^{-1}` followed by the canonical `xNext` rewrite.
  refine cokernel.mapIso (E.d (-1) 0) (E.dFrom (-1)) (Iso.refl _) eCurr ?_
  simpa [eCurr, E.dFrom_eq hrel]

/-- Helper for Lemma 15.67.6: every zero object of `ModuleCat R` is flat. -/
private theorem flat_of_isZero_moduleCat_local
    (N : ModuleCat R) (hN : IsZero N) :
    Module.Flat R N := by
  -- Proof comment: transport the standard flatness of the literal zero module along the unique
  -- isomorphism from `N` to a concrete zero object.
  let Z : ModuleCat R := ModuleCat.of R PUnit
  have hZ : IsZero Z := ModuleCat.isZero_of_subsingleton Z
  letI : Subsingleton ↥Z := ModuleCat.subsingleton_of_isZero hZ
  letI : Module.Free R ↥Z := Module.Free.of_subsingleton (R := R) (N := ↥Z)
  let _ : Module.Flat R Z := Module.Flat.of_free
  let e : N ≅ Z := hN.iso hZ
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Helper for Lemma 15.67.6: above the truncation cutoff, the smart lower truncation keeps the
original term. -/
private noncomputable def truncGE_term_iso_of_gt
    (K : Cpx) (a n : ℤ) (han : a < n) :
    (K.truncGE a).X n ≅ K.X n := by
  let i : ℕ := Int.toNat (n - a)
  let hi' : (ComplexShape.embeddingUpIntGE a).f i = n := by
    -- Proof comment: the retained index `i = n - a` maps back to degree `n`.
    dsimp [ComplexShape.embeddingUpIntGE]
    rw [Int.toNat_of_nonneg]
    · omega
    · omega
  let hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  -- Proof comment: the truncation API identifies every strictly retained degree with the original
  -- term.
  exact K.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 15.67.6: smart lower truncation of a bounded-above complex remains bounded
above. -/
private theorem truncGE_isStrictlyLE_of_isStrictlyLE_local
    (K : Cpx) (a b : ℤ) (ha_le_b : a ≤ b) (hK : K.IsStrictlyLE b) :
    (K.truncGE a).IsStrictlyLE b := by
  -- Proof comment: above `b`, the truncation term is still the original term, which is already
  -- zero.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have han : a < n := lt_of_le_of_lt ha_le_b hn
  exact ((truncGE_term_iso_of_gt (K := K) a n han).isZero_iff).2 (by
    rw [CochainComplex.isStrictlyLE_iff] at hK
    exact hK n hn)

/-- Helper for Lemma 15.67.6: in cochain indexing, the predecessor of degree `i` is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.67.6: the cutoff term of the smart lower truncation is the cokernel of
the incoming differential. -/
private noncomputable def truncGE_cutoff_term_iso_cokernel
    (P : Cpx) (a : ℤ) :
    (P.truncGE a).X a ≅ cokernel (P.dFrom (a - 1)) := by
  -- TODO: identify the cutoff truncation term with degree-`a` opcycles and then rewrite those
  -- opcycles as the cokernel of the incoming differential `dFrom (a - 1)`.
  sorry

/-- Helper for Lemma 15.67.6: once the cutoff cokernel is flat, the smart lower truncation is
termwise flat. -/
private theorem truncGE_isTermwiseFlat_of_flat_cokernel_local
    (P : Cpx) (a : ℤ) (hFlat : P.IsTermwiseFlat)
    (hCutFlat : Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R))) :
    (P.truncGE a).IsTermwiseFlat := by
  -- TODO: prove degrees below the cutoff are zero, the cutoff term is the flat cokernel from
  -- `truncGE_cutoff_term_iso_cokernel`, and higher degrees agree with the original termwise-flat
  -- complex via `truncGE_term_iso_of_gt`.
  sorry

/-- Helper for Lemma 15.67.6: a bounded flat representative of `M[0]` supported in `[-d, 0]`
gives a finite flat resolution of length at most `d`. -/
private lemma hasFiniteFlatResolutionLengthLE_of_flat_representative {d : ℕ}
    {E : CochainComplex (ModuleCat R) ℤ}
    (e : (single₀).obj M ≅ DerivedCategory.Q.obj E)
    (hGE : E.IsStrictlyGE (-(d : ℤ)))
    (hLE : E.IsStrictlyLE 0)
    (hFlat : E.IsTermwiseFlat) :
    HasFiniteFlatResolutionLengthLE M d := by
  -- TODO: package the bounded flat representative by reading off the terms
  -- `E^{-d}, …, E⁰`, using `flat_representative_zero_cokernel_iso` for the augmentation, and
  -- `flat_representative_homology_isZero_of_ne` for the exactness and injectivity clauses.
  sorry

/-- Helper for Lemma 15.67.6: a finite flat resolution gives tor dimension at most the same
length. -/
private lemma hasTorDimensionLE_of_hasFiniteFlatResolutionLengthLE_explicit {d : ℕ}
    (hM : HasFiniteFlatResolutionLengthLE M d) :
    ModuleHasTorDimensionLE M d := by
  induction d generalizing M with
  | zero =>
      -- In length `0`, the resolution hypothesis is exactly flatness.
      simpa [HasFiniteFlatResolutionLengthLE] using
        moduleHasTorDimensionLE_zero_of_flat (R := R) (M := M) hM
  | succ n ih =>
      rcases hM with ⟨F, hFlat, δ, π, hsurj, hExact₀, hExact, hInj⟩
      let K : ModuleCat R := ModuleCat.of R (LinearMap.ker π.hom)
      have hδ0_mem : ∀ x, (δ 0).hom x ∈ LinearMap.ker π.hom := by
        -- Exactness at `F₀` makes the first differential land in the kernel of the augmentation.
        intro x
        change π.hom ((δ 0).hom x) = 0
        simpa [Function.comp] using congrArg (fun f ↦ f x) (Function.Exact.comp_eq_zero hExact₀)
      let πK : F 1 ⟶ K := ModuleCat.ofHom ((δ 0).hom.codRestrict (LinearMap.ker π.hom) hδ0_mem)
      have hπK_surj : Function.Surjective πK.hom := by
        -- Repackage exactness at `F₀` as surjectivity onto the kernel module.
        intro x
        rcases (hExact₀ x.1).1 x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext hy⟩
      have hKresolution : HasFiniteFlatResolutionLengthLE K n := by
        cases n with
        | zero =>
            -- In the two-term case, `F₁ → ker π` is a linear equivalence, so the kernel is flat.
            have hπK_inj : Function.Injective πK.hom := by
              intro x y hxy
              apply hInj
              exact congrArg Subtype.val hxy
            let e : (F 1 : Type u) ≃ₗ[R] (K : Type u) :=
              LinearEquiv.ofBijective πK.hom ⟨hπK_inj, hπK_surj⟩
            let _ : Module.Flat R (F 1) := hFlat 1
            simpa [HasFiniteFlatResolutionLengthLE] using Module.Flat.of_linearEquiv e.symm
        | succ m =>
            let G : Fin (m + 2) → ModuleCat R := fun i ↦ F i.succ
            let δG : (i : Fin (m + 1)) → G i.succ ⟶ G i.castSucc := fun i ↦ δ i.succ
            have hFlatG : ∀ i, Module.Flat R (G i) := by
              -- The truncated tail keeps the original flat terms.
              intro i
              simpa [G] using hFlat i.succ
            have hExactK₀ : Function.Exact (δG 0) πK := by
              -- The codomain restriction turns exactness of `δ₁, δ₀` into exactness of `δ₁, πK`.
              have hExact10 : Function.Exact (δ 1) (δ 0) := by
                simpa using hExact (0 : Fin (m + 1))
              intro x
              constructor
              · intro hx
                have hx' : (δ 0).hom x = 0 := by
                  exact congrArg Subtype.val hx
                exact (hExact10 x).1 hx'
              · rintro ⟨z, rfl⟩
                ext
                exact congrArg (fun f ↦ f z) (Function.Exact.comp_eq_zero hExact10)
            have hExactG : ∀ i : Fin m, Function.Exact (δG i.succ) (δG i.castSucc) := by
              -- All later exactness statements are inherited verbatim from the original resolution.
              intro i
              simpa [δG] using hExact i.succ
            have hInjG : Function.Injective (δG (Fin.last m)) := by
              -- The leftmost differential of the truncated tail is the original leftmost one.
              simpa [δG] using hInj
            exact ⟨G, hFlatG, δG, πK, hπK_surj, hExactK₀, hExactG, hInjG⟩
      have hKtor : ModuleHasTorDimensionLE K n := ih K hKresolution
      have hF0tor0 : ModuleHasTorDimensionLE (F 0) 0 :=
        moduleHasTorDimensionLE_zero_of_flat (R := R) (M := F 0) (hFlat 0)
      let S : ShortComplex (ModuleCat R) := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      have hSExact : S.Exact := by
        -- The kernel row of the augmentation is exact in `ModuleCat`.
        simpa [S] using ShortComplex.exact_kernel π
      let _ : Mono (kernel.ι π) := inferInstance
      let _ : Epi π := (ModuleCat.epi_iff_surjective π).2 hsurj
      let hS : S.ShortExact := ShortComplex.ShortExact.mk hSExact
      have hKtor_widened :
          CategoryTheory.HasTorAmplitudeIn ((single₀).obj K) (-(n : ℤ)) 1 := by
        -- Widen the upper endpoint from `0` to `1`.
        exact
          hasTorAmplitudeIn_mono (R := R) (K := (single₀).obj K) hKtor
            (by omega) (by omega)
      have hF0tor :
          CategoryTheory.HasTorAmplitudeIn ((single₀).obj (F 0)) (-(Nat.succ n : ℤ)) 0 := by
        -- A flat module has tor-amplitude `[0, 0]`, hence also `[-(n+1), 0]`.
        exact
          hasTorAmplitudeIn_mono (R := R) (K := (single₀).obj (F 0)) hF0tor0
            (by omega) (by omega)
      have hKtor_triangle :
          CategoryTheory.HasTorAmplitudeIn hS.singleTriangle.obj₁ (-(n : ℤ)) 1 := by
        let eK : CategoryTheory.Limits.kernel π ≅ K := ModuleCat.kernelIsoKer π
        simpa [S] using
          (hasTorAmplitudeIn_of_iso_local (R := R) ((single₀).mapIso eK)).2 hKtor_widened
      have hF0tor_triangle :
          CategoryTheory.HasTorAmplitudeIn hS.singleTriangle.obj₂ (-(Nat.succ n : ℤ)) 0 := by
        simpa [S] using hF0tor
      have hKtor_triangle_shifted :
          CategoryTheory.HasTorAmplitudeIn hS.singleTriangle.obj₁ (-(Nat.succ n : ℤ) + 1) (0 + 1) := by
        simpa using hKtor_triangle
      -- The short exact sequence `0 → K → F₀ → M → 0` gives the required one-step shift.
      have hTriangleTor :
          CategoryTheory.HasTorAmplitudeIn hS.singleTriangle.obj₃ (-(Nat.succ n : ℤ)) 0 := by
        simpa using
          CategoryTheory.hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
            (R := R) (a := -(Nat.succ n : ℤ)) (b := 0)
            hS.singleTriangle hS.singleTriangle_distinguished hKtor_triangle_shifted hF0tor_triangle
      simpa [ModuleHasTorDimensionLE, S] using hTriangleTor

-- Proof sketch: the forward implication rewrites tor dimension `≤ d` as tor-amplitude in
-- `[-d, 0]` for `M[0]` and then applies Lemma `15.67.3` to obtain a flat representative
-- supported in that range, which is exactly a flat resolution of length at most `d`. For the
-- reverse implication, such a flat resolution gives a flat representative of `M[0]` in the same
-- range, so Lemma `15.67.3` yields tor-amplitude in `[-d, 0]`.
/-- Lemma 15.67.6: an `R`-module `M` has tor dimension at most `d` if and only if it admits a
finite flat resolution of length at most `d`. -/
theorem hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE (d : ℕ) :
    ModuleHasTorDimensionLE M d ↔ HasFiniteFlatResolutionLengthLE M d := by
  constructor
  · intro hM
    -- TODO: the source-faithful forward implication needs the earlier owner
    -- `CochainComplex.flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE`
    -- together with `projective_resolution_single0_iso`. In the current workspace that owner
    -- file `Lemma_15_67_2` does not compile, so the local proof frontier stops after the base-case
    -- and packaging lemmas above.
    sorry
  · intro hM
    exact hasTorDimensionLE_of_hasFiniteFlatResolutionLengthLE_explicit (R := R) (M := M) hM

/-- A module of tor dimension at most `d` admits a finite flat resolution of length at most
`d`. -/
theorem ModuleHasTorDimensionLE.hasFiniteFlatResolutionLengthLE {d : ℕ}
    (hM : ModuleHasTorDimensionLE M d) :
    HasFiniteFlatResolutionLengthLE M d :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M d).1 hM

/-- A finite flat resolution of length at most `d` gives tor dimension at most `d`. -/
theorem HasFiniteFlatResolutionLengthLE.hasTorDimensionLE {d : ℕ}
    (hM : HasFiniteFlatResolutionLengthLE M d) :
    ModuleHasTorDimensionLE M d := by
  -- Reuse the direct inductive proof of the explicit-resolution direction.
  exact hasTorDimensionLE_of_hasFiniteFlatResolutionLengthLE_explicit (R := R) (M := M) hM

-- Proof sketch: specialize `hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE` to
-- `d = 0` and use `hasFiniteFlatResolutionLengthLE_zero_iff`.
/-- An `R`-module has tor dimension at most `0` exactly when it is flat. -/
theorem hasTorDimensionLE_zero_iff_flat :
    ModuleHasTorDimensionLE M 0 ↔ Module.Flat R M :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M 0).trans
    (hasFiniteFlatResolutionLengthLE_zero_iff M)

end ModuleCat

end
