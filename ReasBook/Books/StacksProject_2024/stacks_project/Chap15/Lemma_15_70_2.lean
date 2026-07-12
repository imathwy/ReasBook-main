import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap13.Definition_13_18_1
import StacksProject_2024.Chap13.Lemma_13_18_3
import StacksProject_2024.Chap13.Lemma_13_18_8
import StacksProject_2024.Chap13.Lemma_13_27_3
import StacksProject_2024.Chap15.Definition_15_70_1
import StacksProject_2024.Chap15.Lemma_15_55_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open CochainComplex.HomComplex.CohomologyClass
open scoped DerivedExt
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling:
- primary domain: injective-amplitude criteria in `DerivedCategory (ModuleCat R)`, expressed by
  vanishing of derived `Ext` groups;
- inspected owner declarations:
  `CategoryTheory.HasInjectiveAmplitudeIn`,
  `CategoryTheory.Ext^i(_, _)`,
  `CategoryTheory.projectiveAmplitudeIn_ext_vanishing_tfae`,
  `CategoryTheory.injective_iff_ext_one_eq_zero`,
  `CategoryTheory.injective_tfae_extOneFromIdealQuotient_eq_zero_baer`;
- best owner abstraction: the source-facing owner is `HasInjectiveAmplitudeIn K a b`; the
  shifted-Hom vanishing clauses are derived API describing that owner, not a separate local owner;
- layer: `source-facing`, since this lemma gives the textbook criterion for the existing owner
  `HasInjectiveAmplitudeIn`;
- primitive data: `K : DMod` and the bounds `a b : ℤ`;
- derived API: testing `Ext^i((single₀).obj N, K)` and its ideal-quotient specialization by
  direct vanishing `∀ e, e = 0`, in the same chapter style as the projective-amplitude and
  Baer-criterion files;
- bridge/view: the core owner remains `ShiftedHom`, but `Ext^i(_, _)` is the canonical
  source-facing notation already introduced in Chapter `13`, so the public theorem surface should
  use that notation rather than restating the raw owner. -/

-- Proof sketch: prove `(1) → (2)` by computing morphisms from degree-zero modules against an
-- injective representative supported in `[a, b]`; `(2) → (3)` is immediate by specializing to
-- quotient modules `R/I`; for `(3) → (1)`, first recover cohomological boundedness of `K` from
-- the case `I = ⊥`, then truncate an injective resolution and apply Lemma `15.55.4` to the final
-- kernel using the vanishing for all quotients `R/I`.
/-- Helper for Lemma 15.70.2: isomorphisms on source and target induce an additive equivalence on
Hom groups. -/
private theorem iso_hom_congr_add_equiv_map_add
    {X Y X₁ Y₁ : DMod} (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- `Iso.homCongr` is additive because composition is additive on both sides.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.70.2: isomorphisms on source and target induce an additive equivalence on
Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv
    {X Y X₁ Y₁ : DMod} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := iso_hom_congr_add_equiv_map_add α β }

/-- Helper for Lemma 15.70.2: if the term `I^n` is zero, then the degree-`n` cochains from a
degree-zero module complex into `I` are zero. -/
lemma single_homComplex_X_isZero_of_term_isZero
    (I : Cpx) (N : ModuleCat R) (n : ℤ)
    (hzero : IsZero (I.X n)) :
    IsZero ((CochainComplex.HomComplex ((singleCpx₀).obj N) I).X n) := by
  have hdeg : (0 : ℤ) + n = n := by omega
  -- Degree-`n` cochains from `N[0]` into `I` are exactly maps `N ⟶ I^n`.
  let e :
      CochainComplex.HomComplex.Cochain ((singleCpx₀).obj N) I n ≃+ (N ⟶ I.X n) :=
    CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (K := I) (X := N) (p := 0) (q := n) (n := n) hdeg
  letI : Subsingleton (N ⟶ I.X n) := ⟨fun f g ↦ hzero.eq_of_tgt f g⟩
  letI : Subsingleton (((CochainComplex.HomComplex ((singleCpx₀).obj N) I).X n) : Type _) :=
    e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton
    ((CochainComplex.HomComplex ((singleCpx₀).obj N) I).X n)

/-- Helper for Lemma 15.70.2: an injective complex supported in `[a, b]` has zero Hom-complex
homology from `N[0]` outside the same interval. -/
lemma single_homComplex_homology_isZero_outside_interval
    (I : Cpx) (a b i : ℤ) (N : ModuleCat R)
    (hIge : I.IsStrictlyGE a) (hIle : I.IsStrictlyLE b)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((CochainComplex.HomComplex ((singleCpx₀).obj N) I).homology i) := by
  have hterm : IsZero (I.X i) := by
    by_cases hilow : i < a
    · exact I.isZero_of_isStrictlyGE a i hilow
    · have hihigh : b < i := by
        by_contra hie
        apply hi
        exact ⟨le_of_not_gt hilow, le_of_not_gt hie⟩
      exact I.isZero_of_isStrictlyLE b i hihigh
  have hX : IsZero ((CochainComplex.HomComplex ((singleCpx₀).obj N) I).X i) :=
    single_homComplex_X_isZero_of_term_isZero I N i hterm
  -- The short complex computing degree-`i` homology has zero middle term.
  simpa using
    (ShortComplex.isZero_homology_of_isZero_X₂
      (S := (CochainComplex.HomComplex ((singleCpx₀).obj N) I).sc i)
      (by simpa using hX))

/-- Helper for Lemma 15.70.2: for a bounded-below injective target, the Hom-complex from `N[0]`
computes the derived extension group `Ext^n_R(N, Q(I))`. -/
noncomputable def single_source_homology_add_equiv_ext_of_bounded_below_injective
    (I : CochainComplex.InjectivePlus (ModuleCat R)) (N : ModuleCat R) (n : ℤ) :
    (CochainComplex.HomComplex ((singleCpx₀).obj N) (I : Cpx)).homology n ≃+
      Ext^n((single₀).obj N, DerivedCategory.Q.obj (I : Cpx)) :=
  let e₁ :
      (CochainComplex.HomComplex ((singleCpx₀).obj N) (I : Cpx)).homology n ≃+
        ((KQ).obj ((singleCpx₀).obj N) ⟶ (KQ).obj (((I : Cpx)⟦n⟧))) :=
    (CochainComplex.HomComplex.homologyAddEquiv ((singleCpx₀).obj N) (I : Cpx) n).trans
      homAddEquiv
  letI : (((I : Cpx)⟦n⟧) : Cpx).IsKInjective := inferInstance
  let e₂ :=
    -- K-injective targets let us identify homotopy morphisms with derived morphisms.
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        ((KQ).obj ((singleCpx₀).obj N) ⟶ (KQ).obj (((I : Cpx)⟦n⟧))) →+
          (((DerivedCategory.Q).obj ((singleCpx₀).obj N)) ⟶
            ((DerivedCategory.Q).obj (((I : Cpx)⟦n⟧)))))
      (CochainComplex.IsKInjective.Qh_map_bijective
        ((KQ).obj ((singleCpx₀).obj N)) (((I : Cpx)⟦n⟧)))
  let e₃ :
      (((DerivedCategory.Q).obj ((singleCpx₀).obj N)) ⟶
          ((DerivedCategory.Q).obj (((I : Cpx)⟦n⟧)))) ≃+
        Ext^n((single₀).obj N, DerivedCategory.Q.obj (I : Cpx)) :=
    iso_hom_congr_add_equiv
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N)
      (((DerivedCategory.Q).commShiftIso n).app (I : Cpx))
  e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 15.70.2: a nonzero module receives a nonzero map from some quotient `R / J`.
-/
lemma exists_nonzero_hom_from_ideal_quotient
    (M : ModuleCat R) (hM : ¬ IsZero M) :
    ∃ J : Ideal R, ∃ f : ModuleCat.of R (R ⧸ J) ⟶ M, f ≠ 0 := by
  classical
  have hnot_all_zero : ¬ ∀ x : M, x = 0 := by
    intro hx
    apply hM
    rw [ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun x y ↦ by rw [hx x, hx y]⟩
  obtain ⟨x, hx⟩ := not_forall.mp hnot_all_zero
  refine ⟨Ideal.torsionOf R M x, ?_⟩
  let f : ModuleCat.of R (R ⧸ Ideal.torsionOf R M x) ⟶ M :=
    ModuleCat.ofHom
      ((Submodule.subtype (R ∙ x)).comp
        ((Ideal.quotTorsionOfEquivSpanSingleton R M x).toLinearMap))
  refine ⟨f, ?_⟩
  intro hf
  -- The class of `1` maps to the chosen nonzero element `x`.
  have hfx : f.hom (Submodule.Quotient.mk (1 : R)) = x := by
    change (((Ideal.quotTorsionOfEquivSpanSingleton R M x)
      (Submodule.Quotient.mk (1 : R)) : R ∙ x) : M) = x
    simp
  have hzero :
      f.hom (Submodule.Quotient.mk (1 : R)) = 0 := by
    exact congrArg
      (fun g : ModuleCat.of R (R ⧸ Ideal.torsionOf R M x) ⟶ M =>
        g.hom (Submodule.Quotient.mk (1 : R)))
      hf
  exact hx (hfx.symm.trans hzero)

/-- Helper for Lemma 15.70.2: degree-`n` cohomology of a derived object matches the homology of
its chosen cochain-complex preimage. -/
noncomputable def objPreimage_homology_iso
    (K : DMod) (n : ℤ) :
    (H n).obj K ≅ (DerivedCategory.Q.objPreimage K).homology n :=
  -- This is the standard comparison between the derived-category homology functor and the chosen
  -- preimage complex used by `DerivedCategory.Q`.
  ((H n).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app
      (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.70.2: the quotient by the zero ideal is canonically the free rank-one
module `R`. -/
private noncomputable def quotient_bot_module_iso :
    ModuleCat.of R (R ⧸ (⊥ : Ideal R)) ≅ ModuleCat.of R R :=
  (Submodule.quotEquivOfEqBot (⊥ : Ideal R) rfl).toModuleIso

/-- Helper for Lemma 15.70.2: the ideal-quotient source `(R / 0)[0]` is the usual `R[0]`. -/
private noncomputable def quotient_bot_single_iso :
    (single₀).obj (ModuleCat.of R (R ⧸ (⊥ : Ideal R))) ≅
      (single₀).obj (ModuleCat.of R R) :=
  (single₀).mapIso (quotient_bot_module_iso (R := R))

/-- Helper for Lemma 15.70.2: a nonzero module receives a nonzero map from the free rank-one
module `R`. -/
lemma exists_nonzero_hom_from_ring
    (M : ModuleCat R) (hM : ¬ IsZero M) :
    ∃ f : ModuleCat.of R R ⟶ M, f ≠ 0 := by
  have hnot_all_zero : ¬ ∀ x : M, x = 0 := by
    intro hx
    apply hM
    rw [ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun x y ↦ by rw [hx x, hx y]⟩
  obtain ⟨x, hx⟩ := not_forall.mp hnot_all_zero
  let f : ModuleCat.of R R ⟶ M :=
    ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight x)
  refine ⟨f, ?_⟩
  intro hf
  -- Evaluating at `1` recovers the chosen nonzero element.
  have hfx : (ModuleCat.homEquiv f) (1 : R) = x := by
    change (((LinearMap.id : R →ₗ[R] R).smulRight x) (1 : R)) = x
    simp [LinearMap.smulRight_apply]
  have hzero : (ModuleCat.homEquiv f) (1 : R) = 0 := by
    exact congrArg (fun g : ModuleCat.of R R ⟶ M ↦ (ModuleCat.homEquiv g) (1 : R)) hf
  exact hx (hfx.symm.trans hzero)

/-- Helper for Lemma 15.70.2: maps from `R[0]` into an object supported strictly below degree
`0` vanish because `R` is projective. -/
private theorem ring_single_hom_eq_zero_of_isLE_negOne
    {Y : DMod} (hY : Y.IsLE (-1))
    (φ : (single₀).obj (ModuleCat.of R R) ⟶ Y) :
    φ = 0 := by
  -- Replace the target by a strictly upper-bounded complex and use projectivity of `R`.
  rcases hY with ⟨L, eL, hL⟩
  apply (cancel_mono eL.hom).1
  simpa using
    (DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (P := ModuleCat.of R R) (L := L) (i := 0) (φ := φ ≫ eL.hom) (n := -1)
      (hn := by omega))

/-- Helper for Lemma 15.70.2: postcomposition with the lower truncation projection
`K ⟶ τ≥n K` is bijective on degree-`n` extensions from `R[0]`. -/
private theorem ring_single_postcomp_truncGE_bijective
    (K : DMod) (n : ℤ) :
    Function.Bijective
      (fun e : Ext^n((single₀).obj (ModuleCat.of R R), K) ↦
        e ≫ ((shiftFunctor DMod n).map
          ((DerivedCategory.TStructure.t.truncGEπ n).app K))) := by
  -- TODO: use the shifted truncation triangle `(t.triangleLTGE n).obj K`, but normalize the
  -- `n.negOnePow` sign inserted on the shifted morphisms before applying
  -- `Triangle.coyoneda_exact₂` and `Triangle.coyoneda_exact₃`.
  sorry

/-- Helper for Lemma 15.70.2: the lower truncation projection induces an isomorphism on the
critical degree-`n` homology group. -/
private theorem isIso_homologyMap_truncGEπ_local
    (K : DMod) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle DMod := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang DMod := by
    -- The canonical truncation triangle is distinguished.
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    -- The lower piece has no degree-`n` homology.
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    -- The connecting morphism also lands in that vanishing homology group.
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using isIso_of_mono_of_epi ((H n).map T.mor₂)

/-- Helper for Lemma 15.70.2: degree-`n` extensions from `R[0]` should identify with maps from
`R` to `H^n(K)`. -/
private noncomputable def ring_source_ext_add_equiv_hom_to_homology
    (K : DMod) (n : ℤ) :
    Ext^n((single₀).obj (ModuleCat.of R R), K) ≃+
      (ModuleCat.of R R ⟶ (H n).obj K) := by
  -- TODO: invert `ring_single_postcomp_truncGE_bijective`, then compose with
  -- `shiftedHomToHomologyMap_bijective` for `X = R[0]` and `Y = τ≥n K`, and finally transport
  -- along `DerivedCategory.singleFunctorCompHomologyFunctorIso` and
  -- `isIso_homologyMap_truncGEπ_local`.
  sorry

/-- Helper for Lemma 15.70.2: a degree `n ≤ b` lies in the image of the upper-truncation
embedding `m ↦ b - m`. -/
private theorem embeddingUpIntLE_toNat_sub_eq
    (b n : ℤ) (hn : n ≤ b) :
    (ComplexShape.embeddingUpIntLE b).f (Int.toNat (b - n)) = n := by
  -- The retained upper-truncation range is exactly the nonnegative difference `b - n`.
  dsimp [ComplexShape.embeddingUpIntLE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.70.2: below the cutoff, the canonical upper truncation keeps the original
term of the complex. -/
private noncomputable def truncLE_term_iso_of_lt
    (I : Cpx) (b n : ℤ) (hn : n < b) :
    (I.truncLE b).X n ≅ I.X n :=
  let i : ℕ := Int.toNat (b - n)
  let hi' : (ComplexShape.embeddingUpIntLE b).f i = n :=
    embeddingUpIntLE_toNat_sub_eq b n (le_of_lt hn)
  let hboundary : ¬ (ComplexShape.embeddingUpIntLE b).BoundaryLE i := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hi0
    have : b = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntLE] using hi'
    omega
  I.truncLEXIso (e := ComplexShape.embeddingUpIntLE b) hi' hboundary

/-- Helper for Lemma 15.70.2: at the cutoff, the canonical upper truncation replaces the last
term by the cycles object. -/
private noncomputable def truncLE_term_iso_cycles
    (I : Cpx) (b : ℤ) :
    (I.truncLE b).X b ≅ I.cycles b :=
  let hi' : (ComplexShape.embeddingUpIntLE b).f 0 = b := by
    simp [ComplexShape.embeddingUpIntLE]
  let hboundary : (ComplexShape.embeddingUpIntLE b).BoundaryLE 0 := by
    simpa using (ComplexShape.boundaryLE_embeddingUpIntLE_iff b 0).2 rfl
  I.truncLEXIsoCycles (e := ComplexShape.embeddingUpIntLE b) hi' hboundary

/-- Helper for Lemma 15.70.2: above the cutoff, the canonical upper truncation has zero terms. -/
private theorem truncLE_term_isZero_of_gt
    (I : Cpx) (b n : ℤ) (hn : b < n) :
    IsZero ((I.truncLE b).X n) := by
  -- The upper truncation is strictly supported in degrees `≤ b`.
  exact (I.truncLE b).isZero_of_isStrictlyLE b n hn

/-- Helper for Lemma 15.70.2: if the ambient complex has injective terms and its cutoff cycles
object is injective, then every term of the canonical upper truncation is injective. -/
lemma truncLE_terms_injective_of_cycles_injective
    (I : Cpx) (b : ℤ)
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (hcycles : Injective (I.cycles b)) :
    ∀ n : ℤ, Injective ((I.truncLE b).X n) := by
  intro n
  by_cases hlt : n < b
  · -- Below the cutoff, truncation does not change the term.
    exact Injective.of_iso (truncLE_term_iso_of_lt I b n hlt).symm (hIinj n)
  · by_cases hEq : n = b
    · -- At the cutoff, truncation replaces the term by the cycles object.
      subst n
      exact Injective.of_iso (truncLE_term_iso_cycles I b).symm hcycles
    · -- Above the cutoff, the term is zero and hence injective.
      have hgt : b < n := by omega
      exact Injective.of_iso (truncLE_term_isZero_of_gt I b n hgt).isoZero.symm inferInstance

/-- Helper for Lemma 15.70.2: the differential `d^b` lands canonically in the next kernel object.
-/
private noncomputable def to_next_kernel
    (I : Cpx) (b : ℤ) :
    I.X b ⟶ kernel (I.d (b + 1) (b + 2)) := by
  -- The composite `d^(b+1) ∘ d^b` vanishes, so `d^b` factors through the next kernel.
  refine kernel.lift (I.d (b + 1) (b + 2)) (I.d b (b + 1)) ?_
  simp

/-- Helper for Lemma 15.70.2: the kernel inclusion of `d^b` is annihilated by the map to the next
kernel object. -/
private theorem kernel_to_next_zero
    (I : Cpx) (b : ℤ) :
    kernel.ι (I.d b (b + 1)) ≫ to_next_kernel I b = 0 := by
  -- After composing with the next kernel inclusion, this is just `d ∘ d = 0`.
  apply (cancel_mono (kernel.ι (I.d (b + 1) (b + 2)))).1
  simp [Category.assoc, to_next_kernel]

/-- Helper for Lemma 15.70.2: the kernel-to-term-to-next-kernel sequence is exact at the middle
term. -/
private theorem kernel_tail_exact
    (I : Cpx) (b : ℤ) :
    (ShortComplex.mk (kernel.ι (I.d b (b + 1))) (to_next_kernel I b)
      (kernel_to_next_zero I b)).Exact := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (kernel.ι (I.d b (b + 1))) (to_next_kernel I b)
      (kernel_to_next_zero I b)
  -- The first map is literally the kernel of the second one.
  have hkernel : IsLimit (KernelFork.ofι S.f S.zero) := by
    refine KernelFork.IsLimit.ofι' (kernel.ι (I.d b (b + 1))) (kernel_to_next_zero I b) ?_
    intro W k hk
    refine ⟨kernel.lift (I.d b (b + 1)) k ?_, by rw [kernel.lift_ι]⟩
    have hk' := congrArg (fun t ↦ t ≫ kernel.ι (I.d (b + 1) (b + 2))) hk
    simp [Category.assoc, to_next_kernel] at hk'
    exact hk'
  exact ShortComplex.exact_of_f_is_kernel S hkernel

/-- Helper for Lemma 15.70.2: vanishing of `H^(b + 1)(I)` makes the canonical map
`I^b → ker(d^(b+1))` surjective. -/
private theorem surjective_to_next_kernel_of_isZero_homology
    (I : Cpx) (b : ℤ) (hzero : IsZero (I.homology (b + 1))) :
    Function.Surjective (to_next_kernel I b).hom := by
  have hExactAt : I.ExactAt (b + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hzero
  have hExactSc : (I.sc (b + 1)).Exact := by
    -- This rewrites exactness at degree `b + 1` into exactness of the short complex
    -- `I^b → I^(b+1) → I^(b+2)`.
    exact (HomologicalComplex.exactAt_iff I (b + 1)).mp hExactAt
  have hRangeKer' :
      LinearMap.range (I.d ((ComplexShape.up ℤ).prev (b + 1)) (b + 1)).hom =
        LinearMap.ker (I.d (b + 1) ((ComplexShape.up ℤ).next (b + 1))).hom := by
    simpa [HomologicalComplex.sc] using ShortComplex.Exact.moduleCat_range_eq_ker hExactSc
  have hRangeKer :
      LinearMap.range (I.d b (b + 1)).hom =
        LinearMap.ker (I.d (b + 1) (b + 2)).hom := by
    have hprev : (ComplexShape.up ℤ).prev (b + 1) = b := by
      simpa using (CochainComplex.prev ℤ (b + 1))
    have hnext : (ComplexShape.up ℤ).next (b + 1) = b + 2 := by
      simpa [add_assoc] using (CochainComplex.next ℤ (b + 1))
    rw [hprev, hnext] at hRangeKer'
    exact hRangeKer'
  have hι_injective :
      Function.Injective (kernel.ι (I.d (b + 1) (b + 2))).hom := by
    simpa using
      (ModuleCat.mono_iff_injective (kernel.ι (I.d (b + 1) (b + 2)))).1 inferInstance
  intro y
  let y' : LinearMap.ker (I.d (b + 1) (b + 2)).hom :=
    ((ModuleCat.kernelIsoKer (I.d (b + 1) (b + 2))).hom).hom y
  have hy_val : (kernel.ι (I.d (b + 1) (b + 2))).hom y = y'.1 := by
    -- The concrete kernel element underlying `y` is exactly its image in `I^(b+1)`.
    exact (congrArg
      (fun g : kernel (I.d (b + 1) (b + 2)) ⟶ I.X (b + 1) ↦ g.hom y)
      (ModuleCat.kernelIsoKer_hom_ker_subtype (f := I.d (b + 1) (b + 2)))).symm
  have hy_range : y'.1 ∈ LinearMap.range (I.d b (b + 1)).hom := by
    have hy_ker : y'.1 ∈ LinearMap.ker (I.d (b + 1) (b + 2)).hom := by
      simpa using y'.2
    rw [hRangeKer]
    exact hy_ker
  rcases hy_range with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply hι_injective
  calc
    (kernel.ι (I.d (b + 1) (b + 2))).hom ((to_next_kernel I b).hom x)
        = (I.d b (b + 1)).hom x := by
            simp [to_next_kernel]
    _ = y'.1 := hx
    _ = (kernel.ι (I.d (b + 1) (b + 2))).hom y := hy_val.symm

/-- Helper for Lemma 15.70.2: if `H^(b + 1)(I)` vanishes, then the canonical tail
`ker(d^b) → I^b → ker(d^(b+1))` is short exact. -/
private theorem kernel_tail_shortExact_of_isZero_homology_succ
    (I : Cpx) (b : ℤ) (hzero : IsZero (I.homology (b + 1))) :
    (ShortComplex.mk (kernel.ι (I.d b (b + 1))) (to_next_kernel I b)
      (kernel_to_next_zero I b)).ShortExact := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (kernel.ι (I.d b (b + 1))) (to_next_kernel I b)
      (kernel_to_next_zero I b)
  have hExact : S.Exact := by
    simpa [S] using kernel_tail_exact I b
  have hEpi : Epi S.g := by
    exact (ModuleCat.epi_iff_surjective S.g).2 <| by
      simpa [S] using surjective_to_next_kernel_of_isZero_homology I b hzero
  exact ShortComplex.ShortExact.mk' hExact inferInstance hEpi

/-- Helper for Lemma 15.70.2: quotient-test vanishing in degree `b + 1` forces the cutoff cycles
module of a bounded-below injective complex to be injective. -/
private theorem cycles_injective_of_ideal_quotient_ext_succ_vanishing
    (I : CochainComplex.InjectivePlus (ModuleCat R)) (b : ℤ)
    (hzero : IsZero (((I : Cpx).homology (b + 1))))
    (hvanish :
      ∀ J : Ideal R,
        ∀ e : Ext^(b + 1)((single₀).obj (ModuleCat.of R (R ⧸ J)),
          DerivedCategory.Q.obj (I : Cpx)), e = 0) :
    Injective ((I : Cpx).cycles b) := by
  -- Route correction: the remaining reverse-direction work is exactly the source tail argument.
  -- The short exact sequence `0 → Z^b(I) → I^b → Z^{b+1}(I) → 0` turns `Ext¹(R/J, Z^b(I))` into
  -- the `(b + 1)`-st homology of the Hom-complex against `I`, and the hypothesis `hvanish`
  -- kills that homology for every quotient `R/J`.
  -- TODO: package the short exact sequence from
  -- `kernel_tail_shortExact_of_isZero_homology_succ (I := (I : Cpx)) b hzero`, compare its
  -- connecting morphism with
  -- `single_source_homology_add_equiv_ext_of_bounded_below_injective I (ModuleCat.of R (R ⧸ J))
  --   (b + 1)`,
  -- and apply `(injective_tfae_extOneFromIdealQuotient_eq_zero_baer (R := R)
  --   ((I : Cpx).cycles b)).out 1 0`.
  sorry

/-- Lemma 15.70.2: for an object `K` of `D(R)` and integers `a, b`, the following are
equivalent: `K` is represented by a cochain complex of injective `R`-modules supported in
degrees `[a, b]`; for every `R`-module `N`, the groups `Ext^i_R(N, K)` vanish for
`i ∉ [a, b]`; and it is enough to test this vanishing on quotient modules `R/I` for ideals
`I ⊆ R`. -/
theorem injectiveAmplitudeIn_ext_vanishing_tfae
    (K : DMod) (a b : ℤ) :
    List.TFAE
      [ HasInjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj N, K), e = 0
      , ∀ (I : Ideal R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ I)), K), e = 0
      ] := by
  tfae_have 1 → 2 := by
    intro hK N i hi e
    rcases hK with ⟨I, hIge, hIle, hIinj, ⟨α⟩⟩
    let Iplus : CochainComplex.InjectivePlus (ModuleCat R) :=
      ⟨⟨I, (CochainComplex.plus_iff (ModuleCat R) I).2 ⟨a, hIge⟩⟩, hIinj⟩
    -- Compute `Ext` by the Hom-complex into the bounded-below injective representative.
    have hhom :
        IsZero ((CochainComplex.HomComplex ((singleCpx₀).obj N) I).homology i) :=
      single_homComplex_homology_isZero_outside_interval I a b i N hIge hIle hi
    let eExt := single_source_homology_add_equiv_ext_of_bounded_below_injective Iplus N i
    have hvanish :
        (Iso.refl _).homCongr ((shiftFunctor DMod i).mapIso α) e = 0 := by
      letI :
          Subsingleton
            (((CochainComplex.HomComplex ((singleCpx₀).obj N) I).homology i) : Type _) :=
        AddCommGrpCat.subsingleton_of_isZero hhom
      letI : Subsingleton (Ext^i((single₀).obj N, DerivedCategory.Q.obj I)) :=
        eExt.symm.injective.subsingleton
      exact Subsingleton.elim _ _
    have hvanish' :
        (Iso.refl _).homCongr ((shiftFunctor DMod i).mapIso α) e =
          ((Iso.refl _).homCongr ((shiftFunctor DMod i).mapIso α)) 0 := by
      simpa using hvanish
    exact ((Iso.refl _).homCongr ((shiftFunctor DMod i).mapIso α)).injective hvanish'
  tfae_have 2 → 3 := by
    intro h I i hi e
    exact h (ModuleCat.of R (R ⧸ I)) i hi e
  tfae_have 3 → 1 := by
    intro h
    -- Route correction: the reverse implication has to stay source-faithful. We first force
    -- vanishing of the preimage homology outside `[a, b]`, then take a bounded-below injective
    -- model and finally package the canonical upper truncation.
    have hpre :
        ∀ n : ℤ, n ∉ Set.Icc a b →
          IsZero ((DerivedCategory.Q.objPreimage K).homology n) := by
      intro n hn
      by_contra hzero
      have hhomology_nonzero : ¬ IsZero ((H n).obj K) := by
        intro hH
        apply hzero
        exact (objPreimage_homology_iso K n).isZero_iff.1 hH
      obtain ⟨f, hf⟩ := exists_nonzero_hom_from_ring ((H n).obj K) hhomology_nonzero
      let eExt :
          Ext^n((single₀).obj (ModuleCat.of R (R ⧸ (⊥ : Ideal R))), K) :=
        (iso_hom_congr_add_equiv (quotient_bot_single_iso (R := R)) (Iso.refl (K⟦n⟧))).symm
          ((ring_source_ext_add_equiv_hom_to_homology (K := K) n).symm f)
      have hext_zero : eExt = 0 := by
        exact h ⊥ n hn eExt
      have hf_zero : f = 0 := by
        have hzero' :=
          congrArg
            ((ring_source_ext_add_equiv_hom_to_homology (K := K) n) ∘
              (iso_hom_congr_add_equiv (quotient_bot_single_iso (R := R))
                (Iso.refl (K⟦n⟧))))
            hext_zero
        simpa [eExt] using hzero'
      exact hf hf_zero
    -- First replace the canonical lower truncation by a bounded-below injective resolution.
    letI : EnoughInjectives (ModuleCat.{u} R) := ModuleCat.enoughInjectives (R := R)
    have hGE : (DerivedCategory.Q.objPreimage K).IsGE a := by
      rw [CochainComplex.isGE_iff]
      intro n hn
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact hpre n (by
        intro hmem
        exact (not_lt_of_ge hmem.1) hn)
    letI : (DerivedCategory.Q.objPreimage K).IsGE a := hGE
    obtain ⟨I, hIge, _⟩ :=
      exists_injectiveResolution_strictlyGE_with_termwise_mono
        (K := (DerivedCategory.Q.objPreimage K).truncGE a) a inferInstance
    let α : DerivedCategory.Q.objPreimage K ⟶ (I : Cpx) :=
      ((DerivedCategory.Q.objPreimage K).πTruncGE a) ≫ I.ι
    letI : QuasiIso ((DerivedCategory.Q.objPreimage K).πTruncGE a) := inferInstance
    letI : QuasiIso I.ι := inferInstance
    letI : QuasiIso α := inferInstance
    -- Then transport the upper vanishing to the injective model and make the canonical cutoff
    -- map into a quasi-isomorphism at the specific bound `b`.
    have hupper : ∀ n : ℤ, b < n → IsZero (((I : Cpx).homology n)) := by
      intro n hn
      exact (isoOfQuasiIsoAt α n).isZero_iff.1 (hpre n (by
        intro hmem
        exact (not_lt_of_ge hmem.2) hn))
    have hIle : (I : Cpx).IsLE b := by
      rw [CochainComplex.isLE_iff]
      intro n hn
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact hupper n hn
    letI : (I : Cpx).IsLE b := hIle
    have hαQ : IsIso (DerivedCategory.Q.map α) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance
    have hι : QuasiIso ((I : Cpx).ιTruncLE b) := inferInstance
    have hιQ : IsIso (DerivedCategory.Q.map ((I : Cpx).ιTruncLE b)) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance
    have hcycles : Injective ((I : Cpx).cycles b) := by
      -- Apply the isolated tail lemma to convert the quotient-test vanishing in degree `b + 1`
      -- into injectivity of the cutoff cycles module.
      have hbnot : (b + 1 : ℤ) ∉ Set.Icc a b := by
        intro hmem
        have : ¬ (b + 1 ≤ b) := by omega
        exact this hmem.2
      refine cycles_injective_of_ideal_quotient_ext_succ_vanishing (R := R) I b
        (hupper (b + 1) (by omega)) ?_
      intro J e
      let β :
          (DerivedCategory.Q.obj (I : Cpx))⟦b + 1⟧ ≅ K⟦b + 1⟧ :=
        (shiftFunctor DMod (b + 1)).mapIso
          ((asIso (DerivedCategory.Q.map α)).symm ≪≫
            (DerivedCategory.Q.objObjPreimageIso K))
      let eK :
          Ext^(b + 1)((single₀).obj (ModuleCat.of R (R ⧸ J)), K) :=
        e ≫ β.hom
      have heK_zero : eK = 0 := h J (b + 1) hbnot eK
      have htransport :
          ((Iso.refl _).homCongr β) e = ((Iso.refl _).homCongr β) 0 := by
        simpa [eK] using heK_zero
      exact ((Iso.refl _).homCongr β).injective htransport
    have htruncInj :
        ∀ n : ℤ, Injective ((((I : Cpx).truncLE b).X n)) :=
      truncLE_terms_injective_of_cycles_injective (I : Cpx) b I.injective hcycles
    have htruncGE : ((I : Cpx).truncLE b).IsStrictlyGE a := by
      rw [CochainComplex.isStrictlyGE_iff] at hIge
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      by_cases hlt : n < b
      · exact ((truncLE_term_iso_of_lt (I : Cpx) b n hlt).isZero_iff).2 (hIge n hn)
      · by_cases hEq : n = b
        · subst n
          have hcyclesZero : IsZero (((I : Cpx).cycles b)) :=
            Limits.IsZero.of_mono ((I : Cpx).iCycles b) (hIge b hn)
          exact ((truncLE_term_iso_cycles (I : Cpx) b).isZero_iff).2 hcyclesZero
        · have hgt : b < n := by omega
          exact truncLE_term_isZero_of_gt (I : Cpx) b n hgt
    -- Finally, package the canonical upper truncation as the desired bounded injective model.
    refine ⟨(I : Cpx).truncLE b, htruncGE, inferInstance, htruncInj, ?_⟩
    exact ⟨(DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      asIso (DerivedCategory.Q.map α) ≪≫
        (asIso (DerivedCategory.Q.map ((I : Cpx).ιTruncLE b))).symm⟩
  tfae_finish

end

end CategoryTheory
