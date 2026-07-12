import Mathlib.Data.List.TFAE
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Lemma_10_77_2
import StacksProject_2024.Chap13.Lemma_13_11_5
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap13.Lemma_13_18_3
import StacksProject_2024.Chap13.Lemma_13_19_3
import StacksProject_2024.Chap13.Lemma_13_19_10
import StacksProject_2024.Chap13.Remark_13_24_3
import StacksProject_2024.Chap13.Lemma_13_27_3
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap15.Definition_15_69_1
import StacksProject_2024.Chap15.Lemma_15_66_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-
Domain-style sampling:
- primary domain: projective-amplitude criteria in `D(R)` detected by derived `Ext` against
  degree-zero modules;
- sampled owner declarations:
  `HasProjectiveAmplitudeIn` from `Definition_15_69_1`,
  `derivedExtToModuleFunctor` from `Lemma_15_66_1`,
  `ShiftedHom`,
  `Ext^i(X, Y)` from `Definition_13_27_1`,
  `existsUnique_truncation_gap_biprod_and_projectiveAmplitude_of_ext_vanishing` from
    `Lemma_15_77_6`;
- best owner abstraction:
  `source-facing`: the interval and half-line vanishing clauses in the TFAE, written as
    vanishing of the derived extension groups `Ext^i(K, N[0])`;
  `core/canonical`: the chapter owner `derivedExtToModuleFunctor K i` for the unrestricted
    degree-`i` vanishing test on modules;
  `bridge/view`: its value at `N`, namely `ShiftedHom K ((singleFunctor _ 0).obj N) i`, written in
    the chapter notation as `Ext^i(K, N[0])`.

Primitive data here are only the degree-wise vanishing statements with their module argument
visible. The “outside an interval”, “for all degrees above a bound”, and mixed cohomology-plus-Ext
clauses are derived API over the existing Ext owner, so the public theorem surface should keep the
source-facing pointwise `Ext^i(K, N[0])` clauses rather than hide `N` inside
`IsZero (derivedExtToModuleFunctor K i)`.
-/

/-
Proof sketch: follow the Stacks proof. `(1) → (2)` computes `Ext` from a bounded projective
representative. `(2) → (3)` and `(3) → (4)` test cohomology against injective modules. For
`(4) → (1)`, first deduce cohomology vanishing below `a`, choose a bounded-above projective
representative, truncate in degree `a`, and use the degree `1 - a` `Ext`-vanishing plus
Lemma `10.77.2` to show the leftmost cokernel is projective.
-/
/-- Helper for Lemma 15.69.2: transporting morphisms along source and target isomorphisms gives an
additive equivalence on Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv
    {X Y X₁ Y₁ : DMod} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := by
      intro f g
      simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp] }

/-- Helper for Lemma 15.69.2: for a bounded-above projective complex, degree-`n` homology of the
Hom complex into `M[0]` computes `Ext^n` against the represented derived object. -/
private noncomputable def projective_homology_add_equiv_ext_single
    (P : CochainComplex.ProjectiveMinus (ModuleCat R)) (M : ModuleCat R) (n : ℤ) :
    (CochainComplex.HomComplex P ((singleCpx₀).obj M)).homology n ≃+
      Ext^n(DerivedCategory.Q.obj (P : Cpx), (single₀).obj M) :=
  let e₁ :
      (CochainComplex.HomComplex P ((singleCpx₀).obj M)).homology n ≃+
        ((KQ).obj P ⟶ (KQ).obj (((singleCpx₀).obj M)⟦n⟧)) :=
    (CochainComplex.HomComplex.homologyAddEquiv P ((singleCpx₀).obj M) n).trans homAddEquiv
  let e₂ :
      ((KQ).obj P ⟶ (KQ).obj (((singleCpx₀).obj M)⟦n⟧)) ≃+
        (DerivedCategory.Q.obj (P : Cpx) ⟶
          DerivedCategory.Q.obj (((singleCpx₀).obj M)⟦n⟧)) :=
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        ((KQ).obj P ⟶ (KQ).obj (((singleCpx₀).obj M)⟦n⟧)) →+
          (DerivedCategory.Q.obj (P : Cpx) ⟶
            DerivedCategory.Q.obj (((singleCpx₀).obj M)⟦n⟧)))
      (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective
        P (((singleCpx₀).obj M)⟦n⟧))
  let e₃ :
      (DerivedCategory.Q.obj (P : Cpx) ⟶ DerivedCategory.Q.obj (((singleCpx₀).obj M)⟦n⟧)) ≃+
        Ext^n(DerivedCategory.Q.obj (P : Cpx), (single₀).obj M) :=
    iso_hom_congr_add_equiv
      (Iso.refl _)
      ((DerivedCategory.Q.commShiftIso n).app ((singleCpx₀).obj M))
  e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 15.69.2: if the source term `E^{-i}` vanishes, then the degree-`i` term of
`HomComplex(E, N[0])` vanishes. -/
lemma homComplex_single_term_isZero_of_source_term_isZero
    (E : Cpx) (N : ModuleCat R) (i : ℤ)
    (hzero : IsZero (E.X (-i))) :
    IsZero ((CochainComplex.HomComplex E ((singleCpx₀).obj N)).X i) := by
  have hdeg : (-i : ℤ) + i = 0 := by omega
  -- Degree-`i` cochains into `N[0]` are exactly module maps out of `E^{-i}`.
  let e :
      CochainComplex.HomComplex.Cochain E ((singleCpx₀).obj N) i ≃+ (E.X (-i) ⟶ N) :=
    CochainComplex.HomComplex.Cochain.toSingleEquiv
      (K := E) (X := N) (p := -i) (q := 0) (n := i) hdeg
  letI : Subsingleton (E.X (-i) ⟶ N) := ⟨fun f g ↦ hzero.eq_of_src f g⟩
  letI :
      Subsingleton (((CochainComplex.HomComplex E ((singleCpx₀).obj N)).X i) : Type _) :=
    e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton
    ((CochainComplex.HomComplex E ((singleCpx₀).obj N)).X i)

/-- Helper for Lemma 15.69.2: a bounded-above projective representative supported in degrees
`≥ a` has vanishing `Ext^i(-, N[0])` for every `i > -a`. -/
lemma projective_amplitude_ext_vanishes_upper
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {a : ℤ} (hPge : (P : Cpx).IsStrictlyGE a)
    (N : ModuleCat R) (i : ℤ) (hi : -a < i)
    (e : Ext^i(DerivedCategory.Q.obj (P : Cpx), (single₀).obj N)) :
    e = 0 := by
  have hterm : IsZero ((P : Cpx).X (-i)) := by
    -- The lower support bound kills the source term in degree `-i`.
    exact (P : Cpx).isZero_of_isStrictlyGE a (-i) (by omega)
  have hX :
      IsZero ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).X i) :=
    homComplex_single_term_isZero_of_source_term_isZero (E := (P : Cpx)) N i hterm
  have hhom :
      IsZero ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).homology i) := by
    -- Zero middle term forces zero homology in degree `i`.
    simpa using
      (ShortComplex.isZero_homology_of_isZero_X₂
        (S := (CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc i)
        (by simpa using hX))
  let eExt := projective_homology_add_equiv_ext_single (P := P) N i
  letI :
      Subsingleton
        (((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).homology i) : Type _) :=
    AddCommGrpCat.subsingleton_of_isZero hhom
  letI : Subsingleton (Ext^i(DerivedCategory.Q.obj (P : Cpx), (single₀).obj N)) :=
    eExt.symm.injective.subsingleton
  exact Subsingleton.elim _ _

/-- Helper for Lemma 15.69.2: projective amplitude in `[a, b]` implies Ext vanishing outside the
interval `[-b, -a]`. -/
lemma projective_amplitude_ext_vanishes
    {K : DMod} {a b : ℤ}
    (hK : HasProjectiveAmplitudeIn K a b)
    (N : ModuleCat R) (i : ℤ) (hi : i ∉ Set.Icc (-b) (-a))
    (e : Ext^i(K, (single₀).obj N)) :
    e = 0 := by
  rcases hK with ⟨P, eP, hPge, hPle, hPproj⟩
  have hsplit : i < -b ∨ -a < i := by
    -- Outside the closed interval means the degree is strictly below the left endpoint or
    -- strictly above the right endpoint.
    by_contra hsplit
    apply hi
    refine ⟨?_, ?_⟩ <;> omega
  rcases hsplit with hlt | hgt
  · have hQle : (DerivedCategory.Q.obj P).IsLE b := by
      -- A representative strictly supported in degrees `≤ b` lies in `D^{≤ b}`.
      rw [DerivedCategory.isLE_Q_obj_iff]
      let _ : P.IsStrictlyLE b := hPle
      infer_instance
    have hKle : K.IsLE b := t.isLE_of_iso eP.symm b
    have hSub : Subsingleton (Ext^i(K, (single₀).obj N)) := by
      -- Degrees below `-b` vanish because the source is in `D^{≤ b}` and the target module
      -- object is in `D^{≥ 0}`.
      exact shiftedHom_subsingleton_of_lt_sub
        K ((single₀).obj N) b 0 i hKle inferInstance (by omega)
    exact Subsingleton.elim _ _
  · let Pminus : CochainComplex.ProjectiveMinus (ModuleCat R) :=
      ⟨⟨P, (CochainComplex.minus_iff (ModuleCat R) P).2 ⟨b, hPle⟩⟩, fun j ↦ by
        change Projective (P.X j)
        exact hPproj j⟩
    have htransport :
        eP.homCongr (Iso.refl (((single₀).obj N)⟦i⟧)) e = 0 := by
      -- Transport the class to the chosen projective representative and compute it there.
      exact projective_amplitude_ext_vanishes_upper
        Pminus hPge N i hgt (eP.homCongr (Iso.refl (((single₀).obj N)⟦i⟧)) e)
    -- The chosen derived equivalence is faithful on Hom groups, so the original class vanishes.
    exact (eP.homCongr (Iso.refl (((single₀).obj N)⟦i⟧))).injective <| by
      simpa using htransport

/-- Helper for Lemma 15.69.2: the degree-`n` single object becomes the degree-zero single object
after shifting by `n`. -/
private noncomputable def singleFunctor_shifted_single0_iso_canonical
    (M : ModuleCat R) (n : ℤ) :
    (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅ (single₀).obj M :=
  ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso n 0 n
    (add_zero_eq_self_int (R := R) n)).app M

/-- Helper for Lemma 15.69.2: the degree-`n` single object is canonically the shift by `-n` of
the degree-zero single object. -/
private noncomputable def singleFunctor_obj_iso_shifted_single0_neg
    (M : ModuleCat R) (n : ℤ) :
    (DerivedCategory.singleFunctor (ModuleCat R) n).obj M ≅ ((single₀).obj M)⟦-n⟧ :=
  (shiftShiftNeg ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) n).symm ≪≫
    (shiftFunctor DMod (-n)).mapIso
      (singleFunctor_shifted_single0_iso_canonical (R := R) M n)

/-- Helper for Lemma 15.69.2: degree-`n` homology of an object agrees with degree-`n` homology of
its chosen `Q.objPreimage` representative. -/
private noncomputable def objPreimage_homology_iso
    (K : DMod) (n : ℤ) :
    (H n).obj K ≅ (DerivedCategory.Q.objPreimage K).homology n :=
  ((H n).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app
      (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.69.2: a nonzero degree-`n` cohomology object produces a nonzero
`Ext^{-n}`-class against some degree-zero module. -/
private lemma exists_nonzero_ext_of_nonzero_homology
    (K : DMod) (n : ℤ) (hnonzero : ¬ IsZero ((H n).obj K)) :
    ∃ (M : ModuleCat R) (e : Ext^(-n)(K, (single₀).obj M)), e ≠ 0 := by
  let E := DerivedCategory.Q.objPreimage K
  let M := differentialCokernel (R := R) (E := E) n
  let β₀ :
      DerivedCategory.Q.obj E ⟶ (DerivedCategory.singleFunctor (ModuleCat R) n).obj M :=
    DerivedCategory.Q.map (to_single_of_differential_cokernel (R := R) (E := E) n)
  let eK : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let β : K ⟶ (DerivedCategory.singleFunctor (ModuleCat R) n).obj M := eK.inv ≫ β₀
  have hβmono : Mono (homologyToSingle (R := R) n β) := by
    -- Transport the monicity of the canonical representative map along the `Q.objPreimage`
    -- comparison isomorphism.
    exact mono_homologyToSingle_precompose_iso
      (R := R) (i := n) eK β₀
      (homologyToSingle_Q_map_to_single_of_differential_cokernel_mono
        (R := R) (E := E) n)
  have hβ_homology_nonzero : homologyToSingle (R := R) n β ≠ 0 := by
    -- If the induced homology map were zero, monicity would force `H^n(K)` to vanish.
    intro hzero
    exact hnonzero (IsZero.of_mono_eq_zero (homologyToSingle (R := R) n β) hzero)
  have hβ_nonzero : β ≠ 0 := by
    -- A zero derived morphism induces the zero map on homology.
    intro hzero
    apply hβ_homology_nonzero
    simpa [β, hzero]
  let eExt :
      (K ⟶ (DerivedCategory.singleFunctor (ModuleCat R) n).obj M) ≃+
        Ext^(-n)(K, (single₀).obj M) :=
    iso_hom_congr_add_equiv
      (Iso.refl _)
      (singleFunctor_obj_iso_shifted_single0_neg (R := R) M n)
  refine ⟨M, eExt β, ?_⟩
  -- The shift-normalization equivalence detects nonzero morphisms.
  intro hzero
  apply hβ_nonzero
  exact eExt.injective (by simpa using hzero)

/-- Helper for Lemma 15.69.2: if every `Ext^{-n}(K, N[0])` class vanishes, then `H^n(K)` is zero.
-/
private lemma homology_isZero_of_ext_vanishes_at_degree
    (K : DMod) (n : ℤ)
    (hvanish : ∀ (M : ModuleCat R) (e : Ext^(-n)(K, (single₀).obj M)), e = 0) :
    IsZero ((H n).obj K) := by
  by_contra hnonzero
  obtain ⟨M, e, he⟩ := exists_nonzero_ext_of_nonzero_homology (R := R) K n hnonzero
  exact he (hvanish M e)

/-- Helper for Lemma 15.69.2: clause `(4)` gives the bounded-above projective model required by
the source proof, and the lower homology vanishing transports to that model. -/
private lemma bounded_above_projective_minus_model_of_clause4
    (K : DMod) (a b : ℤ)
    (hHabove : ∀ n : ℤ, b < n → IsZero ((H n).obj K))
    (hHbelow : ∀ n : ℤ, n < a → IsZero ((H n).obj K)) :
    ∃ (P : CochainComplex.ProjectiveMinus (ModuleCat R))
      (_ : K ≅ DerivedCategory.Q.obj (P : Cpx)),
      (P : Cpx).IsStrictlyLE b ∧
        ∀ n : ℤ, n < a → IsZero (((P : Cpx).homology n)) := by
  let C : Cpx := DerivedCategory.Q.objPreimage K
  have hCup : ∀ n : ℤ, b < n → IsZero (C.homology n) := by
    intro n hn
    -- Transport the upper cohomology vanishing of `K` to the chosen cochain representative.
    exact (objPreimage_homology_iso (R := R) K n).isZero_iff.1 (hHabove n hn)
  have hCLE : C.IsLE b := by
    -- The preimage representative is exact above `b`, so its upper truncation is a
    -- quasi-isomorphic bounded-above model.
    rw [CochainComplex.isLE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hCup n hn
  letI : C.IsLE b := hCLE
  obtain ⟨P, hPLE, _⟩ :=
    exists_projectiveResolution_strictlyLE_with_termwise_epi
      (𝒜 := ModuleCat R) (K := C.truncLE b) b inferInstance
  let Pminus : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨P, (CochainComplex.minus_iff (ModuleCat R) P).2 ⟨b, hPLE⟩⟩, fun i ↦ by
      change Projective (P.X i)
      infer_instance⟩
  let eRep : K ≅ DerivedCategory.Q.obj (Pminus : Cpx) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (C.ιTruncLE b))).symm ≪≫
        (asIso (DerivedCategory.Q.map P.π)).symm
  refine ⟨Pminus, eRep, hPLE, ?_⟩
  intro n hn
  have hzeroK : IsZero ((H n).obj K) := hHbelow n hn
  have hzeroQP : IsZero ((H n).obj (DerivedCategory.Q.obj (Pminus : Cpx))) :=
    hzeroK.of_iso ((H n).mapIso eRep.symm)
  -- Compute the derived homology of the chosen representative on the nose.
  exact ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app
    (Pminus : Cpx)).isZero_iff.1 hzeroQP

/-- Helper for Lemma 15.69.2: vanishing homology below `a` makes the smart lower truncation map
`P ⟶ P.truncGE a` a quasi-isomorphism. -/
private theorem quasiIso_piTruncGE_of_isZero_homology_below_local
    (P : Cpx) (a : ℤ)
    (hP : ∀ n : ℤ, n < a → IsZero (P.homology n)) :
    QuasiIso (P.πTruncGE a) := by
  -- Proof comment: convert the lower homology vanishing into the standard exactness owner
  -- `P.IsGE a`, then let the canonical truncation instance conclude.
  have hGE : P.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hP n hn
  letI : P.IsGE a := hGE
  infer_instance

/-- Helper for Lemma 15.69.2: on the retained range, the lower-truncation embedding `n ↦ a + n`
hits the original degree. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (a n : ℤ) (han : a ≤ n) :
    (ComplexShape.embeddingUpIntGE a).f (Int.toNat (n - a)) = n := by
  -- Proof comment: the lower-truncation embedding is affine on the surviving indices.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.69.2: above the cutoff, smart lower truncation keeps the original term. -/
private noncomputable def truncGE_term_iso_of_gt
    (P : Cpx) (a n : ℤ) (han : a < n) :
    (P.truncGE a).X n ≅ P.X n := by
  let i : ℕ := Int.toNat (n - a)
  let hi' : (ComplexShape.embeddingUpIntGE a).f i = n :=
    embeddingUpIntGE_toNat_sub_eq a n (le_of_lt han)
  let hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  -- Proof comment: once the retained index is identified, the core truncation API gives the
  -- surviving term isomorphism directly.
  exact P.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 15.69.2: in a cochain complex, the predecessor of degree `i` is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.69.2: the new degree-`a` term of `P.truncGE a` is the cutoff cokernel
`cokernel (P.dFrom (a - 1))`. -/
private noncomputable def truncGE_cutoff_term_iso_cokernel
    (P : Cpx) (a : ℤ) :
    (P.truncGE a).X a ≅ cokernel (P.dFrom (a - 1)) := by
  let eCut :
      (P.truncGE a).X a ≅ P.opcycles a :=
    P.truncGEXIsoOpcycles (e := ComplexShape.embeddingUpIntGE a) rfl <| by
      simpa using (ComplexShape.boundaryGE_embeddingUpIntGE_iff a 0).2 rfl
  let eOpcPrev :
      P.opcycles a ≅ cokernel (P.d ((ComplexShape.up ℤ).prev a) a) := by
    -- Proof comment: the degree-`a` opcycles are the cokernel of the incoming differential in
    -- the standard degree-`a` short complex.
    simpa [HomologicalComplex.opcycles, HomologicalComplex.sc] using
      (ShortComplex.opcyclesIsoCokernel (S := P.sc a))
  have hprev : (ComplexShape.up ℤ).prev a = a - 1 := by
    simpa using cochain_prev_eq a
  let eOpc :
      P.opcycles a ≅ cokernel (P.d (a - 1) a) := by
    cases hprev
    simpa using eOpcPrev
  let hrel : (ComplexShape.up ℤ).Rel (a - 1) a := by simp
  let eDFrom :
      cokernel (P.d (a - 1) a) ≅ cokernel (P.dFrom (a - 1)) := by
    let eCurr : P.X a ≅ P.xNext (a - 1) := (P.xNextIso hrel).symm
    -- Proof comment: `dFrom (a - 1)` is the same differential with the target rewritten through
    -- the canonical `xNext` identification.
    refine cokernel.mapIso (P.d (a - 1) a) (P.dFrom (a - 1)) (Iso.refl _) eCurr ?_
    simpa [eCurr, P.dFrom_eq hrel]
  exact eCut ≪≫ eOpc ≪≫ eDFrom

/-- Helper for Lemma 15.69.2: if `P` already vanishes above `b < a`, then the cutoff cokernel at
degree `a` is zero. -/
private theorem cokernel_dFrom_isZero_of_isStrictlyLE
    (P : Cpx) (a b : ℤ) (hba : b < a) (hPle : P.IsStrictlyLE b) :
    IsZero (cokernel (P.dFrom (a - 1))) := by
  rw [CochainComplex.isStrictlyLE_iff] at hPle
  have hzeroXa : IsZero (P.X a) := hPle a hba
  let hrel : (ComplexShape.up ℤ).Rel (a - 1) a := by simp
  have hzeroTarget : IsZero (P.xNext (a - 1)) := by
    -- Proof comment: the canonical `xNext` object at degree `a - 1` is just the vanished degree
    -- `a` term of the original complex.
    exact hzeroXa.of_iso (P.xNextIso hrel).symm
  letI : IsZero (P.xNext (a - 1)) := hzeroTarget
  letI : Epi (P.dFrom (a - 1)) := by infer_instance
  -- Proof comment: every map into a zero object is epi, so its cokernel vanishes.
  exact Limits.isZero_cokernel_of_epi (P.dFrom (a - 1))

/-- Helper for Lemma 15.69.2: smart lower truncation of a bounded-above complex is still bounded
above at the same bound. -/
private theorem truncGE_isStrictlyLE_of_isStrictlyLE_local
    (P : Cpx) (a b : ℤ) (hPle : P.IsStrictlyLE b) :
    (P.truncGE a).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  by_cases hna : n < a
  · -- Proof comment: below the cutoff, the smart lower truncation vanishes by construction.
    exact (P.truncGE a).isZero_of_isStrictlyGE a n hna
  · by_cases hEq : n = a
    · subst hEq
      -- Proof comment: at the cutoff degree, the term is the cokernel of a map into the already
      -- vanished degree-`a` target because `b < a`.
      exact ((truncGE_cutoff_term_iso_cokernel (P := P) a).isZero_iff).2
        (cokernel_dFrom_isZero_of_isStrictlyLE P a b hn hPle)
    · have hgt : a < n := by omega
      -- Proof comment: above the cutoff, the truncation term is canonically the original term.
      exact ((truncGE_term_iso_of_gt (P := P) a n hgt).isZero_iff).2 (by
        rw [CochainComplex.isStrictlyLE_iff] at hPle
        exact hPle n hn)

/-- Helper for Lemma 15.69.2: once the cutoff cokernel is projective, every term of the smart
lower truncation is projective. -/
private theorem truncGE_term_projective_of_cutoff_projective
    (P : Cpx) (a b n : ℤ) (hPle : P.IsStrictlyLE b)
    (hPproj : ∀ i : ℤ, Projective (P.X i))
    (hCutProj : Projective (cokernel (P.dFrom (a - 1)))) :
    Projective ((P.truncGE a).X n) := by
  by_cases hlt : n < a
  · have hzero : IsZero ((P.truncGE a).X n) :=
      (P.truncGE a).isZero_of_isStrictlyGE a n hlt
    -- Proof comment: below the cutoff, the term is zero and hence projective.
    exact Projective.of_iso hzero.isoZero (by infer_instance)
  · by_cases hEq : n = a
    · subst hEq
      -- Proof comment: the cutoff term is exactly the projective cokernel from the source proof.
      exact Projective.of_iso (truncGE_cutoff_term_iso_cokernel (P := P) a) hCutProj
    · have hgt : a < n := by omega
      -- Proof comment: above the cutoff, the truncation term is the original projective term.
      exact Projective.of_iso (truncGE_term_iso_of_gt (P := P) a n hgt) (hPproj n)

/-- Helper for Lemma 15.69.2: once the cutoff cokernel is projective, the smart lower truncation
of a bounded-above projective model is already a projective-amplitude witness. -/
private theorem hasProjectiveAmplitudeIn_of_projective_truncGE
    {K : DMod} (P : Cpx) (eP : K ≅ DerivedCategory.Q.obj P) (a b : ℤ)
    (hPbelow : ∀ n : ℤ, n < a → IsZero (P.homology n))
    (hPle : P.IsStrictlyLE b) (hPproj : ∀ i : ℤ, Projective (P.X i))
    (hCutProj : Projective (cokernel (P.dFrom (a - 1)))) :
    HasProjectiveAmplitudeIn K a b := by
  let T : Cpx := P.truncGE a
  have hπ : QuasiIso (P.πTruncGE a) :=
    quasiIso_piTruncGE_of_isZero_homology_below_local P a hPbelow
  letI : IsIso (DerivedCategory.Q.map (P.πTruncGE a)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hπ
  let eT : K ≅ DerivedCategory.Q.obj T :=
    eP ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE a))
  refine ⟨T, eT, inferInstance, ?_, ?_⟩
  · -- Proof comment: the truncation keeps the lower support bound by construction and preserves
    -- the original upper support bound degreewise.
    exact truncGE_isStrictlyLE_of_isStrictlyLE_local P a b hPle
  · intro n
    -- Proof comment: the only new term is the cutoff cokernel; all other retained terms are
    -- inherited from the original projective complex.
    exact truncGE_term_projective_of_cutoff_projective P a b n hPle hPproj hCutProj

/-- Helper for Lemma 15.69.2: on retained degrees of a lower brutal truncation, the truncated term
identifies with the original term. -/
private noncomputable def lower_stupid_truncation_term_iso
    (E : Cpx) (t : ℤ) {i : ℤ} (hti : t ≤ i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i ≅ E.X i :=
  E.stupidTruncXIso (ComplexShape.embeddingUpIntGE t)
    (embeddingUpIntGE_toNat_sub_eq t i hti)

/-- Helper for Lemma 15.69.2: the lower brutal truncation carries its canonical inclusion into the
ambient complex. -/
private noncomputable def lower_stupid_truncation_inclusion
    (E : Cpx) (t : ℤ) :
    E.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶ E where
  f i :=
    if hti : t ≤ i then
      (lower_stupid_truncation_term_iso E t hti).hom
    else
      0
  comm' i j hij := by
    by_cases hti : t ≤ i
    · have htj : t ≤ j := by
        have hj : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      rw [dif_pos hti, dif_pos htj]
      -- Proof comment: on retained degrees, the inclusion components are the canonical
      -- retained-term identifications, so compatibility with differentials is the standard
      -- brutal-truncation transport formula.
      let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
        ComplexShape.embeddingUpIntGE t
      let i₀ : ℕ := Int.toNat (i - t)
      let j₀ : ℕ := Int.toNat (j - t)
      have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq t i hti
      have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq t j htj
      change (lower_stupid_truncation_term_iso E t hti).hom ≫ E.d i j =
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
            (lower_stupid_truncation_term_iso E t htj).hom
      calc
        (lower_stupid_truncation_term_iso E t hti).hom ≫ E.d i j =
            (lower_stupid_truncation_term_iso E t hti).hom ≫
              ((lower_stupid_truncation_term_iso E t hti).inv ≫
                (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
                  (lower_stupid_truncation_term_iso E t htj).hom) := by
                have htransport :
                    (lower_stupid_truncation_term_iso E t hti).inv ≫
                      (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
                      (lower_stupid_truncation_term_iso E t htj).hom =
                        E.d i j := by
                  change (lower_stupid_truncation_term_iso E t hti).inv ≫
                      ((E.restriction e).extend e).d i j ≫
                      (lower_stupid_truncation_term_iso E t htj).hom =
                        E.d i j
                  rw [HomologicalComplex.extend_d_eq (K := E.restriction e) (e := e) hi₀ hj₀]
                  rw [HomologicalComplex.restriction_d_eq (K := E) (e := e) hi₀ hj₀]
                  simp [lower_stupid_truncation_term_iso, HomologicalComplex.stupidTrunc,
                    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e,
                    i₀, j₀]
                rw [htransport]
        _ = (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
              (lower_stupid_truncation_term_iso E t htj).hom := by
              simp [Category.assoc]
    · have hzero :
          IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i) := by
        -- Proof comment: below the cutoff, the lower brutal truncation has no degree-`i` term.
        exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) i
          (by
            simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
              lt_of_not_ge hti)
      by_cases htj : t ≤ j
      · have hsrczero :
            (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j = 0 :=
          hzero.eq_of_src ((E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j) 0
        simp [lower_stupid_truncation_inclusion, hti, htj, hsrczero]
      · simp [lower_stupid_truncation_inclusion, hti, htj]

/-- Helper for Lemma 15.69.2: the lower brutal truncation is strictly supported in degrees
`≥ t`. -/
private theorem lower_stupid_truncation_isStrictlyGE_local
    (E : Cpx) (t : ℤ) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).IsStrictlyGE t := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  -- Proof comment: below the cutoff, the lower brutal truncation vanishes by construction.
  exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) i
    (by
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi)

/-- Helper for Lemma 15.69.2: if the ambient complex is strictly supported above `b`, then so is
its lower brutal truncation. -/
private theorem lower_stupid_truncation_isStrictlyLE_local
    (E : Cpx) (t b : ℤ) (hE : E.IsStrictlyLE b) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE t)).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hti : t ≤ i
  · -- Proof comment: on retained degrees, transport the vanishing statement from the ambient
    -- complex.
    exact ((lower_stupid_truncation_term_iso E t hti).isZero_iff).2 (by
      rw [CochainComplex.isStrictlyLE_iff] at hE
      exact hE i hi)
  · -- Proof comment: below the cutoff, the lower brutal truncation vanishes by construction.
    exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) i
      (by
        simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
          lt_of_not_ge hti)

/-- Helper for Lemma 15.69.2: the brutal cut of `P.truncGE a` by the lower truncation at `a + 1`
is a short exact sequence whose quotient is the degree-`a` single complex on the cutoff
cokernel. -/
private theorem truncGE_brutal_cut_shortExact
    (P : Cpx) (a : ℤ) :
    let T : Cpx := P.truncGE a
    let Tail : Cpx := T.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))
    let Qmod : ModuleCat R := cokernel (P.dFrom (a - 1))
    let g : T ⟶ (CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod :=
      { f := fun i ↦
          if hia : i = a then
            hia.rec
              ((truncGE_cutoff_term_iso_cokernel (P := P) a).hom ≫
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Qmod).inv)
          else
            0
        comm' := by
          intro i j hij
          have hj : j = i + 1 := by
            simpa [ComplexShape.up, eq_comm] using hij
          by_cases hlt : i < a
          · have hzeroTi : IsZero ((P.truncGE a).X i) :=
              (P.truncGE a).isZero_of_isStrictlyGE a i hlt
            have hright :
                (P.truncGE a).d i j ≫
                  (if hja : j = a then
                    hja.rec
                      ((truncGE_cutoff_term_iso_cokernel (P := P) a).hom ≫
                        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Qmod).inv)
                  else
                    0) = 0 := by
              exact hzeroTi.eq_of_src _ _
            have hleft :
                (if hia : i = a then
                  hia.rec
                    ((truncGE_cutoff_term_iso_cokernel (P := P) a).hom ≫
                      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Qmod).inv)
                else
                  0) ≫
                  ((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).d i j = 0 := by
              by_cases hia : i = a
              · omega
              · simp [hia]
            simp [hleft, hright]
          · by_cases hia : i = a
            · subst hia
              have hja : j ≠ a := by omega
              have hsingle :
                  ((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).d a j = 0 := by
                exact HomologicalComplex.isZero_single_obj_d_to (ComplexShape.up ℤ) a Qmod j hja
              simp [hja, hsingle]
            · have hgt : a < i := by omega
              have hia' : i ≠ a := hia
              have hja : j ≠ a := by omega
              have hsingleX :
                  IsZero (((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).X i) :=
                HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a Qmod i hia'
              have hleft :
                  (0 :
                    (P.truncGE a).X i ⟶
                      ((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).X i) ≫
                    ((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).d i j = 0 := by
                simp
              have hright :
                  (P.truncGE a).d i j ≫
                    (0 :
                      (P.truncGE a).X j ⟶
                        ((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).X j) = 0 := by
                simp
              simp [hia, hja, hleft, hright]
      }
    let S :
        ShortComplex (Cpx) :=
      ShortComplex.mk
        (lower_stupid_truncation_inclusion T (a + 1))
        g
        (by
          ext i
          by_cases hia : i = a
          · subst hia
            have hzero :
                IsZero ((Tail : Cpx).X a) := by
              exact T.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) a
                (by
                  simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
                    (show a < a + 1 by omega))
            exact hzero.eq_of_src _ _
          · have hia_lt : i < a ∨ a < i := by omega
            rcases hia_lt with hi_lt | hi_gt
            · have hzero :
                  IsZero ((Tail : Cpx).X i) := by
                exact T.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) i
                  (by
                    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
                      (show i < a + 1 by omega))
              exact hzero.eq_of_src _ _
            · simp [ShortComplex.mk, g, lower_stupid_truncation_inclusion, hi_gt.ne, hia])
    S.ShortExact := by
  intro T Tail Qmod g S
  -- Proof comment: degreewise the brutal cut splits in the three source-proof regions
  -- `n < a`, `n = a`, and `a < n`.
  refine HomologicalComplex.shortExact_of_degreewise_shortExact S ?_
  intro n
  by_cases hlt : n < a
  · have hzero₁ : IsZero (((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).X₁)) := by
      exact (T.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) n
        (by
          simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
            (show n < a + 1 by omega)))
    have hzero₂ :
        IsZero (((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).X₂)) := by
      exact (P.truncGE a).isZero_of_isStrictlyGE a n hlt
    have hzero₃ :
        IsZero (((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).X₃)) := by
      exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a Qmod n (by omega)
    have hg : IsIso ((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).g) := by
      exact hzero₂.isIso hzero₃ _
    exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hzero₁ hg |>.shortExact
  · by_cases hEq : n = a
    · subst hEq
      have hzero₁ :
          IsZero (((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) a)).X₁)) := by
        exact T.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) a
          (by
            simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
              (show a < a + 1 by omega))
      have hg :
          IsIso ((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) a)).g) := by
        dsimp [S, g, ShortComplex.map, Functor.map]
        rw [dif_pos rfl]
        change IsIso
          ((truncGE_cutoff_term_iso_cokernel (P := P) a).hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Qmod).inv)
        infer_instance
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hzero₁ hg |>.shortExact
    · have hgt : a < n := by omega
      have hzero₃ :
          IsZero (((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).X₃)) := by
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a Qmod n hEq
      have hf :
          IsIso ((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).f) := by
        dsimp [S, ShortComplex.map, Functor.map]
        rw [dif_pos (by omega)]
        infer_instance
      exact ShortComplex.Splitting.ofIsIsoOfIsZero _ hf hzero₃ |>.shortExact

/-- Helper for Lemma 15.69.2: the lower brutal truncation of `P.truncGE a` removes the cutoff
term and still witnesses projective-amplitude in `[a + 1, b]`. -/
private theorem truncGE_tail_hasProjectiveAmplitudeIn
    (P : Cpx) (a b : ℤ) (hPle : P.IsStrictlyLE b)
    (hPproj : ∀ i : ℤ, Projective (P.X i)) :
    let T : Cpx := P.truncGE a
    let Tail : Cpx := T.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))
    HasProjectiveAmplitudeIn (DerivedCategory.Q.obj Tail) (a + 1) b := by
  intro T Tail
  refine ⟨Tail, Iso.refl _, ?_, ?_, ?_⟩
  · exact lower_stupid_truncation_isStrictlyGE_local T (a + 1)
  · exact lower_stupid_truncation_isStrictlyLE_local T (a + 1) b
      (truncGE_isStrictlyLE_of_isStrictlyLE_local P a b hPle)
  · intro n
    by_cases hn : n < a + 1
    · have hzero : IsZero (Tail.X n) :=
        T.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) n
          (by
            simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hn)
      -- Proof comment: below `a + 1`, the tail vanishes and is therefore projective.
      exact Projective.of_iso hzero.isoZero (by infer_instance)
    · have hge : a + 1 ≤ n := by omega
      have hgt : a < n := by omega
      -- Proof comment: above the cutoff, the tail and the smart truncation agree with the
      -- original complex termwise.
      exact Projective.of_iso
        ((lower_stupid_truncation_term_iso T (a + 1) hge) ≪≫
          truncGE_term_iso_of_gt (P := P) a n hgt)
        (hPproj n)

/-- Helper for Lemma 15.69.2: `Ext^(1 - a)` from the degree-`a` single object agrees with the
module-side `Ext¹`. -/
private noncomputable def single_degree_ext_one_equiv
    (Q N : ModuleCat R) (a : ℤ) :
    Ext^(1 - a)((DerivedCategory.singleFunctor (ModuleCat R) a).obj Q, (single₀).obj N) ≃+
      CategoryTheory.Abelian.Ext Q N 1 :=
  let e₁ :
      Ext^(1 - a)((DerivedCategory.singleFunctor (ModuleCat R) a).obj Q, (single₀).obj N) ≃+
        ((((single₀).obj Q)⟦-a⟧) ⟶ ((single₀).obj N)⟦(1 - a : ℤ)⟧) :=
    iso_hom_congr_add_equiv
      (singleFunctor_obj_iso_shifted_single0_neg (R := R) Q a)
      (Iso.refl _)
  let e₂ :
      ((((single₀).obj Q)⟦-a⟧) ⟶ ((single₀).obj N)⟦(1 - a : ℤ)⟧) ≃+
        (((single₀).obj Q) ⟶ (((single₀).obj N)⟦(1 - a : ℤ)⟧)⟦a⟧) :=
    AddEquiv.ofEquiv
      (((shiftEquiv DMod a).symm.toAdjunction.homEquiv
          ((single₀).obj Q) (((single₀).obj N)⟦(1 - a : ℤ)⟧)))
      (by
        intro f g
        simp)
  let e₃ :
      (((single₀).obj Q) ⟶ (((single₀).obj N)⟦(1 - a : ℤ)⟧)⟦a⟧) ≃+
        (((single₀).obj Q) ⟶ ((single₀).obj N)⟦(1 : ℤ)⟧) :=
    iso_hom_congr_add_equiv
      (Iso.refl _)
      ((shiftFunctorAdd' DMod (1 - a : ℤ) a (1 : ℤ) (by omega)).app ((single₀).obj N))
  let e₄ :
      (((single₀).obj Q) ⟶ ((single₀).obj N)⟦(1 : ℤ)⟧) ≃+
        CategoryTheory.Abelian.Ext Q N 1 :=
    (CategoryTheory.Abelian.Ext.homEquiv
      (C := ModuleCat R) (X := Q) (Y := N) (n := 1)).symm
  e₁.trans (e₂.trans (e₃.trans e₄))

/-- Helper for Lemma 15.69.2: the remaining source-faithful closing step is to show the cutoff
cokernel of the bounded-above projective model is projective from clause `(4)`. -/
private theorem cutoff_cokernel_projective_of_clause4
    (K : DMod) (a b : ℤ) (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (eP : K ≅ DerivedCategory.Q.obj (P : Cpx))
    (hPle : (P : Cpx).IsStrictlyLE b)
    (hPbelow : ∀ n : ℤ, n < a → IsZero (((P : Cpx).homology n)))
    (hClause4 : ∀ (N : ModuleCat R), ∀ e : Ext^(-a + 1)(K, (single₀).obj N), e = 0) :
    Projective (cokernel (((P : Cpx).dFrom (a - 1)))) := by
  -- Route correction: the remaining source-faithful step must run on `T := P.truncGE a`,
  -- cut it by the brutal short exact sequence `σ_{≥ a + 1}T ⟶ T ⟶ σ_{≤ a}T`, identify the right
  -- term with the single object in degree `a`, and read the resulting exact `Ext` row.
  let T : Cpx := (P : Cpx).truncGE a
  let Tail : Cpx := T.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))
  let Qmod : ModuleCat R := cokernel (((P : Cpx).dFrom (a - 1)))
  have hTailAmp :
      HasProjectiveAmplitudeIn (DerivedCategory.Q.obj Tail) (a + 1) b :=
    truncGE_tail_hasProjectiveAmplitudeIn (P := (P : Cpx)) a b hPle (fun n ↦ by
      change Projective (((P : Cpx).X n))
      exact P.2 n)
  have hTailZero :
      ∀ (N : ModuleCat R), ∀ e : Ext^(-a)(DerivedCategory.Q.obj Tail, (single₀).obj N), e = 0 := by
    intro N e
    exact projective_amplitude_ext_vanishes hTailAmp N (-a) (by
      intro hmem
      omega) e
  have hπ : QuasiIso (((P : Cpx).πTruncGE a)) :=
    quasiIso_piTruncGE_of_isZero_homology_below_local (P := (P : Cpx)) a hPbelow
  letI : IsIso (DerivedCategory.Q.map (((P : Cpx).πTruncGE a))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hπ
  let eT : K ≅ DerivedCategory.Q.obj T :=
    eP ≪≫ asIso (DerivedCategory.Q.map (((P : Cpx).πTruncGE a)))
  have hClause4T :
      ∀ (N : ModuleCat R), ∀ e : Ext^(1 - a)(DerivedCategory.Q.obj T, (single₀).obj N), e = 0 := by
    intro N e
    have htransport :
        (eT.symm.homCongr (Iso.refl (((single₀).obj N)⟦(1 - a : ℤ)⟧))) e = 0 := by
      exact hClause4 N ((eT.symm.homCongr (Iso.refl (((single₀).obj N)⟦(1 - a : ℤ)⟧))) e)
    exact (eT.symm.homCongr (Iso.refl (((single₀).obj N)⟦(1 - a : ℤ)⟧))).injective htransport
  have hShortExact :
      let T : Cpx := (P : Cpx).truncGE a
      let Tail : Cpx := T.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))
      let Qmod : ModuleCat R := cokernel (((P : Cpx).dFrom (a - 1)))
      let g : T ⟶ (CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod :=
        { f := fun i ↦
            if hia : i = a then
              hia.rec
                ((truncGE_cutoff_term_iso_cokernel (P := (P : Cpx)) a).hom ≫
                  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Qmod).inv)
            else
              0
          comm' := by
            intro i j hij
            have hj : j = i + 1 := by
              simpa [ComplexShape.up, eq_comm] using hij
            by_cases hlt : i < a
            · have hzeroTi : IsZero (T.X i) := T.isZero_of_isStrictlyGE a i hlt
              have hright :
                  T.d i j ≫
                    (if hja : j = a then
                      hja.rec
                        ((truncGE_cutoff_term_iso_cokernel (P := (P : Cpx)) a).hom ≫
                          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Qmod).inv)
                    else
                      0) = 0 := by
                exact hzeroTi.eq_of_src _ _
              have hleft :
                  (if hia : i = a then
                    hia.rec
                      ((truncGE_cutoff_term_iso_cokernel (P := (P : Cpx)) a).hom ≫
                        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Qmod).inv)
                  else
                    0) ≫
                    ((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).d i j = 0 := by
                by_cases hia : i = a
                · omega
                · simp [hia]
              simp [hleft, hright]
            · by_cases hia : i = a
              · subst hia
                have hja : j ≠ a := by omega
                have hsingle :
                    ((CochainComplex.singleFunctor (ModuleCat R) a).obj Qmod).d a j = 0 := by
                  exact HomologicalComplex.isZero_single_obj_d_to
                    (ComplexShape.up ℤ) a Qmod j hja
                simp [hja, hsingle]
              · have hia' : i ≠ a := hia
                have hja : j ≠ a := by omega
                simp [hia, hja]
        }
      let S :
          ShortComplex (Cpx) :=
        ShortComplex.mk
          (lower_stupid_truncation_inclusion T (a + 1))
          g
          (by
            ext i
            by_cases hia : i = a
            · subst hia
              have hzero :
                  IsZero (Tail.X a) := by
                exact T.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) a
                  (by
                    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
                      (show a < a + 1 by omega))
              exact hzero.eq_of_src _ _
            · have hia_lt : i < a ∨ a < i := by omega
              rcases hia_lt with hi_lt | hi_gt
              · have hzero :
                    IsZero (Tail.X i) := by
                  exact T.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) i
                    (by
                      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
                        (show i < a + 1 by omega))
                exact hzero.eq_of_src _ _
              · simp [ShortComplex.mk, g, lower_stupid_truncation_inclusion, hi_gt.ne, hia])
      S.ShortExact :=
    truncGE_brutal_cut_shortExact (P := (P : Cpx)) a
  have hDist :
      DerivedCategory.triangleOfSES hShortExact ∈ distTriang DMod := by
    simpa using DerivedCategory.triangleOfSES_distinguished hShortExact
  have hSingleExtZero :
      ∀ (N : ModuleCat R),
        ∀ e : Ext^(1 - a)
          ((DerivedCategory.singleFunctor (ModuleCat R) a).obj Qmod)
          ((single₀).obj N), e = 0 := by
    intro N e
    let W : DMod := ((single₀).obj N)⟦(1 - a : ℤ)⟧
    let f :
        (DerivedCategory.triangleOfSES hShortExact).obj₃ ⟶ W := by
      simpa [W, DerivedCategory.triangleOfSES] using e
    have hf_zero :
        (DerivedCategory.triangleOfSES hShortExact).mor₂ ≫ f = 0 := by
      -- Proof comment: clause `(4)` transported to `T` kills the right-hand Ext term.
      exact hClause4T N (by simpa [f, W, DerivedCategory.triangleOfSES] using
        ((DerivedCategory.triangleOfSES hShortExact).mor₂ ≫ f))
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃
      (T := DerivedCategory.triangleOfSES hShortExact) hDist f hf_zero
    have hg_zero : g = 0 := by
      -- Proof comment: the factor lands in the vanishing group `Ext^{-a}(Tail, N[0])`.
      exact hTailZero N (by simpa [W, DerivedCategory.triangleOfSES] using g)
    simpa [f, W, DerivedCategory.triangleOfSES, hg_zero] using hg
  have hExtOneSubsingleton :
      ∀ (M : Type u) (_ : AddCommGroup M) (_ : Module R M),
        Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of R (Qmod : Type u))
          (ModuleCat.of R M) 1) := by
    intro M _ _
    let N : ModuleCat R := ModuleCat.of R M
    let eEquiv := single_degree_ext_one_equiv (R := R) Qmod N a
    refine ⟨fun x y ↦ ?_⟩
    apply eEquiv.symm.injective
    have hx : eEquiv.symm x = 0 := hSingleExtZero N (eEquiv.symm x)
    have hy : eEquiv.symm y = 0 := hSingleExtZero N (eEquiv.symm y)
    rw [hx, hy]
  have hModuleProj :
      Module.Projective R (Qmod : Type u) :=
    ((module_projective_direct_summand_free_extOne_tfae (R := R)
      (P := (Qmod : Type u))).out 2 0) hExtOneSubsingleton
  letI : Module.Projective R (Qmod : Type u) := hModuleProj
  exact inferInstance

/-- Lemma 15.69.2: for an object `K` of `D(R)` and integers `a, b`, the following are
equivalent: `K` has projective-amplitude in `[a, b]`; the derived `Ext` groups
`Ext^i_R(K, N)` vanish for every `R`-module `N` and every
`i ∉ [-b, -a]`; `H^n(K)` vanishes for `n > b` and these groups vanish for all `i > -a`; and
`H^n(K)` vanishes for `n ∉ [a - 1, b]` and `Ext^{-a + 1}_R(K, N)` vanishes for every
`R`-module `N`. -/
@[stacks 0A5P]
theorem projectiveAmplitudeIn_ext_vanishing_tfae
    (K : DMod) (a b : ℤ) :
    List.TFAE
      [ HasProjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          ∀ e : Ext^i(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, b < n → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R) (i : ℤ), -a < i → ∀ e : Ext^i(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, n ∉ Set.Icc (a - 1) b → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R), ∀ e : Ext^(-a + 1)(K, (single₀).obj N), e = 0
      ] := by
  -- Route correction: the source-proof `(1) → (2)` is implemented directly on a bounded
  -- projective representative. The remaining source-faithful blocker is the injective-target
  -- comparison used to pass between Ext vanishing and cohomology vanishing.
  tfae_have 1 → 2 := by
    intro hK N i hi e
    -- Condition `(2)` is exactly the explicit Ext-vanishing computed above.
    exact projective_amplitude_ext_vanishes hK N i hi e
  tfae_have 2 → 3 := by
    intro h
    constructor
    · intro n hn
      -- A nonzero `H^n(K)` would produce a forbidden `Ext^{-n}`-class.
      refine homology_isZero_of_ext_vanishes_at_degree (R := R) K n ?_
      intro M e
      exact h M (-n) (by
        intro hmem
        exact hn (by omega)) e
    · intro N i hi e
      -- The upper-half Ext vanishing is an immediate restriction of condition `(2)`.
      exact h N i (by
        intro hmem
        exact hi hmem.2) e
  tfae_have 3 → 4 := by
    intro h
    constructor
    · intro n hn
      by_cases hnb : b < n
      · -- Above `b` the cohomology already vanishes by condition `(3)`.
        exact h.1 n hnb
      · have hna : n < a - 1 := by omega
        -- Below `a - 1`, the degree `-n` lies in the upper-vanishing range from `(3)`.
        refine homology_isZero_of_ext_vanishes_at_degree (R := R) K n ?_
        intro M e
        exact h.2 M (-n) (by omega) e
    · intro N e
      -- The distinguished degree `-a + 1` lies in the upper-vanishing range of condition `(3)`.
      exact h.2 N (-a + 1) (by omega) e
  tfae_have 4 → 1 := by
    intro h
    have hHa1 : IsZero ((H (a - 1)).obj K) := by
      -- The distinguished vanishing degree in clause `(4)` forces `H^(a - 1)(K)` to vanish.
      refine homology_isZero_of_ext_vanishes_at_degree (R := R) K (a - 1) ?_
      intro N e
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.2 N e
    have hHabove : ∀ n : ℤ, b < n → IsZero ((H n).obj K) := by
      intro n hn
      exact h.1 n (by
        intro hmem
        exact hn hmem.2)
    have hHbelow : ∀ n : ℤ, n < a → IsZero ((H n).obj K) := by
      intro n hn
      by_cases hEq : n = a - 1
      · subst hEq
        exact hHa1
      · exact h.1 n (by
          intro hmem
          have : n < a - 1 := by omega
          exact this.not_le hmem.1)
    obtain ⟨P, eP, hPle, hPbelow⟩ :=
      bounded_above_projective_minus_model_of_clause4
        (R := R) K a b hHabove hHbelow
    have hCutProj :
        Projective (cokernel (((P : Cpx).dFrom (a - 1)))) :=
      cutoff_cokernel_projective_of_clause4
        (K := K) a b P eP hPle hPbelow h.2
    -- Proof comment: once the cutoff cokernel is projective, smart lower truncation supplies the
    -- desired bounded projective representative in the source interval `[a, b]`.
    exact
      hasProjectiveAmplitudeIn_of_projective_truncGE
        (K := K) (P := (P : Cpx)) eP a b hPbelow hPle
        (fun n ↦ by
          change Projective (((P : Cpx).X n))
          exact P.2 n)
        hCutProj
  tfae_finish

end

end CategoryTheory
