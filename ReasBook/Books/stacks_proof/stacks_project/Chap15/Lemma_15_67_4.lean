import Mathlib
import StacksProject_2024.Chap10.Lemma_10_75_8
import StacksProject_2024.Chap10.Lemma_10_39_13
import StacksProject_2024.Chap13.Lemma_13_11_5
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Lemma_15_59_6
import StacksProject_2024.Chap15.Lemma_15_59_7
import StacksProject_2024.Chap15.Lemma_15_59_10
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_67_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open DerivedCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => homologyFunctor (ModuleCat R)
local notation "Q" => DerivedCategory.Q
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.67.4:
- primary domain: lower-bounded tor-amplitude in `D(R)` and representative complexes computing
  derived tensor products with degree-zero modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the lower-bound condition should be phrased through the canonical
  t-structure owner `IsGE` on each derived tensor product `K ⊗[R]^L M[0]`, while the
  representative side should expose the primitive complex predicates directly instead of bundling
  them into a new wrapper class;
- primitive vs. derived:
  primitive data are a representative complex `E`, its support condition `E.IsStrictlyGE a`, its
  K-flatness and termwise flatness, and an isomorphism `K ≅ Q.obj E`;
  derived API is the lower-bounded tor-amplitude predicate on `K`, together with the equivalence
  between that predicate and the existence of such a representative;
- source/core/bridge triage:
  `source-facing`: `HasTorAmplitudeGE` and the main equivalence theorem below;
  `core/canonical`: `DerivedCategory.IsGE`, `DerivedCategory.isGE_iff`, `CochainComplex.IsKFlat`,
    `CochainComplex.IsTermwiseFlat`, and `CochainComplex.IsStrictlyGE`;
  `bridge/view`: the use of `K ⊗[R]^L M[0]` to transport the derived-category lower-bound
    condition to a concrete K-flat flat representative.
-/

/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` if tensoring with any degree-zero
`R`-module produces an object of the derived category lying in degrees `≥ a`. -/
def HasTorAmplitudeGE (K : DMod) (a : ℤ) : Prop :=
  ∀ M : ModuleCat R, (K ⊗[R]^L (single₀).obj M).IsGE a

/-- Finite-interval tor-amplitude in `[a, b]` implies lower tor-amplitude in `[a, ∞]`. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE {K : DMod} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeGE K a := by
  intro M
  rw [isGE_iff]
  intro i hi
  exact hK M i fun hmem ↦ (not_lt_of_ge hmem.1 hi).elim

-- Proof sketch: unfold `HasTorAmplitudeGE` and rewrite the derived-category `IsGE` condition by
-- the canonical t-structure characterization in terms of vanishing of homology below degree `a`.
/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` exactly when tensoring with any degree-zero
`R`-module has vanishing homology in every degree `< a`. -/
theorem hasTorAmplitudeGE_iff
    (K : DMod) (a : ℤ) :
    HasTorAmplitudeGE K a ↔
      ∀ (M : ModuleCat R) (i : ℤ), i < a →
        IsZero ((H i).obj (K ⊗[R]^L (single₀).obj M)) := by
  simp [HasTorAmplitudeGE, isGE_iff]

/-- Helper for Lemma 15.67.4: lower tor-amplitude is invariant under isomorphism in `D(R)`. -/
private theorem hasTorAmplitudeGE_iff_of_iso {K L : DMod} {a : ℤ} (e : K ≅ L) :
    HasTorAmplitudeGE K a ↔ HasTorAmplitudeGE L a := by
  rw [hasTorAmplitudeGE_iff, hasTorAmplitudeGE_iff]
  constructor
  · intro h M i hi
    -- Proof comment: transport the derived tensor homology along the induced tensor isomorphism.
    exact
      (h M i hi).of_iso
        ((H i).mapIso ((derivedTensorProduct ((single₀).obj M)).mapIso e.symm))
  · intro h M i hi
    -- Proof comment: the converse direction uses the inverse tensor transport.
    exact
      (h M i hi).of_iso
        ((H i).mapIso ((derivedTensorProduct ((single₀).obj M)).mapIso e))

/-- Helper for Lemma 15.67.4: if `Q.obj E` has lower tor-amplitude `≥ a`, then the representative
`E` has zero homology below `a`. -/
private theorem isZero_homology_of_hasTorAmplitudeGE_below
    (E : Cpx) (a i : ℤ) (hTor : HasTorAmplitudeGE (Q.obj E) a) (hi : i < a) :
    IsZero (E.homology i) := by
  let eUnit :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app (ModuleCat.of R R)) ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (ModuleCat.of R R))).symm
  let eRing :
      (Q.obj E) ⊗[R]^L (single₀).obj (ModuleCat.of R R) ≅ Q.obj E :=
    (derivedTensorProduct_comm (Q.obj E) ((single₀).obj (ModuleCat.of R R))) ≪≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct
        ((single₀).obj (ModuleCat.of R R)) (Q.obj E)).symm ≪≫
        whiskerRightIso eUnit (Q.obj E) ≪≫
          λ_ (Q.obj E)
  have hGEtensor :
      ((Q.obj E) ⊗[R]^L (single₀).obj (ModuleCat.of R R)).IsGE a :=
    hTor (ModuleCat.of R R)
  rw [isGE_iff] at hGEtensor
  have hzero_tensor :
      IsZero ((H i).obj ((Q.obj E) ⊗[R]^L (single₀).obj (ModuleCat.of R R))) := by
    -- Evaluate tor-amplitude on the regular module `R`.
    exact hGEtensor i hi
  have hzero_Q : IsZero ((H i).obj (Q.obj E)) :=
    hzero_tensor.of_iso ((H i).mapIso eRing).symm
  -- Compare derived homology with ordinary homology on the chosen representative.
  exact ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E).isZero_iff.1 hzero_Q

/-- Helper for Lemma 15.67.4: degreewise right tensoring preserves a strict lower support bound. -/
private theorem tensorRight_isStrictlyGE_of_isStrictlyGE
    (E : Cpx) (M : ModuleCat R) (a : ℤ) (hE : E.IsStrictlyGE a) :
    CochainComplex.IsStrictlyGE
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E) a := by
  -- Right tensoring is applied degreewise, so zero terms below `a` remain zero after tensoring.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hzeroEi : IsZero (E.X i) := by
    let _ : E.IsStrictlyGE a := hE
    exact E.isZero_of_isStrictlyGE a i hi
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (CategoryTheory.MonoidalCategory.tensorRight M).map_isZero hzeroEi

/-- Helper for Lemma 15.67.4: if `E` is strictly supported in degrees `≥ a`, then its ordinary
tensor with a degree-zero module has zero homology below `a`. -/
private theorem tensorObj_single0_homology_isZero_of_isStrictlyGE
    (E : Cpx) (M : ModuleCat R) (a i : ℤ) (hE : E.IsStrictlyGE a) (hi : i < a) :
    IsZero ((HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).homology i) := by
  let T :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E)
  have hTstrict : T.IsStrictlyGE a :=
    tensorRight_isStrictlyGE_of_isStrictlyGE E M a hE
  let _ : T.IsStrictlyGE a := hTstrict
  have hTge : T.IsGE a := inferInstance
  rw [CochainComplex.isGE_iff] at hTge
  have hExact : T.ExactAt i := hTge i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hExact
  -- Proof comment: compare the tensor-with-single complex to degreewise tensoring on the right.
  exact hExact.of_iso
    (ShortComplex.homologyMapIso
      (CochainComplex.tensor_single0_shortComplex_iso (R := R) E M i))

/-- Helper for Lemma 15.67.4: a K-flat strictly-below-zero-free representative already realizes
the lower tor-amplitude condition. -/
private theorem hasTorAmplitudeGE_of_representative
    {K : DMod} (E : Cpx) (e : K ≅ Q.obj E) (a : ℤ)
    (hGE : E.IsStrictlyGE a) (hKFlat : E.IsKFlat) :
    HasTorAmplitudeGE K a := by
  apply (hasTorAmplitudeGE_iff_of_iso (a := a) e).2
  rw [hasTorAmplitudeGE_iff]
  intro M i hi
  have hzeroOrd :
      IsZero ((HomologicalComplex.tensorObj E
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).homology i) :=
    tensorObj_single0_homology_isZero_of_isStrictlyGE E M a i hGE hi
  have hzeroDerived :
      IsZero ((H i).obj ((Q.obj E) ⊗[R]^L (single₀).obj M)) := by
    -- Proof comment: the public homology bridge from Lemma `15.67.2` computes the derived tensor
    -- homology on a K-flat representative.
    exact hzeroOrd.of_iso
      (CochainComplex.tensorObj_single0_homology_iso_derivedTensor (R := R) E i M).symm
  -- Proof comment: the K-flat hypothesis is the reason the public bridge applies to `E`.
  let _ : E.IsKFlat := hKFlat
  exact hzeroDerived

/-- Helper for Lemma 15.67.4: on the retained range, the lower-truncation embedding
`n ↦ a + n` lands in the original degree `n`. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (a n : ℤ) (han : a ≤ n) :
    (ComplexShape.embeddingUpIntGE a).f (Int.toNat (n - a)) = n := by
  -- Proof comment: `embeddingUpIntGE a` is affine on the surviving indices.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.67.4: in a cochain complex, the predecessor of degree `i` is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.67.4: above the cutoff, smart lower truncation keeps the original term. -/
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
  -- Proof comment: the generic truncation API returns the original term once we identify the
  -- surviving index and show it is not the boundary index.
  exact P.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 15.67.4: the new degree-`a` term of `P.truncGE a` is the source cutoff
cokernel `cokernel (P.dFrom (a - 1))`. -/
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

/-- Helper for Lemma 15.67.4: once the cutoff cokernel is flat, smart lower truncation is
termwise flat. -/
private theorem truncGE_isTermwiseFlat_of_flat_cokernel
    (P : Cpx) (a : ℤ) (hFlat : P.IsTermwiseFlat)
    (hCutFlat : Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R))) :
    (P.truncGE a).IsTermwiseFlat := by
  intro i
  by_cases hi_lt : i < a
  · -- Proof comment: below the cutoff the smart truncation term is zero, hence flat.
    let hzero : IsZero ((P.truncGE a).X i) := (P.truncGE a).isZero_of_isStrictlyGE a i hi_lt
    letI : Module.Flat R ((0 : ModuleCat R) : Type u) := Module.Flat.of_free
    exact Module.Flat.of_linearEquiv hzero.isoZero.toLinearEquiv
  · by_cases hi_eq : i = a
    · subst hi_eq
      letI : Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R)) := hCutFlat
      exact Module.Flat.of_linearEquiv (truncGE_cutoff_term_iso_cokernel (P := P) a).toLinearEquiv
    · have hgt : a < i := by omega
      letI : Module.Flat R (P.X i : Type u) := hFlat i
      exact Module.Flat.of_linearEquiv (truncGE_term_iso_of_gt (P := P) a i hgt).toLinearEquiv

/-- Helper for Lemma 15.67.4: the differential cokernel in degree `a` is canonically the cokernel
of `dFrom (a - 1)`. -/
private noncomputable theorem differentialCokernel_iso_cokernel_dFrom_local
    (E : Cpx) (a : ℤ) :
    differentialCokernel (R := R) (E := E) a ≅ cokernel (E.dFrom (a - 1)) := by
  let hrel : (ComplexShape.up ℤ).Rel (a - 1) a := by simp
  let eCurr : E.X a ≅ E.xNext (a - 1) := (E.xNextIso hrel).symm
  -- Proof comment: `dFrom (a - 1)` is the incoming differential rewritten through `xNext`.
  refine cokernel.mapIso (E.d (a - 1) a) (E.dFrom (a - 1)) (Iso.refl _) eCurr ?_
  simpa [differentialCokernel, eCurr, E.dFrom_eq hrel]

/-- Helper for Lemma 15.67.4: below the cutoff, tensoring the upper stupid truncation of a K-flat
representative computes the same derived homology as tensoring the original representative. -/
private theorem upper_window_tensor_homology_iso_below_cutoff_of_isKFlat
    (P : Cpx) (a : ℤ) (hKFlat : P.IsKFlat) (hFlat : P.IsTermwiseFlat)
    (N : ModuleCat R) (i : ℤ) (hi : i < a) :
    (H i).obj
        ((Q.obj (P.stupidTrunc (ComplexShape.embeddingUpIntLE a))) ⊗[R]^L (single₀).obj N) ≅
      (H i).obj ((Q.obj P) ⊗[R]^L (single₀).obj N) := by
  let B := P.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  let eOrd :
      (HomologicalComplex.tensorObj B
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i ≅
        (HomologicalComplex.tensorObj P
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i :=
    ShortComplex.homologyMapIso
      (CochainComplex.tensor_single0_shortComplex_iso (R := R) B N i ≪≫
        CochainComplex.tensorRight_upper_stupid_truncation_sc_iso_of_lt
          (R := R) P N a i hi ≪≫
        (CochainComplex.tensor_single0_shortComplex_iso (R := R) P N i).symm)
  have hBminus : CochainComplex.minus (ModuleCat R) B := by
    refine (CochainComplex.minus_iff (ModuleCat R) B).2 ?_
    exact ⟨a, inferInstance⟩
  have hBFlat : B.IsTermwiseFlat := by infer_instance
  -- Proof comment: the left bridge uses bounded-above flatness of the upper window, while the
  -- right bridge uses K-flatness of `P`.
  let _ : CochainComplex.minus (ModuleCat R) B := hBminus
  let _ : B.IsTermwiseFlat := hBFlat
  let _ : P.IsKFlat := hKFlat
  exact
    (CochainComplex.tensorObj_single0_homology_iso_derivedTensor (R := R) B i N).symm ≪≫
      eOrd ≪≫
      CochainComplex.tensorObj_single0_homology_iso_derivedTensor (R := R) P i N

/-- Helper for Lemma 15.67.4: the upper stupid truncation window inherits the same lower
tor-amplitude bound as the ambient K-flat representative. -/
private theorem hasTorAmplitudeGE_of_upper_stupid_truncation_window
    (P : Cpx) (a : ℤ) (hKFlat : P.IsKFlat) (hFlat : P.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE (Q.obj P) a) :
    HasTorAmplitudeGE (Q.obj (P.stupidTrunc (ComplexShape.embeddingUpIntLE a))) a := by
  rw [hasTorAmplitudeGE_iff]
  intro M i hi
  -- Proof comment: transport the vanishing from `P` to the upper window through the comparison
  -- isomorphism proved above.
  exact
    (hTor M i hi).of_iso
      (upper_window_tensor_homology_iso_below_cutoff_of_isKFlat
        (P := P) a hKFlat hFlat M i hi).symm

/-- Helper for Lemma 15.67.4: above the cutoff, the smart lower truncation comparison is an
isomorphism on each retained component. -/
private theorem piTruncGE_component_isIso_of_gt
    (P : Cpx) (a i : ℤ) (hai : a < i) :
    IsIso ((P.πTruncGE a).f i) := by
  let e := ComplexShape.embeddingUpIntGE a
  let j : ℕ := Int.toNat (i - a)
  have hj : e.f j = i := embeddingUpIntGE_toNat_sub_eq a i (le_of_lt hai)
  have hboundary : ¬ e.BoundaryGE j := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hj0
    have : a = i := by
      simpa [e, j, hj0, ComplexShape.embeddingUpIntGE] using hj
    omega
  have hcomp :
      (P.πTruncGE a).f i = (truncGE_term_iso_of_gt (P := P) a i hai).inv := by
    -- Route correction: read the component from the dual `πTruncGE` formula and then unop it.
    apply Quiver.Hom.op_inj
    change ((P.op.πTruncGE e.op).f i) =
      (P.op.truncGEXIso e.op hj (by simpa using hboundary)).inv
    dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
    rw [e.op.liftExtend_f (P.op.restrictionToTruncGE' e.op)
        (P.op.restrictionToTruncGE'_hasLift e.op) hj]
    rw [P.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hj (by simpa using hboundary)]
    simp [truncGE_term_iso_of_gt, HomologicalComplex.truncGEXIso, Category.assoc]
    rfl
  -- Proof comment: once the component is identified with the inverse retained-term isomorphism,
  -- its invertibility is immediate.
  rw [hcomp]
  infer_instance

/-- Helper for Lemma 15.67.4: at the cutoff degree, the smart lower truncation comparison is the
canonical cokernel projection under the standard cutoff-term identification. -/
private theorem piTruncGE_component_comp_cutoff_term_iso
    (P : Cpx) (a : ℤ) :
    (P.πTruncGE a).f a ≫ (truncGE_cutoff_term_iso_cokernel (P := P) a).hom =
      cokernel.π (P.dFrom (a - 1)) := by
  let e := ComplexShape.embeddingUpIntGE a
  let ha' : e.f 0 = a := by
    simpa [e, ComplexShape.embeddingUpIntGE] using
      (embeddingUpIntGE_toNat_sub_eq a a le_rfl)
  have hboundary : e.BoundaryGE 0 := by
    simpa [e] using (ComplexShape.boundaryGE_embeddingUpIntGE_iff a 0).2 rfl
  -- Route correction: read the cutoff component from the dual `πTruncGE` boundary formula, then
  -- transport it through the explicit cutoff-term/cokernel identification.
  apply Quiver.Hom.unop_inj
  change ((truncGE_cutoff_term_iso_cokernel (P := P) a).hom ≫ (P.πTruncGE a).f a).op =
    (cokernel.π (P.dFrom (a - 1))).op
  change
    (truncGE_cutoff_term_iso_cokernel (P := P) a).hom.op ≫ ((P.op.πTruncGE e.op).f a) =
      (cokernel.π (P.dFrom (a - 1))).op
  dsimp [truncGE_cutoff_term_iso_cokernel]
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (P.op.restrictionToTruncGE' e.op)
      (P.op.restrictionToTruncGE'_hasLift e.op) ha']
  rw [P.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e.op ha'
      (by simpa using hboundary)]
  simp [Category.assoc, HomologicalComplex.truncGEXIsoOpcycles, HomologicalComplex.opcyclesOpIso]

/-- Helper for Lemma 15.67.4: the canonical map to the smart lower truncation is epimorphic. -/
private theorem piTruncGE_is_epi
    (P : Cpx) (a : ℤ) :
    Epi (P.πTruncGE a) := by
  refine (cochainComplex_epi_iff_degreewise_epi (P.πTruncGE a)).2 ?_
  intro i
  by_cases hi_lt : i < a
  · let hzero : IsZero ((P.truncGE a).X i) := (P.truncGE a).isZero_of_isStrictlyGE a i hi_lt
    let eZero : (P.truncGE a).X i ≅ 0 := hzero.isoZero
    letI : Epi (0 : P.X i ⟶ (0 : ModuleCat R)) := by infer_instance
    have hcomp : (P.πTruncGE a).f i ≫ eZero.hom = 0 := by
      exact hzero.eq_of_tgt _ _
    rw [hcomp]
    exact CategoryTheory.epi_of_epi ((P.πTruncGE a).f i) eZero.hom
  · by_cases hi_eq : i = a
    · subst hi_eq
      let eCut := truncGE_cutoff_term_iso_cokernel (P := P) a
      have hcomp :
          (P.πTruncGE a).f a ≫ eCut.hom = cokernel.π (P.dFrom (a - 1)) :=
        piTruncGE_component_comp_cutoff_term_iso (P := P) a
      rw [hcomp]
      exact CategoryTheory.epi_of_epi ((P.πTruncGE a).f a) eCut.hom
    · have hgt : a < i := by omega
      letI : IsIso ((P.πTruncGE a).f i) :=
        piTruncGE_component_isIso_of_gt (P := P) a i hgt
      infer_instance

/-- Helper for Lemma 15.67.4: the kernel row of the smart lower truncation map is short exact. -/
private theorem piTruncGE_kernel_shortExact
    (P : Cpx) (a : ℤ) :
    (ShortComplex.mk (kernel.ι (P.πTruncGE a)) (P.πTruncGE a)
      (kernel.condition (P.πTruncGE a))).ShortExact := by
  letI : Epi (P.πTruncGE a) := piTruncGE_is_epi (P := P) a
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  -- Proof comment: the standard kernel row is exact once the truncation map is known to be epi.
  exact ShortComplex.exact_kernel (P.πTruncGE a)

/-- Helper for Lemma 15.67.4: the kernel of the smart lower truncation map is termwise flat once
the cutoff cokernel is flat. -/
private theorem piTruncGE_kernel_isTermwiseFlat
    (P : Cpx) (a : ℤ) (hFlat : P.IsTermwiseFlat)
    (hCutFlat : Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R))) :
    (kernel (P.πTruncGE a)).IsTermwiseFlat := by
  let E := P.truncGE a
  let S : ShortComplex Cpx :=
    ShortComplex.mk (kernel.ι (P.πTruncGE a)) (P.πTruncGE a) (kernel.condition (P.πTruncGE a))
  have hS : S.ShortExact := piTruncGE_kernel_shortExact (P := P) a
  have hEFlat : E.IsTermwiseFlat :=
    truncGE_isTermwiseFlat_of_flat_cokernel (P := P) a hFlat hCutFlat
  intro i
  let Si : ShortComplex (ModuleCat R) :=
    S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i)
  have hSi : Si.ShortExact := by
    -- Proof comment: evaluation preserves the short exact kernel row degreewise.
    simpa [S, Si] using hS.map_of_exact
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i)
  letI : Module.Flat R Si.X₂ := by
    simpa [S, Si] using hFlat i
  letI : Module.Flat R Si.X₃ := by
    simpa [E, S, Si] using hEFlat i
  -- Proof comment: degreewise flatness of the left term is exactly the module-level short exact
  -- flatness lemma applied to the evaluated row.
  simpa [S, Si] using CategoryTheory.ShortComplex.ShortExact.flat_X₁ (R := R) hSi

/-- Helper for Lemma 15.67.4: the kernel of the smart lower truncation map is supported in
degrees `≤ a`. -/
private theorem piTruncGE_kernel_isStrictlyLE
    (P : Cpx) (a : ℤ) :
    (kernel (P.πTruncGE a)).IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have hmono : Mono ((P.πTruncGE a).f i) := by
    letI : IsIso ((P.πTruncGE a).f i) :=
      piTruncGE_component_isIso_of_gt (P := P) a i hi
    infer_instance
  have hzeroKernel : IsZero (kernel ((P.πTruncGE a).f i)) := by
    exact IsZero.of_iso (isZero_zero _) (kernel.ofMono ((P.πTruncGE a).f i))
  let eKernel :=
    PreservesKernel.iso (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i)
      (P.πTruncGE a)
  -- Proof comment: evaluation preserves kernels, so the stagewise kernel vanishes above the
  -- cutoff as soon as the component map is an isomorphism.
  exact hzeroKernel.of_iso eKernel.symm

/-- Helper for Lemma 15.67.4: once the cutoff cokernel is flat, the smart lower truncation is
K-flat. -/
private theorem truncGE_isKFlat_of_flat_cokernel
    (P : Cpx) (a : ℤ) (hKFlat : P.IsKFlat) (hFlat : P.IsTermwiseFlat)
    (hCutFlat : Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R))) :
    (P.truncGE a).IsKFlat := by
  let E : Cpx := P.truncGE a
  let L : Cpx := kernel (P.πTruncGE a)
  let S : ShortComplex Cpx :=
    ShortComplex.mk (kernel.ι (P.πTruncGE a)) (P.πTruncGE a) (kernel.condition (P.πTruncGE a))
  have hS : S.ShortExact := piTruncGE_kernel_shortExact (P := P) a
  have hLFlat : L.IsTermwiseFlat :=
    piTruncGE_kernel_isTermwiseFlat (P := P) a hFlat hCutFlat
  have hLLE : L.IsStrictlyLE a := piTruncGE_kernel_isStrictlyLE (P := P) a
  have hLminus : CochainComplex.minus (ModuleCat R) L := by
    -- Proof comment: strict support in degrees `≤ a` is exactly the bounded-above hypothesis.
    exact (CochainComplex.minus_iff (ModuleCat R) L).2 ⟨a, hLLE⟩
  have hLKFlat : L.IsKFlat :=
    CochainComplex.isKFlat_of_boundedAbove_of_flat (R := R) L hLminus hLFlat
  have hEFlat : E.IsTermwiseFlat :=
    truncGE_isTermwiseFlat_of_flat_cokernel (P := P) a hFlat hCutFlat
  -- Proof comment: the source proof now closes by applying the kernel-row short exact sequence to
  -- Lemma `15.59.6`.
  simpa [E, L, S] using
    CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃ (R := R) (S := S) hS hEFlat hLKFlat hKFlat

-- Proof sketch: for `(→)`, choose a termwise-flat K-flat resolution of a representative of `K`,
-- use the tor-amplitude hypothesis to show the cokernel in degree `a` is flat, truncate below `a`,
-- and apply the K-flat closure lemmas to the resulting short exact sequence. For `(←)`, tensor the
-- chosen K-flat representative with any degree-zero module and compute the derived tensor product
-- on the nose; since the tensor complex is strictly supported in degrees `≥ a`, its homology
-- vanishes below `a`.
/-- Lemma 15.67.4: an object `K` of `D(R)` has tor-amplitude in `[a, ∞]` if and only if it is
quasi-isomorphic to a K-flat cochain complex of flat `R`-modules that vanishes in every degree
`< a`. -/
@[stacks 0BYL]
theorem hasTorAmplitudeGE_iff_exists_representative
    (K : DMod) (a : ℤ) :
    HasTorAmplitudeGE K a ↔
      ∃ (E : Cpx) (_ : K ≅ Q.obj E),
        E.IsStrictlyGE a ∧ E.IsKFlat ∧ E.IsTermwiseFlat := by
  constructor
  · intro hK
    obtain ⟨P, π, hPKFlat, hPFlat, hπ, _hπepi⟩ :=
      CochainComplex.exists_epi_kFlatResolution (Q.objPreimage K)
    have hQπ : IsIso (Q.map π) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact hπ
    let eP : K ≅ Q.obj P :=
      (Q.objObjPreimageIso K).symm ≪≫ (asIso (Q.map π)).symm
    have hTorP : HasTorAmplitudeGE (Q.obj P) a :=
      (hasTorAmplitudeGE_iff_of_iso (a := a) eP).1 hK
    let B : Cpx := P.stupidTrunc (ComplexShape.embeddingUpIntLE a)
    have hTorB : HasTorAmplitudeGE (Q.obj B) a :=
      hasTorAmplitudeGE_of_upper_stupid_truncation_window (P := P) a hPKFlat hPFlat hTorP
    have hBminus : CochainComplex.minus (ModuleCat R) B := by
      refine (CochainComplex.minus_iff (ModuleCat R) B).2 ?_
      exact ⟨a, inferInstance⟩
    have hBFlat : B.IsTermwiseFlat := by infer_instance
    have hCutFlatB :
        Module.Flat R ↑((cokernel (B.dFrom (a - 1)) : ModuleCat R)) :=
      CochainComplex.flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
        (R := R) B a hBminus hBFlat hTorB
    let eCut :
        cokernel (B.dFrom (a - 1)) ≅ cokernel (P.dFrom (a - 1)) :=
      (differentialCokernel_iso_cokernel_dFrom_local (R := R) B a).symm ≪≫
        CochainComplex.upper_stupid_truncation_differential_cokernel_iso (R := R) P a
    have hCutFlat :
        Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R)) := by
      letI : Module.Flat R ↑((cokernel (B.dFrom (a - 1)) : ModuleCat R)) := hCutFlatB
      exact Module.Flat.of_linearEquiv eCut.toLinearEquiv
    let E : Cpx := P.truncGE a
    have hEGE : E.IsStrictlyGE a := by infer_instance
    have hEFlat : E.IsTermwiseFlat :=
      truncGE_isTermwiseFlat_of_flat_cokernel (P := P) a hPFlat hCutFlat
    have hEKFlat : E.IsKFlat :=
      truncGE_isKFlat_of_flat_cokernel (P := P) a hPKFlat hPFlat hCutFlat
    have hPbelow : ∀ i : ℤ, i < a → IsZero (P.homology i) := by
      intro i hi
      -- Proof comment: evaluate lower tor-amplitude on the K-flat resolution itself.
      exact isZero_homology_of_hasTorAmplitudeGE_below P a i hTorP hi
    have hπTrunc : QuasiIso (P.πTruncGE a) :=
      quasiIso_piTruncGE_of_isZero_homology_below a P hPbelow
    have hQπTrunc : IsIso (Q.map (P.πTruncGE a)) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact hπTrunc
    let eE : K ≅ Q.obj E :=
      eP ≪≫ asIso (Q.map (P.πTruncGE a))
    -- Proof comment: the smart lower truncation now gives the desired representative.
    exact ⟨E, eE, hEGE, hEKFlat, hEFlat⟩
  · rintro ⟨E, e, hGE, hKFlat, _hFlat⟩
    -- Route correction: the reverse implication only needs the public homology-level bridge from
    -- Lemma `15.67.2`, not a new chain-level tensor comparison.
    exact hasTorAmplitudeGE_of_representative E e a hGE hKFlat

end

end CategoryTheory
