import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_16_4
import stacks_proof.stacks_project.Chap13.Definition_13_27_1
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.«15_74_0_2»
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.Lemma_15_73_2
import stacks_proof.stacks_project.Chap15.Lemma_15_74_1
import stacks_proof.stacks_project.Chap15.Lemma_15_74_2
import stacks_proof.stacks_project.Chap15.Lemma_15_74_4

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "𝓗" => DerivedCategory.homologyFunctor (ModuleCat A)

open scoped DerivedInternalHom
open scoped DerivedExt
open scoped DerivedTensorProduct

/- Domain-style sampling for Lemma 15.75.15:
- primary domain: rigid duality for perfect objects of `D(A)`, expressed through the canonical
  tensor owner `derivedTensorProduct`, the monoidal-closed owner `MonoidalClosed DMod`, and the
  monoidal duality owner `ExactPairing`;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  the source-facing notation `RHom[H](K, L)`,
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.derivedInternalHom_comp`,
  `CategoryTheory.derivedHom_cohomology_iso_shiftedHom`,
  `CategoryTheory.ExactPairing`;
- best owner abstraction:
  `source-facing`: the derived dual `K^∨ = RHom_A(K, A[0])` and the canonical comparison maps
  appearing in parts `(2)` to `(4)`;
  `core/canonical`: `derivedTensorProduct`, `RHom[H](K, L)`, `ExactPairing`, and the chapter owner
  `derivedHom_cohomology_iso_shiftedHom` for `H^n(RHom)` versus `ShiftedHom`;
  `bridge/view`: the right-unit identifications for `A[0]`, the bidual comparison morphism, the
  tensor-to-Hom comparison natural transformation below, and the degree-zero passage from
  `ShiftedHom K L 0` to `K ⟶ L`.

Primitive data are only the chosen monoidal-closed owner `H` and the canonical tensor unit
`A[0]`. The bidual map, tensor/Hom comparison, degree-zero comparison, and exact-pairing package
are derived API and should therefore be exposed as actual morphisms and natural transformations,
not hidden behind `Nonempty` wrappers.
-/

/-- The derived dual `K^\vee = R\mathrm{Hom}_A(K, A[0])` attached to a chosen derived
internal-Hom package on `D(A)`. -/
abbrev derivedDual (H : RHomPkg) (K : DMod) : DMod :=
  RHom[H](K, ringSingle)

notation:max K:max "ᵛ⟮" H:max "⟯" => derivedDual H K

/-- The contravariant map on derived duals induced by a morphism in `D(A)`. -/
abbrev derivedDualMap
    (H : RHomPkg) {K L : DMod} (f : K ⟶ L) :
    Lᵛ⟮H⟯ ⟶ Kᵛ⟮H⟯ :=
  derivedInternalHomMap H f (𝟙 ringSingle)

/-- The canonical evaluation morphism
`K^\vee \otimes_A^{\mathbf L} K \to A[0]`. -/
private noncomputable def derivedDualEvaluationDerivedTensor
    (H : RHomPkg) (K : DMod) :
    Kᵛ⟮H⟯ ⊗[A]^L K ⟶ ringSingle :=
  (H.derivedTensorAdj K).counit.app ringSingle

private noncomputable def derivedDualTensorEvaluation
    (H : RHomPkg) (K : DMod) :
    K ⊗[A]^L Kᵛ⟮H⟯ ⟶ ringSingle :=
  (derivedTensorProduct_comm K Kᵛ⟮H⟯).hom ≫
    derivedDualEvaluationDerivedTensor H K

private noncomputable def derivedInternalHomIdUnit
    (H : RHomPkg) (K : DMod) :
    ringSingle ⟶ RHom[H](K, K) :=
  letI : MonoidalClosed DMod := H
  (H.derivedTensorAdj K).homEquiv ringSingle K (singleZeroDerivedTensorIso K).hom

private noncomputable def derivedInternalHomUnitComparison
    (H : RHomPkg) (L : DMod) :
    L ⟶ RHom[H](ringSingle, L) :=
  letI : MonoidalClosed DMod := H
  (H.derivedTensorAdj ringSingle).homEquiv L L
    ((derivedTensorProduct_comm L ringSingle ≪≫ singleZeroDerivedTensorIso L).hom)

/-- Helper for Lemma 15.75.15: the unit comparison `L ⟶ RHom_A(A[0], L)` is natural in `L`. -/
private theorem derivedInternalHomUnitComparison_natural
    (H : RHomPkg) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    f ≫ derivedInternalHomUnitComparison H L₂ =
      derivedInternalHomUnitComparison H L₁ ≫
        derivedInternalHomMap H (𝟙 ringSingle) f := by
  letI : MonoidalClosed DMod := H
  let adj := H.derivedTensorAdj ringSingle
  have hTensor :
      (derivedTensorProduct ringSingle).map f ≫
          ((derivedTensorProduct_comm L₂ ringSingle ≪≫ singleZeroDerivedTensorIso L₂).hom) =
        ((derivedTensorProduct_comm L₁ ringSingle ≪≫ singleZeroDerivedTensorIso L₁).hom) ≫ f := by
    -- Proof comment: expand the right-unit identification once and use the fixed-right-factor
    -- naturality of the ambient/derived tensor comparison.
    simp only [singleZeroDerivedTensorIso, derivedTensorProduct_comm,
      derivedCategory_tensorObj_iso_derivedTensorProduct,
      tensoringRightIsoDerivedTensorProduct_hom_app,
      tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit, Category.assoc]
  have hMate :
      (adj.homEquiv L₁ L₂).symm (f ≫ derivedInternalHomUnitComparison H L₂) =
        (adj.homEquiv L₁ L₂).symm
          (derivedInternalHomUnitComparison H L₁ ≫
            derivedInternalHomMap H (𝟙 ringSingle) f) := by
    -- Proof comment: move both morphisms back across the adjunction and compare the resulting
    -- maps `L₁ ⊗^L A[0] ⟶ L₂`.
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
    simpa [adj, derivedInternalHomUnitComparison, derivedInternalHomMap, Category.assoc] using
      hTensor
  exact (adj.homEquiv L₁ L₂).symm.injective hMate

-- Proof sketch: this is the evaluation morphism
-- `K \otimes_A^{\mathbf L} K^\vee \to A[0]` transposed across the adjunction
-- `- \otimes_A^{\mathbf L} K^\vee ⊣ R\mathrm{Hom}_A(K^\vee, -)`.
/-- The canonical bidual comparison morphism
`K \to (K^\vee)^\vee`. -/
noncomputable def derivedDualBidualComparison
    (H : RHomPkg) (K : DMod) :
    K ⟶ (Kᵛ⟮H⟯)ᵛ⟮H⟯ :=
  (H.derivedTensorAdj Kᵛ⟮H⟯).homEquiv K ringSingle
    (derivedDualTensorEvaluation H K)

/-- Helper for Lemma 15.75.15: the termwise dual of a bounded finite-projective cochain complex is
again bounded finite projective. This is the complex-level source step before transporting the
dual model across the derived-category identification `Q.obj P^∨ ≅ RHom_A(P, A[0])`. -/
private theorem projective_model_dual_isBoundedFiniteProjective
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P] :
    CochainComplex.IsBoundedFiniteProjective P^∨ := by
  -- Proof comment: package the representative bounds as `CochainComplex.bounded`, build the exact
  -- pairing `P^∨ ⊣ P`, then read boundedness and degreewise finite projectivity back off the dual.
  have hPbounded : CochainComplex.bounded (ModuleCat A) P := by
    rcases hP.bounded with ⟨a, b, ha, hb⟩
    refine (CochainComplex.bounded_iff (C := ModuleCat A) P).2 ?_
    exact ⟨(CochainComplex.plus_iff (C := ModuleCat A) P).2 ⟨a, ha⟩,
      (CochainComplex.minus_iff (C := ModuleCat A) P).2 ⟨b, hb⟩⟩
  have hPtermwise :
      ∀ n : ℤ, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n) := fun n ↦
        ⟨inferInstance, inferInstance⟩
  letI : ExactPairing P^∨ P :=
    moduleComplexDualExactPairing (R := A) (M := P) hPbounded hPtermwise
  have hPdualBounded : CochainComplex.bounded (ModuleCat A) P^∨ :=
    exactPairing_left_complex_isBounded (R := A) (M := P^∨) (N := P)
  have hPdualFiniteProjective :
      ∀ n : ℤ, Module.Finite A ((P^∨).X n) ∧ Module.Projective A ((P^∨).X n) := fun n ↦
        exactPairing_left_term_finite_projective (R := A) (M := P^∨) (N := P) n
  rcases (CochainComplex.bounded_iff (C := ModuleCat A) P^∨).1 hPdualBounded with
    ⟨hPdualPlus, hPdualMinus⟩
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff (C := ModuleCat A) P^∨).1 hPdualPlus
  obtain ⟨b, hb⟩ := (CochainComplex.minus_iff (C := ModuleCat A) P^∨).1 hPdualMinus
  refine (CochainComplex.isBoundedFiniteProjective_iff (R := A) P^∨).2 ?_
  refine ⟨⟨a, b, ha, hb⟩, ?_, ?_⟩
  · intro n
    exact (hPdualFiniteProjective n).1
  · intro n
    exact (hPdualFiniteProjective n).2

/-- Helper for Lemma 15.75.15: a bounded finite-projective complex is bounded above, so it
packages canonically as a `ProjectiveMinus` complex. This is the owner needed for the Chapter 13
and 15 comparison theorems on derived Hom out of projective models. -/
private theorem bounded_finite_projective_minus
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P] :
    CochainComplex.minus (ModuleCat A) P := by
  -- Proof comment: only the upper support bound matters for the `ProjectiveMinus` owner.
  rcases hP.bounded with ⟨_, b, _, hb⟩
  exact (CochainComplex.minus_iff (C := ModuleCat A) P).2 ⟨b, hb⟩

/-- Helper for Lemma 15.75.15: package a bounded finite-projective model as a
`ProjectiveMinus` complex so the source-side derived-Hom comparison theorems apply directly. -/
private noncomputable abbrev projective_model_as_projective_minus
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P] :
    CochainComplex.ProjectiveMinus (ModuleCat A) :=
  ⟨⟨P, bounded_finite_projective_minus (A := A) P⟩, fun n ↦ inferInstance⟩

/-- Helper for Lemma 15.75.15: on a bounded finite-projective model `P`, the cohomology of the
termwise dual complex agrees additively with the cohomology of the derived dual
`R\mathrm{Hom}_A(Q(P), A[0])`. This is the source-level `Hom^\bullet(P^\bullet, A)` computation
from Lemma `15.74.2`, followed by the standard cohomology/shifted-Hom bridge for derived Hom. -/
private noncomputable def projective_model_dual_homology_add_equiv_derivedDual
    (H : RHomPkg)
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P]
    (n : ℤ) :
    (P^∨).homology n ≃+
      ((𝓗 n).obj ((DerivedCategory.Q.obj P)ᵛ⟮H⟯)) := by
  -- Proof comment: first compute the dual complex cohomology as shifted morphisms out of the
  -- projective model by Lemma `15.74.2`.
  refine
    (by
      simpa [derivedDual, ringSingle, CochainComplex.moduleComplexDual] using
        (CochainComplex.ProjectiveMinus.homologyAddEquivShiftedHom
          (projective_model_as_projective_minus (A := A) P)
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj (ModuleCat.of A A))
          n)).trans ?_
  -- Proof comment: then identify those shifted morphisms with the cohomology of the chosen
  -- derived internal-Hom object by the Chapter `15.74.0.2` bridge.
  exact
    (derivedHom_cohomology_iso_shiftedHom H (DerivedCategory.Q.obj P) ringSingle n).symm.toAddEquiv

/-- Helper for Lemma 15.75.15: derived duality carries source isomorphisms to isomorphisms of
derived duals by applying the opposite-category internal-Hom functor at `A[0]`. -/
private noncomputable abbrev derivedDual_iso_of_iso
    (H : RHomPkg) {K L : DMod} (e : K ≅ L) :
    Kᵛ⟮H⟯ ≅ Lᵛ⟮H⟯ :=
  letI : RHomPkg := H
  ((MonoidalClosed.internalHom).flip.obj ringSingle).mapIso e.op

/-- Helper for Lemma 15.75.15: the public complex-level evaluation map for the dual complex
`P^\vee = \operatorname{Hom}^\bullet_A(P^\bullet, A[0])`. This is the exact source morphism
whose mate yields the derived comparison `Q.obj P^\vee ⟶ RHom_A(Q.obj P, A[0])`. -/
private noncomputable abbrev projective_model_dual_evaluation_complex
    (P : CochainComplex (ModuleCat A) ℤ) :
    P^∨ ⊗ P ⟶ 𝟙_ (CochainComplex (ModuleCat A) ℤ) :=
  (β_ P^∨ P).hom ≫ (ihom.ev P).app (𝟙 _)

/-- Helper for Lemma 15.75.15: after passing to the derived category and translating both tensor
and unit through the canonical `Q`-monoidal identifications, the public complex evaluation map on
`P^\vee ⊗ P` becomes a morphism
`Q.obj P^\vee \otimes_A^{\mathbf L} Q.obj P ⟶ A[0]`. -/
private noncomputable def projective_model_dual_evaluation_derived
    (P : CochainComplex (ModuleCat A) ℤ) :
    DerivedCategory.Q.obj P^∨ ⊗[A]^L DerivedCategory.Q.obj P ⟶ ringSingle :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      (DerivedCategory.Q.obj P^∨) (DerivedCategory.Q.obj P)).inv ≫
    (Functor.Monoidal.μIso
      (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod) P^∨ P).hom ≫
        DerivedCategory.Q.map (projective_model_dual_evaluation_complex (A := A) P) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (ModuleCat.of A A)).inv

/-- Helper for Lemma 15.75.15: the model-level comparison
`Q.obj P^\vee ⟶ RHom_A(Q.obj P, A[0])` obtained by transposing the public derived evaluation map
under the chosen adjunction `- \otimes_A^{\mathbf L} Q.obj P ⊣ RHom_A(Q.obj P, -)`. -/
private noncomputable def projective_model_derivedDual_comparison
    (H : RHomPkg)
    (P : CochainComplex (ModuleCat A) ℤ) :
    DerivedCategory.Q.obj P^∨ ⟶ (DerivedCategory.Q.obj P)ᵛ⟮H⟯ :=
  (H.derivedTensorAdj (DerivedCategory.Q.obj P)).homEquiv _ _
    (projective_model_dual_evaluation_derived (A := A) P)

/-- Helper for Lemma 15.75.15: by construction, the mate of
`projective_model_derivedDual_comparison` is exactly the derived evaluation map built from the
public complex evaluation formula. -/
private theorem projective_model_derivedDual_comparison_def
    (H : RHomPkg)
    (P : CochainComplex (ModuleCat A) ℤ) :
    ((H.derivedTensorAdj (DerivedCategory.Q.obj P)).homEquiv _ _).symm
        (projective_model_derivedDual_comparison (A := A) H P) =
      projective_model_dual_evaluation_derived (A := A) P := by
  -- Proof comment: this is the defining `homEquiv`/`symm` cancellation for the chosen mate.
  simp [projective_model_derivedDual_comparison]

/-- Helper for Lemma 15.75.15: the source-textbook tensor/Hom comparison on a bounded
finite-projective model, written using only the public complex-level tensor/internal-Hom API. -/
private noncomputable abbrev projective_model_tensor_dual_complex_comparison
    (P L : CochainComplex (ModuleCat A) ℤ) :
    HomologicalComplex.tensorObj L P^∨ ⟶ (ihom P).obj L :=
  module_complex_tensor_internal_hom_comparison L (𝟙 _) P ≫
    (ihom P).map ((ρ_ L).hom)

/-- Helper for Lemma 15.75.15: the named complex-side tensor/Hom comparison is definitionally the
public tensor/internal-Hom comparison followed by the right-unitor transport
`L \otimes A[0] \cong L`. -/
private theorem projective_model_tensor_dual_complex_comparison_def
    (P L : CochainComplex (ModuleCat A) ℤ) :
    projective_model_tensor_dual_complex_comparison (A := A) P L =
      module_complex_tensor_internal_hom_comparison L (𝟙 _) P ≫
        (ihom P).map ((ρ_ L).hom) := by
  -- Proof comment: this is the defining expansion of the named source-side comparison.
  rfl

/-- Helper for Lemma 15.75.15: every cohomology map induced by the model comparison
`Q.obj P^\vee ⟶ RHom_A(Q.obj P, A[0])` is bijective, because the projective-model computation of
`H^n(P^\vee)` already identifies it with the target cohomology of the derived dual. -/
private theorem projective_model_derivedDual_comparison_homology_bijective
    (H : RHomPkg)
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P]
    (n : ℤ) :
    Function.Bijective
      ((𝓗 n).map (projective_model_derivedDual_comparison (A := A) H P)) := by
  -- Proof comment: this packages the source-faithful cohomology calculation into the exact
  -- shape needed by homology detection in the derived category.
  simpa [projective_model_dual_homology_add_equiv_derivedDual, derivedDual, ringSingle,
    projective_model_derivedDual_comparison, projective_model_dual_evaluation_derived,
    projective_model_dual_evaluation_complex] using
    (projective_model_dual_homology_add_equiv_derivedDual (A := A) H P n).bijective

/-- Helper for Lemma 15.75.15: a bounded finite-projective model computes the derived dual after
passing to the derived category. This is the source-faithful bridge from the dual complex `P^∨`
to `R\mathrm{Hom}_A(P, A[0])`. -/
private theorem projective_model_derivedDual_iso
    (H : RHomPkg)
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P] :
    DerivedCategory.Q.obj P^∨ ≅ (DerivedCategory.Q.obj P)ᵛ⟮H⟯ := by
  -- Route correction: the source-faithful cohomology computation is now isolated in
  -- `projective_model_dual_homology_add_equiv_derivedDual`, while
  -- `projective_model_derivedDual_comparison` now names the concrete comparison morphism
  -- `Q.obj P^∨ ⟶ RHom_A(Q.obj P, A[0])` built from the public evaluation formula.
  -- TODO: identify the homology maps of
  -- `projective_model_derivedDual_comparison (A := A) H P` with
  -- identify each induced homology map with
  -- `projective_model_dual_homology_add_equiv_derivedDual`, and conclude by
  -- `derivedCategory_isIso_iff_homology_map_isIso`.
  have hcomparison : IsIso (projective_model_derivedDual_comparison (A := A) H P) := by
    -- Proof comment: detect the comparison in `D(A)` on all cohomology groups and rewrite the
    -- induced map to the explicit projective-model computation already packaged above.
    refine
      (derivedCategory_isIso_iff_homology_map_isIso
        (ℬ := ModuleCat A)
        (projective_model_derivedDual_comparison (A := A) H P)).2 ?_
    intro n
    refine (CategoryTheory.isIso_iff_bijective _).2 ?_
    exact projective_model_derivedDual_comparison_homology_bijective (A := A) H P n
  exact asIso (projective_model_derivedDual_comparison (A := A) H P)

/-- Helper for Lemma 15.75.15: a bounded finite-projective complex is canonically isomorphic to
the double dual of its termwise dual complex, because both objects are left duals of `P^\vee` in
the monoidal category of cochain complexes. -/
private noncomputable def projective_model_bidual_iso
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P] :
    P ≅ (P^∨)^∨ := by
  let hPbounded : CochainComplex.bounded (ModuleCat A) P := by
    -- Proof comment: convert the finite-projective support bounds into the boundedness owner used
    -- by `moduleComplexDualExactPairing`.
    rcases hP.bounded with ⟨a, b, ha, hb⟩
    refine (CochainComplex.bounded_iff (C := ModuleCat A) P).2 ?_
    exact ⟨(CochainComplex.plus_iff (C := ModuleCat A) P).2 ⟨a, ha⟩,
      (CochainComplex.minus_iff (C := ModuleCat A) P).2 ⟨b, hb⟩⟩
  let hPtermwise :
      ∀ n : ℤ, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n) := fun n ↦
        ⟨inferInstance, inferInstance⟩
  let pBase : ExactPairing P^∨ P :=
    CochainComplex.moduleComplexDualExactPairing (R := A) (M := P) hPbounded hPtermwise
  letI : ExactPairing P^∨ P := pBase
  let pLeft : ExactPairing P P^∨ :=
    BraidedCategory.exactPairing_swap P^∨ P
  have hPdual : CochainComplex.IsBoundedFiniteProjective P^∨ :=
    projective_model_dual_isBoundedFiniteProjective (A := A) P
  let hPdualBounded : CochainComplex.bounded (ModuleCat A) P^∨ := by
    -- Proof comment: the dual complex inherits bounded support from the same finite-projective
    -- source data.
    rcases hPdual.bounded with ⟨a, b, ha, hb⟩
    refine (CochainComplex.bounded_iff (C := ModuleCat A) P^∨).2 ?_
    exact ⟨(CochainComplex.plus_iff (C := ModuleCat A) P^∨).2 ⟨a, ha⟩,
      (CochainComplex.minus_iff (C := ModuleCat A) P^∨).2 ⟨b, hb⟩⟩
  let hPdualTermwise :
      ∀ n : ℤ, Module.Finite A ((P^∨).X n) ∧ Module.Projective A ((P^∨).X n) := fun n ↦
        ⟨inferInstance, inferInstance⟩
  let pBidual : ExactPairing (P^∨)^∨ P^∨ :=
    CochainComplex.moduleComplexDualExactPairing (R := A) (M := P^∨) hPdualBounded hPdualTermwise
  -- Proof comment: `P` and `(P^\vee)^\vee` are both left duals of `P^\vee`, so the generic
  -- uniqueness isomorphism for left duals gives the desired source-model identification.
  exact leftDualIso pLeft pBidual

/-- Helper for Lemma 15.75.15: the internal-Hom functor on cochain complexes is the canonical
right adjoint to tensoring on the right by a fixed complex. -/
private noncomputable abbrev projective_model_tensor_dual_rightTensorAdj
    (P : CochainComplex (ModuleCat A) ℤ) :
    MonoidalCategory.tensorRight P ⊣ CategoryTheory.ihom P :=
  (CategoryTheory.ihom.adjunction P).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight P)

/-- Helper for Lemma 15.75.15: for a bounded finite-projective model `P`, the source complex dual
`P^\vee` is the canonical right adjoint to tensoring on the right by `P`. -/
private noncomputable def projective_model_tensor_dual_complex_iso
    (P : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P] :
    MonoidalCategory.tensorRight P^∨ ≅ CategoryTheory.ihom P := by
  let hPbounded : CochainComplex.bounded (ModuleCat A) P := by
    -- Proof comment: the exact-pairing package for `P^\vee ⊣ P` uses the bounded-support owner.
    rcases hP.bounded with ⟨a, b, ha, hb⟩
    refine (CochainComplex.bounded_iff (C := ModuleCat A) P).2 ?_
    exact ⟨(CochainComplex.plus_iff (C := ModuleCat A) P).2 ⟨a, ha⟩,
      (CochainComplex.minus_iff (C := ModuleCat A) P).2 ⟨b, hb⟩⟩
  let hPtermwise :
      ∀ n : ℤ, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n) := fun n ↦
        ⟨inferInstance, inferInstance⟩
  let pBase : ExactPairing P^∨ P :=
    CochainComplex.moduleComplexDualExactPairing (R := A) (M := P) hPbounded hPtermwise
  letI : ExactPairing P^∨ P := pBase
  let pRight : ExactPairing P P^∨ :=
    BraidedCategory.exactPairing_swap P^∨ P
  letI : ExactPairing P P^∨ := pRight
  -- Proof comment: both `- ⊗ P^\vee` and `ihom P` are right adjoints to `- ⊗ P`, so uniqueness
  -- of right adjoints packages the canonical source-side tensor/Hom identification.
  exact (tensorRightAdjunction P P^∨).rightAdjointUniq
    (projective_model_tensor_dual_rightTensorAdj (A := A) P)

/-- Helper for Lemma 15.75.15: each component of the source-side right-adjoint-uniqueness
comparison `- ⊗ P^\vee ≅ ihom(P,-)` is an isomorphism. -/
private theorem projective_model_tensor_dual_complex_iso_app_isIso
    (P L : CochainComplex (ModuleCat A) ℤ)
    [hP : CochainComplex.IsBoundedFiniteProjective P] :
    IsIso ((projective_model_tensor_dual_complex_iso (A := A) P).app L).hom := by
  let e := (projective_model_tensor_dual_complex_iso (A := A) P).app L
  -- Proof comment: the displayed morphism is the `hom` component of a natural isomorphism.
  simpa [e] using (inferInstance : IsIso e.hom)

-- Proof sketch: choose a bounded finite-projective representative of `K`. Lemma `15.74.2`
-- identifies `RHom_A(K, A)` with the termwise dual complex, whose terms remain finite projective,
-- so the resulting object is again represented by a bounded finite-projective complex.
/-- Lemma 15.75.15 (1): if `K` is a perfect object of `D(A)`, then its derived dual
`K^\vee = R\mathrm{Hom}_A(K, A[0])` is again perfect. -/
@[stacks 07VI]
theorem derivedDual_isPerfect
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect Kᵛ⟮H⟯ := by
  -- Route correction: the complex-level source step is now isolated in
  -- `projective_model_dual_isBoundedFiniteProjective`; the remaining blocker is only the bridge
  -- from the dual complex model `Q.obj P^∨` to the derived dual object `RHom_A(K, A[0])`.
  rcases hK with ⟨P, eP, hP⟩
  letI : CochainComplex.IsBoundedFiniteProjective P := hP
  have hPdual : CochainComplex.IsBoundedFiniteProjective P^∨ :=
    projective_model_dual_isBoundedFiniteProjective (A := A) P
  have hDualModelPerfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj P^∨) := by
    exact ⟨P^∨, Iso.refl _, hPdual⟩
  have hRepresentedDualPerfect :
      DerivedCategory.IsPerfect ((DerivedCategory.Q.obj P)ᵛ⟮H⟯) := by
    -- Proof comment: once the projective model is bridged to the derived dual, perfectness
    -- transports directly from the dual complex representative.
    exact DerivedCategory.IsPerfect.prop_of_iso
      (projective_model_derivedDual_iso (A := A) H P)
      hDualModelPerfect
  -- Proof comment: the original object `K` is only represented up to isomorphism by `P`, so the
  -- final step is to transport the derived dual along that source isomorphism.
  exact DerivedCategory.IsPerfect.prop_of_iso
    (derivedDual_iso_of_iso (A := A) H eP).symm
    hRepresentedDualPerfect

-- Proof sketch: represent `K` by a bounded finite-projective complex. Degreewise evaluation on
-- finite projective modules identifies that complex with its double dual, and the induced map in
-- the derived category is the canonical bidual comparison defined above.
/-- Lemma 15.75.15 (2): for a perfect object `K`, the canonical bidual comparison
`K \to (K^\vee)^\vee` is an isomorphism. -/
@[stacks 07VI]
theorem perfect_iso_derivedDual_derivedDual
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualBidualComparison H K) := by
  rcases hK with ⟨P, eP, hP⟩
  letI : CochainComplex.IsBoundedFiniteProjective P := hP
  have hModelBidualIso :
      IsIso (DerivedCategory.Q.map (projective_model_bidual_iso (A := A) P).hom) := by
    infer_instance
  have hModelDualIso :
      DerivedCategory.Q.obj P^∨ ≅ (DerivedCategory.Q.obj P)ᵛ⟮H⟯ :=
    projective_model_derivedDual_iso (A := A) H P
  have hModelBidualTargetIso :
      DerivedCategory.Q.obj (P^∨)^∨ ≅ ((DerivedCategory.Q.obj P)ᵛ⟮H⟯)ᵛ⟮H⟯ :=
    (projective_model_derivedDual_iso (A := A) H P^∨) ≪≫
      derivedDual_iso_of_iso (A := A) H hModelDualIso
  -- Proof comment: the source model is now explicit on both the object and bidual sides; only the
  -- final identification of `derivedDualBidualComparison H (DerivedCategory.Q.obj P)` with the
  -- transported complex double-dual isomorphism remains.
  -- TODO: compare `derivedDualBidualComparison H (DerivedCategory.Q.obj P)` with
  -- `DerivedCategory.Q.map (projective_model_bidual_iso (A := A) P).hom`, after rewriting the
  -- target by `hModelBidualTargetIso`, and then transport the resulting isomorphism across `eP`.
  sorry

/-- The canonical natural transformation
`- \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, -)`. -/
noncomputable def derivedDualTensorComparison
    (H : RHomPkg) (K : DMod) :
    letI := H
    derivedTensorProduct Kᵛ⟮H⟯ ⟶ ihom K where
  app L :=
    (derivedTensorProduct Kᵛ⟮H⟯).map
        (derivedInternalHomUnitComparison H L) ≫
      derivedInternalHom_comp H K ringSingle L
  naturality {L₁ L₂} f := by
    -- Proof comment: first move `f` through the unit comparison into `RHom_A(A[0], -)`, then use
    -- the target-variable functoriality of composition in the closed monoidal structure.
    rw [Functor.map_comp, Category.assoc, derivedInternalHomUnitComparison_natural]
    simp only [Functor.map_comp, derivedInternalHomMap, derivedInternalHom_comp, Category.assoc]

/-- The canonical comparison
`K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)`. -/
abbrev derivedDualTensorToEnd
    (H : RHomPkg) (K : DMod) :
    K ⊗[A]^L Kᵛ⟮H⟯ ⟶ RHom[H](K, K) :=
  (derivedDualTensorComparison H K).app K

-- Proof sketch: choose a bounded finite-projective representative of `K`, let `E^•` be its
-- termwise dual, and use the left-dual pairing from Section `15.73` to identify the totalized
-- tensor functor `- ⊗_A E^•` with the Hom complex functor `Hom^•(K^•,-)`. Passing to derived
-- categories yields the canonical natural transformation above, and it is an isomorphism for a
-- perfect source complex.
/-- Lemma 15.75.15 (3): if `K` is perfect, then the canonical natural transformation
`- \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K,-)` is an isomorphism. -/
@[stacks 07VI]
theorem tensor_derivedDual_iso_derivedInternalHom
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualTensorComparison H K) := by
  rcases hK with ⟨P, eP, hP⟩
  letI : CochainComplex.IsBoundedFiniteProjective P := hP
  have hModelRightAdjointIso :
      MonoidalCategory.tensorRight P^∨ ≅ CategoryTheory.ihom P :=
    projective_model_tensor_dual_complex_iso (A := A) P
  have hModelDualIso :
      DerivedCategory.Q.obj P^∨ ≅ (DerivedCategory.Q.obj P)ᵛ⟮H⟯ :=
    projective_model_derivedDual_iso (A := A) H P
  -- Proof comment: the source model now carries the canonical right-adjoint-uniqueness
  -- isomorphism `- ⊗ P^\vee ≅ ihom P`; the remaining work is to identify its component with the
  -- named comparison `projective_model_tensor_dual_complex_comparison`, pass it through `Q`, and
  -- then compare the resulting derived morphism with the public `derivedDualTensorComparison`.
  -- TODO: prove that `((hModelRightAdjointIso.app L).hom)` is exactly
  -- `projective_model_tensor_dual_complex_comparison (A := A) P L`, rewrite its `Q`-image into
  -- `((derivedDualTensorComparison H (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj L))`,
  -- and finally transport along `eP`.
  sorry

/-- For a perfect object, the canonical comparison
`K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)` is an isomorphism. -/
theorem derivedDualTensorToEnd_isIso_of_isPerfect
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualTensorToEnd H K) := by
  -- Proof comment: part `(3)` is a natural isomorphism, so its component at `L = K` is an
  -- isomorphism as well.
  letI : IsIso (derivedDualTensorComparison H K) :=
    tensor_derivedDual_iso_derivedInternalHom H hK
  simpa [derivedDualTensorToEnd] using
    (inferInstance : IsIso ((derivedDualTensorComparison H K).app K))

/-- The canonical coevaluation morphism
`A[0] \to K \otimes_A^{\mathbf L} K^\vee`,
obtained from the identity of `K` via the tensor-to-endomorphism comparison. -/
private noncomputable def derivedDualCoevaluationDerivedTensor
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    ringSingle ⟶ K ⊗[A]^L Kᵛ⟮H⟯ :=
  derivedInternalHomIdUnit H K ≫
    inv (derivedDualTensorToEnd H K)

/-- Helper for Lemma 15.75.15: the derived coevaluation is defined so that composing it with the
tensor-to-endomorphism comparison recovers the internal-Hom identity morphism of `K`. -/
private theorem derivedDualCoevaluationDerivedTensor_comp_tensorToEnd
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    derivedDualCoevaluationDerivedTensor H K ≫
        derivedDualTensorToEnd H K =
      derivedInternalHomIdUnit H K := by
  -- Proof comment: cancel the inverse introduced in the definition of the coevaluation.
  simp [derivedDualCoevaluationDerivedTensor, Category.assoc]

/-- Helper for Lemma 15.75.15: whiskering the coevaluation/comparison identity on the left by the
derived dual produces the left-triangle prefix normalization needed later. -/
private theorem derivedDualCoevaluationDerivedTensor_whiskerLeft_comp_tensorToEnd
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    Kᵛ⟮H⟯ ◁ derivedDualCoevaluationDerivedTensor H K ≫
        Kᵛ⟮H⟯ ◁ derivedDualTensorToEnd H K =
      Kᵛ⟮H⟯ ◁ derivedInternalHomIdUnit H K := by
  -- Proof comment: this is just the base cancellation identity whiskered by `K^\vee`.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ Kᵛ⟮H⟯ ◁ k)
      (derivedDualCoevaluationDerivedTensor_comp_tensorToEnd H K)

/-- Helper for Lemma 15.75.15: whiskering the coevaluation/comparison identity on the right by
`K` produces the right-triangle prefix normalization needed later. -/
private theorem derivedDualCoevaluationDerivedTensor_whiskerRight_comp_tensorToEnd
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    derivedDualCoevaluationDerivedTensor H K ▷ K ≫
        derivedDualTensorToEnd H K ▷ K =
      derivedInternalHomIdUnit H K ▷ K := by
  -- Proof comment: this is the same cancellation identity, now whiskered by `K` on the right.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ▷ K)
      (derivedDualCoevaluationDerivedTensor_comp_tensorToEnd H K)

/-- The canonical evaluation morphism
`K^\vee ⊗ K \to \mathbb{1}` in the monoidal category `D(A)`. -/
noncomputable def derivedDualEvaluation
    (H : RHomPkg) (K : DMod) :
    Kᵛ⟮H⟯ ⊗ K ⟶ 𝟙_ DMod :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct Kᵛ⟮H⟯ K).hom ≫
    derivedDualEvaluationDerivedTensor H K ≫
      (singleZeroIsoTensorUnit : ringSingle ≅ 𝟙_ DMod).hom

/-- The canonical coevaluation morphism
`\mathbb{1} \to K ⊗ K^\vee` in the monoidal category `D(A)`. -/
noncomputable def derivedDualCoevaluation
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    𝟙_ DMod ⟶ K ⊗ Kᵛ⟮H⟯ :=
  (singleZeroIsoTensorUnit : ringSingle ≅ 𝟙_ DMod).inv ≫
    derivedDualCoevaluationDerivedTensor H K ≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct K Kᵛ⟮H⟯).inv

-- Proof sketch: after transporting across the inverse of
-- `K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)`, the first triangle identity becomes
-- the identity of `K^\vee`.
/-- The canonical coevaluation and evaluation maps for the derived dual satisfy the first triangle
identity. -/
theorem derivedDual_coevaluation_evaluation
    (H : RHomPkg) {K : DMod}
    [IsIso (derivedDualTensorToEnd H K)] :
    Kᵛ⟮H⟯ ◁ derivedDualCoevaluation H K ≫
        (α_ _ _ _).inv ≫
        derivedDualEvaluation H K ▷ Kᵛ⟮H⟯ =
      (ρ_ Kᵛ⟮H⟯).hom ≫
        (λ_ Kᵛ⟮H⟯).inv := by
  -- TODO: insert `Kᵛ⟮H⟯ ◁ derivedDualTensorToEnd H K`, reduce the remaining suffix to the
  -- closed-monoidal identity tail, and then close with the right unitor of `Kᵛ⟮H⟯`.
  sorry

-- Proof sketch: transport the identity of `K` through the same tensor-to-endomorphism
-- isomorphism.
/-- The canonical coevaluation and evaluation maps for the derived dual satisfy the second
triangle identity. -/
theorem derivedDual_evaluation_coevaluation
    (H : RHomPkg) {K : DMod}
    [IsIso (derivedDualTensorToEnd H K)] :
    derivedDualCoevaluation H K ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ derivedDualEvaluation H K =
      (λ_ K).hom ≫ (ρ_ K).inv := by
  -- TODO: transport the identity of `K` across `derivedDualTensorToEnd H K`, normalize the
  -- explicit evaluation suffix, and then cancel the remaining unitors.
  sorry

/-- The derived dual together with its canonical coevaluation and evaluation maps gives a left
dual once the tensor-to-endomorphism comparison is an isomorphism. -/
@[reducible] noncomputable def derivedDualExactPairingOfIsIso
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    ExactPairing Kᵛ⟮H⟯ K :=
  letI : ExactPairing K Kᵛ⟮H⟯ :=
    { coevaluation' := derivedDualCoevaluation H K
      evaluation' := derivedDualEvaluation H K
      coevaluation_evaluation' := derivedDual_coevaluation_evaluation H
      evaluation_coevaluation' := derivedDual_evaluation_coevaluation H }
  BraidedCategory.exactPairing_swap K Kᵛ⟮H⟯

/-- For a perfect object, the derived dual is the canonical left dual furnished by the evaluation
and coevaluation maps above. -/
noncomputable abbrev derivedDualExactPairing
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    ExactPairing Kᵛ⟮H⟯ K :=
  letI : IsIso (derivedDualTensorToEnd H K) :=
    derivedDualTensorToEnd_isIso_of_isPerfect H hK
  derivedDualExactPairingOfIsIso H K

/-- The induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to H^0(R\mathrm{Hom}_A(K, L))`. -/
noncomputable def derivedDualTensorZeroCohomologyComparison
    (H : RHomPkg) (K L : DMod) :
    (𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯) ⟶
      (𝓗 0).obj (RHom[H](K, L)) :=
  (𝓗 0).map ((derivedDualTensorComparison H K).app L)

-- Proof sketch: apply degree-zero cohomology to the tensor/Hom comparison from part `(3)`.
/-- If `K` is perfect, then the induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to H^0(R\mathrm{Hom}_A(K, L))` is an isomorphism. -/
theorem derivedDualTensorZeroCohomologyComparison_isIso_of_isPerfect
    (H : RHomPkg)
    {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    IsIso (derivedDualTensorZeroCohomologyComparison H K L) := by
  -- Proof comment: degree-zero cohomology preserves the componentwise isomorphism from part `(3)`.
  letI : IsIso (derivedDualTensorComparison H K) :=
    tensor_derivedDual_iso_derivedInternalHom H hK
  simpa [derivedDualTensorZeroCohomologyComparison] using
    (Functor.map_isIso (𝓗 0) ((derivedDualTensorComparison H K).app L))

/-- The canonical degree-zero bridge from `Ext^0_A(K, L) = ShiftedHom K L 0` to
`Hom_{D(A)}(K, L)`. -/
private noncomputable abbrev shiftedHomZeroLinearEquiv (K L : DMod) :
    Ext^((0 : ℤ))(K, L) ≃ₗ[A] (K ⟶ L) :=
  (LinearEquiv.ofBijective
      { toFun := ShiftedHom.mk₀ (0 : ℤ) rfl
        map_add' := by
          intro f g
          simp
        map_smul' := by
          intro r f
          simpa using ShiftedHom.mk₀_smul (0 : ℤ) rfl r f }
      (by
        constructor
        · intro f g hfg
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).injective <| by
            simpa using hfg
        · intro x
          refine ⟨(ShiftedHom.homEquiv (0 : ℤ) rfl).symm x, ?_⟩
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).apply_symm_apply x)).symm

/-- The canonical degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to \operatorname{Ext}^0_A(K, L)`. -/
noncomputable def derivedDualTensorExtZeroComparison
    (H : RHomPkg) (K L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) →ₗ[A] Ext^((0 : ℤ))(K, L) :=
  (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).toLinearMap.comp
    (derivedDualTensorZeroCohomologyComparison H K L).hom

-- Proof sketch: apply degree-zero cohomology to the tensor/Hom comparison from part `(3)`, then
-- identify the target with the chapter owner `Ext^0_A(K, L)` via the standard degree-zero
-- cohomology/internal-Hom comparison.
/-- Lemma 15.75.15 (4): if `K` is perfect, then the induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to \operatorname{Ext}^0_A(K, L)` is bijective. -/
@[stacks 07VI]
theorem derivedDualTensorZeroCohomology_iso_extZero
    (H : RHomPkg)
    {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    Function.Bijective (derivedDualTensorExtZeroComparison H K L) := by
  let f := (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).toLinearMap
  have hf : Function.Bijective f := by
    simpa [f] using (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).bijective
  letI : IsIso (derivedDualTensorZeroCohomologyComparison H K L) :=
    derivedDualTensorZeroCohomologyComparison_isIso_of_isPerfect H hK L
  let hg := ConcreteCategory.bijective_of_isIso
    (derivedDualTensorZeroCohomologyComparison H K L)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact hg.1 (hf.1 hxy)
  · intro z
    obtain ⟨w, hw⟩ := hf.2 z
    obtain ⟨x, hx⟩ := hg.2 w
    refine ⟨x, ?_⟩
    simpa [derivedDualTensorExtZeroComparison, hw] using (congrArg f hx).trans hw

/-- For a perfect object `K`, the degree-zero comparison identifies
`H^0(L \otimes_A^{\mathbf L} K^\vee)` with `\operatorname{Ext}^0_A(K, L)` as an `A`-linear
equivalence. -/
noncomputable def derivedDualTensorExtZeroEquiv
    (H : RHomPkg) {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) ≃ₗ[A] Ext^((0 : ℤ))(K, L) :=
  LinearEquiv.ofBijective
    (derivedDualTensorExtZeroComparison H K L)
    (derivedDualTensorZeroCohomology_iso_extZero H hK L)

/-- Companion bridge: the degree-zero comparison specialized from `Ext^0_A(K, L)` to the ordinary
morphism module `Hom_{D(A)}(K, L)`. -/
noncomputable def derivedDualTensorZeroLinearComparison
    (H : RHomPkg) (K L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) →ₗ[A] (K ⟶ L) :=
  (shiftedHomZeroLinearEquiv K L).toLinearMap.comp
    (derivedDualTensorExtZeroComparison H K L)

/-- Companion bridge: for a perfect object `K`, the degree-zero comparison identifies
`H^0(L \otimes_A^{\mathbf L} K^\vee)` with `Hom_{D(A)}(K, L)` after transporting
`Ext^0_A(K, L)` across the canonical degree-zero equivalence. -/
noncomputable def derivedDualTensorZeroLinearEquiv
    (H : RHomPkg) {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) ≃ₗ[A] (K ⟶ L) :=
  (derivedDualTensorExtZeroEquiv H hK L).trans (shiftedHomZeroLinearEquiv K L)

end

end CategoryTheory
