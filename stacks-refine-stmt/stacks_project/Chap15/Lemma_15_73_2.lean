import stacks_project.Chap13.Definition_13_8_1
import stacks_project.Chap15.Lemma_15_72_4
import stacks_project.Chap15.Lemma_15_72_1
import stacks_project.Chap15.Lemma_15_73_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ExactPairing
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape
open HomologicalComplex

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
local notation "BoundedCpx" => CochainComplex.bounded (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

private abbrev TermwiseFiniteProjective (M : CpxR) : Prop :=
  ∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)

/- Domain-style sampling:
- primary domain: rigid duality for cochain complexes of `R`-modules, together with the chapter
  owner for module-valued internal-Hom complexes and the boundedness owner from Chapter `13`;
- sampled owner declarations:
  `ExactPairing`,
  `CochainComplex.bounded`,
  `ihom`,
  `rightDualIso`;
- best owner abstraction: the explicit dual complex attached to `M^•` should use the canonical
  closed-category owner `(ihom M).obj (𝟙_ CpxR)`, written source-facing as `M^∨` with the ambient
  closed structure implicit in instances, rather than a second entrywise reimplementation of its
  objects, differential, shape, and `d ∘ d = 0` proof;
- primitive vs. derived:
  the primitive data here are the complex `M`, the exact pairing `ExactPairing M N`, and the
  canonical internal-Hom owner `ihom`; the textbook signed-transpose dual complex is
  derived API over that owner, while boundedness remains owned by `CochainComplex.bounded`.

Source/core/bridge triage:
- `source-facing`: the textbook dual complex `n ↦ Hom_R(M^{-n}, R)` and the duality statements of
  Lemma `15.73.2`;
- `core/canonical`: `ExactPairing`, `CochainComplex.bounded`, and the internal-Hom owner `ihom`;
- `bridge/view`: the internal-Hom-to-unit specialization `(ihom M).obj (𝟙_ CpxR)`, written
  source-facing as `M^∨`.
-/

variable {M N : CochainComplex (ModuleCat R) ℤ}
variable [ExactPairing M N]

private abbrev tensorSummand (M N : CpxR) (p q : ℤ) : ModuleCat R :=
  ((curriedTensor (ModuleCat R)).obj (M.X p)).obj (N.X q)

private noncomputable def exactPairing_degreewise_projection (n : ℤ) :
    ((M ⊗ N : CpxR).X 0) ⟶ tensorSummand M N n (-n) :=
  HomologicalComplex.mapBifunctorDesc fun p q _ ↦
    if hp : p = n then
      if hq : q = -n then
        show tensorSummand M N p q ⟶ tensorSummand M N n (-n) from
          eqToHom (by subst p; subst q; rfl)
      else
        show tensorSummand M N p q ⟶ tensorSummand M N n (-n) from
          0
    else
      show tensorSummand M N p q ⟶ tensorSummand M N n (-n) from
        0

/-- The degree-`(n,-n)` coevaluation map extracted from the coevaluation of an exact pairing of
cochain complexes. -/
noncomputable def exactPairing_degreewise_coevaluation (n : ℤ) :
    𝟙_ (ModuleCat R) ⟶ ((M.X n) ⊗ (N.X (-n)) : ModuleCat R) :=
  (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
    ((inferInstance : ExactPairing M N).coevaluation').f 0 ≫
    exactPairing_degreewise_projection n

/-- The degree-`(-n,n)` evaluation map extracted from the evaluation of an exact pairing of
cochain complexes. -/
noncomputable def exactPairing_degreewise_evaluation (n : ℤ) :
    ((N.X (-n)) ⊗ (M.X n) : ModuleCat R) ⟶ 𝟙_ (ModuleCat R) :=
  ιTensorObj N M (-n) n 0 (neg_add_cancel n) ≫
    ((inferInstance : ExactPairing M N).evaluation').f 0 ≫
    (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom

-- Proof sketch: the coevaluation `η : 𝟙 ⟶ M ⊗ N` has only finitely many nonzero homogeneous
-- components because the tensor unit is concentrated in degree `0`; the triangle identities then
-- force both complexes to vanish outside a finite interval.
/-- Lemma 15.73.2 (1): if `M^•` is a left dual of `N^•` in the monoidal category of cochain
complexes of `R`-modules, then `M^•` is bounded. -/
theorem exactPairing_left_complex_isBounded :
    BoundedCpx M := sorry

-- Proof sketch: apply the same boundedness argument after swapping the exact pairing.
/-- Lemma 15.73.2 (2): if `M^•` is a left dual of `N^•`, then `N^•` is bounded. -/
theorem exactPairing_right_complex_isBounded :
    BoundedCpx N := sorry

-- Proof sketch: the degree-`0` components of the coevaluation and evaluation induce a left dual
-- pairing between `M^n` and `N^{-n}`; then apply the single-module duality lemma degreewise.
/-- Lemma 15.73.2 (3): for every `n`, the module `M^n` is finite projective over `R`. -/
theorem exactPairing_left_term_finite_projective (n : ℤ) :
    Module.Finite R (M.X n) ∧ Module.Projective R (M.X n) := sorry

-- Proof sketch: after extracting the degreewise left dual pairing between `M^n` and `N^{-n}`,
-- apply the single-module duality lemma to the dual module `N^{-n}`.
/-- Lemma 15.73.2 (4): for every `n`, the module `N^n` is finite projective over `R`. -/
theorem exactPairing_right_term_finite_projective (n : ℤ) :
    Module.Finite R (N.X n) ∧ Module.Projective R (N.X n) := sorry

-- Proof sketch: decompose the degree-`0` parts of the complex coevaluation and evaluation into
-- their homogeneous summands; the triangle identities then restrict to degree `n` and `-n`,
-- yielding the required left dual pairing on modules.
/-- Lemma 15.73.2 (5): the degreewise components `M^n` and `N^{-n}` inherit a left dual pairing
from the exact pairing of complexes. -/
@[implicit_reducible]
noncomputable def exactPairing_degreewise_left_dual (n : ℤ) :
    ExactPairing (M.X n : ModuleCat R) (N.X (-n) : ModuleCat R) where
  coevaluation' := exactPairing_degreewise_coevaluation n
  evaluation' := exactPairing_degreewise_evaluation n
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

variable (M)

section ClosedDuality

variable [BraidedCategory (CochainComplex (ModuleCat R) ℤ)]
variable [MonoidalClosed (CochainComplex (ModuleCat R) ℤ)]

/-- The dual complex `M^∨ = \operatorname{Hom}^\bullet_R(M^\bullet, R[0])`, realized as internal
Hom into the tensor unit. -/
noncomputable abbrev moduleComplexDual
    (M : CochainComplex (ModuleCat R) ℤ) :
    CochainComplex (ModuleCat R) ℤ :=
  (ihom M).obj (𝟙_ CpxR)

@[inherit_doc moduleComplexDual]
postfix:max "^∨" => moduleComplexDual

private noncomputable def moduleComplexInternalHomIdUnit
    (M : CochainComplex (ModuleCat R) ℤ) :
    𝟙_ CpxR ⟶ (ihom M).obj M :=
  curry ((ρ_ M).hom)

private abbrev moduleComplexDualTensorToEnd
    (M : CochainComplex (ModuleCat R) ℤ) :
    M ⊗ M^∨ ⟶ (ihom M).obj M :=
  module_complex_tensor_internal_hom_comparison M (𝟙_ CpxR) M ≫
    (ihom M).map ((ρ_ M).hom)

private noncomputable def moduleComplexDualCoevaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    [IsIso (moduleComplexDualTensorToEnd M)] :
    𝟙_ CpxR ⟶ M ⊗ M^∨ :=
  moduleComplexInternalHomIdUnit M ≫
    inv (moduleComplexDualTensorToEnd M)

private abbrev moduleComplexDualEvaluation
    (M : CochainComplex (ModuleCat R) ℤ) :
    M^∨ ⊗ M ⟶ 𝟙_ CpxR :=
  (β_ M^∨ M).hom ≫ (ihom.ev M).app (𝟙_ CpxR)

private theorem moduleComplexDual_coevaluation_evaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    [IsIso (moduleComplexDualTensorToEnd M)] :
    M^∨ ◁ moduleComplexDualCoevaluation M ≫
        (α_ _ _ _).inv ≫
        moduleComplexDualEvaluation M ▷ M^∨ =
      (ρ_ M^∨).hom ≫
        (λ_ M^∨).inv := by
  sorry

private theorem moduleComplexDual_evaluation_coevaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    [IsIso (moduleComplexDualTensorToEnd M)] :
    moduleComplexDualCoevaluation M ▷ M ≫
        (α_ _ _ _).hom ≫
        M ◁ moduleComplexDualEvaluation M =
      (λ_ M).hom ≫ (ρ_ M).inv := by
  sorry

@[reducible] private noncomputable def moduleComplexDualExactPairingOfIsIso
    (M : CochainComplex (ModuleCat R) ℤ)
    [IsIso (moduleComplexDualTensorToEnd M)] :
    ExactPairing M^∨ M :=
  letI : ExactPairing M M^∨ :=
    { coevaluation' := moduleComplexDualCoevaluation M
      evaluation' := moduleComplexDualEvaluation M
      coevaluation_evaluation' := moduleComplexDual_coevaluation_evaluation M
      evaluation_coevaluation' := moduleComplexDual_evaluation_coevaluation M }
  BraidedCategory.exactPairing_swap M M^∨

-- Proof sketch: define the coevaluation by transporting the identity of `M^•` across the
-- canonical comparison `M^• ⊗ (M^•)^∨ ⟶ Hom^•(M^•, M^•)`, use the evaluation map from `ihom.ev`,
-- and then verify the triangle identities by the signed-transpose description of the dual
-- differential.
/-- Lemma 15.73.2 (7): conversely, if `M^•` is bounded and each `M^n` is a finite projective
`R`-module, then the dual complex `M^∨ = \operatorname{Hom}^\bullet_R(M^\bullet, R[0])` is a left
dual of `M^•`. -/
@[reducible]
noncomputable def moduleComplexDualExactPairing
    (hbounded : BoundedCpx M)
    (hfinite_projective : ∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)) :
    ExactPairing M^∨ M :=
  have hIso :
      IsIso
        (show M ⊗ M^∨ ⟶ (ihom M).obj M from
          moduleComplexDualTensorToEnd M) := by
    sorry
  letI : IsIso (moduleComplexDualTensorToEnd M) := hIso
  moduleComplexDualExactPairingOfIsIso M

end ClosedDuality

-- Proof sketch: specialize Lemma `15.73.1` to the degreewise exact pairing from clause `(5)`,
-- with index `-n`, to identify `N^n` with `Hom_R(M^{-n}, R)`.
/-- The degreewise identification used in Lemma `15.73.2 (6)`: under an exact pairing
`M^• ⊣ N^•`, the term `N^n` is canonically isomorphic to `Hom_R(M^{-n}, R)`. -/
noncomputable abbrev exactPairing_rightTermIso_moduleDual
    (M N : CpxR) [ExactPairing M N] (n : ℤ) :
    ModuleCat.of R (N.X n) ≅ ModuleCat.of R (Module.Dual R (M.X (-n))) := by
  letI : ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X n)) := by
    simpa [neg_neg] using
      (exactPairing_degreewise_left_dual (-n) :
        ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X (-(-n)))))
  letI : ExactPairing (ModuleCat.of R (N.X n)) (ModuleCat.of R (M.X (-n))) :=
    BraidedCategory.exactPairing_swap _ _
  exact asIso ExactPairing.toModuleDual

variable {M}

-- Proof sketch: identify `N^n` and `N^{n+1}` with the degreewise dual modules using
-- `exactPairing_rightTermIso_moduleDual`; then the chain-map compatibility of the complex pairing
-- gives the textbook formula that `d_N^n` is the signed transpose of `d_M^{-n-1}`.
/-- Lemma 15.73.2 (6): under the degreewise identifications
`N^n ≅ Hom_R(M^{-n}, R)` and `N^{n + 1} ≅ Hom_R(M^{-n-1}, R)` coming from Lemma `15.73.1`, the
differential `d_N^n` is the signed transpose `-(-1)^n (d_M^{-n-1})ᵗ`. -/
theorem exactPairing_rightTermIso_moduleDual_d_comm (n : ℤ) :
    CommSq (N.d n (n + 1))
      (exactPairing_rightTermIso_moduleDual M N n).hom
      (exactPairing_rightTermIso_moduleDual M N (n + 1)).hom
      ((-n.negOnePow) •
        ModuleCat.ofHom
          ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) :
            Module.Dual R (M.X (-n)) →ₗ[R] Module.Dual R (M.X (-(n + 1))))) := sorry

end
