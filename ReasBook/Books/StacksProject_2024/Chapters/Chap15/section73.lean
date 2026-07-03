import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_73_1 (from Chap15) -/
/-
Domain-style sampling:
- primary domain: duality in `ModuleCat R`, comparing an abstract exact pairing with the canonical
  module-dual owner of `M`;
- sampled owner declarations:
  `Definition 4.43.5` (`ExactPairing Y X` for a left dual `Y` of `X`),
  `MonoidalClosed.curry`,
  `Module.Dual`,
  `ModuleCat.homLinearEquiv`,
  `CategoryTheory.rightDualIso`,
  `BraidedCategory.exactPairing_swap`;
- best owner abstraction: the comparison from a chosen left dual is canonically the curried
  evaluation morphism into the internal Hom to the tensor unit; the module-theoretic codomain
  `Module.Dual R M = Hom_R(M, R)` is the canonical owner view of that internal-Hom object in
  `ModuleCat R`;
- primitive data: the ambient commutative ring, the two `R`-modules, and the exact pairing
  instance `[ExactPairing (ModuleCat.of R N) (ModuleCat.of R M)]`;
- derived API: the internal Hom object `(ihom (ModuleCat.of R M)).obj (𝟙_ (ModuleCat R))`, the
  currying map from the evaluation pairing, and the resulting comparison morphism to the canonical
  dual owner.

Source/core/bridge triage:
- `source-facing`: the textbook map from a left dual of `M` to `Hom_R(M, R)`;
- `core/canonical`: `MonoidalClosed.curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M))`;
- `bridge/view`: `ExactPairing.toModuleDual`, the thin codomain-change bridge from the canonical
  curried evaluation morphism to the module-dual owner `Module.Dual R M`.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ModuleCat
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [ExactPairing (ModuleCat.of R N) (ModuleCat.of R M)]

namespace ExactPairing

/-- The canonical morphism from a left dual `N` of `M` to the canonical module dual
`Module.Dual R M = Hom_R(M, R)`, obtained by currying the evaluation pairing and then identifying
the internal Hom to the tensor unit with `Module.Dual R M`. This is the inverse of the textbook
map `e`. -/
abbrev toModuleDual : ModuleCat.of R N ⟶ ModuleCat.of R (Module.Dual R M) :=
  curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) ≫
    ((homLinearEquiv :
        (ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R)) ≃ₗ[R] Module.Dual R M).toModuleIso.hom)

-- Proof sketch: choose a finite free module surjecting onto `M`, lift the coevaluation through
-- it, and use the triangle identity to factor `𝟙_M` through that finite free module; this gives
-- finite projectivity of `M`.
/-- Lemma 15.73.1 (1): if `N` is a left dual of `M` in the monoidal category of `R`-modules, then
`M` is a finite projective `R`-module. -/
theorem exactPairing_source_finite_projective :
    Module.Finite R M ∧ Module.Projective R M := sorry

-- Proof sketch: apply the same argument as for `M` after swapping the exact pairing in the
-- symmetric monoidal category `ModuleCat R`.
/-- Lemma 15.73.1 (2): if `N` is a left dual of `M` in the monoidal category of `R`-modules, then
`N` is a finite projective `R`-module. -/
theorem exactPairing_target_finite_projective :
    Module.Finite R N ∧ Module.Projective R N := sorry

-- Proof sketch: specialize the canonical hom-set equivalence of Lemma `4.43.6` to
-- `Z = 𝟙_(ModuleCat R)` and `Z' = 𝟙_(ModuleCat R)`, then identify maps out of and into the tensor
-- unit with `Module.Dual R M` and `N`.
/-- Lemma 15.73.1 (3): the canonical morphism `N ⟶ Module.Dual R M` obtained from the evaluation
pairing is an isomorphism; equivalently, the textbook map
`e : Hom_R(M, R) → N` given by `φ ↦ (φ ⊗ 1)(η)` is bijective. -/
theorem isIso_toModuleDual :
    IsIso (toModuleDual : ModuleCat.of R N ⟶ ModuleCat.of R (Module.Dual R M)) := sorry

attribute [instance] isIso_toModuleDual

-- Proof sketch: `toModuleDual` is obtained by currying the evaluation pairing and then
-- identifying the internal-Hom object to the tensor unit with `Module.Dual R M`, so evaluation
-- on `m` is literally the original pairing.
/-- Lemma 15.73.1 (4): for `n : N` and `m : M`, evaluating the functional
`toModuleDual n : Module.Dual R M` at `m` recovers the exact-pairing evaluation on
`m ⊗ n`; equivalently, this is the inverse of the textbook map `e` applied to `n` and then
evaluated at `m`. -/
theorem toModuleDual_apply (n : N) (m : M) :
    (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) (m ⊗ₜ[R] n) =
      toModuleDual n m := by
  rfl

end ExactPairing

end

/-! ### Lemma_15_73_2 (from Chap15) -/
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
