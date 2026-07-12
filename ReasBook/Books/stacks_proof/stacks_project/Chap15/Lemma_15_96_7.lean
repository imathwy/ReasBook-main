import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.RingTheory.Regular.IsSMulRegular
import StacksProject_2024.Chap15.PrincipalIdeal
import StacksProject_2024.Chap15.«15_96_5_1»
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex
open HomologicalComplex

noncomputable section

universe u v w

section

variable {A : Type u} [CommRing A]

/-- A cochain complex of `A`-modules indexed by `ℤ`. -/
abbrev ModuleComplex (A : Type u) [CommRing A] := CochainComplex (ModuleCat A) ℤ

/-- A cochain complex of `A`-modules indexed by `ℕ`. -/
abbrev NatModuleCochainComplex (A : Type u) [CommRing A] :=
  CochainComplex (ModuleCat A) ℕ

namespace BerthelotOgusInt

/-- A `ℤ`-indexed cochain complex is termwise `f`-torsion free if multiplication by `f` is
injective in every degree. -/
class IsTermwiseFTorsionFree (f : A) (K : ModuleComplex A) : Prop where
  /-- Multiplication by `f` is injective in degree `i`. -/
  isSMulRegular (i : ℤ) : IsSMulRegular (K.X i) f

instance (f : A) (K : ModuleComplex A) [h : IsTermwiseFTorsionFree f K] (i : ℤ) :
    IsSMulRegular (K.X i) f :=
  h.isSMulRegular i

end BerthelotOgusInt

open BerthelotOgusInt

/-- A nonnegative cochain complex is termwise `f`-torsion free if multiplication by `f` is
injective in every degree. -/
class IsTermwiseFTorsionFree (f : A) (M : NatModuleCochainComplex A) : Prop where
  /-- Multiplication by `f` is injective in degree `n`. -/
  isSMulRegular (n : ℕ) : IsSMulRegular (M.X n) f

instance (f : A) (M : NatModuleCochainComplex A) [h : IsTermwiseFTorsionFree f M] (n : ℕ) :
    IsSMulRegular (M.X n) f :=
  h.isSMulRegular n

namespace IsTermwiseFTorsionFree

/-- Passing to extension by zero gives the owner `ℤ`-indexed torsion-freeness predicate. -/
theorem toIsTermwiseFTorsionFree
    {f : A} {M : NatModuleCochainComplex A} (hM : IsTermwiseFTorsionFree f M) :
    BerthelotOgusInt.IsTermwiseFTorsionFree f (M.extend ComplexShape.embeddingUpNat) := by
  constructor
  intro i
  by_cases hi : 0 ≤ i
  · -- In nonnegative degrees, extension by zero identifies the term with the original degree.
    let e :
        ((M.extend ComplexShape.embeddingUpNat).X i) ≃ₗ[A] M.X i.toNat :=
      (M.extendXIso ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hi)).toLinearEquiv
    exact (LinearEquiv.isSMulRegular_congr e f).2 (hM.isSMulRegular i.toNat)
  · -- In negative degrees, the extended complex is zero, so regularity is automatic.
    let hzero : CategoryTheory.Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).X i) :=
      M.isZero_extend_X ComplexShape.embeddingUpNat i (by
        intro n hni
        exact hi (hni ▸ Int.natCast_nonneg n))
    letI : Subsingleton ((M.extend ComplexShape.embeddingUpNat).X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact IsSMulRegular.of_right_eq_zero_of_smul (fun x _hx => Subsingleton.elim _ _)

end IsTermwiseFTorsionFree

instance (f : A) (M : NatModuleCochainComplex A) [hM : IsTermwiseFTorsionFree f M] :
    BerthelotOgusInt.IsTermwiseFTorsionFree f (M.extend ComplexShape.embeddingUpNat) :=
  hM.toIsTermwiseFTorsionFree

namespace CochainComplex

/-- The degree-`i` differential on the scalar-restricted reduction of a cochain complex modulo
`I`. -/
private abbrev reduceModIdealADifferential
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    ModuleCat.of A (K.X i ⧸ I • (⊤ : Submodule A (K.X i))) ⟶
      ModuleCat.of A (K.X (i + 1) ⧸ I • (⊤ : Submodule A (K.X (i + 1)))) :=
  ModuleCat.ofHom <|
    Submodule.mapQ
      (I • (⊤ : Submodule A (K.X i)))
      (I • (⊤ : Submodule A (K.X (i + 1))))
      (K.d i (i + 1)).hom
      (Submodule.smul_top_le_comap_smul_top I (K.d i (i + 1)).hom)

/-- Two successive reduced differentials compose to zero. -/
private theorem reduceModIdealADifferential_sq
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    reduceModIdealADifferential I K i ≫ reduceModIdealADifferential I K (i + 1) = 0 := by
  -- The quotient differential is induced degreewise, so square-zero descends from the original
  -- relation `d ≫ d = 0`.
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun q ↦ ?_
  refine Quotient.inductionOn' q ?_
  intro x
  have hsq :
      (K.d i (i + 1) ≫ K.d (i + 1) ((i + 1) + 1)).hom x = 0 := by
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (K.d_comp_d i (i + 1) ((i + 1) + 1))) x
  have hsq' := hsq
  change (K.d (i + 1) ((i + 1) + 1)).hom ((K.d i (i + 1)).hom x) = 0 at hsq'
  change
    (Submodule.Quotient.mk
        ((K.d (i + 1) ((i + 1) + 1)).hom ((K.d i (i + 1)).hom x) :
          K.X ((i + 1) + 1)) :
      K.X ((i + 1) + 1) ⧸ I • (⊤ : Submodule A (K.X ((i + 1) + 1)))) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  rw [hsq']
  simp

/-- The scalar-restricted `A`-linear view of `K / IK`. -/
abbrev reduceModIdealA
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) :
    CochainComplex (ModuleCat.{v} A) ι :=
  let _ : DecidableEq ι := Classical.decEq ι
  CochainComplex.of
    (fun i ↦ ModuleCat.of A (K.X i ⧸ I • (⊤ : Submodule A (K.X i))))
    (fun i ↦ reduceModIdealADifferential I K i)
    (fun i ↦ reduceModIdealADifferential_sq I K i)

end CochainComplex

/- Domain-style sampling:
- primary domain: short exact sequences and connecting morphisms for cochain complexes of
  `A`-modules;
  `NatModuleCochainComplex`, `CochainComplex.reduceModIdealA`,
  together with the owner boundary `ShortComplex.ShortExact.δ` and the mathlib owner
  `Submodule.torsionBy`;
- best owner abstraction:
  `source-facing`: the bounded-below Berthelot-Ogus Bockstein operator and the surjectivity
    criterion on cycles;
  `core/canonical`: the `ModuleComplex A` short exact sequence
    `K/fK --f→ K/f²K → K/fK`, its connecting morphism, and the induced cycles map;
  `bridge/view`: the nonnegative `NatModuleCochainComplex A` surface used by the source-facing
    statements below;
- primitive data vs derived API: the primitive owner data are the quotient complexes, the
  short exact sequence, and the standard `a`-torsion owner `Submodule.torsionBy`. The Bockstein
  map and the cycle-surjectivity predicate are derived from those owners, so the bounded-below
  bridge should not expose a second public copy of the reduction-sequence data. -/

-- Proof sketch: if `x = f ^ 2 • y`, then also `x = f • (f • y)`, so every element of `f²M`
-- already lies in `fM`.
/-- The quotient submodule `(f²)M` is contained in `fM`. -/
private theorem principalIdeal_sq_smul_top_le
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    principalIdeal (f ^ 2) • (⊤ : Submodule A M) ≤
      Submodule.comap (LinearMap.id : M →ₗ[A] M) (principalIdeal f • (⊤ : Submodule A M)) :=
  by
  -- Compare the principal ideals first, then pass to their multiples of `⊤`.
  have hpow : principalIdeal (f ^ 2) ≤ principalIdeal f := by
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_
    rw [principalIdeal, pow_two]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  simpa using Submodule.smul_mono hpow le_rfl

-- Proof sketch: if `x = f • y`, then multiplying by `f` gives `f • x = f² • y`, so the
-- multiplication-by-`f` map carries `fM` into `f²M`.
/-- Multiplication by `f` sends `fM` into `f²M`. -/
private theorem principalIdeal_smul_top_le_sq_preimage
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    principalIdeal f • (⊤ : Submodule A M) ≤
      Submodule.comap (f • (LinearMap.id : M →ₗ[A] M))
        (principalIdeal (f ^ 2) • (⊤ : Submodule A M)) := by
  -- Push the source through multiplication by `f` and rewrite the image as an iterated smul.
  rw [← Submodule.map_le_iff_le_comap]
  calc
    Submodule.map (f • (LinearMap.id : M →ₗ[A] M)) (principalIdeal f • (⊤ : Submodule A M))
        = principalIdeal f •
            Submodule.map (f • (LinearMap.id : M →ₗ[A] M)) (⊤ : Submodule A M) := by
              rw [Submodule.map_smul'']
    _ = principalIdeal f • LinearMap.range (f • (LinearMap.id : M →ₗ[A] M)) := by
          rw [Submodule.map_top]
    _ ≤ principalIdeal f • (principalIdeal f • (⊤ : Submodule A M)) := by
          refine Submodule.smul_mono le_rfl ?_
          rintro _ ⟨x, rfl⟩
          -- Any value in the range is visibly a single `f`-multiple.
          change f • x ∈ principalIdeal f • (⊤ : Submodule A M)
          exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) (by simp)
    _ = (principalIdeal f * principalIdeal f) • (⊤ : Submodule A M) := by
          simpa using
            (Submodule.smul_assoc
              (principalIdeal f) (principalIdeal f) (⊤ : Submodule A M)).symm
    _ = principalIdeal (f ^ 2) • (⊤ : Submodule A M) := by
          rw [show principalIdeal f * principalIdeal f = principalIdeal (f ^ 2) by
            simpa [principalIdeal, pow_two] using Ideal.span_singleton_mul_span_singleton f f]

namespace ModFSquared

open BerthelotOgusInt

/- The canonical owner for the `f²`-to-`f` reduction sequence lives on the chapter's
`ModuleComplex A` owner. The bounded-below `Nat` API below is the bridge/view used by the
source-facing lemmas in this file, while downstream `ℤ`-indexed files should reuse the owner
declarations in this namespace directly. -/

/-- The reduction `K^\bullet / fK^\bullet` on the `ModuleComplex A` owner. -/
private abbrev modFComplex (f : A) (K : ModuleComplex A) :=
  reduceModIdealA (principalIdeal f) K

/-- The reduction `K^\bullet / f²K^\bullet` on the `ModuleComplex A` owner. -/
private abbrev modFSquaredComplex (f : A) (K : ModuleComplex A) :=
  reduceModIdealA (principalIdeal (f ^ 2)) K

/-- The termwise reduction map `K/f²K → K/fK`. -/
private abbrev reductionComponent (f : A) (K : ModuleComplex A) (i : ℤ) :
    (modFSquaredComplex f K).X i ⟶ (modFComplex f K).X i :=
  ModuleCat.ofHom <|
    Submodule.mapQ
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (LinearMap.id : K.X i →ₗ[A] K.X i)
      (principalIdeal_sq_smul_top_le f)

/-- The termwise multiplication map `K/fK → K/f²K` induced by `x ↦ f x`. -/
private abbrev multiplicationComponent (f : A) (K : ModuleComplex A) (i : ℤ) :
    (modFComplex f K).X i ⟶ (modFSquaredComplex f K).X i :=
  ModuleCat.ofHom <|
    Submodule.mapQ
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (f • (LinearMap.id : K.X i →ₗ[A] K.X i))
      (principalIdeal_smul_top_le_sq_preimage f)

/-- Helper for Lemma 15.96.7: the termwise reduction `K/f²K → K/fK` is induced by the identity
on representatives. -/
private theorem reductionComponent_apply_mk
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : K.X i) :
    (reductionComponent f K i).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x :
        K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
  -- The reduction map is the quotient map induced by the identity linear map.
  simpa [reductionComponent, LinearMap.id_apply] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
        (principalIdeal f • (⊤ : Submodule A (K.X i)))
        (LinearMap.id : K.X i →ₗ[A] K.X i))
      x

/-- Helper for Lemma 15.96.7: the termwise multiplication map sends a class modulo `f` to the
class of `f • x` modulo `f²`. -/
private theorem multiplicationComponent_apply_mk
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : K.X i) :
    (multiplicationComponent f K i).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f • x) :
        K.X i ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i))) := by
  -- This quotient map is induced by multiplication by `f` on representatives.
  simpa [multiplicationComponent, LinearMap.id_apply] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        (principalIdeal f • (⊤ : Submodule A (K.X i)))
        (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
        (f • (LinearMap.id : K.X i →ₗ[A] K.X i)))
      x

/-- Helper for Lemma 15.96.7: every single `f`-multiple dies in the quotient by `fK`. -/
private theorem quotient_mk_smul_eq_zero
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) (x : M) :
    (Submodule.Quotient.mk (f • x) :
      M ⧸ principalIdeal f • (⊤ : Submodule A M)) = 0 := by
  -- The class vanishes because `f • x` already lies in the denominator `fM`.
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  simpa [principalIdeal] using
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
      (show x ∈ (⊤ : Submodule A M) by simp))

/-- Helper for Lemma 15.96.7: the image of scalar multiplication by `a` is exactly the submodule
`aM`. -/
private theorem range_lsmul_eq_principalIdeal_smul_top
    {M : Type*} [AddCommGroup M] [Module A M] (a : A) :
    LinearMap.range (LinearMap.lsmul A M a) =
      principalIdeal a • (⊤ : Submodule A M) := by
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- A visible `a`-multiple lies in `aM` by construction.
    simpa [principalIdeal, LinearMap.lsmul_apply] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a)
        (show y ∈ (⊤ : Submodule A M) by simp))
  · intro hx
    -- To land in the range, it is enough to check the spanning generators of `aM`.
    have hle : principalIdeal a • (⊤ : Submodule A M) ≤ LinearMap.range (LinearMap.lsmul A M a) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨b, rfl⟩
      refine LinearMap.mem_range.mpr ⟨b • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.96.7: membership in `fM` is equivalent to being an explicit `f`-multiple.
-/
private theorem exists_smul_eq_of_mem_principalIdeal_smul_top
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) {x : M}
    (hx : x ∈ principalIdeal f • (⊤ : Submodule A M)) :
    ∃ y, f • y = x := by
  -- Rewrite the denominator as the range of multiplication by `f`.
  have hx' : x ∈ LinearMap.range (LinearMap.lsmul A M f) := by
    rwa [range_lsmul_eq_principalIdeal_smul_top (A := A) (M := M) f]
  simpa [LinearMap.lsmul_apply] using LinearMap.mem_range.mp hx'

/-- Helper for Lemma 15.96.7: in adjacent degrees the reduced differential is induced by the
original differential on representatives. -/
private theorem reduceModIdealA_d_eq
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    (CochainComplex.reduceModIdealA I K).d i (i + 1) =
      CochainComplex.reduceModIdealADifferential I K i := by
  -- The reduced complex is built with `CochainComplex.of`, so its adjacent differential is the
  -- defining quotient differential.
  simp [CochainComplex.reduceModIdealA, CochainComplex.of_d]

/-- Helper for Lemma 15.96.7: in adjacent degrees the reduced differential is induced by the
original differential on representatives. -/
private theorem reduceModIdealADifferential_apply_mk
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) (x : K.X i) :
    (CochainComplex.reduceModIdealADifferential I K i).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
        K.X (i + 1) ⧸ I • (⊤ : Submodule A (K.X (i + 1)))) := by
  -- The quotient differential is literally the map induced by `K.d i (i + 1)`.
  simpa [CochainComplex.reduceModIdealADifferential] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        (I • (⊤ : Submodule A (K.X i)))
        (I • (⊤ : Submodule A (K.X (i + 1))))
        (K.d i (i + 1)).hom)
      x

/-- Helper for Lemma 15.96.7: away from adjacent degrees, reduction modulo an ideal has zero
differential. -/
private theorem reduceModIdealA_d_eq_zero_of_ne
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) {i j : ι} (hij : j ≠ i + 1) :
    (CochainComplex.reduceModIdealA I K).d i j = 0 := by
  -- The reduced complex is built with `CochainComplex.of`, so non-adjacent differentials vanish
  -- by the cochain shape.
  exact (CochainComplex.reduceModIdealA I K).shape i j (by
    intro hji
    exact hij hji.symm)

/-- Helper for Lemma 15.96.7: in adjacent degrees the reduction map `K/f²K → K/fK` commutes with
the quotient differential after both sides are normalized on representatives. -/
private theorem reduction_differential_naturality
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    reductionComponent f K i ≫ (modFComplex f K).d i (i + 1) =
      (modFSquaredComplex f K).d i (i + 1) ≫ reductionComponent f K (i + 1) := by
  -- Both composites send the class of `x` modulo `f²` to the class of `d x` modulo `f`.
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i))) q
  change
    ((modFComplex f K).d i (i + 1)).hom
        ((reductionComponent f K i).hom (Submodule.Quotient.mk x)) =
      (reductionComponent f K (i + 1)).hom
        (((modFSquaredComplex f K).d i (i + 1)).hom (Submodule.Quotient.mk x))
  rw [reduceModIdealA_d_eq, reduceModIdealA_d_eq]
  rw [reductionComponent_apply_mk]
  calc
    (CochainComplex.reduceModIdealADifferential (principalIdeal f) K i).hom
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
        K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) :=
      reduceModIdealADifferential_apply_mk (I := principalIdeal f) K i x
    _ = (reductionComponent f K (i + 1)).hom
          (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
            K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) := by
          rw [reductionComponent_apply_mk]
    _ = (reductionComponent f K (i + 1)).hom
          ((CochainComplex.reduceModIdealADifferential
              (principalIdeal (f ^ 2)) K i).hom (Submodule.Quotient.mk x)) := by
          exact congrArg
            ((reductionComponent f K (i + 1)).hom)
            (reduceModIdealADifferential_apply_mk (I := principalIdeal (f ^ 2)) K i x).symm

/-- Helper for Lemma 15.96.7: in adjacent degrees the multiplication map `K/fK → K/f²K`
commutes with the quotient differential after both sides are normalized on representatives. -/
private theorem multiplication_differential_naturality
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    multiplicationComponent f K i ≫ (modFSquaredComplex f K).d i (i + 1) =
      (modFComplex f K).d i (i + 1) ≫ multiplicationComponent f K (i + 1) := by
  -- Both composites send the class of `x` modulo `f` to the class of `f • d x` modulo `f²`.
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective
      (principalIdeal f • (⊤ : Submodule A (K.X i))) q
  change
    ((modFSquaredComplex f K).d i (i + 1)).hom
        ((multiplicationComponent f K i).hom (Submodule.Quotient.mk x)) =
      (multiplicationComponent f K (i + 1)).hom
        (((modFComplex f K).d i (i + 1)).hom (Submodule.Quotient.mk x))
  rw [reduceModIdealA_d_eq, reduceModIdealA_d_eq]
  rw [multiplicationComponent_apply_mk]
  calc
    (CochainComplex.reduceModIdealADifferential (principalIdeal (f ^ 2)) K i).hom
        (Submodule.Quotient.mk (f • x)) =
      (Submodule.Quotient.mk ((K.d i (i + 1)).hom (f • x)) :
        K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) :=
      reduceModIdealADifferential_apply_mk (I := principalIdeal (f ^ 2)) K i (f • x)
    _ = (Submodule.Quotient.mk (f • (K.d i (i + 1)).hom x) :
          K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) := by
          rw [LinearMap.map_smul]
    _ = (multiplicationComponent f K (i + 1)).hom
          (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
            K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) := by
          rw [multiplicationComponent_apply_mk]
    _ = (multiplicationComponent f K (i + 1)).hom
          ((CochainComplex.reduceModIdealADifferential
              (principalIdeal f) K i).hom (Submodule.Quotient.mk x)) := by
          exact congrArg
            ((multiplicationComponent f K (i + 1)).hom)
            (reduceModIdealADifferential_apply_mk (I := principalIdeal f) K i x).symm

/-- The reduction maps `K/f²K → K/fK` commute with the reduced differentials. -/
private theorem reductionComponent_comm
    (f : A) (K : ModuleComplex A) (i j : ℤ) :
    CommSq
      (reductionComponent f K i)
      ((modFSquaredComplex f K).d i j)
      ((modFComplex f K).d i j)
      (reductionComponent f K j) := by
  by_cases hij : j = i + 1
  · subst hij
    -- Route correction: previous attempts got stuck in raw `Submodule.mapQ` transport; the
    -- representative-level normalization lemma isolates that coercion noise first.
    exact CommSq.mk (reduction_differential_naturality f K i)
  · -- Away from adjacent degrees, both reduced differentials vanish by the cochain shape.
    have hmodFSquared :
        (modFSquaredComplex f K).d i j = 0 :=
      reduceModIdealA_d_eq_zero_of_ne (principalIdeal (f ^ 2)) K hij
    have hmodF :
        (modFComplex f K).d i j = 0 :=
      reduceModIdealA_d_eq_zero_of_ne (principalIdeal f) K hij
    -- Once the non-adjacent differentials are zero, the square is formal.
    refine CommSq.mk ?_
    rw [hmodFSquared, hmodF]
    calc
      reductionComponent f K i ≫ 0 = 0 := by rw [CategoryTheory.Limits.comp_zero]
      _ = 0 ≫ reductionComponent f K j := by rw [CategoryTheory.Limits.zero_comp]

/-- The multiplication maps `K/fK → K/f²K` commute with the reduced differentials. -/
private theorem multiplicationComponent_comm
    (f : A) (K : ModuleComplex A) (i j : ℤ) :
    CommSq
      (multiplicationComponent f K i)
      ((modFComplex f K).d i j)
      ((modFSquaredComplex f K).d i j)
      (multiplicationComponent f K j) := by
  by_cases hij : j = i + 1
  · subst hij
    -- Route correction: the adjacent-degree square is proved only after caching the quotient
    -- normalization, so the remaining step is the linearity rewrite `d (f • x) = f • d x`.
    exact CommSq.mk (multiplication_differential_naturality f K i)
  · -- Outside adjacent degrees, the cochain-shape forces both differentials to vanish.
    have hmodFSquared :
        (modFSquaredComplex f K).d i j = 0 :=
      reduceModIdealA_d_eq_zero_of_ne (principalIdeal (f ^ 2)) K hij
    have hmodF :
        (modFComplex f K).d i j = 0 :=
      reduceModIdealA_d_eq_zero_of_ne (principalIdeal f) K hij
    -- Once the non-adjacent differentials are zero, the square is formal.
    refine CommSq.mk ?_
    rw [hmodFSquared, hmodF]
    calc
      multiplicationComponent f K i ≫ 0 = 0 := by rw [CategoryTheory.Limits.comp_zero]
      _ = 0 ≫ multiplicationComponent f K j := by rw [CategoryTheory.Limits.zero_comp]

/-- The cochain map `K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet`. -/
private def reductionMap (f : A) (K : ModuleComplex A) :
    modFSquaredComplex f K ⟶ modFComplex f K where
  f i := reductionComponent f K i
  comm' i j _ := (reductionComponent_comm f K i j).w

/-- The cochain map `K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet` induced by multiplication by
`f`. -/
private def multiplicationMap (f : A) (K : ModuleComplex A) :
    modFComplex f K ⟶ modFSquaredComplex f K where
  f i := multiplicationComponent f K i
  comm' i j _ := (multiplicationComponent_comm f K i j).w

/-- The composite `K/fK → K/f²K → K/fK` is zero. -/
private theorem multiplicationComponent_comp_reductionComponent
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    multiplicationComponent f K i ≫ reductionComponent f K i = 0 := by
  -- Evaluate the composite on representatives and observe that every `f`-multiple dies modulo
  -- `f`.
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun q ↦ ?_
  refine Quotient.inductionOn' q ?_
  intro x
  change
    (reductionComponent f K i).hom
        ((multiplicationComponent f K i).hom (Submodule.Quotient.mk x)) = 0
  rw [multiplicationComponent_apply_mk, reductionComponent_apply_mk]
  simpa using quotient_mk_smul_eq_zero f x

/-- The composite `K/fK → K/f²K → K/fK` is zero. -/
private theorem multiplicationMap_comp_reductionMap
    (f : A) (K : ModuleComplex A) :
    multiplicationMap f K ≫ reductionMap f K = 0 := by
  -- The cochain-map composite vanishes degreewise on the canonical quotient row.
  apply HomologicalComplex.hom_ext
  intro i
  exact multiplicationComponent_comp_reductionComponent f K i

/-- The short complex
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet`. -/
private abbrev shortComplex (f : A) (K : ModuleComplex A) :
    ShortComplex (ModuleComplex A) :=
  ShortComplex.mk (multiplicationMap f K) (reductionMap f K)
    (multiplicationMap_comp_reductionMap f K)

/-- Helper for Lemma 15.96.7: the canonical quotient row in a fixed degree is a short complex of
`A`-modules. -/
private abbrev degreeShortComplex (f : A) (K : ModuleComplex A) (i : ℤ) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk (multiplicationComponent f K i) (reductionComponent f K i)
    (multiplicationComponent_comp_reductionComponent f K i)

/-- Helper for Lemma 15.96.7: in a fixed degree, the kernel of the reduction
`K^i / f² K^i → K^i / f K^i` is exactly the image of multiplication by `f` on `K^i / f K^i`. -/
private theorem quotient_row_exact_at_middle
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    LinearMap.ker (reductionComponent f K i).hom =
      LinearMap.range (multiplicationComponent f K i).hom := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ :=
      Submodule.mkQ_surjective
        (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i))) q
    -- A kernel class reduces to zero modulo `f`, so its representative is already an `f`-multiple.
    have hx_mem :
        x ∈ principalIdeal f • (⊤ : Submodule A (K.X i)) := by
      have hx_zero :
          (reductionComponent f K i).hom (Submodule.Quotient.mk x) = 0 := by
        simpa using hq
      rw [reductionComponent_apply_mk] at hx_zero
      exact
        (Submodule.Quotient.mk_eq_zero
          (principalIdeal f • (⊤ : Submodule A (K.X i)))).1 hx_zero
    obtain ⟨y, hy⟩ :=
      exists_smul_eq_of_mem_principalIdeal_smul_top (A := A) (M := K.X i) f hx_mem
    -- Rewriting the representative as `f • y` gives the required preimage in `K^i / f K^i`.
    refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk y, ?_⟩
    rw [multiplicationComponent_apply_mk]
    simp [hy]
  · rintro ⟨q, rfl⟩
    -- Any `f`-multiple dies after the further reduction modulo `f`.
    refine LinearMap.mem_ker.mpr ?_
    refine Quotient.inductionOn' q ?_
    intro x
    change
      (reductionComponent f K i).hom
          ((multiplicationComponent f K i).hom (Submodule.Quotient.mk x)) = 0
    rw [multiplicationComponent_apply_mk, reductionComponent_apply_mk]
    simpa using quotient_mk_smul_eq_zero f x

/-- Helper for Lemma 15.96.7: in each degree the quotient row
`0 → K^i/fK^i → K^i/f²K^i → K^i/fK^i → 0` is short exact when multiplication by `f` on `K^i` is
injective. -/
private theorem degreewise_shortExact_of_termwise_regular
    (f : A) (K : ModuleComplex A) (i : ℤ) (hreg : IsSMulRegular (K.X i) f) :
    (degreeShortComplex f K i).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · let S : ShortComplex (ModuleCat A) := degreeShortComplex f K i
    -- Route correction: the middle exactness is now proved directly on quotient representatives,
    -- so the short-exact packaging reduces to the standard `range = ker` criterion.
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    simpa [S, degreeShortComplex] using
      (quotient_row_exact_at_middle f K i).symm
  · refine (ModuleCat.mono_iff_injective _).2 ?_
    intro q₁ q₂ hq
    have hmul_zero :
        ∀ q : (modFComplex f K).X i,
          (multiplicationComponent f K i).hom q = 0 → q = 0 := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro x hx
      -- If `f • x` vanishes modulo `f²`, then `f • x = f • (f • y)` for some `y`; cancel one
      -- factor of `f` using regularity in degree `i`.
      change
        (multiplicationComponent f K i).hom (Submodule.Quotient.mk x) = 0 at hx
      rw [multiplicationComponent_apply_mk] at hx
      have hx_mem :
          f • x ∈ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)) := by
        exact
          (Submodule.Quotient.mk_eq_zero
            (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))).1 hx
      obtain ⟨y, hy⟩ :=
        exists_smul_eq_of_mem_principalIdeal_smul_top
          (A := A) (M := K.X i) (f := f ^ 2) hx_mem
      have hcancel :
          f • x = f • (f • y) := by
        simpa [pow_two, smul_smul, mul_assoc] using hy.symm
      have hx_eq : x = f • y := (show Function.Injective (fun z : K.X i ↦ f • z) from hreg) hcancel
      rw [hx_eq]
      exact quotient_mk_smul_eq_zero f y
    apply sub_eq_zero.mp
    exact hmul_zero (q₁ - q₂) <| by
      calc
        (multiplicationComponent f K i).hom (q₁ - q₂)
            = (multiplicationComponent f K i).hom q₁
                - (multiplicationComponent f K i).hom q₂ := by
                  exact (multiplicationComponent f K i).hom.map_sub q₁ q₂
        _ = 0 := sub_eq_zero.mpr hq
  · exact (ModuleCat.epi_iff_surjective _).2 fun q ↦ by
      obtain ⟨x, rfl⟩ :=
        Submodule.mkQ_surjective
          (principalIdeal f • (⊤ : Submodule A (K.X i))) q
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      simpa using reductionComponent_apply_mk f K i x

/-- The reduction sequence
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet → 0`
is short exact when `K^\bullet` is termwise `f`-torsion free. -/
private theorem shortExact (f : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree f K) :
    (shortComplex f K).ShortExact := by
  -- Reduce short exactness of cochain complexes to the already established degreewise row.
  refine (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S := shortComplex f K)).2 ?_
  intro i
  simpa [shortComplex, degreeShortComplex] using
    degreewise_shortExact_of_termwise_regular f K i (hK.isSMulRegular i)

/-- The Berthelot-Ogus Bockstein morphism on the canonical `ModuleComplex A` owner, obtained as
the connecting morphism of
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet → 0`. -/
noncomputable abbrev bockstein
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (hK : IsTermwiseFTorsionFree f K) :
    (reduceModIdealA (principalIdeal f) K).homology i ⟶
      (reduceModIdealA (principalIdeal f) K).homology (i + 1) :=
  (shortExact f K hK).δ i (i + 1) (ComplexShape.up_mk i (i + 1) rfl)

/-- The condition that `Ker(d^i mod f²) → Ker(d^i mod f)` is surjective, expressed as the
epimorphy of the induced map on cycles on the canonical `ModuleComplex` owner. -/
abbrev cyclesReductionSurjective (f : A) (K : ModuleComplex A) (i : ℤ) : Prop :=
  Epi (cyclesMap (reductionMap f K) i)

-- Proof sketch: homology is obtained from cycles by quotienting out boundaries, so an epi on the
-- cycle objects stays epi after passing to the quotient homology objects.
/-- Helper for Lemma 15.96.7: surjectivity on reduced cycles implies surjectivity on reduced
homology. -/
private theorem epi_homology_reduction_of_epi_cycles_reduction
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [Epi (cyclesMap (reductionMap f K) i)] :
    Epi (homologyMap (reductionMap f K) i) := by
  -- The degree-`i` homology map is the short-complex homology map attached to `K.sc i`, so the
  -- standard short-complex lemma upgrades epimorphy of `cyclesMap` to epimorphy on homology.
  simpa [HomologicalComplex.homologyMap, HomologicalComplex.cyclesMap] using
    (ShortComplex.epi_homologyMap_of_epi_cyclesMap'
      ((HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℤ) i).map
        (reductionMap f K))
      (show Epi (ShortComplex.cyclesMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℤ) i).map
          (reductionMap f K))) by
        simpa [HomologicalComplex.cyclesMap] using
          (show Epi (cyclesMap (reductionMap f K) i) by infer_instance)))

/-- Helper for Lemma 15.96.7: on the owner short complex, a left-homology class vanishes exactly
when its cycle representative lies in the boundary range. -/
private theorem leftHomologyπ_eq_zero_iff_exists_boundary
    (K : ModuleComplex A) (i : ℤ) (q : K.cycles i) :
    ((K.sc i).leftHomologyπ).hom q = 0 ↔
      ∃ b : (K.sc i).X₁, (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q := by
  let S := K.sc i
  have hcomm :
      S.leftHomologyπ ≫ S.moduleCatLeftHomologyData.leftHomologyIso.hom =
        S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := by
    -- Compare the abstract left-homology quotient with the concrete module quotient on the same
    -- short complex before evaluating at the chosen cycle.
    simpa [S] using
      (ShortComplex.leftHomologyMapData (𝟙 S) S.leftHomologyData S.moduleCatLeftHomologyData).commπ
  constructor
  · intro hq
    -- Push the vanishing class through the concrete quotient comparison.
    have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (((S.leftHomologyπ).hom q)) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hπ' : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := hπ.symm
    -- Zero in the quotient is exactly membership in the boundary range.
    have hmem : S.moduleCatCyclesIso.hom q ∈ LinearMap.range S.moduleCatToCycles := by
      simpa using (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).1 hπ'
    exact LinearMap.mem_range.mp hmem
  · rintro ⟨b, hb⟩
    -- An explicit boundary witness gives zero in the concrete quotient.
    have hπ : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).2
        (LinearMap.mem_range.mpr ⟨b, hb⟩)
    -- Transport that zero back across the quotient comparison isomorphism.
    have hzero := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (((S.leftHomologyπ).hom q)) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj : Function.Injective S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.leftHomologyIso.hom).1
        inferInstance
    have h0 : 0 = S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom 0 := by
      simpa using (S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.96.7: a homology class represented by a cycle vanishes exactly when that
cycle comes from a boundary in the previous degree. -/
private theorem homologyπ_eq_zero_iff_exists_boundary
    (K : ModuleComplex A) (i : ℤ) (q : K.cycles i) :
    (K.homologyπ i).hom q = 0 ↔
      ∃ b : (K.sc i).X₁, (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q := by
  -- Rewrite the abstract homology quotient through the owner short-complex left homology, then
  -- appeal to the explicit quotient model established above.
  rw [HomologicalComplex.homologyπ, ShortComplex.homologyπ]
  constructor
  · intro hq
    -- Since `leftHomologyIso` is an isomorphism, vanishing after transport implies vanishing
    -- before transport.
    have hleft : ((K.sc i).leftHomologyπ).hom q = 0 := by
      have hinj : Function.Injective ((K.sc i).leftHomologyIso.hom).hom :=
        (ModuleCat.mono_iff_injective ((K.sc i).leftHomologyIso.hom)).1 inferInstance
      apply hinj
      simpa using hq
    exact (leftHomologyπ_eq_zero_iff_exists_boundary K i q).1 hleft
  · intro hq
    -- Conversely, a boundary witness kills the left-homology class, hence also the transported
    -- homology class.
    have hleft : ((K.sc i).leftHomologyπ).hom q = 0 :=
      (leftHomologyπ_eq_zero_iff_exists_boundary K i q).2 hq
    change ((K.sc i).leftHomologyIso.hom).hom (((K.sc i).leftHomologyπ).hom q) = 0
    rw [hleft]
    simp

/-- Helper for Lemma 15.96.7: transporting a cycle through `moduleCatCyclesIso.hom` forgets to
the same ambient element as the canonical inclusion `iCycles`. -/
private theorem moduleCatCyclesIso_hom_iCycles
    (S : ShortComplex (ModuleCat A)) (z : S.cycles) :
    (S.moduleCatCyclesIso.hom z).1 = S.iCycles.hom z := by
  -- The categorical cycles object is definitionally the kernel used by
  -- `moduleCatCyclesIso`, so both sides forget to the same ambient element.
  rfl

/-- Helper for Lemma 15.96.7: transporting a concrete kernel element back through
`moduleCatCyclesIso.inv` forgets to its original ambient representative. -/
private theorem moduleCatCyclesIso_inv_iCycles
    (S : ShortComplex (ModuleCat A)) (u : LinearMap.ker S.g.hom) :
    S.iCycles.hom (S.moduleCatCyclesIso.inv.hom u) = u.1 := by
  -- Compare the transported cycle with `u` after pushing it forward again through
  -- `moduleCatCyclesIso.hom`.
  calc
    S.iCycles.hom (S.moduleCatCyclesIso.inv.hom u) =
        (S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv.hom u)).1 := by
          symm
          exact moduleCatCyclesIso_hom_iCycles
            (S := S) (z := S.moduleCatCyclesIso.inv.hom u)
    _ = u.1 := by
          simpa using congrArg Subtype.val (S.moduleCatCyclesIso.inv_hom_id_apply u)

/-- Helper for Lemma 15.96.7: the categorical boundary map `toCycles` becomes the concrete
kernel-level map `moduleCatToCycles` after passing through `moduleCatCyclesIso.hom`. -/
private theorem moduleCatCyclesIso_hom_toCycles
    (S : ShortComplex (ModuleCat A)) (b : S.X₁) :
    S.moduleCatCyclesIso.hom (S.toCycles.hom b) = S.moduleCatToCycles b := by
  -- Compare both kernel elements through their ambient values in `S.X₂`; `toCycles_i`
  -- rewrites the categorical boundary to the short-complex source map.
  apply Subtype.ext
  change S.iCycles.hom (S.toCycles.hom b) = (S.moduleCatToCycles b).1
  have hto :
      S.iCycles.hom (S.toCycles.hom b) = S.f.hom b := by
    have hto' :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_i S)) b
    change ((S.toCycles ≫ S.iCycles).hom b) = S.f.hom b at hto'
    exact hto'
  simpa [ShortComplex.moduleCatToCycles] using hto

/-- Helper for Lemma 15.96.7: every class modulo `f` lifts along the reduction map
`K/f²K → K/fK`. -/
private theorem reductionComponent_surjective
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K) (i : ℤ) :
    Function.Surjective (reductionComponent f K i).hom := by
  let S : ShortComplex (ModuleCat A) := degreeShortComplex f K i
  have hS : S.ShortExact := by
    -- The degreewise quotient row is already short exact by termwise `f`-regularity.
    simpa [S, degreeShortComplex] using
      degreewise_shortExact_of_termwise_regular f K i (hK.isSMulRegular i)
  letI : Epi S.g := hS.epi_g
  -- Surjectivity is the module-category form of the epimorphism on the right-hand quotient map.
  simpa [S, degreeShortComplex] using
    (ModuleCat.epi_iff_surjective S.g).1 inferInstance

/-- Helper for Lemma 15.96.7: after applying `moduleCatCyclesIso.hom`, the image of a lifted
boundary under a cycles map is the concrete boundary induced on degree `i - 1` terms. -/
private theorem cyclesMap_toCycles_moduleCatToCycles
    {S₁ S₂ : ShortComplex (ModuleCat A)} (φ : S₁ ⟶ S₂) (b : S₁.X₁) :
    S₂.moduleCatCyclesIso.hom (((ShortComplex.cyclesMap φ).hom) (S₁.toCycles.hom b)) =
      S₂.moduleCatToCycles (φ.τ₁.hom b) := by
  -- Naturality of `toCycles` rewrites the categorical cycle map of a boundary to the target
  -- boundary, and `moduleCatCyclesIso_hom_toCycles` identifies that target boundary concretely.
  have hnat := congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_naturality φ)
  have hnat' := LinearMap.congr_fun hnat b
  calc
    S₂.moduleCatCyclesIso.hom (((ShortComplex.cyclesMap φ).hom) (S₁.toCycles.hom b)) =
        S₂.moduleCatCyclesIso.hom (S₂.toCycles.hom (φ.τ₁.hom b)) := by
          exact congrArg S₂.moduleCatCyclesIso.hom hnat'
    _ = S₂.moduleCatToCycles (φ.τ₁.hom b) :=
          moduleCatCyclesIso_hom_toCycles S₂ (φ.τ₁.hom b)

/-- Helper for Lemma 15.96.7: a homology class in a short complex of `A`-modules vanishes exactly
when its cycle representative is a boundary. -/
private theorem shortComplex_homologyπ_eq_zero_iff_exists_boundary
    (S : ShortComplex (ModuleCat A)) [S.HasHomology] (q : S.cycles) :
    S.homologyπ.hom q = 0 ↔
      ∃ b : S.X₁, S.moduleCatToCycles b = S.moduleCatCyclesIso.hom q := by
  have hcomm :
      S.homologyπ ≫ S.moduleCatHomologyIso.hom =
        S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := by
    simpa using S.π_moduleCatCyclesIso_hom
  constructor
  · intro hq
    -- Move to the concrete quotient of the kernel, where zero means lying in the boundary range.
    have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hπ' : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := hπ.symm
    have hmem : S.moduleCatCyclesIso.hom q ∈ LinearMap.range S.moduleCatToCycles := by
      simpa using (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).1 hπ'
    exact LinearMap.mem_range.mp hmem
  · rintro ⟨b, hb⟩
    -- An explicit boundary witness is zero in the concrete quotient, hence also in homology.
    have hπ : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).2
        (LinearMap.mem_range.mpr ⟨b, hb⟩)
    have hzero := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).1 inferInstance
    have h0 : 0 = S.moduleCatHomologyIso.hom.hom 0 := by
      simpa using (S.moduleCatHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.96.7: the predecessor degree in `K.sc (i + 1)` is exactly `i`. -/
private theorem shortComplex_prev_degree_transport (i : ℤ) :
    (ComplexShape.up ℤ).prev (i + 1) = i := by
  -- For the cochain shape on `ℤ`, the predecessor chosen for `i + 1` is the evident one.
  classical
  simp [ComplexShape.prev, ComplexShape.up, ComplexShape.up']

/-- Helper for Lemma 15.96.7: the successor degree in `K.sc i` is exactly `i + 1`. -/
private theorem shortComplex_next_degree_transport (i : ℤ) :
    (ComplexShape.up ℤ).next i = i + 1 := by
  -- For the cochain shape on `ℤ`, the successor chosen for `i` is the evident one.
  classical
  simp [ComplexShape.next, ComplexShape.up, ComplexShape.up']

/-- Helper for Lemma 15.96.7: after identifying the predecessor degree `j` with `i`, a boundary
witness in degree `j` can be viewed as a boundary witness in degree `i`. -/
private theorem prev_boundary_witness_cast
    (K : ModuleComplex A) {i j : ℤ} (hj' : j = i)
    {bPrev : K.X j} {t : K.X (i + 1)}
    (hb_prev : (K.d j (i + 1)).hom bPrev = t)
    (hji : ↥(K.X j) = ↥(K.X i)) :
    (K.d i (i + 1)).hom (cast hji bPrev) = t := by
  -- Eliminate the index equality so both the differential and the cast become definitional.
  subst hj'
  cases hji
  simpa using hb_prev

/-- Helper for Lemma 15.96.7: a degree-`j` homology class vanishes exactly when its cycle comes
from the previous differential. -/
private theorem homologyπ_eq_zero_iff_exists_prev_boundary
    (K : ModuleComplex A) (j : ℤ) (q : K.cycles j) :
    (K.homologyπ j).hom q = 0 ↔
      ∃ b : K.X ((ComplexShape.up ℤ).prev j),
        (K.d ((ComplexShape.up ℤ).prev j) j).hom b = (K.iCycles j).hom q := by
  -- Repackage the short-complex boundary criterion using the ambient predecessor degree.
  rw [homologyπ_eq_zero_iff_exists_boundary]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    exact congrArg Subtype.val (by simpa [moduleCatCyclesIso_hom_iCycles] using hb)
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    exact Subtype.ext hb

/-- Helper for Lemma 15.96.7: the reduced short-complex differential `g` sends the class of `x`
to the class of the original differential in the chosen successor degree. -/
private theorem reduced_short_complex_g_apply_mk
    (I : Ideal A) (K : ModuleComplex A) (i : ℤ) (x : K.X i) :
    let j : ℤ := (ComplexShape.up ℤ).next i
    (((CochainComplex.reduceModIdealA I K).sc i).g).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((K.d i j).hom x) :
        K.X j ⧸ I • (⊤ : Submodule A (K.X j))) := by
  dsimp
  -- `sc i` uses the outgoing differential to `next i`, so after rewriting that successor as
  -- `i + 1` the claim is exactly the quotient-differential formula on representatives.
  change
    ((CochainComplex.reduceModIdealA I K).d i ((ComplexShape.up ℤ).next i)).hom
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((K.d i ((ComplexShape.up ℤ).next i)).hom x) :
        K.X ((ComplexShape.up ℤ).next i) ⧸
          I • (⊤ : Submodule A (K.X ((ComplexShape.up ℤ).next i))))
  rw [shortComplex_next_degree_transport (i := i)]
  -- The remaining statement is the cached description of the reduced adjacent differential.
  rw [reduceModIdealA_d_eq]
  exact reduceModIdealADifferential_apply_mk (I := I) (K := K) (i := i) x

/-- Helper for Lemma 15.96.7: an ambient element in degree `i + 1` whose next differential
vanishes packages canonically as a cycle in degree `i + 1`. -/
private theorem exists_cycle_of_d_next_eq_zero
    (K : ModuleComplex A) (i : ℤ) {y : K.X (i + 1)}
    (hy : (K.d (i + 1) ((i + 1) + 1)).hom y = 0) :
    ∃ q : K.cycles (i + 1), (K.iCycles (i + 1)).hom q = y := by
  -- Package `y` as a kernel element for the owner short complex in degree `i + 1`.
  let u : LinearMap.ker (((K.sc (i + 1)).g).hom) := by
    refine ⟨y, ?_⟩
    change (K.d (i + 1) ((ComplexShape.up ℤ).next (i + 1))).hom y = 0
    rw [shortComplex_next_degree_transport (i := i + 1)]
    exact hy
  refine ⟨(K.sc (i + 1)).moduleCatCyclesIso.inv.hom u, ?_⟩
  -- The inverse cycle isomorphism was built from the same kernel object, so forgetting it gives
  -- back the original representative `y`.
  simpa [u] using
    moduleCatCyclesIso_inv_iCycles (S := K.sc (i + 1)) (u := u)

/-- Helper for Lemma 15.96.7: for a morphism of short complexes of `A`-modules, surjectivity on
homology together with surjectivity on the left term lifts every target cycle. -/
private theorem epi_cyclesMap_of_epi_homologyMap_of_surjective_left
    {S₁ S₂ : ShortComplex (ModuleCat A)} [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) [Epi (ShortComplex.homologyMap φ)]
    (hτ₁ : Function.Surjective φ.τ₁.hom) :
    Epi (ShortComplex.cyclesMap φ) := by
  -- Work elementwise in `ModuleCat`: first lift the target homology class, then correct the
  -- resulting cycle by a lifted boundary coming from the left term.
  refine (ModuleCat.epi_iff_surjective _).2 ?_
  intro z
  have hhom_surj :
      Function.Surjective (ShortComplex.homologyMap φ).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨hz, hhz⟩ := hhom_surj (S₂.homologyπ.hom z)
  have hπ_surj : Function.Surjective S₁.homologyπ.hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hπ_surj hz
  let r : S₂.cycles := (ShortComplex.cyclesMap φ).hom x - z
  have hr_zero : S₂.homologyπ.hom r = 0 := by
    -- Naturality of the quotient map shows that the residual cycle is homologically trivial.
    calc
      S₂.homologyπ.hom r
          = S₂.homologyπ.hom ((ShortComplex.cyclesMap φ).hom x) - S₂.homologyπ.hom z := by
              rw [map_sub]
      _ = (ShortComplex.homologyMap φ).hom (S₁.homologyπ.hom x) - S₂.homologyπ.hom z := by
            have hnat :
                (ShortComplex.homologyMap φ).hom (S₁.homologyπ.hom x) =
                  S₂.homologyπ.hom ((ShortComplex.cyclesMap φ).hom x) := by
              exact LinearMap.congr_fun
                (ModuleCat.hom_ext_iff.mp (ShortComplex.homologyπ_naturality φ)) x
            rw [hnat.symm]
      _ = 0 := by simpa [hx] using sub_eq_zero.mpr hhz
  obtain ⟨b, hb⟩ := (shortComplex_homologyπ_eq_zero_iff_exists_boundary S₂ r).1 hr_zero
  obtain ⟨a, ha⟩ := hτ₁ b
  refine ⟨x - S₁.toCycles.hom a, ?_⟩
  -- After subtracting the lifted boundary, the residual cycle disappears.
  have hinj : Function.Injective S₂.moduleCatCyclesIso.hom.hom :=
    (ModuleCat.mono_iff_injective S₂.moduleCatCyclesIso.hom).1 inferInstance
  let kb : S₂.moduleCatLeftHomologyData.K := S₂.moduleCatToCycles b
  have hkb : kb = S₂.moduleCatCyclesIso.hom r := by
    simpa [kb] using hb
  have hb_cycle : S₂.toCycles.hom b = r := by
    apply hinj
    calc
      S₂.moduleCatCyclesIso.hom (S₂.toCycles.hom b) = kb := by
        simpa [kb] using moduleCatCyclesIso_hom_toCycles S₂ b
      _ = S₂.moduleCatCyclesIso.hom r := hkb
  have hcorr : (ShortComplex.cyclesMap φ).hom (S₁.toCycles.hom a) = r := by
    have hnat :
        (ShortComplex.cyclesMap φ).hom (S₁.toCycles.hom a) =
          S₂.toCycles.hom (φ.τ₁.hom a) := by
      exact LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp (ShortComplex.toCycles_naturality φ)) a
    calc
      (ShortComplex.cyclesMap φ).hom (S₁.toCycles.hom a)
          = S₂.toCycles.hom (φ.τ₁.hom a) := hnat
      _ = S₂.toCycles.hom b := by rw [ha]
      _ = r := hb_cycle
  calc
    (ShortComplex.cyclesMap φ).hom (x - S₁.toCycles.hom a)
        = (ShortComplex.cyclesMap φ).hom x -
            (ShortComplex.cyclesMap φ).hom (S₁.toCycles.hom a) := by
              rw [map_sub]
    _ = (ShortComplex.cyclesMap φ).hom x - r := by rw [hcorr]
    _ = z := by
          dsimp [r]
          abel

-- Proof sketch: identify the owner-level Berthelot-Ogus `β` with the connecting morphism of the
-- canonical short exact sequence above and apply exactness of the long exact homology sequence.
/-- Owner-level form of Lemma `15.96.7`: surjectivity of
`Ker(d^i mod f²) → Ker(d^i mod f)` is equivalent to vanishing of the canonical Bockstein
morphism. -/
theorem cyclesReductionSurjective_iff_bockstein_eq_zero
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K)
    (i : ℤ) :
    cyclesReductionSurjective f K i ↔ bockstein f K i hK = 0 := by
  let S : ShortComplex (ModuleComplex A) := shortComplex f K
  have hS : S.ShortExact := by
    -- Freeze the canonical quotient row once so both directions can reuse the same exactness API.
    simpa [S] using shortExact f K hK
  constructor
  · intro hcycles
    letI : Epi (cyclesMap (reductionMap f K) i) := hcycles
    -- The long exact sequence identifies vanishing of the connecting morphism with surjectivity
    -- on homology once the cycle-level epi has been descended to homology.
    rw [← (hS.homology_exact₃ i (i + 1) (by simp)).epi_f_iff]
    simpa [S] using
      (epi_homology_reduction_of_epi_cycles_reduction (f := f) (K := K) (i := i))
  · intro hbockstein
    -- Route correction: the reverse implication has to follow the source's boundary-correction
    -- argument on cycles, rather than asking exactness on homology to prove cycle surjectivity
    -- directly.
    let φ :=
      ((HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℤ) i).map
        (reductionMap f K))
    haveI : Epi (homologyMap (reductionMap f K) i) := by
      -- Exactness of the long exact homology sequence identifies vanishing of `β` with
      -- epimorphy of the reduction on homology.
      exact ((hS.homology_exact₃ i (i + 1) (by simp)).epi_f_iff).2 <| by
        simpa [S, bockstein] using hbockstein
    haveI : Epi (ShortComplex.homologyMap φ) := by
      simpa [φ, HomologicalComplex.homologyMap] using
        (show Epi (homologyMap (reductionMap f K) i) by infer_instance)
    have hτ₁ : Function.Surjective φ.τ₁.hom := by
      -- The previous-degree term of the reduction map is already surjective degreewise.
      change Function.Surjective (reductionComponent f K ((ComplexShape.up ℤ).prev i)).hom
      simpa [φ, HomologicalComplex.shortComplexFunctor, reductionMap] using
        reductionComponent_surjective f K hK ((ComplexShape.up ℤ).prev i)
    letI : Epi (ShortComplex.cyclesMap φ) :=
      epi_cyclesMap_of_epi_homologyMap_of_surjective_left φ hτ₁
    simpa [φ, HomologicalComplex.cyclesMap] using
      (show Epi (ShortComplex.cyclesMap φ) by infer_instance)

-- Proof sketch: the factorization from `15.96.5.1` shows that the owner-level Bockstein factors
-- through the `f`-torsion in homology.
/-- Helper for Lemma 15.96.7: if `d x = f • y`, then `y` is a cycle in the next degree. -/
private theorem d_next_eq_zero_of_d_eq_smul
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K) (i : ℤ)
    {x : K.X i} {y : K.X (i + 1)}
    (hxy : (K.d i (i + 1)).hom x = f • y) :
    (K.d (i + 1) ((i + 1) + 1)).hom y = 0 := by
  -- Apply `d ∘ d = 0` to `x`, rewrite the result as `f • d y = 0`, and cancel one factor of `f`.
  have hdd :
      (K.d (i + 1) ((i + 1) + 1)).hom ((K.d i (i + 1)).hom x) = 0 := by
    exact
      LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp (K.d_comp_d i (i + 1) ((i + 1) + 1))) x
  rw [hxy, LinearMap.map_smul] at hdd
  have hinj : Function.Injective (fun z : K.X ((i + 1) + 1) ↦ f • z) :=
    hK.isSMulRegular ((i + 1) + 1)
  exact hinj (by simpa using hdd)

/-- Helper for Lemma 15.96.7: if `d x = f • y` with `y` a cycle in degree `i + 1`, then the
homology class of `y` is annihilated by `f`. -/
private theorem homology_class_mem_torsionBy_of_d_eq_smul
    (f : A) (K : ModuleComplex A) (i : ℤ)
    {x : K.X i} {q : K.cycles (i + 1)}
    (hqx : (K.d i (i + 1)).hom x = f • (K.iCycles (i + 1)).hom q) :
    (K.homologyπ (i + 1)).hom q ∈ Submodule.torsionBy A (K.homology (i + 1)) f := by
  -- The cycle `f • q` is already a boundary, so its homology class vanishes.
  have hboundary :
      ∃ b : K.X ((ComplexShape.up ℤ).prev (i + 1)),
        (K.d ((ComplexShape.up ℤ).prev (i + 1)) (i + 1)).hom b =
          (K.iCycles (i + 1)).hom (f • q) := by
    rw [shortComplex_prev_degree_transport (i := i)]
    refine ⟨x, ?_⟩
    simpa using hqx
  have hzero :
      (K.homologyπ (i + 1)).hom (f • q) = 0 :=
    (homologyπ_eq_zero_iff_exists_prev_boundary K (i + 1) (f • q)).2 hboundary
  -- Membership in `torsionBy` says exactly that multiplying the class by `f` kills it.
  rw [Submodule.mem_torsionBy_iff]
  simpa [LinearMap.map_smul] using hzero

/-- Helper for Lemma 15.96.7: a representative of a reduced cycle has differential divisible by
`f`. -/
private theorem d_representative_mem_f_smul_of_reduced_cycle
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (z : (modFComplex f K).cycles i) {x : K.X i}
    (hx :
      (Submodule.Quotient.mk x :
        K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) =
        ((modFComplex f K).iCycles i).hom z) :
    (K.d i (i + 1)).hom x ∈
      principalIdeal f • (⊤ : Submodule A (K.X (i + 1))) := by
  -- Rewrite the cycle condition for `z` on the chosen representative `x`.
  have hz :
      ((modFComplex f K).d i (i + 1)).hom (((modFComplex f K).iCycles i).hom z) = 0 := by
    exact LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom ((modFComplex f K).iCycles_d i (i + 1))) z
  rw [← hx] at hz
  rw [reduceModIdealA_d_eq] at hz
  have hz' :
      (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
        K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) = 0 := by
    calc
      (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
          K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1))))
          = (CochainComplex.reduceModIdealADifferential (principalIdeal f) K i).hom
              (Submodule.Quotient.mk x) := by
                symm
                exact reduceModIdealADifferential_apply_mk
                  (I := principalIdeal f) (K := K) (i := i) x
      _ = 0 := hz
  exact
    (Submodule.Quotient.mk_eq_zero
      (principalIdeal f • (⊤ : Submodule A (K.X (i + 1))))).1 hz'

/-- Helper for Lemma 15.96.7: the differential of a representative of a reduced cycle is an
explicit `f`-multiple. -/
private theorem exists_d_eq_smul_of_reduced_cycle_representative
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (z : (modFComplex f K).cycles i) {x : K.X i}
    (hx :
      (Submodule.Quotient.mk x :
        K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) =
        ((modFComplex f K).iCycles i).hom z) :
    ∃ y : K.X (i + 1), (K.d i (i + 1)).hom x = f • y := by
  -- Convert divisibility-by-`f` membership into an explicit witness.
  obtain ⟨y, hy⟩ :=
    exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (M := K.X (i + 1)) f
      (d_representative_mem_f_smul_of_reduced_cycle f K i z hx)
  exact ⟨y, hy.symm⟩

/-- Helper for Lemma 15.96.7: after forgetting to ambient degree `i`, the cycles map induced by
`K/f²K → K/fK` is the termwise reduction map. -/
private theorem cyclesMap_reduction_iCycles
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (z' : (modFSquaredComplex f K).cycles i) :
    ((modFComplex f K).iCycles i).hom ((cyclesMap (reductionMap f K) i).hom z') =
      (reductionComponent f K i).hom (((modFSquaredComplex f K).iCycles i).hom z') := by
  let φ :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℤ) i).map
      (reductionMap f K)
  -- Evaluate the standard naturality square for `ShortComplex.cyclesMap`.
  exact congrArg
    (fun g : (modFSquaredComplex f K).cycles i ⟶ (modFComplex f K).X i ↦ g.hom z')
    (by
      simpa [φ, HomologicalComplex.shortComplexFunctor, HomologicalComplex.cyclesMap,
        reductionMap] using
        (ShortComplex.cyclesMap_i φ))

/-- Helper for Lemma 15.96.7: correcting a representative by `f • b` produces a cycle modulo
`f²`. -/
private theorem corrected_representative_cycle_condition
    (f : A) (K : ModuleComplex A) (i : ℤ)
    {x b : K.X i} {y : K.X (i + 1)}
    (hxy : (K.d i (i + 1)).hom x = f • y)
    (hb : (K.d i (i + 1)).hom b = y) :
    (((modFSquaredComplex f K).sc i).g).hom
        (Submodule.Quotient.mk (x - f • b)) = 0 := by
  -- Normalize the short-complex differential to the adjacent reduced differential on
  -- representatives before doing the linear algebra computation.
  change
    ((modFSquaredComplex f K).d i ((ComplexShape.up ℤ).next i)).hom
        (Submodule.Quotient.mk (x - f • b)) = 0
  rw [shortComplex_next_degree_transport (i := i), reduceModIdealA_d_eq]
  calc
    (CochainComplex.reduceModIdealADifferential (principalIdeal (f ^ 2)) K i).hom
        (Submodule.Quotient.mk (x - f • b)) =
      (Submodule.Quotient.mk ((K.d i (i + 1)).hom (x - f • b)) :
        K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) := by
          exact reduceModIdealADifferential_apply_mk
            (I := principalIdeal (f ^ 2)) (K := K) (i := i) (x := x - f • b)
    _ = (Submodule.Quotient.mk
          ((K.d i (i + 1)).hom x - f • (K.d i (i + 1)).hom b) :
            K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) := by
          rw [LinearMap.map_sub, LinearMap.map_smul]
    _ = (Submodule.Quotient.mk (f • y - f • y) :
          K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) := by
          rw [hxy, hb]
    _ = 0 := by simp

/-- If `H^{i+1}(K^\bullet)[f] = 0`, then the owner-level cycles map
`Ker(d^i mod f²) → Ker(d^i mod f)` is surjective. -/
theorem cyclesReductionSurjective_of_homology_f_torsion_eq_bot
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K)
    (i : ℤ) (hH : Submodule.torsionBy A (K.homology (i + 1)) f = ⊥) :
    cyclesReductionSurjective f K i := by
  -- Route correction: follow the source proof on representatives instead of asking exactness to
  -- produce the lifting abstractly.
  refine (ModuleCat.epi_iff_surjective _).2 ?_
  intro z
  -- Choose an ambient representative `x` of the target reduced cycle.
  obtain ⟨x, hx⟩ :=
    Submodule.mkQ_surjective
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (((modFComplex f K).iCycles i).hom z)
  -- The reduced cycle condition says `d x` is divisible by `f`.
  obtain ⟨y, hxy⟩ :=
    exists_d_eq_smul_of_reduced_cycle_representative f K i z hx
  have hy_zero : (K.d (i + 1) ((i + 1) + 1)).hom y = 0 :=
    d_next_eq_zero_of_d_eq_smul f K hK i hxy
  -- Package the correction term `y` itself as a cycle in degree `i + 1`.
  obtain ⟨q, hq⟩ := exists_cycle_of_d_next_eq_zero K i hy_zero
  have hqx :
      (K.d i (i + 1)).hom x = f • (K.iCycles (i + 1)).hom q := by
    simpa [hq] using hxy
  -- The homology class of `q` is killed by `f`, hence vanishes by the torsion hypothesis.
  have htors :
      (K.homologyπ (i + 1)).hom q ∈
        Submodule.torsionBy A (K.homology (i + 1)) f :=
    homology_class_mem_torsionBy_of_d_eq_smul f K i hqx
  have hq_zero : (K.homologyπ (i + 1)).hom q = 0 := by
    rw [hH] at htors
    simpa using htors
  -- Vanishing of the class produces the boundary witness `b` with `d b = y`.
  set j : ℤ := (ComplexShape.up ℤ).prev (i + 1) with hj
  obtain ⟨bPrev, hb_prev⟩ :
      ∃ b : K.X j, (K.d j (i + 1)).hom b = (K.iCycles (i + 1)).hom q := by
    simpa [hj] using (homologyπ_eq_zero_iff_exists_prev_boundary K (i + 1) q).1 hq_zero
  -- Rewrite the predecessor index through the named variable `j`, then substitute `j = i`.
  have hj' : j = i := by
    simpa [hj] using shortComplex_prev_degree_transport (i := i)
  have hji : ↥(K.X j) = ↥(K.X i) := by
    simpa using congrArg (fun t ↦ ↥(K.X t)) hj'
  let b : K.X i := cast hji bPrev
  have hb_q :
      (K.d i (i + 1)).hom b = (K.iCycles (i + 1)).hom q := by
    -- Transport the predecessor witness from the named degree `j` back to the concrete degree `i`.
    simpa [b] using prev_boundary_witness_cast
      (K := K) (i := i) (j := j) hj' hb_prev hji
  have hb : (K.d i (i + 1)).hom b = y := by
    calc
      (K.d i (i + 1)).hom b = (K.iCycles (i + 1)).hom q := hb_q
      _ = y := hq
  -- The corrected representative `x - f • b` is now a genuine cycle modulo `f²`.
  let u : LinearMap.ker (((modFSquaredComplex f K).sc i).g).hom :=
    ⟨Submodule.Quotient.mk (x - f • b),
      corrected_representative_cycle_condition f K i hxy hb⟩
  let z' : (modFSquaredComplex f K).cycles i :=
    ((modFSquaredComplex f K).sc i).moduleCatCyclesIso.inv.hom u
  refine ⟨z', ?_⟩
  -- Compare the lifted cycle with `z` after applying the injective inclusion into ambient degree
  -- `i`.
  apply (ModuleCat.mono_iff_injective ((modFComplex f K).iCycles i)).1 inferInstance
  have hz'_repr :
      ((modFSquaredComplex f K).iCycles i).hom z' =
        (Submodule.Quotient.mk (x - f • b) :
          K.X i ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i))) := by
    simpa [z', u] using
      moduleCatCyclesIso_inv_iCycles
        (S := (modFSquaredComplex f K).sc i) (u := u)
  have hambient :
      ((modFComplex f K).iCycles i).hom ((cyclesMap (reductionMap f K) i).hom z') =
        (Submodule.Quotient.mk x :
          K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
    calc
    ((modFComplex f K).iCycles i).hom ((cyclesMap (reductionMap f K) i).hom z') =
        (reductionComponent f K i).hom (((modFSquaredComplex f K).iCycles i).hom z') := by
          simpa using cyclesMap_reduction_iCycles f K i z'
    _ = (reductionComponent f K i).hom
          (Submodule.Quotient.mk (x - f • b) :
            K.X i ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i))) := by
          rw [hz'_repr]
    _ = (Submodule.Quotient.mk (x - f • b) :
          K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
          rw [reductionComponent_apply_mk]
    _ = (Submodule.Quotient.mk x :
          K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
          calc
            (Submodule.Quotient.mk (x - f • b) :
                K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) =
              (Submodule.Quotient.mk x :
                K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) -
                (Submodule.Quotient.mk (f • b) :
                  K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
                    simpa using
                      (Submodule.mkQ
                        (principalIdeal f • (⊤ : Submodule A (K.X i)))).map_sub x (f • b)
            _ = (Submodule.Quotient.mk x :
                K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
                  rw [quotient_mk_smul_eq_zero]
                  simp
  exact hambient.trans hx

namespace Nat

/-- Helper for Lemma 15.96.7: quotient maps induced by ambient linear maps send a quotient
generator to the class of its image. -/
private theorem quotientByIdealTopMap_apply_mk
    (I : Ideal A) {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (φ : M →ₗ[A] N)
    (hφ : I • (⊤ : Submodule A M) ≤ Submodule.comap φ (I • (⊤ : Submodule A N)))
    (x : M) :
    (Submodule.mapQ
        (I • (⊤ : Submodule A M))
        (I • (⊤ : Submodule A N))
        φ hφ)
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (φ x) :
        N ⧸ I • (⊤ : Submodule A N)) := by
  -- The quotient map is defined by passing `φ` to representatives.
  simpa using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        (I • (⊤ : Submodule A M))
        (I • (⊤ : Submodule A N))
        φ)
      x

/-- Helper for Lemma 15.96.7: a linear equivalence of ambient modules induces an equivalence on
the quotients by `IM` and `IN`. -/
private noncomputable def quotientByIdealTopLinearEquiv
    (I : Ideal A) {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) :
    (M ⧸ I • (⊤ : Submodule A M)) ≃ₗ[A] (N ⧸ I • (⊤ : Submodule A N)) :=
  let hForward :
      I • (⊤ : Submodule A M) ≤
        Submodule.comap e.toLinearMap (I • (⊤ : Submodule A N)) := by
    -- Transport each generator of `IM` across `e`; linearity preserves visible `I`-multiples.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e y ∈ (⊤ : Submodule A N) by simp))
  let hBackward :
      I • (⊤ : Submodule A N) ≤
        Submodule.comap e.symm.toLinearMap (I • (⊤ : Submodule A M)) := by
    -- The inverse equivalence transports the quotient denominator back in the same way.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e.symm y ∈ (⊤ : Submodule A M) by simp))
  let f :
      (M ⧸ I • (⊤ : Submodule A M)) →ₗ[A] (N ⧸ I • (⊤ : Submodule A N)) :=
    Submodule.mapQ
      (I • (⊤ : Submodule A M))
      (I • (⊤ : Submodule A N))
      e.toLinearMap
      hForward
  let g :
      (N ⧸ I • (⊤ : Submodule A N)) →ₗ[A] (M ⧸ I • (⊤ : Submodule A M)) :=
    Submodule.mapQ
      (I • (⊤ : Submodule A N))
      (I • (⊤ : Submodule A M))
      e.symm.toLinearMap
      hBackward
  -- Check the two composites on quotient generators; the ambient compositions are identities.
  LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change f (g (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      rw [quotientByIdealTopMap_apply_mk (A := A) I e.symm.toLinearMap hBackward]
      rw [quotientByIdealTopMap_apply_mk (A := A) I e.toLinearMap hForward]
      simp)
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change g (f (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      rw [quotientByIdealTopMap_apply_mk (A := A) I e.toLinearMap hForward]
      rw [quotientByIdealTopMap_apply_mk (A := A) I e.symm.toLinearMap hBackward]
      simp)

/-- Helper for Lemma 15.96.7: quotient transport along a linear equivalence sends a
representative to the class of its image. -/
private theorem quotientByIdealTopLinearEquiv_apply_mk
    (I : Ideal A) {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (x : M) :
    quotientByIdealTopLinearEquiv (A := A) I e (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (e x) :
        N ⧸ I • (⊤ : Submodule A N)) := by
  -- Unfold the transport equivalence once; its forward map is the quotient map induced by `e`.
  simpa [quotientByIdealTopLinearEquiv] using
    (quotientByIdealTopMap_apply_mk (A := A) I e.toLinearMap
      (by
        rw [Submodule.smul_le]
        intro r hr y hy
        simpa using
          (Submodule.smul_mem_smul hr (show e y ∈ (⊤ : Submodule A N) by simp)))
      x)

/-- Helper for Lemma 15.96.7: in negative degree, reducing the extension-by-zero complex is
again zero. -/
private theorem reduceModIdealA_extend_source_isZero_of_neg
    (I : Ideal A) (M : NatModuleCochainComplex A) {i : ℤ} (hi : ¬ 0 ≤ i) :
    CategoryTheory.Limits.IsZero
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X i) := by
  -- The ambient extended term is zero, so its quotient remains a zero object in `ModuleCat`.
  let hzero : CategoryTheory.Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).X i) :=
    M.isZero_extend_X ComplexShape.embeddingUpNat i (by
      intro n hni
      exact hi (hni ▸ Int.natCast_nonneg n))
  letI : Subsingleton ((M.extend ComplexShape.embeddingUpNat).X i) :=
    ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X i) := by
    change Subsingleton
      (((M.extend ComplexShape.embeddingUpNat).X i) ⧸
        I • (⊤ : Submodule A ((M.extend ComplexShape.embeddingUpNat).X i)))
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.96.7: in negative degree, extension by zero of the reduced bounded-below
complex is zero. -/
private theorem reduceModIdealA_extend_target_isZero_of_neg
    (I : Ideal A) (M : NatModuleCochainComplex A) {i : ℤ} (hi : ¬ 0 ≤ i) :
    CategoryTheory.Limits.IsZero
      (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X i) := by
  -- Extension by zero kills every negative degree of the bounded-below reduced complex.
  exact
    (reduceModIdealA I M).isZero_extend_X ComplexShape.embeddingUpNat i (by
      intro n hni
      exact hi (hni ▸ Int.natCast_nonneg n))

/-- Helper for Lemma 15.96.7: after applying the successor-degree `extendXIso`, the extended
differential of a bounded-below complex becomes the original differential in consecutive
nonnegative degrees. -/
private theorem extendXIso_d_apply
    (M : NatModuleCochainComplex A) (n : ℕ)
    (x : (M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :
    ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).toLinearEquiv)
        (((M.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x) =
      (M.d n (n + 1)).hom
        (((M.extendXIso ComplexShape.embeddingUpNat
            (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv) x) := by
  let e0 := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  let e1 := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).toLinearEquiv
  -- Rewrite the extended differential once using `extend_d_eq`, then cancel the successor-degree
  -- identification by applying `e1`.
  have hd :=
    congrArg ModuleCat.Hom.hom
      (HomologicalComplex.extend_d_eq
        (K := M) (e := ComplexShape.embeddingUpNat)
        (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ))
        (i := n) (j := n + 1) (by simp : ((n : ℕ) : ℤ) = (n : ℤ))
        (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1))
  have hd' := LinearMap.congr_fun hd x
  rw [hd']
  change e1 (e1.symm ((M.d n (n + 1)).hom (e0 x))) =
      (M.d n (n + 1)).hom (e0 x)
  simp

/-- Helper for Lemma 15.96.7: in nonnegative degree, reducing after extension by zero agrees with
extension by zero of the reduced bounded-below complex. -/
private noncomputable def reduceModIdealA_extendComponentIso_nonneg
    (I : Ideal A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X (n : ℤ) ≅
      ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X (n : ℤ) :=
  let eSource :
      ((M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) ≃ₗ[A] M.X n :=
    (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv
  let eTarget :
      (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X (n : ℤ)) ≃ₗ[A]
        (reduceModIdealA I M).X n :=
    ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv
  let e :
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X (n : ℤ)) ≃ₗ[A]
        (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X (n : ℤ)) :=
    (quotientByIdealTopLinearEquiv (A := A) I eSource).trans eTarget.symm
  -- Route correction: first transport the ambient quotient along `extendXIso`, then cancel the
  -- target extension wrapper by the inverse reduced `extendXIso`.
  { hom := ModuleCat.ofHom e.toLinearMap
    inv := ModuleCat.ofHom e.symm.toLinearMap
    hom_inv_id := by
      apply ModuleCat.hom_ext
      ext x
      change e.symm (e x) = x
      exact e.left_inv x
    inv_hom_id := by
      apply ModuleCat.hom_ext
      ext x
      change e (e.symm x) = x
      exact e.right_inv x }

/-- Helper for Lemma 15.96.7: on a quotient generator, the nonnegative comparison isomorphism is
the quotient transport induced by the source `extendXIso`, followed by the inverse reduced
`extendXIso`. -/
private theorem reduceModIdealA_extendComponentIso_nonneg_hom_apply_mk
    (I : Ideal A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : (M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :
    ((reduceModIdealA_extendComponentIso_nonneg (A := A) I M n).hom).hom
        (Submodule.Quotient.mk x) =
      (((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).inv.hom)
        (Submodule.Quotient.mk
          (((M.extendXIso ComplexShape.embeddingUpNat
              (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv) x)) := by
  let eSource :
      ((M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) ≃ₗ[A] M.X n :=
    (M.extendXIso ComplexShape.embeddingUpNat
      (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  let eTarget :
      (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X (n : ℤ)) ≃ₗ[A]
        (reduceModIdealA I M).X n :=
    ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
      (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  -- Unfold the transport isomorphism once: it is the quotient map induced by the source
  -- `extendXIso`, followed by cancellation of the target extension wrapper.
  change
    ((quotientByIdealTopLinearEquiv (A := A) I eSource).trans eTarget.symm)
        (Submodule.Quotient.mk x) =
      eTarget.symm (Submodule.Quotient.mk (eSource x))
  rw [LinearEquiv.trans_apply, quotientByIdealTopLinearEquiv_apply_mk]
  rfl

/-- Helper for Lemma 15.96.7: in negative degree, both comparison terms are zero objects. -/
private noncomputable def reduceModIdealA_extendComponentIso_neg
    (I : Ideal A) (M : NatModuleCochainComplex A) {i : ℤ} (hi : ¬ 0 ≤ i) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X i ≅
      ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X i :=
  letI :
      Subsingleton ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X i) :=
    ModuleCat.subsingleton_of_isZero
      (reduceModIdealA_extend_source_isZero_of_neg (A := A) I M hi)
  letI :
      Subsingleton (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X i) :=
    ModuleCat.subsingleton_of_isZero
      (reduceModIdealA_extend_target_isZero_of_neg (A := A) I M hi)
  -- In negative degree both terms are zero objects, so the unique maps are inverse.
  { hom := 0
    inv := 0
    hom_inv_id := by
      ext x
      exact Subsingleton.elim _ _
    inv_hom_id := by
      ext x
      exact Subsingleton.elim _ _ }

/-- Helper for Lemma 15.96.7: choose the degreewise comparison according to whether the degree is
nonnegative or negative. -/
private noncomputable def reduceModIdealA_extendComponentIso
    (I : Ideal A) (M : NatModuleCochainComplex A) (i : ℤ) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X i ≅
      ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X i := by
  by_cases hi : 0 ≤ i
  · let n : ℕ := i.toNat
    have hn : (n : ℤ) = i := Int.toNat_of_nonneg hi
    -- In nonnegative degree the comparison is the quotient transport built from `extendXIso`.
    simpa [n, hn] using
      (reduceModIdealA_extendComponentIso_nonneg (A := A) I M n)
  · -- In negative degree both source and target reduce to zero objects.
    exact reduceModIdealA_extendComponentIso_neg (A := A) I M hi

/-- Helper for Lemma 15.96.7: in nonnegative degrees, the quotient transport of `extendXIso`
commutes with the reduced differential. -/
private theorem reduceModIdealA_extendComponentIso_nonneg_comm_apply_mk
    (I : Ideal A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : (M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :
    (((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M n).hom ≫
            ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).d
              (n : ℤ) ((n + 1 : ℕ) : ℤ)) ≫
          ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
            (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).hom).hom)
        (Submodule.Quotient.mk x)) =
      (((((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d
              (n : ℤ) ((n + 1 : ℕ) : ℤ)) ≫
            (reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom) ≫
          ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
            (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).hom).hom)
        (Submodule.Quotient.mk x) := by
  let e0 :
      ((M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) ≃ₗ[A] M.X n :=
    (M.extendXIso ComplexShape.embeddingUpNat
      (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  let e1 :
      ((M.extend ComplexShape.embeddingUpNat).X (((n + 1 : ℕ) : ℤ))) ≃ₗ[A] M.X (n + 1) :=
    (M.extendXIso ComplexShape.embeddingUpNat
      (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).toLinearEquiv
  let r0 :
      (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X (n : ℤ)) ≃ₗ[A]
        (reduceModIdealA I M).X n :=
    ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
      (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  let r1 :
      (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X (((n + 1 : ℕ) : ℤ))) ≃ₗ[A]
        (reduceModIdealA I M).X (n + 1) :=
    ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
      (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).toLinearEquiv
  let q :
      ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X (n : ℤ) :=
    r0.symm (Submodule.Quotient.mk (e0 x))
  let targetValue :
      (reduceModIdealA I M).X (n + 1) :=
    (Submodule.Quotient.mk ((M.d n (n + 1)).hom (e0 x)) :
      M.X (n + 1) ⧸ I • (⊤ : Submodule A (M.X (n + 1))))
  have hleft_normalized :
      (((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M n).hom ≫
              ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).d
                (n : ℤ) ((n + 1 : ℕ) : ℤ)) ≫
            ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
              (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).hom).hom)
          (Submodule.Quotient.mk x)) =
        targetValue := by
    have hdq :=
      extendXIso_d_apply (M := reduceModIdealA I M) (n := n) q
    have hq : r0 q = (Submodule.Quotient.mk (e0 x) : (reduceModIdealA I M).X n) := by
      simpa [q] using
        (LinearEquiv.apply_symm_apply r0 (Submodule.Quotient.mk (e0 x) : (reduceModIdealA I M).X n))
    -- Normalize the left composite by first rewriting the comparison on the generator and then
    -- using the reduced `extendXIso` differential computation.
    change
      r1
          ((((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).d
                (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom
            (((reduceModIdealA_extendComponentIso_nonneg (A := A) I M n).hom).hom
              (Submodule.Quotient.mk x))) =
        targetValue
    rw [reduceModIdealA_extendComponentIso_nonneg_hom_apply_mk]
    calc
      r1 ((((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).d
            (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom q) =
          ((reduceModIdealA I M).d n (n + 1)).hom (Submodule.Quotient.mk (e0 x)) := by
            refine hdq.trans ?_
            simpa using congrArg (((reduceModIdealA I M).d n (n + 1)).hom) hq
      _ = targetValue := by
            rw [reduceModIdealA_d_eq]
            exact reduceModIdealADifferential_apply_mk (I := I) (K := M) n (e0 x)
  let rightValue :
      (reduceModIdealA I M).X (n + 1) :=
    (((((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d
            (n : ℤ) ((n + 1 : ℕ) : ℤ)) ≫
          (reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom) ≫
        ((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
          (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).hom).hom)
      (Submodule.Quotient.mk x)
  have hright_normalized : rightValue = targetValue := by
    have hdx := extendXIso_d_apply (M := M) (n := n) x
    -- Normalize the right composite by evaluating the reduced differential on the generator,
    -- transporting that quotient class across the comparison, and finally rewriting the source
    -- extended differential via `extendXIso_d_apply`.
    change
      r1
          ((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom).hom)
            (((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d
                (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom (Submodule.Quotient.mk x))) =
        targetValue
    have hdreduce :
        (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d
            (n : ℤ) ((n + 1 : ℕ) : ℤ) =
          CochainComplex.reduceModIdealADifferential
            I (M.extend ComplexShape.embeddingUpNat) (n : ℤ) := by
      simpa using
        (reduceModIdealA_d_eq
          (I := I) (K := M.extend ComplexShape.embeddingUpNat) (i := (n : ℤ)))
    have hmk :
        (CochainComplex.reduceModIdealADifferential
            I (M.extend ComplexShape.embeddingUpNat) (n : ℤ)).hom
          (Submodule.Quotient.mk x) =
        (Submodule.Quotient.mk
          (((M.extend ComplexShape.embeddingUpNat).d
              (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x) :
          (M.extend ComplexShape.embeddingUpNat).X (((n + 1 : ℕ) : ℤ)) ⧸
            I • (⊤ : Submodule A
              ((M.extend ComplexShape.embeddingUpNat).X (((n + 1 : ℕ) : ℤ))))) := by
      exact
        reduceModIdealADifferential_apply_mk
          (I := I) (K := M.extend ComplexShape.embeddingUpNat) (i := (n : ℤ)) x
    rw [hdreduce]
    have hmk' :
        r1
            ((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom).hom)
              ((CochainComplex.reduceModIdealADifferential
                  I (M.extend ComplexShape.embeddingUpNat) (n : ℤ)).hom
                (Submodule.Quotient.mk x))) =
          r1
            ((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom).hom)
              (Submodule.Quotient.mk
                (((M.extend ComplexShape.embeddingUpNat).d
                    (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x))) := by
      exact congrArg
        (fun z ↦
          r1 ((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom).hom) z))
        hmk
    have hiso :
        r1
            ((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom).hom)
              (Submodule.Quotient.mk
                (((M.extend ComplexShape.embeddingUpNat).d
                    (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x))) =
          r1
            ((((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
                  (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).inv).hom
              (Submodule.Quotient.mk
                (e1 (((M.extend ComplexShape.embeddingUpNat).d
                  (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x)))) := by
      exact congrArg (fun z ↦ r1 z)
        (reduceModIdealA_extendComponentIso_nonneg_hom_apply_mk
          (A := A) I M (n + 1)
          (((M.extend ComplexShape.embeddingUpNat).d
              (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x))
    calc
      r1
          ((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom).hom)
            ((CochainComplex.reduceModIdealADifferential
                I (M.extend ComplexShape.embeddingUpNat) (n : ℤ)).hom
              (Submodule.Quotient.mk x))) =
          r1
            ((((reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom).hom)
              (Submodule.Quotient.mk
                (((M.extend ComplexShape.embeddingUpNat).d
                    (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x))) := hmk'
      _ = r1
          ((((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
                (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).inv).hom
            (Submodule.Quotient.mk
              (e1 (((M.extend ComplexShape.embeddingUpNat).d
                (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x)))) := hiso
      _ = (Submodule.Quotient.mk
            (e1 (((M.extend ComplexShape.embeddingUpNat).d
              (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x)) :
            M.X (n + 1) ⧸ I • (⊤ : Submodule A (M.X (n + 1)))) := by
            simpa [r1] using
              (LinearEquiv.apply_symm_apply r1
                (Submodule.Quotient.mk
                  (e1 (((M.extend ComplexShape.embeddingUpNat).d
                    (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x)) :
                  (reduceModIdealA I M).X (n + 1)))
      _ = (Submodule.Quotient.mk ((M.d n (n + 1)).hom (e0 x)) :
            M.X (n + 1) ⧸ I • (⊤ : Submodule A (M.X (n + 1)))) := by
            exact congrArg
              (fun y : M.X (n + 1) ↦
                (Submodule.Quotient.mk y :
                  M.X (n + 1) ⧸ I • (⊤ : Submodule A (M.X (n + 1)))))
              hdx
  simpa [rightValue] using hleft_normalized.trans hright_normalized.symm

private theorem reduceModIdealA_extendComponentIso_nonneg_comm
    (I : Ideal A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (reduceModIdealA_extendComponentIso_nonneg (A := A) I M n).hom ≫
      ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫
      (reduceModIdealA_extendComponentIso_nonneg (A := A) I M (n + 1)).hom := by
  -- Route correction: compare the square only after postcomposing with the successor reduced
  -- `extendXIso`; on quotient generators that removes the inverse transport from the comparison.
  apply (cancel_mono (((reduceModIdealA I M).extendXIso ComplexShape.embeddingUpNat
    (by simp : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1)).hom)).1
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun q ↦ ?_
  refine Quotient.inductionOn' q ?_
  intro x
  simpa [Category.assoc] using
    (reduceModIdealA_extendComponentIso_nonneg_comm_apply_mk (A := A) I M n x)

/-- Helper for Lemma 15.96.7: when the source degree is negative, the comparison square
commutes because the source object is zero. -/
private theorem reduceModIdealA_extendComponentIso_neg_comm
    (I : Ideal A) (M : NatModuleCochainComplex A) {i j : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hi : ¬ 0 ≤ i) :
    (reduceModIdealA_extendComponentIso (A := A) I M i).hom ≫
      ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).d i j =
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d i j ≫
      (reduceModIdealA_extendComponentIso (A := A) I M j).hom := by
  letI :
      Subsingleton ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X i) :=
    ModuleCat.subsingleton_of_isZero
      (reduceModIdealA_extend_source_isZero_of_neg (A := A) I M hi)
  have hsub :
      Subsingleton
        (((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X i) ⟶
          (((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).X j)) := by
    refine ⟨?_⟩
    intro f g
    apply ModuleCat.hom_ext
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    cases hx
    rw [LinearMap.map_zero, LinearMap.map_zero]
  -- Both composites have the same zero source, so the hom-set itself is a subsingleton.
  exact hsub.elim _ _

/-- Helper for Lemma 15.96.7: the chosen degreewise comparison commutes with the differentials of
the two reduced complexes. -/
private theorem reduceModIdealA_extendComponentIso_comm
    (I : Ideal A) (M : NatModuleCochainComplex A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (reduceModIdealA_extendComponentIso (A := A) I M i).hom ≫
      ((reduceModIdealA I M).extend ComplexShape.embeddingUpNat).d i j =
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d i j ≫
      (reduceModIdealA_extendComponentIso (A := A) I M j).hom := by
  -- Split on the sign of the source degree so the remaining comparison is either the cached
  -- nonnegative successor square or the zero-object square in negative degree.
  by_cases hi : 0 ≤ i
  · rcases hij with rfl
    let n : ℕ := i.toNat
    have hn : (n : ℤ) = i := Int.toNat_of_nonneg hi
    -- After rewriting `i` as a natural degree, the comparison is exactly the successor square
    -- already proved on quotient generators.
    rw [← hn]
    simpa [reduceModIdealA_extendComponentIso] using
      (reduceModIdealA_extendComponentIso_nonneg_comm (A := A) I M n)
  · -- In negative degree the source term is zero, so the dedicated zero-object commutative square
    -- closes the comparison.
    exact reduceModIdealA_extendComponentIso_neg_comm (A := A) I M hij hi

/-- Helper for Lemma 15.96.7: reduction modulo `I` should commute with extension by zero. The
complex-level comparison is isolated here so the bounded-below Bockstein can be defined by honest
conjugation of the owner `ℤ`-indexed morphism. -/
private noncomputable def reduceModIdealA_extendIso
    (I : Ideal A) (M : NatModuleCochainComplex A) :
    reduceModIdealA I (M.extend ComplexShape.embeddingUpNat) ≅
      (reduceModIdealA I M).extend ComplexShape.embeddingUpNat :=
  -- Assemble the degreewise comparisons into an isomorphism of cochain complexes.
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ reduceModIdealA_extendComponentIso (A := A) I M i)
    (reduceModIdealA_extendComponentIso_comm (A := A) I M)

/-- Helper for Lemma 15.96.7: the canonical homology identification
`M.extend embeddingUpNat` transports `f`-torsion submodules exactly. -/
private theorem extendHomologyIso_torsionBy_map
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (Submodule.torsionBy A ((M.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) f).map
        (M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv.toLinearMap =
      Submodule.torsionBy A (M.homology n) f := by
  -- Membership in `torsionBy` is preserved by the degreewise homology equivalence.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ Submodule.torsionBy A ((M.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) f at hy
    change ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv y) ∈
      Submodule.torsionBy A (M.homology n) f
    rw [Submodule.mem_torsionBy_iff] at hy ⊢
    simpa using congrArg
      ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).hom) hy
  · intro hx
    refine ⟨(M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).inv x, ?_, by simp⟩
    change ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).inv x) ∈
      Submodule.torsionBy A ((M.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) f
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    simpa using congrArg
      ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).inv) hx

/-- Helper for Lemma 15.96.7: after identifying reduction with extension degreewise, the homology
of the reduced owner complex in degree `i` is canonically the homology of the reduced bounded-below
complex in degree `i`. -/
noncomputable abbrev reduceModIdealAHomologyIso
    (I : Ideal A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).homology (i : ℤ) ≅
      (reduceModIdealA I M).homology i :=
  HomologicalComplex.homologyMapIso (reduceModIdealA_extendIso (A := A) I M) (i : ℤ) ≪≫
    (reduceModIdealA I M).extendHomologyIso ComplexShape.embeddingUpNat (by simp)

/-- The bounded-below bridge/view of the Berthelot-Ogus Bockstein morphism
`H^i(M^\bullet/fM^\bullet) → H^{i+1}(M^\bullet/fM^\bullet)` coming from the short exact
sequence on the owner complex `M.extend ComplexShape.embeddingUpNat`, transported back to the
bounded-below model along the canonical reduction homology identifications from
`Remark_15_96_5`. In the textbook Berthelot-Ogus setting, this is the map
`β : H^i(M^\bullet ⊗_A f^iA/f^{i+1}A) → H^{i+1}(M^\bullet ⊗_A f^{i+1}A/f^{i+2}A)`. -/
noncomputable abbrev bockstein
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    (reduceModIdealA (principalIdeal f) M).homology i ⟶
      (reduceModIdealA (principalIdeal f) M).homology (i + 1) :=
  -- Transport the owner `ℤ`-indexed Bockstein through the canonical reduction homology bridge.
  (reduceModIdealAHomologyIso (principalIdeal f) M i).inv ≫
    ModFSquared.bockstein f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)
      hM.toIsTermwiseFTorsionFree ≫
    (reduceModIdealAHomologyIso (principalIdeal f) M (i + 1)).hom

/-- The bounded-below bridge/view of the condition that
`Ker(d^i mod f²) → Ker(d^i mod f)` is surjective, expressed as the epimorphy of the induced map
on cycles. This is the bounded-below bridge/view of the owner predicate
`ModFSquared.cyclesReductionSurjective` on `M.extend ComplexShape.embeddingUpNat`. -/
abbrev cyclesReductionSurjective
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) : Prop :=
  ModFSquared.cyclesReductionSurjective f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)

-- Proof sketch: identify the textbook `β` with the connecting morphism of
-- `0 → M^\bullet/fM^\bullet → M^\bullet/f²M^\bullet → M^\bullet/fM^\bullet → 0`; exactness of
-- the long exact homology sequence then says that surjectivity on cycles is equivalent to the
-- vanishing of this connecting morphism.
/-- Lemma 15.96.7, bounded-below bridge/view: for a cochain complex of `f`-torsion-free
`A`-modules, surjectivity of `Ker(d^i mod f²) → Ker(d^i mod f)` is equivalent to the vanishing of
the Berthelot-Ogus Bockstein morphism
`β : H^i(M^\bullet ⊗_A f^iA/f^{i+1}A) → H^{i+1}(M^\bullet ⊗_A f^{i+1}A/f^{i+2}A)`. -/
@[stacks 0F7Y]
theorem cyclesReductionSurjective_iff_bockstein_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M)
    (i : ℕ) :
    cyclesReductionSurjective f M i ↔ bockstein f M i hM = 0 := by
  constructor
  · intro hcycles
    have howner :
        ModFSquared.bockstein f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)
            hM.toIsTermwiseFTorsionFree = 0 :=
      (ModFSquared.cyclesReductionSurjective_iff_bockstein_eq_zero
        f (M.extend ComplexShape.embeddingUpNat) hM.toIsTermwiseFTorsionFree (i : ℤ)).1 hcycles
    -- Once the owner Bockstein vanishes, its conjugate on the bounded-below model also vanishes.
    simp [bockstein, howner]
  · intro hbockstein
    have howner :
        ModFSquared.bockstein f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)
            hM.toIsTermwiseFTorsionFree = 0 := by
      -- Cancel the surrounding transport isomorphisms to recover the owner vanishing statement.
      have htransport :=
        congrArg
          (fun φ ↦
            (reduceModIdealAHomologyIso (principalIdeal f) M i).hom ≫ φ ≫
              (reduceModIdealAHomologyIso (principalIdeal f) M (i + 1)).inv)
          hbockstein
      simpa [bockstein, Category.assoc] using htransport
    exact
      (ModFSquared.cyclesReductionSurjective_iff_bockstein_eq_zero
        f (M.extend ComplexShape.embeddingUpNat) hM.toIsTermwiseFTorsionFree (i : ℤ)).2 howner

-- Proof sketch: by the factorization from `15.96.5.1`, the Bockstein map factors through the
-- `f`-torsion in `H^{i+1}(M^\bullet)`. If that torsion submodule is zero, then the Bockstein map
-- vanishes; the equivalence above then gives surjectivity on cycles.
/-- If `H^{i+1}(M^\bullet)[f] = 0`, then `Ker(d^i mod f²) → Ker(d^i mod f)` is surjective. -/
theorem cyclesReductionSurjective_of_homology_f_torsion_eq_bot
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M)
    (i : ℕ) (hH : Submodule.torsionBy A (M.homology (i + 1)) f = ⊥) :
    cyclesReductionSurjective f M i := by
  let e :=
    M.extendHomologyIso ComplexShape.embeddingUpNat
      (rfl : (((i + 1 : ℕ) : ℤ)) = ((i + 1 : ℕ) : ℤ))
  have hownerTorsion :
      Submodule.torsionBy A
          ((M.extend ComplexShape.embeddingUpNat).homology ((i + 1 : ℕ) : ℤ)) f =
        ⊥ := by
    -- The degreewise homology equivalence identifies the owner torsion submodule with the bounded
    -- below one, so triviality of the latter forces triviality of the former.
    apply le_antisymm
    · intro x hx
      have hx' :
          (e.toLinearEquiv x) ∈
            (Submodule.torsionBy A
              ((M.extend ComplexShape.embeddingUpNat).homology ((i + 1 : ℕ) : ℤ)) f).map
                e.toLinearEquiv.toLinearMap := by
        exact ⟨x, hx, rfl⟩
      rw [extendHomologyIso_torsionBy_map, hH] at hx'
      change x = 0
      have hx0 : e.toLinearEquiv x = e.toLinearEquiv 0 := by
        calc
          e.toLinearEquiv x = 0 := by simpa using hx'
          _ = e.toLinearEquiv 0 := by
            symm
            simpa using e.toLinearEquiv.map_zero
      exact e.toLinearEquiv.injective hx0
    · exact bot_le
  -- Apply the owner torsion corollary on the extension-by-zero complex.
  exact
    ModFSquared.cyclesReductionSurjective_of_homology_f_torsion_eq_bot
      f (M.extend ComplexShape.embeddingUpNat) hM.toIsTermwiseFTorsionFree (i : ℤ) hownerTorsion

end Nat

end ModFSquared

end
