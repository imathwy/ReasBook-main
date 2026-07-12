import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Regular.IsSMulRegular
import StacksProject_2024.Chap15.PrincipalIdeal
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open CochainComplex

universe u v w

noncomputable section

variable {A : Type u} [CommRing A]

/-- A cochain complex of `A`-modules indexed by `ℤ`. -/
abbrev ModuleComplex (A : Type u) [CommRing A] := CochainComplex (ModuleCat A) ℤ

/-- A cochain complex of `A`-modules indexed by `ℕ`. -/
abbrev NatModuleCochainComplex (A : Type u) [CommRing A] :=
  CochainComplex (ModuleCat A) ℕ

namespace BerthelotOgusInt

/-- The degree-`i` Berthelot-Ogus term on a `ℤ`-indexed cochain complex. -/
abbrev degreeSubmodule (f : A) (K : ModuleComplex A) (i : ℤ) :
    Submodule A (K.X i) :=
  LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (K.X (i + 1)) (f ^ Int.toNat (i + 1)))).comap (K.d i (i + 1)).hom

/-- The differential of `K` preserves the Berthelot-Ogus degree submodules. -/
private theorem differential_mem
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : degreeSubmodule f K i) :
    K.d i (i + 1) x ∈ degreeSubmodule f K (i + 1) := by
  refine ⟨?_, ?_⟩
  · simpa [degreeSubmodule] using x.2.2
  · refine ⟨0, ?_⟩
    have hdd := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (K.d_comp_d i (i + 1) (i + 2))) x
    rw [show i + 2 = i + 1 + 1 by abel] at hdd
    calc
      ((LinearMap.lsmul A (K.X (i + 1 + 1)) (f ^ Int.toNat (i + 1 + 1))) 0) = 0 := by
        simp
      _ = (ModuleCat.Hom.hom (K.d (i + 1) (i + 1 + 1))) ((ConcreteCategory.hom (K.d i (i + 1))) x) :=
        hdd.symm

/-- The restricted differential on the Berthelot-Ogus complex. -/
abbrev differentialLinear (f : A) (K : ModuleComplex A) (i : ℤ) :
    degreeSubmodule f K i →ₗ[A] degreeSubmodule f K (i + 1) :=
  ((K.d i (i + 1)).hom.comp (degreeSubmodule f K i).subtype).codRestrict
    (degreeSubmodule f K (i + 1))
    (differential_mem f K i)

/-- Successive Berthelot-Ogus differentials compose to zero. -/
theorem differential_sq (f : A) (K : ModuleComplex A) (i : ℤ) :
    ModuleCat.ofHom (differentialLinear f K i) ≫
        ModuleCat.ofHom (differentialLinear f K (i + 1)) =
      0 := by
  ext x
  change
    (ModuleCat.Hom.hom (K.d (i + 1) (i + 1 + 1))) ((ModuleCat.Hom.hom (K.d i (i + 1))) x) = 0
  have hdd := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (K.d_comp_d i (i + 1) (i + 2))) x
  rw [show i + 2 = i + 1 + 1 by abel] at hdd
  exact hdd

/-- The Berthelot-Ogus complex `η_f K` on a `ℤ`-indexed cochain complex. -/
def complex (f : A) (K : ModuleComplex A) : ModuleComplex A :=
  CochainComplex.of
    (fun i ↦ ModuleCat.of A (degreeSubmodule f K i))
    (fun i ↦ ModuleCat.ofHom (differentialLinear f K i))
    (fun i ↦ differential_sq f K i)

/-- If `K` is supported in nonnegative degrees, then so is `η_f K`. -/
instance complex_isStrictlyGE_zero
    (f : A) (K : ModuleComplex A) [K.IsStrictlyGE 0] :
    (complex f K).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  let hzero : CategoryTheory.Limits.IsZero (K.X i) := K.isZero_of_isStrictlyGE 0 i hi
  letI : Subsingleton (K.X i) := ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton ((complex f K).X i) := by
    change Subsingleton (degreeSubmodule f K i)
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

scoped[BerthelotOgusInt] notation "η[" f "] " K:arg => complex f K

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

/-- The degree-`n` Berthelot-Ogus term for a nonnegative cochain complex. -/
abbrev etaFDegreeSubmodule (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    Submodule A (M.X n) :=
  LinearMap.range (LinearMap.lsmul A (M.X n) (f ^ n)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (M.X (n + 1)) (f ^ (n + 1)))).comap (M.d n (n + 1)).hom

/-- The differential of `M` preserves the source-facing Berthelot-Ogus degree submodules. -/
private theorem etaFDifferential_mem
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : etaFDegreeSubmodule f M n) :
    M.d n (n + 1) x ∈ etaFDegreeSubmodule f M (n + 1) := by
  refine ⟨?_, ?_⟩
  · simpa [etaFDegreeSubmodule] using x.2.2
  · refine ⟨0, ?_⟩
    calc
      ((LinearMap.lsmul A (M.X ((n + 1) + 1)) (f ^ ((n + 1) + 1))) 0) = 0 := by
        simp
      _ = (ModuleCat.Hom.hom (M.d (n + 1) ((n + 1) + 1))) ((ConcreteCategory.hom (M.d n (n + 1))) x) :=
        (LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (M.d_comp_d n (n + 1) ((n + 1) + 1))) x).symm

/-- The restricted differential on `η_f M`. -/
private abbrev etaFDifferentialLinear
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    etaFDegreeSubmodule f M n →ₗ[A] etaFDegreeSubmodule f M (n + 1) :=
  ((M.d n (n + 1)).hom.comp (etaFDegreeSubmodule f M n).subtype).codRestrict
    (etaFDegreeSubmodule f M (n + 1))
    (etaFDifferential_mem f M n)

/-- Successive source-facing Berthelot-Ogus differentials compose to zero. -/
private theorem etaFDifferential_sq (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (etaFDifferentialLinear f M n) ≫
        ModuleCat.ofHom (etaFDifferentialLinear f M (n + 1)) =
      0 := by
  ext x
  change
    (ModuleCat.Hom.hom (M.d (n + 1) (n + 1 + 1))) ((ModuleCat.Hom.hom (M.d n (n + 1))) x) = 0
  have hdd := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (M.d_comp_d n (n + 1) ((n + 1) + 1))) x
  exact hdd

/-- The source-facing Berthelot-Ogus complex `η_f M` on `NatModuleCochainComplex A`. -/
def etaFComplex (f : A) (M : NatModuleCochainComplex A) : NatModuleCochainComplex A :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (etaFDegreeSubmodule f M n))
    (fun n ↦ ModuleCat.ofHom (etaFDifferentialLinear f M n))
    (fun n ↦ etaFDifferential_sq f M n)

notation "η[" f "] " M:arg => etaFComplex f M

open scoped BerthelotOgusInt

/- Domain-style sampling for the reduction owner:
- primary domain: reduction modulo an ideal of cochain complexes of `A`-modules, and the
  source-facing Berthelot-Ogus reduction `η_f(K^\bullet) / f η_f(K^\bullet)`;
- sampled owner declarations:
  `CochainComplex (ModuleCat A) ι`,
  `LinearMap.reduceModIdeal`,
  `ModuleCat.restrictScalars`,
  `BerthelotOgusInt.complex`;
- best owner abstraction:
  `core/canonical`: reduction modulo an ideal of a cochain complex, owned once by
    `CochainComplex.reduceModIdeal` together with its induced map
    `CochainComplex.reduceModIdealMap` and scalar-restricted view
    `CochainComplex.reduceModIdealA`;
  `source-facing`: the Berthelot-Ogus reduction owners
    `BerthelotOgusEtaReduction.complex` together with the quotient-ring comparison map
    `BerthelotOgusEtaReduction.toHomology`;
  `bridge/view`: the scalar-restricted `A`-linear view, the nonnegative-degree restriction and
  homology identifications for `CochainComplex.reduceModIdealA`, and the bounded-below
    comparison map `BerthelotOgusEtaReduction.Nat.toHomology`;
  `primitive data vs derived API`: the primitive data are the quotient terms and induced
  differentials. The Berthelot-Ogus reduction and the quotient-to-homology maps are derived from
  that owner construction, so the file should not keep parallel local bounded-below copies of the
  quotient-ring reduction complex or cocycle map. -/

namespace CochainComplex

/-- Helper for Remark 15.96.5: reducing a composite modulo an ideal and evaluating on a quotient
representative agrees with reducing the composite directly. -/
theorem LinearMap.reduceModIdeal_comp_apply_mk
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (I : Ideal A) (f : M →ₗ[A] N) (g : N →ₗ[A] P) (x : M) :
    (g.reduceModIdeal I) ((f.reduceModIdeal I) (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (g (f x)) := by
  -- Both quotient maps are induced by the original linear maps, so evaluation on a representative
  -- is definitionally the quotient class of the composite.
  simp [LinearMap.reduceModIdeal_apply]

/-- The degree-`i` differential on the reduction of a cochain complex modulo `I`. -/
private abbrev reduceModIdealDifferential
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    ModuleCat.of (A ⧸ I) (K.X i ⧸ I • (⊤ : Submodule A (K.X i))) ⟶
      ModuleCat.of (A ⧸ I) (K.X (i + 1) ⧸ I • (⊤ : Submodule A (K.X (i + 1)))) :=
  ModuleCat.ofHom <| (K.d i (i + 1)).hom.reduceModIdeal I

-- Proof sketch: the reduced differential is induced from the differential of `K`, so two
-- successive reduced differentials factor through the quotient of `d ≫ d = 0`.
/-- Two successive reduced differentials compose to zero. -/
private theorem reduceModIdealDifferential_sq
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    reduceModIdealDifferential I K i ≫ reduceModIdealDifferential I K (i + 1) = 0 := by
  -- The quotient differential is induced degreewise, so square-zero descends to quotient
  -- representatives from the original relation `d ≫ d = 0`.
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
    Submodule.Quotient.mk
        ((K.d (i + 1) ((i + 1) + 1)).hom ((K.d i (i + 1)).hom x)) =
      0
  rw [Submodule.Quotient.mk_eq_zero]
  rw [hsq']
  simp

/-- The cochain complex obtained by reducing every term of `K` modulo `I`, viewed over the
quotient ring `A ⧸ I`. -/
abbrev reduceModIdeal
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) :
    CochainComplex (ModuleCat.{v} (A ⧸ I)) ι :=
  let _ : DecidableEq ι := Classical.decEq ι
  CochainComplex.of
    (fun i ↦ ModuleCat.of (A ⧸ I) (K.X i ⧸ I • (⊤ : Submodule A (K.X i))))
    (fun i ↦ reduceModIdealDifferential I K i)
    (fun i ↦ reduceModIdealDifferential_sq I K i)

/-- The scalar-restricted `A`-linear view of `K / IK`. -/
abbrev reduceModIdealA
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) :
    CochainComplex (ModuleCat.{v} A) ι :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ι)).obj
    (reduceModIdeal I K)

/-- Helper for Remark 15.96.5: the reduced differential sends a quotient generator to the quotient
class of the original differential. -/
private theorem reduceModIdeal_d_apply_mk
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) (x : K.X i) :
    (ModuleCat.Hom.hom ((reduceModIdeal I K).d i (i + 1))) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((K.d i (i + 1)).hom x) := by
  classical
  delta reduceModIdeal
  rw [@CochainComplex.of_d _ _ _ ι _ _ (Classical.decEq ι)]
  simpa only [reduceModIdealDifferential, ModuleCat.hom_ofHom] using
    (LinearMap.reduceModIdeal_apply (I := I) (f := (K.d i (i + 1)).hom) x)

/-- Helper for Remark 15.96.5: scalar restriction does not change how the reduced differential
acts on quotient generators. -/
private theorem reduceModIdealA_d_apply_mk
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) (x : K.X i) :
    (ModuleCat.Hom.hom ((reduceModIdealA I K).d i (i + 1))) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((K.d i (i + 1)).hom x) := by
  simpa [reduceModIdealA] using reduceModIdeal_d_apply_mk I K i x

/-- The morphism induced on reduced complexes by a morphism of cochain complexes. -/
abbrev reduceModIdealMap
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    {K L : CochainComplex (ModuleCat.{v} A) ι} (I : Ideal A) (φ : K ⟶ L) :
    reduceModIdeal I K ⟶ reduceModIdeal I L where
  f i := ModuleCat.ofHom <| (φ.f i).hom.reduceModIdeal I
  comm' i j hij := by
    rcases hij with rfl
    -- Reduce the square to quotient representatives and then use the original cochain-map
    -- commutativity in degree `i`.
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun q ↦ ?_
    refine Quotient.inductionOn' q ?_
    intro x
    -- On a quotient representative, both sides are the reduced classes of the original
    -- commutative square for `φ`.
    calc
      (ModuleCat.Hom.hom
          (ModuleCat.ofHom (LinearMap.reduceModIdeal I (ModuleCat.Hom.hom (φ.f i))) ≫
            (reduceModIdeal I L).d i (i + 1)))
          (Quotient.mk'' x) =
          (Submodule.Quotient.mk ((L.d i (i + 1)).hom ((φ.f i).hom x)) :
            L.X (i + 1) ⧸ I • (⊤ : Submodule A (L.X (i + 1)))) := by
            rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
              Submodule.Quotient.mk''_eq_mk, LinearMap.reduceModIdeal_apply]
            exact reduceModIdeal_d_apply_mk I L i ((φ.f i).hom x)
      _ =
          (Submodule.Quotient.mk ((φ.f (i + 1)).hom ((K.d i (i + 1)).hom x)) :
            L.X (i + 1) ⧸ I • (⊤ : Submodule A (L.X (i + 1)))) := by
            exact congrArg Submodule.Quotient.mk
              (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (φ.comm i (i + 1))) x)
      _ =
          (ModuleCat.Hom.hom
            ((reduceModIdeal I K).d i (i + 1) ≫
              ModuleCat.ofHom (LinearMap.reduceModIdeal I (ModuleCat.Hom.hom (φ.f (i + 1))))))
            (Quotient.mk'' x) := by
            symm
            classical
            delta reduceModIdeal
            rw [@CochainComplex.of_d _ _ _ ι _ _ (Classical.decEq ι)]
            simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
              Submodule.Quotient.mk''_eq_mk, reduceModIdealDifferential] using
              (LinearMap.reduceModIdeal_comp_apply_mk
                (A := A) (I := I) ((K.d i (i + 1)).hom) ((φ.f (i + 1)).hom) x)

/-- The scalar-restricted `A`-linear view of the morphism induced on reduced complexes. -/
abbrev reduceModIdealAMap
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    {K L : CochainComplex (ModuleCat.{v} A) ι} (I : Ideal A) (φ : K ⟶ L) :
    reduceModIdealA I K ⟶ reduceModIdealA I L :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ι)).map
    (reduceModIdealMap I φ)

end CochainComplex

namespace BerthelotOgusEtaReduction

open BerthelotOgusInt

/-- The canonical inclusion `η_f(K^\bullet) ⟶ K^\bullet`. -/
private def etaInclusion (f : A) (K : ModuleComplex A) :
    η[f] K ⟶ K where
  f i := ModuleCat.ofHom (degreeSubmodule f K i).subtype
  comm' i j hij := by
    rcases hij with rfl
    -- Both sides are the same underlying differential; only one side remembers the codomain
    -- restriction defining `η_f(K)`.
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x ↦ ?_
    simpa [BerthelotOgusInt.complex, BerthelotOgusInt.differentialLinear]

/-- The bounded-below `ℤ`-indexed bridge reduction
`η_f(K^\bullet) / f η_f(K^\bullet)` over `A ⧸ (f)`. -/
abbrev complex (f : A) (K : ModuleComplex A) :
    ModuleComplex (A ⧸ principalIdeal f) :=
  reduceModIdeal (principalIdeal f) (BerthelotOgusInt.complex f K)

private abbrev toRawReductionLinear
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    (complex f K).X i →ₗ[A ⧸ principalIdeal f]
      (reduceModIdeal (principalIdeal f) K).X i :=
  ((reduceModIdealMap (principalIdeal f) (etaInclusion f K)).f i).hom

/- Route correction: the unguarded owner-level cocycle claim is false in negative degrees,
because `Int.toNat (i + 1) = 0` no longer forces `d(x)` to be divisible by `f`. The source proof
for Remark 15.96.5 is bounded-below, so we record the needed divisibility only in nonnegative
degrees and use `K.IsStrictlyGE 0` to discard the negative-degree source terms. -/
/-- Helper for Remark 15.96.5: in nonnegative degrees, the defining Berthelot-Ogus witness for
`x ∈ (η_f K)^i` already places `d(x)` in `(f)K^{i + 1}`. -/
private theorem differential_mem_principal_of_nonneg
    (f : A) (K : ModuleComplex A) (i : ℤ) (hi : 0 ≤ i)
    (x : degreeSubmodule f K i) :
    (K.d i (i + 1)).hom x ∈
      principalIdeal f • (⊤ : Submodule A (K.X (i + 1))) := by
  rcases x.2.2 with ⟨y, hy⟩
  -- The second defining condition writes `d(x)` as `f ^ Int.toNat (i + 1)` times a witness.
  have hpos : 0 < i + 1 := by
    linarith
  have hpowpos : 0 < Int.toNat (i + 1) := by
    simpa [Int.toNat_of_nonneg (le_of_lt hpos)] using hpos
  have hpowmem : f ^ Int.toNat (i + 1) ∈ principalIdeal f := by
    have hbase : f ∈ principalIdeal f := Ideal.subset_span (by simp)
    have hpowmem' : f ^ Int.toNat (i + 1) ∈ (principalIdeal f) ^ Int.toNat (i + 1) := by
      exact Ideal.pow_mem_pow hbase (Int.toNat (i + 1))
    exact (Ideal.pow_le_self (I := principalIdeal f) (Nat.ne_of_gt hpowpos)) hpowmem'
  -- Since the exponent is positive, the witness lies in `(f)K^{i + 1}`.
  rw [← hy]
  simpa [LinearMap.lsmul_apply] using
    (Submodule.smul_mem_smul hpowmem
      (show y ∈ (⊤ : Submodule A (K.X (i + 1))) by simp))

-- Proof sketch: an element of `η_f(K)^i` reduces to a cocycle in `K^i / fK^i` because its
-- differential is already divisible by `f` in degree `i + 1`.
/-- The canonical quotient map from the reduced Berthelot-Ogus term to the reduced complex lands in
cycles. -/
private theorem toRawReductionLinear_comp_d_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) [K.IsStrictlyGE 0] :
    ModuleCat.ofHom (toRawReductionLinear f K i) ≫
        (reduceModIdeal (principalIdeal f) K).d i (i + 1) =
      0 := by
  by_cases hi : 0 ≤ i
  · -- In nonnegative degrees, quotient representatives are cocycles because their differentials
    -- lie in `(f)K^{i + 1}` by the Berthelot-Ogus divisibility condition.
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun q ↦ ?_
    refine Quotient.inductionOn' q ?_
    intro x
    have hx0 :
        (Submodule.Quotient.mk ((K.d i (i + 1)).hom x.1) :
            K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) =
          0 := by
      exact (Submodule.Quotient.mk_eq_zero
        (principalIdeal f • (⊤ : Submodule A (K.X (i + 1))))).2
        (differential_mem_principal_of_nonneg f K i hi x)
    calc
      (ModuleCat.Hom.hom
          (ModuleCat.ofHom (toRawReductionLinear f K i) ≫
            (reduceModIdeal (principalIdeal f) K).d i (i + 1)))
          (Quotient.mk'' x) =
          (Submodule.Quotient.mk ((K.d i (i + 1)).hom x.1) :
            K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) := by
            classical
            delta reduceModIdeal
            rw [@CochainComplex.of_d _ _ _ ℤ _ _ (Classical.decEq ℤ)]
            simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
              Submodule.Quotient.mk''_eq_mk, toRawReductionLinear,
              reduceModIdealDifferential] using
              (LinearMap.reduceModIdeal_comp_apply_mk
                (A := A) (I := principalIdeal f)
                (((etaInclusion f K).f i).hom) ((K.d i (i + 1)).hom) x)
      _ = 0 := hx0
  · -- In negative degrees, bounded-below support makes the source quotient term zero.
    have hzero : CategoryTheory.Limits.IsZero ((η[f] K).X i) :=
      (η[f] K).isZero_of_isStrictlyGE 0 i (lt_of_not_ge hi)
    letI : Subsingleton ((η[f] K).X i) := ModuleCat.subsingleton_of_isZero hzero
    letI : Subsingleton ((complex f K).X i) := by
      change Subsingleton (((η[f] K).X i) ⧸
        principalIdeal f • (⊤ : Submodule A ((η[f] K).X i)))
      infer_instance
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun q ↦ ?_
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    simpa using
      LinearMap.map_zero
        ((ModuleCat.Hom.hom (reduceModIdealDifferential (principalIdeal f) K i)) ∘ₗ
          toRawReductionLinear f K i)

/-- The canonical map
`(η_f(K^\bullet)^i / f η_f(K^\bullet)^i) ⟶ Z^i(K^\bullet / f K^\bullet)`. -/
abbrev toCycles (f : A) (K : ModuleComplex A) (i : ℤ) [K.IsStrictlyGE 0] :
    (complex f K).X i ⟶ (reduceModIdeal (principalIdeal f) K).cycles i :=
  (reduceModIdeal (principalIdeal f) K).liftCycles'
    (ModuleCat.ofHom (toRawReductionLinear f K i))
    (i + 1) (by simp) (toRawReductionLinear_comp_d_eq_zero f K i)

/-- The canonical map
`(η_f(K^\bullet)^i / f η_f(K^\bullet)^i) ⟶ H^i(K^\bullet / f K^\bullet)`. -/
abbrev toHomology (f : A) (K : ModuleComplex A) (i : ℤ) [K.IsStrictlyGE 0] :
    (complex f K).X i ⟶ (reduceModIdeal (principalIdeal f) K).homology i :=
  toCycles f K i ≫ (reduceModIdeal (principalIdeal f) K).homologyπ i

namespace Nat

/-- The canonical inclusion `η_f(M^\bullet) ⟶ M^\bullet`. -/
private def etaInclusion (f : A) (M : NatModuleCochainComplex A) :
    η[f] M ⟶ M where
  f i := ModuleCat.ofHom (etaFDegreeSubmodule f M i).subtype
  comm' i j hij := by
    rcases hij with rfl
    -- As in the owner-level bridge, the source differential is the codomain restriction of `M.d`.
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x ↦ ?_
    simpa [etaFComplex]

private abbrev toRawReduction
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i ⟶
      (reduceModIdealA (principalIdeal f) M).X i :=
  (reduceModIdealAMap (principalIdeal f) (etaInclusion f M)).f i

/-- The scalar-restricted `A`-linear quotient map induced by the canonical inclusion
`η_f(M^\bullet) ⟶ M^\bullet`. -/
private abbrev toRawReductionLinear
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i →ₗ[A]
      (reduceModIdealA (principalIdeal f) M).X i :=
  (toRawReduction f M i).hom

/-- Helper for Remark 15.96.5: multiplication by a power of an `f`-regular scalar stays
injective. -/
private theorem lsmul_pow_injective
    {N : Type*} [AddCommGroup N] [Module A N] {f : A}
    (hf : IsSMulRegular N f) (n : ℕ) :
    Function.Injective (LinearMap.lsmul A N (f ^ n)) := by
  intro x y hxy
  induction n with
  | zero =>
      simpa using hxy
  | succ n ih =>
      apply ih
      apply hf
      simpa [LinearMap.lsmul_apply, pow_succ, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        using hxy

/-- Helper for Remark 15.96.5: an `η_f` degree term carries a canonical witness in the range of
multiplication by `f ^ i`. -/
private abbrev eta_degree_to_power_range
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    etaFDegreeSubmodule f M i →ₗ[A]
      LinearMap.range (LinearMap.lsmul A (M.X i) (f ^ i)) :=
  LinearMap.codRestrict
    (LinearMap.range (LinearMap.lsmul A (M.X i) (f ^ i)))
    (etaFDegreeSubmodule f M i).subtype
    (fun x ↦ x.2.1)

/-- Helper for Remark 15.96.5: the visible `f ^ i` factor identifies `M^i` with its image under
multiplication by `f ^ i`. -/
private noncomputable abbrev power_range_equiv
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    M.X i ≃ₗ[A] LinearMap.range (LinearMap.lsmul A (M.X i) (f ^ i)) :=
  LinearEquiv.ofInjective
    (LinearMap.lsmul A (M.X i) (f ^ i))
    (lsmul_pow_injective (A := A) (N := M.X i) (f := f) (hM.isSMulRegular i) i)

/-- Helper for Remark 15.96.5: divide a degree-`i` `η_f` element by its canonical `f ^ i`
factor before reducing modulo `(f)`. -/
private noncomputable abbrev divide_eta_degree_repr
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    etaFDegreeSubmodule f M i →ₗ[A] M.X i :=
  ((power_range_equiv f M i hM).symm : _ ≃ₗ[A] _).toLinearMap.comp
    (eta_degree_to_power_range f M i)

/-- Helper for Remark 15.96.5: multiplying the divided representative by `f ^ i` recovers the
original `η_f` element. -/
private theorem smul_divide_eta_degree_repr
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) (x : etaFDegreeSubmodule f M i) :
    (f ^ i) • divide_eta_degree_repr f M i hM x = x := by
  -- The representative is chosen as the inverse image of the range witness already stored in `x`.
  change
    (LinearMap.lsmul A (M.X i) (f ^ i))
        (((power_range_equiv f M i hM).symm) ⟨x.1, x.2.1⟩) = x.1
  simpa [power_range_equiv] using
    congrArg Subtype.val ((power_range_equiv f M i hM).apply_symm_apply ⟨x.1, x.2.1⟩)

/-- Helper for Remark 15.96.5: the divided representative induces the textbook quotient map
`(η_f M)^i / f(η_f M)^i → M^i / fM^i`. -/
private noncomputable abbrev divide_eta_degree_linear
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i →ₗ[A]
      (reduceModIdealA (principalIdeal f) M).X i :=
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) M).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  Submodule.mapQ
    (principalIdeal f • (⊤ : Submodule A (etaFDegreeSubmodule f M i)))
    (principalIdeal f • (⊤ : Submodule A (M.X i)))
    (divide_eta_degree_repr f M i hM)
    (Submodule.smul_top_le_comap_smul_top (principalIdeal f)
      (divide_eta_degree_repr f M i hM))

/-- Helper for Remark 15.96.5: on quotient generators, the divided map sends an `η_f`
representative to its divided class modulo `(f)`. -/
private theorem divide_eta_degree_linear_apply_mk
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) (x : etaFDegreeSubmodule f M i) :
    divide_eta_degree_linear f M i hM (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (divide_eta_degree_repr f M i hM x) := by
  -- The quotient map is induced by `divide_eta_degree_repr`, so it is computed on generators by
  -- applying that linear map before quotienting.
  simpa [divide_eta_degree_linear] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        (principalIdeal f • (⊤ : Submodule A (etaFDegreeSubmodule f M i)))
        (principalIdeal f • (⊤ : Submodule A (M.X i)))
        (divide_eta_degree_repr f M i hM))
      x

/-- Helper for Remark 15.96.5: the differential of the divided representative is divisible by
`f`, hence vanishes after reduction modulo `(f)`. -/
private theorem divide_eta_degree_d_mem_principal
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) (x : etaFDegreeSubmodule f M i) :
    (M.d i (i + 1)).hom (divide_eta_degree_repr f M i hM x) ∈
      principalIdeal f • (⊤ : Submodule A (M.X (i + 1))) := by
  rcases x.2.2 with ⟨y, hy⟩
  -- Apply the differential to the recovered equality `x = f ^ i • x'`.
  have hmul :
      (f ^ i) • ((M.d i (i + 1)).hom (divide_eta_degree_repr f M i hM x)) =
        (f ^ i) • (f • y) := by
    calc
      (f ^ i) • ((M.d i (i + 1)).hom (divide_eta_degree_repr f M i hM x))
          = (M.d i (i + 1)).hom ((f ^ i) • divide_eta_degree_repr f M i hM x) := by
              rw [_root_.map_smul]
      _ = (M.d i (i + 1)).hom x := by
            rw [smul_divide_eta_degree_repr f M i hM x]
      _ = (f ^ (i + 1)) • y := by
            simpa [LinearMap.lsmul_apply] using hy.symm
      _ = (f ^ i) • (f • y) := by
            simp [pow_succ, smul_smul, mul_comm]
  have hcancel :
      (M.d i (i + 1)).hom (divide_eta_degree_repr f M i hM x) = f • y := by
    exact (lsmul_pow_injective (A := A) (N := M.X (i + 1)) (f := f)
      (hM.isSMulRegular (i + 1)) i) hmul
  -- Once the differential is written as `f • y`, it lies in `(f)M`.
  rw [hcancel]
  simpa [principalIdeal] using
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
      (show y ∈ (⊤ : Submodule A (M.X (i + 1))) by simp))

/-- Helper for Remark 15.96.5: the divided quotient map lands in cycles of `M / fM`. -/
private theorem divide_eta_degree_comp_d_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    ModuleCat.ofHom (divide_eta_degree_linear f M i hM) ≫
        (reduceModIdealA (principalIdeal f) M).d i (i + 1) =
      0 := by
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) M).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) M).X (i + 1)) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  -- Evaluate on quotient representatives and use the divisibility lemma above.
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun q ↦ ?_
  refine Quotient.inductionOn' q ?_
  intro x
  change
    ((reduceModIdealA (principalIdeal f) M).d i (i + 1)).hom
        (divide_eta_degree_linear f M i hM (Submodule.Quotient.mk x)) = 0
  rw [divide_eta_degree_linear_apply_mk]
  have hx0 :
      (Submodule.Quotient.mk
          ((M.d i (i + 1)).hom (divide_eta_degree_repr f M i hM x)) :
            M.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (M.X (i + 1)))) =
        0 := by
    exact
      (Submodule.Quotient.mk_eq_zero
        (principalIdeal f • (⊤ : Submodule A (M.X (i + 1))))).2
        (divide_eta_degree_d_mem_principal f M i hM x)
  calc
    ((reduceModIdealA (principalIdeal f) M).d i (i + 1)).hom
        (Submodule.Quotient.mk (divide_eta_degree_repr f M i hM x)) =
        (Submodule.Quotient.mk
          ((M.d i (i + 1)).hom (divide_eta_degree_repr f M i hM x)) :
            M.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (M.X (i + 1)))) := by
          exact
            reduceModIdealA_d_apply_mk
              (principalIdeal f) M i (divide_eta_degree_repr f M i hM x)
    _ = 0 := hx0

/-- The canonical bounded-below map
`(η_f(M^\bullet)^i / f η_f(M^\bullet)^i) ⟶ H^i(M^\bullet / f M^\bullet)`. -/
abbrev toHomology (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i ⟶
      (reduceModIdealA (principalIdeal f) M).homology i :=
  by
    classical
    -- Route correction: the old reduced-inclusion map is zero in positive degrees, so the
    -- bounded-below comparison has to divide by the visible `f ^ i` factor before reducing
    -- modulo `(f)`.
    by_cases hM : IsTermwiseFTorsionFree f M
    · let _ : Module A ↑((reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
        Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
      let _ : Module A ↑((reduceModIdeal (principalIdeal f) M).X i) :=
        Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
      exact
        (reduceModIdealA (principalIdeal f) M).liftCycles'
            (ModuleCat.ofHom (divide_eta_degree_linear f M i hM))
            (i + 1) (by simp)
            (divide_eta_degree_comp_d_eq_zero f M i hM) ≫
          (reduceModIdealA (principalIdeal f) M).homologyπ i
    · exact 0

end Nat

end BerthelotOgusEtaReduction

/-- Remark 15.96.5: the canonical degree-`i` comparison map from the reduced Berthelot-Ogus term
to the degree-`i` cohomology of the reduction modulo `(f)`. -/
@[stacks 0F7S]
abbrev berthelotOgusEtaReductionToHomology
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i ⟶
      (reduceModIdealA (principalIdeal f) M).homology i :=
  BerthelotOgusEtaReduction.Nat.toHomology f M i
