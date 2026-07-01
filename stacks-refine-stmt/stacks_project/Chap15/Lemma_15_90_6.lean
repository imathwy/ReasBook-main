import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import stacks_project.Chap15.Definition_15_30_1
import stacks_project.Chap15.Lemma_15_90_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory
open ModuleCat
open scoped KoszulComplex
open Ideal.Quotient (eq_zero_iff_mem)

universe u

section

variable {R : Type u} [CommRing R] {n : ℕ}
variable (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N]

/- Domain-style sampling:
- primary domain: first Koszul homology with coefficients, its quotient presentation by cycles and
  boundaries, and the exact sequence obtained from the relation presentation of Lemma `15.90.5`;
- sampled owner declarations:
  `K^•(f)`,
  `HomologicalComplex.tensorObj`,
  `RingTheory.Sequence.IsH1RegularOn`,
  `CategoryTheory.ShortComplex.moduleCatToCycles`,
  `CategoryTheory.ShortComplex.moduleCatHomologyIso`,
  `LinearMap.quotKerEquivOfSurjective`,
  `Ext.precompOfLinear`;
- source/core/bridge triage:
  `source-facing`: the first Koszul homology object `koszulH1 f N`;
  `core/canonical`: degree-`1` homology of the chapter owner `K^•(f)` after tensoring with the
    coefficient module `N`, equivalently the owner predicate `RingTheory.Sequence.IsH1RegularOn`;
  `bridge/view`: the explicit three-term quotient model `koszulH1ModelShortComplex f N`, its
    quotient presentation `koszulH1Presentation f N`, and the vanishing bridge back to the chapter
    owner abstraction;
- primitive data: the owner complex `K^•(f) ⊗ N`, the relation map on tuples, the diagonal linear
  map, the three-term source-facing quotient model, and the linear connecting map
  `Hom_R(I, N) → Ext¹_R(R / I, N)`;
- derived API: the owner-level short exact sequence
  `0 ⟶ Ext¹_R(R / I, N) ⟶ koszulH1 f N ⟶ Hom_R(K, N) ⟶ 0`.
-/

private abbrev moduleSingle₀ (R : Type u) [CommRing R] (N : Type u) [AddCommGroup N] [Module R N] :
    ChainComplex (ModuleCat R) ℕ :=
  (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R N)

private abbrev koszulComplexWithModule (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N] :
    ChainComplex (ModuleCat R) ℕ :=
  HomologicalComplex.tensorObj (K^•(f)) (moduleSingle₀ R N)

/-- The tuple condition `fᵢ xⱼ = fⱼ xᵢ` defining degree-one Koszul cycles. -/
def koszulFirstCycleCondition (x : Fin n → N) : Prop :=
  ∀ i j : Fin n, f i • x j = f j • x i

/-- The linear map whose `(i, j)`-component is `x ↦ fᵢ xⱼ - fⱼ xᵢ`. -/
def koszulFirstCycleMap : (Fin n → N) →ₗ[R] Fin n × Fin n → N :=
  LinearMap.pi fun ij ↦
    (DistribSMul.toLinearMap R N (f ij.1)).comp (LinearMap.proj ij.2) -
      (DistribSMul.toLinearMap R N (f ij.2)).comp (LinearMap.proj ij.1)

/-- The submodule of degree-one Koszul cycles for the finite family `f`. -/
def koszulFirstCycles : Submodule R (Fin n → N) :=
  LinearMap.ker (koszulFirstCycleMap f N)

/-- The tuple condition defining degree-one Koszul cycles is equivalent to membership in the
kernel of the canonical relation map. -/
theorem koszulFirstCycleCondition_iff_mem_ker (x : Fin n → N) :
    koszulFirstCycleCondition f N x ↔ x ∈ LinearMap.ker (koszulFirstCycleMap f N) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    ext ij
    exact sub_eq_zero.mpr (hx ij.1 ij.2)
  · intro hx i j
    exact sub_eq_zero.mp (congrFun hx (i, j))

/-- Membership in the first-cycle submodule is exactly the pairwise Koszul cycle condition. -/
theorem mem_koszulFirstCycles_iff (x : Fin n → N) :
    x ∈ koszulFirstCycles f N ↔ koszulFirstCycleCondition f N x := by
  rw [koszulFirstCycles, koszulFirstCycleCondition_iff_mem_ker]

/-- An element of the first-cycle submodule satisfies the pairwise Koszul cycle condition. -/
theorem koszulFirstCycleCondition_of_mem {x : Fin n → N} (hx : x ∈ koszulFirstCycles f N) :
    koszulFirstCycleCondition f N x :=
  (mem_koszulFirstCycles_iff f N x).1 hx

/-- The diagonal linear map `x ↦ (f₁x, …, fₙx)` landing in the ambient tuple module. -/
def koszulDiagonalLinearMap : N →ₗ[R] Fin n → N :=
  LinearMap.pi fun i ↦ DistribSMul.toLinearMap R N (f i)

/-- The explicit three-term Koszul bridge model with coefficients in `N`,
`N ⟶ N^n ⟶ N^(n × n)`, whose homology presents the owner `H₁(N, f_•)`. -/
def koszulH1ModelShortComplex : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (koszulDiagonalLinearMap f N) (koszulFirstCycleMap f N) <| by
    ext x ij
    change f ij.1 • (f ij.2 • x) - f ij.2 • (f ij.1 • x) = 0
    rw [smul_smul, smul_smul, mul_comm (f ij.1) (f ij.2), sub_self]

/-- The source-facing first Koszul homology object `H₁(N, f_•)`, given as the quotient
`ker / im` of the three-term model `N ⟶ N^n ⟶ N^(n × n)`. -/
abbrev koszulH1 : ModuleCat R :=
  (koszulH1ModelShortComplex f N).homology

/-- The source-facing owner `koszulH1 f N` vanishes exactly when the chapter's canonical
degree-`1` Koszul homology with coefficients in `N` vanishes. -/
theorem isZero_koszulH1_iff_isZero_koszulComplexWithModule_homology :
    IsZero (koszulH1 f N) ↔ IsZero ((koszulComplexWithModule f N).homology 1) := by
  sorry

/-- The source-facing owner `koszulH1 f N` is the vanishing predicate used by the chapter owner
`RingTheory.Sequence.IsH1RegularOn`. -/
theorem isH1RegularOn_iff_isZero_koszulH1 :
    RingTheory.Sequence.IsH1RegularOn N f ↔ IsZero (koszulH1 f N) := by
  sorry

/-- The diagonal tuple attached to an element of `N` is a degree-one Koszul cycle. -/
theorem koszulDiagonalTuple_mem_firstCycles (x : N) :
    koszulFirstCycleCondition f N (fun i : Fin n ↦ f i • x) := by
  rw [← mem_koszulFirstCycles_iff]
  rw [koszulFirstCycles, LinearMap.mem_ker]
  ext ij
  change f ij.1 • (f ij.2 • x) - f ij.2 • (f ij.1 • x) = 0
  rw [smul_smul, smul_smul, mul_comm (f ij.1) (f ij.2), sub_self]

/-- The diagonal linear map lands in the first-cycle submodule. -/
theorem koszulDiagonalLinearMap_mem_firstCycles (x : N) :
    koszulDiagonalLinearMap f N x ∈ koszulFirstCycles f N := by
  simpa [koszulDiagonalLinearMap] using
    (mem_koszulFirstCycles_iff f N (koszulDiagonalLinearMap f N x)).2
      (koszulDiagonalTuple_mem_firstCycles f N x)

/-- The diagonal map `x ↦ (f₁x, …, fₙx)` from `N` into the first-cycle module. -/
abbrev koszulDiagonalMap : N →ₗ[R] koszulFirstCycles f N :=
  (koszulH1ModelShortComplex f N).moduleCatToCycles

/-- The explicit quotient presentation of `H₁(N, f_•)`. This remains a bridge/view; the public
owner is `koszulH1 f N`. -/
abbrev koszulH1Presentation :=
  (koszulH1ModelShortComplex f N).moduleCatLeftHomologyData.H

/-- The canonical comparison from the owner `koszulH1 f N` to its quotient presentation. -/
noncomputable abbrev koszulH1IsoPresentation :
    koszulH1 f N ≅ ModuleCat.of R (koszulH1Presentation f N) :=
  (koszulH1ModelShortComplex f N).moduleCatHomologyIso

/-- The free-module map determined by a tuple `(x₁, …, xₙ)` in `N^n`. -/
def koszulTupleLinearMap (x : Fin n → N) : (Fin n → R) →ₗ[R] N :=
  ∑ i : Fin n, (LinearMap.proj i).smulRight (x i)

-- Proof sketch: each generator `fᵢ eⱼ - fⱼ eᵢ` of the relation submodule is sent to
-- `fᵢ • xⱼ - fⱼ • xᵢ`, which vanishes because `x` satisfies the cycle condition.
/-- A first cycle induces a linear map on the relation module of Lemma `15.90.5`. -/
theorem idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap
    {x : Fin n → N}
    (hx : koszulFirstCycleCondition f N x) :
    idealGeneratorRelationSubmodule f ≤
      LinearMap.ker (koszulTupleLinearMap N x) := sorry

/-- A first cycle determines a linear map from the relation module of Lemma `15.90.5` to `N`. -/
def koszulCycleToRelationModuleHom
    (x : koszulFirstCycles f N) :
    idealGeneratorRelationModule f →ₗ[R] N :=
  (idealGeneratorRelationSubmodule f).liftQ
    (koszulTupleLinearMap N x.1)
    (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
      (koszulFirstCycleCondition_of_mem f N x.2))

-- Proof sketch: the assignment `x ↦ (M → N)` is linear because the induced map on the free
-- module depends linearly on the tuple entries, and passage to the quotient preserves linearity.
/-- The construction sending a first cycle to a map from the relation module is additive. -/
theorem koszulCycleToRelationModuleHom_map_add
    (x y : koszulFirstCycles f N) :
    koszulCycleToRelationModuleHom f N (x + y) =
      koszulCycleToRelationModuleHom f N x +
        koszulCycleToRelationModuleHom f N y := sorry

-- Proof sketch: the induced map on the relation module scales pointwise with the tuple, so the
-- assignment is linear in the scalar parameter as well.
/-- The construction sending a first cycle to a map from the relation module is `R`-linear. -/
theorem koszulCycleToRelationModuleHom_map_smul
    (a : R) (x : koszulFirstCycles f N) :
    koszulCycleToRelationModuleHom f N (a • x) =
      a • koszulCycleToRelationModuleHom f N x := sorry

-- Proof sketch: two first cycles induce maps `K → N`, and restricting the sum of their maps from
-- the relation module agrees with the sum of the restrictions.
/-- The canonical map from first cycles to `Hom_R(K, N)` is additive. -/
theorem koszulCyclesToKernelHom_map_add
    (x y : koszulFirstCycles f N) :
    (koszulCycleToRelationModuleHom f N (x + y)).comp
        (idealGeneratorRelationKernel f).subtype =
      (koszulCycleToRelationModuleHom f N x).comp
          (idealGeneratorRelationKernel f).subtype +
        (koszulCycleToRelationModuleHom f N y).comp
          (idealGeneratorRelationKernel f).subtype := sorry

-- Proof sketch: scalar multiplication commutes with restricting the induced map from the relation
-- module to the kernel `K`.
/-- The canonical map from first cycles to `Hom_R(K, N)` is `R`-linear. -/
theorem koszulCyclesToKernelHom_map_smul
    (a : R) (x : koszulFirstCycles f N) :
    (koszulCycleToRelationModuleHom f N (a • x)).comp
        (idealGeneratorRelationKernel f).subtype =
      a •
        (koszulCycleToRelationModuleHom f N x).comp
          (idealGeneratorRelationKernel f).subtype := sorry

/-- The map from first cycles to `Hom_R(K, N)`, where `K` is the kernel from Lemma `15.90.5`. -/
def koszulCyclesToKernelHom :
    koszulFirstCycles f N →ₗ[R]
      (idealGeneratorRelationKernel f →ₗ[R] N) where
  toFun x :=
    (koszulCycleToRelationModuleHom f N x).comp
      (idealGeneratorRelationKernel f).subtype
  map_add' := koszulCyclesToKernelHom_map_add f N
  map_smul' := koszulCyclesToKernelHom_map_smul f N

-- Proof sketch: the tuple `i ↦ fᵢ x` defines a map from the relation module that factors through
-- the canonical surjection to the ideal `(f₁, …, fₙ)`, so its restriction to the kernel `K`
-- vanishes.
/-- Diagonal tuples induce the zero map on the kernel `K` of Lemma `15.90.5`. -/
theorem koszulDiagonalMap_mem_ker_cyclesToKernelHom
    (x : N) :
    koszulCyclesToKernelHom f N (koszulDiagonalMap f N x) = 0 := sorry

-- Proof sketch: every element of the range of the diagonal map is represented by some tuple
-- `i ↦ fᵢ x`, and the previous lemma shows that such tuples are sent to zero on `K`.
/-- The diagonal image is contained in the kernel of the canonical map to `Hom_R(K, N)`. -/
theorem koszulDiagonalMap_le_ker_cyclesToKernelHom :
    LinearMap.range (koszulDiagonalMap f N) ≤ LinearMap.ker (koszulCyclesToKernelHom f N) :=
  sorry

/-- The canonical map from the cycle-quotient presentation in degree one to `Hom_R(K, N)`. -/
def koszulH1PresentationToHomKernel :
    koszulH1Presentation f N →ₗ[R]
      (idealGeneratorRelationKernel f →ₗ[R] N) :=
  (LinearMap.range (koszulDiagonalMap f N)).liftQ
    (koszulCyclesToKernelHom f N)
    (koszulDiagonalMap_le_ker_cyclesToKernelHom f N)

/-- The canonical short complex `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0` for
`I = Ideal.span (Set.range f)`. -/
private def idealSpanQuotientShortComplex :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (Ideal.span (Set.range f)).subtype
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      exact eq_zero_iff_mem.mpr x.2)

-- Proof sketch: this is the standard short exact sequence attached to the quotient map
-- `R → R ⧸ Ideal.span (Set.range f)`.
/-- The ideal quotient short complex `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0` is short exact. -/
private theorem idealSpanQuotientShortComplex_shortExact :
    (idealSpanQuotientShortComplex f).ShortExact := by
  sorry

/-- Evaluating an `R`-linear map `I → N` on the generators `fᵢ` gives a degree-one Koszul cycle. -/
def idealSpanHomToKoszulFirstCycles :
    ((Ideal.span (Set.range f)) →ₗ[R] N) →ₗ[R] koszulFirstCycles f N where
  toFun φ :=
    ⟨fun i ↦ φ ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩, by
      rw [mem_koszulFirstCycles_iff]
      intro i j
      rw [← φ.map_smul, ← φ.map_smul]
      apply congrArg φ
      apply Subtype.ext
      simp [smul_eq_mul, mul_comm]⟩
  map_add' φ ψ := by
    ext i
    simp
  map_smul' a φ := by
    ext i
    simp

/-- The map `N → Hom_R(I, N)` induced by the inclusion `I ↪ R`, sending `x` to
`(a ↦ a • x)`. -/
def spanToIdealSpanHom :
    N →ₗ[R] ((Ideal.span (Set.range f)) →ₗ[R] N) where
  toFun x :=
    { toFun a := (a : R) • x
      map_add' a b := by
        simp [add_smul]
      map_smul' r a := by
        simp [smul_smul] }
  map_add' x y := by
    ext a
    simp [smul_add]
  map_smul' a x := by
    ext b
    simp [smul_smul, mul_comm]

/-- The map `Hom_R(I, N) → koszulH1Presentation f N` induced by evaluation on the generators
`fᵢ`, modulo diagonal boundaries. -/
def idealSpanHomToKoszulH1Presentation :
    ((Ideal.span (Set.range f)) →ₗ[R] N) →ₗ[R] koszulH1Presentation f N :=
  (LinearMap.range (koszulDiagonalMap f N)).mkQ.comp (idealSpanHomToKoszulFirstCycles f N)

/-- The map `N → Hom_R(I, N)` identifies with the diagonal map after passing to the cycle
presentation. -/
theorem idealSpanHomToKoszulH1Presentation_comp_spanToIdealSpanHom :
    idealSpanHomToKoszulH1Presentation f N ∘ₗ spanToIdealSpanHom f N = 0 := by
  sorry

/-- The connecting map `Hom_R(I, N) → Ext¹_R(R / I, N)` for the canonical quotient sequence
`0 ⟶ I ⟶ R ⟶ R / I ⟶ 0`. -/
noncomputable def idealSpanHomToExt :
    ((Ideal.span (Set.range f)) →ₗ[R] N) →ₗ[R]
      Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1 :=
  let hS := idealSpanQuotientShortComplex_shortExact f
  (hS.extClass.precompOfLinear R (ModuleCat.of R N) (Nat.add_zero 1)) ∘ₗ
    (((Ext.linearEquiv₀ :
        Ext (ModuleCat.of R (Ideal.span (Set.range f))) (ModuleCat.of R N) 0 ≃ₗ[R]
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N)).symm.toLinearMap) ∘ₗ
      ((ModuleCat.homLinearEquiv :
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
            ((Ideal.span (Set.range f)) →ₗ[R] N)).symm.toLinearMap))

-- Proof sketch: this is the degree-`1` connecting map in the contravariant long exact Ext
-- sequence for `0 → I → R → R / I → 0`; surjectivity follows because `Ext¹_R(R, N) = 0`.
/-- The connecting map `Hom_R(I, N) → Ext¹_R(R / I, N)` for the quotient sequence is surjective. -/
theorem idealSpanHomToExt_surjective :
    Function.Surjective (idealSpanHomToExt f N) := by
  sorry

-- Proof sketch: if two maps `I → N` differ by multiplication with an element of `N`, they define
-- the same class in `koszulH1Presentation f N`, and the only additional relations come from the
-- kernel of the connecting map above.
/-- The source-facing map `Hom_R(I, N) → koszulH1Presentation f N` kills the kernel of the
connecting map to `Ext¹`. -/
theorem ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation :
    LinearMap.ker (idealSpanHomToExt f N) ≤
      LinearMap.ker (idealSpanHomToKoszulH1Presentation f N) := by
  sorry

/-- The quotient of `Hom_R(I, N)` by the kernel of the connecting map maps canonically to the
source-facing degree-one Koszul quotient. -/
noncomputable def idealSpanHomKerToKoszulH1Presentation :
    (((Ideal.span (Set.range f)) →ₗ[R] N) ⧸ LinearMap.ker (idealSpanHomToExt f N)) →ₗ[R]
      koszulH1Presentation f N :=
  (LinearMap.ker (idealSpanHomToExt f N)).liftQ
    (idealSpanHomToKoszulH1Presentation f N)
    (ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation f N)

/-- The canonical left map
`Ext¹_R(R / Ideal.span (Set.range f), N) ⟶ koszulH1Presentation f N`. -/
noncomputable def koszulExtToH1Presentation :
    Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1 →ₗ[R]
      koszulH1Presentation f N :=
  idealSpanHomKerToKoszulH1Presentation f N ∘ₗ
    ((idealSpanHomToExt f N).quotKerEquivOfSurjective
      (idealSpanHomToExt_surjective f N)).symm.toLinearMap

-- Proof sketch: a map `I → N` induces a tuple map on the relation module that factors through
-- `I`; its restriction to the kernel `K` is therefore zero, and the factorization survives the
-- quotient by boundaries and the identification with `Ext¹`.
/-- The canonical left map to `koszulH1Presentation f N` composes trivially with the map to
`Hom_R(K, N)`. -/
theorem koszulH1PresentationToHomKernel_comp_koszulExtToH1Presentation :
    (koszulH1PresentationToHomKernel f N).comp (koszulExtToH1Presentation f N) = 0 := by
  sorry

/-- The canonical map `H₁(N, f_•) ⟶ Hom_R(K, N)` induced from the quotient presentation. -/
noncomputable def koszulH1ToHomKernel :
    koszulH1 f N ⟶ ModuleCat.of R (idealGeneratorRelationKernel f →ₗ[R] N) :=
  (koszulH1IsoPresentation f N).hom ≫ ModuleCat.ofHom (koszulH1PresentationToHomKernel f N)

/-- The canonical map `Hom_R(I, N) ⟶ H₁(N, f_•)` induced from the quotient presentation. -/
noncomputable def idealSpanHomToKoszulH1 :
    ModuleCat.of R (((Ideal.span (Set.range f)) →ₗ[R] N)) ⟶ koszulH1 f N :=
  ModuleCat.ofHom (idealSpanHomToKoszulH1Presentation f N) ≫ (koszulH1IsoPresentation f N).inv

/-- The canonical left map `Ext¹_R(R / I, N) ⟶ H₁(N, f_•)`. -/
noncomputable def koszulExtToH1 :
    ModuleCat.of R
        (Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1) ⟶
      koszulH1 f N :=
  ModuleCat.ofHom (koszulExtToH1Presentation f N) ≫ (koszulH1IsoPresentation f N).inv

/-- The owner-level left map `Ext¹_R(R / I, N) ⟶ H₁(N, f_•)` composes trivially with the map to
`Hom_R(K, N)`. -/
theorem koszulH1ToHomKernel_comp_koszulExtToH1 :
    koszulExtToH1 f N ≫ koszulH1ToHomKernel f N = 0 := by
  sorry

/-- The canonical short complex
`0 ⟶ Ext¹_R(R / Ideal.span (Set.range f), N) ⟶ koszulH1 f N ⟶ Hom_R(K, N)`. -/
def koszulH1ShortComplex :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (koszulExtToH1 f N)
    (koszulH1ToHomKernel f N)
    (koszulH1ToHomKernel_comp_koszulExtToH1 f N)

-- Proof sketch: compare the quotient description of `H₁` with the exact sequence
-- `Hom_R(I, N) → Ext¹_R(R / I, N)` from the quotient short exact sequence
-- `0 → I → R → R / I → 0`, and then use Lemma `15.90.5` to identify the cokernel term with
-- `Hom_R(K, N)`.
/-- Lemma 15.90.6: for
`I = Ideal.span (Set.range f)` and `K = idealGeneratorRelationKernel f`, the quotient
presentation short complex
`0 ⟶ Ext¹_R(R / I, N) ⟶ koszulH1 f N ⟶ Hom_R(K, N) ⟶ 0`
is short exact. -/
theorem koszulH1ShortComplex_shortExact :
    (koszulH1ShortComplex f N).ShortExact := by
  sorry

end
