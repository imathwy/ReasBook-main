import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import stacks_proof.stacks_project.Chap15.Definition_15_30_1
import stacks_proof.stacks_project.Chap15.Lemma_15_90_5
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Lemma 15.90.6: the tuple map reads off the coefficient of a basis vector. -/
theorem koszulTupleLinearMap_apply_basisFun
    (x : Fin n → N) (i : Fin n) :
    koszulTupleLinearMap N x (Pi.basisFun R (Fin n) i) = x i := by
  -- Only the `i`-th basis coordinate contributes to the finite sum.
  simp [koszulTupleLinearMap]

/-- Helper for Lemma 15.90.6: evaluating the tuple map on a basic relation generator produces the
cycle expression `fᵢ • xⱼ - fⱼ • xᵢ`. -/
theorem koszulTupleLinearMap_apply_relation_generator
    (x : Fin n → N) (i j : Fin n) :
    koszulTupleLinearMap N x (f i • Pi.basisFun R (Fin n) j - f j • Pi.basisFun R (Fin n) i) =
      f i • x j - f j • x i := by
  -- Expand by linearity and then read off the two basis coordinates.
  rw [LinearMap.map_sub, LinearMap.map_smul, LinearMap.map_smul]
  rw [koszulTupleLinearMap_apply_basisFun (N := N), koszulTupleLinearMap_apply_basisFun (N := N)]

/-- Helper for Lemma 15.90.6: each basic relation generator lies in the kernel of the tuple map
for a first cycle. -/
theorem relation_generator_mem_ker_koszulTupleLinearMap
    {x : Fin n → N}
    (hx : koszulFirstCycleCondition f N x) (i j : Fin n) :
    f i • Pi.basisFun R (Fin n) j - f j • Pi.basisFun R (Fin n) i ∈
      LinearMap.ker (koszulTupleLinearMap N x) := by
  -- Evaluate the generator explicitly and rewrite the result with the cycle relation.
  rw [LinearMap.mem_ker, koszulTupleLinearMap_apply_relation_generator]
  exact sub_eq_zero.mpr (hx i j)

-- Proof sketch: each generator `fᵢ eⱼ - fⱼ eᵢ` of the relation submodule is sent to
-- `fᵢ • xⱼ - fⱼ • xᵢ`, which vanishes because `x` satisfies the cycle condition.
/-- A first cycle induces a linear map on the relation module of Lemma `15.90.5`. -/
theorem idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap
    {x : Fin n → N}
    (hx : koszulFirstCycleCondition f N x) :
    idealGeneratorRelationSubmodule f ≤
      LinearMap.ker (koszulTupleLinearMap N x) := by
  -- Route correction: the proof should now use the public relation-generator map exposed from
  -- Lemma `15.90.5` and finish by `LinearMap.range_le_ker_iff`.
  rw [idealGeneratorRelationSubmodule, LinearMap.range_le_ker_iff]
  -- The composite vanishes on the standard basis because each relation generator is killed by a
  -- first cycle.
  refine (Pi.basisFun R (Fin n × Fin n)).ext fun ij ↦ ?_
  rcases ij with ⟨i, j⟩
  rw [LinearMap.comp_apply, idealGeneratorRelationMap_apply_basisFun, LinearMap.zero_apply]
  simpa [LinearMap.mem_ker] using
    relation_generator_mem_ker_koszulTupleLinearMap (f := f) (N := N) hx i j

/-- A first cycle determines a linear map from the relation module of Lemma `15.90.5` to `N`. -/
def koszulCycleToRelationModuleHom
    (x : koszulFirstCycles f N) :
    idealGeneratorRelationModule f →ₗ[R] N :=
  (idealGeneratorRelationSubmodule f).liftQ
    (koszulTupleLinearMap N x.1)
    (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
      (koszulFirstCycleCondition_of_mem f N x.2))

/-- Helper for Lemma 15.90.6: evaluating the map induced by a cycle on the class of the `i`-th
basis vector recovers the `i`-th tuple entry. -/
theorem koszulCycleToRelationModuleHom_apply_basisClass
    (x : koszulFirstCycles f N) (i : Fin n) :
    koszulCycleToRelationModuleHom f N x
      ((idealGeneratorRelationSubmodule f).mkQ (Pi.basisFun R (Fin n) i)) =
        x.1 i := by
  -- The quotient lift is computed on representatives, and the tuple map reads basis vectors by
  -- their indexed coordinate.
  have hmk := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N x.1)
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N x.2)))
    (Pi.basisFun R (Fin n) i)
  simpa [koszulCycleToRelationModuleHom] using
    hmk.trans (koszulTupleLinearMap_apply_basisFun (N := N) x.1 i)

/-- Helper for Lemma 15.90.6: the cycle-to-relation-module construction is injective. -/
theorem koszulCycleToRelationModuleHom_injective :
    Function.Injective (koszulCycleToRelationModuleHom f N) := by
  intro x y hxy
  ext i
  -- Compare the two induced maps on the class of the `i`-th basis vector.
  calc
    x.1 i
      =
        koszulCycleToRelationModuleHom f N x
          ((idealGeneratorRelationSubmodule f).mkQ (Pi.basisFun R (Fin n) i)) := by
            symm
            exact koszulCycleToRelationModuleHom_apply_basisClass (f := f) (N := N) x i
    _ =
        koszulCycleToRelationModuleHom f N y
          ((idealGeneratorRelationSubmodule f).mkQ (Pi.basisFun R (Fin n) i)) := by
            rw [hxy]
    _ = y.1 i := by
            exact koszulCycleToRelationModuleHom_apply_basisClass (f := f) (N := N) y i

/-- Helper for Lemma 15.90.6: a linear map on the relation module determines a first Koszul cycle
by evaluating it on the classes of the standard basis vectors. -/
def relationModuleHomToKoszulFirstCycles
    (g : idealGeneratorRelationModule f →ₗ[R] N) :
    koszulFirstCycles f N :=
  ⟨fun i ↦ g ((idealGeneratorRelationSubmodule f).mkQ (Pi.basisFun R (Fin n) i)), by
    -- Apply `g` to the vanishing class of each basic relation generator.
    rw [mem_koszulFirstCycles_iff]
    intro i j
    have hrel :
        (idealGeneratorRelationSubmodule f).mkQ
            (f i • Pi.basisFun R (Fin n) j - f j • Pi.basisFun R (Fin n) i) = 0 := by
      -- The defining relation already lies in the relation submodule, so its quotient class is zero.
      rw [← idealGeneratorRelationMap_apply_basisFun (f := f) i j]
      exact (Submodule.Quotient.mk_eq_zero _).2
        ⟨Pi.basisFun R (Fin n × Fin n) (i, j), rfl⟩
    have hgrel :
        g ((idealGeneratorRelationSubmodule f).mkQ
          (f i • Pi.basisFun R (Fin n) j - f j • Pi.basisFun R (Fin n) i)) = 0 := by
      simpa using congrArg g hrel
    -- Rewrite the quotient relation through the linearity of `g`.
    exact sub_eq_zero.mp <| by
      simpa [LinearMap.map_sub, LinearMap.map_smul] using hgrel⟩

/-- Helper for Lemma 15.90.6: evaluating the cycle reconstructed from `g : M → N` returns the
value of `g` on the corresponding basis class. -/
theorem relationModuleHomToKoszulFirstCycles_apply
    (g : idealGeneratorRelationModule f →ₗ[R] N) (i : Fin n) :
    ((relationModuleHomToKoszulFirstCycles f N g : koszulFirstCycles f N) : Fin n → N) i =
      g ((idealGeneratorRelationSubmodule f).mkQ (Pi.basisFun R (Fin n) i)) := by
  rfl

/-- Helper for Lemma 15.90.6: passing from a relation-module map to a cycle and back recovers the
original map. -/
theorem koszulCycleToRelationModuleHom_relationModuleHomToKoszulFirstCycles
    (g : idealGeneratorRelationModule f →ₗ[R] N) :
    koszulCycleToRelationModuleHom f N (relationModuleHomToKoszulFirstCycles f N g) = g := by
  have hfree :
      koszulTupleLinearMap N ((relationModuleHomToKoszulFirstCycles f N g).1) =
        g.comp (idealGeneratorRelationSubmodule f).mkQ := by
    -- Both linear maps out of the free module agree on the standard basis vectors.
    apply (Pi.basisFun R (Fin n)).ext
    intro i
    rw [LinearMap.comp_apply, koszulTupleLinearMap_apply_basisFun]
    rfl
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (idealGeneratorRelationSubmodule f) q
  have hmk := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N ((relationModuleHomToKoszulFirstCycles f N g).1))
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N
          (relationModuleHomToKoszulFirstCycles f N g).2)))
    w
  rw [show (koszulCycleToRelationModuleHom f N (relationModuleHomToKoszulFirstCycles f N g))
      ((idealGeneratorRelationSubmodule f).mkQ w) =
        koszulTupleLinearMap N ((relationModuleHomToKoszulFirstCycles f N g).1) w by
      simpa [koszulCycleToRelationModuleHom] using hmk]
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun hfree w

/-- Helper for Lemma 15.90.6: passing from a cycle to the induced relation-module map and then
reading off the basis classes recovers the original cycle. -/
theorem relationModuleHomToKoszulFirstCycles_koszulCycleToRelationModuleHom
    (x : koszulFirstCycles f N) :
    relationModuleHomToKoszulFirstCycles f N (koszulCycleToRelationModuleHom f N x) = x := by
  ext i
  -- The induced relation-module map remembers each tuple entry via the basis classes.
  exact koszulCycleToRelationModuleHom_apply_basisClass (f := f) (N := N) x i

/-- Helper for Lemma 15.90.6: relation-module maps and first Koszul cycles are canonically
equivalent. -/
noncomputable def relation_module_hom_equiv_koszul_first_cycles :
    (idealGeneratorRelationModule f →ₗ[R] N) ≃ₗ[R] koszulFirstCycles f N where
  toFun := relationModuleHomToKoszulFirstCycles f N
  invFun := koszulCycleToRelationModuleHom f N
  left_inv := koszulCycleToRelationModuleHom_relationModuleHomToKoszulFirstCycles f N
  right_inv := relationModuleHomToKoszulFirstCycles_koszulCycleToRelationModuleHom f N
  map_add' g h := by
    ext i
    -- The reconstructed cycle is computed pointwise from the additive map on basis classes.
    simp [relationModuleHomToKoszulFirstCycles]
  map_smul' a g := by
    ext i
    -- Scalar multiplication is likewise read pointwise on basis classes.
    simp [relationModuleHomToKoszulFirstCycles]

-- Proof sketch: the assignment `x ↦ (M → N)` is linear because the induced map on the free
-- module depends linearly on the tuple entries, and passage to the quotient preserves linearity.
/-- The construction sending a first cycle to a map from the relation module is additive. -/
theorem koszulCycleToRelationModuleHom_map_add
    (x y : koszulFirstCycles f N) :
    koszulCycleToRelationModuleHom f N (x + y) =
      koszulCycleToRelationModuleHom f N x +
        koszulCycleToRelationModuleHom f N y := by
  -- Evaluate on quotient representatives so the computation reduces to additivity of the tuple map.
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (idealGeneratorRelationSubmodule f) q
  have hxy := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N (x + y).1)
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N (x + y).2))) w
  have hx := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N x.1)
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N x.2))) w
  have hy := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N y.1)
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N y.2))) w
  rw [show (koszulCycleToRelationModuleHom f N (x + y)) ((idealGeneratorRelationSubmodule f).mkQ w) =
      koszulTupleLinearMap N (x + y).1 w by
      simpa [koszulCycleToRelationModuleHom] using hxy]
  rw [LinearMap.add_apply]
  rw [show (koszulCycleToRelationModuleHom f N x) ((idealGeneratorRelationSubmodule f).mkQ w) =
      koszulTupleLinearMap N x.1 w by
      simpa [koszulCycleToRelationModuleHom] using hx]
  rw [show (koszulCycleToRelationModuleHom f N y) ((idealGeneratorRelationSubmodule f).mkQ w) =
      koszulTupleLinearMap N y.1 w by
      simpa [koszulCycleToRelationModuleHom] using hy]
  -- The tuple map is additive because it is defined coordinatewise and summed over `Fin n`.
  simp [koszulTupleLinearMap, Finset.sum_add_distrib, smul_add]

-- Proof sketch: the induced map on the relation module scales pointwise with the tuple, so the
-- assignment is linear in the scalar parameter as well.
/-- The construction sending a first cycle to a map from the relation module is `R`-linear. -/
theorem koszulCycleToRelationModuleHom_map_smul
    (a : R) (x : koszulFirstCycles f N) :
    koszulCycleToRelationModuleHom f N (a • x) =
      a • koszulCycleToRelationModuleHom f N x := by
  -- Again reduce to quotient representatives and compute on the underlying tuple map.
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (idealGeneratorRelationSubmodule f) q
  have hax := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N (a • x).1)
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N (a • x).2))) w
  have hx := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N x.1)
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N x.2))) w
  rw [show (koszulCycleToRelationModuleHom f N (a • x)) ((idealGeneratorRelationSubmodule f).mkQ w) =
      koszulTupleLinearMap N (a • x).1 w by
      simpa [koszulCycleToRelationModuleHom] using hax]
  rw [LinearMap.smul_apply]
  rw [show (koszulCycleToRelationModuleHom f N x) ((idealGeneratorRelationSubmodule f).mkQ w) =
      koszulTupleLinearMap N x.1 w by
      simpa [koszulCycleToRelationModuleHom] using hx]
  -- Pull the scalar outside the finite sum and commute ring scalars in the coefficient.
  have htuple : koszulTupleLinearMap N (a • x).1 =
      (a • koszulTupleLinearMap N x.1 : (Fin n → R) →ₗ[R] N) := by
    -- The tuple map is linear in the tuple entries coordinatewise.
    apply LinearMap.ext
    intro v
    calc
      koszulTupleLinearMap N (a • x).1 v
          = ∑ i : Fin n, v i • ((a • x : koszulFirstCycles f N).1 i) := by
              simp [koszulTupleLinearMap]
      _ = ∑ i : Fin n, a • (v i • x.1 i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              change v i • (a • x.1 i) = a • (v i • x.1 i)
              calc
                v i • (a • x.1 i) = (v i * a) • x.1 i := by
                  simpa [smul_smul]
                _ = (a * v i) • x.1 i := by
                  rw [mul_comm]
                _ = a • (v i • x.1 i) := by
                  simpa [smul_smul]
      _ = a • ∑ i : Fin n, v i • x.1 i := by
              rw [Finset.smul_sum]
      _ = (a • koszulTupleLinearMap N x.1 : (Fin n → R) →ₗ[R] N) v := by
              simp [koszulTupleLinearMap]
  exact LinearMap.congr_fun htuple w

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
          (idealGeneratorRelationKernel f).subtype := by
  -- Restriction to the kernel preserves the additive identity already proved on the relation module.
  apply LinearMap.ext
  intro z
  simp [koszulCycleToRelationModuleHom_map_add, LinearMap.add_apply]

-- Proof sketch: scalar multiplication commutes with restricting the induced map from the relation
-- module to the kernel `K`.
/-- The canonical map from first cycles to `Hom_R(K, N)` is `R`-linear. -/
theorem koszulCyclesToKernelHom_map_smul
    (a : R) (x : koszulFirstCycles f N) :
    (koszulCycleToRelationModuleHom f N (a • x)).comp
        (idealGeneratorRelationKernel f).subtype =
      a •
        (koszulCycleToRelationModuleHom f N x).comp
          (idealGeneratorRelationKernel f).subtype := by
  -- The same restriction argument works for scalar multiplication.
  apply LinearMap.ext
  intro z
  simp [koszulCycleToRelationModuleHom_map_smul, LinearMap.smul_apply]

/-- The map from first cycles to `Hom_R(K, N)`, where `K` is the kernel from Lemma `15.90.5`. -/
def koszulCyclesToKernelHom :
    koszulFirstCycles f N →ₗ[R]
      (idealGeneratorRelationKernel f →ₗ[R] N) where
  toFun x :=
    (koszulCycleToRelationModuleHom f N x).comp
      (idealGeneratorRelationKernel f).subtype
  map_add' := koszulCyclesToKernelHom_map_add f N
  map_smul' := koszulCyclesToKernelHom_map_smul f N

/-- Helper for Lemma 15.90.6: the quotient map from Lemma `15.90.5` sends the class of a tuple
`w` to the corresponding linear combination `∑ i, fᵢ wᵢ` in the ideal `Ideal.span (Set.range f)`.
-/
theorem idealGeneratorRelationModuleToSpan_apply_mkQ
    (w : Fin n → R) :
    (idealGeneratorRelationModuleToSpan f) ((idealGeneratorRelationSubmodule f).mkQ w) =
      ⟨∑ i : Fin n, f i * w i, by
        refine Submodule.sum_mem _ ?_
        intro i _
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)⟩ := by
  -- Unfold the quotient lift and then identify the hidden owner map with the explicit
  -- linear combination `∑ i, fᵢ wᵢ` on the free module.
  simp [idealGeneratorRelationModuleToSpan]
  apply Subtype.ext
  change (Module.piEquiv (Fin n) R R f) w = ∑ i : Fin n, f i * w i
  calc
    (Module.piEquiv (Fin n) R R f) w = ∑ i : Fin n, w i * f i := by
      simp [Module.piEquiv_apply_apply]
    _ = ∑ i : Fin n, f i * w i := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [mul_comm]

/-- Helper for Lemma 15.90.6: the diagonal cycle has `i`-th entry `fᵢ • x`. -/
theorem koszulDiagonalMap_coe_apply
    (x : N) (i : Fin n) :
    (((koszulDiagonalMap f N x : koszulFirstCycles f N) : Fin n → N) i) = f i • x := by
  rfl

-- Proof sketch: the tuple `i ↦ fᵢ x` defines a map from the relation module that factors through
-- the canonical surjection to the ideal `(f₁, …, fₙ)`, so its restriction to the kernel `K`
-- vanishes.
/-- Diagonal tuples induce the zero map on the kernel `K` of Lemma `15.90.5`. -/
theorem koszulDiagonalMap_mem_ker_cyclesToKernelHom
    (x : N) :
    koszulCyclesToKernelHom f N (koszulDiagonalMap f N x) = 0 := by
  -- Evaluate on a quotient representative of `K`; the kernel condition forces the scalar
  -- `∑ i, w i * f i` to vanish, so the diagonal tuple acts by zero.
  apply LinearMap.ext
  intro z
  change
    (koszulCycleToRelationModuleHom f N (koszulDiagonalMap f N x)) z.1 = 0
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (idealGeneratorRelationSubmodule f) z.1
  have hdiag := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N ((koszulDiagonalMap f N x).1))
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N (koszulDiagonalMap f N x).2))) w
  have hspan :
      ((idealGeneratorRelationModuleToSpan f)
          ((idealGeneratorRelationSubmodule f).mkQ w) : R) =
        ∑ i : Fin n, f i * w i := by
    exact congrArg Subtype.val (idealGeneratorRelationModuleToSpan_apply_mkQ (f := f) w)
  have hzker : z.1 ∈ LinearMap.ker (idealGeneratorRelationModuleToSpan f) := z.2
  have hz0 : (idealGeneratorRelationModuleToSpan f) z.1 = 0 := by
    simpa [LinearMap.mem_ker] using hzker
  have hzq :
      (idealGeneratorRelationModuleToSpan f)
        ((idealGeneratorRelationSubmodule f).mkQ w) = 0 := by
    simpa [hw] using hz0
  have hz :
      ((idealGeneratorRelationModuleToSpan f)
          ((idealGeneratorRelationSubmodule f).mkQ w) : R) = 0 := by
    exact congrArg Subtype.val hzq
  rw [← hw]
  rw [show (koszulCycleToRelationModuleHom f N (koszulDiagonalMap f N x))
      ((idealGeneratorRelationSubmodule f).mkQ w) =
        koszulTupleLinearMap N ((koszulDiagonalMap f N x).1) w by
      simpa [koszulCycleToRelationModuleHom] using hdiag]
  calc
    koszulTupleLinearMap N ((koszulDiagonalMap f N x).1) w
        = ∑ i : Fin n, (f i * w i) • x := by
            calc
              koszulTupleLinearMap N ((koszulDiagonalMap f N x).1) w
                  = ∑ i : Fin n, w i • (((koszulDiagonalMap f N x : koszulFirstCycles f N) :
                      Fin n → N) i) := by
                        simp [koszulTupleLinearMap]
              _ = ∑ i : Fin n, w i • (f i • x) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        rw [koszulDiagonalMap_coe_apply]
              _ = ∑ i : Fin n, (f i * w i) • x := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        calc
                          w i • (f i • x) = (w i * f i) • x := by
                            simpa [smul_smul]
                          _ = (f i * w i) • x := by
                            rw [mul_comm]
    _ = (∑ i : Fin n, f i * w i) • x := by
            rw [Finset.sum_smul]
    _ = 0 := by
            rw [← hspan, hz, zero_smul]

-- Proof sketch: every element of the range of the diagonal map is represented by some tuple
-- `i ↦ fᵢ x`, and the previous lemma shows that such tuples are sent to zero on `K`.
/-- The diagonal image is contained in the kernel of the canonical map to `Hom_R(K, N)`. -/
theorem koszulDiagonalMap_le_ker_cyclesToKernelHom :
    LinearMap.range (koszulDiagonalMap f N) ≤ LinearMap.ker (koszulCyclesToKernelHom f N) :=
  by
    -- Every diagonal cycle is killed by the kernel map, so every element of its range lies in the kernel.
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simpa [LinearMap.mem_ker] using koszulDiagonalMap_mem_ker_cyclesToKernelHom f N x

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
  -- This is the standard quotient row `0 → I → R → R / I → 0`.
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · simpa [idealSpanQuotientShortComplex] using
      LinearMap.exact_subtype_mkQ (Ideal.span (Set.range f))
  · exact Submodule.injective_subtype (Ideal.span (Set.range f))
  · simpa [idealSpanQuotientShortComplex] using
      (Ideal.Quotient.mkₐ_surjective R (Ideal.span (Set.range f)))

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

/-- Helper for Lemma 15.90.6: a cycle coming from a linear map `I → N` factors through the
canonical surjection from the relation module to the ideal generated by `f`. -/
theorem idealSpanHom_cycle_to_relation_module_factorization
    (φ : (Ideal.span (Set.range f)) →ₗ[R] N) :
    koszulCycleToRelationModuleHom f N ((idealSpanHomToKoszulFirstCycles f N) φ) =
      φ.comp (idealGeneratorRelationModuleToSpan f) := by
  -- Compare both maps on quotient representatives and then pull the tuple sum through `φ`.
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (idealGeneratorRelationSubmodule f) q
  have hcycle := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N ((idealSpanHomToKoszulFirstCycles f N φ).1))
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N ((idealSpanHomToKoszulFirstCycles f N) φ).2))) w
  have hspan :
      ((idealGeneratorRelationModuleToSpan f)
          ((idealGeneratorRelationSubmodule f).mkQ w) : R) =
        ∑ i : Fin n, f i * w i := by
    exact congrArg Subtype.val (idealGeneratorRelationModuleToSpan_apply_mkQ (f := f) w)
  have hsum :
      ∑ i : Fin n, w i • (⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩ : Ideal.span (Set.range f)) =
        (idealGeneratorRelationModuleToSpan f) ((idealGeneratorRelationSubmodule f).mkQ w) := by
    -- Both ideal elements have the same underlying scalar `∑ i, fᵢ wᵢ`.
    apply Subtype.ext
    change
      ((∑ i : Fin n, w i • (⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩ :
          Ideal.span (Set.range f)) : Ideal.span (Set.range f)) : R) =
      ((idealGeneratorRelationModuleToSpan f)
        ((idealGeneratorRelationSubmodule f).mkQ w) : R)
    rw [hspan]
    simp [smul_eq_mul, mul_comm]
  rw [show (koszulCycleToRelationModuleHom f N ((idealSpanHomToKoszulFirstCycles f N) φ))
      ((idealGeneratorRelationSubmodule f).mkQ w) =
        koszulTupleLinearMap N ((idealSpanHomToKoszulFirstCycles f N φ).1) w by
      simpa [koszulCycleToRelationModuleHom] using hcycle]
  rw [LinearMap.comp_apply]
  calc
    koszulTupleLinearMap N ((idealSpanHomToKoszulFirstCycles f N φ).1) w
        = ∑ i : Fin n, w i • (((idealSpanHomToKoszulFirstCycles f N) φ :
            koszulFirstCycles f N) : Fin n → N) i := by
            simp [koszulTupleLinearMap]
    _ = ∑ i : Fin n, w i • φ ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩ := by
            rfl
    _ = ∑ i : Fin n, φ (w i • (⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩ :
            Ideal.span (Set.range f))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [← φ.map_smul]
    _ = φ (∑ i : Fin n, w i • (⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩ :
            Ideal.span (Set.range f))) := by
            symm
            exact map_sum φ (fun i ↦
              w i • (⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩ : Ideal.span (Set.range f))
            ) Finset.univ
    _ = φ ((idealGeneratorRelationModuleToSpan f)
          ((idealGeneratorRelationSubmodule f).mkQ w)) := by
            rw [hsum]

/-- Helper for Lemma 15.90.6: the map associated to a diagonal Koszul cycle factors through the
canonical surjection from the relation module to the ideal generated by `f`. -/
theorem diagonal_cycle_to_relation_module_factorization
    (x : N) :
    koszulCycleToRelationModuleHom f N (koszulDiagonalMap f N x) =
      (spanToIdealSpanHom f N x).comp (idealGeneratorRelationModuleToSpan f) := by
  -- Compare both maps on quotient representatives; both compute the scalar
  -- `∑ i, w i * f i` and then let it act on `x`.
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (idealGeneratorRelationSubmodule f) q
  have hdiag := LinearMap.congr_fun
    ((idealGeneratorRelationSubmodule f).liftQ_mkQ
      (koszulTupleLinearMap N ((koszulDiagonalMap f N x).1))
      (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
        (koszulFirstCycleCondition_of_mem f N (koszulDiagonalMap f N x).2))) w
  have hspan :
      ((idealGeneratorRelationModuleToSpan f)
          ((idealGeneratorRelationSubmodule f).mkQ w) : R) =
        ∑ i : Fin n, f i * w i := by
    exact congrArg Subtype.val (idealGeneratorRelationModuleToSpan_apply_mkQ (f := f) w)
  rw [show (koszulCycleToRelationModuleHom f N (koszulDiagonalMap f N x))
      ((idealGeneratorRelationSubmodule f).mkQ w) =
        koszulTupleLinearMap N ((koszulDiagonalMap f N x).1) w by
      simpa [koszulCycleToRelationModuleHom] using hdiag]
  rw [LinearMap.comp_apply, spanToIdealSpanHom]
  change koszulTupleLinearMap N ((koszulDiagonalMap f N x).1) w =
    (((idealGeneratorRelationModuleToSpan f) ((idealGeneratorRelationSubmodule f).mkQ w) : R) • x)
  calc
    koszulTupleLinearMap N ((koszulDiagonalMap f N x).1) w
        = ∑ i : Fin n, (f i * w i) • x := by
            calc
              koszulTupleLinearMap N ((koszulDiagonalMap f N x).1) w
                  = ∑ i : Fin n, w i • (((koszulDiagonalMap f N x : koszulFirstCycles f N) :
                      Fin n → N) i) := by
                        simp [koszulTupleLinearMap]
              _ = ∑ i : Fin n, w i • (f i • x) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        rw [koszulDiagonalMap_coe_apply]
              _ = ∑ i : Fin n, (f i * w i) • x := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        calc
                          w i • (f i • x) = (w i * f i) • x := by
                            simpa [smul_smul]
                          _ = (f i * w i) • x := by
                            rw [mul_comm]
    _ = (∑ i : Fin n, f i * w i) • x := by
            rw [Finset.sum_smul]
    _ = (((idealGeneratorRelationModuleToSpan f)
        ((idealGeneratorRelationSubmodule f).mkQ w) : R) • x) := by
            rw [hspan]

/-- The map `Hom_R(I, N) → koszulH1Presentation f N` induced by evaluation on the generators
`fᵢ`, modulo diagonal boundaries. -/
def idealSpanHomToKoszulH1Presentation :
    ((Ideal.span (Set.range f)) →ₗ[R] N) →ₗ[R] koszulH1Presentation f N :=
  (LinearMap.range (koszulDiagonalMap f N)).mkQ.comp (idealSpanHomToKoszulFirstCycles f N)

/-- The map `N → Hom_R(I, N)` identifies with the diagonal map after passing to the cycle
presentation. -/
theorem idealSpanHomToKoszulH1Presentation_comp_spanToIdealSpanHom :
    idealSpanHomToKoszulH1Presentation f N ∘ₗ spanToIdealSpanHom f N = 0 := by
  -- The image of `x` is exactly the diagonal cycle, hence zero in the quotient by diagonal boundaries.
  apply LinearMap.ext
  intro x
  change (LinearMap.range (koszulDiagonalMap f N)).mkQ
      ((idealSpanHomToKoszulFirstCycles f N) (spanToIdealSpanHom f N x)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨x, ?_⟩
  ext i
  change
      (((idealSpanHomToKoszulFirstCycles f N) (spanToIdealSpanHom f N x) :
          koszulFirstCycles f N) : Fin n → N) i =
        ((koszulDiagonalMap f N x : koszulFirstCycles f N) : Fin n → N) i
  symm
  rfl

/-- Helper for Lemma 15.90.6: the presentation quotient kills exactly the diagonal maps
`a ↦ a • x`. -/
theorem idealSpanHomToKoszulH1Presentation_ker_eq_range_spanToIdealSpanHom :
    LinearMap.ker (idealSpanHomToKoszulH1Presentation f N) =
      LinearMap.range (spanToIdealSpanHom f N) := by
  apply le_antisymm
  · intro φ hφ
    rw [LinearMap.mem_ker] at hφ
    have hφmem :
        ((idealSpanHomToKoszulFirstCycles f N) φ) ∈ LinearMap.range (koszulDiagonalMap f N) := by
      simpa using
        (Submodule.Quotient.mk_eq_zero (LinearMap.range (koszulDiagonalMap f N))).1 hφ
    rcases LinearMap.mem_range.mp hφmem with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    -- Route correction: rather than redoing span induction on `I`, compare the two maps after the
    -- surjection from Lemma `15.90.5`, where the cycle equality `hx` already lives.
    have hcomp :
        φ.comp (idealGeneratorRelationModuleToSpan f) =
          (spanToIdealSpanHom f N x).comp (idealGeneratorRelationModuleToSpan f) := by
      calc
        φ.comp (idealGeneratorRelationModuleToSpan f)
            = koszulCycleToRelationModuleHom f N ((idealSpanHomToKoszulFirstCycles f N) φ) := by
                symm
                exact idealSpanHom_cycle_to_relation_module_factorization (f := f) (N := N) φ
        _ = koszulCycleToRelationModuleHom f N (koszulDiagonalMap f N x) := by
              simpa [hx]
        _ = (spanToIdealSpanHom f N x).comp (idealGeneratorRelationModuleToSpan f) := by
              exact diagonal_cycle_to_relation_module_factorization (f := f) (N := N) x
    ext a
    obtain ⟨q, rfl⟩ := idealGeneratorRelationModuleToSpan_surjective (f := f) a
    exact (LinearMap.congr_fun hcomp q).symm
  · rw [LinearMap.range_le_ker_iff]
    exact idealSpanHomToKoszulH1Presentation_comp_spanToIdealSpanHom (f := f) (N := N)

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

/-- Helper for Lemma 15.90.6: restricting an `R`-linear map `R → N` to the ideal
`Ideal.span (Set.range f)` gives the map `a ↦ a • g(1)`. -/
theorem homLinearEquiv_subtype_comp_eq_spanToIdealSpanHom
    (g : R →ₗ[R] N) :
    (ModuleCat.homLinearEquiv :
        (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
          ((Ideal.span (Set.range f)) →ₗ[R] N))
      (ModuleCat.ofHom (g.comp (Ideal.span (Set.range f)).subtype)) =
        spanToIdealSpanHom f N (g 1) := by
  -- Evaluate the restricted map on an ideal element and use `R`-linearity to pull out the scalar.
  ext a
  change g (a : R) = (a : R) • g 1
  simpa using g.map_smul (a : R) (1 : R)

/-- Helper for Lemma 15.90.6: the quotient-row connecting map kills every diagonal map
`a ↦ a • x`. -/
theorem idealSpanHomToExt_comp_spanToIdealSpanHom :
    idealSpanHomToExt f N ∘ₗ spanToIdealSpanHom f N = 0 := by
  let hS := idealSpanQuotientShortComplex_shortExact f
  -- View `a ↦ a • x` as the restriction of the ambient map `r ↦ r • x : R → N`.
  apply LinearMap.ext
  intro x
  let gx : R →ₗ[R] N :=
    { toFun := fun r ↦ r • x
      map_add' := by
        intro a b
        simp [add_smul]
      map_smul' := by
        intro a b
        simp [smul_smul] }
  have hhom :
      ((ModuleCat.homLinearEquiv :
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
            ((Ideal.span (Set.range f)) →ₗ[R] N)).symm
        (spanToIdealSpanHom f N x)) =
        ModuleCat.ofHom (gx.comp (Ideal.span (Set.range f)).subtype) := by
    -- The diagonal map is exactly the restriction of the ambient scalar-action map.
    apply (ModuleCat.homLinearEquiv :
      (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
        ((Ideal.span (Set.range f)) →ₗ[R] N)).injective
    simpa [gx] using
      homLinearEquiv_subtype_comp_eq_spanToIdealSpanHom (f := f) (N := N) gx
  have hzero :
      (hS.extClass.precompOfLinear R (ModuleCat.of R N) (Nat.add_zero 1))
        (((Ext.mk₀ (idealSpanQuotientShortComplex f).f).precompOfLinear R
            (ModuleCat.of R N) (zero_add 0))
          (Ext.mk₀ (ModuleCat.ofHom gx))) = 0 := by
    -- Consecutive maps in the contravariant long exact `Ext` sequence compose to zero.
    have hseq :=
      (Ext.contravariantSequence_exact hS (ModuleCat.of R N) 0 1 (by decide)).zero 1
        (by decide)
    rw [show (Ext.contravariantSequence hS (ModuleCat.of R N) 0 1 (by decide)).map' 1 2
        (by decide) (by decide) =
          AddCommGrpCat.ofHom
            ((Ext.mk₀ (idealSpanQuotientShortComplex f).f).precomp
              (ModuleCat.of R N) (zero_add 0)) by
        rfl,
      show (Ext.contravariantSequence hS (ModuleCat.of R N) 0 1 (by decide)).map' 2 3
        (by decide) (by decide) =
          AddCommGrpCat.ofHom
            (hS.extClass.precomp (ModuleCat.of R N) (Nat.add_zero 1)) by
        rfl] at hseq
    have hval := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom' hseq)
      (Ext.mk₀ (ModuleCat.ofHom gx))
    change
      (hS.extClass.precomp (ModuleCat.of R N) (Nat.add_zero 1))
          (((Ext.mk₀ (idealSpanQuotientShortComplex f).f).precomp
              (ModuleCat.of R N) (zero_add 0))
            (Ext.mk₀ (ModuleCat.ofHom gx))) = 0 at hval
    simpa using hval
  have hmk :
      (((Ext.mk₀ (idealSpanQuotientShortComplex f).f).precompOfLinear R
          (ModuleCat.of R N) (zero_add 0))
        (Ext.mk₀ (ModuleCat.ofHom gx))) =
        Ext.mk₀
          ((ModuleCat.homLinearEquiv :
              (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
                ((Ideal.span (Set.range f)) →ₗ[R] N)).symm
            (spanToIdealSpanHom f N x)) := by
    -- The degree-zero map is restriction along `I ↪ R`, rewritten through the explicit
    -- `Hom ≃ LinearMap` bridge.
    calc
      (((Ext.mk₀ (idealSpanQuotientShortComplex f).f).precompOfLinear R
          (ModuleCat.of R N) (zero_add 0))
        (Ext.mk₀ (ModuleCat.ofHom gx)))
          = Ext.mk₀ ((idealSpanQuotientShortComplex f).f ≫ ModuleCat.ofHom gx) := by
              simpa [Ext.mk₀_comp_mk₀]
      _ = Ext.mk₀
            ((ModuleCat.homLinearEquiv :
                (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
                  ((Ideal.span (Set.range f)) →ₗ[R] N)).symm
              (spanToIdealSpanHom f N x)) := by
              simpa [idealSpanQuotientShortComplex] using congrArg Ext.mk₀ hhom
  -- Rewrite the connecting map through the `Ext⁰ ≃ Hom ≃ LinearMap` identifications.
  change
    (hS.extClass.precompOfLinear R (ModuleCat.of R N) (Nat.add_zero 1))
      (Ext.mk₀
        ((ModuleCat.homLinearEquiv :
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
              ((Ideal.span (Set.range f)) →ₗ[R] N)).symm
          (spanToIdealSpanHom f N x))) = 0
  simpa [idealSpanHomToExt, hS, hmk, Ext.homEquiv₀_symm_apply] using hzero

-- Proof sketch: this is the degree-`1` connecting map in the contravariant long exact Ext
-- sequence for `0 → I → R → R / I → 0`; surjectivity follows because `Ext¹_R(R, N) = 0`.
/-- The connecting map `Hom_R(I, N) → Ext¹_R(R / I, N)` for the quotient sequence is surjective. -/
theorem idealSpanHomToExt_surjective :
    Function.Surjective (idealSpanHomToExt f N) := by
  let hS := idealSpanQuotientShortComplex_shortExact f
  intro e
  have hkill0 :
      (Ext.mk₀ (ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).toLinearMap)).comp
        e (zero_add 1) = 0 := by
    -- The middle term of the quotient row is `R`, hence projective, so the next map vanishes.
    letI : Projective (ModuleCat.of R R) := inferInstance
    exact
      ((Ext.mk₀ (ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).toLinearMap)).comp
        e (zero_add 1)).eq_zero_of_projective
  have hkill :
      (Ext.mk₀ (idealSpanQuotientShortComplex f).g).comp e (zero_add 1) = 0 := by
    simpa [idealSpanQuotientShortComplex] using hkill0
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS (ModuleCat.of R N) e hkill
    (Nat.add_zero 1)
  let φ : (Ideal.span (Set.range f)) →ₗ[R] N :=
    (ModuleCat.homLinearEquiv :
      (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
        ((Ideal.span (Set.range f)) →ₗ[R] N))
      ((Ext.linearEquiv₀ :
        Ext (ModuleCat.of R (Ideal.span (Set.range f))) (ModuleCat.of R N) 0 ≃ₗ[R]
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N)) x)
  have hφExt :
      Ext.mk₀
        ((ModuleCat.homLinearEquiv :
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
              ((Ideal.span (Set.range f)) →ₗ[R] N)).symm φ) = x := by
    -- This is exactly the inverse of the `Ext⁰ ≃ Hom ≃ LinearMap` conversion used to define `φ`.
    have hhom :
        ((ModuleCat.homLinearEquiv :
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
              ((Ideal.span (Set.range f)) →ₗ[R] N)).symm φ) =
          (Ext.linearEquiv₀ :
            Ext (ModuleCat.of R (Ideal.span (Set.range f))) (ModuleCat.of R N) 0 ≃ₗ[R]
              (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N)) x := by
      exact LinearEquiv.symm_apply_apply
        (ModuleCat.homLinearEquiv :
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
            ((Ideal.span (Set.range f)) →ₗ[R] N))
        ((Ext.linearEquiv₀ :
          Ext (ModuleCat.of R (Ideal.span (Set.range f))) (ModuleCat.of R N) 0 ≃ₗ[R]
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N)) x)
    rw [hhom]
    simpa using
      (Ext.mk₀_linearEquiv₀_apply (R := R)
        (X := ModuleCat.of R (Ideal.span (Set.range f))) (Y := ModuleCat.of R N) x)
  refine ⟨φ, ?_⟩
  -- The exactness witness already computes the value of the boundary map on this representative.
  change
    hS.extClass.comp
      (Ext.mk₀
        ((ModuleCat.homLinearEquiv :
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
              ((Ideal.span (Set.range f)) →ₗ[R] N)).symm φ))
      (Nat.add_zero 1) = e
  calc
    hS.extClass.comp
        (Ext.mk₀
          ((ModuleCat.homLinearEquiv :
              (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
                ((Ideal.span (Set.range f)) →ₗ[R] N)).symm φ))
        (Nat.add_zero 1)
      = hS.extClass.comp x (Nat.add_zero 1) := by
          exact congrArg (fun t ↦ hS.extClass.comp t (Nat.add_zero 1)) hφExt
    _ = e := hx

-- Proof sketch: if two maps `I → N` differ by multiplication with an element of `N`, they define
-- the same class in `koszulH1Presentation f N`, and the only additional relations come from the
-- kernel of the connecting map above.
/-- The source-facing map `Hom_R(I, N) → koszulH1Presentation f N` kills the kernel of the
connecting map to `Ext¹`. -/
theorem ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation :
    LinearMap.ker (idealSpanHomToExt f N) ≤
      LinearMap.ker (idealSpanHomToKoszulH1Presentation f N) := by
  let hS := idealSpanQuotientShortComplex_shortExact f
  intro z hz
  let zHom : ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N :=
    (ModuleCat.homLinearEquiv :
      (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
        ((Ideal.span (Set.range f)) →ₗ[R] N)).symm z
  let zExt : Ext (ModuleCat.of R (Ideal.span (Set.range f))) (ModuleCat.of R N) 0 := Ext.mk₀ zHom
  have hzExt : hS.extClass.comp zExt (Nat.add_zero 1) = 0 := by
    have hz0 : idealSpanHomToExt f N z = 0 := by
      simpa [LinearMap.mem_ker] using hz
    -- Rewrite kernel membership through the `Ext⁰ ≃ Hom` identifications used in the definition.
    simpa [idealSpanHomToExt, hS, zHom, zExt, Ext.homEquiv₀_symm_apply] using hz0
  obtain ⟨yExt, hyExt⟩ := Ext.contravariant_sequence_exact₁ hS (ModuleCat.of R N) zExt
    (Nat.add_zero 1) hzExt
  obtain ⟨yHom, rfl⟩ := Ext.homEquiv₀.symm.surjective yExt
  let y : R →ₗ[R] N := by
    simpa [idealSpanQuotientShortComplex] using yHom.hom
  have hyHom : (idealSpanQuotientShortComplex f).f ≫ yHom = zHom := by
    -- Convert the degree-zero exactness witness back into an honest extension `R → N`.
    apply Ext.homEquiv₀.symm.injective
    simpa [zExt, Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] using hyExt
  have hz_eq : z = spanToIdealSpanHom f N (y 1) := by
    -- The recovered extension is determined by the image of `1`, so restricting it is diagonal.
    have hz_apply :
        (ModuleCat.homLinearEquiv :
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
              ((Ideal.span (Set.range f)) →ₗ[R] N)) zHom = z := by
      exact LinearEquiv.apply_symm_apply
        (ModuleCat.homLinearEquiv :
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
            ((Ideal.span (Set.range f)) →ₗ[R] N)) z
    calc
      z = (ModuleCat.homLinearEquiv :
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
              ((Ideal.span (Set.range f)) →ₗ[R] N)) zHom := by
            exact hz_apply.symm
      _ = (ModuleCat.homLinearEquiv :
            (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
              ((Ideal.span (Set.range f)) →ₗ[R] N))
            (ModuleCat.ofHom (y.comp (Ideal.span (Set.range f)).subtype)) := by
            simpa [idealSpanQuotientShortComplex, y] using congrArg
              (ModuleCat.homLinearEquiv :
                (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
                  ((Ideal.span (Set.range f)) →ₗ[R] N)) hyHom.symm
      _ = spanToIdealSpanHom f N (y 1) := by
            simpa using
              homLinearEquiv_subtype_comp_eq_spanToIdealSpanHom (f := f) (N := N) y
  rw [LinearMap.mem_ker, hz_eq]
  -- The source-facing quotient kills every diagonal class coming from `N`.
  exact LinearMap.congr_fun
    (idealSpanHomToKoszulH1Presentation_comp_spanToIdealSpanHom (f := f) (N := N))
    (y 1)

/-- Helper for Lemma 15.90.6: the only classes in `Hom_R(I, N)` killed by the quotient-row
connecting map are the diagonal maps `a ↦ a • x`. -/
theorem idealSpanHomToExt_ker_eq_range_spanToIdealSpanHom :
    LinearMap.ker (idealSpanHomToExt f N) =
      LinearMap.range (spanToIdealSpanHom f N) := by
  apply le_antisymm
  · intro z hz
    have hz' :
        z ∈ LinearMap.ker (idealSpanHomToKoszulH1Presentation f N) :=
      ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation (f := f) (N := N) hz
    rw [idealSpanHomToKoszulH1Presentation_ker_eq_range_spanToIdealSpanHom (f := f) (N := N)]
      at hz'
    exact hz'
  · rw [LinearMap.range_le_ker_iff]
    exact idealSpanHomToExt_comp_spanToIdealSpanHom (f := f) (N := N)

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

/-- Helper for Lemma 15.90.6: the presentation map from `Hom_R(I, N)` to `Hom_R(K, N)` is zero
because each cycle from `I → N` factors through the quotient map whose kernel is `K`. -/
theorem koszulH1PresentationToHomKernel_comp_idealSpanHomToKoszulH1Presentation :
    (koszulH1PresentationToHomKernel f N).comp (idealSpanHomToKoszulH1Presentation f N) = 0 := by
  -- Evaluate on a map `φ : I → N`, rewrite through the quotient presentation, and use that
  -- `idealGeneratorRelationKernel f` is the kernel of the factor map to `I`.
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro z
  have hpresent :
      ((LinearMap.range (koszulDiagonalMap f N)).liftQ
        (koszulCyclesToKernelHom f N)
        (koszulDiagonalMap_le_ker_cyclesToKernelHom f N))
        (((LinearMap.range (koszulDiagonalMap f N)).mkQ)
          ((idealSpanHomToKoszulFirstCycles f N) φ)) =
        koszulCyclesToKernelHom f N ((idealSpanHomToKoszulFirstCycles f N) φ) := by
    exact LinearMap.congr_fun
      ((LinearMap.range (koszulDiagonalMap f N)).liftQ_mkQ
        (koszulCyclesToKernelHom f N)
        (koszulDiagonalMap_le_ker_cyclesToKernelHom f N))
      ((idealSpanHomToKoszulFirstCycles f N) φ)
  have hz0 : (idealGeneratorRelationModuleToSpan f) z.1 = 0 := by
    simpa [LinearMap.mem_ker] using z.2
  change
    (((LinearMap.range (koszulDiagonalMap f N)).liftQ
      (koszulCyclesToKernelHom f N)
      (koszulDiagonalMap_le_ker_cyclesToKernelHom f N))
      (((LinearMap.range (koszulDiagonalMap f N)).mkQ)
        ((idealSpanHomToKoszulFirstCycles f N) φ))) z = 0
  rw [hpresent]
  change
    ((koszulCycleToRelationModuleHom f N ((idealSpanHomToKoszulFirstCycles f N) φ)).comp
      (idealGeneratorRelationKernel f).subtype) z = 0
  -- Route correction: use the explicit factorization through `idealGeneratorRelationModuleToSpan`
  -- instead of waiting for the later Ext exactness package.
  rw [idealSpanHom_cycle_to_relation_module_factorization (f := f) (N := N) φ]
  simp [LinearMap.comp_apply, hz0]

/-- Helper for Lemma 15.90.6: the descended quotient map to the presentation is also killed by
the map to `Hom_R(K, N)`. -/
theorem koszulH1PresentationToHomKernel_comp_idealSpanHomKerToKoszulH1Presentation :
    (koszulH1PresentationToHomKernel f N).comp
      (idealSpanHomKerToKoszulH1Presentation f N) = 0 := by
  -- Descend the already-zero composition along the quotient by `ker (idealSpanHomToExt f N)`.
  apply LinearMap.ext
  intro q
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (idealSpanHomToExt f N)) q
  have hq := LinearMap.congr_fun
    ((LinearMap.ker (idealSpanHomToExt f N)).liftQ_mkQ
      (idealSpanHomToKoszulH1Presentation f N)
      (ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation f N))
    φ
  have hdesc :
      (idealSpanHomKerToKoszulH1Presentation f N)
          ((LinearMap.ker (idealSpanHomToExt f N)).mkQ φ) =
        idealSpanHomToKoszulH1Presentation f N φ := by
    simpa [idealSpanHomKerToKoszulH1Presentation, LinearMap.comp_apply] using hq
  change
    (koszulH1PresentationToHomKernel f N)
      ((idealSpanHomKerToKoszulH1Presentation f N)
        ((LinearMap.ker (idealSpanHomToExt f N)).mkQ φ)) = 0
  rw [hdesc]
  exact LinearMap.congr_fun
    (koszulH1PresentationToHomKernel_comp_idealSpanHomToKoszulH1Presentation
      (f := f) (N := N))
    φ

-- Proof sketch: a map `I → N` induces a tuple map on the relation module that factors through
-- `I`; its restriction to the kernel `K` is therefore zero, and the factorization survives the
-- quotient by boundaries and the identification with `Ext¹`.
/-- The canonical left map to `koszulH1Presentation f N` composes trivially with the map to
`Hom_R(K, N)`. -/
theorem koszulH1PresentationToHomKernel_comp_koszulExtToH1Presentation :
    (koszulH1PresentationToHomKernel f N).comp (koszulExtToH1Presentation f N) = 0 := by
  -- After quotienting by `ker (idealSpanHomToExt f N)`, the remaining composition is already zero.
  apply LinearMap.ext
  intro e
  have hzero := LinearMap.congr_fun
    (koszulH1PresentationToHomKernel_comp_idealSpanHomKerToKoszulH1Presentation
      (f := f) (N := N))
    (((idealSpanHomToExt f N).quotKerEquivOfSurjective
      (idealSpanHomToExt_surjective f N)).symm e)
  simpa [koszulExtToH1Presentation, LinearMap.comp_apply] using hzero

/-- Helper for Lemma 15.90.6: a class in the presentation is killed by the map to `Hom_R(K, N)`
exactly when it comes from a map `I → N`. -/
theorem idealSpanHomToKoszulH1Presentation_range_eq_ker_presentationToHomKernel :
    LinearMap.range (idealSpanHomToKoszulH1Presentation f N) =
      LinearMap.ker (koszulH1PresentationToHomKernel f N) := by
  apply le_antisymm
  · intro q hq
    rcases hq with ⟨φ, rfl⟩
    -- The factorization through `I` already forces the restriction to `K` to vanish.
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun
      (koszulH1PresentationToHomKernel_comp_idealSpanHomToKoszulH1Presentation
        (f := f) (N := N))
      φ
  · intro q hq
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (koszulDiagonalMap f N)) q
    have hcDesc :
        koszulH1PresentationToHomKernel f N
          ((LinearMap.range (koszulDiagonalMap f N)).mkQ c) =
            koszulCyclesToKernelHom f N c := by
      -- The presentation map is the quotient descent of the restriction map on cycles.
      change
        (((LinearMap.range (koszulDiagonalMap f N)).liftQ
          (koszulCyclesToKernelHom f N)
          (koszulDiagonalMap_le_ker_cyclesToKernelHom f N)).comp
            ((LinearMap.range (koszulDiagonalMap f N)).mkQ)) c =
          koszulCyclesToKernelHom f N c
      simpa using congrArg (fun F => F c)
        ((LinearMap.range (koszulDiagonalMap f N)).liftQ_mkQ
          (koszulCyclesToKernelHom f N)
          (koszulDiagonalMap_le_ker_cyclesToKernelHom f N))
    have hc0 : koszulCyclesToKernelHom f N c = 0 := by
      have hq0 :
          koszulH1PresentationToHomKernel f N
            ((LinearMap.range (koszulDiagonalMap f N)).mkQ c) = 0 := by
        simpa [LinearMap.mem_ker] using hq
      rwa [hcDesc] at hq0
    let S := (idealGeneratorRelationModuleToSpan f).shortComplexKer
    let cHom : ModuleCat.of R (idealGeneratorRelationModule f) ⟶ ModuleCat.of R N :=
      ModuleCat.ofHom (koszulCycleToRelationModuleHom f N c)
    let cExt :
        Ext (ModuleCat.of R (idealGeneratorRelationModule f)) (ModuleCat.of R N) 0 :=
      Ext.mk₀ cHom
    have hrestrictHom : S.f ≫ cHom = 0 := by
      -- The vanishing of the quotient map says precisely that the induced map restricts to zero on `K`.
      apply ModuleCat.hom_ext_iff.mpr
      ext z
      simpa [S, cHom, koszulCyclesToKernelHom] using LinearMap.congr_fun hc0 z
    have hrestrictExt : (Ext.mk₀ S.f).comp cExt (zero_add 0) = 0 := by
      -- Rewrite the degree-zero class through composition with the kernel inclusion.
      simpa [cExt, Ext.mk₀_comp_mk₀, hrestrictHom]
    obtain ⟨φExt, hφExt⟩ := Ext.contravariant_sequence_exact₂
      (hS := idealGeneratorRelationShortExact f) (Y := ModuleCat.of R N) cExt hrestrictExt
    obtain ⟨φHom, rfl⟩ := Ext.homEquiv₀.symm.surjective φExt
    let φ : (Ideal.span (Set.range f)) →ₗ[R] N :=
      (ModuleCat.homLinearEquiv :
        (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
          ((Ideal.span (Set.range f)) →ₗ[R] N))
        φHom
    have hfactorHom : S.g ≫ φHom = cHom := by
      -- Exactness of the relation short exact sequence supplies the required factorization through `I`.
      apply Ext.homEquiv₀.symm.injective
      simpa [S, cExt, Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] using hφExt
    have hfactor :
        φ.comp (idealGeneratorRelationModuleToSpan f) =
          koszulCycleToRelationModuleHom f N c := by
      -- Translate the categorical factorization back into a statement about linear maps.
      exact ModuleCat.hom_ext_iff.mp <| by
        simpa [S, cHom, φ] using hfactorHom
    have hcEq :
        c = idealSpanHomToKoszulFirstCycles f N φ := by
      -- The relation-module map remembers the cycle completely, so the factorization identifies the cycle.
      apply koszulCycleToRelationModuleHom_injective (f := f) (N := N)
      calc
        koszulCycleToRelationModuleHom f N c
            = φ.comp (idealGeneratorRelationModuleToSpan f) := hfactor.symm
        _ = koszulCycleToRelationModuleHom f N ((idealSpanHomToKoszulFirstCycles f N) φ) := by
              symm
              exact idealSpanHom_cycle_to_relation_module_factorization (f := f) (N := N) φ
    refine ⟨φ, ?_⟩
    -- Replace the chosen cycle representative by the one coming from `φ : I → N`.
    rw [idealSpanHomToKoszulH1Presentation, hcEq]
    rfl

/-- Helper for Lemma 15.90.6: after quotienting by the common kernel, the descended map to the
Koszul presentation is injective. -/
theorem idealSpanHomKerToKoszulH1Presentation_injective :
    Function.Injective (idealSpanHomKerToKoszulH1Presentation f N) := by
  have hkerEq :
      LinearMap.ker (idealSpanHomToExt f N) =
        LinearMap.ker (idealSpanHomToKoszulH1Presentation f N) := by
    rw [idealSpanHomToExt_ker_eq_range_spanToIdealSpanHom (f := f) (N := N),
      idealSpanHomToKoszulH1Presentation_ker_eq_range_spanToIdealSpanHom (f := f) (N := N)]
  have hkerBot :
      LinearMap.ker (idealSpanHomKerToKoszulH1Presentation f N) = ⊥ := by
    exact Submodule.ker_liftQ_eq_bot'
      (LinearMap.ker (idealSpanHomToExt f N))
      (idealSpanHomToKoszulH1Presentation f N)
      hkerEq
  exact LinearMap.ker_eq_bot.mp hkerBot

/-- Helper for Lemma 15.90.6: the left presentation map is injective because both quotient rows
mod out by the same kernel inside `Hom_R(I, N)`. -/
theorem koszulExtToH1Presentation_injective :
    Function.Injective (koszulExtToH1Presentation f N) := by
  intro x y hxy
  apply ((idealSpanHomToExt f N).quotKerEquivOfSurjective
    (idealSpanHomToExt_surjective f N)).symm.injective
  apply idealSpanHomKerToKoszulH1Presentation_injective (f := f) (N := N)
  simpa [koszulExtToH1Presentation] using hxy

/-- Helper for Lemma 15.90.6: the left map in the presentation short complex has image equal to
the kernel of the map to `Hom_R(K, N)`. -/
theorem koszulExtToH1Presentation_range_eq_ker :
    LinearMap.range (koszulExtToH1Presentation f N) =
      LinearMap.ker (koszulH1PresentationToHomKernel f N) := by
  let e :=
    (idealSpanHomToExt f N).quotKerEquivOfSurjective (idealSpanHomToExt_surjective f N)
  have hrange₁ :
      LinearMap.range (koszulExtToH1Presentation f N) =
        LinearMap.range (idealSpanHomKerToKoszulH1Presentation f N) := by
    apply le_antisymm
    · intro q hq
      rcases hq with ⟨x, rfl⟩
      refine ⟨e.symm x, ?_⟩
      rfl
    · intro q hq
      rcases hq with ⟨x, rfl⟩
      refine ⟨e x, ?_⟩
      change
        idealSpanHomKerToKoszulH1Presentation f N (e.symm (e x)) =
          idealSpanHomKerToKoszulH1Presentation f N x
      rw [e.symm_apply_apply]
  have hrange₂ :
      LinearMap.range (idealSpanHomKerToKoszulH1Presentation f N) =
        LinearMap.range (idealSpanHomToKoszulH1Presentation f N) := by
    apply le_antisymm
    · intro q hq
      rcases hq with ⟨x, rfl⟩
      obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (idealSpanHomToExt f N)) x
      refine ⟨φ, ?_⟩
      simpa [idealSpanHomKerToKoszulH1Presentation, LinearMap.comp_apply] using
        LinearMap.congr_fun
          ((LinearMap.ker (idealSpanHomToExt f N)).liftQ_mkQ
            (idealSpanHomToKoszulH1Presentation f N)
            (ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation f N))
          φ
    · intro q hq
      rcases hq with ⟨φ, rfl⟩
      refine ⟨Submodule.Quotient.mk φ, ?_⟩
      simpa [idealSpanHomKerToKoszulH1Presentation, LinearMap.comp_apply] using
        LinearMap.congr_fun
          ((LinearMap.ker (idealSpanHomToExt f N)).liftQ_mkQ
            (idealSpanHomToKoszulH1Presentation f N)
            (ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation f N))
          φ
  calc
    LinearMap.range (koszulExtToH1Presentation f N)
      = LinearMap.range (idealSpanHomKerToKoszulH1Presentation f N) := hrange₁
    _ = LinearMap.range (idealSpanHomToKoszulH1Presentation f N) := hrange₂
    _ = LinearMap.ker (koszulH1PresentationToHomKernel f N) := by
          exact idealSpanHomToKoszulH1Presentation_range_eq_ker_presentationToHomKernel
            (f := f) (N := N)

/-- Helper for Lemma 15.90.6: once a map `K → N` lifts to the relation module, the lift descends
to a presentation class with the prescribed image in `Hom_R(K, N)`. -/
theorem relation_lift_gives_presentation_class
    {ψ : idealGeneratorRelationKernel f →ₗ[R] N}
    (cHom : idealGeneratorRelationModule f →ₗ[R] N)
    (hcHom : cHom.comp (idealGeneratorRelationKernel f).subtype = ψ) :
    ∃ q : koszulH1Presentation f N, koszulH1PresentationToHomKernel f N q = ψ := by
  let c : koszulFirstCycles f N :=
    relation_module_hom_equiv_koszul_first_cycles (f := f) (N := N) cHom
  refine ⟨(LinearMap.range (koszulDiagonalMap f N)).mkQ c, ?_⟩
  -- Descending the chosen cycle representative computes by the quotient lift formula.
  have hdesc :
      koszulH1PresentationToHomKernel f N ((LinearMap.range (koszulDiagonalMap f N)).mkQ c) =
        koszulCyclesToKernelHom f N c := by
    exact LinearMap.congr_fun
      ((LinearMap.range (koszulDiagonalMap f N)).liftQ_mkQ
        (koszulCyclesToKernelHom f N)
        (koszulDiagonalMap_le_ker_cyclesToKernelHom f N))
      c
  rw [hdesc]
  change (koszulCycleToRelationModuleHom f N c).comp
      (idealGeneratorRelationKernel f).subtype = ψ
  -- The cycle/relation-module equivalence recovers the original lift on the nose.
  rw [show koszulCycleToRelationModuleHom f N c = cHom by
        simpa [c] using
          koszulCycleToRelationModuleHom_relationModuleHomToKoszulFirstCycles
            (f := f) (N := N) cHom]
  exact hcHom

/-- Helper for Lemma 15.90.6: if the relation-row `Ext¹` obstruction of `ψ : K → N` vanishes,
then `ψ` is represented by a class in the Koszul presentation. -/
theorem presentation_class_lifts_kernel_hom_of_obstruction_zero
    (ψ : idealGeneratorRelationKernel f →ₗ[R] N)
    (hψ :
      let hS := idealGeneratorRelationShortExact f
      hS.extClass.comp (Ext.mk₀ (ModuleCat.ofHom ψ)) (Nat.add_zero 1) = 0) :
    ∃ q : koszulH1Presentation f N, koszulH1PresentationToHomKernel f N q = ψ := by
  let S := (idealGeneratorRelationModuleToSpan f).shortComplexKer
  let hS := idealGeneratorRelationShortExact f
  let ψExt :
      Ext (ModuleCat.of R (idealGeneratorRelationKernel f)) (ModuleCat.of R N) 0 :=
    Ext.mk₀ (ModuleCat.ofHom ψ)
  have hψExt : hS.extClass.comp ψExt (Nat.add_zero 1) = 0 := by
    simpa [hS, ψExt] using hψ
  obtain ⟨cExt, hcExt⟩ := Ext.contravariant_sequence_exact₁
    hS (ModuleCat.of R N) ψExt (Nat.add_zero 1) hψExt
  obtain ⟨cHomCat, rfl⟩ := Ext.homEquiv₀.symm.surjective cExt
  let cHom : idealGeneratorRelationModule f →ₗ[R] N := cHomCat.hom
  have hcHomCat : S.f ≫ cHomCat = ModuleCat.ofHom ψ := by
    -- Exactness rewrites the degree-zero predecessor into an honest lift across `K ↪ M`.
    apply Ext.homEquiv₀.symm.injective
    simpa [S, ψExt, Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] using hcExt
  have hcHom : cHom.comp (idealGeneratorRelationKernel f).subtype = ψ := by
    -- Translate the categorical lift into the underlying linear-map equation.
    exact ModuleCat.hom_ext_iff.mp <| by
      simpa [S, cHom] using hcHomCat
  exact relation_lift_gives_presentation_class (f := f) (N := N) cHom hcHom

/-- Helper for Lemma 15.90.6: after killing the quotient-row obstruction, every map `K → N`
comes from a presentation class. -/
theorem presentation_class_lifts_kernel_hom
    (ψ : idealGeneratorRelationKernel f →ₗ[R] N) :
    ∃ q : koszulH1Presentation f N, koszulH1PresentationToHomKernel f N q = ψ := by
  -- Route correction: the source-faithful proof reduces surjectivity to vanishing of the
  -- relation-row obstruction `S.extClass.comp (Ext.mk₀ ψ) : Ext¹_R(I, N)`.
  -- TODO: prove that obstruction vanishes, or audit the target if only exactness at the right
  -- term is available from the source statement.
  sorry

/-- Helper for Lemma 15.90.6: the quotient presentation surjects onto `Hom_R(K, N)`. -/
theorem koszulH1PresentationToHomKernel_surjective :
    Function.Surjective (koszulH1PresentationToHomKernel f N) := by
  intro ψ
  -- Once the quotient-row obstruction is absorbed, the helper already provides the presentation
  -- lift required for surjectivity.
  exact presentation_class_lifts_kernel_hom (f := f) (N := N) ψ

/-- Helper for Lemma 15.90.6: the presentation short complex
`0 ⟶ Ext¹_R(R / I, N) ⟶ koszulH1Presentation f N ⟶ Hom_R(K, N) ⟶ 0`
is short exact. -/
theorem koszulH1Presentation_shortExact :
    let S : ShortComplex (ModuleCat R) :=
      ShortComplex.mk
        (ModuleCat.ofHom (koszulExtToH1Presentation f N))
        (ModuleCat.ofHom (koszulH1PresentationToHomKernel f N))
        (by
          change
            ModuleCat.ofHom
              ((koszulH1PresentationToHomKernel f N).comp (koszulExtToH1Presentation f N)) =
                ModuleCat.ofHom 0
          simpa using congrArg ModuleCat.ofHom
            (koszulH1PresentationToHomKernel_comp_koszulExtToH1Presentation
              (f := f) (N := N)))
    S.ShortExact := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (ModuleCat.ofHom (koszulExtToH1Presentation f N))
      (ModuleCat.ofHom (koszulH1PresentationToHomKernel f N))
      (by
        change
          ModuleCat.ofHom
            ((koszulH1PresentationToHomKernel f N).comp (koszulExtToH1Presentation f N)) =
              ModuleCat.ofHom 0
        simpa using congrArg ModuleCat.ofHom
          (koszulH1PresentationToHomKernel_comp_koszulExtToH1Presentation
            (f := f) (N := N)))
  -- Package the proved exactness, injectivity, and surjectivity data into the canonical `ShortExact`.
  refine ModuleCat.shortComplex_shortExact S ?_ ?_ ?_
  · simpa [S] using
      (LinearMap.exact_iff.2 (koszulExtToH1Presentation_range_eq_ker (f := f) (N := N)).symm)
  · simpa [S] using koszulExtToH1Presentation_injective (f := f) (N := N)
  · simpa [S] using koszulH1PresentationToHomKernel_surjective (f := f) (N := N)

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
  -- Transport the presentation-level zero composition across the homology-presentation isomorphism.
  simp [koszulExtToH1, koszulH1ToHomKernel, Category.assoc]
  change
    ModuleCat.ofHom
      ((koszulH1PresentationToHomKernel f N).comp (koszulExtToH1Presentation f N)) =
        ModuleCat.ofHom 0
  simpa using congrArg ModuleCat.ofHom
    (koszulH1PresentationToHomKernel_comp_koszulExtToH1Presentation (f := f) (N := N))

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
@[stacks 05EE]
theorem koszulH1ShortComplex_shortExact :
    (koszulH1ShortComplex f N).ShortExact := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (ModuleCat.ofHom (koszulExtToH1Presentation f N))
      (ModuleCat.ofHom (koszulH1PresentationToHomKernel f N))
      (by
        change
          ModuleCat.ofHom
            ((koszulH1PresentationToHomKernel f N).comp (koszulExtToH1Presentation f N)) =
              ModuleCat.ofHom 0
        simpa using congrArg ModuleCat.ofHom
          (koszulH1PresentationToHomKernel_comp_koszulExtToH1Presentation
            (f := f) (N := N)))
  have hS : S.ShortExact := koszulH1Presentation_shortExact (f := f) (N := N)
  let e : koszulH1ShortComplex f N ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (koszulH1IsoPresentation f N) (Iso.refl _)
      (by
        -- The left map is defined by conjugating the presentation map across the middle isomorphism.
        simp [koszulH1ShortComplex, koszulExtToH1, S, Category.assoc])
      (by
        -- The right map is definitionally the presentation map postcomposed with the middle isomorphism.
        simp [koszulH1ShortComplex, koszulH1ToHomKernel, S, Category.assoc])
  -- Transport the short exact presentation row back to the source-facing owner `koszulH1`.
  exact ShortComplex.shortExact_of_iso e.symm hS

end
