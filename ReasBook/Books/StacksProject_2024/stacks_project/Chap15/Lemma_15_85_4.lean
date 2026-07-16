import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_3
import StacksProject_2024.stacks_project.Chap13.«13_18_6_1»
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_7
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_8
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle
open DerivedCategory
open CategoryTheory.Limits
open HomologicalComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (up ℤ)
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.85.4:
- primary domain: comparison between homotopy-category and derived-category morphisms from
  bounded-above complexes, together with maps to shifted single complexes encoded by cocycles in
  `HomComplex`;
- inspected owner declarations:
  `CochainComplex.IsKProjective.Qh_map_bijective`,
  `DerivedCategory.Qh.map`,
  `CochainComplex.HomComplex.Cocycle.toSingleMk`,
  `CochainComplex.HomComplex.Cocycle.equivHomShift`;
- best owner abstraction: the comparison map of part `(1)` is the canonical localization map
  `DerivedCategory.Qh.map` on homotopy-category morphisms, while the primitive source datum in
  parts `(3)` and `(4)` is a degree `-2` cocycle `a : M.X (-2) ⟶ X` with
  `M.d (-3) (-2) ≫ a = 0`, owned by `Cocycle.toSingleMk`; the derived morphism to `X[2]` is a
  bridge/view obtained by applying `ShiftedHom.map` along `DerivedCategory.Q`;
- primitive data vs. derived API:
  the primitive data is the support/projectivity hypotheses together with the cocycle condition in
  degree `-2`, while the derived morphisms `M^• ⟶ X[2]` and `K^• ⟶ K^{-2}[2]` are bridge
  constructions and should not be stored as independent primitive wrapper data.

Source/core/bridge triage:
- `source-facing`: the four theorem statements below;
-- `core/canonical`: `DerivedCategory.Qh.map` and the cocycle owners
--   `Cocycle.toSingleMk` / `Cocycle.equivHomShift`;
-- `bridge/view`: the derived morphisms obtained from those cocycles via `ShiftedHom.map`. -/

abbrev negTwoCocycleToShift {M K : Cpx}
    (a : M.X (-2) ⟶ K.X (-2)) (ha : M.d (-3) (-2) ≫ a = 0) :=
  Q.map
    (equivHomShift.symm (toSingleMk a (by omega) (-3) (by omega) ha))
    ≫
      ((Q.commShiftIso (2 : ℤ)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom
    ≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

abbrev negTwoProjection (K : Cpx) (hK : K.IsStrictlyGE (-2)) :=
  letI : K.IsStrictlyGE (-2) := hK
  Q.map
    (equivHomShift.symm
      (toSingleMk
        (𝟙 (K.X (-2)))
        (by omega)
        (-3)
        (by omega)
        (by
          simpa using
            (K.isZero_of_isStrictlyGE (-2) (-3) (by omega)).eq_of_src (K.d (-3) (-2)) 0)))
    ≫
      ((Q.commShiftIso (2 : ℤ)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom
    ≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

/-- Helper for Lemma 15.85.4: in the split exact degree-`0` row
`0 ⟶ kernel π₀ ⟶ P₀ ⟶ M₀ ⟶ 0`, every map out of `kernel π₀` extends across `P₀` once `M₀` is
projective. -/
lemma extend_degree_zero_component_from_kernel
    {P₀ M₀ T : ModuleCat R} (π₀ : P₀ ⟶ M₀) [Epi π₀]
    (hM₀ : Projective M₀) (u : kernel π₀ ⟶ T) :
    ∃ s : P₀ ⟶ T, kernel.ι π₀ ≫ s = u := by
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk (kernel.ι π₀) π₀ (kernel.condition π₀)
  have hS : S.ShortExact := by
    -- The kernel row is exact, with the given epimorphism as its right map.
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ShortComplex.exact_kernel π₀
  letI : Projective M₀ := hM₀
  letI : IsSplitMono S.f := (hS.splittingOfProjective).isSplitMono_f
  -- A retraction of the kernel inclusion gives the required extension immediately.
  refine ⟨retraction S.f ≫ u, ?_⟩
  simpa [S, Category.assoc]

/-- Helper for Lemma 15.85.4: the differential `d^{-1}` lands in the degree-`0` cycles. -/
lemma d_negOne_zero_factors_through_zero_cycles
    (A : Cpx) :
    A.d (-1) 0 ≫ A.d 0 1 = 0 := by
  -- This is the basic `d ∘ d = 0` identity specialized to degrees `-1, 0, 1`.
  simpa using A.d_comp_d (-1) 0 1

/-- Helper for Lemma 15.85.4: the canonical map from `A^{-1}` to the degree-`0` cycles. -/
def to_zero_cycles {A : CochainComplex (ModuleCat R) ℤ} :
    A.X (-1) ⟶ kernel (A.d 0 1) :=
  kernel.lift (A.d 0 1) (A.d (-1) 0) (d_negOne_zero_factors_through_zero_cycles A)

/-- Helper for Lemma 15.85.4: in an acyclic complex supported in degrees `≥ -1`, every
degree-`0` cycle comes from degree `-1`. -/
lemma surjective_to_zero_cycles_of_acyclic_strictlyGE_negOne
    {A : CochainComplex (ModuleCat R) ℤ} (hAcyclic : A.Acyclic) (hA : A.IsStrictlyGE (-1)) :
    Function.Surjective (@to_zero_cycles R _ A).hom := by
  -- Keep the support hypothesis in scope: this lemma is the cycles-object step used later in the
  -- `≥ -1` null-homotopy descent route.
  let _ := hA
  have hExactAt : A.ExactAt 0 := by
    -- Acyclicity identifies exactness at degree `0`.
    exact (HomologicalComplex.acyclic_iff A).mp hAcyclic 0
  have hExactSc : (A.sc 0).Exact := by
    -- Rewrite exactness at degree `0` as exactness of `A^{-1} ⟶ A^0 ⟶ A^1`.
    exact (HomologicalComplex.exactAt_iff A 0).mp hExactAt
  have hRangeKer' :
      LinearMap.range (A.d ((ComplexShape.up ℤ).prev 0) 0).hom =
        LinearMap.ker (A.d 0 ((ComplexShape.up ℤ).next 0)).hom := by
    simpa [HomologicalComplex.sc] using ShortComplex.Exact.moduleCat_range_eq_ker hExactSc
  have hRangeKer :
      LinearMap.range (A.d (-1) 0).hom =
        LinearMap.ker (A.d 0 1).hom := by
    have hprev : (ComplexShape.up ℤ).prev 0 = -1 := by
      simpa using (CochainComplex.prev ℤ 0)
    have hnext : (ComplexShape.up ℤ).next 0 = 1 := by
      simpa using (CochainComplex.next ℤ 0)
    rw [hprev, hnext] at hRangeKer'
    exact hRangeKer'
  have hι_injective :
      Function.Injective (kernel.ι (A.d 0 1)).hom := by
    simpa using
      (ModuleCat.mono_iff_injective (kernel.ι (A.d 0 1))).1 inferInstance
  intro y
  let y' : LinearMap.ker (A.d 0 1).hom :=
    ((ModuleCat.kernelIsoKer (A.d 0 1)).hom).hom y
  have hy_val : (kernel.ι (A.d 0 1)).hom y = y'.1 := by
    -- Convert the categorical kernel point to the underlying linear-algebra kernel element.
    exact (congrArg
      (fun g : kernel (A.d 0 1) ⟶ A.X 0 ↦ g.hom y)
      (ModuleCat.kernelIsoKer_hom_ker_subtype (f := A.d 0 1))).symm
  have hy_range : y'.1 ∈ LinearMap.range (A.d (-1) 0).hom := by
    have hy_ker : y'.1 ∈ LinearMap.ker (A.d 0 1).hom := by
      simpa using y'.2
    rw [hRangeKer]
    exact hy_ker
  rcases hy_range with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Equality in the kernel object is checked after the monomorphism `kernel.ι`.
  apply hι_injective
  calc
    (kernel.ι (A.d 0 1)).hom ((@to_zero_cycles R _ A).hom x)
        = (A.d (-1) 0).hom x := by
            simp [to_zero_cycles]
    _ = y'.1 := hx
    _ = (kernel.ι (A.d 0 1)).hom y := hy_val.symm

/-- Helper for Lemma 15.85.4: if an acyclic target complex is supported in degrees `≥ -1`, then
its differential `A^{-1} ⟶ A^0` is monic. This is the exactness input needed to cancel the
degree-`-1` correction in the cokernel descent route. -/
lemma mono_d_negOne_zero_of_acyclic_strictlyGE_negOne
    {A : Cpx} (hAcyclic : A.Acyclic) (hA : A.IsStrictlyGE (-1)) :
    Mono (A.d (-1) 0) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  have hExactAt : A.ExactAt (-1) := by
    exact (HomologicalComplex.acyclic_iff A).mp hAcyclic (-1)
  have hExactSc : (A.sc (-1)).Exact := by
    -- Rewrite exactness at degree `-1` into the concrete short complex
    -- `A^{-2} ⟶ A^{-1} ⟶ A^0`.
    exact (HomologicalComplex.exactAt_iff A (-1)).mp hExactAt
  have hRangeKer' :
      LinearMap.range (A.d ((ComplexShape.up ℤ).prev (-1)) (-1)).hom =
        LinearMap.ker (A.d (-1) ((ComplexShape.up ℤ).next (-1))).hom := by
    simpa [HomologicalComplex.sc] using ShortComplex.Exact.moduleCat_range_eq_ker hExactSc
  have hRangeKer :
      LinearMap.range (A.d (-2) (-1)).hom =
        LinearMap.ker (A.d (-1) 0).hom := by
    have hprev : (ComplexShape.up ℤ).prev (-1) = -2 := by
      simpa using (CochainComplex.prev ℤ (-1))
    have hnext : (ComplexShape.up ℤ).next (-1) = 0 := by
      simpa using (CochainComplex.next ℤ (-1))
    rw [hprev, hnext] at hRangeKer'
    exact hRangeKer'
  have hsub_mem :
      x - y ∈ LinearMap.ker (A.d (-1) 0).hom := by
    change (A.d (-1) 0).hom (x - y) = 0
    simp [hxy]
  rw [← hRangeKer] at hsub_mem
  rcases hsub_mem with ⟨z, hz⟩
  have hd_negTwo : A.d (-2) (-1) = 0 := by
    -- Support in degrees `≥ -1` kills the incoming differential from degree `-2`.
    exact (A.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_src _ _
  have hz_zero : x - y = 0 := by
    rw [hd_negTwo] at hz
    simpa using hz.symm
  exact sub_eq_zero.mp hz_zero

/-- Helper for Lemma 15.85.4: a map from a complex supported in degrees `≤ 0` to an acyclic
complex supported in degrees `≥ -1` is killed by a single degree-`0` homotopy component. -/
lemma exists_degree_zero_null_homotopy_to_acyclic_strictlyGE_negOne
    {M A : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hAcyclic : A.Acyclic)
    (hA : A.IsStrictlyGE (-1))
    (f : M ⟶ A) :
    ∃ h0 : M.X 0 ⟶ A.X (-1),
      f.f 0 + h0 ≫ A.d (-1) 0 = 0 ∧
      f.f (-1) + M.d (-1) 0 ≫ h0 = 0 := by
  let _ : Projective (M.X 0) := hM0
  have hf_one : f.f 1 = 0 := by
    exact (M.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_src _ _
  have hf_cycle : f.f 0 ≫ A.d 0 1 = 0 := by
    -- The degree-`0` component lands in cycles because the source vanishes in degree `1`.
    calc
      f.f 0 ≫ A.d 0 1 = M.d 0 1 ≫ f.f 1 := by
        simpa using f.comm 0
      _ = 0 := by
        simp [hf_one]
  let z0 : M.X 0 ⟶ kernel (A.d 0 1) :=
    kernel.lift (A.d 0 1) (-f.f 0) (by simpa [Category.assoc] using hf_cycle)
  let toZeroCycles : A.X (-1) ⟶ kernel (A.d 0 1) :=
    kernel.lift (A.d 0 1) (A.d (-1) 0) (d_negOne_zero_factors_through_zero_cycles A)
  have hEpiToCycles : Epi toZeroCycles := by
    rw [ModuleCat.epi_iff_surjective]
    have hExactAt : A.ExactAt 0 := by
      exact (HomologicalComplex.acyclic_iff A).mp hAcyclic 0
    have hExactSc : (A.sc 0).Exact := by
      exact (HomologicalComplex.exactAt_iff A 0).mp hExactAt
    have hRangeKer' :
        LinearMap.range (A.d ((ComplexShape.up ℤ).prev 0) 0).hom =
          LinearMap.ker (A.d 0 ((ComplexShape.up ℤ).next 0)).hom := by
      simpa [HomologicalComplex.sc] using ShortComplex.Exact.moduleCat_range_eq_ker hExactSc
    have hRangeKer :
        LinearMap.range (A.d (-1) 0).hom =
          LinearMap.ker (A.d 0 1).hom := by
      have hprev : (ComplexShape.up ℤ).prev 0 = -1 := by
        simpa using (CochainComplex.prev ℤ 0)
      have hnext : (ComplexShape.up ℤ).next 0 = 1 := by
        simpa using (CochainComplex.next ℤ 0)
      rw [hprev, hnext] at hRangeKer'
      exact hRangeKer'
    have hι_injective :
        Function.Injective (kernel.ι (A.d 0 1)).hom := by
      simpa using
        (ModuleCat.mono_iff_injective (kernel.ι (A.d 0 1))).1 inferInstance
    intro y
    let y' : LinearMap.ker (A.d 0 1).hom :=
      ((ModuleCat.kernelIsoKer (A.d 0 1)).hom).hom y
    have hy_val : (kernel.ι (A.d 0 1)).hom y = y'.1 := by
      exact (congrArg
        (fun g : kernel (A.d 0 1) ⟶ A.X 0 ↦ g.hom y)
        (ModuleCat.kernelIsoKer_hom_ker_subtype (f := A.d 0 1))).symm
    have hy_range : y'.1 ∈ LinearMap.range (A.d (-1) 0).hom := by
      have hy_ker : y'.1 ∈ LinearMap.ker (A.d 0 1).hom := by
        simpa using y'.2
      rw [hRangeKer]
      exact hy_ker
    rcases hy_range with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply hι_injective
    calc
      (kernel.ι (A.d 0 1)).hom (toZeroCycles.hom x)
          = (A.d (-1) 0).hom x := by
              simp [toZeroCycles]
      _ = y'.1 := hx
      _ = (kernel.ι (A.d 0 1)).hom y := hy_val.symm
  let h0 : M.X 0 ⟶ A.X (-1) := Projective.factorThru z0 toZeroCycles
  have hh0_to_cycles : h0 ≫ toZeroCycles = z0 := by
    exact Projective.factorThru_comp z0 toZeroCycles
  have hh0_degree_zero : h0 ≫ A.d (-1) 0 = -f.f 0 := by
    -- Lift the chosen degree-`0` cycle back along `A^{-1} ⟶ Z^0(A)`.
    calc
      h0 ≫ A.d (-1) 0 = h0 ≫ toZeroCycles ≫ kernel.ι (A.d 0 1) := by
        simp [toZeroCycles]
      _ = z0 ≫ kernel.ι (A.d 0 1) := by
        simpa [Category.assoc] using
          congrArg (fun t ↦ t ≫ kernel.ι (A.d 0 1)) hh0_to_cycles
      _ = -f.f 0 := by
        simp [z0]
  have hcomp_zero :
      (f.f (-1) + M.d (-1) 0 ≫ h0) ≫ A.d (-1) 0 = 0 := by
    -- The residual degree-`-1` error maps to zero after `d_A^{-1}` by the chain-map equation.
    calc
      (f.f (-1) + M.d (-1) 0 ≫ h0) ≫ A.d (-1) 0
          = f.f (-1) ≫ A.d (-1) 0 + M.d (-1) 0 ≫ (h0 ≫ A.d (-1) 0) := by
              simp [Category.assoc]
      _ = M.d (-1) 0 ≫ f.f 0 + M.d (-1) 0 ≫ (h0 ≫ A.d (-1) 0) := by
            rw [f.comm (-1)]
      _ = M.d (-1) 0 ≫ f.f 0 + M.d (-1) 0 ≫ (-f.f 0) := by
            rw [hh0_degree_zero]
      _ = 0 := by
            simp
  have hmono : Mono (A.d (-1) 0) :=
    mono_d_negOne_zero_of_acyclic_strictlyGE_negOne hAcyclic hA
  refine ⟨h0, ?_, ?_⟩
  · simpa [hh0_degree_zero]
  · exact (cancel_mono (A.d (-1) 0)).1 (by simpa using hcomp_zero)

/-- Helper for Lemma 15.85.4: a degree-`0` correction datum already determines the whole
null-homotopy when the source is supported in degrees `≤ 0` and the target in degrees `≥ -1`. -/
lemma homotopy_of_single_degree_zero_component
    {M A : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hA : A.IsStrictlyGE (-1))
    {f : M ⟶ A}
    {h0 : M.X 0 ⟶ A.X (-1)}
    (hh0_zero : f.f 0 + h0 ≫ A.d (-1) 0 = 0)
    (hh0_negOne : f.f (-1) + M.d (-1) 0 ≫ h0 = 0) :
    Nonempty (Homotopy f 0) := by
  let hom : (i j : ℤ) → M.X i ⟶ A.X j :=
    fun i j ↦
      if hi : i = 0 then
        if hj : j = -1 then by
          subst hi
          subst hj
          exact -h0
        else
          0
      else
        0
  refine ⟨Homotopy.mk hom ?_ ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = -1
      · exfalso
        exact hij (by simpa [hj])
      · simp [hom, hj]
    · simp [hom, hi]
  · intro i
    by_cases hzero : i = 0
    · subst hzero
      have hcomp_zero :
          (-h0) ≫ A.d (-1) 0 = -(h0 ≫ A.d (-1) 0) := by
        simpa using CategoryTheory.Preadditive.neg_comp h0 (A.d (-1) 0)
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      -- In degree `0`, the chosen degree-zero correction is the only surviving homotopy term.
      calc
        f.f 0 = -(h0 ≫ A.d (-1) 0) := by
          exact eq_neg_of_add_eq_zero_left hh0_zero
        _ = (-h0) ≫ A.d (-1) 0 := by
          simpa using hcomp_zero.symm
        _ = M.d 0 1 ≫ hom 1 0 + hom 0 (-1) ≫ A.d (-1) 0 + 0 := by
          simp [hom]
    · by_cases hnegOne : i = -1
      · subst hnegOne
        have hcomp_neg :
            M.d (-1) 0 ≫ (-h0) = -(M.d (-1) 0 ≫ h0) := by
          simpa using CategoryTheory.Preadditive.comp_neg (M.d (-1) 0) h0
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp)]
        -- In degree `-1`, the target has no degree `-2` term, so only `d_M^{-1} ≫ h^0` remains.
        calc
          f.f (-1) = -(M.d (-1) 0 ≫ h0) := by
            exact eq_neg_of_add_eq_zero_left hh0_negOne
          _ = M.d (-1) 0 ≫ (-h0) := by
            simpa using hcomp_neg.symm
          _ = M.d (-1) 0 ≫ hom 0 (-1) + hom (-1) (-2) ≫ A.d (-2) (-1) + 0 := by
            simp [hom]
      · have hf_zero : f.f i = 0 := by
          by_cases hi : i < -1
          · exact (A.isZero_of_isStrictlyGE (-1) i hi).eq_of_tgt _ _
          · exact (M.isZero_of_isStrictlyLE 0 i (by omega)).eq_of_src _ _
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
        -- Outside degrees `-1` and `0`, both the map and the proposed homotopy vanish.
        calc
          f.f i = 0 := hf_zero
          _ = M.d i (i + 1) ≫ hom (i + 1) i + hom i (i - 1) ≫ A.d (i - 1) i + 0 := by
            simp [hom, hzero, hnegOne]

/-- Helper for Lemma 15.85.4: every map from a complex supported in degrees `≤ 0` with
projective degree `0` to an acyclic complex supported in degrees `≥ -1` is null-homotopic. -/
lemma homotopic_to_zero_of_projective_degree_zero_to_acyclic_strictlyGE_negOne
    {M A : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hAcyclic : A.Acyclic)
    (hA : A.IsStrictlyGE (-1))
    (f : M ⟶ A) :
    Nonempty (Homotopy f 0) := by
  -- Package the degree-`0` correction produced above into the unique possible homotopy.
  obtain ⟨h0, hh0_zero, hh0_negOne⟩ :=
    exists_degree_zero_null_homotopy_to_acyclic_strictlyGE_negOne hM hM0 hAcyclic hA f
  exact homotopy_of_single_degree_zero_component hM hA hh0_zero hh0_negOne

/-- Helper for Lemma 15.85.4: a self-homotopy of the zero map into an acyclic target supported
in degrees `≥ -1` is itself zero. -/
lemma homotopy_zero_zero_eq_zero_to_acyclic_strictlyGE_negOne
    {M A : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hAcyclic : A.Acyclic)
    (hA : A.IsStrictlyGE (-1))
    (H : Homotopy (0 : M ⟶ A) (0 : M ⟶ A)) :
    ∀ i j, H.hom i j = 0 := by
  intro i j
  ext x
  by_cases hrel : (ComplexShape.up ℤ).Rel j i
  · by_cases hi0 : i = 0
    · subst hi0
      have hj : j = -1 := by
        have hji : j + 1 = 0 := by
          simpa using hrel
        omega
      subst hj
      have hhom_one : H.hom 1 0 = 0 := by
        -- The source complex has no degree-`1` term, so the next homotopy component vanishes.
        exact (M.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_src _ _
      have hcomm_zero := H.comm 0
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hcomm_zero
      have hcomp_zero : H.hom 0 (-1) ≫ A.d (-1) 0 = 0 := by
        -- With both endpoint maps zero, the degree-`0` homotopy identity leaves only this term.
        simpa [hhom_one, add_assoc, add_left_comm, add_comm] using hcomm_zero.symm
      have hmono : Mono (A.d (-1) 0) :=
        mono_d_negOne_zero_of_acyclic_strictlyGE_negOne hAcyclic hA
      have hzero : H.hom 0 (-1) = 0 := by
        exact (cancel_mono (A.d (-1) 0)).1 (by simpa using hcomp_zero)
      exact congrArg (fun k : M.X 0 ⟶ A.X (-1) ↦ k.hom x) hzero
    · by_cases hi_lt : i < 0
      · have hj_lt : j < -1 := by
          have hji : j + 1 = i := by
            simpa using hrel
          omega
        -- Negative degrees force the target component to vanish because `A` starts in degree `-1`.
        exact congrArg
          (fun k : M.X i ⟶ A.X j ↦ k.hom x)
          ((A.isZero_of_isStrictlyGE (-1) j hj_lt).eq_of_tgt _ _)
      · have hi_pos : 0 < i := by
          omega
        -- Positive degrees force the source component to vanish because `M` stops in degree `0`.
        exact congrArg
          (fun k : M.X i ⟶ A.X j ↦ k.hom x)
          ((M.isZero_of_isStrictlyLE 0 i hi_pos).eq_of_src _ _)
  · -- Off the diagonal `j + 1 = i`, homotopy components are definitionally zero.
    exact congrArg
      (fun k : M.X i ⟶ A.X j ↦ k.hom x)
      (H.zero i j hrel)

/-- Helper for Lemma 15.85.4: if a homotopy into an acyclic target supported in degrees `≥ -1`
has both endpoints equal to zero, then every component of the homotopy vanishes. -/
lemma homotopy_components_zero_of_endpoint_eq_zero_to_acyclic_strictlyGE_negOne
    {M A : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hAcyclic : A.Acyclic)
    (hA : A.IsStrictlyGE (-1))
    {u v : M ⟶ A}
    (H : Homotopy u v)
    (hu : u = 0)
    (hv : v = 0) :
    ∀ i j, H.hom i j = 0 := by
  -- Rewriting the endpoints is enough; the zero-homotopy vanishing lemma handles the rest.
  subst hu
  subst hv
  exact homotopy_zero_zero_eq_zero_to_acyclic_strictlyGE_negOne hM hAcyclic hA H

/-- Helper for Lemma 15.85.4: postcomposing a homotopy with the cokernel projection kills each
diagonal component when the cokernel is acyclic and supported in degrees `≥ -1`. -/
lemma homotopy_compRight_cokernel_diagonal_eq_zero
    {M K I : Cpx}
    (hM : M.IsStrictlyLE 0)
    {ι : K ⟶ I}
    (hCac : (cokernel ι).Acyclic)
    (hCge : (cokernel ι).IsStrictlyGE (-1))
    {f g : M ⟶ K}
    (H : Homotopy (f ≫ ι) (g ≫ ι))
    (i : ℤ) :
    H.hom i (i - 1) ≫ (cokernel.π ι).f (i - 1) = 0 := by
  have hu : (f ≫ ι ≫ cokernel.π ι : M ⟶ cokernel ι) = 0 := by
    ext n x
    change (((ι ≫ cokernel.π ι).f n).hom ((f.f n).hom x)) = 0
    simp [cokernel.condition]
  have hv : (g ≫ ι ≫ cokernel.π ι : M ⟶ cokernel ι) = 0 := by
    ext n x
    change (((ι ≫ cokernel.π ι).f n).hom ((g.f n).hom x)) = 0
    simp [cokernel.condition]
  have hzero :
      (H.compRight (cokernel.π ι)).hom i (i - 1) = 0 :=
    homotopy_components_zero_of_endpoint_eq_zero_to_acyclic_strictlyGE_negOne
      hM hCac hCge (H.compRight (cokernel.π ι)) hu hv i (i - 1)
  -- `Homotopy.compRight_hom` exposes the desired concrete diagonal composite.
  simpa using hzero

/-- Helper for Lemma 15.85.4: a degreewise map to a termwise-monic complex descends once its
component is killed by the corresponding cokernel component. -/
lemma component_factor_along_termwise_mono_of_zero_cokernel
    {M K I : Cpx} (ι : K ⟶ I) (n : ℤ) [Mono (ι.f n)]
    (g : M.X n ⟶ I.X n) (hg : g ≫ (cokernel.π ι).f n = 0) :
    ∃ f : M.X n ⟶ K.X n, f ≫ ι.f n = g := by
  let e :
      parallelPair (ι.f n) 0 ≅
        parallelPair ι 0 ⋙ HomologicalComplex.eval (ModuleCat R) (up ℤ) n :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp)
      (by simp [HomologicalComplex.zero_f])
  let mapped :=
    (HomologicalComplex.eval (ModuleCat R) (up ℤ) n).mapCocone
      (CokernelCofork.ofπ (cokernel.π ι) (cokernel.condition ι))
  let s : CokernelCofork (ι.f n) := (Cocone.precompose e.hom).obj mapped
  let hs0 : IsColimit mapped :=
    isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (up ℤ) n)
      (cokernelIsCokernel ι)
  let hs : IsColimit s := (IsColimit.precomposeInvEquiv e.symm mapped).2 hs0
  -- The evaluated cokernel cofork is still colimit, so the mono component is a kernel there.
  let f : M.X n ⟶ K.X n :=
    (Abelian.monoIsKernelOfCokernel s hs).lift
      (KernelFork.ofι g (by simpa [s, mapped] using hg))
  refine ⟨f, ?_⟩
  -- The descended component is characterized by postcomposing back with `ι.f n`.
  exact (Abelian.monoIsKernelOfCokernel s hs).fac
    (KernelFork.ofι g (by simpa [s, mapped] using hg)) WalkingParallelPair.zero

/-- Helper for Lemma 15.85.4: any morphism into a termwise-monic component descends once its
composite with the corresponding cokernel component is zero. -/
lemma factor_morphism_along_termwise_mono_of_zero_cokernel
    {P : ModuleCat R} {K I : Cpx} (ι : K ⟶ I) (n : ℤ) [Mono (ι.f n)]
    (g : P ⟶ I.X n) (hg : g ≫ (cokernel.π ι).f n = 0) :
    ∃ f : P ⟶ K.X n, f ≫ ι.f n = g := by
  let e :
      parallelPair (ι.f n) 0 ≅
        parallelPair ι 0 ⋙ HomologicalComplex.eval (ModuleCat R) (up ℤ) n :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp)
      (by simp [HomologicalComplex.zero_f])
  let mapped :=
    (HomologicalComplex.eval (ModuleCat R) (up ℤ) n).mapCocone
      (CokernelCofork.ofπ (cokernel.π ι) (cokernel.condition ι))
  let s : CokernelCofork (ι.f n) := (Cocone.precompose e.hom).obj mapped
  let hs0 : IsColimit mapped :=
    isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (up ℤ) n)
      (cokernelIsCokernel ι)
  let hs : IsColimit s := (IsColimit.precomposeInvEquiv e.symm mapped).2 hs0
  let f : P ⟶ K.X n :=
    (Abelian.monoIsKernelOfCokernel s hs).lift
      (KernelFork.ofι g (by simpa [s, mapped] using hg))
  refine ⟨f, ?_⟩
  exact (Abelian.monoIsKernelOfCokernel s hs).fac
    (KernelFork.ofι g (by simpa [s, mapped] using hg)) WalkingParallelPair.zero

/-- Helper for Lemma 15.85.4: every morphism from a projective module into the evaluated
cokernel component lifts along that cokernel projection. -/
lemma projective_lift_along_cokernel_component
    {P : ModuleCat R} {K I : Cpx} (ι : K ⟶ I) (n : ℤ)
    [Projective P] (u : P ⟶ (cokernel ι).X n) :
    ∃ v : P ⟶ I.X n, v ≫ (cokernel.π ι).f n = u := by
  let e :
      parallelPair (ι.f n) 0 ≅
        parallelPair ι 0 ⋙ HomologicalComplex.eval (ModuleCat R) (up ℤ) n :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp)
      (by simp [HomologicalComplex.zero_f])
  let mapped :=
    (HomologicalComplex.eval (ModuleCat R) (up ℤ) n).mapCocone
      (CokernelCofork.ofπ (cokernel.π ι) (cokernel.condition ι))
  let s : CokernelCofork (ι.f n) := (Cocone.precompose e.hom).obj mapped
  let hs0 : IsColimit mapped :=
    isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (up ℤ) n)
      (cokernelIsCokernel ι)
  let hs : IsColimit s := (IsColimit.precomposeInvEquiv e.symm mapped).2 hs0
  let _ : Epi s.π := Cofork.IsColimit.epi hs
  -- The evaluated cokernel cofork makes `s.π` an epi, so projectivity gives a lift.
  let v : P ⟶ I.X n := Projective.factorThru (show P ⟶ s.pt from u) s.π
  refine ⟨v, ?_⟩
  have hv : v ≫ s.π = (show P ⟶ s.pt from u) := by
    exact Projective.factorThru_comp (show P ⟶ s.pt from u) s.π
  -- Switch back to the evaluated cokernel cofork point before using the lifted factorization.
  change v ≫ s.π = (show P ⟶ s.pt from u)
  exact hv

/-- Helper for Lemma 15.85.4: a chain map to a termwise-monic complex descends strictly once its
composite with the cokernel complex vanishes. -/
lemma descend_chainMap_along_termwise_mono_of_zero_cokernel_composite
    {M K I : Cpx} (ι : K ⟶ I) (hmono : ∀ n : ℤ, Mono (ι.f n))
    (g : M ⟶ I) (hg : g ≫ cokernel.π ι = 0) :
    ∃ f : M ⟶ K, f ≫ ι = g := by
  let descended : ∀ n : ℤ, M.X n ⟶ K.X n := fun n ↦
    letI : Mono (ι.f n) := hmono n
    Classical.choose
      (component_factor_along_termwise_mono_of_zero_cokernel ι n (g.f n) (by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          (congrArg (fun φ : M ⟶ cokernel ι ↦ φ.f n) hg)))
  have descended_fac : ∀ n : ℤ, descended n ≫ ι.f n = g.f n := by
    intro n
    letI : Mono (ι.f n) := hmono n
    exact Classical.choose_spec
      (component_factor_along_termwise_mono_of_zero_cokernel ι n (g.f n) (by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          (congrArg (fun φ : M ⟶ cokernel ι ↦ φ.f n) hg)))
  let f : M ⟶ K :=
    { f := descended
      comm' := fun i j hij ↦ by
        have hj : i + 1 = j := by simpa using hij
        subst j
        letI : Mono (ι.f (i + 1)) := hmono (i + 1)
        -- Check the chain-map equation after postcomposing with the monic target component.
        apply (cancel_mono (ι.f (i + 1))).1
        calc
          descended i ≫ K.d i (i + 1) ≫ ι.f (i + 1)
              = descended i ≫ (K.d i (i + 1) ≫ ι.f (i + 1)) := by
                  simp [Category.assoc]
          _ = descended i ≫ (ι.f i ≫ I.d i (i + 1)) := by
                rw [ι.comm i]
          _ = (descended i ≫ ι.f i) ≫ I.d i (i + 1) := by
                simp [Category.assoc]
          _ = g.f i ≫ I.d i (i + 1) := by
                rw [descended_fac i]
          _ = M.d i (i + 1) ≫ g.f (i + 1) := by
                exact g.comm i (i + 1)
          _ = M.d i (i + 1) ≫ (descended (i + 1) ≫ ι.f (i + 1)) := by
                rw [descended_fac (i + 1)]
          _ = (M.d i (i + 1) ≫ descended (i + 1)) ≫ ι.f (i + 1) := by
                simp }
  refine ⟨f, ?_⟩
  ext n x
  -- Equality of chain maps is checked degreewise on the underlying module morphisms.
  change (descended n ≫ ι.f n).hom x = (g.f n).hom x
  exact congrArg (fun k : M.X n ⟶ I.X n ↦ k.hom x) (by simpa [f] using descended_fac n)

/-- Helper for Lemma 15.85.4: a homotopy between maps that becomes visible only after
postcomposing with a termwise monomorphism already descends to the source target, provided the
cokernel target is acyclic and supported in degrees `≥ -1`. -/
lemma homotopy_of_diagonal_family_up
    {M K : Cpx} {f g : M ⟶ K}
    (hom : (i j : ℤ) → M.X i ⟶ K.X j)
    (hzero : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → hom i j = 0)
    (hs :
      ∀ i : ℤ,
        f.f i = M.d i (i + 1) ≫ hom (i + 1) i + hom i (i - 1) ≫ K.d (i - 1) i + g.f i) :
    Nonempty (Homotopy f g) := by
  refine ⟨Homotopy.mk hom ?_ ?_⟩
  · intro i j hij
    exact hzero i j hij
  · intro i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    -- The commutativity field is now exactly the assumed degree-`i` diagonal identity.
    exact hs i

/-- Helper for Lemma 15.85.4: the component of a chain-map morphism is compatible with index
transport on source and target objects. -/
lemma component_eqToHom_naturality
    {K I : Cpx} (ι : K ⟶ I) {j i : ℤ} (h : j = i) :
    ι.f j ≫ eqToHom (congrArg I.X h) =
      eqToHom (congrArg K.X h) ≫ ι.f i := by
  -- Reduce to the reflexive case, where both transports are identities.
  cases h
  simp

/-- Helper for Lemma 15.85.4: the successor diagonal composite can be rewritten using a stable
transport on both the source and target components. -/
lemma successor_diagonal_postcompose_cast_eq
    {M K I : Cpx} {ι : K ⟶ I} (i : ℤ)
    (s : M.X (i + 1) ⟶ K.X ((i + 1) - 1)) :
    s ≫ ι.f ((i + 1) - 1) ≫
        eqToHom (congrArg I.X (show ((i + 1 : ℤ) - 1) = i by omega)) =
      s ≫ eqToHom (congrArg K.X (show ((i + 1 : ℤ) - 1) = i by omega)) ≫ ι.f i := by
  -- Move the transport across the component `ι.f _` before using it in the homotopy equation.
  have h : ((i + 1 : ℤ) - 1) = i := by
    omega
  calc
    s ≫ ι.f ((i + 1) - 1) ≫ eqToHom (congrArg I.X h)
        = s ≫ (ι.f ((i + 1) - 1) ≫ eqToHom (congrArg I.X h)) := by
            simp
    _ = s ≫ (eqToHom (congrArg K.X h) ≫ ι.f i) := by
          rw [component_eqToHom_naturality (ι := ι) h]
    _ = s ≫ eqToHom (congrArg K.X h) ≫ ι.f i := by
          simp [Category.assoc]

/-- Helper for Lemma 15.85.4: if the diagonal components of a postcomposed homotopy already lift
degreewise through a termwise monomorphism, then the whole homotopy descends. -/
lemma diagonal_homotopy_descends_of_postcompose_eq
    {M K I : Cpx} {ι : K ⟶ I}
    (hmono : ∀ n : ℤ, Mono (ι.f n))
    {f g : M ⟶ K}
    (H : Homotopy (f ≫ ι) (g ≫ ι))
    (s : ∀ i : ℤ, M.X i ⟶ K.X (i - 1))
    (hs_fac : ∀ i : ℤ, s i ≫ ι.f (i - 1) = H.hom i (i - 1)) :
    Nonempty (Homotopy f g) := by
  -- Route correction: package the descended diagonal family separately, so the cancellation
  -- against `ι.f i` happens before building `Homotopy.mk`.
  let _ := hmono
  let hom : (i j : ℤ) → M.X i ⟶ K.X j := fun i j ↦
    if h : j = i - 1 then s i ≫ eqToHom (congrArg K.X h.symm) else 0
  refine homotopy_of_diagonal_family_up (hom := hom) ?_ ?_
  · intro i j hij
    by_cases h : j = i - 1
    · exfalso
      exact hij (by simp [h])
    · simp [hom, h]
  · intro i
    -- Check the diagonal identity after postcomposing with the monic component `ι.f i`.
    apply (cancel_mono (ι.f i)).1
    have hcomm := H.comm i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)] at hcomm
    have hs_succ :
        s (i + 1) ≫ eqToHom (congrArg K.X (show ((i + 1 : ℤ) - 1) = i by omega)) ≫ ι.f i =
          H.hom (i + 1) i := by
      have hs_succ' :=
        congrArg
          (fun k : M.X (i + 1) ⟶ I.X ((i + 1) - 1) ↦
            k ≫ eqToHom (congrArg I.X (show ((i + 1 : ℤ) - 1) = i by omega)))
          (hs_fac (i + 1))
      -- Rewrite the successor component using the dedicated transport-stable cast lemma.
      simpa [successor_diagonal_postcompose_cast_eq, Category.assoc] using hs_succ'
    have hs_prev :
        s i ≫ K.d (i - 1) i ≫ ι.f i = H.hom i (i - 1) ≫ I.d (i - 1) i := by
      -- Move the differential through `ι` and then substitute the lifted predecessor component.
      calc
        s i ≫ K.d (i - 1) i ≫ ι.f i
            = s i ≫ (K.d (i - 1) i ≫ ι.f i) := by simp
        _ = s i ≫ (ι.f (i - 1) ≫ I.d (i - 1) i) := by
              rw [ι.comm (i - 1)]
        _ = (s i ≫ ι.f (i - 1)) ≫ I.d (i - 1) i := by
              simp [Category.assoc]
        _ = H.hom i (i - 1) ≫ I.d (i - 1) i := by
              rw [hs_fac i]
    have hs_succ' :
        M.d i (i + 1) ≫ H.hom (i + 1) i =
          (M.d i (i + 1) ≫ hom (i + 1) i) ≫ ι.f i := by
      -- The successor lift is now in the exact shape consumed by the packaged diagonal family.
      rw [← hs_succ]
      simp [hom, Category.assoc]
    have hs_prev' :
        H.hom i (i - 1) ≫ I.d (i - 1) i =
          (hom i (i - 1) ≫ K.d (i - 1) i) ≫ ι.f i := by
      -- The predecessor lift is already uncast, so only the `hom` packaging remains.
      simpa [hom, Category.assoc] using hs_prev.symm
    calc
      f.f i ≫ ι.f i
          = M.d i (i + 1) ≫ H.hom (i + 1) i + H.hom i (i - 1) ≫ I.d (i - 1) i +
              g.f i ≫ ι.f i := by
                simpa [HomologicalComplex.comp_f, Category.assoc] using hcomm
      _ = (M.d i (i + 1) ≫ hom (i + 1) i) ≫ ι.f i +
            (hom i (i - 1) ≫ K.d (i - 1) i) ≫ ι.f i +
            g.f i ≫ ι.f i := by
              rw [hs_succ', hs_prev']
      _ = (M.d i (i + 1) ≫ hom (i + 1) i + hom i (i - 1) ≫ K.d (i - 1) i +
            g.f i) ≫ ι.f i := by
              simp [Category.assoc]

/-- Helper for Lemma 15.85.4: a homotopy between maps that becomes visible only after
postcomposing with a termwise monomorphism already descends to the source target, provided the
cokernel target is acyclic and supported in degrees `≥ -1`. -/
lemma homotopy_descend_along_termwise_mono
    {M K I : Cpx}
    (hM : M.IsStrictlyLE 0)
    {ι : K ⟶ I} (hmono : ∀ n : ℤ, Mono (ι.f n))
    (hCac : (cokernel ι).Acyclic)
    (hCge : (cokernel ι).IsStrictlyGE (-1))
    {f g : M ⟶ K}
    (hfg : Nonempty (Homotopy (f ≫ ι) (g ≫ ι))) :
    Nonempty (Homotopy f g) := by
  obtain ⟨H⟩ := hfg
  let descended : ∀ i : ℤ, M.X i ⟶ K.X (i - 1) := fun i ↦
    letI : Mono (ι.f (i - 1)) := hmono (i - 1)
    Classical.choose
      (factor_morphism_along_termwise_mono_of_zero_cokernel ι (i - 1) (H.hom i (i - 1))
        (homotopy_compRight_cokernel_diagonal_eq_zero hM hCac hCge H i))
  have hdescended_fac :
      ∀ i : ℤ, descended i ≫ ι.f (i - 1) = H.hom i (i - 1) := by
    intro i
    letI : Mono (ι.f (i - 1)) := hmono (i - 1)
    exact Classical.choose_spec
      (factor_morphism_along_termwise_mono_of_zero_cokernel ι (i - 1) (H.hom i (i - 1))
        (homotopy_compRight_cokernel_diagonal_eq_zero hM hCac hCge H i))
  -- The cokernel argument already produces the diagonal lifts; the new packaging helper turns
  -- them into an honest homotopy after one cancellation step.
  exact diagonal_homotopy_descends_of_postcompose_eq hmono H descended hdescended_fac

/-- Helper for Lemma 15.85.4: a single correction map `h^0 : M^0 ⟶ I^{-1}` can be packaged as a
new chain map that only changes degrees `0` and `-1`, together with the corresponding
one-component homotopy. -/
lemma correct_chainMap_by_degree_zero_homotopy_component
    {M I : Cpx} (g : M ⟶ I) (h0 : M.X 0 ⟶ I.X (-1)) :
    ∃ g' : M ⟶ I, ∃ H : Homotopy g g',
      g'.f 0 = g.f 0 + h0 ≫ I.d (-1) 0 ∧
      g'.f (-1) = g.f (-1) + M.d (-1) 0 ≫ h0 ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ -1 → g'.f i = g.f i) ∧
      H.hom 0 (-1) = -h0 := by
  let corrected : (n : ℤ) → M.X n ⟶ I.X n := fun n ↦
    if hn0 : n = 0 then
      hn0 ▸ (g.f 0 + h0 ≫ I.d (-1) 0)
    else if hnnegOne : n = -1 then
      hnnegOne ▸ (g.f (-1) + M.d (-1) 0 ≫ h0)
    else
      g.f n
  have hcorrected_zero : corrected 0 = g.f 0 + h0 ≫ I.d (-1) 0 := by
    simp [corrected]
  have hcorrected_negOne : corrected (-1) = g.f (-1) + M.d (-1) 0 ≫ h0 := by
    simp [corrected]
  have hcorrected_other (i : ℤ) (hi0 : i ≠ 0) (hinegOne : i ≠ -1) :
      corrected i = g.f i := by
    simp [corrected, hi0, hinegOne]
  let g' : M ⟶ I :=
    { f := corrected
      comm' := fun i j hij ↦ by
        have hj : j = i + 1 := by
          simpa using hij.symm
        subst j
        by_cases hi0 : i = 0
        · subst hi0
          have hd_comp : I.d (-1) 0 ≫ I.d 0 1 = 0 := by
            simpa using I.d_comp_d (-1) 0 1
          -- Only the added degree-`0` correction contributes here, and it dies by `d ∘ d = 0`.
          calc
            corrected 0 ≫ I.d 0 1
                = (g.f 0 + h0 ≫ I.d (-1) 0) ≫ I.d 0 1 := by
                    rw [hcorrected_zero]
            _ = g.f 0 ≫ I.d 0 1 + h0 ≫ (I.d (-1) 0 ≫ I.d 0 1) := by
                  simp [Category.assoc]
            _ = g.f 0 ≫ I.d 0 1 := by
                  simp [hd_comp]
            _ = M.d 0 1 ≫ g.f 1 := by
                  simpa using g.comm 0 1
            _ = M.d 0 1 ≫ corrected 1 := by
                  rw [hcorrected_other 1 (by omega) (by omega)]
        · by_cases hinegOne : i = -1
          · subst hinegOne
            -- In degree `-1`, the correction is exactly the boundary of `h^0`.
            calc
              corrected (-1) ≫ I.d (-1) 0
                  = (g.f (-1) + M.d (-1) 0 ≫ h0) ≫ I.d (-1) 0 := by
                      rw [hcorrected_negOne]
              _ = g.f (-1) ≫ I.d (-1) 0 + M.d (-1) 0 ≫ (h0 ≫ I.d (-1) 0) := by
                    simp [Category.assoc]
              _ = M.d (-1) 0 ≫ g.f 0 + M.d (-1) 0 ≫ (h0 ≫ I.d (-1) 0) := by
                    simpa using g.comm (-1) 0
              _ = M.d (-1) 0 ≫ (g.f 0 + h0 ≫ I.d (-1) 0) := by
                    simp [Category.assoc]
              _ = M.d (-1) 0 ≫ corrected 0 := by
                    rw [hcorrected_zero]
          · by_cases hinegTwo : i = -2
            · subst hinegTwo
              have hd_comp : M.d (-2) (-1) ≫ M.d (-1) 0 = 0 := by
                simpa using M.d_comp_d (-2) (-1) 0
              -- The degree `-1` correction is invisible one step lower because `d ∘ d = 0`.
              calc
                corrected (-2) ≫ I.d (-2) (-1)
                    = g.f (-2) ≫ I.d (-2) (-1) := by
                        rw [hcorrected_other (-2) (by omega) (by omega)]
                _ = M.d (-2) (-1) ≫ g.f (-1) := by
                      simpa using g.comm (-2) (-1)
                _ = M.d (-2) (-1) ≫ (g.f (-1) + M.d (-1) 0 ≫ h0) := by
                      simp [Category.assoc, hd_comp]
                _ = M.d (-2) (-1) ≫ corrected (-1) := by
                      rw [hcorrected_negOne]
            · -- Away from degrees `0`, `-1`, and `-2`, nothing changed.
              simpa [hcorrected_other i hi0 hinegOne,
                hcorrected_other (i + 1) (by omega) (by omega)] using g.comm i (i + 1) }
  let hom : (i j : ℤ) → M.X i ⟶ I.X j := fun i j ↦
    if hi0 : i = 0 then
      if hjnegOne : j = -1 then
        hi0 ▸ hjnegOne ▸ (-h0)
      else
        0
    else
      0
  let H : Homotopy g g' :=
    Homotopy.mk hom
      (by
        intro i j hij
        by_cases hi0 : i = 0
        · subst hi0
          by_cases hjnegOne : j = -1
          · exact (hij (by simpa [hjnegOne])).elim
          · simp [hom, hjnegOne]
        · simp [hom, hi0])
      (by
        intro i
        by_cases hi0 : i = 0
        · subst hi0
          have hneg_comp :
              (-h0) ≫ I.d (-1) 0 = -(h0 ≫ I.d (-1) 0) := by
            simpa using CategoryTheory.Preadditive.neg_comp h0 (I.d (-1) 0)
          rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
            prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
          -- The degree-`0` homotopy equation records the added boundary `h^0 d_I^{-1}`.
          have hcomm :
              g.f 0 =
                M.d 0 1 ≫ hom 1 0 + hom 0 (-1) ≫ I.d (-1) 0 + corrected 0 := by
            simp [hom, hcorrected_zero, hneg_comp, add_assoc, add_left_comm, add_comm]
          simpa [g'] using hcomm
        · by_cases hinegOne : i = -1
          · subst hinegOne
            have hcomp_neg :
                M.d (-1) 0 ≫ (-h0) = -(M.d (-1) 0 ≫ h0) := by
              simpa using CategoryTheory.Preadditive.comp_neg (M.d (-1) 0) h0
            rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
              prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp)]
            -- The degree-`-1` homotopy equation records the added source boundary.
            have hcomm :
                g.f (-1) =
                  M.d (-1) 0 ≫ hom 0 (-1) + hom (-1) (-2) ≫ I.d (-2) (-1) +
                    corrected (-1) := by
              simp [hom, hcorrected_negOne, hcomp_neg, add_assoc, add_left_comm, add_comm]
            simpa [g'] using hcomm
          · -- Outside degrees `0` and `-1`, the homotopy is zero and the map is unchanged.
            have hhom_next : hom (i + 1) i = 0 := by
              have hnext0 : i + 1 ≠ 0 := by
                omega
              simp [hom, hnext0]
            have hhom_prev : hom i (i - 1) = 0 := by
              simp [hom, hi0]
            rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
              prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
            calc
              g.f i = corrected i := by
                rw [hcorrected_other i hi0 hinegOne]
              _ = M.d i (i + 1) ≫ hom (i + 1) i + hom i (i - 1) ≫ I.d (i - 1) i +
                    corrected i := by
                      simp [hhom_next, hhom_prev])
  refine ⟨g', H, hcorrected_zero, hcorrected_negOne, ?_, ?_⟩
  · intro i hi0 hinegOne
    exact hcorrected_other i hi0 hinegOne
  · simp [H, hom]

/-- Helper for Lemma 15.85.4: if the target complex starts in degree `-1`, then the cokernel of
any map into it also starts in degree `-1`. -/
lemma cokernel_strictlyGE_of_target_strictlyGE
    {K I : Cpx} (ι : K ⟶ I) (hI : I.IsStrictlyGE (-1)) :
    (cokernel ι).IsStrictlyGE (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  letI : I.IsStrictlyGE (-1) := hI
  -- Each cokernel term is an epimorphic image of the corresponding target term.
  exact Limits.IsZero.of_epi ((cokernel.π ι).f n) (I.isZero_of_isStrictlyGE (-1) n hn)

/-- Helper for Lemma 15.85.4: a map into the injective resolution target can be corrected by a
single degree-`0` homotopy component so that its cokernel composite vanishes strictly. -/
lemma exists_homotopic_map_with_zero_cokernel_composite
    {M K I : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    {ι : K ⟶ I}
    (hCac : (cokernel ι).Acyclic)
    (hCge : (cokernel ι).IsStrictlyGE (-1))
    (g : M ⟶ I) :
    ∃ g' : M ⟶ I, Nonempty (Homotopy g g') ∧ g' ≫ cokernel.π ι = 0 := by
  obtain ⟨h0C, hh0_zero, hh0_negOne⟩ :=
    exists_degree_zero_null_homotopy_to_acyclic_strictlyGE_negOne hM hM0 hCac hCge
      (g ≫ cokernel.π ι)
  letI : Projective (M.X 0) := hM0
  obtain ⟨h0I, hh0I⟩ := projective_lift_along_cokernel_component ι (-1) h0C
  obtain ⟨g', H, hg'zero, hg'negOne, hg'other, _⟩ :=
    correct_chainMap_by_degree_zero_homotopy_component g h0I
  refine ⟨g', ⟨H⟩, ?_⟩
  ext n x
  by_cases hzero : n = 0
  · subst hzero
    have hcomp_zero : g'.f 0 ≫ (cokernel.π ι).f 0 = 0 := by
      -- The corrected degree-`0` component is exactly the chosen null-homotopy equation on the
      -- cokernel complex after lifting `h^0` through the cokernel projection.
      calc
        g'.f 0 ≫ (cokernel.π ι).f 0
            = (g.f 0 + h0I ≫ I.d (-1) 0) ≫ (cokernel.π ι).f 0 := by
                rw [hg'zero]
        _ = g.f 0 ≫ (cokernel.π ι).f 0 +
              h0I ≫ (I.d (-1) 0 ≫ (cokernel.π ι).f 0) := by
                simp [Category.assoc]
        _ = g.f 0 ≫ (cokernel.π ι).f 0 +
              h0I ≫ ((cokernel.π ι).f (-1) ≫ (cokernel ι).d (-1) 0) := by
                rw [(cokernel.π ι).comm (-1)]
        _ = g.f 0 ≫ (cokernel.π ι).f 0 +
              (h0I ≫ (cokernel.π ι).f (-1)) ≫ (cokernel ι).d (-1) 0 := by
                simp [Category.assoc]
        _ = g.f 0 ≫ (cokernel.π ι).f 0 + h0C ≫ (cokernel ι).d (-1) 0 := by
              rw [hh0I]
        _ = 0 := by
              simpa [HomologicalComplex.comp_f, Category.assoc] using hh0_zero
    exact congrArg (fun k : M.X 0 ⟶ (cokernel ι).X 0 ↦ k.hom x) hcomp_zero
  · by_cases hnegOne : n = -1
    · subst hnegOne
      have hcomp_negOne : g'.f (-1) ≫ (cokernel.π ι).f (-1) = 0 := by
        -- The corrected degree-`-1` component is the second null-homotopy equation.
        calc
          g'.f (-1) ≫ (cokernel.π ι).f (-1)
              = (g.f (-1) + M.d (-1) 0 ≫ h0I) ≫ (cokernel.π ι).f (-1) := by
                  rw [hg'negOne]
          _ = g.f (-1) ≫ (cokernel.π ι).f (-1) +
                M.d (-1) 0 ≫ (h0I ≫ (cokernel.π ι).f (-1)) := by
                  simp [Category.assoc]
          _ = g.f (-1) ≫ (cokernel.π ι).f (-1) + M.d (-1) 0 ≫ h0C := by
                rw [hh0I]
          _ = 0 := by
                simpa [HomologicalComplex.comp_f, Category.assoc] using hh0_negOne
      exact congrArg (fun k : M.X (-1) ⟶ (cokernel ι).X (-1) ↦ k.hom x) hcomp_negOne
    · by_cases hlt : n < -1
      · letI : (cokernel ι).IsStrictlyGE (-1) := hCge
        exact congrArg
          (fun k : M.X n ⟶ (cokernel ι).X n ↦ k.hom x)
          (((cokernel ι).isZero_of_isStrictlyGE (-1) n hlt).eq_of_tgt
            (g'.f n ≫ (cokernel.π ι).f n) 0)
      · have hgt : 0 < n := by
          omega
        have hg'n : g'.f n = 0 := by
          rw [hg'other n hzero hnegOne]
          exact (M.isZero_of_isStrictlyLE 0 n hgt).eq_of_src _ _
        change (((cokernel.π ι).f n).hom ((g'.f n).hom x)) = 0
        simp [hg'n]

/-- Helper for Lemma 15.85.4: postcomposition with a termwise-monic injective-resolution map is
already bijective on homotopy classes out of a complex supported in degrees `≤ 0` with
projective degree `0`. -/
lemma homotopyCategory_postcomp_bijective_of_termwise_mono_from_projective_degree_zero
    {M K I : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    {ι : K ⟶ I}
    (hmono : ∀ n : ℤ, Mono (ι.f n))
    (hCac : (cokernel ι).Acyclic)
    (hCge : (cokernel ι).IsStrictlyGE (-1)) :
    Function.Bijective
      (fun φ : (KQ).obj M ⟶ (KQ).obj K ↦ φ ≫ (KQ).map ι) := by
  let Ho := HomotopyCategory.quotient (ModuleCat R) (up ℤ)
  refine ⟨?_, ?_⟩
  · intro φ₁ φ₂ hφ
    obtain ⟨f₁, rfl⟩ := Ho.map_surjective φ₁
    obtain ⟨f₂, rfl⟩ := Ho.map_surjective φ₂
    -- Equality after postcomposition is equality in the quotient, hence a homotopy after
    -- unpacking it and descending the homotopy through the termwise monomorphisms.
    obtain ⟨H⟩ :=
      homotopy_descend_along_termwise_mono hM hmono hCac hCge
        ⟨HomotopyCategory.homotopyOfEq _ _ (by simpa [Functor.map_comp] using hφ)⟩
    exact HomotopyCategory.eq_of_homotopy _ _ H
  · intro ψ
    obtain ⟨g, rfl⟩ := Ho.map_surjective ψ
    obtain ⟨g', ⟨H⟩, hg'⟩ :=
      exists_homotopic_map_with_zero_cokernel_composite hM hM0 hCac hCge g
    obtain ⟨f, hf⟩ :=
      descend_chainMap_along_termwise_mono_of_zero_cokernel_composite ι hmono g' hg'
    refine ⟨Ho.map f, ?_⟩
    -- First strictify the representative on the cokernel side, then descend it strictly along
    -- the termwise monomorphism `ι`.
    calc
      Ho.map f ≫ Ho.map ι = Ho.map (f ≫ ι) := by
        simp [Functor.map_comp]
      _ = Ho.map g' := by
            rw [hf]
      _ = Ho.map g := by
            exact (HomotopyCategory.eq_of_homotopy _ _ H).symm

/-- Helper for Lemma 15.85.4: postcomposition by a quasi-isomorphism is bijective in the derived
category because the induced map in `D(R)` is an isomorphism. -/
lemma derived_postcomp_bijective_of_quasiIso_moduleCat
    {M K I : Cpx} (ι : K ⟶ I) [QuasiIso ι] :
    Function.Bijective
      (fun g : Qh.obj ((KQ).obj M) ⟶ Qh.obj ((KQ).obj K) ↦
        g ≫ Qh.map ((KQ).map ι)) := by
  have hQι : IsIso (Qh.map ((KQ).map ι)) := by
    exact ((NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (ModuleCat R)) ι)).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) ι).2 inferInstance)
  letI : IsIso (Qh.map ((KQ).map ι)) := hQι
  refine ⟨?_, ?_⟩
  · intro g₁ g₂ h
    exact (cancel_mono (Qh.map ((KQ).map ι))).1 h
  · intro g
    -- Surjectivity is witnessed by postcomposing with the inverse isomorphism in `D(R)`.
    refine ⟨g ≫ inv (Qh.map ((KQ).map ι)), ?_⟩
    simp [Category.assoc]

/-- Helper for Lemma 15.85.4: the comparison map `Qh.map` commutes with postcomposition by the
injective-resolution comparison morphism. -/
lemma comparison_square_postcomp_injectiveResolution
    {M K I : Cpx} (ι : K ⟶ I) :
    ((Qh.map : ((KQ).obj M ⟶ (KQ).obj I) → _) ∘
        fun φ : (KQ).obj M ⟶ (KQ).obj K ↦ φ ≫ (KQ).map ι) =
      (fun ψ : Qh.obj ((KQ).obj M) ⟶ Qh.obj ((KQ).obj K) ↦
          ψ ≫ Qh.map ((KQ).map ι)) ∘
        (Qh.map : ((KQ).obj M ⟶ (KQ).obj K) → _) := by
  -- This is the functoriality square of `Qh`.
  funext φ
  simp [Functor.map_comp]

-- Proof sketch: resolve `K^•` by a termwise-monic bounded-below injective resolution
-- `ι : K^• ⟶ I^•`. Since `I^•` is bounded below injective, every derived morphism
-- `M^• ⟶ K^•` is represented by an honest map `M^• ⟶ I^•`. The cokernel of `ι` is acyclic and
-- still supported in degrees `≥ -1`, so projectivity of `M^0` makes every map
-- `M^• ⟶ cokernel ι` null-homotopic by a one-step correction in degree `0`; this descends maps
-- and homotopies from `I^•` back to `K^•`.
/-- Lemma 15.85.4 (1): if `M^•` is zero in positive degrees with `M^0` projective, and `K^•` is
zero in degrees `≤ -2`, then the canonical comparison
`Hom_{K(R)}(M^•, K^•) → Hom_{D(R)}(M^•, K^•)` is bijective. -/
theorem homotopyCategory_to_derived_bijective_of_projective_degree_zero
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-1)) :
    Function.Bijective (Qh.map : ((KQ).obj M ⟶ (KQ).obj K) → _) := by
  -- Route correction: the earlier source-side kernel route was aiming at a false normal-form
  -- helper. The corrected source-faithful plan resolves the target by a termwise-monic injective
  -- resolution and descends through its acyclic cokernel.
  -- TODO: instantiate `exists_injectiveResolution_strictlyGE_with_termwise_mono` at the exact
  -- hidden `ModuleCat` universe of the local notation `Cpx`, then finish with the already-built
  -- square of bijections:
  -- `hpostHo`, `derived_postcomp_bijective_of_quasiIso_moduleCat`,
  -- `comparison_square_postcomp_injectiveResolution`, and
  -- `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedBelow_injective`.
  sorry

-- Proof sketch: if `a^{-1} + h^0 d_M^{-1} = 0`, modify `a^•` by the homotopy with only
-- degree-zero component `h^0` to kill degree `-1`; then every map `K^• ⟶ N[1]` is homotopic to
-- one vanishing in degree `0`, so the induced `Ext^1` map is zero. Conversely, test against the
-- canonical class in `Ext^1_R(K^•, K^{-1})` and use part `(1)` to recover the required `h^0`.
/-- Lemma 15.85.4 (2): assume `K^•` is zero outside degrees `-1` and `0`, and `K^0` is
projective. For a map of complexes `a^• : M^• ⟶ K^•`, the induced maps
`Ext^1_R(K^•, N) → Ext^1_R(M^•, N)` vanish for all `R`-modules `N` if and only if there exists
`h^0 : M^0 ⟶ K^{-1}` with `a^{-1} + h^0 ∘ d_M^{-1} = 0`. -/
theorem inducesZeroOnModuleExt1_iff_exists_degree_zero_homotopy
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hKge : K.IsStrictlyGE (-1))
    (hKle : K.IsStrictlyLE 0)
    (hK0 : Projective (K.X 0))
    (a : M ⟶ K) :
    (∀ (N : ModuleCat R) (e : ShiftedHom (Q.obj K) ((single₀).obj N) (1 : ℤ)),
      Q.map a ≫ e = 0) ↔
      ∃ h0 : M.X 0 ⟶ K.X (-1), a.f (-1) + M.d (-1) 0 ≫ h0 = 0 := by
  -- TODO: first represent maps to shifted singles by honest chain maps using part `(1)`, then
  -- identify null-homotopies with the unique degree-zero component allowed by the support bounds.
  sorry

-- Proof sketch: choose a projective resolution `F^• → M^•` as in the proof of part `(1)` and a
-- representative `b^• : F^• ⟶ K^•` of `α`. The hypothesis on the composition with the canonical
-- projection to `K^{-2}[2]` lets one modify `b^•` by a homotopy so that its degree `-2`
-- component is exactly `a ∘ p^{-2}`; the support assumptions on `M^•` and `K^•` then force the
-- remaining components to factor through `M^•`, yielding a representative `a^• : M^• ⟶ K^•`
-- with prescribed degree `-2` term.
/-- Lemma 15.85.4 (3): assume `K^•` is zero in degrees `≤ -3`. Let
`α : Hom_{D(R)}(M^•, K^•)`. If the composite of `α` with the canonical projection
`K^• → K^{-2}[2]` comes from a module map `a : M^{-2} ⟶ K^{-2}` satisfying
`a ∘ d_M^{-3} = 0`, then `α` is represented by a map of complexes
`a^• : M^• ⟶ K^•` whose degree `-2` component is `a`. -/
theorem exists_representative_with_prescribed_degree_negTwo
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    (α : Q.obj M ⟶ Q.obj K)
    (a : M.X (-2) ⟶ K.X (-2))
    (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : α ≫ negTwoProjection K hK = negTwoCocycleToShift a ha) :
    ∃ aMap : M ⟶ K, Q.map aMap = α ∧ aMap.f (-2) = a := by
  -- TODO: move `α` to a bounded-above projective resolution of `M`, normalize the degree `-2`
  -- component there using `negTwoProjection`, and then descend the representative back to `M`.
  sorry

/-- Helper for Lemma 15.85.4: if the source is supported in degrees `≤ 0` and the target in
degrees `≥ -2`, then a homotopy between maps with the same degree `-2` component collapses to the
displayed degree `-1` and `0` formulas. -/
lemma homotopy_support_collapse_for_low_source_and_target
    {M K : Cpx} {aMap aMap' : M ⟶ K}
    (h : Homotopy aMap' aMap)
    (hM : M.IsStrictlyLE 0)
    (hK : K.IsStrictlyGE (-2))
    (hnegTwo : aMap.f (-2) = aMap'.f (-2)) :
    M.d (-2) (-1) ≫ h.hom (-1) (-2) = 0 ∧
      aMap'.f (-1) =
        aMap.f (-1) + h.hom (-1) (-2) ≫ K.d (-2) (-1) + M.d (-1) 0 ≫ h.hom 0 (-1) ∧
      aMap'.f 0 = aMap.f 0 + h.hom 0 (-1) ≫ K.d (-1) 0 := by
  -- The support hypotheses force the only potentially nonzero homotopy components to sit in
  -- degrees `-1` and `0`.
  have hhom_one : h.hom 1 0 = 0 := by
    exact (M.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_src _ _
  have hhom_negTwo : h.hom (-2) (-3) = 0 := by
    exact (K.isZero_of_isStrictlyGE (-2) (-3) (by omega)).eq_of_tgt _ _
  -- Rewrite the homotopy identities in the concrete cochain-complex degrees we need.
  have hcomm_negTwo := h.comm (-2)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-3) (-2) by simp)] at hcomm_negTwo
  have hzero : M.d (-2) (-1) ≫ h.hom (-1) (-2) = 0 := by
    simpa [hhom_negTwo, hnegTwo] using hcomm_negTwo
  have hcomm_negOne := h.comm (-1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp)] at hcomm_negOne
  have hcomm_zero := h.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hcomm_zero
  have hzero_degZero : aMap'.f 0 = aMap.f 0 + h.hom 0 (-1) ≫ K.d (-1) 0 := by
    simpa [hhom_one, add_assoc, add_left_comm, add_comm] using hcomm_zero
  refine ⟨hzero, ?_⟩
  refine ⟨?_, hzero_degZero⟩
  simpa [add_assoc, add_left_comm, add_comm] using hcomm_negOne

/-- Helper for Lemma 15.85.4: a null-homotopy of a map to the cochain-level shifted single
complex `N[1]` is already determined in degree `0`, and therefore yields the expected
degree-`-1` equation. -/
lemma exists_degree_zero_component_of_null_homotopic_to_shifted_single
    {M : Cpx}
    (hM : M.IsStrictlyLE 0)
    (N : ModuleCat R)
    (f : M ⟶ (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦(1 : ℤ)⟧)) :
    Nonempty (Homotopy f 0) →
      ∃ h0 : M.X 0 ⟶ ((((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦
        (1 : ℤ)⟧).X (-1)),
        f.f (-1) + M.d (-1) 0 ≫ h0 = 0 := by
  let S : Cpx := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N
  let K : Cpx := (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦(1 : ℤ)⟧)
  let fK : M ⟶ K := f
  have hS : S.IsStrictlyGE 0 := by
    dsimp [S]
    infer_instance
  have hKnegOne : K.IsStrictlyGE (-1) := by
    letI : S.IsStrictlyGE 0 := hS
    simpa [K, S] using S.isStrictlyGE_shift 0 (1 : ℤ) (-1) (by omega)
  letI : K.IsStrictlyGE (-1) := hKnegOne
  have hK : K.IsStrictlyGE (-2) := by
    exact K.isStrictlyGE_of_ge (-2) (-1) (by omega)
  intro hf
  obtain ⟨h⟩ := (show Nonempty (Homotopy fK 0) from hf)
  -- The shifted single complex is already zero in degree `-2`, so the degree `-2` components
  -- of `fK` and of the zero map agree automatically.
  have hnegTwo : (0 : M ⟶ K).f (-2) = fK.f (-2) := by
    exact (K.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_tgt _ _
  rcases homotopy_support_collapse_for_low_source_and_target
      (aMap := 0) (aMap' := fK) h hM hK hnegTwo with
    ⟨_, hnegOne, _⟩
  have hKd : K.d (-2) (-1) = 0 := by
    exact (K.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_src _ _
  -- After collapsing the unused homotopy components, only the degree-zero term survives.
  have hnegOne' : fK.f (-1) = M.d (-1) 0 ≫ h.hom 0 (-1) := by
    simpa [hKd] using hnegOne
  refine ⟨-h.hom 0 (-1), ?_⟩
  calc
    f.f (-1) + M.d (-1) 0 ≫ (-h.hom 0 (-1))
        = fK.f (-1) - M.d (-1) 0 ≫ h.hom 0 (-1) := by
            change
              fK.f (-1) + M.d (-1) 0 ≫ (-h.hom 0 (-1)) =
                fK.f (-1) - M.d (-1) 0 ≫ h.hom 0 (-1)
            simp [sub_eq_add_neg]
    _ = 0 := by
      simp [hnegOne']

/-- Helper for Lemma 15.85.4: for maps to the shifted single complex `N[1]`, a null-homotopy is
equivalent to choosing the unique possible degree-zero homotopy component that kills the degree
`-1` term. -/
lemma null_homotopic_to_shifted_single_iff_exists_degree_zero_component
    {M : Cpx}
    (hM : M.IsStrictlyLE 0)
    (N : ModuleCat R)
    (f : M ⟶ (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦(1 : ℤ)⟧)) :
    Nonempty (Homotopy f 0) ↔
      ∃ h0 : M.X 0 ⟶ ((((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦
        (1 : ℤ)⟧).X (-1)),
        f.f (-1) + M.d (-1) 0 ≫ h0 = 0 := by
  let S : Cpx := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N
  let K : Cpx := (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦(1 : ℤ)⟧)
  let fK : M ⟶ K := f
  refine ⟨exists_degree_zero_component_of_null_homotopic_to_shifted_single hM N f, ?_⟩
  rintro ⟨h0, hh0⟩
  have hSge : S.IsStrictlyGE 0 := by
    dsimp [S]
    infer_instance
  have hSle : S.IsStrictlyLE 0 := by
    dsimp [S]
    infer_instance
  have hKge : K.IsStrictlyGE (-1) := by
    letI : S.IsStrictlyGE 0 := hSge
    simpa [K, S] using S.isStrictlyGE_shift 0 (1 : ℤ) (-1) (by omega)
  have hKle : K.IsStrictlyLE (-1) := by
    letI : S.IsStrictlyLE 0 := hSle
    simpa [K, S] using S.isStrictlyLE_shift 0 (1 : ℤ) (-1) (by omega)
  let hom : (i j : ℤ) → M.X i ⟶ K.X j :=
    fun i j ↦
      if hi : i = 0 then
        if hj : j = -1 then by
          subst hi
          subst hj
          exact -h0
        else
          0
      else
        0
  refine ⟨Homotopy.mk hom ?_ ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = -1
      · exfalso
        exact hij (by simpa [hj])
      · simp [hom, hj]
    · simp [hom, hi]
  · intro i
    by_cases hzero : i = 0
    · subst hzero
      have hf_zero : fK.f 0 = 0 := by
        exact (K.isZero_of_isStrictlyLE (-1) 0 (by omega)).eq_of_tgt _ _
      have hKd_zero : K.d (-1) 0 = 0 := by
        exact (K.isZero_of_isStrictlyLE (-1) 0 (by omega)).eq_of_tgt _ _
      have hcomp_zero : (-h0) ≫ (0 : K.X (-1) ⟶ K.X 0) = 0 := by
        exact (K.isZero_of_isStrictlyLE (-1) 0 (by omega)).eq_of_tgt _ _
      have hrhs_zero :
          M.d 0 1 ≫ hom 1 0 + hom 0 (-1) ≫ K.d (-1) 0 = 0 := by
        exact (K.isZero_of_isStrictlyLE (-1) 0 (by omega)).eq_of_tgt _ _
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      -- In degree `0`, only the `h^0 ≫ d_K^{-1}` term can survive, but that differential is zero.
      calc
        fK.f 0 = 0 := hf_zero
        _ = (-h0) ≫ (0 : K.X (-1) ⟶ K.X 0) := by
          simpa using hcomp_zero.symm
        _ = M.d 0 1 ≫ hom 1 0 + hom 0 (-1) ≫ K.d (-1) 0 + 0 := by
          rw [hcomp_zero, hrhs_zero]
          simp
    · by_cases hnegOne : i = -1
      · subst hnegOne
        have hcomp_neg :
            M.d (-1) 0 ≫ (-h0) = -(M.d (-1) 0 ≫ h0) := by
          simpa using CategoryTheory.Preadditive.comp_neg (M.d (-1) 0) h0
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp)]
        -- In degree `-1`, the chosen degree-zero component is exactly the correction term.
        calc
          fK.f (-1) = -(M.d (-1) 0 ≫ h0) := by
            exact eq_neg_of_add_eq_zero_left hh0
          _ = M.d (-1) 0 ≫ (-h0) := by
            simpa using hcomp_neg.symm
          _ = M.d (-1) 0 ≫ hom 0 (-1) + hom (-1) (-2) ≫ K.d (-2) (-1) + 0 := by
            have hhom_neg : hom (-1) (-2) = 0 := by
              simp [hom]
            have hzero_comp : (0 : M.X (-1) ⟶ K.X (-2)) ≫ K.d (-2) (-1) = 0 := by
              simp
            rw [hhom_neg, hzero_comp, add_zero]
            simpa [hom]
      · have hf_zero : fK.f i = 0 := by
          by_cases hi : i < -1
          · exact (K.isZero_of_isStrictlyGE (-1) i hi).eq_of_tgt _ _
          · exact (K.isZero_of_isStrictlyLE (-1) i (by omega)).eq_of_tgt _ _
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
        -- Outside degrees `-1` and `0`, both the map and the proposed homotopy vanish.
        calc
          fK.f i = 0 := hf_zero
          _ = M.d i (i + 1) ≫ hom (i + 1) i + hom i (i - 1) ≫ K.d (i - 1) i + 0 := by
            simp [hom, hzero, hnegOne]

-- Proof sketch: a homotopy between two representatives with the same image in `D(R)` can be
-- chosen on a projective resolution of `M^•`; arguing as in part `(3)`, it factors through
-- `M^•`. If the degree `-2` components already agree, then the support assumptions on `K^•`
-- force the remaining homotopy to have only degree `-1` and degree `0` components, giving
-- exactly the displayed formulas.
/-- Lemma 15.85.4 (4): under the hypotheses of part `(3)`, any two representatives of the same
derived morphism with the same degree `-2` component differ by homotopy components
`h^{-1} : M^{-1} ⟶ K^{-2}` and `h^0 : M^0 ⟶ K^{-1}` satisfying the usual degree `-1` and degree
`0` homotopy formulas. -/
theorem representative_difference_controlled_by_two_step_homotopy
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    {aMap aMap' : M ⟶ K}
    (hQ : Q.map aMap = Q.map aMap')
    (hnegTwo : aMap.f (-2) = aMap'.f (-2)) :
    ∃ h : Homotopy aMap' aMap,
      M.d (-2) (-1) ≫ h.hom (-1) (-2) = 0 ∧
        aMap'.f (-1) =
          aMap.f (-1) + h.hom (-1) (-2) ≫ K.d (-2) (-1) + M.d (-1) 0 ≫ h.hom 0 (-1) ∧
        aMap'.f 0 = aMap.f 0 + h.hom 0 (-1) ≫ K.d (-1) 0 := by
  -- Route correction: equality in `D(R)` is not enough by itself; the missing ingredient is still
  -- the descent step that turns a derived equality with vanishing degree `-2` component into an
  -- actual homotopy on `M` by factoring the difference through a lower-tail target supported in
  -- degrees `≥ -1`.
  -- TODO: factor `aMap' - aMap` through an explicit lower-tail complex, use part `(1)` on that
  -- target to show the factor is homotopic to zero, then apply the support-collapse helper.
  sorry

end

end CategoryTheory
