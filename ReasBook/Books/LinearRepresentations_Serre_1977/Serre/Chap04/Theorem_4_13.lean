import Mathlib.RepresentationTheory.Semisimple
import LinearRepresentations_Serre_1977.Serre.Chap01.Remark_1_1_3_2
import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_9
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.SubrepresentationInvariant

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

-- Semantic recall: the source-facing input is an invariant submodule, while a stable
-- complementary summand is recorded canonically as a `Subrepresentation ρ`.

universe u v

namespace Representation

section AveragedHermitian

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]

/-- Helper for Theorem 4-13: the standard coordinate Hermitian form attached to a finite basis. -/
def coordinateHermitian {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ V) (x y : V) : ℂ :=
  ∑ i, star (b.equivFun x i) * b.equivFun y i

/-- Helper for Theorem 4-13: the coordinate Hermitian integrand is continuous along each orbit. -/
lemma coordinateHermitianIntegrandContinuous {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x y : V) :
    Continuous fun g ↦ coordinateHermitian b (ρ g x) (ρ g y) := by
  -- The basis coordinates of the two orbit maps are continuous, so each finite summand is.
  have hx : Continuous fun g ↦ b.equivFun (ρ g x) := by
    simpa using (continuous_equivFun_basis b).comp (Representation.continuous_apply ρ x)
  have hy : Continuous fun g ↦ b.equivFun (ρ g y) := by
    simpa using (continuous_equivFun_basis b).comp (Representation.continuous_apply ρ y)
  refine continuous_finset_sum Finset.univ fun i _ => ?_
  have hxi : Continuous fun g ↦ b.equivFun (ρ g x) i := by
    simpa using (_root_.continuous_apply i).comp hx
  have hyi : Continuous fun g ↦ b.equivFun (ρ g y) i := by
    simpa using (_root_.continuous_apply i).comp hy
  exact (Continuous.star hxi).mul hyi

/-- Helper for Theorem 4-13: the coordinate Hermitian integrand is integrable against the
normalized Haar measure. -/
lemma coordinateHermitianIntegrandIntegrable {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x y : V) :
    Integrable (fun g ↦ coordinateHermitian b (ρ g x) (ρ g y)) normalizedHaarMeasure := by
  -- On the compact group `G`, continuity gives integrability on `univ`.
  simpa [IntegrableOn] using
    (coordinateHermitianIntegrandContinuous b ρ x y).continuousOn.integrableOn_compact'
      (μ := normalizedHaarMeasure) isCompact_univ MeasurableSet.univ

/-- Helper for Theorem 4-13: the averaged coordinate Hermitian form on `V`. -/
def averagedCoordinateHermitian {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x y : V) : ℂ :=
  ∫ g, coordinateHermitian b (ρ g x) (ρ g y) ∂normalizedHaarMeasure

/-- Helper for Theorem 4-13: the coordinate Hermitian form is Hermitian. -/
lemma coordinateHermitian_conjSymm {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (x y : V) :
    conj (coordinateHermitian b y x) = coordinateHermitian b x y := by
  -- Take conjugates termwise and commute the scalar product inside each summand.
  simp [coordinateHermitian, mul_comm]

/-- Helper for Theorem 4-13: the coordinate Hermitian form is additive in the first variable. -/
lemma coordinateHermitian_add_left {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (x y z : V) :
    coordinateHermitian b (x + y) z =
      coordinateHermitian b x z + coordinateHermitian b y z := by
  -- Basis coordinates are linear, so the finite sum splits termwise.
  simp [coordinateHermitian, add_mul, Finset.sum_add_distrib]

/-- Helper for Theorem 4-13: the coordinate Hermitian form is conjugate-linear in the first
variable. -/
lemma coordinateHermitian_smul_left {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (c : ℂ) (x y : V) :
    coordinateHermitian b (c • x) y = conj c * coordinateHermitian b x y := by
  -- Pull the scalar out of each coordinate and then factor it out of the sum.
  simp [coordinateHermitian, mul_assoc, Finset.mul_sum]

/-- Helper for Theorem 4-13: on the diagonal, the coordinate Hermitian form is the sum of the
coordinate norm-squares. -/
lemma coordinateHermitian_self {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (x : V) :
    coordinateHermitian b x x = ∑ i, (Complex.normSq (b.equivFun x i) : ℂ) := by
  -- Each diagonal summand is `conj z * z`, hence the complexified norm-square.
  simp [coordinateHermitian, Complex.normSq_eq_conj_mul_self]

/-- Helper for Theorem 4-13: the averaged coordinate Hermitian form is Hermitian. -/
lemma averagedCoordinateHermitian_conjSymm {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x y : V) :
    conj (averagedCoordinateHermitian b ρ y x) = averagedCoordinateHermitian b ρ x y := by
  -- Conjugation commutes with the integral, and the pointwise coordinate form is Hermitian.
  calc
    conj (averagedCoordinateHermitian b ρ y x)
      = ∫ g, conj (coordinateHermitian b (ρ g y) (ρ g x)) ∂normalizedHaarMeasure := by
          simpa [averagedCoordinateHermitian] using
            (integral_conj (f := fun g ↦ coordinateHermitian b (ρ g y) (ρ g x))).symm
    _ = ∫ g, coordinateHermitian b (ρ g x) (ρ g y) ∂normalizedHaarMeasure := by
          congr with g
          exact coordinateHermitian_conjSymm b (ρ g x) (ρ g y)
    _ = averagedCoordinateHermitian b ρ x y := by
          rfl

/-- Helper for Theorem 4-13: the averaged coordinate Hermitian form is additive in the first
variable. -/
lemma averagedCoordinateHermitian_add_left {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x y z : V) :
    averagedCoordinateHermitian b ρ (x + y) z =
      averagedCoordinateHermitian b ρ x z + averagedCoordinateHermitian b ρ y z := by
  -- The integral respects addition once the pointwise coordinate form is expanded.
  calc
    averagedCoordinateHermitian b ρ (x + y) z
      = ∫ g, coordinateHermitian b (ρ g (x + y)) (ρ g z) ∂normalizedHaarMeasure := by
          rfl
    _ = ∫ g,
          (coordinateHermitian b (ρ g x) (ρ g z) +
            coordinateHermitian b (ρ g y) (ρ g z)) ∂normalizedHaarMeasure := by
          congr with g
          simpa using coordinateHermitian_add_left b (ρ g x) (ρ g y) (ρ g z)
    _ =
        ∫ g, coordinateHermitian b (ρ g x) (ρ g z) ∂normalizedHaarMeasure +
          ∫ g, coordinateHermitian b (ρ g y) (ρ g z) ∂normalizedHaarMeasure := by
            simpa using integral_add
              (coordinateHermitianIntegrandIntegrable b ρ x z)
              (coordinateHermitianIntegrandIntegrable b ρ y z)
    _ = averagedCoordinateHermitian b ρ x z + averagedCoordinateHermitian b ρ y z := by
          rfl

/-- Helper for Theorem 4-13: the averaged coordinate Hermitian form is conjugate-linear in the
first variable. -/
lemma averagedCoordinateHermitian_smul_left {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (c : ℂ) (x y : V) :
    averagedCoordinateHermitian b ρ (c • x) y =
      conj c * averagedCoordinateHermitian b ρ x y := by
  -- Pull the scalar through the coordinate form and then through the integral.
  calc
    averagedCoordinateHermitian b ρ (c • x) y
      = ∫ g, coordinateHermitian b (ρ g (c • x)) (ρ g y) ∂normalizedHaarMeasure := by
          rfl
    _ = ∫ g, conj c * coordinateHermitian b (ρ g x) (ρ g y) ∂normalizedHaarMeasure := by
          congr with g
          simpa using coordinateHermitian_smul_left b c (ρ g x) (ρ g y)
    _ = conj c * ∫ g, coordinateHermitian b (ρ g x) (ρ g y) ∂normalizedHaarMeasure := by
          simpa [smul_eq_mul] using
            (integral_smul (c := conj c)
              (f := fun g ↦ coordinateHermitian b (ρ g x) (ρ g y)))
    _ = conj c * averagedCoordinateHermitian b ρ x y := by
          rfl

/-- Helper for Theorem 4-13: averaging makes the coordinate Hermitian form `G`-invariant. -/
lemma averagedCoordinateHermitian_invariant {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ]
    (s : G) (x y : V) :
    averagedCoordinateHermitian b ρ (ρ s x) (ρ s y) = averagedCoordinateHermitian b ρ x y := by
  -- Rewrite the integrand by right-translation and invoke Haar invariance.
  rw [averagedCoordinateHermitian]
  calc
    ∫ t, coordinateHermitian b (ρ t (ρ s x)) (ρ t (ρ s y)) ∂normalizedHaarMeasure
      = ∫ t, coordinateHermitian b (ρ (t * s) x) (ρ (t * s) y) ∂normalizedHaarMeasure := by
          congr with t
          simp [mul_assoc]
    _ = ∫ t, coordinateHermitian b (ρ t x) (ρ t y) ∂normalizedHaarMeasure := by
          simpa using
            (integral_normalizedHaarMeasure_mul_right_eq
              (f := fun t ↦ coordinateHermitian b (ρ t x) (ρ t y)) s).symm
    _ = averagedCoordinateHermitian b ρ x y := by
          rfl

/-- Helper for Theorem 4-13: the real diagonal integrand of the averaged coordinate Hermitian
form. -/
def coordinateNormSqIntegrand {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) (x : V) (g : G) : ℝ :=
  ∑ i, Complex.normSq (b.equivFun (ρ g x) i)

/-- Helper for Theorem 4-13: the real diagonal integrand is continuous. -/
lemma coordinateNormSqIntegrandContinuous {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x : V) :
    Continuous (coordinateNormSqIntegrand b ρ x) := by
  -- Each coordinate norm-square varies continuously along the orbit map.
  have hx : Continuous fun g ↦ b.equivFun (ρ g x) := by
    simpa using (continuous_equivFun_basis b).comp (Representation.continuous_apply ρ x)
  refine continuous_finset_sum Finset.univ fun i _ => ?_
  have hxi : Continuous fun g ↦ b.equivFun (ρ g x) i := by
    simpa using (_root_.continuous_apply i).comp hx
  exact Complex.continuous_normSq.comp hxi

/-- Helper for Theorem 4-13: the real diagonal integrand is integrable on the compact group. -/
lemma coordinateNormSqIntegrandIntegrable {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x : V) :
    Integrable (coordinateNormSqIntegrand b ρ x) normalizedHaarMeasure := by
  -- Continuity on `univ` again gives integrability.
  simpa [IntegrableOn, coordinateNormSqIntegrand] using
    (coordinateNormSqIntegrandContinuous b ρ x).continuousOn.integrableOn_compact'
      (μ := normalizedHaarMeasure) isCompact_univ MeasurableSet.univ

/-- Helper for Theorem 4-13: for a nonzero vector, every translate has strictly positive
coordinate norm-square integrand. -/
lemma coordinateNormSqIntegrand_ne_zero {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) (g : G) :
    coordinateNormSqIntegrand b ρ x g ≠ 0 := by
  -- Since `ρ g` is invertible, `ρ g x` is nonzero; some basis coordinate is then nonzero, so the
  -- sum of coordinate norm-squares cannot vanish.
  classical
  have hxg : ρ g x ≠ 0 := by
    intro hzero
    apply hx
    simpa using congrArg (ρ g⁻¹) hzero
  have hcoords : b.equivFun (ρ g x) ≠ 0 := by
    intro hzero
    apply hxg
    exact b.equivFun.injective <| by simpa using hzero
  obtain ⟨i, hi⟩ : ∃ i, b.equivFun (ρ g x) i ≠ 0 := by
    classical
    by_contra h
    apply hcoords
    ext i
    exact by_contra fun hi' => h ⟨i, hi'⟩
  have hpos : 0 < coordinateNormSqIntegrand b ρ x g := by
    refine lt_of_lt_of_le ((Complex.normSq_pos).2 hi) ?_
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  exact ne_of_gt hpos

/-- Helper for Theorem 4-13: the real part of the averaged diagonal equals the averaged sum of
coordinate norm-squares. -/
lemma re_averagedCoordinateHermitian_self {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] (x : V) :
    Complex.re (averagedCoordinateHermitian b ρ x x) =
      ∫ g, coordinateNormSqIntegrand b ρ x g ∂normalizedHaarMeasure := by
  -- Move real part through the integral and simplify the diagonal coordinate form pointwise.
  simpa [averagedCoordinateHermitian, coordinateNormSqIntegrand, coordinateHermitian_self] using
    (integral_re (coordinateHermitianIntegrandIntegrable b ρ x x)).symm

/-- Helper for Theorem 4-13: the averaged coordinate Hermitian form is positive definite on
nonzero vectors. -/
lemma averagedCoordinateHermitian_re_self_pos {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] {x : V} (hx : x ≠ 0) :
    0 < Complex.re (averagedCoordinateHermitian b ρ x x) := by
  -- The diagonal integrand is nonnegative everywhere and nonzero everywhere on a nonzero orbit.
  rw [re_averagedCoordinateHermitian_self]
  have hsupport :
      Function.support (coordinateNormSqIntegrand b ρ x) = Set.univ := by
    ext g
    simp [Function.support, coordinateNormSqIntegrand_ne_zero b ρ x hx g]
  refine (MeasureTheory.integral_pos_iff_support_of_nonneg
      (f := coordinateNormSqIntegrand b ρ x)
      (fun g ↦ Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
      (coordinateNormSqIntegrandIntegrable b ρ x)).2 ?_
  simpa [hsupport, normalizedHaarMeasure_univ]

/-- Helper for Theorem 4-13: the averaged coordinate Hermitian form yields an inner-product core
on `V`. -/
@[reducible] def innerProductCoreOfAveragedCoordinateHermitian {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ G V) [IsContinuous ρ] :
    InnerProductSpace.Core ℂ V where
  inner := averagedCoordinateHermitian b ρ
  conj_inner_symm := averagedCoordinateHermitian_conjSymm b ρ
  re_inner_nonneg x := by
    -- The averaged diagonal is the integral of a pointwise nonnegative real function.
    simpa [re_averagedCoordinateHermitian_self] using
      (integral_nonneg_of_ae <| Filter.Eventually.of_forall fun g =>
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  add_left x y z := averagedCoordinateHermitian_add_left b ρ x y z
  smul_left x y c := averagedCoordinateHermitian_smul_left b ρ c x y
  definite x hx := by
    -- A nonzero vector would have strictly positive averaged self-pairing.
    by_contra hx0
    exact (lt_irrefl 0) <| by
      simpa [hx] using averagedCoordinateHermitian_re_self_pos b ρ hx0

/-- Helper for Theorem 4-13: after averaging, the Chapter 1 orthogonal-complement theorem
produces an invariant complementary submodule. -/
theorem exists_isCompl_invtSubmodule_of_compact
    (ρ : Representation ℂ G V) [IsContinuous ρ] (W : Submodule ℂ V)
    (hW : W ∈ ρ.invtSubmodule) :
    ∃ W₀ : ρ.invtSubmodule, IsCompl W (W₀ : Submodule ℂ V) := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ V) ℂ V :=
    Module.Basis.ofVectorSpace ℂ V
  letI : Fintype (Module.Basis.ofVectorSpaceIndex ℂ V) :=
    Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex ℂ V)
  let core : InnerProductSpace.Core ℂ V := innerProductCoreOfAveragedCoordinateHermitian b ρ
  letI : InnerProductSpace.Core ℂ V := core
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedSpace ℂ V := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V :=
    { toNormedSpace := inferInstance
      toInner := ⟨averagedCoordinateHermitian b ρ⟩
      norm_sq_eq_re_inner := by
        intro x
        simpa [pow_two] using
          (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℂ) (F := V) x).symm
      conj_inner_symm := averagedCoordinateHermitian_conjSymm b ρ
      add_left := averagedCoordinateHermitian_add_left b ρ
      smul_left := fun x y r ↦ averagedCoordinateHermitian_smul_left b ρ r x y }
  have hρ : ∀ s : G, ∀ x y : V, ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ := by
    -- The local inner product is exactly the averaged coordinate Hermitian form.
    intro s x y
    exact averagedCoordinateHermitian_invariant b ρ s x y
  -- With an invariant inner product in hand, the orthogonal complement is the desired complement.
  exact exists_isCompl_of_mem_invtSubmodule_of_inner_invariant ρ W hρ hW

end AveragedHermitian

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]

/-- Theorem 4-13: if `ρ : Representation ℂ G V` is a finite-dimensional continuous representation
of the compact group `G` and `W` is a `G`-stable subspace of `V`, then `W` admits a `G`-stable
complementary subspace. Lean keeps the source-facing input as a submodule together with its
invariance proof, and returns the complementary summand canonically as a `Subrepresentation ρ`. -/
theorem exists_isCompl_of_mem_invtSubmodule_of_compact
    (ρ : Representation ℂ G V) [IsContinuous ρ] (W : Submodule ℂ V)
    (hW : W ∈ ρ.invtSubmodule) :
    ∃ W₀ : Subrepresentation ρ, IsCompl W W₀.toSubmodule := by
  classical
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  -- Use the averaged invariant Hermitian form to obtain an invariant orthogonal complement.
  obtain ⟨W₀, hcompl⟩ := exists_isCompl_invtSubmodule_of_compact (ρ := ρ) W hW
  refine ⟨Subrepresentation.ofInvtSubmodule W₀, ?_⟩
  -- Repackage the invariant complementary submodule as a bundled subrepresentation.
  simpa using hcompl

/-- Theorem 4-13, bundled form: every subrepresentation of a finite-dimensional continuous
complex representation of a compact group admits a complementary subrepresentation. -/
theorem exists_isCompl_subrepresentation_of_compact
    (ρ : Representation ℂ G V) [IsContinuous ρ] (W : Subrepresentation ρ) :
    ∃ W₀ : Subrepresentation ρ, IsCompl W W₀ := by
  simpa using
    exists_isCompl_of_mem_invtSubmodule_of_compact ρ W.toSubmodule W.toSubmodule_mem_invtSubmodule

/-- Continuous finite-dimensional complex representations of compact groups are semisimple. This
is the canonical owner-level form of Theorem 4-13 for downstream typeclass reuse. -/
instance instIsSemisimpleRepresentationOfCompact
    (ρ : Representation ℂ G V) [IsContinuous ρ] : IsSemisimpleRepresentation ρ where
  exists_isCompl W := exists_isCompl_subrepresentation_of_compact ρ W

end

end Representation
