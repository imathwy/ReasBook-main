import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Integral
import LinearRepresentations_Serre_1977.Chap04.Definition_4_23
import LinearRepresentations_Serre_1977.Chap04.Definition_4_28
import LinearRepresentations_Serre_1977.Chap04.Lemma_4_22
import LinearRepresentations_Serre_1977.Chap04.Lemma_4_48
import LinearRepresentations_Serre_1977.Chap04.Lemma_4_50
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_11
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_14
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_15

open MeasureTheory
open scoped ComplexConjugate ENNReal Representation

noncomputable section

-- Semantic recall: this item keeps the source-facing Peter–Weyl owner as the set of `L²(G)`
-- matrix coefficients and states the theorem as density of its `ℂ`-linear span.

universe u v w

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

local notation "L²G" => (G →₂[(μG : Measure G)] ℂ)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {ι : Type w} [Fintype ι]

/-- Helper for Theorem 4-51: every coefficient `x ↦ ⟪u, π x v⟫` of a finite-dimensional
continuous complex representation is a continuous function on `G`. -/
theorem vectorCoefficient_continuous_of_isContinuous
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous) (u v : H) :
    Continuous fun x ↦ inner ℂ u (π x v) := by
  -- Continuity comes from composing the orbit map with the fixed first-slot inner product.
  simpa [Function.comp] using
    (innerSL ℂ u).continuous.comp (Representation.continuous_apply π v)

/-- Helper for Theorem 4-51: every matrix coefficient of a finite-dimensional continuous complex
representation of a compact group is a continuous function on `G`. -/
theorem matrixCoefficient_continuous_of_isContinuous
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (b : OrthonormalBasis ι ℂ H) (i j : ι) :
    Continuous (mc[π, b, i, j]) := by
  -- Rewrite the matrix coefficient to the general coefficient form with basis vectors.
  have hmc : mc[π, b, i, j] = fun x ↦ inner ℂ (b i) (π x (b j)) := by
    funext x
    rw [matrixCoefficient_eq_inner]
  rw [hmc]
  -- The general coefficient continuity lemma now applies directly.
  exact vectorCoefficient_continuous_of_isContinuous π hπ_cont (b i) (b j)

/-- The `L²(G)` class of the matrix coefficient `mc[π, b, i, j]`, with continuity supplied as an
ordinary argument. -/
def matrixCoefficientL2OfContinuous
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (b : OrthonormalBasis ι ℂ H) (i j : ι) : L²G :=
  ContinuousMap.toLp (2 : ENNReal) μG ℂ
    ⟨mc[π, b, i, j], matrixCoefficient_continuous_of_isContinuous π hπ_cont b i j⟩

/-- The subset of `L²(G)` consisting of the matrix coefficients of finite-dimensional irreducible
unitary continuous representations of `G`. -/
def peterWeylMatrixCoefficientSet : Set L²G :=
  {f : L²G | ∃ (K : Type*) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
    (_ : FiniteDimensional ℂ K) (κ : Type*) (_ : Fintype κ)
    (π : Representation ℂ G K) (hπ_cont : π.IsContinuous),
      π.IsIrreducible ∧ π.IsUnitary ∧
        ∃ (b : OrthonormalBasis κ ℂ K) (i j : κ),
          f = matrixCoefficientL2OfContinuous π hπ_cont b i j}

/-- Membership in `peterWeylMatrixCoefficientSet` is exactly the existence of a realizing
finite-dimensional irreducible unitary continuous matrix coefficient. -/
@[simp] theorem mem_peterWeylMatrixCoefficientSet_iff (f : L²G) :
    f ∈ peterWeylMatrixCoefficientSet.{u, v, w} ↔
      ∃ (K : Type*) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
        (_ : FiniteDimensional ℂ K) (κ : Type*) (_ : Fintype κ)
        (π : Representation ℂ G K) (hπ_cont : π.IsContinuous),
          π.IsIrreducible ∧ π.IsUnitary ∧
            ∃ (b : OrthonormalBasis κ ℂ K) (i j : κ),
              f = matrixCoefficientL2OfContinuous π hπ_cont b i j := by
  -- This is exactly the defining predicate of `peterWeylMatrixCoefficientSet`.
  rfl

/-- Helper for Theorem 4-51: a concrete continuous irreducible unitary matrix coefficient defines
an element of `peterWeylMatrixCoefficientSet`. -/
theorem matrixCoefficientL2OfContinuous_mem_peterWeylMatrixCoefficientSet
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (hπ_irred : π.IsIrreducible) (hπ_unitary : π.IsUnitary)
    (b : OrthonormalBasis ι ℂ H) (i j : ι) :
    matrixCoefficientL2OfContinuous π hπ_cont b i j ∈ peterWeylMatrixCoefficientSet.{u, v, w} := by
  -- Register the explicit coefficient by its witnessing representation and basis data.
  refine (mem_peterWeylMatrixCoefficientSet_iff _).2 ?_
  exact ⟨H, inferInstance, inferInstance, inferInstance, ι, inferInstance, π, hπ_cont,
    hπ_irred, hπ_unitary, b, i, j, rfl⟩

/-- Helper for Theorem 4-51: passing a left-translated continuous function to `L²(G)` agrees
with the regular representation on its `L²` class. -/
theorem regularRepresentation_toLp_mulLeft
    (g : G) (F : C(G, ℂ)) :
    regularRepresentation μG g (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) =
      ContinuousMap.toLp (2 : ENNReal) μG ℂ (F.comp (ContinuousMap.mulLeft g⁻¹)) := by
  -- Compare the two `L²(G)` classes through the common pointwise formula `x ↦ F (g⁻¹ * x)`.
  apply Lp.ext
  have hregular :
      regularRepresentation μG g (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) =ᵐ[μG]
        fun x : G ↦ (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) (g⁻¹ * x) := by
    simpa using
      (regularRepresentation_apply_ae_eq (μ := (μG : Measure G)) g
        (ContinuousMap.toLp (2 : ENNReal) μG ℂ F))
  have htranslate :
      (fun x : G ↦ (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) (g⁻¹ * x)) =ᵐ[μG]
        fun x : G ↦ F (g⁻¹ * x) := by
    exact (measurePreserving_mul_left (μG : Measure G) g⁻¹).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ) F)
  have hrhs :
      ContinuousMap.toLp (2 : ENNReal) μG ℂ (F.comp (ContinuousMap.mulLeft g⁻¹)) =ᵐ[μG]
        fun x : G ↦ F (g⁻¹ * x) := by
    simpa [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft] using
      (ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
        (F.comp (ContinuousMap.mulLeft g⁻¹)))
  exact hregular.trans (htranslate.trans hrhs.symm)

/-- Helper for Theorem 4-51: once an irreducible unitary representation is fixed, the Peter–Weyl
span already contains the `L²(G)` class of every coefficient `x ↦ ⟪u, π x v⟫`, not just the basis
coefficients used to define the generator set. -/
theorem matrixCoefficientL2OfContinuous_mem_peterWeylSpan_of_vectors
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (hπ_irred : π.IsIrreducible) (hπ_unitary : π.IsUnitary)
    (b : OrthonormalBasis ι ℂ H) (uVec vVec : H) :
    ContinuousMap.toLp (2 : ENNReal) μG ℂ
      ⟨fun x ↦ inner ℂ uVec (π x vVec),
        vectorCoefficient_continuous_of_isContinuous π hπ_cont uVec vVec⟩ ∈
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w} : Submodule ℂ L²G) := by
  let Fuv : C(G, ℂ) :=
    ⟨fun x ↦ inner ℂ uVec (π x vVec),
      vectorCoefficient_continuous_of_isContinuous π hπ_cont uVec vVec⟩
  let Fij : ι → ι → C(G, ℂ) := fun i j ↦
    ⟨mc[π, b, i, j], matrixCoefficient_continuous_of_isContinuous π hπ_cont b i j⟩
  -- Expand both vectors in the orthonormal basis so the coefficient becomes a finite linear
  -- combination of the basis matrix coefficients already used as Peter–Weyl generators.
  have hFuv :
      Fuv =
        ∑ i, ∑ j, (inner ℂ uVec (b i) * inner ℂ (b j) vVec) • Fij i j := by
    ext x
    calc
      inner ℂ uVec (π x vVec)
          = ∑ i, inner ℂ uVec (b i) * inner ℂ (b i) (π x vVec) := by
            symm
            exact b.sum_inner_mul_inner uVec (π x vVec)
      _ = ∑ i, inner ℂ uVec (b i) * inner ℂ (b i) (π x (∑ j, inner ℂ (b j) vVec • b j)) := by
            rw [b.sum_repr' vVec]
      _ = ∑ i, inner ℂ uVec (b i) * inner ℂ (b i) (∑ j, inner ℂ (b j) vVec • π x (b j)) := by
            simp [map_sum]
      _ = ∑ i, inner ℂ uVec (b i) *
            (∑ j, inner ℂ (b j) vVec * inner ℂ (b i) (π x (b j))) := by
            simp
      _ = ∑ i, ∑ j, (inner ℂ uVec (b i) * inner ℂ (b j) vVec) *
            inner ℂ (b i) (π x (b j)) := by
            simp_rw [Finset.mul_sum, mul_assoc]
      _ = ∑ i, ∑ j, (inner ℂ uVec (b i) * inner ℂ (b j) vVec) * mc[π, b, i, j] x := by
            simp_rw [matrixCoefficient_eq_inner]
      _ = ∑ i, ∑ j, (inner ℂ uVec (b i) * inner ℂ (b j) vVec) * Fij i j x := by
            rfl
      _ = (∑ i, ∑ j, (inner ℂ uVec (b i) * inner ℂ (b j) vVec) • Fij i j) x := by
            simp [Fij]
  -- Map the finite linear combination through `ContinuousMap.toLp` and then close by span.
  have htoLp :
      ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv =
        ∑ i, ∑ j, (inner ℂ uVec (b i) * inner ℂ (b j) vVec) •
          matrixCoefficientL2OfContinuous π hπ_cont b i j := by
    rw [hFuv]
    simp [Fij, matrixCoefficientL2OfContinuous]
  rw [htoLp]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  refine (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w}).smul_mem _ ?_
  exact Submodule.subset_span <|
    matrixCoefficientL2OfContinuous_mem_peterWeylMatrixCoefficientSet
      π hπ_cont hπ_irred hπ_unitary b i j

/-- Helper for Theorem 4-51: left translation of a Peter–Weyl generator is the `L²(G)` class of
the corresponding coefficient with the first vector moved by `π g`. -/
theorem regularRepresentation_matrixCoefficientL2_eq_vectorCoefficient
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (hπ_unitary : π.IsUnitary) (b : OrthonormalBasis ι ℂ H) (i j : ι) (g : G) :
    regularRepresentation μG g (matrixCoefficientL2OfContinuous π hπ_cont b i j) =
      ContinuousMap.toLp (2 : ENNReal) μG ℂ
        ⟨fun x ↦ inner ℂ (π g (b i)) (π x (b j)),
          vectorCoefficient_continuous_of_isContinuous π hπ_cont (π g (b i)) (b j)⟩ := by
  letI : π.IsUnitary := hπ_unitary
  let Fij : C(G, ℂ) :=
    ⟨mc[π, b, i, j], matrixCoefficient_continuous_of_isContinuous π hπ_cont b i j⟩
  let Fgij : C(G, ℂ) :=
    ⟨fun x ↦ inner ℂ (π g (b i)) (π x (b j)),
      vectorCoefficient_continuous_of_isContinuous π hπ_cont (π g (b i)) (b j)⟩
  -- Normalize the regular representation to a translated continuous function.
  rw [matrixCoefficientL2OfContinuous, regularRepresentation_toLp_mulLeft]
  -- The translated basis coefficient equals the arbitrary coefficient with first vector `π g (b i)`.
  suffices hcomp : Fij.comp (ContinuousMap.mulLeft g⁻¹) = Fgij by
    have htoLp := congrArg (ContinuousMap.toLp (2 : ENNReal) μG ℂ) hcomp
    simpa [Fij, Fgij] using htoLp
  ext x
  have hmul :
      π (g⁻¹ * x) (b j) = π g⁻¹ (π x (b j)) := by
    simpa [map_mul] using
      congrArg (fun T : H →L[ℂ] H => T (b j)) (π.map_mul g⁻¹ x)
  let eg : H →ₗᵢ[ℂ] H := (π g).toLinearIsometry (Representation.isometry π g)
  have hundo : π g (π g⁻¹ (π x (b j))) = π x (b j) := by
    simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
      (π.toContinuousLinearEquivHom g).apply_symm_apply (π x (b j))
  calc
    (Fij.comp (ContinuousMap.mulLeft g⁻¹)) x = inner ℂ (b i) (π g⁻¹ (π x (b j))) := by
      change mc[π, b, i, j] (g⁻¹ * x) = inner ℂ (b i) (π g⁻¹ (π x (b j)))
      rw [matrixCoefficient_eq_inner, hmul]
    _ = inner ℂ (π g (b i)) (π x (b j)) := by
      calc
        inner ℂ (b i) (π g⁻¹ (π x (b j)))
            = inner ℂ (π g (b i)) (π g (π g⁻¹ (π x (b j)))) := by
                symm
                exact LinearIsometry.inner_map_map eg (b i) (π g⁻¹ (π x (b j)))
        _ = inner ℂ (π g (b i)) (π x (b j)) := by rw [hundo]
    _ = Fgij x := by simp [Fgij]

/-- Helper for Theorem 4-51: the Peter–Weyl span is stable under the left regular representation. -/
theorem peterWeylSpan_leftInvariant (g : G)
    {f : L²G}
    (hf : f ∈
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w} : Submodule ℂ L²G)) :
    regularRepresentation μG g f ∈
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w} : Submodule ℂ L²G) := by
  -- It suffices to check left-translation stability on the Peter–Weyl generator set.
  refine Submodule.span_induction (s := peterWeylMatrixCoefficientSet.{u, v, w}) ?_ ?_ ?_ ?_ hf
  · intro f hfmem
    rcases (mem_peterWeylMatrixCoefficientSet_iff f).1 hfmem with
      ⟨K, _, _, _, κ, _, π, hπ_cont, hπ_irred, hπ_unitary, b, i, j, rfl⟩
    -- Rewrite the translate of a basis generator as an arbitrary coefficient and use the vector
    -- coefficient span lemma proved above.
    rw [regularRepresentation_matrixCoefficientL2_eq_vectorCoefficient
      (π := π) (hπ_cont := hπ_cont) (hπ_unitary := hπ_unitary) (b := b) (i := i) (j := j)
      (g := g)]
    exact matrixCoefficientL2OfContinuous_mem_peterWeylSpan_of_vectors
      π hπ_cont hπ_irred hπ_unitary b (π g (b i)) (b j)
  · simp
  · intro x y hx hy hxmem hymem
    simpa [map_add] using
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w}).add_mem hxmem hymem
  · intro c x hx hxmem
    simpa [map_smul] using
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w}).smul_mem c hxmem

/-- Helper for Theorem 4-51: left translation on `L²(G)` agrees with pullback along
`t ↦ g⁻¹ * t`, viewed as the canonical `Lp` linear isometry. -/
theorem regularRepresentation_eq_compMeasurePreserving (g : G) :
    regularRepresentation μG g =
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
        (fun t : G ↦ g⁻¹ * t) (measurePreserving_mul_left (μG : Measure G) g⁻¹)).toLinearMap := by
  ext f
  have hregular :
      regularRepresentation μG g f =ᵐ[μG] fun t : G ↦ f (g⁻¹ * t) := by
    simpa using
      (regularRepresentation_apply_ae_eq (μ := (μG : Measure G)) g f)
  have hcomp :
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
        (fun t : G ↦ g⁻¹ * t) (measurePreserving_mul_left (μG : Measure G) g⁻¹) f) =ᵐ[μG]
        fun t : G ↦ f (g⁻¹ * t) := by
    simpa using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (f := fun t : G ↦ g⁻¹ * t) (μ := (μG : Measure G)) (μb := (μG : Measure G))
        (g := f) (hf := measurePreserving_mul_left (μG : Measure G) g⁻¹))
  exact hregular.trans hcomp.symm

/-- Helper for Theorem 4-51: every left translate acts isometrically on `L²(G)`. -/
theorem regularRepresentation_norm_eq (g : G) (f : L²G) :
    ‖regularRepresentation μG g f‖ = ‖f‖ := by
  -- Rewrite to the canonical pullback isometry coming from normalized Haar left-invariance.
  rw [regularRepresentation_eq_compMeasurePreserving (G := G) (g := g)]
  exact
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
      (fun t : G ↦ g⁻¹ * t) (measurePreserving_mul_left (μG : Measure G) g⁻¹)).norm_map f

/-- Helper for Theorem 4-51: the normalized Haar measure on a compact group is invariant under
inversion. -/
theorem haarMeasure_inv_eq_self_of_compactGroup :
    ((μG : Measure G)).inv = (μG : Measure G) := by
  letI : IsProbabilityMeasure (((μG : Measure G)).inv) := by
    refine ⟨?_⟩
    rw [Measure.inv_apply]
    simp
  letI : (((μG : Measure G)).inv).IsMulRightInvariant := by
    infer_instance
  simpa [μG, normalizedHaarMeasure] using
    (eq_normalizedHaarMeasure_of_isProbabilityMeasure_of_isMulRightInvariant
      (G := G) (((μG : Measure G)).inv))

/-- Helper for Theorem 4-51: register inversion invariance of the normalized Haar measure for the
local `L²(G)` API. -/
local instance compactHaarIsInvInvariant :
    MeasureTheory.Measure.IsInvInvariant (μG : Measure G) where
  inv_eq_self := haarMeasure_inv_eq_self_of_compactGroup (G := G)

/-- Helper for Theorem 4-51: `invConjLp` is the normalized-Haar `L²(G)` involution represented by
`x ↦ conj (f (x⁻¹))`. -/
def invConjLp (f : L²G) : L²G :=
  star <|
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
      Inv.inv (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))) f

/-- Helper for Theorem 4-51: `invConjLp f` is almost everywhere the function
`x ↦ conj (f (x⁻¹))`. -/
theorem invConjLp_ae_eq (f : L²G) :
    invConjLp (G := G) f =ᵐ[μG] fun x ↦ conj (f x⁻¹) := by
  let Finv : L²G :=
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
      Inv.inv (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))) f
  have hcomp : Finv =ᵐ[μG] fun x : G ↦ f x⁻¹ := by
    -- Pulling back the `L²(G)` class along inversion gives the `x ↦ f (x⁻¹)` representative.
    simpa [Finv, Function.comp] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (f := Inv.inv) (μ := (μG : Measure G)) (μb := (μG : Measure G))
        (g := f) (hf := MeasureTheory.Measure.measurePreserving_inv (μG : Measure G)))
  have hstar : invConjLp (G := G) f =ᵐ[μG] fun x : G ↦ conj (Finv x) := by
    -- Complex conjugation on `L²(G)` is pointwise conjugation on representatives.
    simpa [invConjLp, Finv] using (MeasureTheory.Lp.coeFn_star Finv)
  filter_upwards [hstar, hcomp] with x hxstar hxcomp
  rw [hxstar, hxcomp]

/-- Helper for Theorem 4-51: passing a continuous function to `L²(G)` and then applying
`invConjLp` agrees with first applying inversion and complex conjugation on `C(G, ℂ)`. -/
theorem invConjLp_toLp
    (F : C(G, ℂ)) :
    invConjLp (G := G) (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) =
      ContinuousMap.toLp (2 : ENNReal) μG ℂ
        ⟨fun x ↦ conj (F x⁻¹), (Complex.continuous_conj.comp (F.continuous.comp continuous_inv))⟩ := by
  apply Lp.ext
  have hleft :
      invConjLp (G := G) (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) =ᵐ[μG]
        fun x ↦ conj ((ContinuousMap.toLp (2 : ENNReal) μG ℂ F) x⁻¹) :=
    invConjLp_ae_eq (G := G) (ContinuousMap.toLp (2 : ENNReal) μG ℂ F)
  have hmid :
      (fun x : G ↦ (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) x⁻¹) =ᵐ[μG]
        fun x ↦ F x⁻¹ := by
    -- Precompose the canonical `toLp` representative equality with inversion.
    simpa [Function.comp] using
      (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G)).quasiMeasurePreserving.ae_eq_comp
        (ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
          (f := F))
  have hright :
      ContinuousMap.toLp (2 : ENNReal) μG ℂ
          ⟨fun x ↦ conj (F x⁻¹),
            (Complex.continuous_conj.comp (F.continuous.comp continuous_inv))⟩ =ᵐ[μG]
        fun x ↦ conj (F x⁻¹) := by
    -- The target `toLp` class is represented by the same inverted-conjugated continuous function.
    simpa using
      (ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
        (f := ⟨fun x ↦ conj (F x⁻¹),
          (Complex.continuous_conj.comp (F.continuous.comp continuous_inv))⟩))
  filter_upwards [hleft, hmid, hright] with x hxleft hxmid hxright
  calc
    invConjLp (G := G) (ContinuousMap.toLp (2 : ENNReal) μG ℂ F) x
        = conj ((ContinuousMap.toLp (2 : ENNReal) μG ℂ F) x⁻¹) := hxleft
    _ = conj (F x⁻¹) := by rw [hxmid]
    _ = ContinuousMap.toLp (2 : ENNReal) μG ℂ
          ⟨fun x ↦ conj (F x⁻¹),
            (Complex.continuous_conj.comp (F.continuous.comp continuous_inv))⟩ x := by
          symm
          exact hxright

/-- Helper for Theorem 4-51: applying `invConjLp` twice returns the original `L²(G)` class. -/
theorem invConjLp_involutive (f : L²G) :
    invConjLp (G := G) (invConjLp (G := G) f) = f := by
  -- Compare both sides through the common representative `x ↦ conj (conj (f x))`.
  apply Lp.ext
  have houter :
      invConjLp (G := G) (invConjLp (G := G) f) =ᵐ[μG]
        fun x : G ↦ conj (invConjLp (G := G) f x⁻¹) :=
    invConjLp_ae_eq (G := G) (invConjLp (G := G) f)
  have hinner :
      (fun x : G ↦ invConjLp (G := G) f x⁻¹) =ᵐ[μG]
        fun x : G ↦ conj (f ((x⁻¹)⁻¹)) := by
    simpa only [Function.comp] using
      (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G)).quasiMeasurePreserving.ae_eq_comp
        (invConjLp_ae_eq (G := G) f)
  filter_upwards [houter, hinner] with x hxouter hxinner
  rw [hxouter, hxinner]
  simp

/-- Helper for Theorem 4-51: the involution `invConjLp` is continuous on `L²(G)`. -/
theorem continuous_invConjLp :
    Continuous (invConjLp (G := G) : L²G → L²G) := by
  let conjLp : L²G →L[ℝ] L²G :=
    ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap).compLpL
      (p := (2 : ENNReal)) (μ := (μG : Measure G))
  have hconj : Continuous conjLp := conjLp.continuous
  have hcomp :
      Continuous fun f : L²G ↦
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
          Inv.inv (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))) f := by
    exact (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
      Inv.inv (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))).continuous
  have hEq :
      invConjLp (G := G) = fun f : L²G ↦
        conjLp
          ((MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
            Inv.inv (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))) f) := by
    funext f
    -- The pointwise conjugation owner `conjLp` packages the `star` front end as a continuous map.
    apply Lp.ext
    filter_upwards
        [MeasureTheory.Lp.coeFn_star
          ((MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal)) Inv.inv
            (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))) f),
         ContinuousLinearMap.coeFn_compLpL (μ := (μG : Measure G)) (p := (2 : ENNReal))
          (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap))
          ((MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal)) Inv.inv
            (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))) f)]
      with x hxstar hxconj
    simpa [invConjLp] using Eq.trans hxstar hxconj.symm
  rw [hEq]
  exact hconj.comp hcomp

/-- Helper for Theorem 4-51: right translation on `L²(G)` can be expressed using the already
constructed left regular representation and the involution `invConjLp`. -/
def rightRegularRepresentation (s : G) (f : L²G) : L²G :=
  invConjLp (G := G) (regularRepresentation μG s (invConjLp (G := G) f))

/-- Helper for Theorem 4-51: `rightRegularRepresentation s f` is almost everywhere the function
`u ↦ f (u * s)`. -/
theorem rightRegularRepresentation_ae_eq
    (s : G) (f : L²G) :
    rightRegularRepresentation (G := G) s f =ᵐ[μG] fun u ↦ f (u * s) := by
  have houter :
      rightRegularRepresentation (G := G) s f =ᵐ[μG]
        fun u : G ↦ conj (regularRepresentation μG s (invConjLp (G := G) f) u⁻¹) := by
    simpa [rightRegularRepresentation] using
      invConjLp_ae_eq (G := G) (regularRepresentation μG s (invConjLp (G := G) f))
  have hreg :
      regularRepresentation μG s (invConjLp (G := G) f) =ᵐ[μG]
        fun t : G ↦ invConjLp (G := G) f (s⁻¹ * t) := by
    simpa using
      (regularRepresentation_apply_ae_eq (μ := (μG : Measure G)) s
        (invConjLp (G := G) f))
  have hregComp :
      (fun u : G ↦ regularRepresentation μG s (invConjLp (G := G) f) u⁻¹) =ᵐ[μG]
        fun u : G ↦ invConjLp (G := G) f (s⁻¹ * u⁻¹) := by
    simpa only [Function.comp] using
      (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G)).quasiMeasurePreserving.ae_eq_comp
        hreg
  have hinvComp :
      (fun u : G ↦ invConjLp (G := G) f (s⁻¹ * u⁻¹)) =ᵐ[μG]
        fun u : G ↦ conj (f ((s⁻¹ * u⁻¹)⁻¹)) := by
    let hsInv : MeasurePreserving (fun u : G ↦ s⁻¹ * u⁻¹) (μG : Measure G) (μG : Measure G) :=
      (measurePreserving_mul_left (μG : Measure G) s⁻¹).comp
        (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G))
    simpa only [Function.comp] using
      hsInv.quasiMeasurePreserving.ae_eq_comp (invConjLp_ae_eq (G := G) f)
  -- The resulting pointwise formula simplifies to the expected right-translation representative.
  filter_upwards [houter, hregComp, hinvComp] with u huouter hureg huinv
  rw [huouter, hureg, huinv]
  simp

/-- Helper for Theorem 4-51: right translation by the identity element is the identity on
`L²(G)`. -/
theorem rightRegularRepresentation_one (f : L²G) :
    rightRegularRepresentation (G := G) (1 : G) f = f := by
  apply Lp.ext
  exact (rightRegularRepresentation_ae_eq (G := G) (s := (1 : G)) f).trans <|
    Filter.Eventually.of_forall fun u ↦ by simp

/-- Helper for Theorem 4-51: right translation on `L²(G)` is the canonical pullback along
`u ↦ u * g`, viewed as a linear isometry. -/
def rightRegularRepresentationLinear (g : G) : L²G →ₗᵢ[ℂ] L²G :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
    (fun t : G ↦ t * g) (measurePreserving_mul_right (μG : Measure G) g)

/-- Helper for Theorem 4-51: the previously defined right-translation operator agrees with the
canonical `Lp` pullback along `u ↦ u * g`. -/
theorem rightRegularRepresentation_eq_linear (g : G) :
    rightRegularRepresentation (G := G) g =
      (rightRegularRepresentationLinear (G := G) g).toLinearMap := by
  ext f
  have hright :
      rightRegularRepresentation (G := G) g f =ᵐ[μG]
        fun t : G ↦ f (t * g) :=
    rightRegularRepresentation_ae_eq (G := G) (s := g) f
  have hcomp :
      rightRegularRepresentationLinear (G := G) g f =ᵐ[μG]
        fun t : G ↦ f (t * g) := by
    simpa [rightRegularRepresentationLinear, Function.comp] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (f := fun t : G ↦ t * g) (μ := (μG : Measure G)) (μb := (μG : Measure G))
        (g := f) (hf := measurePreserving_mul_right (μG : Measure G) g))
  exact hright.trans hcomp.symm

/-- Helper for Theorem 4-51: every right translate acts isometrically on `L²(G)`. -/
theorem rightRegularRepresentation_norm_eq (g : G) (f : L²G) :
    ‖rightRegularRepresentation (G := G) g f‖ = ‖f‖ := by
  -- Rewrite right translation to the canonical pullback isometry coming from right invariance.
  rw [rightRegularRepresentation_eq_linear (G := G) (g := g)]
  exact (rightRegularRepresentationLinear (G := G) g).norm_map f

/-- Helper for Theorem 4-51: right translations compose according to multiplication in `G`. -/
theorem rightRegularRepresentation_mul (g h : G) (f : L²G) :
    rightRegularRepresentation (G := G) g (rightRegularRepresentation (G := G) h f) =
      rightRegularRepresentation (G := G) (g * h) f := by
  rw [rightRegularRepresentation_eq_linear (G := G) (g := g)]
  rw [rightRegularRepresentation_eq_linear (G := G) (g := h)]
  rw [rightRegularRepresentation_eq_linear (G := G) (g := g * h)]
  simpa [rightRegularRepresentationLinear, Function.comp, mul_assoc] using
    (MeasureTheory.Lp.compMeasurePreserving_comp_apply
      (g := f)
      (hf := measurePreserving_mul_right (μG : Measure G) h)
      (hf' := measurePreserving_mul_right (μG : Measure G) g)).symm

/-- The ambient right regular representation of `G` on `L²(G)`. -/
def rightRegularRepresentationRep : Representation ℂ G L²G where
  toFun g := (rightRegularRepresentationLinear (G := G) g).toLinearMap
  map_one' := by
    ext f
    rw [← rightRegularRepresentation_eq_linear (G := G) (g := (1 : G))]
    simpa using rightRegularRepresentation_one (G := G) f
  map_mul' g h := by
    ext f
    rw [← rightRegularRepresentation_eq_linear (G := G) (g := g)]
    rw [← rightRegularRepresentation_eq_linear (G := G) (g := h)]
    rw [← rightRegularRepresentation_eq_linear (G := G) (g := g * h)]
    simpa using rightRegularRepresentation_mul (G := G) g h f

/-- Helper for Theorem 4-51: the right-translation orbit of an `L²(G)` vector is continuous. -/
theorem continuous_rightRegularRepresentation_orbit (f : L²G) :
    Continuous (fun s : G ↦ rightRegularRepresentation (G := G) s f) := by
  have hleft :
      Continuous fun s : G ↦ regularRepresentation μG s (invConjLp (G := G) f) := by
    simpa [regularRepresentation] using
      (continuous_id.smul continuous_const :
        Continuous fun s : G ↦ s • invConjLp (G := G) f)
  -- Right translation is the continuous involution `invConjLp` applied to a continuous left orbit.
  exact continuous_invConjLp (G := G) |>.comp hleft

/-- Helper for Theorem 4-51: the ambient right regular representation is continuous. -/
theorem rightRegularRepresentationRep_isContinuous :
    Representation.IsContinuous (rightRegularRepresentationRep (G := G)) := by
  refine Representation.isContinuous_of_continuousAction
    (rightRegularRepresentationRep (G := G)) ?_
  -- Route correction: use the stable `invConjLp ∘ regularRepresentation ∘ invConjLp`
  -- factorization to prove continuity of the full action map, not only of fixed orbits.
  have hreg :
      Continuous fun gv : G × L²G ↦ regularRepresentation μG gv.1 gv.2 := by
    simpa [regularRepresentation] using
      (continuous_fst.smul continuous_snd : Continuous fun gv : G × L²G ↦ gv.1 • gv.2)
  have hmid :
      Continuous fun gv : G × L²G ↦
        regularRepresentation μG gv.1 (invConjLp (G := G) gv.2) := by
    exact hreg.comp <|
      continuous_fst.prodMk ((continuous_invConjLp (G := G)).comp continuous_snd)
  have hright :
      Continuous fun gv : G × L²G ↦
        invConjLp (G := G)
          (regularRepresentation μG gv.1 (invConjLp (G := G) gv.2)) := by
    exact (continuous_invConjLp (G := G)).comp hmid
  have hEq :
      (fun gv : G × L²G ↦
        (rightRegularRepresentationRep (G := G) gv.1) gv.2) =
      fun gv : G × L²G ↦
        invConjLp (G := G)
          (regularRepresentation μG gv.1 (invConjLp (G := G) gv.2)) := by
    funext gv
    simpa [rightRegularRepresentationRep, rightRegularRepresentation] using
      (congrArg (fun T : L²G → L²G => T gv.2)
        (rightRegularRepresentation_eq_linear (G := G) (g := gv.1))).symm
  rw [hEq]
  exact hright

/-- Helper for Theorem 4-51: the ambient right regular representation is unitary. -/
theorem rightRegularRepresentationRep_isUnitary :
    Representation.IsUnitary (rightRegularRepresentationRep (G := G)) := by
  refine Representation.isUnitary_of_isometry
    (rightRegularRepresentationRep (G := G)) fun g ↦ ?_
  -- Right translation is already packaged as a linear isometry.
  simpa [rightRegularRepresentationRep,
    rightRegularRepresentation_eq_linear (G := G) (g := g)] using
    (rightRegularRepresentationLinear (G := G) g).isometry

/-- Helper for Theorem 4-51: every nonzero `L²(G)` vector yields a continuous positive-definite
coefficient for the right regular representation. -/
def positiveDefiniteWitness (f : L²G) : C(G, ℂ) :=
  ⟨fun s ↦ inner ℂ f (rightRegularRepresentation (G := G) s f),
    -- The witness is the fixed-vector inner product of the continuous right orbit.
    (innerSL ℂ f).continuous.comp (continuous_rightRegularRepresentation_orbit (G := G) f)⟩

/-- Helper for Theorem 4-51: the positive-definite witness attached to `f` takes the value
`‖f‖^2` at the identity. -/
theorem positiveDefiniteWitness_one (f : L²G) :
    positiveDefiniteWitness (G := G) f 1 = ‖f‖ ^ 2 := by
  -- At the identity, the right orbit is just `f`, so the coefficient reduces to `⟪f, f⟫`.
  simpa [positiveDefiniteWitness, rightRegularRepresentation_one] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f)

/-- Helper for Theorem 4-51: a nonzero vector has a positive real witness value at the identity. -/
theorem positiveDefiniteWitness_re_one_pos_of_ne_zero
    {f : L²G} (hf : f ≠ 0) :
    0 < Complex.re (positiveDefiniteWitness (G := G) f 1) := by
  -- The value at `1` is the strictly positive real number `‖f‖²`.
  have hnorm_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hsq_pos : 0 < ‖f‖ ^ 2 := by positivity
  simpa [positiveDefiniteWitness_one] using hsq_pos

/-- Helper for Theorem 4-51: the positive-definite witness of a nonzero vector is not the zero
continuous function. -/
theorem positiveDefiniteWitness_ne_zero_of_ne_zero
    {f : L²G} (hf : f ≠ 0) :
    positiveDefiniteWitness (G := G) f ≠ 0 := by
  intro hzero
  -- Evaluating at `1` contradicts the strict positivity of the real part.
  have hpos :
      0 < Complex.re (positiveDefiniteWitness (G := G) f 1) :=
    positiveDefiniteWitness_re_one_pos_of_ne_zero (G := G) hf
  have hvanish : Complex.re (positiveDefiniteWitness (G := G) f 1) = 0 := by
    simpa using congrArg (fun F : C(G, ℂ) ↦ Complex.re (F 1)) hzero
  have : 0 < (0 : ℝ) := by simpa [hvanish] using hpos
  exact lt_irrefl 0 this

/-- Helper for Theorem 4-51: the kernel `y ↦ conj (h (y⁻¹))` attached to an `L²(G)` vector is
integrable on the compact group. -/
theorem integrable_conj_inv_of_memLp
    (h : L²G) :
    Integrable (fun y : G ↦ conj (h y⁻¹)) μG := by
  -- Compactness upgrades the `L²` vector `h` to an `L¹` function, then inversion and conjugation
  -- preserve integrability.
  have hh_int : Integrable (fun y : G ↦ h y) μG := by
    exact (Lp.memLp h).integrable (q := (2 : ℝ≥0∞)) (by norm_num)
  have hinv_int : Integrable (fun y : G ↦ h y⁻¹) μG := by
    simpa [Function.comp] using
      (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G)).integrable_comp_of_integrable
        (f := Inv.inv) (g := fun y : G ↦ h y) hh_int
  simpa [Complex.conjCLE_apply] using
    (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap).integrable_comp hinv_int)

/-- Helper for Theorem 4-51: `invConjLp` is additive on `L²(G)`. -/
theorem invConjLp_add (f g : L²G) :
    invConjLp (G := G) (f + g) = invConjLp (G := G) f + invConjLp (G := G) g := by
  apply Lp.ext
  have hsum :
      (((invConjLp (G := G) f + invConjLp (G := G) g : L²G) : L²G) : G → ℂ) =ᵐ[μG]
        fun x ↦ invConjLp (G := G) f x + invConjLp (G := G) g x :=
    Lp.coeFn_add (invConjLp (G := G) f) (invConjLp (G := G) g)
  -- Compare both sides through the common representative `x ↦ conj (f (x⁻¹)) + conj (g (x⁻¹))`.
  filter_upwards [invConjLp_ae_eq (G := G) (f + g), invConjLp_ae_eq (G := G) f,
    invConjLp_ae_eq (G := G) g, hsum] with x hfg hf hg hsumx
  rw [hfg, hsumx, hf, hg]
  simpa using map_add (starRingEnd ℂ) (f x⁻¹) (g x⁻¹)

/-- Helper for Theorem 4-51: `invConjLp` is conjugate-linear with respect to the complex scalar
action. -/
theorem invConjLp_smul (c : ℂ) (f : L²G) :
    invConjLp (G := G) (c • f) = conj c • invConjLp (G := G) f := by
  apply Lp.ext
  have hsmul :
      (((conj c • invConjLp (G := G) f : L²G) : L²G) : G → ℂ) =ᵐ[μG]
        fun x ↦ conj c * invConjLp (G := G) f x :=
    Lp.coeFn_smul (conj c) (invConjLp (G := G) f)
  -- Pull the scalar through the inverted-conjugated representative and use `conj_mul`.
  filter_upwards [invConjLp_ae_eq (G := G) (c • f), invConjLp_ae_eq (G := G) f,
    hsmul] with x hcf hf hsmulx
  rw [hcf, hsmulx, hf]
  simpa [smul_eq_mul] using map_mul (starRingEnd ℂ) c (f x⁻¹)

/-- Helper for Theorem 4-51: applying `invConjLp` to a Peter–Weyl generator swaps the coefficient
vectors, so it stays inside the same irreducible unitary representation. -/
theorem invConjLp_matrixCoefficientL2_eq_vectorCoefficient
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (hπ_unitary : π.IsUnitary) (b : OrthonormalBasis ι ℂ H) (i j : ι) :
    invConjLp (G := G) (matrixCoefficientL2OfContinuous π hπ_cont b i j) =
      ContinuousMap.toLp (2 : ENNReal) μG ℂ
        ⟨fun x ↦ inner ℂ (b j) (π x (b i)),
          vectorCoefficient_continuous_of_isContinuous π hπ_cont (b j) (b i)⟩ := by
  letI : π.IsUnitary := hπ_unitary
  let Fij : C(G, ℂ) :=
    ⟨mc[π, b, i, j], matrixCoefficient_continuous_of_isContinuous π hπ_cont b i j⟩
  have htoLp :
      invConjLp (G := G) (matrixCoefficientL2OfContinuous π hπ_cont b i j) =
        ContinuousMap.toLp (2 : ENNReal) μG ℂ
          ⟨fun x ↦ conj (Fij x⁻¹),
            (Complex.continuous_conj.comp (Fij.continuous.comp continuous_inv))⟩ := by
    -- First normalize the `L²(G)` class through the continuous representative of the generator.
    simpa [matrixCoefficientL2OfContinuous, Fij] using invConjLp_toLp (G := G) Fij
  rw [htoLp]
  -- Then rewrite the inverted-conjugated coefficient by the standard unitary matrix-coefficient
  -- identity `conj(mc(x⁻¹)) = ⟪b_j, π x b_i⟫`.
  congr 1
  ext x
  let ex : H →ₗᵢ[ℂ] H := (π x).toLinearIsometry (Representation.isometry π x)
  have hundo : π x (π x⁻¹ (b j)) = b j := by
    simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
      (π.toContinuousLinearEquivHom x).apply_symm_apply (b j)
  calc
    conj (Fij x⁻¹) = conj (inner ℂ (b i) (π x⁻¹ (b j))) := by
      rw [show Fij x⁻¹ = mc[π, b, i, j] x⁻¹ by rfl, matrixCoefficient_eq_inner]
    _ = inner ℂ (π x⁻¹ (b j)) (b i) := by simp
    _ = inner ℂ (π x (π x⁻¹ (b j))) (π x (b i)) := by
          symm
          exact LinearIsometry.inner_map_map ex (π x⁻¹ (b j)) (b i)
    _ = inner ℂ (b j) (π x (b i)) := by rw [hundo]

/-- Helper for Theorem 4-51: the Peter–Weyl span is stable under the anti-linear involution
`f(x) ↦ conj (f (x⁻¹))`. -/
theorem peterWeylSpan_invConjInvariant
    {f : L²G}
    (hf : f ∈
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w} : Submodule ℂ L²G)) :
    invConjLp (G := G) f ∈
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w} : Submodule ℂ L²G) := by
  -- Check the anti-linear symmetry on generators, then extend by span induction.
  refine Submodule.span_induction (s := peterWeylMatrixCoefficientSet.{u, v, w}) ?_ ?_ ?_ ?_ hf
  · intro f hfmem
    rcases (mem_peterWeylMatrixCoefficientSet_iff f).1 hfmem with
      ⟨K, _, _, _, κ, _, π, hπ_cont, hπ_irred, hπ_unitary, b, i, j, rfl⟩
    rw [invConjLp_matrixCoefficientL2_eq_vectorCoefficient
      (G := G) (π := π) (hπ_cont := hπ_cont) (hπ_unitary := hπ_unitary)
      (b := b) (i := i) (j := j)]
    exact matrixCoefficientL2OfContinuous_mem_peterWeylSpan_of_vectors
      π hπ_cont hπ_irred hπ_unitary b (b j) (b i)
  · simpa [invConjLp] using
      (show (0 : L²G) ∈ Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w} from
        Submodule.zero_mem (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w}))
  · intro x y hx hy hxmem hymem
    simpa [invConjLp_add (G := G) x y] using
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w}).add_mem hxmem hymem
  · intro c x hx hxmem
    simpa [invConjLp_smul (G := G) c x] using
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w}).smul_mem (conj c) hxmem

/-- Helper for Theorem 4-51: the topological closure of an `invConjLp`-stable submodule of
`L²(G)` remains `invConjLp`-stable. -/
theorem topologicalClosure_invConjInvariant_of_invConjInvariant
    (S : Submodule ℂ L²G)
    (hS_invConj : Set.MapsTo (invConjLp (G := G)) S S) :
    Set.MapsTo (invConjLp (G := G)) S.topologicalClosure S.topologicalClosure := by
  intro x hx
  have hmaps :
      Set.MapsTo (invConjLp (G := G)) (S : Set L²G) (S.topologicalClosure : Set L²G) :=
    fun y hy ↦ S.le_topologicalClosure (hS_invConj hy)
  have hclosed :=
    hmaps.closure_left (continuous_invConjLp (G := G)) (Submodule.isClosed_topologicalClosure S)
  simpa [Submodule.topologicalClosure_coe] using hclosed hx

/-- Helper for Theorem 4-51: `invConjLp` transports the `L²(G)` inner product by conjugating the
second argument after the same involution. -/
theorem inner_invConjLp_left (f g : L²G) :
    inner ℂ (invConjLp (G := G) f) g = conj (inner ℂ f (invConjLp (G := G) g)) := by
  -- Rewrite both inner products by their integral formulas and compare them after inversion.
  have hleft :
      inner ℂ (invConjLp (G := G) f) g = ∫ x : G, g x * f x⁻¹ ∂μG := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [invConjLp_ae_eq (G := G) f] with x hx
    rw [hx, RCLike.inner_apply]
    simp
  have hright :
      conj (inner ℂ f (invConjLp (G := G) g)) = ∫ x : G, g x⁻¹ * f x ∂μG := by
    rw [MeasureTheory.L2.inner_def, ← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards [invConjLp_ae_eq (G := G) g] with x hx
    rw [hx, RCLike.inner_apply]
    simp [mul_comm, mul_left_comm, mul_assoc]
  calc
    inner ℂ (invConjLp (G := G) f) g = ∫ x : G, g x * f x⁻¹ ∂μG := hleft
    _ = ∫ x : G, g x⁻¹ * f x ∂μG := by
      -- Inversion preserves normalized Haar measure, so the two integral spellings agree.
      have hinv :=
        (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G)).integral_comp'
          (f := MeasurableEquiv.inv G) (g := fun x : G ↦ g x * f x⁻¹)
      simpa [mul_assoc] using hinv.symm
    _ = conj (inner ℂ f (invConjLp (G := G) g)) := hright.symm

/-- Helper for Theorem 4-51: if a submodule is stable under `invConjLp`, then so is its
orthogonal complement. -/
theorem orthogonal_invConjInvariant_of_invConjInvariant
    (S : Submodule ℂ L²G)
    (hS_invConj : Set.MapsTo (invConjLp (G := G)) S S) :
    Set.MapsTo (invConjLp (G := G)) Sᗮ Sᗮ := by
  intro x hx
  have hx' : ∀ y ∈ S, inner ℂ x y = 0 :=
    (Submodule.mem_orthogonal' (K := S) x).1 hx
  refine (Submodule.mem_orthogonal' (K := S) (invConjLp (G := G) x)).2 ?_
  intro y hy
  -- Move orthogonality across the antiunitary involution using the inner-product bridge.
  have hxy : inner ℂ x (invConjLp (G := G) y) = 0 :=
    hx' (invConjLp (G := G) y) (hS_invConj hy)
  calc
    inner ℂ (invConjLp (G := G) x) y =
        conj (inner ℂ x (invConjLp (G := G) y)) := inner_invConjLp_left (G := G) x y
    _ = 0 := by simp [hxy]

/-- Helper for Theorem 4-51: left-translation stability together with `invConjLp`-stability
implies right-translation stability on `L²(G)`. -/
theorem rightInvariant_of_leftInvariant_invConjInvariant
    (K : Submodule ℂ L²G)
    (hK_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) K K)
    (hK_invConj : Set.MapsTo (invConjLp (G := G)) K K) :
    ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K := by
  intro g x hx
  -- Route correction: use the exact `invConjLp ∘ regularRepresentation ∘ invConjLp` owner of
  -- right translation instead of trying to normalize left coefficients directly.
  rw [rightRegularRepresentation]
  exact hK_invConj <| hK_left g <| hK_invConj hx

/-- Helper for Theorem 4-51: the topological closure of a left-invariant submodule of `L²(G)`
remains left-invariant. -/
theorem topologicalClosure_leftInvariant_of_leftInvariant
    (S : Submodule ℂ L²G)
    (hS_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) S S) :
    ∀ g : G, Set.MapsTo (regularRepresentation μG g) S.topologicalClosure S.topologicalClosure := by
  intro g x hx
  -- A continuous translate of a point in the closure stays in the closure of the translated set.
  have hcont :
      Continuous (regularRepresentation μG g : L²G → L²G) := by
    simpa [regularRepresentation_eq_compMeasurePreserving (G := G) (g := g)] using
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
        (fun t : G ↦ g⁻¹ * t) (measurePreserving_mul_left (μG : Measure G) g⁻¹)).continuous
  have hmaps :
      Set.MapsTo (regularRepresentation μG g) (S : Set L²G) (S.topologicalClosure : Set L²G) :=
    fun y hy ↦ S.le_topologicalClosure (hS_left g hy)
  have hclosed :=
    hmaps.closure_left hcont
      (Submodule.isClosed_topologicalClosure S)
  simpa [Submodule.topologicalClosure_coe] using hclosed hx

/-- Helper for Theorem 4-51: the orthogonal complement of a left-invariant submodule of `L²(G)`
is still left-invariant. -/
theorem orthogonal_leftInvariant_of_leftInvariant
    (S : Submodule ℂ L²G)
    (hS_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) S S) :
    ∀ g : G, Set.MapsTo (regularRepresentation μG g) Sᗮ Sᗮ := by
  intro g x hx
  let T : L²G →ₗᵢ[ℂ] L²G :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
      (fun t : G ↦ g⁻¹ * t) (measurePreserving_mul_left (μG : Measure G) g⁻¹)
  have hT_apply (z : L²G) : T z = regularRepresentation μG g z := by
    -- The pullback isometry is exactly the left regular translate on `L²(G)`.
    change
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
        (fun t : G ↦ g⁻¹ * t) (measurePreserving_mul_left (μG : Measure G) g⁻¹)).toLinearMap) z =
        regularRepresentation μG g z
    rw [← regularRepresentation_eq_compMeasurePreserving (G := G) (g := g)]
  have hT_surj : Function.Surjective T := by
    intro y
    refine ⟨regularRepresentation μG g⁻¹ y, ?_⟩
    -- The inverse translate `g⁻¹` provides the preimage for the pullback isometry.
    simpa [hT_apply] using
      congrArg (fun A : L²G →L[ℂ] L²G => A y) ((regularRepresentation μG).map_mul g g⁻¹)
  let e : L²G ≃ₗᵢ[ℂ] L²G := LinearIsometryEquiv.ofSurjective T hT_surj
  have he_apply (z : L²G) : e z = regularRepresentation μG g z := by
    -- This identifies the abstract isometric equivalence with left translation.
    simpa [e] using hT_apply z
  have hmap_eq : S.map (e.toLinearEquiv : L²G →ₗ[ℂ] L²G) = S := by
    apply le_antisymm
    · rintro y hy
      rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
      -- Forward invariance gives one inclusion of the transported submodule.
      simpa [he_apply] using hS_left g hz
    · intro y hy
      refine Submodule.mem_map.mpr ?_
      refine ⟨regularRepresentation μG g⁻¹ y, hS_left g⁻¹ hy, ?_⟩
      -- The inverse translate recovers every vector of `S`, hence the reverse inclusion.
      simpa [he_apply] using
        congrArg (fun A : L²G →L[ℂ] L²G => A y) ((regularRepresentation μG).map_mul g g⁻¹)
  have hxmap : e x ∈ (S.map (e.toLinearEquiv : L²G →ₗ[ℂ] L²G))ᗮ := by
    -- Orthogonality transports cleanly across the surjective linear isometry equivalence.
    rw [← Submodule.map_orthogonal_equiv (K := S) (f := e)]
    exact Submodule.mem_map_of_mem hx
  simpa [he_apply, hmap_eq] using hxmap

/-- Helper for Theorem 4-51: if a submodule of `L²(G)` is stable under the left regular
representation and contains `h`, then it contains the span of the full regular orbit of `h`. -/
theorem regularRepresentationTranslateSpanOfMemLp_le_of_leftInvariant
    (K : Submodule ℂ L²G)
    (hK_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) K K)
    {h : G → ℂ} (hh : MemLp h (2 : ENNReal) μG)
    (hhK : MemLp.toLp h hh ∈ K) :
    regularRepresentationTranslateSpanOfMemLp (G := G) h hh ≤ K := by
  -- Expand the translate span and reduce to the generating regular orbit.
  rw [regularRepresentationTranslateSpanOfMemLp, regularRepresentationTranslateSpan]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  -- Each translate stays in `K` by the assumed left-invariance.
  exact hK_left g hhK

/-- Helper for Theorem 4-51: Lemma 4-50 upgrades a vector in any closed left-invariant submodule of
`L²(G)` to a convolution-smoothed vector that still lies in that submodule. -/
theorem compactGroupConvolutionToLp_mem_of_closed_leftInvariant
    (K : Submodule ℂ L²G) (hK_closed : IsClosed (K : Set L²G))
    (hK_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) K K)
    {f h : G → ℂ} (hf : Integrable f μG) (hh : MemLp h (2 : ENNReal) μG)
    (hhK : MemLp.toLp h hh ∈ K) :
    ∃ hF : MemLp (compactGroupConvolutionFun (G := G) f h) (2 : ENNReal) μG,
      compactGroupConvolutionToLp (G := G) f h hF ∈ K := by
  rcases exists_tendsto_memLp_toLp_integral_mul_inv_mul
      (G := G) (f := f) (h := h) hf hh with
    ⟨hF, u, hu_tendsto, hu_mem⟩
  have hspan :
      regularRepresentationTranslateSpanOfMemLp (G := G) h hh ≤ K :=
    regularRepresentationTranslateSpanOfMemLp_le_of_leftInvariant
      (G := G) (K := K) hK_left hh hhK
  have hu_mem_K : ∀ n, u n ∈ K := by
    intro n
    -- The approximating sequence from Lemma 4-50 already lives in the translate span.
    exact hspan (hu_mem n)
  refine ⟨hF, ?_⟩
  -- Closedness of `K` keeps the `L²`-limit of the approximants inside `K`.
  exact hK_closed.mem_of_tendsto hu_tendsto (Filter.Eventually.of_forall hu_mem_K)

/-- Helper for Theorem 4-51: every irreducible continuous unitary character already lies in the
Peter–Weyl span because it is the finite sum of its diagonal matrix coefficients. -/
theorem characterL2_mem_peterWeylSpan
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (hπ_irred : π.IsIrreducible) (hπ_unitary : π.IsUnitary) :
    Representation.characterL2 π ∈
      (Submodule.span ℂ peterWeylMatrixCoefficientSet.{u, v, w} : Submodule ℂ L²G) := by
  letI : π.IsContinuous := hπ_cont
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  let χ : C(G, ℂ) :=
    ⟨π.character, Representation.continuous_character_of_isContinuousCompact (ρ := π)⟩
  have hχ :
      χ = ∑ i, ⟨mc[π, b, i, i], matrixCoefficient_continuous_of_isContinuous π hπ_cont b i i⟩ := by
    -- Rewrite the character as the finite sum of the diagonal matrix coefficients.
    ext x
    simpa [χ] using Representation.character_eq_sumDiagonalMatrixCoefficient π b x
  have hcharacter :
      Representation.characterL2 π =
        ∑ i, matrixCoefficientL2OfContinuous π hπ_cont b i i := by
    -- Mapping the diagonal character expansion through `ContinuousMap.toLp` gives the `L²(G)` sum.
    calc
      Representation.characterL2 π = ContinuousMap.toLp (2 : ENNReal) μG ℂ χ := by
        rfl
      _ = ContinuousMap.toLp (2 : ENNReal) μG ℂ
            (∑ i, ⟨mc[π, b, i, i],
              matrixCoefficient_continuous_of_isContinuous π hπ_cont b i i⟩) := by
            rw [hχ]
      _ = ∑ i, matrixCoefficientL2OfContinuous π hπ_cont b i i := by
            simp [matrixCoefficientL2OfContinuous]
  rw [hcharacter]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  -- Each diagonal matrix coefficient is already one of the Peter–Weyl generators.
  refine Submodule.subset_span ?_
  refine (mem_peterWeylMatrixCoefficientSet_iff _).2 ?_
  exact ⟨H, inferInstance, inferInstance, inferInstance, Fin (Module.finrank ℂ H), inferInstance,
    π, hπ_cont, hπ_irred, hπ_unitary, b, i, i, rfl⟩

/-- Helper for Theorem 4-51: a continuous representation restricts to a continuous action on every
subrepresentation. -/
theorem subrepresentationToRepresentationIsContinuous
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : Subrepresentation ρ) :
    Representation.IsContinuous σ.toRepresentation := by
  -- Restrict the ambient continuous action to the invariant subtype carrier.
  refine Representation.isContinuous_of_continuousAction σ.toRepresentation ?_
  exact
    ((Representation.continuousAction ρ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      (fun gx ↦ σ.apply_mem_toSubmodule gx.1 gx.2.2)

/-- Helper for Theorem 4-51: a unitary representation remains unitary after restricting to a
subrepresentation. -/
theorem subrepresentationToRepresentationIsUnitary
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsUnitary ρ]
    (σ : Subrepresentation ρ) :
    Representation.IsUnitary σ.toRepresentation := by
  -- The restricted action is still pointwise isometric because it uses the same ambient maps.
  exact Representation.isUnitary_of_isometry σ.toRepresentation fun g x y ↦ by
    simpa using (Representation.isometry ρ g x y)

/-- The bundled regular subrepresentation carried by a left-invariant submodule `K ≤ L²(G)`. -/
abbrev closedLeftInvariantSubrepresentation
    (K : Submodule ℂ L²G)
    (hK_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) K K) :
    Subrepresentation (regularRepresentation μG) :=
  ⟨K, fun g hx ↦ hK_left g hx⟩

/-- The restricted regular representation on a left-invariant submodule `K ≤ L²(G)`. -/
abbrev closedLeftInvariantRepresentation
    (K : Submodule ℂ L²G)
    (hK_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) K K) :
    Representation ℂ G K :=
  (closedLeftInvariantSubrepresentation (G := G) K hK_left).toRepresentation

/-- The bundled right-regular subrepresentation carried by a right-invariant submodule
`K ≤ L²(G)`. -/
abbrev closedRightInvariantSubrepresentation
    (K : Submodule ℂ L²G)
    (hK_right : ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K) :
    Subrepresentation (rightRegularRepresentationRep (G := G)) :=
  ⟨K, fun g {x} hx ↦ by
    have hx' : rightRegularRepresentation (G := G) g x ∈ K :=
      hK_right g hx
    have hEq :
        (rightRegularRepresentationRep (G := G) g) x =
          rightRegularRepresentation (G := G) g x := by
      simpa [rightRegularRepresentationRep] using
        congrArg
          (fun T : L²G →ₗ[ℂ] L²G => T x)
          (rightRegularRepresentation_eq_linear (G := G) (g := g))
    simpa [hEq] using hx'⟩

/-- The restricted right regular representation on a right-invariant submodule `K ≤ L²(G)`. -/
abbrev closedRightInvariantRepresentation
    (K : Submodule ℂ L²G)
    (hK_right : ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K) :
    Representation ℂ G K :=
  (closedRightInvariantSubrepresentation (G := G) K hK_right).toRepresentation

/-- Helper for Theorem 4-51: the restricted right regular representation on a right-invariant
submodule of `L²(G)` is unitary. -/
theorem closedRightInvariantRepresentationIsUnitary
    (K : Submodule ℂ L²G)
    (hK_right : ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K) :
    Representation.IsUnitary (closedRightInvariantRepresentation (G := G) K hK_right) := by
  letI : Representation.IsUnitary (rightRegularRepresentationRep (G := G)) :=
    rightRegularRepresentationRep_isUnitary (G := G)
  exact subrepresentationToRepresentationIsUnitary
    (ρ := rightRegularRepresentationRep (G := G))
    (σ := closedRightInvariantSubrepresentation (G := G) K hK_right)

/-- Helper for Theorem 4-51: a nonzero closed right-invariant submodule of `L²(G)` contains a
nonzero finite-dimensional subrepresentation of the restricted right regular action. -/
theorem existsNonzeroFiniteDimensionalSubrepresentationOfClosedRightInvariant
    (K : Submodule ℂ L²G) (hK_closed : IsClosed (K : Set L²G))
    (hK_right : ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K)
    (hK_ne_bot : K ≠ ⊥) :
    ∃ σ : Subrepresentation (closedRightInvariantRepresentation (G := G) K hK_right),
      σ ≠ ⊥ ∧ FiniteDimensional ℂ σ.toSubmodule := by
  letI : CompleteSpace K := hK_closed.completeSpace_coe
  letI : Representation.IsContinuous (rightRegularRepresentationRep (G := G)) :=
    rightRegularRepresentationRep_isContinuous (G := G)
  letI : Representation.IsUnitary (rightRegularRepresentationRep (G := G)) :=
    rightRegularRepresentationRep_isUnitary (G := G)
  let ρK : Representation ℂ G K := closedRightInvariantRepresentation (G := G) K hK_right
  letI : Representation.IsContinuous ρK :=
    subrepresentationToRepresentationIsContinuous
      (ρ := rightRegularRepresentationRep (G := G))
      (σ := closedRightInvariantSubrepresentation (G := G) K hK_right)
  letI : Representation.IsUnitary ρK :=
    subrepresentationToRepresentationIsUnitary
      (ρ := rightRegularRepresentationRep (G := G))
      (σ := closedRightInvariantSubrepresentation (G := G) K hK_right)
  have hρK_isometry : ∀ g : G, Isometry (ρK g) := by
    intro g x y
    simpa using (Representation.isometry ρK g x y)
  have hsurjK : ∀ g : G, Function.Surjective ((ρK g).toLinearIsometry (hρK_isometry g)) := by
    intro g y
    refine ⟨(ρK g⁻¹) y, ?_⟩
    simpa using congrArg (fun A : K →ₗ[ℂ] K => A y) (ρK.map_mul g g⁻¹)
  let eK : G → K ≃L[ℂ] K := fun g ↦
    (LinearIsometryEquiv.ofSurjective
      ((ρK g).toLinearIsometry (hρK_isometry g))
      (hsurjK g)).toContinuousLinearEquiv
  have heK_apply (g : G) (x : K) : eK g x = ρK g x := by
    simpa [eK] using
      (LinearIsometryEquiv.coe_ofSurjective
        ((ρK g).toLinearIsometry (hρK_isometry g))
        (hsurjK g) x)
  let ρKHilbert : HilbertSpaceRepresentation G K :=
    { toMonoidHom :=
        { toFun := eK
          map_one' := by
            ext x
            change ((eK (1 : G) x : K) : L²G) = x
            rw [heK_apply]
            simpa using
              congrArg (fun A : K →ₗ[ℂ] K => ((A x : K) : L²G)) (ρK.map_one)
          map_mul' := by
            intro g h
            ext x
            change ((eK (g * h) x : K) : L²G) = ((eK g * eK h) x : K)
            rw [heK_apply, heK_apply, heK_apply]
            simpa using
              congrArg (fun A : K →ₗ[ℂ] K => ((A x : K) : L²G)) (ρK.map_mul g h) }
      continuous_action := by
        simpa [heK_apply] using (Representation.continuousAction ρK) }
  obtain ⟨ι, σ, hσ_sum, hσ_fd⟩ :=
    HilbertSpaceRepresentation.exists_isHilbertSum_finiteDimensional_subrepresentations_of_compact
      ρKHilbert
  obtain ⟨x, hxK, hx_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK_ne_bot
  let xK : K := ⟨x, hxK⟩
  have hcoord_ne : ∃ i, hσ_sum.linearIsometryEquiv xK i ≠ 0 := by
    -- A nonzero vector in the Hilbert sum has at least one nonzero coordinate.
    by_contra hcoord_ne
    have hall : ∀ i, hσ_sum.linearIsometryEquiv xK i = 0 := by
      intro i
      by_contra hi
      exact hcoord_ne ⟨i, hi⟩
    have hy_zero : hσ_sum.linearIsometryEquiv xK = 0 := by
      ext i
      exact hall i
    have hxK_zero : xK = 0 := hσ_sum.linearIsometryEquiv.injective hy_zero
    have hx_zero : x = 0 := by
      simpa using congrArg Subtype.val xK_zero
    exact hx_ne_zero hx_zero
  rcases hcoord_ne with ⟨i, hi⟩
  refine ⟨σ i, ?_, hσ_fd i⟩
  intro hbot
  have hsub_bot : (σ i).toSubmodule = ⊥ := by
    simpa using congrArg Subrepresentation.toSubmodule hbot
  have hcoord_zero : hσ_sum.linearIsometryEquiv xK i = 0 := by
    apply Subtype.ext
    simpa [hsub_bot] using (hσ_sum.linearIsometryEquiv xK i).property
  exact hi hcoord_zero

/-- Helper for Theorem 4-51: a nonzero finite-dimensional continuous representation of a compact
group contains a nonzero irreducible subrepresentation. -/
theorem existsNonzeroIrreducibleSubrepresentationOfNonzeroFiniteDimensional
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsContinuous ρ] [Nontrivial V] :
    ∃ σ : Subrepresentation ρ, σ ≠ ⊥ ∧ σ.toRepresentation.IsIrreducible := by
  classical
  obtain ⟨ι, _, σ, _, hσ_top, hσ_irred⟩ :=
    Representation.exists_iSupIndep_irreducible_subrepresentations_of_compact ρ
  -- The irreducible decomposition cannot consist entirely of zero summands in a nontrivial space.
  by_contra hσ_exists
  have hσ_bot : ∀ i, σ i = ⊥ := by
    intro i
    by_contra hi
    exact hσ_exists ⟨σ i, hi, hσ_irred i⟩
  have hbot_top : (⊥ : Submodule ℂ V) = ⊤ := by
    have hbot_submodule : ((⊥ : Subrepresentation ρ).toSubmodule : Submodule ℂ V) = ⊥ := rfl
    have hσ_top' :
        (⨆ i, ((⊥ : Subrepresentation ρ).toSubmodule : Submodule ℂ V)) = ⊤ := by
      simpa [hσ_bot] using hσ_top
    simpa [hbot_submodule] using hσ_top'
  exact bot_ne_top hbot_top

/-- Helper for Theorem 4-51: the `L²(G)` norm-square of a diagonal matrix coefficient is the
inverse complex dimension given by Lemma 4-22. -/
theorem matrixCoefficientL2_inner_self_eq_invFinrank
    [DecidableEq ι]
    (π : Representation ℂ G H) (hπ_cont : π.IsContinuous)
    (hπ_irred : π.IsIrreducible) (hπ_unitary : π.IsUnitary)
    (b : OrthonormalBasis ι ℂ H) (i : ι) :
    inner ℂ (matrixCoefficientL2OfContinuous π hπ_cont b i i)
      (matrixCoefficientL2OfContinuous π hπ_cont b i i) =
      (Module.finrank ℂ H : ℂ)⁻¹ := by
  letI : π.IsContinuous := hπ_cont
  letI : π.IsIrreducible := hπ_irred
  letI : π.IsUnitary := hπ_unitary
  -- Rewrite the `L²` inner product through the canonical `toLp` representative of the
  -- diagonal coefficient and then apply Lemma 4-22 with matching indices.
  calc
    inner ℂ (matrixCoefficientL2OfContinuous π hπ_cont b i i)
        (matrixCoefficientL2OfContinuous π hπ_cont b i i)
      = ∫ t, mc[π, b, i, i] t * conj (mc[π, b, i, i] t) ∂μG := by
          unfold matrixCoefficientL2OfContinuous
          rw [MeasureTheory.L2.inner_def]
          refine integral_congr_ae ?_
          filter_upwards
              [ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
                (f := ⟨mc[π, b, i, i],
                  matrixCoefficient_continuous_of_isContinuous π hπ_cont b i i⟩),
               ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
                (f := ⟨mc[π, b, i, i],
                  matrixCoefficient_continuous_of_isContinuous π hπ_cont b i i⟩)]
            with x hx1 hx2
          calc
            inner ℂ
                ((ContinuousMap.toLp (2 : ENNReal) μG ℂ
                  ⟨mc[π, b, i, i],
                    matrixCoefficient_continuous_of_isContinuous π hπ_cont b i i⟩ : L²G) x)
                ((ContinuousMap.toLp (2 : ENNReal) μG ℂ
                  ⟨mc[π, b, i, i],
                    matrixCoefficient_continuous_of_isContinuous π hπ_cont b i i⟩ : L²G) x)
              = inner ℂ (mc[π, b, i, i] x) (mc[π, b, i, i] x) := by
                  rw [hx1, hx2]
                  simpa
            _ = mc[π, b, i, i] x * (starRingEnd ℂ) (mc[π, b, i, i] x) := by
              rw [RCLike.inner_apply]
    _ = (Module.finrank ℂ H : ℂ)⁻¹ := by
          simpa using
            Representation.matrixCoefficientIntegral_eq_inv_finrank_mul_kronecker π b i i i i

/-- Helper for Theorem 4-51: a vector lying both in a submodule and in its orthogonal complement
has zero `L²(G)` self-inner-product. -/
theorem coefficientSelfInner_eq_zero_of_memOrthogonalClosure
    (U : Submodule ℂ L²G) {f : L²G}
    (hfK : f ∈ Uᗮ) (hfU : f ∈ U) :
    inner ℂ f f = 0 := by
  -- Orthogonality against all of `U` applies in particular to `f` itself.
  rw [Submodule.mem_orthogonal'] at hfK
  exact hfK f hfU

/-- Helper for Theorem 4-51: nested right-subrepresentation vectors act by the ambient right
regular representation once all subtype coercions are forgotten. -/
theorem closedRightInvariantSubrepresentation_apply_coe
    (K : Submodule ℂ L²G)
    (hK_right : ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K)
    (τ : Subrepresentation (closedRightInvariantRepresentation (G := G) K hK_right))
    (σ : Subrepresentation τ.toRepresentation)
    (g : G) (z : σ.toSubmodule) :
    ((((σ.toRepresentation g z : σ.toSubmodule) : τ.toSubmodule) : K) : L²G) =
      rightRegularRepresentation (G := G) g ((((z : σ.toSubmodule) : τ.toSubmodule) : K) : L²G) := by
  -- This is definitional: every restricted right action is the ambient right regular action with
  -- codomain narrowed by invariant-submodule membership.
  rw [rightRegularRepresentation_eq_linear (G := G) (g := g)]
  rfl

/-- Helper for Theorem 4-51: pairing a left translate against a test vector rewrites as the
scalar integral with the test vector translated in the opposite direction. -/
theorem inner_regularRepresentation_eq_integral_mul_conj
    (g : G) (w v : L²G) :
    inner ℂ w (regularRepresentation μG g v) =
      ∫ z : G, v z * conj (w (g * z)) ∂μG := by
  -- Expand the `L²(G)` inner product and then normalize the left translate by a left-change of
  -- variables.
  rw [MeasureTheory.L2.inner_def]
  have hreg :
      regularRepresentation μG g v =ᵐ[μG] fun z : G ↦ v (g⁻¹ * z) := by
    simpa using (regularRepresentation_apply_ae_eq (μ := (μG : Measure G)) g v)
  calc
    ∫ z : G, regularRepresentation μG g v z * conj (w z) ∂μG
      = ∫ z : G, v (g⁻¹ * z) * conj (w z) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards [hreg] with z hz
          rw [hz]
    _ = ∫ z : G, v z * conj (w (g * z)) ∂μG := by
          simpa [mul_assoc] using
            (integral_mul_left_eq_self
              (μ := (μG : Measure G))
              (f := fun z : G ↦ v z * conj (w (g * z))) g⁻¹)

/-- Helper for Theorem 4-51: the natural right coefficient is the source-facing scalar convolution
formula `x ↦ ∫ y, v (y * x) * conj (u y)`. -/
theorem naturalRightOrbitCoefficient_apply_eq_integral
    (K : Submodule ℂ L²G) (u v : K) (x : G) :
    inner ℂ ((u : K) : L²G)
      (rightRegularRepresentation (G := G) x ((v : K) : L²G)) =
      ∫ y : G, (((v : K) : L²G) (y * x)) * conj ((((u : K) : L²G) y)) ∂μG := by
  -- Expand the right orbit coefficient through the pointwise formula for right translation.
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [rightRegularRepresentation_ae_eq (G := G) (s := x) (((v : K) : L²G))] with y hy
  rw [hy, RCLike.inner_apply]

/-- Helper for Theorem 4-51: the natural right coefficient also has the convolution spelling
`x ↦ ∫ y, conj (u (y⁻¹)) * v (y⁻¹ * x)`. -/
theorem naturalRightOrbitCoefficient_apply_eq_convolutionIntegral
    (K : Submodule ℂ L²G) (u v : K) (x : G) :
    inner ℂ ((u : K) : L²G)
      (rightRegularRepresentation (G := G) x ((v : K) : L²G)) =
      ∫ y : G, conj ((((u : K) : L²G) y⁻¹)) * (((v : K) : L²G) (y⁻¹ * x)) ∂μG := by
  -- Inversion preserves Haar measure, so the source-facing orbit integral can be rewritten in the
  -- convolution normal form used by Lemma 4-50.
  calc
    inner ℂ ((u : K) : L²G)
        (rightRegularRepresentation (G := G) x ((v : K) : L²G))
      = ∫ y : G, (((v : K) : L²G) (y * x)) * conj ((((u : K) : L²G) y)) ∂μG := by
          exact naturalRightOrbitCoefficient_apply_eq_integral (G := G) K u v x
    _ = ∫ y : G, (((v : K) : L²G) (y⁻¹ * x)) * conj ((((u : K) : L²G) y⁻¹)) ∂μG := by
          have hinv :=
            (MeasureTheory.Measure.measurePreserving_inv (μG : Measure G)).integral_comp'
              (f := MeasurableEquiv.inv G)
              (g := fun y : G ↦
                (((v : K) : L²G) (y⁻¹ * x)) * conj ((((u : K) : L²G) y⁻¹)))
          simpa [mul_assoc] using hinv
    _ = ∫ y : G, conj ((((u : K) : L²G) y⁻¹)) * (((v : K) : L²G) (y⁻¹ * x)) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with y
          ring

/-- Helper for Theorem 4-51: the natural right matrix coefficient attached to `u v : K`
identifies against continuous test vectors with the weighted regular-orbit integral from
Lemma 4-50. -/
theorem inner_naturalRightOrbitCoefficient_toLp_eq_weightedOrbitIntegral_of_continuous
    (K : Submodule ℂ L²G) (u v : K) (W : C(G, ℂ)) :
    let kernel : G → ℂ := fun y ↦ conj ((((u : K) : L²G) y⁻¹))
    let Fuv : C(G, ℂ) :=
      ⟨fun x ↦ inner ℂ ((u : K) : L²G)
          (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
        (innerSL ℂ ((u : K) : L²G)).continuous.comp
          (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
    inner ℂ (ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
        (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv) =
      ∫ y : G, kernel y * inner ℂ (ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
        (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
  let kernel : G → ℂ := fun y ↦ conj ((((u : K) : L²G) y⁻¹))
  let seed : G → ℂ := fun y ↦ (((v : K) : L²G) y)
  let Fuv : C(G, ℂ) :=
    ⟨fun x ↦ inner ℂ ((u : K) : L²G)
        (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
      (innerSL ℂ ((u : K) : L²G)).continuous.comp
        (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
  have hkernel_int : Integrable kernel μG := by
    -- The kernel is the inversion-conjugate of an `L²(G)` vector, hence integrable.
    simpa [kernel] using integrable_conj_inv_of_memLp (G := G) (((u : K) : L²G))
  have hseed_int : Integrable seed μG := by
    -- Compactness upgrades the ambient `L²(G)` representative of `v` to an `L¹` function.
    simpa [seed] using
      (Lp.memLp (((v : K) : L²G))).integrable (q := (2 : ℝ≥0∞)) (by norm_num)
  have hpair_mul_int :
      Integrable (fun z : G × G ↦ kernel z.1 * seed z.2) ((μG : Measure G).prod μG) := by
    -- The separated kernel-seed product is integrable on the product space.
    exact hkernel_int.mul_prod hseed_int
  have hpair_trans_int :
      Integrable
        (fun z : G × G ↦
          (kernel z.1 * seed z.2) * conj (W (z.1 * z.2)))
        ((μG : Measure G).prod μG) := by
    -- Route correction: use boundedness of the continuous twist factor instead of asking Lean to
    -- re-solve the compact `continuousOn` integrability interface inside the main proof.
    let twist : G × G → ℂ := fun z ↦ conj (W (z.1 * z.2))
    letI : OpensMeasurableSpace (G × G) := by infer_instance
    have htwist_cont : Continuous twist := by
      exact Complex.continuous_conj.comp (W.continuous.comp (continuous_fst.mul continuous_snd))
    have htwist_int : Integrable twist ((μG : Measure G).prod μG) := by
      have hcompact : HasCompactSupport twist := by
        exact HasCompactSupport.of_support_subset_isCompact
          (by simpa using isCompact_univ)
          (by intro z hz; simp)
      exact htwist_cont.integrable_of_hasCompactSupport hcompact
    have htwist_meas : AEStronglyMeasurable twist ((μG : Measure G).prod μG) :=
      htwist_int.aestronglyMeasurable
    have htwist_bound :
        ∀ᵐ z : G × G ∂((μG : Measure G).prod μG), ‖twist z‖ ≤ ‖W‖ := by
      exact Filter.Eventually.of_forall fun z ↦ by
        simpa [twist] using W.norm_coe_le_norm (z.1 * z.2)
    simpa [twist] using hpair_mul_int.mul_bdd htwist_meas htwist_bound
  have hpair_int :
      Integrable
        (fun z : G × G ↦
          kernel z.2 * (seed (z.2⁻¹ * z.1) * conj (W z.1)))
        ((μG : Measure G).prod μG) := by
    -- Pull the integrable product integrand back along `(x, y) ↦ (y, y⁻¹ * x)`.
    letI : ContinuousMul G := by infer_instance
    letI : OpensMeasurableSpace G := by infer_instance
    letI : MeasurableMul G := by infer_instance
    letI : MeasurableMul₂ G := by infer_instance
    letI : MeasurableInv G := by infer_instance
    have hswap :
        MeasurePreserving (fun z : G × G ↦ (z.2, z.2⁻¹ * z.1))
          ((μG : Measure G).prod μG) ((μG : Measure G).prod μG) := by
      simpa using
        (measurePreserving_prod_inv_mul_swap (μ := (μG : Measure G)) (ν := (μG : Measure G)))
    simpa [Function.comp, mul_assoc, mul_comm, mul_left_comm] using
      hswap.integrable_comp_of_integrable hpair_trans_int
  calc
    inner ℂ (ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
        (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv)
      = ∫ x : G, Fuv x * conj (W x) ∂μG := by
          -- Expand the `L²(G)` inner product through the literal continuous representatives.
          rw [MeasureTheory.L2.inner_def]
          refine integral_congr_ae ?_
          filter_upwards
              [ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
                Fuv,
               ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
                W]
            with x hxF hxW
          rw [hxF, hxW, RCLike.inner_apply]
    _ = ∫ x : G, (∫ y : G, kernel y * seed (y⁻¹ * x) ∂μG) * conj (W x) ∂μG := by
          -- Rewrite the coefficient with the convolution normal form already proved above.
          refine integral_congr_ae ?_
          filter_upwards with x
          dsimp [Fuv, kernel, seed]
          rw [naturalRightOrbitCoefficient_apply_eq_convolutionIntegral (G := G) (K := K) u v x]
    _ = ∫ x : G, ∫ y : G, kernel y * (seed (y⁻¹ * x) * conj (W x)) ∂μG ∂μG := by
          -- Move the scalar test factor inside the `y`-integral.
          refine integral_congr_ae ?_
          filter_upwards with x
          calc
            (∫ y : G, kernel y * seed (y⁻¹ * x) ∂μG) * conj (W x)
              = ∫ y : G, (kernel y * seed (y⁻¹ * x)) * conj (W x) ∂μG := by
                  symm
                  simpa using
                    integral_mul_const (conj (W x)) (fun y : G ↦ kernel y * seed (y⁻¹ * x))
            _ = ∫ y : G, kernel y * (seed (y⁻¹ * x) * conj (W x)) ∂μG := by
                  refine integral_congr_ae ?_
                  filter_upwards with y
                  rw [mul_assoc]
    _ = ∫ y : G, ∫ x : G, kernel y * (seed (y⁻¹ * x) * conj (W x)) ∂μG ∂μG := by
          -- One Fubini swap is now justified by the product-integrability lemma above.
          rw [integral_integral_swap hpair_int]
    _ = ∫ y : G, kernel y * (∫ x : G, seed (y⁻¹ * x) * conj (W x) ∂μG) ∂μG := by
          -- Pull the scalar weight `kernel y` out of the inner integral.
          refine integral_congr_ae ?_
          filter_upwards with y
          simpa using
            integral_const_mul (kernel y) (fun x : G ↦ seed (y⁻¹ * x) * conj (W x))
    _ = ∫ y : G, kernel y * (∫ z : G, seed z * conj (W (y * z)) ∂μG) ∂μG := by
          -- Normalize the inner scalar integral by left-invariance of Haar measure.
          refine integral_congr_ae ?_
          filter_upwards with y
          congr 1
          simpa [mul_assoc] using
            (integral_mul_left_eq_self
              (μ := (μG : Measure G))
              (f := fun z : G ↦ seed z * conj (W (y * z))) y⁻¹)
    _ = ∫ y : G, kernel y * (∫ z : G, seed z *
          conj ((ContinuousMap.toLp (2 : ENNReal) μG ℂ W) (y * z)) ∂μG) ∂μG := by
          -- Replace the continuous test by its `L²` representative under left translation.
          refine integral_congr_ae ?_
          filter_upwards with y
          congr 1
          refine integral_congr_ae ?_
          filter_upwards
              [(measurePreserving_mul_left (μG : Measure G) y).quasiMeasurePreserving.ae_eq_comp
                (ContinuousMap.coeFn_toLp (μ := (μG : Measure G)) (p := (2 : ENNReal))
                  (𝕜 := ℂ) W)]
            with z hz
          simpa using congrArg (fun c : ℂ ↦ seed z * conj c) hz.symm
    _ = ∫ y : G, kernel y * inner ℂ (ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
          (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
          -- The inner scalar integral is exactly the pairing against the left translate of `v`.
          refine integral_congr_ae ?_
          filter_upwards with y
          simpa [seed] using
            congrArg
              (fun c : ℂ ↦ kernel y * c)
              ((inner_regularRepresentation_eq_integral_mul_conj
                (G := G) (g := y)
                (w := ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
                (v := ((v : K) : L²G))).symm)

/-- Helper for Theorem 4-51: the natural right matrix coefficient attached to `u v : K`
identifies against arbitrary test vectors with the weighted regular-orbit integral from
Lemma 4-50. -/
theorem inner_naturalRightOrbitCoefficient_toLp_eq_weightedOrbitIntegral
    (K : Submodule ℂ L²G) (u v : K) (w : L²G) :
    let kernel : G → ℂ := fun y ↦ conj ((((u : K) : L²G) y⁻¹))
    let Fuv : C(G, ℂ) :=
      ⟨fun x ↦ inner ℂ ((u : K) : L²G)
          (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
        (innerSL ℂ ((u : K) : L²G)).continuous.comp
          (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
    inner ℂ w (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv) =
      ∫ y : G, kernel y * inner ℂ w (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
  let kernel : G → ℂ := fun y ↦ conj ((((u : K) : L²G) y⁻¹))
  let Fuv : C(G, ℂ) :=
    ⟨fun x ↦ inner ℂ ((u : K) : L²G)
        (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
      (innerSL ℂ ((u : K) : L²G)).continuous.comp
        (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
  let T : L²G := ∫ y : G, kernel y • regularRepresentation μG y ((v : K) : L²G) ∂μG
  have hkernel_int : Integrable kernel μG := by
    -- The same `L¹` kernel controls both the continuous-test bridge and the Bochner integral `T`.
    simpa [kernel] using integrable_conj_inv_of_memLp (G := G) (((u : K) : L²G))
  have horbit_int :
      Integrable (fun y : G ↦ kernel y • regularRepresentation μG y ((v : K) : L²G)) μG := by
    -- Lemma 4-50 already packages the weighted regular-orbit integrability.
    simpa [kernel] using
      integrable_weightedRegularRepresentationOrbit_lp
        (G := G) (f := kernel) hkernel_int (((v : K) : L²G))
  have hT_inner (z : L²G) :
      inner ℂ z T =
        ∫ y : G, kernel y * inner ℂ z (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
    -- Pairing against `T` is the weighted regular-orbit scalar integral.
    calc
      inner ℂ z T
        = inner ℂ z (∫ y : G, kernel y • regularRepresentation μG y ((v : K) : L²G) ∂μG) := by
            rfl
      _ = ∫ y : G, inner ℂ z (kernel y • regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
            symm
            exact integral_inner (𝕜 := ℂ) horbit_int z
      _ = ∫ y : G, kernel y * inner ℂ z (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
            refine integral_congr_ae ?_
            filter_upwards with y
            rw [inner_smul_right]
  have hclosed :
      IsClosed
        {z : L²G |
          inner ℂ z (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv) = inner ℂ z T} := by
    -- The equality locus of two continuous scalar functionals is closed.
    refine isClosed_eq ?_ ?_
    · simpa using
        (continuous_id.inner continuous_const :
          Continuous fun z : L²G => inner ℂ z (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv))
    · simpa using
        (continuous_id.inner continuous_const : Continuous fun z : L²G => inner ℂ z T)
  have hdense :
      DenseRange (ContinuousMap.toLp (2 : ENNReal) μG ℂ : C(G, ℂ) →L[ℂ] L²G) :=
    ContinuousMap.toLp_denseRange (α := G) (E := ℂ) (μ := (μG : Measure G))
      (p := (2 : ENNReal)) (𝕜 := ℂ) (by norm_num)
  have hEq :
      inner ℂ w (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv) = inner ℂ w T := by
    -- Extend the continuous-test identity from the dense image of `ContinuousMap.toLp`.
    refine hdense.induction_on w hclosed ?_
    intro W
    calc
      inner ℂ (ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
          (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv)
        = ∫ y : G, kernel y * inner ℂ (ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
            (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
              simpa [kernel, Fuv] using
                inner_naturalRightOrbitCoefficient_toLp_eq_weightedOrbitIntegral_of_continuous
                  (G := G) (K := K) u v W
      _ = inner ℂ (ContinuousMap.toLp (2 : ENNReal) μG ℂ W) T := by
            symm
            exact hT_inner (ContinuousMap.toLp (2 : ENNReal) μG ℂ W)
  calc
    inner ℂ w (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv) = inner ℂ w T := hEq
    _ = ∫ y : G, kernel y * inner ℂ w (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
          exact hT_inner w

/-- Helper for Theorem 4-51: the natural right matrix coefficient attached to `u v : K`
identifies with the convolution owner from Lemma 4-50. -/
theorem naturalRightOrbitCoefficient_toLp_eq_compactGroupConvolutionToLp
    (K : Submodule ℂ L²G) (u v : K) :
    let kernel : G → ℂ := fun y ↦ conj ((((u : K) : L²G) y⁻¹))
    let seed : G → ℂ := fun y ↦ (((v : K) : L²G) y)
    let Fuv : C(G, ℂ) :=
      ⟨fun x ↦ inner ℂ ((u : K) : L²G)
          (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
        (innerSL ℂ ((u : K) : L²G)).continuous.comp
          (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
    ∃ hF : MemLp (compactGroupConvolutionFun (G := G) kernel seed) (2 : ENNReal) μG,
      ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv =
        compactGroupConvolutionToLp (G := G) kernel seed hF := by
  let kernel : G → ℂ := fun y ↦ conj ((((u : K) : L²G) y⁻¹))
  let seed : G → ℂ := fun y ↦ (((v : K) : L²G) y)
  let Fuv : C(G, ℂ) :=
    ⟨fun x ↦ inner ℂ ((u : K) : L²G)
        (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
      (innerSL ℂ ((u : K) : L²G)).continuous.comp
        (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
  have hseed_mem : MemLp seed (2 : ENNReal) μG := by
    -- The seed is just the ambient `L²(G)` representative of `v`.
    simpa [seed] using (Lp.memLp (((v : K) : L²G)))
  have hseed_toLp : MeasureTheory.MemLp.toLp seed hseed_mem = ((v : K) : L²G) := by
    -- Reusing the ambient `L²(G)` class avoids introducing a second owner for `v`.
    simpa [seed] using
      (MeasureTheory.MemLp.toLp_congr hseed_mem (Lp.memLp (((v : K) : L²G)))
        (Filter.EventuallyEq.rfl :
          seed =ᵐ[μG] fun y ↦ (((v : K) : L²G) y)))
  have hkernel_int : Integrable kernel μG := by
    -- The kernel is the inversion-conjugate of an `L²(G)` vector, hence integrable on the compact
    -- group.
    simpa [kernel] using integrable_conj_inv_of_memLp (G := G) (((u : K) : L²G))
  have horbit_int :
      Integrable (fun y : G ↦ kernel y • regularRepresentation μG y ((v : K) : L²G)) μG := by
    -- Lemma 4-50 already packages the weighted regular-orbit integrability we need.
    simpa [seed, hseed_toLp] using
      (integrable_weightedRegularRepresentationOrbit
        (G := G) (f := kernel) (h := seed) hkernel_int hseed_mem)
  rcases exists_compactGroupConvolutionToLp_eq_weightedOrbitIntegral
      (G := G) (f := kernel) (h := seed) hseed_mem with ⟨hF, hweighted⟩
  refine ⟨hF, ?_⟩
  -- Compare the two `L²(G)` owners only through scalar pairings with arbitrary test vectors.
  refine ext_inner_left ℂ ?_
  intro w
  calc
    inner ℂ w (ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv)
      = ∫ y : G, kernel y * inner ℂ w (regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
          simpa [kernel, Fuv] using
            inner_naturalRightOrbitCoefficient_toLp_eq_weightedOrbitIntegral
              (G := G) (K := K) u v w
    _ = ∫ y : G, inner ℂ w (kernel y • regularRepresentation μG y ((v : K) : L²G)) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with y
          rw [inner_smul_right]
    _ = inner ℂ w (∫ y : G, kernel y • regularRepresentation μG y ((v : K) : L²G) ∂μG) := by
          symm
          exact (integral_inner (𝕜 := ℂ) horbit_int w).symm
    _ = inner ℂ w (compactGroupConvolutionToLp (G := G) kernel seed hF) := by
          symm
          simpa [hseed_toLp] using
            congrArg (fun z : L²G => inner ℂ w z) hweighted

/-- Helper for Theorem 4-51: after forgetting the nested subtype structure, the matrix
coefficient of a right subrepresentation is exactly the ambient natural right-orbit coefficient. -/
theorem matrixCoefficientL2_eq_naturalRightOrbitCoefficient_toLp
    (K : Submodule ℂ L²G)
    (hK_right : ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K)
    (τ : Subrepresentation (closedRightInvariantRepresentation (G := G) K hK_right))
    (σ : Subrepresentation τ.toRepresentation)
    [FiniteDimensional ℂ σ.toSubmodule]
    (hσ_cont : σ.toRepresentation.IsContinuous)
    (b : OrthonormalBasis ι ℂ σ.toSubmodule) (i j : ι) :
    let u : K := (((b i : σ.toSubmodule) : τ.toSubmodule) : K)
    let v : K := (((b j : σ.toSubmodule) : τ.toSubmodule) : K)
    let Fuv : C(G, ℂ) :=
      ⟨fun x ↦ inner ℂ ((u : K) : L²G)
          (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
        (innerSL ℂ ((u : K) : L²G)).continuous.comp
          (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
    matrixCoefficientL2OfContinuous σ.toRepresentation hσ_cont b i j =
      ContinuousMap.toLp (2 : ENNReal) μG ℂ Fuv := by
  let u : K := (((b i : σ.toSubmodule) : τ.toSubmodule) : K)
  let v : K := (((b j : σ.toSubmodule) : τ.toSubmodule) : K)
  let Fuv : C(G, ℂ) :=
    ⟨fun x ↦ inner ℂ ((u : K) : L²G)
        (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
      (innerSL ℂ ((u : K) : L²G)).continuous.comp
        (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
  let Fmc : C(G, ℂ) :=
    ⟨mc[σ.toRepresentation, b, i, j],
      matrixCoefficient_continuous_of_isContinuous σ.toRepresentation hσ_cont b i j⟩
  have hcoeff : Fmc = Fuv := by
    ext x
    have hact :=
      closedRightInvariantSubrepresentation_apply_coe
        (G := G) (K := K) (hK_right := hK_right) (τ := τ) (σ := σ) (g := x) (z := b j)
    have hinner :=
      congrArg
        (fun z : L²G => inner ℂ ((((b i : σ.toSubmodule) : τ.toSubmodule) : K) : L²G) z) hact
    -- The restricted coefficient becomes the ambient right-orbit coefficient after forgetting the
    -- nested subtype wrappers.
    simpa [Fmc, Fuv, u, v, matrixCoefficient_eq_inner, OrthonormalBasis.repr_apply_apply] using
      hinner
  -- Passing the common continuous representative to `L²(G)` gives the desired identification.
  simpa [matrixCoefficientL2OfContinuous, Fmc, Fuv] using
    congrArg (ContinuousMap.toLp (2 : ENNReal) μG ℂ) hcoeff

/-- Helper for Theorem 4-51: every matrix coefficient of a finite-dimensional nested
right subrepresentation of a closed left-invariant submodule `K ≤ L²(G)` lies in `K`. -/
theorem matrixCoefficientL2_mem_closedInvariant_of_rightSubrepresentation
    (K : Submodule ℂ L²G) (hK_closed : IsClosed (K : Set L²G))
    (hK_left : ∀ g : G, Set.MapsTo (regularRepresentation μG g) K K)
    (hK_right : ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K)
    (τ : Subrepresentation (closedRightInvariantRepresentation (G := G) K hK_right))
    (σ : Subrepresentation τ.toRepresentation)
    [FiniteDimensional ℂ σ.toSubmodule]
    (hσ_cont : σ.toRepresentation.IsContinuous)
    (hσ_unitary : σ.toRepresentation.IsUnitary)
    (b : OrthonormalBasis ι ℂ σ.toSubmodule) (i j : ι) :
    matrixCoefficientL2OfContinuous σ.toRepresentation hσ_cont b i j ∈ K := by
  letI : σ.toRepresentation.IsUnitary := hσ_unitary
  let u : K := (((b i : σ.toSubmodule) : τ.toSubmodule) : K)
  let v : K := (((b j : σ.toSubmodule) : τ.toSubmodule) : K)
  let kernel : G → ℂ := fun y ↦ conj ((((u : K) : L²G) y⁻¹))
  let seed : G → ℂ := fun y ↦ (((v : K) : L²G) y)
  let Fuv : C(G, ℂ) :=
    ⟨fun x ↦ inner ℂ ((u : K) : L²G)
        (rightRegularRepresentation (G := G) x ((v : K) : L²G)),
      (innerSL ℂ ((u : K) : L²G)).continuous.comp
        (continuous_rightRegularRepresentation_orbit (G := G) ((v : K) : L²G))⟩
  rcases
      (naturalRightOrbitCoefficient_toLp_eq_compactGroupConvolutionToLp
        (G := G) (K := K) u v) with
    ⟨hF, hFuv⟩
  have hseed_mem : MemLp seed (2 : ENNReal) μG := by
    simpa [seed] using (Lp.memLp (((v : K) : L²G)))
  have hseed_toLp : MemLp.toLp seed hseed_mem = ((v : K) : L²G) := by
    simpa [seed] using
      (MemLp.toLp_congr hseed_mem (Lp.memLp (((v : K) : L²G)))
        (Filter.EventuallyEq.rfl :
          seed =ᵐ[μG] fun y ↦ (((v : K) : L²G) y)))
  have hv_mem : MemLp.toLp seed hseed_mem ∈ K := by
    rw [hseed_toLp]
    exact v.property
  have hkernel_int : Integrable kernel μG := by
    simpa [kernel] using integrable_conj_inv_of_memLp (G := G) (((u : K) : L²G))
  rcases
      (compactGroupConvolutionToLp_mem_of_closed_leftInvariant
        (G := G) (K := K) hK_closed hK_left
        (f := kernel) (h := seed) hkernel_int hseed_mem hv_mem) with
    ⟨hF', hconv_mem⟩
  have hsame :
      compactGroupConvolutionToLp (G := G) kernel seed hF =
        compactGroupConvolutionToLp (G := G) kernel seed hF' := by
    simpa [compactGroupConvolutionToLp] using
      (MemLp.toLp_congr hF hF' (Filter.EventuallyEq.rfl :
        compactGroupConvolutionFun (G := G) kernel seed =ᵐ[μG]
          compactGroupConvolutionFun (G := G) kernel seed))
  -- First identify the restricted matrix coefficient with the ambient right-orbit coefficient.
  rw [matrixCoefficientL2_eq_naturalRightOrbitCoefficient_toLp
    (G := G) (K := K) (hK_right := hK_right) (τ := τ) (σ := σ)
    (hσ_cont := hσ_cont) (b := b) (i := i) (j := j)]
  -- Then move into `K` through the convolution owner from Lemma 4-50.
  rw [hFuv, hsame]
  exact hconv_mem

/-- Theorem 4-51 — Peter–Weyl Theorem.

If `G` is a compact group, then the `ℂ`-linear span of the `L²(G)`-classes of all matrix
coefficients of all finite-dimensional irreducible unitary continuous representations of `G` is
dense in `L²(G)`. -/
theorem peterWeyl_dense_span_matrixCoefficientSet :
    Dense
      ((Submodule.span ℂ peterWeylMatrixCoefficientSet :
        Submodule ℂ L²G) : Set L²G) := by
  let PW : Submodule ℂ L²G := Submodule.span ℂ peterWeylMatrixCoefficientSet
  let U : Submodule ℂ L²G := PW.topologicalClosure
  let K : Submodule ℂ L²G := Uᗮ
  -- Route correction: the left-translation front end is now stabilized by
  -- `matrixCoefficientL2OfContinuous_mem_peterWeylSpan_of_vectors` and
  -- `peterWeylSpan_leftInvariant`, so the remaining proof should focus only on the closed
  -- orthogonal-complement/convolution/eigenspace argument from the source proof.
  by_contra hDense
  have hU_ne_top : U ≠ ⊤ := by
    intro hU_top
    have hPW_dense : Dense (PW : Set L²G) :=
      (Submodule.dense_iff_topologicalClosure_eq_top).2 <| by
        simpa [U] using hU_top
    exact hDense <| by simpa [PW] using hPW_dense
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    apply hU_ne_top
    exact Submodule.orthogonal_eq_bot_iff.mp <| by simpa [K] using hK_bot
  have hU_left :
      ∀ g : G, Set.MapsTo (regularRepresentation μG g) U U :=
    topologicalClosure_leftInvariant_of_leftInvariant
      (G := G) (S := PW) fun g f hf ↦ peterWeylSpan_leftInvariant (G := G) g hf
  have hPW_invConj :
      Set.MapsTo (invConjLp (G := G)) PW PW := by
    intro x hx
    -- The Peter–Weyl span is already stable under the involution `f(x) ↦ conj (f (x⁻¹))`.
    exact peterWeylSpan_invConjInvariant (G := G) hx
  have hU_invConj :
      Set.MapsTo (invConjLp (G := G)) U U :=
    topologicalClosure_invConjInvariant_of_invConjInvariant (G := G) PW hPW_invConj
  have hK_left :
      ∀ g : G, Set.MapsTo (regularRepresentation μG g) K K :=
    orthogonal_leftInvariant_of_leftInvariant (G := G) (S := U) hU_left
  have hK_invConj :
      Set.MapsTo (invConjLp (G := G)) K K :=
    orthogonal_invConjInvariant_of_invConjInvariant (G := G) (S := U) hU_invConj
  have hK_right :
      ∀ g : G, Set.MapsTo (rightRegularRepresentation (G := G) g) K K :=
    rightInvariant_of_leftInvariant_invConjInvariant (G := G) K hK_left hK_invConj
  have hK_closed : IsClosed (K : Set L²G) := Submodule.isClosed_orthogonal U
  obtain ⟨τ, hτ_ne_bot, hτ_fd⟩ :=
    existsNonzeroFiniteDimensionalSubrepresentationOfClosedRightInvariant
      (G := G) K hK_closed hK_right hK_ne_bot
  let ρτ : Representation ℂ G τ.toSubmodule := τ.toRepresentation
  letI : FiniteDimensional ℂ τ.toSubmodule := hτ_fd
  letI : Representation.IsContinuous (rightRegularRepresentationRep (G := G)) :=
    rightRegularRepresentationRep_isContinuous (G := G)
  letI : Representation.IsContinuous (closedRightInvariantRepresentation (G := G) K hK_right) :=
    subrepresentationToRepresentationIsContinuous
      (ρ := rightRegularRepresentationRep (G := G))
      (σ := closedRightInvariantSubrepresentation (G := G) K hK_right)
  letI : Representation.IsUnitary (closedRightInvariantRepresentation (G := G) K hK_right) :=
    closedRightInvariantRepresentationIsUnitary (G := G) K hK_right
  letI : Representation.IsContinuous ρτ :=
    subrepresentationToRepresentationIsContinuous
      (ρ := closedRightInvariantRepresentation (G := G) K hK_right) τ
  letI : Representation.IsUnitary ρτ :=
    subrepresentationToRepresentationIsUnitary
      (ρ := closedRightInvariantRepresentation (G := G) K hK_right) τ
  have hτ_sub_ne_bot : τ.toSubmodule ≠ ⊥ := by
    intro hbot
    exact hτ_ne_bot (Subrepresentation.toSubmodule_injective hbot)
  letI : Nontrivial τ.toSubmodule := (Submodule.nontrivial_iff_ne_bot).2 hτ_sub_ne_bot
  obtain ⟨π, hπ_ne_bot, hπ_irred⟩ :=
    existsNonzeroIrreducibleSubrepresentationOfNonzeroFiniteDimensional (ρ := ρτ)
  let ρπ : Representation ℂ G π.toSubmodule := π.toRepresentation
  letI : Representation.IsContinuous ρπ :=
    subrepresentationToRepresentationIsContinuous (ρ := ρτ) π
  letI : Representation.IsUnitary ρπ :=
    subrepresentationToRepresentationIsUnitary (ρ := ρτ) π
  letI : Representation.IsIrreducible ρπ := hπ_irred
  have hπ_sub_ne_bot : π.toSubmodule ≠ ⊥ := by
    intro hbot
    exact hπ_ne_bot (Subrepresentation.toSubmodule_injective hbot)
  letI : Nontrivial π.toSubmodule := (Submodule.nontrivial_iff_ne_bot).2 hπ_sub_ne_bot
  let b : OrthonormalBasis (Fin (Module.finrank ℂ π.toSubmodule)) ℂ π.toSubmodule :=
    stdOrthonormalBasis ℂ π.toSubmodule
  have hπ_finrank_pos : 0 < Module.finrank ℂ π.toSubmodule :=
    Module.finrank_pos
  let i : Fin (Module.finrank ℂ π.toSubmodule) := ⟨0, hπ_finrank_pos⟩
  let f : L²G :=
    matrixCoefficientL2OfContinuous ρπ (show ρπ.IsContinuous from inferInstance) b i i
  have hfPW : f ∈ PW := by
    -- Reuse the canonical Peter–Weyl generator-membership lemma instead of repackaging the
    -- existential witness by hand.
    refine Submodule.subset_span ?_
    refine (mem_peterWeylMatrixCoefficientSet_iff _).2 ?_
    exact ⟨↥π.toSubmodule, inferInstance, inferInstance, inferInstance,
      Fin (Module.finrank ℂ π.toSubmodule), inferInstance, ρπ,
      (show ρπ.IsContinuous from inferInstance), (show ρπ.IsIrreducible from inferInstance),
      (show ρπ.IsUnitary from inferInstance), b, i, i, rfl⟩
  have hfU : f ∈ U := by
    -- The Peter–Weyl span sits inside its topological closure.
    exact (Submodule.le_topologicalClosure PW) hfPW
  have hfK : f ∈ K := by
    -- The remaining substantive step is now the right-coefficient/convolution bridge for
    -- `π ≤ τ ≤ K`, after the witness has been moved to the right regular action.
    simpa [f] using
      matrixCoefficientL2_mem_closedInvariant_of_rightSubrepresentation
        (G := G) (K := K) hK_closed hK_left hK_right τ π
        (show ρπ.IsContinuous from inferInstance)
        (show ρπ.IsUnitary from inferInstance) b i i
  have hinner_zero : inner ℂ f f = 0 :=
    coefficientSelfInner_eq_zero_of_memOrthogonalClosure (U := U) hfK hfU
  have hfinrank_ne_zero : (Module.finrank ℂ π.toSubmodule : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hπ_finrank_pos)
  have hinner_formula :
      inner ℂ f f = (Module.finrank ℂ π.toSubmodule : ℂ)⁻¹ := by
    -- Lemma 4-22 computes the norm-square of the chosen diagonal coefficient.
    simpa [f] using
      matrixCoefficientL2_inner_self_eq_invFinrank
        (G := G) ρπ (show ρπ.IsContinuous from inferInstance)
        (show ρπ.IsIrreducible from inferInstance)
        (show ρπ.IsUnitary from inferInstance) b i
  have hinner_ne_zero : inner ℂ f f ≠ 0 := by
    rw [hinner_formula]
    exact inv_ne_zero hfinrank_ne_zero
  exact hinner_ne_zero hinner_zero

/-- The closure of the `ℂ`-span of the Peter–Weyl matrix coefficients is all of `L²(G)`. -/
theorem peterWeyl_span_matrixCoefficientSet_topologicalClosure :
    (Submodule.span ℂ peterWeylMatrixCoefficientSet :
      Submodule ℂ L²G).topologicalClosure = ⊤ := by
  -- Convert the dense-span statement to the equivalent topological-closure formulation.
  exact (Submodule.dense_iff_topologicalClosure_eq_top).mp
    peterWeyl_dense_span_matrixCoefficientSet

end

end Representation
