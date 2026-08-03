module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Group.Basic

public section

open Affine

/- Definition 50.6 (1): `Homeomorph.subRight x₀` is the translation sending `x`
to `x - x₀`. -/
#check Homeomorph.subRight

/-- Helper for Definition 50.6: translating an affine span by a point of its
generating set gives its vector span. -/
lemma imageAffineSpanVsubRight_eq_vectorSpan {𝕜 V P : Type*} [Ring 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AffineSpace V P] {s : Set P} {p : P}
    (hp : p ∈ s) :
    (fun q : P ↦ q -ᵥ p) '' (affineSpan 𝕜 s : Set P) =
      (vectorSpan 𝕜 s : Set V) := by
  -- Express both sides through membership in the direction of the affine span.
  ext v
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [← direction_affineSpan]
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem
      (mem_affineSpan 𝕜 hp) q).2 hq
  · intro hv
    rw [← direction_affineSpan] at hv
    refine ⟨v +ᵥ p, ?_, ?_⟩
    · exact (AffineSubspace.vadd_mem_iff_mem_direction v
        (mem_affineSpan 𝕜 hp)).2 hv
    · exact vadd_vsub v p

/-- Helper for Definition 50.6: `Fin.succ` enumerates the nonzero elements of
`Fin (k + 1)` without changing the range of a family. -/
private lemma rangeSucc_eq_rangeSubtypeNeZero {k : ℕ} {α : Type*}
    (f : Fin (k + 1) → α) :
    Set.range (fun i : Fin k ↦ f (Fin.succ i)) =
      Set.range (fun i : {j : Fin (k + 1) // j ≠ 0} ↦ f i) := by
  -- Reindex the right-hand family along the canonical equivalence omitting zero.
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨finSuccAboveEquiv (0 : Fin (k + 1)) i, ?_⟩
    apply congrArg f
    calc
      ↑(finSuccAboveEquiv (0 : Fin (k + 1)) i) =
          (0 : Fin (k + 1)).succAbove i :=
        congrArg Subtype.val (finSuccAboveEquiv_apply 0 i)
      _ = Fin.succ i := Fin.succAbove_zero_apply i
  · rintro ⟨j, rfl⟩
    refine ⟨(finSuccAboveEquiv (0 : Fin (k + 1))).symm j, ?_⟩
    apply congrArg f
    calc
      Fin.succ ((finSuccAboveEquiv (0 : Fin (k + 1))).symm j) =
          (0 : Fin (k + 1)).succAbove
            ((finSuccAboveEquiv (0 : Fin (k + 1))).symm j) :=
        (Fin.succAbove_zero_apply _).symm
      _ = ↑(finSuccAboveEquiv (0 : Fin (k + 1))
          ((finSuccAboveEquiv (0 : Fin (k + 1))).symm j)) :=
        (congrArg Subtype.val (finSuccAboveEquiv_apply 0 _)).symm
      _ = ↑j := congrArg Subtype.val
        ((finSuccAboveEquiv (0 : Fin (k + 1))).apply_symm_apply j)

/-- Helper for Definition 50.6: the vector span of a `Fin (k + 1)`-family is
spanned by its differences from the zeroth point. -/
private lemma vectorSpanRangeFinSucc_eq_spanVsub {𝕜 V P : Type*} [Ring 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AffineSpace V P] {k : ℕ}
    (x : Fin (k + 1) → P) :
    vectorSpan 𝕜 (Set.range x) =
      Submodule.span 𝕜
        (Set.range (fun i : Fin k ↦ x (Fin.succ i) -ᵥ x 0)) := by
  -- Use mathlib's nonzero-index formula, then put its range in `Fin.succ` form.
  rw [vectorSpan_range_eq_span_range_vsub_right_ne 𝕜 x 0,
    ← rangeSucc_eq_rangeSubtypeNeZero (fun i ↦ x i -ᵥ x 0)]

/-- Definition 50.6 (2): Translation by `-x 0` carries the plane spanned by the
points `x 0, …, x k` onto the span of their difference vectors. -/
theorem image_affineSpan_subRight {N k : ℕ}
    (x : Fin (k + 1) → EuclideanSpace ℝ (Fin N)) :
    Homeomorph.subRight (x 0) ''
        (affineSpan ℝ (Set.range x) : Set (EuclideanSpace ℝ (Fin N))) =
      (Submodule.span ℝ (Set.range (fun i : Fin k ↦ x (Fin.succ i) - x 0)) :
        Set (EuclideanSpace ℝ (Fin N))) := by
  -- First normalize the homeomorphism to affine-space subtraction.
  calc
    Homeomorph.subRight (x 0) ''
        (affineSpan ℝ (Set.range x) : Set (EuclideanSpace ℝ (Fin N))) =
        (fun q ↦ q -ᵥ x 0) ''
          (affineSpan ℝ (Set.range x) : Set (EuclideanSpace ℝ (Fin N))) := by
      ext v
      simp only [Set.mem_image, Homeomorph.subRight_apply, vsub_eq_sub]
    _ = (vectorSpan ℝ (Set.range x) : Set (EuclideanSpace ℝ (Fin N))) :=
      imageAffineSpanVsubRight_eq_vectorSpan (Set.mem_range_self 0)
    -- Finally reindex the direction by the `k` nonzero vertices.
    _ = (Submodule.span ℝ
          (Set.range (fun i : Fin k ↦ x (Fin.succ i) -ᵥ x 0)) :
          Set (EuclideanSpace ℝ (Fin N))) :=
      congrArg (fun W : Submodule ℝ (EuclideanSpace ℝ (Fin N)) ↦
        (W : Set (EuclideanSpace ℝ (Fin N))))
        (vectorSpanRangeFinSucc_eq_spanVsub x)
    _ = (Submodule.span ℝ
          (Set.range (fun i : Fin k ↦ x (Fin.succ i) - x 0)) :
          Set (EuclideanSpace ℝ (Fin N))) := by
      simp only [vsub_eq_sub]

/-- Definition 50.6 (3): The difference vectors from `x 0` are linearly independent. -/
theorem differenceVectors_linearIndependent {N k : ℕ}
    (x : Fin (k + 1) → EuclideanSpace ℝ (Fin N)) (hx : AffineIndependent ℝ x) :
    LinearIndependent ℝ (fun i : Fin k ↦ x (Fin.succ i) - x 0) := by
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ x 0).mp hx
  let e : Fin k ↪ {i : Fin (k + 1) // i ≠ 0} :=
    ⟨fun i ↦ ⟨Fin.succ i, by simp⟩,
      fun _ _ h ↦ Fin.succ_injective _ (Subtype.ext_iff.mp h)⟩
  exact h.comp e e.injective

/-- Definition 50.6 (4): The difference vectors from `x 0` form a basis of the
translated plane. -/
noncomputable def differenceVectorsBasis {N k : ℕ}
    (x : Fin (k + 1) → EuclideanSpace ℝ (Fin N)) (hx : AffineIndependent ℝ x) :
    Module.Basis (Fin k) ℝ
      (Submodule.span ℝ (Set.range (fun i : Fin k ↦ x (Fin.succ i) - x 0))) :=
  Module.Basis.span (differenceVectors_linearIndependent x hx)

/-- Definition 50.6 (5): The span of the difference vectors from `x 0` has dimension `k`. -/
theorem finrank_span_differenceVectors {N k : ℕ}
    (x : Fin (k + 1) → EuclideanSpace ℝ (Fin N)) (hx : AffineIndependent ℝ x) :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun i : Fin k ↦ x (Fin.succ i) - x 0))) = k := by
  simpa using finrank_span_eq_card (differenceVectors_linearIndependent x hx)
