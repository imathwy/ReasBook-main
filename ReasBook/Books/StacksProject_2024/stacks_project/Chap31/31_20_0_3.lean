import StacksProject_2024.Chap10.«10_69_0_1_Core»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {r : ℕ}

/- Source/core/bridge triage for 31.20.0.3:
- `source-facing`: for chosen generators `x₁, …, xᵣ ∈ J`, the polynomial map
  `(R / J)[T₁, …, Tᵣ] → ⨁ d ≥ 0, J^d / J^(d + 1)` sending `Tᵢ` to the degree-one class of `xᵢ`;
- `core/canonical`: `MvPolynomial.aeval`;
- `bridge/view`: the target owner `idealAssociatedGradedRing J` with degree-one generators
  `idealAssociatedGradedDegreeOne (x i)`.

The chosen family `x : Fin r → J` is genuine source data, so this file keeps the source-facing
specialization as a thin bridge rather than collapsing it to a bare recall of `MvPolynomial.aeval`.
-/
-- Semantic recall: `MvPolynomial.aeval` is the canonical owner for the evaluation map here, so
-- this file keeps the source-facing associated-graded bridge together with the generator image
-- lemma used by downstream polynomial calculations.

/-- 31.20.0.3: for chosen elements `x₁, ..., xᵣ ∈ J`, the canonical map
`(R / J)[T₁, ..., Tᵣ] → ⨁ d ≥ 0, J^d / J^(d + 1)` is the polynomial evaluation map
to the quotient-Rees owner `idealAssociatedGradedRing J`, sending `Tᵢ` to the degree-one class of
`xᵢ`. -/
abbrev quasiRegularIdealAssociatedGradedPolynomialMap
    (J : Ideal R) (x : Fin r → J) :
    MvPolynomial (Fin r) (R ⧸ J) →ₐ[R ⧸ J] idealAssociatedGradedRing J :=
  MvPolynomial.aeval fun i ↦ idealAssociatedGradedDegreeOne (x i)

/-- The polynomial evaluation map to the associated graded ring sends `Tᵢ` to the degree-one class
of the `i`-th chosen element of `J`. -/
@[simp] theorem quasiRegularIdealAssociatedGradedPolynomialMap_X
    (J : Ideal R) (x : Fin r → J) (i : Fin r) :
    quasiRegularIdealAssociatedGradedPolynomialMap J x (MvPolynomial.X i) =
      idealAssociatedGradedDegreeOne (x i) := by
  simp [quasiRegularIdealAssociatedGradedPolynomialMap]

end
