import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_12 (from Chap06) -/
section

variable {ι : Type*}
variable {α : Type*} [Zero α]

/-
Definition 6.12 is `source-facing` in the Chapter 6 sparse-optimization API.

Domain sampling:
- `Function.support` from mathlib is the `core/canonical` owner of the nonzero-coordinate set of a
  vector-valued function;
- `Set.encard` is the canonical cardinality owner for “at most `s` nonzero coordinates,” because
  it does not collapse infinite support to the junk value `0`;
- on finite index types, mathlib’s `hammingNorm` is the canonical cardinality bridge for the same
  notion, so the finite-dimensional `ℝ^n` surface should be derived from the support owner rather
  than rebuilt separately;
- Chapter 6 specializes this owner to `Fin n → ℝ`, but the source-facing notion itself is the
  support-cardinality condition rather than the concrete coordinate model;
- later Chapter 6 files `Lemma_6_71` and `Example_6_72` should recover the textbook `ℝ^n`
  presentation by specialization of this owner and its notation, not by a parallel local copy.

Primitive data:
- `source-facing`: only the sparsity level `s` and the vector `x`;
- `derived API`: the membership characterization, which is definitional.

Layer triage:
- `source-facing`: the sparse-vector set `sSparseVectors`;
- `core/canonical`: the pair `Function.support` and `Set.encard`;
- `bridge/view`: the notation `C_[s]` together with the finite-index `hammingNorm` bridge, whose
  specialization to `Fin n → ℝ` recovers the textbook `ℝ^n` presentation.

There is no higher project owner for this textbook set beyond the support-cardinality condition
itself, so the public owner here should remain the source-facing set `sSparseVectors`. -/

/-- Definition 6.12: the set `C_s = {x | ‖x‖₀ ≤ s}` of `s`-sparse vectors, defined as the
functions with at most `s` nonzero coordinates. The textbook `ℝ^n` formulation is the
specialization `ι = Fin n`, `α = ℝ`, while the canonical Lean owner itself only needs a codomain
with zero and uses `Set.encard` so the support count stays faithful even on infinite index types. -/
def sSparseVectors (s : ℕ) : Set (ι → α) :=
  {x | (Function.support x).encard ≤ s}

notation "C_[" s "]" => sSparseVectors s

-- Proof sketch: unfold `sSparseVectors`; membership in `C_[s]` is definitionally the statement
-- that the support set `{i | x i ≠ 0}` has cardinality at most `s`.
/-- A vector belongs to `C_s` exactly when it has at most `s` nonzero coordinates. -/
@[simp]
theorem mem_sSparseVectors_iff (s : ℕ) (x : ι → α) :
    x ∈ C_[s] ↔ (Function.support x).encard ≤ s :=
  Iff.rfl

section Finite

variable [Fintype ι] [DecidableEq α]

-- Proof sketch: on a finite index type, `Set.encard` agrees with `Finset.card`, and
-- `Function.support x` becomes the same finite set counted by mathlib's `hammingNorm x`.
/-- On a finite index type, the support cardinality used in `C_s` is exactly `hammingNorm`. -/
theorem support_encard_eq_hammingNorm (x : ι → α) :
    (Function.support x).encard = hammingNorm x := by
  classical
  rw [Set.encard_eq_coe_toFinset_card, hammingNorm]
  congr
  ext i
  simp [Function.support]

-- Proof sketch: combine the definitional membership theorem with
-- `support_encard_eq_hammingNorm`.
/-- Over a finite index type, `x ∈ C_s` exactly when its Hamming weight is at most `s`. -/
@[simp]
theorem mem_sSparseVectors_iff_hammingNorm_le (s : ℕ) (x : ι → α) :
    x ∈ C_[s] ↔ hammingNorm x ≤ s := by
  rw [mem_sSparseVectors_iff, support_encard_eq_hammingNorm]
  simp

end Finite

end

/-! ### Theorem_6_12 (from Chap06) -/
noncomputable section

universe u

open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 6.12 is `source-facing` in the Chapter 6 proximal-mapping API. Domain sampling in the
minimal scaling-transport closure identifies:

- `prox[...]` and `proximal_objective` from Definition 6.1 as the `core/canonical` owners,
- `proximal_mapping_scaling_translation` from Theorem 6.11 as the direct upstream transport
  theorem of the same kind,
- `proximal_mapping_precompose_continuousAffineMap` from Theorem 6.15 as the later stronger
  `bridge/view` generalization.

The primitive data here are only `g`, `lam`, and `x`. The inverse-scaling formula is therefore a
specialization of the existing Chapter 6 transport theorem, not a second owner-level minimizer
comparison API. -/

-- Proof sketch: specialize Theorem 6.11 with scale `lam⁻¹`, zero translation, and the objective
-- `g' z = λ g z`. This gives the required proximal transport immediately, up to rewriting the
-- transported scaled objective `((lam⁻¹)^2 • g')` pointwise to `z ↦ g z / λ`.
/-- Theorem 6.12: for the scaled pullback `f y = λ g (λ⁻¹ • y)`, the proximal set of `f` at `x`
is the scalar multiple by `λ` of the proximal set of `z ↦ g z / λ` at `λ⁻¹ • x`. This is the
chapter's set-valued formulation of the textbook identity
`prox_f(x) = λ prox_{g / λ}(x / λ)`. The textbook properness hypothesis on `g` is redundant for
this minimizer-set identity, so the canonical Lean statement omits it. -/
theorem proximal_mapping_smul_precompose_inv_smul
    (g : E → EReal) (lam : ℝ) (hlam : lam ≠ 0) (x : E) :
    prox[fun y : E ↦ (lam : EReal) * g (lam⁻¹ • y)] x =
      lam • prox[fun z : E ↦ g z / (lam : EReal)] (lam⁻¹ • x) := by
  let g' : E → EReal := fun z ↦ (lam : EReal) * g z
  have htransport :=
    proximal_mapping_scaling_translation g' lam⁻¹ (inv_ne_zero hlam) (0 : E) x
  have hcoeff : (lam⁻¹ ^ 2 : ℝ) * lam = lam⁻¹ := by
    field_simp [hlam]
  have hscale :
      (((lam⁻¹) ^ 2 : ℝ) : EReal) • g' =
        fun z : E ↦ g z / (lam : EReal) := by
    funext z
    change ((((lam⁻¹) ^ 2 : ℝ) : EReal) * ((lam : EReal) * g z)) =
      g z / (lam : EReal)
    rw [← mul_assoc]
    rw [show ((((lam⁻¹) ^ 2 : ℝ) : EReal) * (lam : EReal)) =
        ((((lam⁻¹ ^ 2 : ℝ) * lam : ℝ) : EReal)) by
      norm_num [EReal.coe_mul]]
    rw [show ((((lam⁻¹ ^ 2 : ℝ) * lam : ℝ) : EReal)) = ((lam⁻¹ : ℝ) : EReal) by
      exact_mod_cast hcoeff]
    rw [show ((lam⁻¹ : ℝ) : EReal) = (lam : EReal)⁻¹ by
      simpa using (EReal.coe_inv lam)]
    rw [div_eq_mul_inv, mul_comm]
  rw [hscale] at htransport
  simpa [g', Set.image_smul, hlam] using htransport

end
