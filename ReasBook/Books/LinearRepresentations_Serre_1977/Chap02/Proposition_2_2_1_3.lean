import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct Kronecker

noncomputable section

universe u v w

section

variable {k : Type u} [Field k] [Invertible (2 : k)]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

namespace Representation

variable (ρ : Representation k G V)

/- Source/core/bridge triage:
- `source-facing`: the three character identities stated below;
- `core/canonical`: `Representation.character` together with `char_prod`, `char_tensor`, and
  `char_iso`;
- `bridge/view`: `Sym² ρ`, `Alt² ρ`, and `ρ.symmetricAlternatingSquareEquivTensor` from
  Definition 1-1.6-1.

Primitive data lives entirely in the Chapter 1 owner layer. This file adds only the derived
character formulas, so there is no parallel wrapper API to keep. -/

/- Route correction: instead of introducing a splitting-field detour, we keep the source proof's
global tensor-square object and use the canonical decomposition
`(Sym² ρ).prod (Alt² ρ) ≃ ρ.tprod ρ`. The sum identity comes from the decomposition, the
difference identity comes from the tensor swap acting by `+1` and `-1` on the two summands, and a
single matrix computation identifies the swapped tensor-square trace with `χ(s^2)`. -/

section

omit [FiniteDimensional k V]

/-- Helper for Proposition 2-2.1-3: under the symmetric/alternating decomposition, the tensor swap
acts by `+1` on the symmetric summand and by `-1` on the alternating summand. -/
lemma tensorSwap_apply_symmetricAlternatingSquareEquivTensor
    (z : (Sym²ₛ ρ).toSubmodule × (Alt²ₛ ρ).toSubmodule) :
    ρ.tensorSwap ((ρ.symmetricAlternatingSquareEquivTensor) z) =
      (ρ.symmetricAlternatingSquareEquivTensor)
        (LinearMap.prodMap (LinearMap.id : Module.End k (Sym²ₛ ρ).toSubmodule)
          (-(LinearMap.id : Module.End k (Alt²ₛ ρ).toSubmodule)) z) := by
  rcases z with ⟨x, y⟩
  have hx : ρ.tensorSwap (x : V ⊗[k] V) = x := by
    exact (ρ.mem_symmetricSquareSubrepresentation_iff (z := (x : V ⊗[k] V))).1 x.2
  have hy : ρ.tensorSwap (y : V ⊗[k] V) = -(y : V ⊗[k] V) := by
    exact (ρ.mem_alternatingSquareSubrepresentation_iff (z := (y : V ⊗[k] V))).1 y.2
  have hx' : (_root_.TensorProduct.comm k V V) (x : V ⊗[k] V) = x := by
    simpa [Representation.tensorSwap] using hx
  have hy' : (_root_.TensorProduct.comm k V V) (y : V ⊗[k] V) = -(y : V ⊗[k] V) := by
    simpa [Representation.tensorSwap] using hy
  -- The direct-sum equivalence is the complementary-submodule decomposition, so it adds the two
  -- summands and the swap acts on them by the corresponding eigenvalues.
  simp [Representation.symmetricAlternatingSquareEquivTensor, hx', hy', LinearMap.prodMap_apply]

end

/-- Helper for Proposition 2-2.1-3: the difference of the symmetric- and alternating-square
characters is the trace of the tensor-square action composed with the tensor swap. -/
lemma char_symmetricSquare_sub_char_alternatingSquare (s : G) :
    (Sym² ρ).character s - (Alt² ρ).character s =
      LinearMap.trace k (V ⊗[k] V) (((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) := by
  let e := ρ.symmetricAlternatingSquareEquivTensor
  let F : Module.End k ((Sym²ₛ ρ).toSubmodule × (Alt²ₛ ρ).toSubmodule) :=
    LinearMap.prodMap ((Sym² ρ) s) (-(Alt² ρ) s)
  let S : Module.End k ((Sym²ₛ ρ).toSubmodule × (Alt²ₛ ρ).toSubmodule) :=
    LinearMap.prodMap (LinearMap.id : Module.End k (Sym²ₛ ρ).toSubmodule)
      (-(LinearMap.id : Module.End k (Alt²ₛ ρ).toSubmodule))
  have hconj : e.toLinearEquiv.conj F = ((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := e.toLinearEquiv.surjective x
    have hz :
        e (F z) = ((((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) : Module.End k (V ⊗[k] V)) (e z) := by
    -- First convert the sign operator on the product side to the tensor swap, then use the
    -- equivariance of `ρ.symmetricAlternatingSquareEquivTensor` for the group action.
      calc
        e (F z)
          = e
              (LinearMap.prodMap ((Sym² ρ) s) ((Alt² ρ) s) (S z)) := by
              rcases z with ⟨x, y⟩
              simp [F, S, LinearMap.prodMap_apply]
        _ = ((ρ.tprod ρ) s) (e (S z)) := by
              simpa [S, LinearMap.prodMap_apply] using
                (LinearMap.congr_fun (e.toIntertwiningMap.2 s) (z.1, -z.2))
        _ = ((ρ.tprod ρ) s) (ρ.tensorSwap (e z)) := by
              simpa [e] using congrArg ((ρ.tprod ρ) s)
                (ρ.tensorSwap_apply_symmetricAlternatingSquareEquivTensor z).symm
        _ = ((((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) : Module.End k (V ⊗[k] V)) (e z) := by
              rfl
    have hleft : e.invFun (e z) = z := by
      exact e.left_inv z
    have hz' :
        e (F (e.invFun (e z))) = ((((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) : Module.End k (V ⊗[k] V)) (e z) := by
      simpa [hleft] using hz
    simpa [LinearEquiv.conj_apply_apply] using hz'
  -- The trace on the product side is the trace difference, and conjugation preserves trace.
  calc
    (Sym² ρ).character s - (Alt² ρ).character s
      = LinearMap.trace k _ F := by
          simp [F, Representation.character, LinearMap.trace_prodMap', sub_eq_add_neg]
    _ = LinearMap.trace k (V ⊗[k] V) (e.toLinearEquiv.conj F) := by
          symm
          exact LinearMap.trace_conj' F e.toLinearEquiv
    _ = LinearMap.trace k (V ⊗[k] V) (((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) := by
          rw [hconj]

section

omit [Invertible (2 : k)]

/-- Helper for Proposition 2-2.1-3: the trace of the tensor-square action composed with the tensor
swap is the character value `χ(s^2)`. -/
lemma trace_tprod_apply_comp_tensorSwap_eq_char_sq (s : G) :
    LinearMap.trace k (V ⊗[k] V) (((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) = ρ.character (s ^ 2) := by
  classical
  let b := Module.Free.chooseBasis k V
  let ι := Module.Free.ChooseBasisIndex k V
  let A := LinearMap.toMatrix b b (ρ s)
  let P : Matrix (ι × ι) (ι × ι) k := (1 : Matrix (ι × ι) (ι × ι) k).submatrix Prod.swap id
  have hswapMatrix :
      LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b) ρ.tensorSwap = P := by
    simpa [Representation.tensorSwap, P] using
      (TensorProduct.toMatrix_comm (R := k) (bM := b) (bN := b))
  -- Pass to the tensor-product basis so that the swap is represented by the permutation matrix
  -- exchanging the two tensor indices.
  calc
    LinearMap.trace k (V ⊗[k] V) (((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap)
      =
        Matrix.trace
          (LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)
            ((((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) : Module.End k (V ⊗[k] V))) := by
          rw [LinearMap.trace_eq_matrix_trace k (b.tensorProduct b)]
    _ =
        Matrix.trace
          ((A ⊗ₖ A) * P) := by
          have hmatrix :
              LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)
                ((((ρ.tprod ρ) s) ∘ₗ ρ.tensorSwap) : Module.End k (V ⊗[k] V)) =
                  (A ⊗ₖ A) * P := by
                change LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)
                    ((((ρ.tprod ρ) s) * ρ.tensorSwap) : Module.End k (V ⊗[k] V)) =
                      (A ⊗ₖ A) * P
                rw [LinearMap.toMatrix_mul, Representation.tprod_apply, TensorProduct.toMatrix_map,
                  hswapMatrix]
          exact congrArg Matrix.trace hmatrix
    _ = Matrix.trace (A * A) := by
          rw [Matrix.trace, Matrix.trace]
          change ∑ ij : ι × ι, (((A ⊗ₖ A) * P) ij ij) = ∑ i : ι, ((A * A) i i)
          rw [show (∑ x : ι, (A * A) x x) = ∑ x : ι, ∑ j : ι, A x j * A j x by
            simp [Matrix.mul_apply]
            rfl]
          have hsum :
              (∑ x, ∑ x_1, ∑ x_2, ∑ x_3,
                if x_2 = x_1 ∧ x_3 = x then A x x_2 * A x_1 x_3 else 0) =
                  ∑ i, ∑ j, A i j * A j i := by
            simp_rw [ite_and]
            simp [Finset.mem_univ]
          simpa [P, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.submatrix_apply,
            Matrix.one_apply, Prod.swap_prod_mk, id_eq, Prod.mk.injEq, mul_ite, mul_one, mul_zero,
            ite_mul, zero_mul, ← ite_and, and_assoc, and_left_comm, and_comm,
            ← Finset.univ_product_univ, Finset.sum_product] using hsum
    _ = LinearMap.trace k V ((ρ s) * (ρ s)) := by
          rw [show A * A = LinearMap.toMatrix b b ((ρ s) * (ρ s)) by
            simp [A, LinearMap.toMatrix_mul]]
          rw [← LinearMap.trace_eq_matrix_trace k b]
    _ = ρ.character (s ^ 2) := by
          simp [Representation.character, pow_two, map_mul]

end

/-- Helper for Proposition 2-2.1-3: pointwise, the symmetric- and alternating-square characters
sum to the square of the original character. -/
lemma char_symmetricSquare_add_char_alternatingSquare_apply (s : G) :
    (Sym² ρ).character s + (Alt² ρ).character s = ρ.character s ^ 2 := by
  -- The tensor-square representation decomposes canonically as the product of the symmetric and
  -- alternating squares, so its character is the sum of the two summand characters.
  simpa [pow_two] using congrFun
    (((char_prod (Sym² ρ) (Alt² ρ)).symm.trans <|
      (char_iso (ρ.symmetricAlternatingSquareEquivTensor)).trans (char_tensor ρ ρ))) s

/-- Proposition 2-2.1-3 (1): over a field where `2` is invertible, the character of the symmetric
square at `s` is half the sum of `χ(s)^2` and `χ(s^2)`. -/
theorem char_symmetricSquare (s : G) :
    (Sym² ρ).character s = (1 / 2 : k) * (ρ.character s ^ 2 + ρ.character (s ^ 2)) := by
  have hsum :
      (Sym² ρ).character s + (Alt² ρ).character s = ρ.character s ^ 2 := by
    exact ρ.char_symmetricSquare_add_char_alternatingSquare_apply s
  have hdiff :
      (Sym² ρ).character s - (Alt² ρ).character s = ρ.character (s ^ 2) := by
    rw [ρ.char_symmetricSquare_sub_char_alternatingSquare, ρ.trace_tprod_apply_comp_tensorSwap_eq_char_sq]
  -- Solve the two linear equations given by the sum and difference identities.
  calc
    (Sym² ρ).character s
      = (1 / 2 : k) *
          ((Sym² ρ).character s + (Alt² ρ).character s +
            ((Sym² ρ).character s - (Alt² ρ).character s)) := by
          field_simp [two_ne_zero]
          ring
    _ = (1 / 2 : k) * (ρ.character s ^ 2 + ρ.character (s ^ 2)) := by
          rw [hsum, hdiff]

-- Proof sketch: as for the symmetric square, compute over a splitting field and descend the
-- resulting identity for the alternating square character.
/-- Proposition 2-2.1-3 (2): the character of the alternating square at `s` is half the difference
between `χ(s)^2` and `χ(s^2)` when `2` is invertible in the coefficient field. -/
theorem char_alternatingSquare (s : G) :
    (Alt² ρ).character s = (1 / 2 : k) * (ρ.character s ^ 2 - ρ.character (s ^ 2)) := by
  have hsum :
      (Sym² ρ).character s + (Alt² ρ).character s = ρ.character s ^ 2 := by
    exact ρ.char_symmetricSquare_add_char_alternatingSquare_apply s
  have hdiff :
      (Sym² ρ).character s - (Alt² ρ).character s = ρ.character (s ^ 2) := by
    rw [ρ.char_symmetricSquare_sub_char_alternatingSquare, ρ.trace_tprod_apply_comp_tensorSwap_eq_char_sq]
  -- Subtract the difference identity from the sum identity to isolate the alternating part.
  calc
    (Alt² ρ).character s
      = (1 / 2 : k) *
          ((Sym² ρ).character s + (Alt² ρ).character s -
            ((Sym² ρ).character s - (Alt² ρ).character s)) := by
          field_simp [two_ne_zero]
          ring
    _ = (1 / 2 : k) * (ρ.character s ^ 2 - ρ.character (s ^ 2)) := by
          rw [hsum, hdiff]

-- Proof sketch: apply the two preceding formulas pointwise and simplify the half-sum plus the
-- half-difference; more canonically, use the chapter-1 decomposition
-- `(Sym² ρ).prod (Alt² ρ) ≃ ρ.tprod ρ` and then apply `char_iso`, `char_prod`, and `char_tensor`.
/-- Proposition 2-2.1-3 (3): the sum of the symmetric- and alternating-square characters is the
square of the character of `ρ`. -/
theorem char_symmetricSquare_add_char_alternatingSquare :
    (Sym² ρ).character + (Alt² ρ).character = ρ.character ^ 2 := by
  -- Repackage the pointwise sum identity as an equality of class functions.
  ext s
  exact ρ.char_symmetricSquare_add_char_alternatingSquare_apply s

end Representation

end
