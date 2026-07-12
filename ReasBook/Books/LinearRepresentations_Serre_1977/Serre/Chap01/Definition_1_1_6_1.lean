import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Representation

noncomputable section

section SymmetricAlternatingSquare

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/- Definition 1-1.6-1: the tensor-factor swap `θ` on `V ⊗[k] V` is the canonical intertwining
equivalence `Representation.TensorProduct.comm ρ ρ`; its `+1`- and `-1`-eigenspaces are the
symmetric and alternating squares of `ρ`. The source's complex case is the specialization
`k = ℂ`. -/
recall Representation.TensorProduct.comm

/-- The tensor-factor swap, viewed as an endomorphism so that its eigenspaces can be taken. -/
abbrev tensorSwap : Module.End k (V ⊗[k] V) :=
  (Representation.TensorProduct.comm ρ ρ).toLinearMap

/-- Helper for Definition 1-1.6-1: the tensor swap intertwines the tensor-square action. -/
theorem tensorSwap_commutes_tprod_apply (g : G) (z : V ⊗[k] V) :
    ρ.tensorSwap ((ρ.tprod ρ) g z) = (ρ.tprod ρ) g (ρ.tensorSwap z) := by
  -- The canonical commutor is itself an intertwining map for `ρ.tprod ρ`.
  have h := (Representation.TensorProduct.comm ρ ρ).isIntertwining' g
  simpa [tensorSwap] using congrArg (fun f : V ⊗[k] V →ₗ[k] V ⊗[k] V => f z) h

/-- Helper for Definition 1-1.6-1: swapping tensor factors twice is the identity. -/
theorem tensorSwap_involutive (z : V ⊗[k] V) :
    ρ.tensorSwap (ρ.tensorSwap z) = z := by
  -- The tensor commutor is an involution on the tensor square.
  have h := congrArg (fun f : V ⊗[k] V →ₗ[k] V ⊗[k] V => f z)
    (TensorProduct.comm_comp_comm k V V)
  simpa [tensorSwap, Representation.TensorProduct.toLinearMap_comm] using h

/-- The `+1`-eigenspace of the tensor swap is stable under the tensor-square action. -/
-- Proof sketch: `Representation.TensorProduct.comm ρ ρ` is an intertwiner, so its underlying
-- linear map commutes with every operator `(ρ.tprod ρ) g`; this preserves the `+1`-eigenspace.
private theorem symmetricSquareSubrepresentation_apply_mem (g : G) {z : V ⊗[k] V}
    (hz : z ∈ ρ.tensorSwap.eigenspace (1 : k)) :
    (ρ.tprod ρ) g z ∈ ρ.tensorSwap.eigenspace (1 : k) := by
  -- Rewrite the eigenspace condition as the fixed-point equation for the swap.
  rw [Module.End.mem_eigenspace_iff] at hz ⊢
  simp only [one_smul] at hz ⊢
  -- Commuting the swap past the action transports the fixed-point relation.
  rw [tensorSwap_commutes_tprod_apply]
  simpa using congrArg ((ρ.tprod ρ) g) hz

/-- The `-1`-eigenspace of the tensor swap is stable under the tensor-square action. -/
-- Proof sketch: as for the symmetric square, use that the tensor swap commutes with the
-- tensor-square action and therefore preserves the `-1`-eigenspace.
private theorem alternatingSquareSubrepresentation_apply_mem (g : G) {z : V ⊗[k] V}
    (hz : z ∈ ρ.tensorSwap.eigenspace (-1 : k)) :
    (ρ.tprod ρ) g z ∈ ρ.tensorSwap.eigenspace (-1 : k) := by
  -- Rewrite the eigenspace condition as the anti-fixed-point equation for the swap.
  rw [Module.End.mem_eigenspace_iff] at hz ⊢
  simp only [neg_one_smul] at hz ⊢
  -- The intertwining property carries the `-1`-eigenvector equation through the action.
  rw [tensorSwap_commutes_tprod_apply]
  simpa using congrArg ((ρ.tprod ρ) g) hz

/-- The symmetric square of `ρ` as a `G`-stable subspace of `V ⊗[k] V`. -/
def symmetricSquareSubrepresentation : Subrepresentation (ρ.tprod ρ) where
  toSubmodule := ρ.tensorSwap.eigenspace (1 : k)
  apply_mem_toSubmodule := symmetricSquareSubrepresentation_apply_mem ρ

/-- The alternating square of `ρ` as a `G`-stable subspace of `V ⊗[k] V`. -/
def alternatingSquareSubrepresentation : Subrepresentation (ρ.tprod ρ) where
  toSubmodule := ρ.tensorSwap.eigenspace (-1 : k)
  apply_mem_toSubmodule := alternatingSquareSubrepresentation_apply_mem ρ

instance : AddCommGroup ↥ρ.symmetricSquareSubrepresentation.toSubmodule := inferInstance

instance : AddCommGroup ↥ρ.alternatingSquareSubrepresentation.toSubmodule := inferInstance

/-- The symmetric square representation carried by the `+1`-eigenspace of the tensor swap. -/
abbrev symmetricSquare :
    Representation k G ρ.symmetricSquareSubrepresentation.toSubmodule :=
  ρ.symmetricSquareSubrepresentation.toRepresentation

/-- The alternating square representation carried by the `-1`-eigenspace of the tensor swap. -/
abbrev alternatingSquare :
    Representation k G ρ.alternatingSquareSubrepresentation.toSubmodule :=
  ρ.alternatingSquareSubrepresentation.toRepresentation

scoped[TensorProduct] notation3:max "Sym²ₛ " ρ:arg =>
  Representation.symmetricSquareSubrepresentation ρ

scoped[TensorProduct] notation3:max "Alt²ₛ " ρ:arg =>
  Representation.alternatingSquareSubrepresentation ρ

scoped[TensorProduct] notation3:max "Sym² " ρ:arg =>
  Representation.symmetricSquare ρ

scoped[TensorProduct] notation3:max "Alt² " ρ:arg =>
  Representation.alternatingSquare ρ

-- Proof sketch: membership in an eigenspace is exactly the eigenvector equation
-- `tensorSwap ρ z = 1 • z`, which simplifies to `tensorSwap ρ z = z`.
/-- A tensor lies in the symmetric square exactly when it is fixed by the tensor swap. -/
theorem mem_symmetricSquareSubrepresentation_iff {z : V ⊗[k] V} :
    z ∈ Sym²ₛ ρ ↔ ρ.tensorSwap z = z := by
  -- The symmetric square is defined as the `+1`-eigenspace of the swap.
  show z ∈ ρ.tensorSwap.eigenspace (1 : k) ↔ ρ.tensorSwap z = z
  rw [Module.End.mem_eigenspace_iff]
  simp

-- Proof sketch: membership in the `-1`-eigenspace is the eigenvector equation
-- `tensorSwap ρ z = (-1 : k) • z`, which is the same as `tensorSwap ρ z = -z`.
/-- A tensor lies in the alternating square exactly when the tensor swap acts by `-1`. -/
theorem mem_alternatingSquareSubrepresentation_iff {z : V ⊗[k] V} :
    z ∈ Alt²ₛ ρ ↔ ρ.tensorSwap z = -z := by
  -- The alternating square is the `-1`-eigenspace of the swap.
  show z ∈ ρ.tensorSwap.eigenspace (-1 : k) ↔ ρ.tensorSwap z = -z
  rw [Module.End.mem_eigenspace_iff]
  simp

-- Proof sketch: the representation on a subrepresentation is obtained by restricting the ambient
-- action, so coercing back to `V ⊗[k] V` recovers the tensor-square action.
/-- The symmetric square representation acts by restricting the tensor-square action. -/
theorem symmetricSquare_apply (g : G) (z : (Sym²ₛ ρ).toSubmodule) :
    (((Sym² ρ) g) z : V ⊗[k] V) = (ρ.tprod ρ) g z := by
  -- The restricted representation uses the ambient tensor-square action on the carrier.
  rfl

-- Proof sketch: as for the symmetric square, this is the restriction of the tensor-square action
-- to the alternating-square carrier.
/-- The alternating square representation acts by restricting the tensor-square action. -/
theorem alternatingSquare_apply (g : G) (z : (Alt²ₛ ρ).toSubmodule) :
    (((Alt² ρ) g) z : V ⊗[k] V) = (ρ.tprod ρ) g z := by
  -- The alternating-square action is the same ambient action restricted to the subspace.
  rfl

section Basis

variable {ι : Type*}
variable (b : Module.Basis ι k V)

/-- The symmetrized tensor attached to two basis vectors, viewed in the symmetric square. -/
-- Proof sketch: apply `mem_symmetricSquareSubrepresentation_iff` and use that the tensor swap
-- exchanges the two pure-tensor summands.
private theorem symmetrizedTensor_mem (i j : ι) :
    (b i ⊗ₜ[k] b j) + (b j ⊗ₜ[k] b i) ∈ Sym²ₛ ρ := by
  -- The tensor swap simply exchanges the two pure tensors in the sum.
  rw [mem_symmetricSquareSubrepresentation_iff]
  simp [tensorSwap, add_comm]

/-- The symmetrized pure tensor attached to two basis vectors. -/
def symmetrizedTensor (i j : ι) : (Sym²ₛ ρ).toSubmodule :=
  ⟨(b i ⊗ₜ[k] b j) + (b j ⊗ₜ[k] b i), symmetrizedTensor_mem ρ b i j⟩

/-- The antisymmetrized pure tensor attached to two basis vectors, viewed inside the alternating
square. -/
-- Proof sketch: apply `mem_alternatingSquareSubrepresentation_iff` and compute the action of the
-- tensor swap on the difference of the two pure tensors.
private theorem alternatingTensor_mem (i j : ι) :
    (b i ⊗ₜ[k] b j) - (b j ⊗ₜ[k] b i) ∈ Alt²ₛ ρ := by
  -- Swapping the factors reverses the ordered difference.
  rw [mem_alternatingSquareSubrepresentation_iff]
  simp [tensorSwap, sub_eq_add_neg, add_comm]

/-- The antisymmetrized pure tensor attached to two basis vectors. -/
def alternatingTensor (i j : ι) : (Alt²ₛ ρ).toSubmodule :=
  ⟨(b i ⊗ₜ[k] b j) - (b j ⊗ₜ[k] b i), alternatingTensor_mem ρ b i j⟩

end Basis

end SymmetricAlternatingSquare

section TwoInvertibleSymmetricAlternatingSquare

variable {k : Type u} [CommRing k] [Invertible (2 : k)]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- Helper for Definition 1-1.6-1: the symmetrization projector onto the fixed-point space of the
tensor swap. -/
abbrev symmetrization : Module.End k (V ⊗[k] V) :=
  ⅟(2 : k) • (LinearMap.id + ρ.tensorSwap)

/-- Helper for Definition 1-1.6-1: a tensor is fixed by symmetrization exactly when it is fixed by
the tensor swap. -/
theorem symmetrization_apply_eq_self_iff {z : V ⊗[k] V} :
    ρ.symmetrization z = z ↔ ρ.tensorSwap z = z := by
  constructor
  · intro hz
    -- Rewrite the symmetrization equation before cancelling the scalar `1 / 2`.
    have hz' : ⅟(2 : k) • (z + ρ.tensorSwap z) = z := by
      simpa only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
        using hz
    have hz'' : z + ρ.tensorSwap z = (2 : k) • z := (invOf_smul_eq_iff).mp hz'
    have hz''' : z + ρ.tensorSwap z = z + z := by
      simpa [two_smul] using hz''
    exact add_left_cancel hz'''
  · intro hz
    -- A tensor fixed by the swap is unchanged by averaging it with its swap.
    calc
      ρ.symmetrization z = ⅟(2 : k) • (z + ρ.tensorSwap z) := by
        simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
      _ = ⅟(2 : k) • (z + z) := by rw [hz]
      _ = ⅟(2 : k) • z + ⅟(2 : k) • z := by rw [smul_add]
      _ = (⅟(2 : k) + ⅟(2 : k)) • z := by rw [← add_smul]
      _ = z := by simp [invOf_two_add_invOf_two]

/-- Helper for Definition 1-1.6-1: symmetrization vanishes exactly on tensors anti-fixed by the
tensor swap. -/
theorem symmetrization_apply_eq_zero_iff {z : V ⊗[k] V} :
    ρ.symmetrization z = 0 ↔ ρ.tensorSwap z = -z := by
  constructor
  · intro hz
    -- Rewrite the equation in a form where the invertible scalar can be cancelled.
    have hz' : ⅟(2 : k) • (z + ρ.tensorSwap z) = 0 := by
      simpa only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
        using hz
    have hz'' : z + ρ.tensorSwap z = 0 := by
      simpa using (invOf_smul_eq_iff).mp hz'
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hz'')
  · intro hz
    -- The average of a tensor and its negative swap is zero.
    calc
      ρ.symmetrization z = ⅟(2 : k) • (z + ρ.tensorSwap z) := by
        simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
      _ = ⅟(2 : k) • (z + -z) := by rw [hz]
      _ = 0 := by simp

/-- Helper for Definition 1-1.6-1: the symmetrization map is an idempotent projector. -/
theorem symmetrization_isIdempotentElem :
    IsIdempotentElem (ρ.symmetrization) := by
  -- Route correction: use that symmetrization already lands in the swap-fixed subspace.
  change ρ.symmetrization * ρ.symmetrization = ρ.symmetrization
  refine LinearMap.ext fun z ↦ ?_
  have hz : ρ.tensorSwap (ρ.symmetrization z) = ρ.symmetrization z := by
    -- Applying the swap to an averaged tensor just reverses the two summands.
    simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      map_add, map_smul, tensorSwap_involutive]
    rw [add_comm]
  -- A second symmetrization acts trivially because the first output is already fixed.
  calc
    ρ.symmetrization (ρ.symmetrization z)
        = ⅟(2 : k) • (ρ.symmetrization z + ρ.tensorSwap (ρ.symmetrization z)) := by
            simp only [symmetrization, LinearMap.smul_apply, LinearMap.add_apply,
              LinearMap.id_apply]
    _ = ⅟(2 : k) • (ρ.symmetrization z + ρ.symmetrization z) := by rw [hz]
    _ = ⅟(2 : k) • ρ.symmetrization z + ⅟(2 : k) • ρ.symmetrization z := by rw [smul_add]
    _ = (⅟(2 : k) + ⅟(2 : k)) • ρ.symmetrization z := by rw [← add_smul]
    _ = ρ.symmetrization z := by simp [invOf_two_add_invOf_two]

/-- Helper for Definition 1-1.6-1: the range of symmetrization is the symmetric square. -/
theorem symmetrization_range_eq_symmetricSquare :
    LinearMap.range (ρ.symmetrization) = (Sym²ₛ ρ).toSubmodule := by
  -- The range of an idempotent consists exactly of its fixed points.
  ext z
  rw [LinearMap.IsIdempotentElem.mem_range_iff (ρ.symmetrization_isIdempotentElem)]
  show ρ.symmetrization z = z ↔ z ∈ Sym²ₛ ρ
  exact (ρ.symmetrization_apply_eq_self_iff).trans
    (ρ.mem_symmetricSquareSubrepresentation_iff).symm

/-- Helper for Definition 1-1.6-1: the kernel of symmetrization is the alternating square. -/
theorem symmetrization_ker_eq_alternatingSquare :
    LinearMap.ker (ρ.symmetrization) = (Alt²ₛ ρ).toSubmodule := by
  -- The kernel consists exactly of tensors on which the swap acts by `-1`.
  ext z
  rw [LinearMap.mem_ker]
  show ρ.symmetrization z = 0 ↔ z ∈ Alt²ₛ ρ
  exact (ρ.symmetrization_apply_eq_zero_iff).trans
    (ρ.mem_alternatingSquareSubrepresentation_iff).symm

-- Proof sketch: the involution `tensorSwap ρ` has eigenvalues `1` and `-1`, and when `2` is
-- invertible the ambient tensor square splits as the direct sum of these eigenspaces.
/-- If `2` is invertible in `k`, the tensor square decomposes as the direct sum of the symmetric
and alternating squares. -/
theorem isCompl_symmetricSquare_alternatingSquare :
    IsCompl (Sym²ₛ ρ).toSubmodule (Alt²ₛ ρ).toSubmodule := by
  -- The projector `1 / 2 • (id + θ)` splits the tensor square into its range and kernel.
  rw [← ρ.symmetrization_range_eq_symmetricSquare, ← ρ.symmetrization_ker_eq_alternatingSquare]
  exact LinearMap.IsIdempotentElem.isCompl (ρ.symmetrization_isIdempotentElem)

-- Proof sketch: the underlying linear equivalence is the canonical direct-sum decomposition of a
-- pair of complementary submodules, and the two restricted actions agree with the ambient
-- tensor-square action on each summand.
private theorem symmetricAlternatingSquareEquivTensor_aux (g : G) :
    ((Sym²ₛ ρ).toSubmodule.prodEquivOfIsCompl (Alt²ₛ ρ).toSubmodule
      (ρ.isCompl_symmetricSquare_alternatingSquare)).toLinearMap ∘ₗ
        (((Sym² ρ).prod (Alt² ρ)) g) =
      (ρ.tprod ρ) g ∘ₗ
        ((Sym²ₛ ρ).toSubmodule.prodEquivOfIsCompl (Alt²ₛ ρ).toSubmodule
          (ρ.isCompl_symmetricSquare_alternatingSquare)).toLinearMap := by
  ext z <;> simp [symmetricSquare_apply, alternatingSquare_apply]

/-- If `2` is invertible in `k`, the direct product of the symmetric and alternating squares is
equivariantly isomorphic to the tensor square. This is the canonical bridge/view from the
source-facing decomposition to the tensor-square owner. -/
def symmetricAlternatingSquareEquivTensor :
    ((Sym² ρ).prod (Alt² ρ)).Equiv (ρ.tprod ρ) :=
  .mk
    ((Sym²ₛ ρ).toSubmodule.prodEquivOfIsCompl (Alt²ₛ ρ).toSubmodule
      (ρ.isCompl_symmetricSquare_alternatingSquare))
    (ρ.symmetricAlternatingSquareEquivTensor_aux)

end TwoInvertibleSymmetricAlternatingSquare

end

end Representation
