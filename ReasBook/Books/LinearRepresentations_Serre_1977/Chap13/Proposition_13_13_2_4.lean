import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_3
import LinearRepresentations_Serre_1977.Chap13.Proposition_13_13_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BigOperators Representation TensorProduct

noncomputable section

universe u v

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: the Frobenius-Schur indicator attached to a complex character.
-- * core/canonical: the class-function owners `⟪-, -⟫` and `Ψ^n`.
-- * bridge/view: specialization to the character `ρ.character` of a complex representation.
--
-- Primitive data: a complex-valued function `χ : G → ℂ`.
-- Derived API: representation-level reformulations obtained by evaluating this owner at
-- `ρ.character`.
/-- The Frobenius-Schur indicator of a complex-valued function on a finite group, defined as the
pairing of the unit character with `Ψ²(χ)`. For characters, this is the usual indicator. -/
def frobeniusSchurIndicator (χ : G → ℂ) : ℂ :=
  ⟪1, Ψ^2(χ)⟫

-- Proof sketch: unfold `frobeniusSchurIndicator`, `Ψ^2`, and the canonical pairing
-- `groupFunctionPairingOverField`; then
-- simplify the factor `(1 : G → ℂ) t⁻¹ = 1`.
/-- The Frobenius-Schur indicator is the average of the values `χ(s²)` over the group. -/
theorem frobeniusSchurIndicator_eq_card_inv_sum_sq
    (χ : G → ℂ) :
    frobeniusSchurIndicator χ = (Nat.card G : ℂ)⁻¹ * ∑ s : G, χ (s ^ 2) := by
  simp [frobeniusSchurIndicator, groupFunctionPairingOverField, adamsOperator, Nat.card_eq_fintype_card]

end

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

local instance : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 13-13.2-4: the Frobenius-Schur indicator is the difference between the
trivial multiplicities in the symmetric and alternating squares. -/
private theorem frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] :
    frobeniusSchurIndicator ρ.character =
      ⟪1, (Sym² ρ).character⟫ - ⟪1, (Alt² ρ).character⟫ := by
  -- Apply the character identity pointwise, then pair with the trivial character.
  rw [frobeniusSchurIndicator]
  have hfun : Ψ^2(ρ.character) = (Sym² ρ).character - (Alt² ρ).character := by
    ext s
    have hsymm := _root_.Representation.char_symmetricSquare (ρ := ρ) s
    have halt := _root_.Representation.char_alternatingSquare (ρ := ρ) s
    change ρ.character (s ^ 2) = (Sym² ρ).character s - (Alt² ρ).character s
    rw [hsymm, halt]
    ring
  rw [hfun, sub_eq_add_neg, groupFunctionPairing_add_right]
  have hneg : -((Alt² ρ).character) = (-1 : ℂ) • (Alt² ρ).character := by
    ext s
    simp
  rw [hneg, groupFunctionPairing_smul_right]
  ring

/-- Helper for Proposition 13-13.2-4: the tensor-square functional attached to an invariant
bilinear form is itself `G`-invariant. -/
private theorem tensor_square_linearForm_is_intertwining
    (ρ : Representation ℂ G V)
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ) :
    ∀ g : G,
      TensorProduct.lift B ∘ₗ (ρ.tprod ρ) g = TensorProduct.lift B := by
  intro g
  -- Check invariance on pure tensors; tensor-product extensionality closes the linear-map equality.
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  exact (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB g x y

/-- Helper for Proposition 13-13.2-4: a nonzero invariant symmetric bilinear form produces a
nonzero intertwiner from the symmetric square to the trivial representation. -/
private theorem symmetricSquare_has_nonzero_trivial_intertwiner_of_nonzero_invariant_symmetric_bilinForm
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ) (hBsymm : B.IsSymm) (hB0 : B ≠ 0) :
    ∃ f : (Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ), f ≠ 0 := by
  let fLin : (Sym²ₛ ρ).toSubmodule →ₗ[ℂ] ℂ :=
    (TensorProduct.lift B).comp (Sym²ₛ ρ).toSubmodule.subtype
  have hf : ∀ g : G, ∀ z : (Sym²ₛ ρ).toSubmodule,
      fLin (((Sym² ρ) g) z) = (Representation.trivial ℂ G ℂ) g (fLin z) := by
    intro g z
    -- Restrict the tensor-square invariant functional to the symmetric summand.
    change TensorProduct.lift B ((((Sym² ρ) g) z : (Sym²ₛ ρ).toSubmodule) : V ⊗[ℂ] V) = fLin z
    rw [ρ.symmetricSquare_apply]
    simpa [fLin, LinearMap.comp_apply] using congrArg (fun F : V ⊗[ℂ] V →ₗ[ℂ] ℂ => F z)
      (tensor_square_linearForm_is_intertwining ρ B hB g)
  let f : (Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ) :=
    fLin.intertwiningMap_of_isIntertwiningMap (Sym² ρ) (Representation.trivial ℂ G ℂ) hf
  refine ⟨f, ?_⟩
  intro hf0
  have hzero : ∀ z : (Sym²ₛ ρ).toSubmodule, f z = 0 := by
    intro z
    simpa using congrArg
      (fun F : (Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ) => F z) hf0
  have hxy : ∃ x y, B x y ≠ 0 := by
    by_contra hxy
    apply hB0
    ext x y
    by_contra hBxy
    exact hxy ⟨x, y, hBxy⟩
  obtain ⟨x, y, hxy⟩ := hxy
  let z : (Sym²ₛ ρ).toSubmodule := by
    refine ⟨x ⊗ₜ[ℂ] y + y ⊗ₜ[ℂ] x, ?_⟩
    -- The standard symmetrized pure tensor lies in the symmetric square.
    exact (ρ.mem_symmetricSquareSubrepresentation_iff
      (z := x ⊗ₜ[ℂ] y + y ⊗ₜ[ℂ] x)).2 <| by
        simp [Representation.tensorSwap, TensorProduct.comm_tmul, add_comm]
  have hz : f z = (2 : ℂ) * B x y := by
    -- On the chosen symmetrized tensor, symmetry doubles the nonzero value `B x y`.
    simp [f, fLin, z, TensorProduct.lift.tmul, hBsymm.eq x y, two_mul]
  have : (2 : ℂ) * B x y = 0 := by
    simpa [hz] using hzero z
  have hBxy : B x y = 0 := by
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  exact hxy hBxy

/-- Helper for Proposition 13-13.2-4: a nonzero invariant alternating bilinear form produces a
nonzero intertwiner from the alternating square to the trivial representation. -/
private theorem alternatingSquare_has_nonzero_trivial_intertwiner_of_nonzero_invariant_alternating_bilinForm
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (B : BilinForm ℂ V) (hB : B.IsInvariantUnder ρ) (hBalt : B.IsAlt) (hB0 : B ≠ 0) :
    ∃ f : (Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ), f ≠ 0 := by
  let fLin : (Alt²ₛ ρ).toSubmodule →ₗ[ℂ] ℂ :=
    (TensorProduct.lift B).comp (Alt²ₛ ρ).toSubmodule.subtype
  have hf : ∀ g : G, ∀ z : (Alt²ₛ ρ).toSubmodule,
      fLin (((Alt² ρ) g) z) = (Representation.trivial ℂ G ℂ) g (fLin z) := by
    intro g z
    -- Restrict the tensor-square invariant functional to the alternating summand.
    change TensorProduct.lift B ((((Alt² ρ) g) z : (Alt²ₛ ρ).toSubmodule) : V ⊗[ℂ] V) = fLin z
    rw [ρ.alternatingSquare_apply]
    simpa [fLin, LinearMap.comp_apply] using congrArg (fun F : V ⊗[ℂ] V →ₗ[ℂ] ℂ => F z)
      (tensor_square_linearForm_is_intertwining ρ B hB g)
  let f : (Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ) :=
    fLin.intertwiningMap_of_isIntertwiningMap (Alt² ρ) (Representation.trivial ℂ G ℂ) hf
  refine ⟨f, ?_⟩
  intro hf0
  have hzero : ∀ z : (Alt²ₛ ρ).toSubmodule, f z = 0 := by
    intro z
    simpa using congrArg
      (fun F : (Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ) => F z) hf0
  have hxy : ∃ x y, B x y ≠ 0 := by
    by_contra hxy
    apply hB0
    ext x y
    by_contra hBxy
    exact hxy ⟨x, y, hBxy⟩
  obtain ⟨x, y, hxy⟩ := hxy
  let z : (Alt²ₛ ρ).toSubmodule := by
    refine ⟨x ⊗ₜ[ℂ] y - y ⊗ₜ[ℂ] x, ?_⟩
    -- The standard antisymmetrized pure tensor lies in the alternating square.
    exact (ρ.mem_alternatingSquareSubrepresentation_iff
      (z := x ⊗ₜ[ℂ] y - y ⊗ₜ[ℂ] x)).2 <| by
        simp [Representation.tensorSwap, TensorProduct.comm_tmul, sub_eq_add_neg, add_comm]
  have hz : f z = (2 : ℂ) * B x y := by
    -- Alternation turns the antisymmetrized tensor into the same doubled value.
    simp [f, fLin, z, TensorProduct.lift.tmul, hBalt.neg_eq, sub_eq_add_neg, two_mul]
  have : (2 : ℂ) * B x y = 0 := by
    simpa [hz] using hzero z
  have hBxy : B x y = 0 := by
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  exact hxy hBxy

/-- Helper for Proposition 13-13.2-4: after transporting the tensor swap across the
sym\-metric/alternating decomposition, the symmetric projection is fixed. -/
private theorem symmetric_projection_comp_tensorSwap
    (ρ : Representation ℂ G V)
    (z : (Sym²ₛ ρ).toSubmodule × (Alt²ₛ ρ).toSubmodule) :
    (LinearMap.fst ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
        ((ρ.symmetricAlternatingSquareEquivTensor).symm
          (ρ.tensorSwap ((ρ.symmetricAlternatingSquareEquivTensor) z))) =
      (LinearMap.fst ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule)) z := by
  -- Apply the chapter-2 swap formula and then project to the symmetric summand.
  have h := congrArg
      (fun w : V ⊗[ℂ] V ↦
        (LinearMap.fst ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
          ((ρ.symmetricAlternatingSquareEquivTensor).symm w))
      (ρ.tensorSwap_apply_symmetricAlternatingSquareEquivTensor z)
  simpa [LinearMap.prodMap_apply] using h

/-- Helper for Proposition 13-13.2-4: after transporting the tensor swap across the
sym\-metric/alternating decomposition, the alternating projection changes sign. -/
private theorem alternating_projection_comp_tensorSwap
    (ρ : Representation ℂ G V)
    (z : (Sym²ₛ ρ).toSubmodule × (Alt²ₛ ρ).toSubmodule) :
    (LinearMap.snd ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
        ((ρ.symmetricAlternatingSquareEquivTensor).symm
          (ρ.tensorSwap ((ρ.symmetricAlternatingSquareEquivTensor) z))) =
      -(LinearMap.snd ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule)) z := by
  -- Apply the same swap formula and now project to the alternating summand.
  have h := congrArg
      (fun w : V ⊗[ℂ] V ↦
        (LinearMap.snd ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
          ((ρ.symmetricAlternatingSquareEquivTensor).symm w))
      (ρ.tensorSwap_apply_symmetricAlternatingSquareEquivTensor z)
  simpa [LinearMap.prodMap_apply] using h

/-- Helper for Proposition 13-13.2-4: a nonzero trivial intertwiner on the symmetric square yields
a nonzero invariant symmetric bilinear form on the original irreducible representation. -/
private theorem exists_nonzero_invariant_symmetric_bilinForm_of_symmetricSquare_has_nonzero_trivial_intertwiner
    (ρ : Representation ℂ G V)
    (f : (Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) (hf0 : f ≠ 0) :
    ∃ B : BilinForm ℂ V, B.IsInvariantUnder ρ ∧ B.IsSymm ∧ B ≠ 0 := by
  let fstMap : ((Sym² ρ).prod (Alt² ρ)).IntertwiningMap (Sym² ρ) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ((Sym² ρ).prod (Alt² ρ)) (Sym² ρ)
      (LinearMap.fst ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
      (fun g z ↦ rfl)
  let F : (ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ) :=
    f.comp (fstMap.comp (ρ.symmetricAlternatingSquareEquivTensor.symm.toIntertwiningMap))
  let B : BilinForm ℂ V := (TensorProduct.lift.equiv (.id ℂ) V V ℂ).symm F.toLinearMap
  refine ⟨B, ?_, ?_, ?_⟩
  · -- The tensor functional `F` is equivariant, so its curried bilinear form is invariant.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hF := LinearMap.congr_fun (F.2 g) (x ⊗ₜ[ℂ] y)
    simpa [B, TensorProduct.lift.equiv_symm_apply, Representation.tprod_apply] using hF
  · refine ⟨?_⟩
    intro x y
    let z : (Sym²ₛ ρ).toSubmodule × (Alt²ₛ ρ).toSubmodule :=
      (ρ.symmetricAlternatingSquareEquivTensor).symm (x ⊗ₜ[ℂ] y)
    -- The symmetric projection is unchanged by the tensor swap, so the induced form is symmetric.
    have hswap := symmetric_projection_comp_tensorSwap ρ z
    have hproj :
        (LinearMap.fst ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
            ((ρ.symmetricAlternatingSquareEquivTensor).symm (y ⊗ₜ[ℂ] x)) =
          (LinearMap.fst ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
            ((ρ.symmetricAlternatingSquareEquivTensor).symm (x ⊗ₜ[ℂ] y)) := by
      simpa [z, Representation.tensorSwap] using hswap
    have hvals := congrArg f hproj
    simpa [B, TensorProduct.lift.equiv_symm_apply, F, fstMap] using hvals.symm
  · intro hB0
    apply hf0
    ext z
    -- If the reconstructed bilinear form vanished, then the tensor functional would vanish too,
    -- and evaluating on the symmetric summand would force `f = 0`.
    have hF0 : F.toLinearMap = 0 := by
      have := congrArg (TensorProduct.lift.equiv (.id ℂ) V V ℂ) hB0
      simpa [B] using this
    have hz0 : F ((ρ.symmetricAlternatingSquareEquivTensor) (z, 0)) = 0 := by
      simpa using congrArg
        (fun L : V ⊗[ℂ] V →ₗ[ℂ] ℂ ↦ L ((ρ.symmetricAlternatingSquareEquivTensor) (z, 0))) hF0
    simpa [F, fstMap] using hz0

/-- Helper for Proposition 13-13.2-4: a nonzero trivial intertwiner on the alternating square
yields a nonzero invariant alternating bilinear form on the original irreducible representation. -/
private theorem exists_nonzero_invariant_alternating_bilinForm_of_alternatingSquare_has_nonzero_trivial_intertwiner
    (ρ : Representation ℂ G V)
    (f : (Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) (hf0 : f ≠ 0) :
    ∃ B : BilinForm ℂ V, B.IsInvariantUnder ρ ∧ B.IsAlt ∧ B ≠ 0 := by
  let sndMap : ((Sym² ρ).prod (Alt² ρ)).IntertwiningMap (Alt² ρ) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ((Sym² ρ).prod (Alt² ρ)) (Alt² ρ)
      (LinearMap.snd ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
      (fun g z ↦ rfl)
  let F : (ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ) :=
    f.comp (sndMap.comp (ρ.symmetricAlternatingSquareEquivTensor.symm.toIntertwiningMap))
  let B : BilinForm ℂ V := (TensorProduct.lift.equiv (.id ℂ) V V ℂ).symm F.toLinearMap
  refine ⟨B, ?_, ?_, ?_⟩
  · -- As in the symmetric case, equivariance of `F` gives invariance of the curried form.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro g x y
    have hF := LinearMap.congr_fun (F.2 g) (x ⊗ₜ[ℂ] y)
    simpa [B, TensorProduct.lift.equiv_symm_apply, Representation.tprod_apply] using hF
  · intro x
    let z : (Sym²ₛ ρ).toSubmodule × (Alt²ₛ ρ).toSubmodule :=
      (ρ.symmetricAlternatingSquareEquivTensor).symm (x ⊗ₜ[ℂ] x)
    -- The alternating projection changes sign under the tensor swap, so diagonal values vanish.
    have hswap := alternating_projection_comp_tensorSwap ρ z
    have hproj :
        (LinearMap.snd ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
            ((ρ.symmetricAlternatingSquareEquivTensor).symm (x ⊗ₜ[ℂ] x)) =
          -(LinearMap.snd ℂ ((Sym²ₛ ρ).toSubmodule) ((Alt²ₛ ρ).toSubmodule))
            ((ρ.symmetricAlternatingSquareEquivTensor).symm (x ⊗ₜ[ℂ] x)) := by
      simpa [z, Representation.tensorSwap] using hswap
    have hneg : B x x = -B x x := by
      simpa [B, TensorProduct.lift.equiv_symm_apply, F, sndMap] using congrArg f hproj
    have hsum : B x x + B x x = 0 := by
      calc
        B x x + B x x = -B x x + B x x := by rw [← hneg]
        _ = 0 := by abel
    have htwo : (2 : ℂ) * B x x = 0 := by
      simpa [two_mul] using hsum
    exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
  · intro hB0
    apply hf0
    ext z
    -- Vanishing of the reconstructed form would annihilate the tensor functional on the
    -- alternating summand, forcing the original intertwiner to be zero.
    have hF0 : F.toLinearMap = 0 := by
      have := congrArg (TensorProduct.lift.equiv (.id ℂ) V V ℂ) hB0
      simpa [B] using this
    have hz0 : F ((ρ.symmetricAlternatingSquareEquivTensor) (0, z)) = 0 := by
      simpa using congrArg
        (fun L : V ⊗[ℂ] V →ₗ[ℂ] ℂ ↦ L ((ρ.symmetricAlternatingSquareEquivTensor) (0, z))) hF0
    simpa [F, sndMap] using hz0

/-- Helper for Proposition 13-13.2-4: the trivial multiplicity in the symmetric square is nonzero
exactly when there exists a nonzero invariant symmetric bilinear form. -/
private theorem pairing_trivial_symmetricSquare_ne_zero_iff_exists_nonzero_invariant_symmetric_bilinForm
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ⟪1, (Sym² ρ).character⟫ ≠ 0 ↔
      ∃ B : BilinForm ℂ V, B.IsInvariantUnder ρ ∧ B.IsSymm ∧ B ≠ 0 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hpair :
      ⟪1, (Sym² ρ).character⟫ =
        Module.finrank ℂ ((Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) := by
    have htriv : (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
      ext g
      simp [Representation.character, Representation.trivial]
    calc
      ⟪1, (Sym² ρ).character⟫
        = ⟪(Sym² ρ).character, (Representation.trivial ℂ G ℂ).character⟫ := by
            rw [groupFunctionPairing_comm, htriv]
      _ = Module.finrank ℂ ((Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ (Sym² ρ) (Representation.trivial ℂ G ℂ)
  constructor
  · intro hne
    -- A nonzero pairing gives positive intertwining-space dimension, hence a nonzero intertwiner.
    have hdim_ne :
        Module.finrank ℂ ((Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) ≠ 0 := by
      intro hdim0
      apply hne
      simpa [hpair, hdim0]
    have hdim_pos :
        0 < Module.finrank ℂ ((Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
      Nat.pos_of_ne_zero hdim_ne
    obtain ⟨f, hf0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).1 hdim_pos
    exact
      exists_nonzero_invariant_symmetric_bilinForm_of_symmetricSquare_has_nonzero_trivial_intertwiner
        ρ f hf0
  · rintro ⟨B, hB, hBsymm, hB0⟩
    obtain ⟨f, hf0⟩ :=
      symmetricSquare_has_nonzero_trivial_intertwiner_of_nonzero_invariant_symmetric_bilinForm
        ρ B hB hBsymm hB0
    letI : Nontrivial ((Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
      ⟨⟨f, 0, hf0⟩⟩
    have hdim_ne :
        (Module.finrank ℂ ((Sym² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) : ℂ) ≠ 0 := by
      exact_mod_cast Module.finrank_pos.ne'
    simpa [hpair] using hdim_ne

/-- Helper for Proposition 13-13.2-4: the trivial multiplicity in the alternating square is
nonzero exactly when there exists a nonzero invariant alternating bilinear form. -/
private theorem pairing_trivial_alternatingSquare_ne_zero_iff_exists_nonzero_invariant_alternating_bilinForm
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ⟪1, (Alt² ρ).character⟫ ≠ 0 ↔
      ∃ B : BilinForm ℂ V, B.IsInvariantUnder ρ ∧ B.IsAlt ∧ B ≠ 0 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hpair :
      ⟪1, (Alt² ρ).character⟫ =
        Module.finrank ℂ ((Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) := by
    have htriv : (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
      ext g
      simp [Representation.character, Representation.trivial]
    calc
      ⟪1, (Alt² ρ).character⟫
        = ⟪(Alt² ρ).character, (Representation.trivial ℂ G ℂ).character⟫ := by
            rw [groupFunctionPairing_comm, htriv]
      _ = Module.finrank ℂ ((Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ (Alt² ρ) (Representation.trivial ℂ G ℂ)
  constructor
  · intro hne
    -- As above, nonzero pairing gives a nonzero intertwiner which reconstructs an alternating form.
    have hdim_ne :
        Module.finrank ℂ ((Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) ≠ 0 := by
      intro hdim0
      apply hne
      simpa [hpair, hdim0]
    have hdim_pos :
        0 < Module.finrank ℂ ((Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
      Nat.pos_of_ne_zero hdim_ne
    obtain ⟨f, hf0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).1 hdim_pos
    exact
      exists_nonzero_invariant_alternating_bilinForm_of_alternatingSquare_has_nonzero_trivial_intertwiner
        ρ f hf0
  · rintro ⟨B, hB, hBalt, hB0⟩
    obtain ⟨f, hf0⟩ :=
      alternatingSquare_has_nonzero_trivial_intertwiner_of_nonzero_invariant_alternating_bilinForm
        ρ B hB hBalt hB0
    letI : Nontrivial ((Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
      ⟨⟨f, 0, hf0⟩⟩
    have hdim_ne :
        (Module.finrank ℂ ((Alt² ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) : ℂ) ≠ 0 := by
      exact_mod_cast Module.finrank_pos.ne'
    simpa [hpair] using hdim_ne

/-- Helper for Proposition 13-13.2-4: an irreducible complex representation of a finite group is
nontrivial. -/
private theorem nontrivial_of_isIrreducible
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] : Nontrivial V := by
  -- An irreducible representation cannot have `⊥ = ⊤`, so its carrier is not subsingleton.
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext y
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim y 0)
  exact bot_ne_top hbot

/-- Helper for Proposition 13-13.2-4: intertwining maps from `ρ ⊗ ρ` to the trivial
representation are the same as intertwining maps from `ρ` to `ρᵛ`. -/
private theorem tensorSquare_trivial_intertwining_finrank_eq_dual_intertwining_finrank
    (ρ : Representation ℂ G V) :
    Module.finrank ℂ ((ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) =
      Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) := by
  let e :
      ((ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) ≃ₗ[ℂ]
        (ρ.IntertwiningMap ρ.dual) :=
    { toFun := fun F ↦
        let B : BilinForm ℂ V := (TensorProduct.lift.equiv (.id ℂ) V V ℂ).symm F.toLinearMap
        let hB : B.IsInvariantUnder ρ := by
          -- Curry the tensor-square intertwiner back to an invariant bilinear form.
          rw [LinearMap.BilinForm.isInvariantUnder_iff]
          intro g x y
          have hF := LinearMap.congr_fun (F.2 g) (x ⊗ₜ[ℂ] y)
          simpa [B, TensorProduct.lift.equiv_symm_apply, Representation.tprod_apply] using hF
        ⟨B, (Representation.isInvariantUnder_iff_dual_intertwining B ρ).1 hB⟩
      invFun := fun F ↦
        let B : BilinForm ℂ V := F
        let hB : B.IsInvariantUnder ρ :=
          (Representation.isInvariantUnder_iff_dual_intertwining B ρ).2 (fun g ↦ F.2 g)
        (TensorProduct.lift B).intertwiningMap_of_isIntertwiningMap
          (ρ.tprod ρ) (Representation.trivial ℂ G ℂ) fun g z ↦ by
            -- Conversely, an invariant bilinear form defines an invariant tensor functional.
            have hlin : TensorProduct.lift B ∘ₗ (ρ.tprod ρ) g = TensorProduct.lift B := by
              apply TensorProduct.ext'
              intro x y
              rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
                TensorProduct.lift.tmul, TensorProduct.lift.tmul]
              exact (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB g x y
            simpa using congrArg (fun L : V ⊗[ℂ] V →ₗ[ℂ] ℂ ↦ L z) hlin
      left_inv := by
        intro F
        ext z
        rfl
      right_inv := by
        intro F
        ext x y
        rfl
      map_add' := by
        intro F F'
        ext x y
        rfl
      map_smul' := by
        intro c F
        ext x y
        rfl }
  exact e.finrank_eq

/-- Helper for Proposition 13-13.2-4: in the real-valued irreducible case, the intertwining space
`Hom_G(ρ, ρᵛ)` is one-dimensional. -/
private theorem dual_intertwining_finrank_eq_one_of_hasRealValuedCharacter
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hreal : IsValuedInBaseField ℝ ρ.character) :
    Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) = 1 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI := nontrivial_of_isIrreducible (ρ := ρ)
  obtain ⟨B, hBnondeg, hB⟩ :=
    (hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm ρ).1 hreal
  let f0 : ρ.IntertwiningMap ρ.dual :=
    LinearMap.BilinForm.toDual_intertwiningMap_of_isInvariantUnder ρ B hB
  have hf0 : f0 ≠ 0 := by
    -- The chosen nondegenerate invariant form gives a nonzero generator.
    intro hf0
    apply hBnondeg.ne_zero
    ext x y
    have hfx : f0 x = 0 := by
      simpa using congrArg (fun T : ρ.IntertwiningMap ρ.dual ↦ T x) hf0
    exact congrArg (fun φ : Module.Dual ℂ V ↦ φ y) hfx
  rw [finrank_eq_one_iff_of_nonzero' f0 hf0]
  intro f
  by_cases hf : f = 0
  · refine ⟨0, by simp [hf]⟩
  · have hfInv : LinearMap.BilinForm.IsInvariantUnder (show BilinForm ℂ V from f) ρ :=
        (Representation.isInvariantUnder_iff_dual_intertwining (show BilinForm ℂ V from f) ρ).2
          (fun g ↦ f.2 g)
    have hfB0 : (show BilinForm ℂ V from f) ≠ 0 := by
      -- A nonzero intertwiner is a nonzero invariant bilinear form.
      intro h0
      apply hf
      ext x y
      exact congrArg (fun B' : BilinForm ℂ V ↦ B' x y) h0
    obtain ⟨c, hc⟩ :=
      LinearMap.BilinForm.exists_units_smul_eq_of_isInvariantUnder
        ρ B (show BilinForm ℂ V from f) hB hBnondeg.ne_zero hfInv hfB0
    refine ⟨(c : ℂ), ?_⟩
    -- Proposition 13-13.2-3 now upgrades uniqueness of invariant forms to spanning.
    ext x y
    simpa [f0, mul_comm] using (congrArg (fun B' : BilinForm ℂ V ↦ B' x y) hc).symm

/-- Helper for Proposition 13-13.2-4: in the non-real-valued irreducible case, the intertwining
space `Hom_G(ρ, ρᵛ)` vanishes. -/
private theorem dual_intertwining_finrank_eq_zero_of_not_hasRealValuedCharacter
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hnot : ¬ IsValuedInBaseField ℝ ρ.character) :
    Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) = 0 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI := nontrivial_of_isIrreducible (ρ := ρ)
  have hzero : ∀ f : ρ.IntertwiningMap ρ.dual, f = 0 := by
    intro f
    by_contra hf
    have hfInv : LinearMap.BilinForm.IsInvariantUnder (show BilinForm ℂ V from f) ρ :=
      (Representation.isInvariantUnder_iff_dual_intertwining (show BilinForm ℂ V from f) ρ).2
        (fun g ↦ f.2 g)
    have hfB0 : (show BilinForm ℂ V from f) ≠ 0 := by
      -- Any nonzero dual intertwiner would force a nonzero invariant bilinear form.
      intro h0
      apply hf
      ext x y
      exact congrArg (fun B' : BilinForm ℂ V ↦ B' x y) h0
    have hreal : IsValuedInBaseField ℝ ρ.character :=
      (hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm ρ).2
        ⟨(show BilinForm ℂ V from f),
          LinearMap.BilinForm.nondegenerate_of_nonzero_isInvariantUnder
            ρ (show BilinForm ℂ V from f) hfInv hfB0,
          hfInv⟩
    exact hnot hreal
  letI : Subsingleton (ρ.IntertwiningMap ρ.dual) := ⟨fun f g ↦ by rw [hzero f, hzero g]⟩
  exact Module.finrank_zero_of_subsingleton

/-- Helper for Proposition 13-13.2-4: when the irreducible character is real-valued, the tensor
square contains the trivial representation with multiplicity `1`. -/
private theorem pairing_trivial_character_sq_eq_one_of_hasRealValuedCharacter
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hreal : IsValuedInBaseField ℝ ρ.character) :
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫ = 1 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  calc
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫
      = (Module.finrank ℂ
          ((ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) : ℂ) := by
            have htriv : (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
              ext g
              simp [Representation.character, Representation.trivial]
            calc
              ⟪(1 : G → ℂ), ρ.character ^ 2⟫
                = ⟪(1 : G → ℂ), (ρ.tprod ρ).character⟫ := by
                    rw [Representation.char_tensor, pow_two]
              _ = ⟪(ρ.tprod ρ).character, (Representation.trivial ℂ G ℂ).character⟫ := by
                    rw [groupFunctionPairing_comm, htriv]
              _ = (Module.finrank ℂ
                    ((ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) : ℂ) := by
                    exact_mod_cast
                      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                        ℂ (ρ.tprod ρ) (Representation.trivial ℂ G ℂ))
    _ = Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) := by
          exact_mod_cast tensorSquare_trivial_intertwining_finrank_eq_dual_intertwining_finrank ρ
    _ = 1 := by
          simp [dual_intertwining_finrank_eq_one_of_hasRealValuedCharacter, hreal]

/-- Helper for Proposition 13-13.2-4: when the irreducible character is not real-valued, the
tensor square contains no trivial summand. -/
private theorem pairing_trivial_character_sq_eq_zero_of_not_hasRealValuedCharacter
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hnot : ¬ IsValuedInBaseField ℝ ρ.character) :
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫ = 0 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  calc
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫
      = (Module.finrank ℂ
          ((ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) : ℂ) := by
            have htriv : (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
              ext g
              simp [Representation.character, Representation.trivial]
            calc
              ⟪(1 : G → ℂ), ρ.character ^ 2⟫
                = ⟪(1 : G → ℂ), (ρ.tprod ρ).character⟫ := by
                    rw [Representation.char_tensor, pow_two]
              _ = ⟪(ρ.tprod ρ).character, (Representation.trivial ℂ G ℂ).character⟫ := by
                    rw [groupFunctionPairing_comm, htriv]
              _ = (Module.finrank ℂ
                    ((ρ.tprod ρ).IntertwiningMap (Representation.trivial ℂ G ℂ)) : ℂ) := by
                    exact_mod_cast
                      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                        ℂ (ρ.tprod ρ) (Representation.trivial ℂ G ℂ))
    _ = Module.finrank ℂ (ρ.IntertwiningMap ρ.dual) := by
          exact_mod_cast tensorSquare_trivial_intertwining_finrank_eq_dual_intertwining_finrank ρ
    _ = 0 := by
          simp [dual_intertwining_finrank_eq_zero_of_not_hasRealValuedCharacter, hnot]

-- Finite-dimensionality is derived from irreducibility via
-- `IsIrreducible.finiteDimensional_of_finite ρ`, so it should not remain primitive public data in
-- these irreducible statements.

-- Proof sketch: write the Frobenius-Schur indicator as
-- `⟪1, χ_σ^2⟫ - ⟪1, χ_λ^2⟫` using the symmetric- and alternating-square character formulas from
-- Proposition `2-2.1-3`. Proposition `13-13.2-3` identifies type `1` with the absence of
-- invariant symmetric and alternating bilinear forms, so both multiplicities vanish exactly in
-- this case.
/-- Proposition 13-13.2-4 (1): an irreducible finite-dimensional complex representation is of
LinearRepresentations_Serre_1977 type `1` if and only if its Frobenius-Schur indicator vanishes. Finite-dimensionality is
automatic here. -/
theorem isTypeOne_iff_frobeniusSchurIndicator_eq_zero
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ¬ IsValuedInBaseField ℝ ρ.character ↔ frobeniusSchurIndicator ρ.character = 0 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  constructor
  · intro htype1
    have hno_symm :
        ¬ ∃ B : BilinForm ℂ V, B.IsInvariantUnder ρ ∧ B.IsSymm ∧ B ≠ 0 := by
      intro hsymm
      rcases hsymm with ⟨B, hB, hBsymm, hB0⟩
      have hreal : IsRealizableOver ℝ ρ :=
        isTypeTwo_of_nonzero_invariant_symmetric_bilinForm ρ B hB hBsymm hB0
      rcases
          (isRealizableOverReal_iff_exists_invariant_nondegenerate_symmetric_bilinForm ρ).1 hreal with
        ⟨B', hB'nondeg, _, hB'⟩
      exact htype1
        ((hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm ρ).2
          ⟨B', hB'nondeg, hB'⟩)
    have hno_alt :
        ¬ ∃ B : BilinForm ℂ V, B.IsInvariantUnder ρ ∧ B.IsAlt ∧ B ≠ 0 := by
      intro halt
      rcases halt with ⟨B, hB, hBalt, hB0⟩
      exact htype1 (isTypeThree_of_nonzero_invariant_alternating_bilinForm ρ B hB hBalt hB0).1
    -- Route correction: the new converse bridge lets us kill the two square multiplicities
    -- separately by ruling out the corresponding invariant forms.
    have hsymm_pair : ⟪1, (Sym² ρ).character⟫ = 0 := by
      by_contra hne
      exact hno_symm
        ((pairing_trivial_symmetricSquare_ne_zero_iff_exists_nonzero_invariant_symmetric_bilinForm
          ρ).1 hne)
    have halt_pair : ⟪1, (Alt² ρ).character⟫ = 0 := by
      by_contra hne
      exact hno_alt
        ((pairing_trivial_alternatingSquare_ne_zero_iff_exists_nonzero_invariant_alternating_bilinForm
          ρ).1 hne)
    simp [frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare,
      hsymm_pair, halt_pair]
  · intro hfs
    intro hreal
    letI : Nontrivial V := by
      by_contra hV
      letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        ext y
        constructor
        · intro _
          trivial
        · intro _
          simpa using (Subsingleton.elim y 0)
      exact bot_ne_top hbot
    rcases (hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm ρ).1 hreal with
      ⟨B, hBnondeg, hB⟩
    have hB0 : B ≠ 0 := hBnondeg.ne_zero
    rcases isSymm_or_isAlt_of_nonzero_isInvariantUnder ρ B hB hB0 with hBsymm | hBalt
    · have hsymm_pair : ⟪1, (Sym² ρ).character⟫ ≠ 0 := by
        exact
          (pairing_trivial_symmetricSquare_ne_zero_iff_exists_nonzero_invariant_symmetric_bilinForm
            ρ).2 ⟨B, hB, hBsymm, hB0⟩
      have halt_pair : ⟪1, (Alt² ρ).character⟫ ≠ 0 := by
        intro hzero
        have : frobeniusSchurIndicator ρ.character = ⟪1, (Sym² ρ).character⟫ := by
          rw [frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare,
            hzero, sub_zero]
        exact hsymm_pair (by simpa [hfs] using this.symm)
      rcases
          (pairing_trivial_alternatingSquare_ne_zero_iff_exists_nonzero_invariant_alternating_bilinForm
            ρ).1 halt_pair with
        ⟨B', hB', hB'alt, hB'0⟩
      obtain ⟨c, hc⟩ :=
        LinearMap.BilinForm.exists_units_smul_eq_of_isInvariantUnder ρ B B' hB hB0 hB' hB'0
      have hB'symm : B'.IsSymm := by
        rw [hc]
        exact hBsymm.smul (c : ℂ)
      exact hB'0 (LinearMap.BilinForm.eq_zero_of_isSymm_and_isAlt B' hB'symm hB'alt)
    · have halt_pair : ⟪1, (Alt² ρ).character⟫ ≠ 0 := by
        exact
          (pairing_trivial_alternatingSquare_ne_zero_iff_exists_nonzero_invariant_alternating_bilinForm
            ρ).2 ⟨B, hB, hBalt, hB0⟩
      have hsymm_pair : ⟪1, (Sym² ρ).character⟫ ≠ 0 := by
        intro hzero
        have : frobeniusSchurIndicator ρ.character = -⟪1, (Alt² ρ).character⟫ := by
          rw [frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare,
            hzero, zero_sub]
        have hneq : -⟪1, (Alt² ρ).character⟫ ≠ 0 := neg_ne_zero.mpr halt_pair
        exact hneq (by simpa [hfs] using this.symm)
      rcases
          (pairing_trivial_symmetricSquare_ne_zero_iff_exists_nonzero_invariant_symmetric_bilinForm
            ρ).1 hsymm_pair with
        ⟨B', hB', hB'symm, hB'0⟩
      obtain ⟨c, hc⟩ :=
        LinearMap.BilinForm.exists_units_smul_eq_of_isInvariantUnder ρ B B' hB hB0 hB' hB'0
      have hB'alt : B'.IsAlt := by
        rw [hc]
        exact hBalt.smul (c : ℂ)
      exact hB'0 (LinearMap.BilinForm.eq_zero_of_isSymm_and_isAlt B' hB'symm hB'alt)

-- Proof sketch: the same decomposition of the indicator as
-- `⟪1, χ_σ^2⟫ - ⟪1, χ_λ^2⟫` shows that it measures the difference between the multiplicities of the
-- trivial representation in the symmetric and alternating squares. Proposition `13-13.2-3`
-- identifies type `2` with the case where the symmetric square contains the trivial
-- representation once and the alternating square does not contain it.
/-- Proposition 13-13.2-4 (2): an irreducible finite-dimensional complex representation is of
LinearRepresentations_Serre_1977 type `2` if and only if its Frobenius-Schur indicator is `1`. Finite-dimensionality is
automatic here. -/
theorem isTypeTwo_iff_frobeniusSchurIndicator_eq_one
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    IsRealizableOver ℝ ρ ↔ frobeniusSchurIndicator ρ.character = 1 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  constructor
  · intro htype2
    rcases
        (isRealizableOverReal_iff_exists_invariant_nondegenerate_symmetric_bilinForm ρ).1 htype2
      with ⟨B, hBnondeg, hBsymm, hB⟩
    have hreal : IsValuedInBaseField ℝ ρ.character :=
      (hasRealValuedCharacter_iff_exists_invariant_nondegenerate_bilinForm ρ).2
        ⟨B, hBnondeg, hB⟩
    have hsum :
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫ = 1 := by
      -- Source proof: `χ_σ² + χ_λ² = χ²`, and the tensor square has trivial multiplicity `1`.
      calc
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫
          = ⟪1, ρ.character ^ 2⟫ := by
              rw [← groupFunctionPairing_add_right,
                ρ.char_symmetricSquare_add_char_alternatingSquare]
        _ = 1 := pairing_trivial_character_sq_eq_one_of_hasRealValuedCharacter ρ hreal
    have halt_pair : ⟪1, (Alt² ρ).character⟫ = 0 := by
      -- Route correction: exclude the alternating branch by Proposition 13-13.2-3,
      -- rather than trying to prove multiplicity one directly on `Alt² ρ`.
      by_contra hne
      rcases
          (pairing_trivial_alternatingSquare_ne_zero_iff_exists_nonzero_invariant_alternating_bilinForm
            ρ).1 hne with
        ⟨B', hB', hB'alt, hB'0⟩
      exact
        (isTypeThree_of_nonzero_invariant_alternating_bilinForm ρ B' hB' hB'alt hB'0).2 htype2
    have hsymm_pair : ⟪1, (Sym² ρ).character⟫ = 1 := by
      simpa [halt_pair] using hsum
    -- With multiplicities `(1, 0)`, the indicator is the required difference.
    rw [frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare,
      hsymm_pair, halt_pair]
    norm_num
  · intro hfs
    have hreal : IsValuedInBaseField ℝ ρ.character := by
      -- Nonzero indicator rules out type `1`, so the character is real-valued.
      by_contra hnot
      have hzero := (isTypeOne_iff_frobeniusSchurIndicator_eq_zero ρ).1 hnot
      simp [hfs] at hzero
    have hsum :
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫ = 1 := by
      calc
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫
          = ⟪1, ρ.character ^ 2⟫ := by
              rw [← groupFunctionPairing_add_right,
                ρ.char_symmetricSquare_add_char_alternatingSquare]
        _ = 1 := pairing_trivial_character_sq_eq_one_of_hasRealValuedCharacter ρ hreal
    have hdiff :
        ⟪1, (Sym² ρ).character⟫ - ⟪1, (Alt² ρ).character⟫ = 1 := by
      simpa [frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare]
        using hfs
    have halt_pair : ⟪1, (Alt² ρ).character⟫ = 0 := by
      -- Solving the source equations `x + y = 1` and `x - y = 1` forces `y = 0`.
      have htwo :
          (2 : ℂ) * ⟪1, (Alt² ρ).character⟫ = 0 := by
        calc
          (2 : ℂ) * ⟪1, (Alt² ρ).character⟫
            = ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫ -
                (⟪1, (Sym² ρ).character⟫ - ⟪1, (Alt² ρ).character⟫) := by ring
          _ = 1 - 1 := by rw [hsum, hdiff]
          _ = 0 := by ring
      exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
    have hsymm_pair : ⟪1, (Sym² ρ).character⟫ = 1 := by
      simpa [halt_pair] using hsum
    have hsymm_ne : ⟪1, (Sym² ρ).character⟫ ≠ 0 := by
      rw [hsymm_pair]
      norm_num
    rcases
        (pairing_trivial_symmetricSquare_ne_zero_iff_exists_nonzero_invariant_symmetric_bilinForm
          ρ).1 hsymm_ne with
      ⟨B, hB, hBsymm, hB0⟩
    -- The surviving symmetric summand yields the real model.
    exact isTypeTwo_of_nonzero_invariant_symmetric_bilinForm ρ B hB hBsymm hB0

-- Proof sketch: as above, the Frobenius-Schur indicator is the difference between the
-- multiplicities of the trivial representation in the symmetric and alternating squares.
-- Proposition `13-13.2-3` identifies type `3` with the case where the alternating square
-- contains the trivial representation once and the symmetric square does not.
/-- Proposition 13-13.2-4 (3): an irreducible finite-dimensional complex representation is of
LinearRepresentations_Serre_1977 type `3` if and only if its Frobenius-Schur indicator is `-1`. Finite-dimensionality is
automatic here. -/
theorem isTypeThree_iff_frobeniusSchurIndicator_eq_neg_one
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    IsValuedInBaseField ℝ ρ.character ∧ ¬ IsRealizableOver ℝ ρ ↔
      frobeniusSchurIndicator ρ.character = -1 := by
  letI := IsIrreducible.finiteDimensional_of_finite ρ
  constructor
  · rintro ⟨hreal, hnotrealizable⟩
    have hsum :
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫ = 1 := by
      -- The tensor-square multiplicity is still `1` in every real-valued irreducible case.
      calc
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫
          = ⟪1, ρ.character ^ 2⟫ := by
              rw [← groupFunctionPairing_add_right,
                ρ.char_symmetricSquare_add_char_alternatingSquare]
        _ = 1 := pairing_trivial_character_sq_eq_one_of_hasRealValuedCharacter ρ hreal
    have hsymm_pair : ⟪1, (Sym² ρ).character⟫ = 0 := by
      -- Route correction: now the symmetric branch is the one excluded by Proposition 13-13.2-3.
      by_contra hne
      rcases
          (pairing_trivial_symmetricSquare_ne_zero_iff_exists_nonzero_invariant_symmetric_bilinForm
            ρ).1 hne with
        ⟨B, hB, hBsymm, hB0⟩
      exact hnotrealizable (isTypeTwo_of_nonzero_invariant_symmetric_bilinForm ρ B hB hBsymm hB0)
    have halt_pair : ⟪1, (Alt² ρ).character⟫ = 1 := by
      simpa [hsymm_pair] using hsum
    -- The multiplicities `(0, 1)` give indicator `-1`.
    rw [frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare,
      hsymm_pair, halt_pair]
    norm_num
  · intro hfs
    have hreal : IsValuedInBaseField ℝ ρ.character := by
      -- An indicator of `-1` is again incompatible with type `1`.
      by_contra hnot
      have hzero := (isTypeOne_iff_frobeniusSchurIndicator_eq_zero ρ).1 hnot
      simp [hfs] at hzero
    have hsum :
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫ = 1 := by
      calc
        ⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫
          = ⟪1, ρ.character ^ 2⟫ := by
              rw [← groupFunctionPairing_add_right,
                ρ.char_symmetricSquare_add_char_alternatingSquare]
        _ = 1 := pairing_trivial_character_sq_eq_one_of_hasRealValuedCharacter ρ hreal
    have hdiff :
        ⟪1, (Sym² ρ).character⟫ - ⟪1, (Alt² ρ).character⟫ = -1 := by
      simpa [frobeniusSchurIndicator_eq_pairing_symmetricSquare_sub_pairing_alternatingSquare]
        using hfs
    have hsymm_pair : ⟪1, (Sym² ρ).character⟫ = 0 := by
      -- Solving `x + y = 1` and `x - y = -1` forces `x = 0`.
      have htwo :
          (2 : ℂ) * ⟪1, (Sym² ρ).character⟫ = 0 := by
        calc
          (2 : ℂ) * ⟪1, (Sym² ρ).character⟫
            = (⟪1, (Sym² ρ).character⟫ + ⟪1, (Alt² ρ).character⟫) +
                (⟪1, (Sym² ρ).character⟫ - ⟪1, (Alt² ρ).character⟫) := by ring
          _ = 1 + (-1) := by rw [hsum, hdiff]
          _ = 0 := by ring
      exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
    have halt_pair : ⟪1, (Alt² ρ).character⟫ = 1 := by
      simpa [hsymm_pair] using hsum
    have halt_ne : ⟪1, (Alt² ρ).character⟫ ≠ 0 := by
      rw [halt_pair]
      norm_num
    rcases
        (pairing_trivial_alternatingSquare_ne_zero_iff_exists_nonzero_invariant_alternating_bilinForm
          ρ).1 halt_ne with
      ⟨B, hB, hBalt, hB0⟩
    -- The surviving alternating summand is exactly LinearRepresentations_Serre_1977 type `3`.
    exact isTypeThree_of_nonzero_invariant_alternating_bilinForm ρ B hB hBalt hB0

end

end Representation
