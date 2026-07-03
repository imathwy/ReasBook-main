import Mathlib
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_2_2_1_4 (from Chap02) -/
open scoped TensorProduct

noncomputable section

universe u v w w'

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {W : Type w'} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

/- Source/core/bridge triage:
- `source-facing`: the two exercise character identities below;
- `core/canonical`: `Representation.character` together with `Representation.char_prod` and
  `Representation.char_tensor`;
- `bridge/view`: the symmetric and alternating square owners `Sym²` and `Alt²` from
  Definition 1-1.6-1, together with the tensor-product distributivity equivalences
  `TensorProduct.prodLeft`, `TensorProduct.prodRight`, and the swap equivalence
  `Representation.TensorProduct.comm`.

Primitive data is already owned by the Chapter 1 `Sym²`/`Alt²` layer. This file adds only the
derived character formulas, reusing the Chapter 2 recall layer for `char_prod` and
`char_tensor`, so there is no parallel local wrapper or carrier API to keep. -/

/-- Helper for Exercise 2-2.1-4: the tensor square of `V × W` rearranges equivariantly into the
`VV`, `VW`, `WV`, and `WW` blocks, with the `WV` block transported to `VW` via tensor-factor
commutation. -/
def tensorSquareProdRearrangedLinearEquiv :
    ((V × W) ⊗[k] (V × W)) ≃ₗ[k]
      (V ⊗[k] V) × (((V ⊗[k] W) × (V ⊗[k] W)) × (W ⊗[k] W)) :=
  (TensorProduct.prodLeft k k V W (V × W)).trans <|
    (LinearEquiv.prodCongr
        (TensorProduct.prodRight k k V V W)
        (TensorProduct.prodRight k k W V W)).trans <|
      (LinearEquiv.prodAssoc k (V ⊗[k] V) (V ⊗[k] W) ((W ⊗[k] V) × (W ⊗[k] W))).trans <|
        (LinearEquiv.prodCongr (LinearEquiv.refl k (V ⊗[k] V)) <|
            LinearEquiv.prodCongr (LinearEquiv.refl k (V ⊗[k] W)) <|
              LinearEquiv.prodCongr (Representation.TensorProduct.comm σ ρ).toLinearEquiv
                (LinearEquiv.refl k (W ⊗[k] W))).trans <|
          LinearEquiv.prodCongr (LinearEquiv.refl k (V ⊗[k] V)) <|
            (LinearEquiv.prodAssoc k (V ⊗[k] W) (V ⊗[k] W) (W ⊗[k] W)).symm

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- Helper for Exercise 2-2.1-4: on a pure tensor, the rearranged four-block equivalence records
the `VV`, `VW`, `WV`, and `WW` contributions in the expected order. -/
lemma tensorSquareProdRearrangedLinearEquiv_apply_tmul (v₁ v₂ : V) (w₁ w₂ : W) :
    tensorSquareProdRearrangedLinearEquiv (ρ := ρ) (σ := σ)
      (((v₁, w₁) : V × W) ⊗ₜ[k] ((v₂, w₂) : V × W)) =
        (v₁ ⊗ₜ[k] v₂, ((v₁ ⊗ₜ[k] w₂, v₂ ⊗ₜ[k] w₁), w₁ ⊗ₜ[k] w₂)) := by
  -- Unfold the canonical product/tensor distributivity equivalences and read off each block.
  simp [tensorSquareProdRearrangedLinearEquiv]
  rfl

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- Helper for Exercise 2-2.1-4: the four-block linear equivalence intertwines the tensor-square
action of `ρ.prod σ` with the product action on the rearranged `VV`, `VW`, `WV`, and `WW` blocks.
-/
lemma tensorSquareProdRearrangedLinearEquiv_intertwines (g : G) :
    ↑(tensorSquareProdRearrangedLinearEquiv (ρ := ρ) (σ := σ)) ∘ₗ
        (((ρ.prod σ).tprod (ρ.prod σ)) g) =
      (((ρ.tprod ρ).prod (((ρ.tprod σ).prod (ρ.tprod σ)).prod (σ.tprod σ))) g) ∘ₗ
        ↑(tensorSquareProdRearrangedLinearEquiv (ρ := ρ) (σ := σ)) := by
  -- Both sides are linear in the ambient tensor-square variable, so it is enough to check a pure
  -- tensor and then evaluate each block using the tensor-product action formula.
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · rfl
  · intro x y
    rcases x with ⟨v, w⟩
    rcases y with ⟨v', w'⟩
    simp [tensorSquareProdRearrangedLinearEquiv_apply_tmul, Representation.tprod_apply]
  · intro x y hx hy
    simpa using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Exercise 2-2.1-4: the tensor square of a direct product representation is
equivariantly isomorphic to the four-block product representation. -/
def tensorSquareProdRearrangedEquiv :
    ((ρ.prod σ).tprod (ρ.prod σ)).Equiv
      ((ρ.tprod ρ).prod (((ρ.tprod σ).prod (ρ.tprod σ)).prod (σ.tprod σ))) :=
  Representation.Equiv.mk
    (tensorSquareProdRearrangedLinearEquiv (ρ := ρ) (σ := σ))
    (tensorSquareProdRearrangedLinearEquiv_intertwines (ρ := ρ) (σ := σ))

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- Helper for Exercise 2-2.1-4: after transporting the tensor swap across the four-block
equivalence, it acts by `ρ.tensorSwap` on the `VV` block, by plain factor-swap on the middle two
copies of `V ⊗ W`, and by `σ.tensorSwap` on the `WW` block. -/
lemma tensorSwap_tensorSquareProdRearrangedEquiv_apply
    (z : (V ⊗[k] V) × (((V ⊗[k] W) × (V ⊗[k] W)) × (W ⊗[k] W))) :
    tensorSquareProdRearrangedEquiv (ρ := ρ) (σ := σ)
      ((ρ.prod σ).tensorSwap ((tensorSquareProdRearrangedEquiv (ρ := ρ) (σ := σ)).symm z)) =
        (ρ.tensorSwap z.1, ((z.2.1.2, z.2.1.1), σ.tensorSwap z.2.2)) :=
by
  let e := tensorSquareProdRearrangedEquiv (ρ := ρ) (σ := σ)
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
  -- Evaluate the conjugated swap on pure tensors, then extend by linearity.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · rfl
  · intro x y
    rcases x with ⟨v, w⟩
    rcases y with ⟨v', w'⟩
    -- On a pure tensor, the transported swap is just the rearranged image of the swapped tensor.
    simpa [e, tensorSquareProdRearrangedEquiv, Representation.tensorSwap] using
      tensorSquareProdRearrangedLinearEquiv_apply_tmul (ρ := ρ) (σ := σ) v' v w' w
  · intro x y hx hy
    simpa using congrArg₂ HAdd.hAdd hx hy

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- Helper for Exercise 2-2.1-4: the symmetric-square block decomposition exists by transporting
the swap-fixed condition across the four-block tensor-square equivalence and collapsing the middle
diagonal pair to one copy of `ρ.tprod σ`. -/
private theorem symmetricSquareProdEquiv_exists :
    Nonempty ((Sym² (ρ.prod σ)).Equiv ((Sym² ρ).prod ((ρ.tprod σ).prod (Sym² σ)))) := by
  let e := tensorSquareProdRearrangedEquiv (ρ := ρ) (σ := σ)
  let f : (Sym²ₛ (ρ.prod σ)).toSubmodule →ₗ[k]
      (Sym²ₛ ρ).toSubmodule × ((V ⊗[k] W) × (Sym²ₛ σ).toSubmodule) := by
    refine
      { toFun := fun x => ?_
        map_add' := ?_
        map_smul' := ?_ }
    · let z := e x.1
      have hx : (ρ.prod σ).tensorSwap x.1 = x.1 := by
        exact ((ρ.prod σ).mem_symmetricSquareSubrepresentation_iff (z := x.1)).1 x.2
      have hx' : (_root_.TensorProduct.comm k (V × W) (V × W)) x.1 = x.1 := by
        simpa [Representation.tensorSwap] using hx
      -- The transported `+1`-eigenvector equation splits into the three block conditions.
      have hz :
          (ρ.tensorSwap z.1, ((z.2.1.2, z.2.1.1), σ.tensorSwap z.2.2)) = z := by
        simpa [e, z, hx'] using
          (tensorSwap_tensorSquareProdRearrangedEquiv_apply (ρ := ρ) (σ := σ) z).symm
      have hz₁ : ρ.tensorSwap z.1 = z.1 := by
        simpa using congrArg Prod.fst hz
      have hz₂ : σ.tensorSwap z.2.2 = z.2.2 := by
        simpa using congrArg (fun t => t.2.2) hz
      exact
        (⟨z.1, (ρ.mem_symmetricSquareSubrepresentation_iff (z := z.1)).2 hz₁⟩,
          (z.2.1.1, ⟨z.2.2, (σ.mem_symmetricSquareSubrepresentation_iff (z := z.2.2)).2 hz₂⟩))
    · intro x y
      ext <;> simp [e, map_add]
    · intro a x
      ext <;> simp [e, map_smul]
  let g : (Sym²ₛ ρ).toSubmodule × ((V ⊗[k] W) × (Sym²ₛ σ).toSubmodule) →ₗ[k]
      (Sym²ₛ (ρ.prod σ)).toSubmodule := by
    refine
      { toFun := fun x => ?_
        map_add' := ?_
        map_smul' := ?_ }
    · let z : (V ⊗[k] V) × (((V ⊗[k] W) × (V ⊗[k] W)) × (W ⊗[k] W)) :=
          (x.1.1, ((x.2.1, x.2.1), x.2.2.1))
      have hx₁ : ρ.tensorSwap x.1.1 = x.1.1 := by
        exact (ρ.mem_symmetricSquareSubrepresentation_iff (z := x.1.1)).1 x.1.2
      have hx₂ : σ.tensorSwap x.2.2.1 = x.2.2.1 := by
        exact (σ.mem_symmetricSquareSubrepresentation_iff (z := x.2.2.1)).1 x.2.2.2
      have hx₁' : (_root_.TensorProduct.comm k V V) x.1.1 = x.1.1 := by
        simpa [Representation.tensorSwap] using hx₁
      have hx₂' : (_root_.TensorProduct.comm k W W) x.2.2.1 = x.2.2.1 := by
        simpa [Representation.tensorSwap] using hx₂
      -- Reinsert the duplicated middle block and check that the transported swap fixes it.
      have hz : (ρ.prod σ).tensorSwap (e.symm z) = e.symm z := by
        apply e.toLinearEquiv.injective
        simpa [e, z, hx₁', hx₂'] using
          tensorSwap_tensorSquareProdRearrangedEquiv_apply (ρ := ρ) (σ := σ) z
      exact
        ⟨e.symm z, ((ρ.prod σ).mem_symmetricSquareSubrepresentation_iff (z := e.symm z)).2 hz⟩
    · intro x y
      apply Subtype.ext
      simpa using e.toLinearEquiv.symm.map_add
        (x.1.1, ((x.2.1, x.2.1), x.2.2.1))
        (y.1.1, ((y.2.1, y.2.1), y.2.2.1))
    · intro a x
      apply Subtype.ext
      simpa using e.toLinearEquiv.symm.map_smul a
        (x.1.1, ((x.2.1, x.2.1), x.2.2.1))
  have hfg : Function.LeftInverse g f := by
    intro x
    ext
    let z := e x.1
    have hx : (ρ.prod σ).tensorSwap x.1 = x.1 := by
      exact ((ρ.prod σ).mem_symmetricSquareSubrepresentation_iff (z := x.1)).1 x.2
    have hx' : (_root_.TensorProduct.comm k (V × W) (V × W)) x.1 = x.1 := by
      simpa [Representation.tensorSwap] using hx
    have hz :
        (ρ.tensorSwap z.1, ((z.2.1.2, z.2.1.1), σ.tensorSwap z.2.2)) = z := by
      simpa [e, z, hx'] using
        (tensorSwap_tensorSquareProdRearrangedEquiv_apply (ρ := ρ) (σ := σ) z).symm
    have hmid : z.2.1.2 = z.2.1.1 := by
      simpa using congrArg (fun t => t.2.1.1) hz
    -- The inverse restores the duplicated middle coordinate, which is already diagonal.
    have hdiagTuple : (z.1, ((z.2.1.1, z.2.1.1), z.2.2)) = z := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply Prod.ext
          · rfl
          · simp [hmid]
        · rfl
    apply e.toLinearEquiv.injective
    simpa [f, g, z] using hdiagTuple
  have hgf : Function.RightInverse g f := by
    intro x
    let z : (V ⊗[k] V) × (((V ⊗[k] W) × (V ⊗[k] W)) × (W ⊗[k] W)) :=
      (x.1.1, ((x.2.1, x.2.1), x.2.2.1))
    have hz : e (e.symm z) = z := by
      exact e.apply_symm_apply z
    ext
    · change (e (e.symm z)).1 = z.1
      exact congrArg Prod.fst hz
    · change (e (e.symm z)).2.1.1 = z.2.1.1
      exact congrArg (fun t => t.2.1.1) hz
    · change (e (e.symm z)).2.2 = z.2.2
      exact congrArg (fun t => t.2.2) hz
  let eSymm : (Sym²ₛ (ρ.prod σ)).toSubmodule ≃ₗ[k]
      (Sym²ₛ ρ).toSubmodule × ((V ⊗[k] W) × (Sym²ₛ σ).toSubmodule) :=
    LinearEquiv.ofBijective f
      ⟨Function.LeftInverse.injective hfg, Function.RightInverse.surjective hgf⟩
  refine ⟨Representation.Equiv.mk eSymm ?_⟩
  intro g₀
  ext x
  -- The three retained blocks transform exactly by the product action after transport.
  · have hx := LinearMap.congr_fun (e.toIntertwiningMap.2 g₀) x.1
    simpa [eSymm, f, Representation.symmetricSquare_apply] using congrArg Prod.fst hx
  · have hx := LinearMap.congr_fun (e.toIntertwiningMap.2 g₀) x.1
    simpa [eSymm, f] using congrArg (fun t => t.2.1.1) hx
  · have hx := LinearMap.congr_fun (e.toIntertwiningMap.2 g₀) x.1
    simpa [eSymm, f, Representation.symmetricSquare_apply] using
      congrArg (fun t => t.2.2) hx

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- Helper for Exercise 2-2.1-4: the alternating-square block decomposition exists by transporting
the `-1`-eigenvector condition across the four-block tensor-square equivalence and collapsing the
middle anti-diagonal pair to one copy of `ρ.tprod σ`. -/
private theorem alternatingSquareProdEquiv_exists :
    Nonempty ((Alt² (ρ.prod σ)).Equiv ((Alt² ρ).prod ((ρ.tprod σ).prod (Alt² σ)))) := by
  let e := tensorSquareProdRearrangedEquiv (ρ := ρ) (σ := σ)
  let f : (Alt²ₛ (ρ.prod σ)).toSubmodule →ₗ[k]
      (Alt²ₛ ρ).toSubmodule × ((V ⊗[k] W) × (Alt²ₛ σ).toSubmodule) := by
    refine
      { toFun := fun x => ?_
        map_add' := ?_
        map_smul' := ?_ }
    · let z := e x.1
      have hx : (ρ.prod σ).tensorSwap x.1 = -x.1 := by
        exact ((ρ.prod σ).mem_alternatingSquareSubrepresentation_iff (z := x.1)).1 x.2
      have hx' : (_root_.TensorProduct.comm k (V × W) (V × W)) x.1 = -x.1 := by
        simpa [Representation.tensorSwap] using hx
      -- The transported `-1`-eigenvector equation again splits blockwise.
      have hz :
          (ρ.tensorSwap z.1, ((z.2.1.2, z.2.1.1), σ.tensorSwap z.2.2)) = -z := by
        simpa [e, z, hx'] using
          (tensorSwap_tensorSquareProdRearrangedEquiv_apply (ρ := ρ) (σ := σ) z).symm
      have hz₁ : ρ.tensorSwap z.1 = -z.1 := by
        simpa using congrArg Prod.fst hz
      have hz₂ : σ.tensorSwap z.2.2 = -z.2.2 := by
        simpa using congrArg (fun t => t.2.2) hz
      exact
        (⟨z.1, (ρ.mem_alternatingSquareSubrepresentation_iff (z := z.1)).2 hz₁⟩,
          (z.2.1.1, ⟨z.2.2, (σ.mem_alternatingSquareSubrepresentation_iff (z := z.2.2)).2 hz₂⟩))
    · intro x y
      ext <;> simp [e, map_add]
    · intro a x
      ext <;> simp [e, map_smul]
  let antiDiagonalMiddleMap :
      (Alt²ₛ ρ).toSubmodule × ((V ⊗[k] W) × (Alt²ₛ σ).toSubmodule) →ₗ[k]
        ((V ⊗[k] V) × (((V ⊗[k] W) × (V ⊗[k] W)) × (W ⊗[k] W))) :=
    { toFun := fun x => (x.1.1, ((x.2.1, -x.2.1), x.2.2.1))
      map_add' := by
        intro x y
        ext <;> simp [add_comm]
      map_smul' := by
        intro a x
        ext <;> simp }
  let g : (Alt²ₛ ρ).toSubmodule × ((V ⊗[k] W) × (Alt²ₛ σ).toSubmodule) →ₗ[k]
      (Alt²ₛ (ρ.prod σ)).toSubmodule := by
    refine
      { toFun := fun x => ?_
        map_add' := ?_
        map_smul' := ?_ }
    · let z := antiDiagonalMiddleMap x
      have hx₁ : ρ.tensorSwap x.1.1 = -x.1.1 := by
        exact (ρ.mem_alternatingSquareSubrepresentation_iff (z := x.1.1)).1 x.1.2
      have hx₂ : σ.tensorSwap x.2.2.1 = -x.2.2.1 := by
        exact (σ.mem_alternatingSquareSubrepresentation_iff (z := x.2.2.1)).1 x.2.2.2
      have hx₁' : (_root_.TensorProduct.comm k V V) x.1.1 = -x.1.1 := by
        simpa [Representation.tensorSwap] using hx₁
      have hx₂' : (_root_.TensorProduct.comm k W W) x.2.2.1 = -x.2.2.1 := by
        simpa [Representation.tensorSwap] using hx₂
      -- Reinsert the anti-diagonal middle block and check that the transported swap negates it.
      have hz : (ρ.prod σ).tensorSwap (e.symm z) = -(e.symm z) := by
        apply e.toLinearEquiv.injective
        simpa [antiDiagonalMiddleMap, e, z, hx₁', hx₂'] using
          tensorSwap_tensorSquareProdRearrangedEquiv_apply (ρ := ρ) (σ := σ) z
      exact
        ⟨e.symm z, ((ρ.prod σ).mem_alternatingSquareSubrepresentation_iff (z := e.symm z)).2 hz⟩
    · intro x y
      apply Subtype.ext
      change e.toLinearEquiv.symm (antiDiagonalMiddleMap (x + y)) =
          e.toLinearEquiv.symm (antiDiagonalMiddleMap x) +
            e.toLinearEquiv.symm (antiDiagonalMiddleMap y)
      rw [antiDiagonalMiddleMap.map_add, e.toLinearEquiv.symm.map_add]
    · intro a x
      apply Subtype.ext
      change e.toLinearEquiv.symm (antiDiagonalMiddleMap (a • x)) =
          a • e.toLinearEquiv.symm (antiDiagonalMiddleMap x)
      rw [antiDiagonalMiddleMap.map_smul, e.toLinearEquiv.symm.map_smul]
  have hfg : Function.LeftInverse g f := by
    intro x
    ext
    let z := e x.1
    have hx : (ρ.prod σ).tensorSwap x.1 = -x.1 := by
      exact ((ρ.prod σ).mem_alternatingSquareSubrepresentation_iff (z := x.1)).1 x.2
    have hx' : (_root_.TensorProduct.comm k (V × W) (V × W)) x.1 = -x.1 := by
      simpa [Representation.tensorSwap] using hx
    have hz :
        (ρ.tensorSwap z.1, ((z.2.1.2, z.2.1.1), σ.tensorSwap z.2.2)) = -z := by
      simpa [e, z, hx'] using
        (tensorSwap_tensorSquareProdRearrangedEquiv_apply (ρ := ρ) (σ := σ) z).symm
    have hmid : z.2.1.2 = -z.2.1.1 := by
      simpa using congrArg (fun t => t.2.1.1) hz
    -- The inverse restores the anti-diagonal middle pair determined by the alternating equation.
    have hantiTuple : (z.1, ((z.2.1.1, -z.2.1.1), z.2.2)) = z := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply Prod.ext
          · rfl
          · simp [hmid]
        · rfl
    apply e.toLinearEquiv.injective
    simpa [f, g, z] using hantiTuple
  have hgf : Function.RightInverse g f := by
    intro x
    let z := antiDiagonalMiddleMap x
    have hz : e (e.symm z) = z := by
      exact e.apply_symm_apply z
    ext
    · change (e (e.symm z)).1 = z.1
      exact congrArg Prod.fst hz
    · change (e (e.symm z)).2.1.1 = z.2.1.1
      exact congrArg (fun t => t.2.1.1) hz
    · change (e (e.symm z)).2.2 = z.2.2
      exact congrArg (fun t => t.2.2) hz
  let eAlt : (Alt²ₛ (ρ.prod σ)).toSubmodule ≃ₗ[k]
      (Alt²ₛ ρ).toSubmodule × ((V ⊗[k] W) × (Alt²ₛ σ).toSubmodule) :=
    LinearEquiv.ofBijective f
      ⟨Function.LeftInverse.injective hfg, Function.RightInverse.surjective hgf⟩
  refine ⟨Representation.Equiv.mk eAlt ?_⟩
  intro g₀
  ext x
  -- The same transported-action computation governs the alternating blocks.
  · have hx := LinearMap.congr_fun (e.toIntertwiningMap.2 g₀) x.1
    simpa [eAlt, f, Representation.alternatingSquare_apply] using congrArg Prod.fst hx
  · have hx := LinearMap.congr_fun (e.toIntertwiningMap.2 g₀) x.1
    simpa [eAlt, f] using congrArg (fun t => t.2.1.1) hx
  · have hx := LinearMap.congr_fun (e.toIntertwiningMap.2 g₀) x.1
    simpa [eAlt, f, Representation.alternatingSquare_apply] using
      congrArg (fun t => t.2.2) hx

/-- Helper for Exercise 2-2.1-4: the `+1`-eigenspace of the transported swap is the product of
the symmetric `VV` block, the diagonal `VW` block, and the symmetric `WW` block. -/
def symmetricSquareProdEquiv :
    (Sym² (ρ.prod σ)).Equiv ((Sym² ρ).prod ((ρ.tprod σ).prod (Sym² σ))) :=
  Classical.choice (symmetricSquareProdEquiv_exists (ρ := ρ) (σ := σ))

/-- Helper for Exercise 2-2.1-4: the `-1`-eigenspace of the transported swap is the product of
the alternating `VV` block, the anti-diagonal `VW` block, and the alternating `WW` block. -/
def alternatingSquareProdEquiv :
    (Alt² (ρ.prod σ)).Equiv ((Alt² ρ).prod ((ρ.tprod σ).prod (Alt² σ))) :=
  Classical.choice (alternatingSquareProdEquiv_exists (ρ := ρ) (σ := σ))

-- Proof sketch: transport the tensor square of `V × W` across `TensorProduct.prodLeft` and
-- `TensorProduct.prodRight`. Under the resulting canonical four-block decomposition, the
-- swap-fixed part identifies with `(Sym² ρ).prod ((ρ.tprod σ).prod (Sym² σ))`, and the character
-- formula then reduces to `Representation.char_prod` and `Representation.char_tensor`.
/-- Exercise 2-2.1-4 (1): the character of the symmetric square of a direct sum is the sum of the
symmetric-square characters plus the product of the original characters. -/
theorem char_symmetricSquare_prod :
    (Sym² (ρ.prod σ)).character =
      (Sym² ρ).character + (Sym² σ).character + ρ.character * σ.character :=
by
  -- Once the symmetric square is identified with the three canonical blocks, the character is the
  -- sum of the two outer symmetric-square characters and the middle tensor-product character.
  simpa [Representation.char_prod, Representation.char_tensor, add_assoc, add_left_comm, add_comm]
    using Representation.char_iso (symmetricSquareProdEquiv (ρ := ρ) (σ := σ))

-- Proof sketch: use the same four-block tensor decomposition. The `-1`-eigenspace of the swap
-- identifies with `(Alt² ρ).prod ((ρ.tprod σ).prod (Alt² σ))`, and the character formula again
-- reduces to `Representation.char_prod` and `Representation.char_tensor`.
/-- Exercise 2-2.1-4 (2): the character of the alternating square of a direct sum is the sum of
the alternating-square characters plus the product of the original characters. -/
theorem char_alternatingSquare_prod :
    (Alt² (ρ.prod σ)).character =
      (Alt² ρ).character + (Alt² σ).character + ρ.character * σ.character :=
by
  -- The alternating-square block decomposition has the same middle tensor-product contribution,
  -- with the outer blocks replaced by the alternating squares.
  simpa [Representation.char_prod, Representation.char_tensor, add_assoc, add_left_comm, add_comm]
    using Representation.char_iso (alternatingSquareProdEquiv (ρ := ρ) (σ := σ))

end

end Representation

/-! ### Exercise_2_2_1_5 (from Chap02) -/
universe u v

namespace Representation

section

variable {k : Type*} {G : Type u} {X : Type v} [Field k] [Monoid G] [MulAction G X] [Finite X]

/-
Source/core/bridge triage:
* source-facing: the value of the permutation character at `s`.
* core/canonical owners: `Representation.ofMulAction`, `Representation.character`, and
  `MulAction.fixedBy`.
* bridge/view: in the delta-function basis of `X →₀ k`, the diagonal entry indexed by `x` is `1`
  exactly when `s • x = x`, so the trace counts the fixed basis vectors.
-/
-- Proof sketch: in the delta-function basis of `X →₀ k`, the diagonal entry indexed by `x` is `1`
-- exactly when `s • x = x`, so the trace counts the fixed points of the endomorphism `x ↦ s • x`.
/-- Exercise 2-2.1-5: for the permutation representation attached to a finite `G`-set `X`, the
character at `s` is the number of elements of `X` fixed by `s`. -/
@[simp]
theorem ofMulAction_character_eq_ncard_fixedBy (s : G) :
    (ofMulAction k G X).character s = ↑(MulAction.fixedBy X s).ncard := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  calc
    (ofMulAction k G X).character s
      = Matrix.trace
          (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
            ((ofMulAction k G X) s)) := by
          rw [character, LinearMap.trace_eq_matrix_trace k Finsupp.basisSingleOne]
    _ = ∑ x : X, if s • x = x then 1 else 0 := by
          simp [Matrix.trace, LinearMap.toMatrix_apply, ofMulAction_single,
            Finsupp.single_apply]
    _ = ↑((Finset.univ.filter fun x : X ↦ s • x = x).card) := by
          simp
    _ = ↑((MulAction.fixedBy X s).toFinset.card) := by
          congr
          ext x
          simp [MulAction.mem_fixedBy]
    _ = ↑(MulAction.fixedBy X s).ncard := by
          rw [← Set.ncard_eq_toFinset_card']

end

end Representation

/-! ### Exercise_2_2_1_6 (from Chap02) -/
universe u v w

namespace Representation

open Module.Dual

section

variable {k : Type u} [CommSemiring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/- The canonical contragredient action on the algebraic dual is `Representation.dual`. -/
recall dual

/- The primitive action formula for the canonical dual representation is
`Representation.dual_apply`. -/
recall dual_apply

/-- The canonical dual representation preserves evaluation against `ρ`. -/
theorem dual_preserves_eval (s : G) (x : V) (x' : Module.Dual k V) :
    ρ.dual s x' (ρ s x) = x' x := by
  simp [dual_apply, transpose_apply]

/-- Any representation on the dual space whose action preserves evaluation against `ρ` is the
canonical dual representation `ρ.dual`. -/
theorem eq_dual_of_preserves_eval {ρ' : Representation k G (Module.Dual k V)}
    (hρ' : ∀ (s : G) (x : V) (x' : Module.Dual k V), ρ' s x' (ρ s x) = x' x) :
    ρ' = ρ.dual := by
  ext s x' x
  simpa [dual_apply] using hρ' s (ρ s⁻¹ x) x'

/-- Exercise 2-2.1-6: there exists a unique contragredient representation on the dual space whose
action preserves the natural pairing with `ρ`. -/
theorem existsUnique_dual_representation :
    ∃! ρ' : Representation k G (Module.Dual k V),
      ∀ s x x', ρ' s x' (ρ s x) = x' x := by
  refine ⟨ρ.dual, ρ.dual_preserves_eval, ?_⟩
  · intro ρ' hρ'
    exact ρ.eq_dual_of_preserves_eval hρ'

end

end Representation

/-! ### Exercise_2_2_1_7 (from Chap02) -/
/- Source/core/bridge triage:
- `source-facing`: Exercise 2-2.1-7, namely the Hom representation, its character formula, and its
  identification with the dual-tensor representation;
- `core/canonical`: `Representation.linHom`, `Representation.char_linHom`, and
  `Representation.Equiv.dualTensorHom`;
- `bridge/view`: the underlying linear owner `LinearMap.dualTensorHom` and its equivalence
  `dualTensorHomEquiv`.

Primitive data already lives in mathlib's canonical representation-theoretic owner layer, so this
file should be pure recall of that API rather than a parallel local wrapper. -/

/- Exercise 2-2.1-7: the conjugation action of `G` on `Hom(V, W)` given by
`f ↦ σ s ∘ₗ f ∘ₗ ρ s⁻¹` is the canonical Hom representation `Representation.linHom ρ σ`. -/
recall Representation.linHom

/- The character of the Hom representation is the product of the contragredient character of `ρ`
with the character of `σ`, namely `g ↦ ρ.character g⁻¹ * σ.character g`. -/
recall Representation.char_linHom

/- The Hom representation is canonically isomorphic to the tensor product of the dual
representation of `ρ` with `σ`. -/
recall Representation.Equiv.dualTensorHom

/-! ### Proposition_2_2_1_1 (from Chap02) -/
noncomputable section

universe u v w

section FiniteOrderCharpolyRoots

variable {G : Type u} [Group G]
variable {k : Type w} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

namespace Representation

open Module.End

variable (ρ : Representation k G V)

/-- Helper for finite-order character arguments: a root of the characteristic polynomial of `ρ s`
has `orderOf s`-th power equal to `1`. -/
lemma charpoly_root_pow_orderOf_eq_one (s : G) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    μ ^ orderOf s = 1 := by
  have hρs_pow_eq_one : (ρ s) ^ orderOf s = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hμeig : HasEigenvalue (ρ s) μ :=
    (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).2 <|
      (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).1 hμ
  have hμpow : HasEigenvalue (1 : Module.End k V) (μ ^ orderOf s) := by
    simpa [hρs_pow_eq_one] using hμeig.pow (orderOf s)
  obtain ⟨v, hv⟩ := hμpow.exists_hasEigenvector
  have hsmul : (μ ^ orderOf s - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hv.apply_eq_smul]
    simp
  exact sub_eq_zero.mp <| (smul_eq_zero_iff_left hv.2).mp hsmul

end Representation

end FiniteOrderCharpolyRoots

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- Source clause (1): the character at the identity element equals the degree
`Module.finrank ℂ V` of the representation. This is the existing theorem
`Representation.char_one`. -/
recall Representation.char_one

namespace Representation

open Module.End

variable (ρ : Representation ℂ G V)

/- Bridge/view for Proposition 2-2.1-1 (2): if `s` has finite order, then the character at `s⁻¹`
is the complex conjugate of the character at `s`. The source finite-group statement is recovered
from `isOfFinOrder_of_finite`. -/
-- Proof sketch: if `s : G` has finite order, then `ρ s` has finite order as a
-- linear automorphism. Its eigenvalues are roots of unity, hence their inverses are their complex
-- conjugates; taking traces gives the stated identity.
/-- Helper for Proposition 2-2.1-1: over `ℂ`, a finite-order root of the characteristic
polynomial has conjugate equal to its inverse. -/
lemma star_eq_inv_of_charpoly_root (s : G) (hs : IsOfFinOrder s) {μ : ℂ}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    star μ = μ⁻¹ := by
  -- The previous lemma puts `μ` on the unit circle.
  have hμpow : μ ^ orderOf s = 1 :=
    ρ.charpoly_root_pow_orderOf_eq_one s hμ
  have hnorm : ‖μ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hμpow hs.orderOf_pos.ne'
  simpa using (Complex.inv_eq_conj hnorm).symm

/-- Helper for Proposition 2-2.1-1: the trace of `ρ s⁻¹` is the sum of the inverse roots of the
characteristic polynomial of `ρ s`. -/
lemma trace_inv_eq_sum_inv_charpoly_roots (s : G) :
    LinearMap.trace ℂ V (ρ s⁻¹) = ((ρ s).charpoly.roots.map fun μ ↦ μ⁻¹).sum := by
  let b := Module.Free.chooseBasis ℂ V
  let ι := Module.Free.ChooseBasisIndex ℂ V
  let A : Matrix ι ι ℂ :=
    LinearMap.toMatrix b b (ρ s)
  by_cases hι : IsEmpty ι
  · letI := hι
    -- In the zero-dimensional case both traces and root sums vanish.
    rw [LinearMap.trace_eq_matrix_trace ℂ b, ← LinearMap.charpoly_toMatrix (ρ s) b]
    simp [b, ι]
  · letI := Classical.decEq ι
    letI : Nonempty ι := not_isEmpty_iff.mp hι
    have hA_mul : A * LinearMap.toMatrix b b (ρ s⁻¹) = 1 := by
      -- The matrix of `ρ s⁻¹` is a right inverse for the matrix of `ρ s`.
      change LinearMap.toMatrix b b (ρ s) * LinearMap.toMatrix b b (ρ s⁻¹) = 1
      rw [← LinearMap.toMatrix_mul b (ρ s) (ρ s⁻¹), ← ρ.map_mul, mul_inv_cancel,
        ρ.map_one, LinearMap.toMatrix_one]
    have hAinv : A⁻¹ = LinearMap.toMatrix b b (ρ s⁻¹) :=
      Matrix.inv_eq_right_inv hA_mul
    have hAeval0_ne : A.charpoly.eval 0 ≠ 0 := by
      -- Invertibility of `A` forces the constant coefficient of its characteristic polynomial
      -- to be nonzero.
      intro h0
      have hdet0 : A.det = 0 := by
        rw [Matrix.det_eq_sign_charpoly_coeff, Polynomial.coeff_zero_eq_eval_zero, h0]
        simp
      exact (Matrix.isUnit_det_of_right_inverse hA_mul).ne_zero hdet0
    have hscalar :
        (-1 : ℂ) ^ Fintype.card ι * A.det⁻¹ = (A.charpoly.eval 0)⁻¹ := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Polynomial.coeff_zero_eq_eval_zero]
      field_simp [hAeval0_ne]
    have hcoeff_rev :
        A.charpolyRev.coeff (Fintype.card ι - 1) = A.charpoly.coeff 1 := by
      -- The coefficient just below the top degree in the reverse polynomial is the linear
      -- coefficient of the original characteristic polynomial.
      rw [← A.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim]
      have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos
      have hsub : Fintype.card ι - (Fintype.card ι - 1) = 1 := by omega
      simp [hsub]
    have htrace_inv :
        A⁻¹.trace = - (A.charpoly.derivative.eval 0 / A.charpoly.eval 0) := by
      -- `charpoly_inv` expresses the characteristic polynomial of `A⁻¹`; extracting the
      -- coefficient of degree `dim V - 1` gives a trace formula for the inverse.
      have hA_unit : IsUnit A := IsUnit.of_mul_eq_one _ hA_mul
      have hcoeff_outer :
          (Polynomial.C ((-1 : ℂ) ^ Fintype.card ι) *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev)).coeff
              (Fintype.card ι - 1) =
            (-1 : ℂ) ^ Fintype.card ι *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev).coeff (Fintype.card ι - 1) := by
        simpa [mul_assoc] using
          (Polynomial.coeff_C_mul (p := Polynomial.C (Ring.inverse A.det) * A.charpolyRev)
            (a := (-1 : ℂ) ^ Fintype.card ι) (n := Fintype.card ι - 1))
      have hcoeff_inner :
          (Polynomial.C (Ring.inverse A.det) * A.charpolyRev).coeff (Fintype.card ι - 1) =
            A.det⁻¹ * A.charpolyRev.coeff (Fintype.card ι - 1) := by
        simp [Polynomial.coeff_C_mul, Ring.inverse_eq_inv]
      have hcoeff_total :
          (Polynomial.C ((-1 : ℂ) ^ Fintype.card ι) *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev)).coeff
              (Fintype.card ι - 1) =
            (((-1 : ℂ) ^ Fintype.card ι) * A.det⁻¹) *
              A.charpolyRev.coeff (Fintype.card ι - 1) := by
        calc
          (Polynomial.C ((-1 : ℂ) ^ Fintype.card ι) *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev)).coeff
              (Fintype.card ι - 1) =
              (-1 : ℂ) ^ Fintype.card ι *
                (Polynomial.C (Ring.inverse A.det) * A.charpolyRev).coeff
                  (Fintype.card ι - 1) := by
                  simpa [mul_assoc] using hcoeff_outer
          _ = (((-1 : ℂ) ^ Fintype.card ι) * A.det⁻¹) *
                A.charpolyRev.coeff (Fintype.card ι - 1) := by
                rw [hcoeff_inner]
                ac_rfl
      calc
        A⁻¹.trace = - (A⁻¹).charpoly.coeff (Fintype.card ι - 1) := by
          simpa using Matrix.trace_eq_neg_charpoly_coeff (A⁻¹)
        _ = - ((((-1 : ℂ) ^ Fintype.card ι) * A.det⁻¹) *
            A.charpolyRev.coeff (Fintype.card ι - 1)) := by
              rw [Matrix.charpoly_inv A hA_unit]
              simpa [mul_assoc] using congrArg Neg.neg hcoeff_total
        _ = - ((A.charpoly.eval 0)⁻¹ * A.charpoly.coeff 1) := by
              rw [hscalar, hcoeff_rev]
        _ = - (A.charpoly.coeff 1 * (A.charpoly.eval 0)⁻¹) := by
              rw [mul_comm]
        _ = - (A.charpoly.derivative.eval 0 * (A.charpoly.eval 0)⁻¹) := by
              congr 2
              rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
              norm_num
        _ = - (A.charpoly.derivative.eval 0 / A.charpoly.eval 0) := by
              rw [div_eq_mul_inv]
    have hratio :
        A.charpoly.derivative.eval 0 / A.charpoly.eval 0 =
          - (A.charpoly.roots.map fun μ ↦ μ⁻¹).sum := by
      -- The logarithmic derivative of a split polynomial is the sum of reciprocal linear factors.
      simpa [div_eq_mul_inv] using
        (IsAlgClosed.splits A.charpoly).eval_derivative_div_eval_of_ne_zero (x := 0) hAeval0_ne
    calc
      LinearMap.trace ℂ V (ρ s⁻¹) = (LinearMap.toMatrix b b (ρ s⁻¹)).trace := by
        rw [LinearMap.trace_eq_matrix_trace ℂ b]
      _ = A⁻¹.trace := by rw [← hAinv]
      _ = - (A.charpoly.derivative.eval 0 / A.charpoly.eval 0) := htrace_inv
      _ = ((A.charpoly.roots.map fun μ ↦ μ⁻¹).sum) := by rw [hratio, neg_neg]
      _ = ((ρ s).charpoly.roots.map fun μ ↦ μ⁻¹).sum := by
        simp [A, LinearMap.charpoly_toMatrix]

theorem char_inv_eq_star_of_isOfFinOrder (s : G) (hs : IsOfFinOrder s) :
    ρ.character s⁻¹ = star (ρ.character s) := by
  -- Rewrite the left-hand side as the trace of the inverse and the right-hand side as the
  -- conjugate of the trace.
  change LinearMap.trace ℂ V (ρ s⁻¹) = star (ρ.character s)
  rw [ρ.trace_inv_eq_sum_inv_charpoly_roots s]
  change ((ρ s).charpoly.roots.map fun μ ↦ μ⁻¹).sum = star (LinearMap.trace ℂ V (ρ s))
  rw [trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  rw [show star (Multiset.sum (ρ s).charpoly.roots) =
      (Multiset.map star (ρ s).charpoly.roots).sum by
        simpa using map_multiset_sum (starRingEnd ℂ) ((ρ s).charpoly.roots)]
  -- Each root is inverted by complex conjugation because it is a root of unity.
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun μ hμ ↦ ?_
  simpa using (ρ.star_eq_inv_of_charpoly_root s hs hμ).symm

/- The canonical dual-character identity is the existing theorem
`Representation.char_dual`. -/
recall Representation.char_dual

/-- For a finite-dimensional complex representation of a finite group, the character of the dual
representation is the complex conjugate of the original character. -/
theorem char_dual_eq_star [Finite G] (s : G) :
    ρ.dual.character s = star (ρ.character s) := by
  simpa using ρ.char_inv_eq_star_of_isOfFinOrder s (isOfFinOrder_of_finite s)

/- Source clause (3): the character is constant on conjugacy classes. This is the existing theorem
`Representation.char_conj`. -/
recall Representation.char_conj

section ClassFunctionInfrastructure

variable {R : Type v}

/-- Helper for Proposition 2-2.1-1: a class function on a group factors through conjugacy classes.
-/
@[mk_iff]
class IsClassFunction (f : G → R) : Prop where
  factorsThrough : f.FactorsThrough ConjClasses.mk

/-- Helper for Proposition 2-2.1-1: the complex-valued class functions on `G` form a subspace. -/
abbrev classFunctionSubspace (G : Type u) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := { f | IsClassFunction f }
  zero_mem' := by
    exact ⟨fun _ _ _ ↦ rfl⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_⟩
    intro x y hxy
    change f x + g x = f y + g y
    simpa using congrArg₂ (· + ·) (hf.factorsThrough hxy) (hg.factorsThrough hxy)
  smul_mem' := by
    intro c f hf
    refine ⟨?_⟩
    intro x y hxy
    change c • f x = c • f y
    simpa using congrArg (c • ·) (hf.factorsThrough hxy)

/-- Helper for Proposition 2-2.1-1: membership in `classFunctionSubspace G` is exactly the class
function property. -/
@[simp] theorem mem_classFunctionSubspace_iff (f : G → ℂ) :
    f ∈ classFunctionSubspace G ↔ IsClassFunction f := by
  rfl

end ClassFunctionInfrastructure

omit [FiniteDimensional ℂ V] in
/-- Bridge/view from the canonical conjugacy formula `Representation.char_conj` to the chapter-level
predicate `IsClassFunction`. -/
theorem char_eq_of_isConj {x y : G} (hxy : IsConj x y) :
    ρ.character x = ρ.character y := by
  rcases isConj_iff.1 hxy with ⟨a, rfl⟩
  exact (ρ.char_conj x a).symm

/-- The character of a finite-dimensional complex representation is a class function. -/
instance : IsClassFunction ρ.character :=
  ⟨fun _ _ h ↦ ρ.char_eq_of_isConj <| ConjClasses.mk_eq_mk_iff_isConj.mp h⟩

omit [FiniteDimensional ℂ V] in
/-- Helper for Proposition 2-2.1-1: the character of a representation lies in the
class-function subspace. -/
theorem character_mem_classFunctionSubspace :
    ρ.character ∈ classFunctionSubspace G := by
  -- Membership in the subspace is exactly the conjugacy-invariance property already proved above.
  exact (mem_classFunctionSubspace_iff _).2 inferInstance

/-- The character of a finite-dimensional complex representation, viewed as an element of the
class-function subspace. -/
abbrev classFunction : classFunctionSubspace G :=
  ⟨ρ.character, ρ.character_mem_classFunctionSubspace⟩

omit [FiniteDimensional ℂ V] in
@[simp] theorem classFunction_apply (g : G) :
    (ρ.classFunction : G → ℂ) g = ρ.character g :=
  rfl

end Representation

end

/-! ### Proposition_2_2_1_2 (from Chap02) -/
/- Source/core/bridge triage:
- `source-facing`: Proposition 2-2.1-2 (1) and (2), the two character identities recalled below;
- `core/canonical`: `Representation.character` with `Representation.char_prod` and
  `Representation.char_tensor`;
- `bridge/view`: none.

Primitive data is already owned by `Representation`; this file is pure recall of the canonical
derived API, so there is no parallel local wrapper to keep. -/

/- Proposition 2-2.1-2 (1): the character of the binary direct-sum representation
`ρ₁.prod ρ₂` is the sum of the two characters. This is the canonical owner theorem
`Representation.char_prod`. -/
/-- Proposition 2-2.1-2 (1): the character of a binary product representation is the sum of the
two characters. -/
theorem Representation.char_prod
    {G k V W : Type*} [Monoid G] [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) :
    (Representation.prod ρ σ).character = ρ.character + σ.character := by
  -- Evaluate the product representation pointwise and use additivity of trace on `V × W`.
  ext g
  simpa [Representation.character, Representation.prod] using
    (LinearMap.trace_prodMap' (ρ g) (σ g))

/- Proposition 2-2.1-2 (2): the character of the tensor-product representation is the product of
the two characters. This is the existing theorem `Representation.char_tensor`. -/
recall Representation.char_tensor

/-! ### Proposition_2_2_1_3 (from Chap02) -/
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

/-! ### Remark_2_2_1_2 (from Chap02) -/
universe u v

section

variable {G : Type u} {R : Type v} [Monoid G]

/-- Remark 2-2.1-2: a class function on a group factors through the canonical map to conjugacy
classes, equivalently it is constant on conjugacy classes. -/
@[mk_iff]
class IsClassFunction (f : G → R) : Prop where
  factorsThrough : f.FactorsThrough ConjClasses.mk

theorem IsClassFunction.eq_of_isConj {f : G → R} (hf : IsClassFunction f) {u v : G}
    (h : IsConj u v) : f u = f v :=
  hf.factorsThrough <| ConjClasses.mk_eq_mk_iff_isConj.mpr h

/-- A class function descends canonically to conjugacy classes. -/
def IsClassFunction.lift {f : G → R} (hf : IsClassFunction f) : ConjClasses G → R :=
  Quotient.lift f fun _ _ h ↦ hf.eq_of_isConj h

@[simp] theorem IsClassFunction.lift_mk {f : G → R} (hf : IsClassFunction f) (g : G) :
    hf.lift (ConjClasses.mk g) = f g :=
  rfl

@[simp] theorem IsClassFunction.lift_comp_mk {f : G → R} (hf : IsClassFunction f) :
    hf.lift ∘ ConjClasses.mk = f := by
  ext g
  rfl

theorem isClassFunction_iff_exists {f : G → R} :
    IsClassFunction f ↔ ∃ φ : ConjClasses G → R, f = φ ∘ ConjClasses.mk := by
  constructor
  · intro hf
    exact ⟨hf.lift, hf.lift_comp_mk.symm⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨fun _ _ h ↦ congrArg φ h⟩

theorem IsClassFunction.eq_of_mk_eq {f : G → R} (hf : IsClassFunction f) {u v : G}
    (h : ConjClasses.mk u = ConjClasses.mk v) : f u = f v :=
  hf.factorsThrough h

/-- Postcomposing a class function with any function preserves conjugacy invariance. -/
theorem IsClassFunction.comp {f : G → R} (hf : IsClassFunction f) {S : Type*} (φ : R → S) :
    IsClassFunction (φ ∘ f) := by
  refine ⟨?_⟩
  intro u v huv
  simpa using congrArg φ (hf.eq_of_mk_eq huv)

/-- Precomposing a function on conjugacy classes with `ConjClasses.mk` produces a class function
on `G`. -/
instance (f : ConjClasses G → R) :
    IsClassFunction (f ∘ ConjClasses.mk) :=
  ⟨fun _ _ h ↦ congrArg f h⟩

/-- Constant functions on a group are class functions. -/
instance (c : R) : IsClassFunction (fun _ : G ↦ c) :=
  ⟨fun _ _ _ ↦ rfl⟩

/-- The pointwise sum of two class functions is a class function. -/
instance [Add R] {f g : G → R} [IsClassFunction f] [IsClassFunction g] :
    IsClassFunction (f + g) :=
by
  refine ⟨?_⟩
  intro u v h
  change f u + g u = f v + g v
  simpa using congrArg₂ (· + ·)
    ((inferInstance : IsClassFunction f).factorsThrough h)
    ((inferInstance : IsClassFunction g).factorsThrough h)

/-- Scalar multiples of class functions are class functions. -/
instance {S : Type*} [SMul S R] (c : S) {f : G → R} [IsClassFunction f] :
    IsClassFunction (c • f) :=
by
  refine ⟨?_⟩
  intro u v h
  change c • f u = c • f v
  simpa using congrArg (c • ·) ((inferInstance : IsClassFunction f).factorsThrough h)

section Submodule

variable (R) [Semiring R]

/-- The `R`-submodule of `R`-valued functions on `G` that are constant on conjugacy classes. -/
def classFunctionSubmodule (G : Type u) [Monoid G] : Submodule R (G → R) where
  carrier := { f | IsClassFunction f }
  zero_mem' := by
    simpa using (inferInstance : IsClassFunction (fun _ : G ↦ (0 : R)))
  add_mem' := by
    intro f g hf hg
    letI : IsClassFunction f := hf
    letI : IsClassFunction g := hg
    simpa using (inferInstance : IsClassFunction (f + g))
  smul_mem' := by
    intro c f hf
    letI : IsClassFunction f := hf
    simpa using (inferInstance : IsClassFunction (c • f))

/-- A function lies in `classFunctionSubmodule R G` exactly when it is a class function. -/
@[simp] theorem mem_classFunctionSubmodule_iff (f : G → R) :
    f ∈ classFunctionSubmodule R G ↔ IsClassFunction f := by
  rfl

namespace classFunctionSubmodule

/-- Elements of `classFunctionSubmodule R G` are canonically viewed as `R`-valued functions on
`G`. -/
instance : CoeFun (classFunctionSubmodule R G) (fun _ ↦ G → R) where
  coe f := f.1

/-- The class-function submodule is canonically linearly equivalent to functions on the conjugacy
classes. -/
def equivFun (G : Type u) [Monoid G] : classFunctionSubmodule R G ≃ₗ[R] (ConjClasses G → R) :=
  { toFun := fun χ ↦
      let hf : IsClassFunction (χ : G → R) :=
        χ.2
      hf.lift
    invFun := fun χ ↦
      ⟨χ ∘ ConjClasses.mk, (mem_classFunctionSubmodule_iff R _).2 inferInstance⟩
    left_inv := fun χ ↦ by
      ext g
      rfl
    right_inv := fun χ ↦ by
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rfl
    map_add' := by
      intro χ ψ
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rfl
    map_smul' := by
      intro a χ
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rfl }

end classFunctionSubmodule

end Submodule

/-- The complex vector subspace of functions on `G` that are constant on conjugacy classes. -/
abbrev classFunctionSubspace (G : Type u) [Monoid G] : Submodule ℂ (G → ℂ) :=
  classFunctionSubmodule ℂ G

/-- A function lies in `classFunctionSubspace G` exactly when it is a class function. -/
@[simp] theorem mem_classFunctionSubspace_iff (f : G → ℂ) :
    f ∈ classFunctionSubspace G ↔ IsClassFunction f := by
  rfl

end

section

variable {G : Type u} {R : Type v} [Monoid G]

variable [Zero R] [One R]

namespace ConjClasses

/-- The `R`-valued indicator of a conjugacy class, viewed as a class function on `G`. -/
noncomputable def indicator (c : ConjClasses G) : G → R := by
  classical
  exact c.carrier.indicator 1

@[simp] theorem indicator_apply_eq_one (c : ConjClasses G) {g : G}
    (h : ConjClasses.mk g = c) : c.indicator g = 1 := by
  classical
  simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, h]

@[simp] theorem indicator_apply_eq_zero (c : ConjClasses G) {g : G}
    (h : ConjClasses.mk g ≠ c) : c.indicator g = 0 := by
  classical
  simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, h]

/-- The indicator of a conjugacy class is a class function. -/
instance (c : ConjClasses G) : IsClassFunction (c.indicator : G → R) :=
by
  refine ⟨?_⟩
  intro x y hxy
  by_cases hx : ConjClasses.mk x = c
  · have hy : ConjClasses.mk y = c :=
      hxy.symm.trans hx
    simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, hx, hy]
  · have hy : ConjClasses.mk y ≠ c := fun hy ↦
      hx <| hxy.trans hy
    simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, hx, hy]

section Submodule

variable [Semiring R]

/-- The `R`-valued indicator of a conjugacy class, regarded as an element of the canonical
class-function submodule. -/
noncomputable def indicatorClassFunctionSubmodule (c : ConjClasses G) :
    classFunctionSubmodule R G :=
  ⟨c.indicator, (mem_classFunctionSubmodule_iff R _).2 inferInstance⟩

@[simp] theorem coe_indicatorClassFunctionSubmodule (c : ConjClasses G) :
    (c.indicatorClassFunctionSubmodule : G → R) = c.indicator :=
  rfl

end Submodule

/-- The complex-valued indicator of a conjugacy class, regarded as an element of the canonical
class-function subspace. -/
noncomputable abbrev indicatorClassFunction (c : ConjClasses G) : classFunctionSubspace G :=
  c.indicatorClassFunctionSubmodule (R := ℂ)

@[simp] theorem coe_indicatorClassFunction (c : ConjClasses G) :
    (c.indicatorClassFunction : G → ℂ) = c.indicator :=
  rfl

end ConjClasses

end

section

variable {G : Type u} {R : Type v} [Group G]

/-- A class function satisfies the source-facing identity `f (u * v) = f (v * u)`. -/
-- Proof sketch: the elements `u * v` and `v * u` are conjugate, with witness `v`,
-- so the defining conjugacy-invariance property applies.
theorem IsClassFunction.map_mul_comm {f : G → R} (hf : IsClassFunction f) (u v : G) :
    f (u * v) = f (v * u) :=
  hf.eq_of_isConj <| isConj_iff.2 ⟨v, by simp [mul_assoc]⟩

end

/-! ### Corollary_2_2_2_2 (from Chap02) -/
open scoped BigOperators
noncomputable section

universe u v w u₁ u₂

namespace Representation

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)]
variable {V1 : Type v} [AddCommGroup V1] [Module k V1]
variable {V2 : Type w} [AddCommGroup V2] [Module k V2]
variable {ι1 : Type u₁} [Fintype ι1]
variable {ι2 : Type u₂} [Fintype ι2]

/- Layer triage for Corollary 2-2.2-2 (1):
* core/canonical: the owner abstractions are `(ρ1.linHom ρ2).averageMap`,
  `invariantsEquivIntertwiningMap`, and `IntertwiningMap`.
* source-facing: the averaged conjugates of an arbitrary linear map vanish under irreducibility
  and nonisomorphism.
* bridge/view: the basis-entry formula below is only a coordinate expression of the canonical
  averaged intertwiner. -/
-- Proof sketch: `(ρ1.linHom ρ2).averageMap h` is invariant in `ρ1.linHom ρ2`, hence
-- `invariantsEquivIntertwiningMap` turns it into an intertwining map. Under irreducibility and
-- nonisomorphism, the owner instance `Subsingleton (IntertwiningMap ρ1 ρ2)` forces that map to
-- vanish.
/-- Corollary 2-2.2-2 (1): if `ρ1` and `ρ2` are nonisomorphic irreducible representations over a
field in which `|G|` is invertible, then the average of the conjugates of any linear map
`h : V1 →ₗ[k] V2` is zero. -/
theorem averageMap_linHom_eq_zero_of_not_isomorphic
    (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
    [ρ1.IsIrreducible] [ρ2.IsIrreducible]
    (h : V1 →ₗ[k] V2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    (ρ1.linHom ρ2).averageMap h = 0 := by
  have hinter :
      ρ1.invariantsEquivIntertwiningMap ρ2
          ⟨(ρ1.linHom ρ2).averageMap h, (ρ1.linHom ρ2).averageMap_invariant h⟩ = 0 := by
    exact intertwiningMap_eq_zero_of_not_isomorphic ρ1 ρ2 _ hρ
  simpa using congrArg IntertwiningMap.toLinearMap hinter

/- Bridge/view from the canonical averaged intertwiner to the source-facing matrix-coefficient
formula: this computes the matrix entry of the averaged canonical basis vector
`b1.linearMap b2 (j2, j1)` of `V1 →ₗ[k] V2`. -/
open scoped Classical in
/-- The `(i2, i1)` matrix entry of the averaged basis map `b1.linearMap b2 (j2, j1)` is the
normalized sum of the corresponding matrix-coefficient products. -/
theorem averageMap_linHom_basis_entry_eq
    (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
    (b1 : Module.Basis ι1 k V1) (b2 : Module.Basis ι2 k V2)
    (i1 j1 : ι1) (i2 j2 : ι2) :
    (((ρ1.linHom ρ2).averageMap (b1.linearMap b2 (j2, j1))).toMatrix b1 b2 i2 i1) =
      (Fintype.card G : k)⁻¹ *
        ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 := by
  let τ : Representation k G (V1 →ₗ[k] V2) := ρ1.linHom ρ2
  let e : V1 →ₗ[k] V2 := b1.linearMap b2 (j2, j1)
  have he_apply (x : V1) : e x = (b1.repr x j1) • b2 j2 := by
    dsimp [e]
    rw [← b1.sum_repr x, map_sum]
    simp [Module.Basis.linearMap_apply_apply]
  have havg_apply :
      (τ.averageMap e) (b1 i1) =
        (Fintype.card G : k)⁻¹ •
          ∑ d : G, ((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1) := by
    rw [averageMap, GroupAlgebra.average, map_smul, map_sum]
    simp [LinearMap.smul_apply, LinearMap.sum_apply, invOf_eq_inv]
  have hentry_fun :
      b2.repr ((τ.averageMap e) (b1 i1)) =
        (Fintype.card G : k)⁻¹ •
          ∑ d : G,
            b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) := by
    simpa [map_smul, map_sum] using congrArg b2.repr havg_apply
  have hentry :
      ((τ.averageMap e).toMatrix b1 b2 i2 i1) =
        (Fintype.card G : k)⁻¹ *
          ∑ d : G,
            b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) i2 := by
    rw [LinearMap.toMatrix_apply]
    simpa using congrArg (fun f ↦ f i2) hentry_fun
  have hsum_terms :
      ∑ d : G, (ρ2 d).toMatrix b2 b2 i2 j2 * (ρ1 d⁻¹).toMatrix b1 b1 j1 i1 =
        ∑ d : G,
          b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) i2 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [asAlgebraHom_of, linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, he_apply,
      LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [map_smul, mul_comm]
  have hreindex :
      ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 =
        ∑ t : G, (ρ2 t).toMatrix b2 b2 i2 j2 * (ρ1 t⁻¹).toMatrix b1 b1 j1 i1 := by
    simpa [inv_inv] using
      (Equiv.sum_comp (Equiv.inv G)
        (fun t : G ↦ (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1)).symm
  calc
    ((ρ1.linHom ρ2).averageMap (b1.linearMap b2 (j2, j1))).toMatrix b1 b2 i2 i1
      = (Fintype.card G : k)⁻¹ *
          ∑ d : G, b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) i2 := by
            simpa [τ, e] using hentry
    _ = (Fintype.card G : k)⁻¹ *
          ∑ d : G, (ρ2 d).toMatrix b2 b2 i2 j2 * (ρ1 d⁻¹).toMatrix b1 b1 j1 i1 := by
            rw [← hsum_terms]
    _ = (Fintype.card G : k)⁻¹ *
          ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 := by
            rw [← hreindex]

end

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [Invertible (Module.finrank k V : k)]

/- Layer triage for Corollary 2-2.2-2 (2):
* core/canonical: `IntertwiningMap ρ ρ`, the averaged projector `(ρ.linHom ρ).averageMap`, and
  Schur's lemma in Proposition `2-2.2-1`.
* source-facing: the average of the conjugates of `h` is the scalar homothety with ratio
  `(1 / dim V) * Tr(h)`.
* bridge/view: the proof identifies the scalar through the canonical trace invariance under
  conjugation. -/
-- Proof sketch: send `(ρ.linHom ρ).averageMap h` through
-- `invariantsEquivIntertwiningMap` to obtain an equivariant endomorphism, apply Proposition
-- `2-2.2-1 (2)` to see it is scalar, then identify that scalar by comparing traces, using trace
-- invariance under conjugation, and dividing by `dim V`.
/-- Corollary 2-2.2-2 (2): for an irreducible finite-dimensional representation over an
algebraically closed field in which `|G|` and `dim V` are invertible, the average of the
conjugates of an endomorphism is the homothety of ratio `(1 / n) Tr(h)`, where `n = dim V`. -/
theorem averageMap_linHom_self_eq_trace_smul_id
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (h : V →ₗ[k] V) :
    (ρ.linHom ρ).averageMap h =
      ((Module.finrank k V : k)⁻¹ * LinearMap.trace k V h) • LinearMap.id := by
  let τ : Representation k G (V →ₗ[k] V) := ρ.linHom ρ
  obtain ⟨c, hc⟩ := intertwiningMap_eq_smul_id ρ
    (ρ.invariantsEquivIntertwiningMap ρ ⟨τ.averageMap h, τ.averageMap_invariant h⟩)
  have havg : τ.averageMap h = c • LinearMap.id := by
    simpa [τ] using congrArg IntertwiningMap.toLinearMap hc
  have htrace_conj (g : G) :
      LinearMap.trace k V ((τ.asAlgebraHom (MonoidAlgebra.of k G g)) h) =
        LinearMap.trace k V h := by
    let u : (V →ₗ[k] V)ˣ :=
      { val := ρ g
        inv := ρ g⁻¹
        val_inv := by simpa using (ρ.map_mul g g⁻¹).symm
        inv_val := by simpa using (ρ.map_mul g⁻¹ g).symm }
    simpa [u, asAlgebraHom_of, linHom_apply, mul_assoc] using
      (LinearMap.trace_conj k h u)
  have htrace_avg :
      LinearMap.trace k V (τ.averageMap h) = LinearMap.trace k V h := by
    rw [averageMap, GroupAlgebra.average, map_smul, map_sum,
      LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    simp_rw [htrace_conj]
    rw [Finset.sum_const, Finset.card_univ]
    simpa [smul_eq_mul, mul_assoc] using
      (invOf_mul_cancel_left (Fintype.card G : k) (LinearMap.trace k V h))
  have hc_trace : c * (Module.finrank k V : k) = LinearMap.trace k V h := by
    calc
      c * (Module.finrank k V : k) = LinearMap.trace k V (c • (LinearMap.id : V →ₗ[k] V)) := by
        simp [LinearMap.trace_id, smul_eq_mul]
      _ = LinearMap.trace k V (τ.averageMap h) := by rw [havg]
      _ = LinearMap.trace k V h := htrace_avg
  calc
    (ρ.linHom ρ).averageMap h = c • LinearMap.id := by simpa [τ] using havg
    _ = ((Module.finrank k V : k)⁻¹ * LinearMap.trace k V h) • LinearMap.id := by
          congr 1
          calc
            c = ⅟(Module.finrank k V : k) * ((Module.finrank k V : k) * c) := by
                  symm
                  exact invOf_mul_cancel_left (Module.finrank k V : k) c
            _ = (Module.finrank k V : k)⁻¹ * LinearMap.trace k V h := by
                  rw [mul_comm (Module.finrank k V : k) c, hc_trace, invOf_eq_inv]

end

end Representation
