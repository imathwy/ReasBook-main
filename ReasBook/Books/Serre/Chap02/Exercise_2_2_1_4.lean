import Serre.Chap02.Proposition_2_2_1_2
import Serre.Chap01.Definition_1_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

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
