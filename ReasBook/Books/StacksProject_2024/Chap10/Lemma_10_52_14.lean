import StacksProject_2024.Chap10.Lemma_10_52_13

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct
universe u v w

section Length

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
variable [Module.Flat A B] [Module.Flat B C]

local notation "ClosedFiberAB" => Ideal.Fiber (maximalIdeal A) B
local notation "ClosedFiberBC" => Ideal.Fiber (maximalIdeal B) C
local notation "ClosedFiberAC" => Ideal.Fiber (maximalIdeal A) C

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-
Domain triage:
* primary domain: closed fibers of local ring maps, tensor base change, and finite module length;
* sampled owner API: `Ideal.Fiber`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`, `LinearEquiv.length_eq`, and
  `length_base_change_eq_length_mul_closed_fiber`;
* source-facing layer: the textbook multiplicativity formula for lengths of closed fibers in a
  composite of flat local maps;
* core/canonical owners: `Ideal.Fiber` for the closed fiber itself and the tensor-product
  base-change equivalences for identifying the composite closed fiber with the base change of the
  first closed fiber along `B → C`;
* bridge/view: the theorem remains source-facing, while the proof derives its two length rewrites
  and the composite-fiber identification from the owner abstractions already fixed in the previous
  item and in mathlib.
-/

-- Proof sketch: apply the base-change length formula of Lemma 10.52.13 to the flat local map
-- `B → C` and the `B`-module `ClosedFiberAB`. The tensor product of this closed fiber with `C`
-- identifies with `ClosedFiberAC`, giving the stated multiplicativity of closed-fiber lengths.
/-- Helper for Lemma 10.52.14: extending `maximalIdeal A` along `A → B → C` agrees with
extension along the composite `A → C`. -/
lemma map_map_maximalIdeal_eq :
    Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) (maximalIdeal A)) =
      Ideal.map (algebraMap A C) (maximalIdeal A) := by
  -- Collapse the iterated ideal extension using the scalar tower identity.
  simpa [IsScalarTower.algebraMap_eq A B C] using
    (Ideal.map_map (I := maximalIdeal A) (algebraMap A B) (algebraMap B C))

/-- Helper for Lemma 10.52.14: the quotient model `B / 𝔪_A B` has the same `B`-module length as
the canonical closed fiber of `A → B`. -/
lemma closedFiberAB_quotient_length_eq :
    Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) =
      Module.length ClosedFiberAB ClosedFiberAB := by
  -- First identify the quotient with the canonical closed fiber, then compare scalar actions.
  calc
    Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) =
        Module.length B ClosedFiberAB := by
          simpa using
            (closedFiber_quotient_equiv (A := A) (B := B)).toLinearEquiv.length_eq
    _ = Module.length ClosedFiberAB ClosedFiberAB :=
      closedFiber_length_over_base_eq_self (A := A) (B := B)

/-- Helper for Lemma 10.52.14: base changing the quotient model `B / 𝔪_A B` along `B → C`
produces the canonical closed fiber of the composite `A → C`, with the same `C`-module length. -/
lemma base_change_quotient_length_eq_closedFiberAC_length :
    Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
      Module.length ClosedFiberAC ClosedFiberAC := by
  letI : IsLocalHom (algebraMap A C) := by
    -- The composite of local maps is local, so the `A → C` closed-fiber API is available.
    simpa [IsScalarTower.algebraMap_eq A B C] using
      (RingHom.isLocalHom_comp (algebraMap B C) (algebraMap A B))
  letI : Module.Flat A C := Module.Flat.trans A B C
  -- Rewrite the tensor product as the quotient by the extended ideal.
  calc
    Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
        Module.length C
          (C ⧸ Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) (maximalIdeal A))) := by
          simpa using
            ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
              C (Ideal.map (algebraMap A B) (maximalIdeal A))).symm.toLinearEquiv.length_eq :
                Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
                  Module.length C
                    (C ⧸ Ideal.map (algebraMap B C)
                      (Ideal.map (algebraMap A B) (maximalIdeal A))))
    -- Collapse the iterated ideal extension to the composite one.
    _ = Module.length C (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) := by
          rw [map_map_maximalIdeal_eq]
    -- Identify that quotient with the canonical closed fiber of the composite map.
    _ = Module.length C ClosedFiberAC := by
          simpa using
            (closedFiber_quotient_equiv (A := A) (B := C)).toLinearEquiv.length_eq
    _ = Module.length ClosedFiberAC ClosedFiberAC :=
      closedFiber_length_over_base_eq_self (A := A) (B := C)

/-- Lemma 10.52.14: for flat local homomorphisms `A → B → C` of local rings, the length of the
closed fiber of `A → B` times the length of the closed fiber of `B → C` equals the length of the
closed fiber of the composite `A → C`. -/
theorem length_closed_fiber_mul_length_closed_fiber_eq_length_composite_closed_fiber :
    Module.length ClosedFiberAB ClosedFiberAB * Module.length ClosedFiberBC ClosedFiberBC =
      Module.length ClosedFiberAC ClosedFiberAC := by
  -- Apply Lemma 10.52.13 to `B → C` and the quotient model `B / 𝔪_A B`.
  have hbaseChange :
      Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
        Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) *
          Module.length ClosedFiberBC ClosedFiberBC :=
    length_base_change_eq_length_mul_closed_fiber
      (A := B) (B := C) (M := B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
  -- Rewrite the source quotient and its base change as the canonical closed fibers.
  calc
    Module.length ClosedFiberAB ClosedFiberAB * Module.length ClosedFiberBC ClosedFiberBC =
        Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) *
          Module.length ClosedFiberBC ClosedFiberBC := by
          rw [← closedFiberAB_quotient_length_eq]
    _ = Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) := by
          exact hbaseChange.symm
    _ = Module.length ClosedFiberAC ClosedFiberAC :=
          base_change_quotient_length_eq_closedFiberAC_length

end Length
