import stacks_project.Chap10.Lemma_10_52_13

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
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
/-- Lemma 10.52.14: for flat local homomorphisms `A → B → C` of local rings, the length of the
closed fiber of `A → B` times the length of the closed fiber of `B → C` equals the length of the
closed fiber of the composite `A → C`. -/
theorem length_closed_fiber_mul_length_closed_fiber_eq_length_composite_closed_fiber :
    Module.length ClosedFiberAB ClosedFiberAB * Module.length ClosedFiberBC ClosedFiberBC =
      Module.length ClosedFiberAC ClosedFiberAC := by
  sorry

end Length
