import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_104_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-
Domain-style sampling pass:
* primary domain: local commutative algebra of Cohen-Macaulay local rings under flat local
  homomorphisms, with the closed fiber carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Module.CohenMacaulay`,
  `Ideal.Fiber`,
  `depth_target_eq_depth_source_add_depth_closed_fiber`,
  `Module.supportDim_self_eq_ringKrullDim`;
* best owner abstraction: the Cohen-Macaulay conditions should stay on the owner
  `Module.CohenMacaulay`, and the closed fiber should be expressed by the canonical ring
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`; the quotient `S ⧸ 𝔪S` is only a bridge/view.

Primitive data vs. derived API:
* primitive data: only the flat local algebra map `R → S`;
* derived API: the quotient presentation `S ⧸ 𝔪S` of the closed fiber and the induced local and
  Noetherian instances used to formulate the owner statement on `ClosedFiber`.

Source/core/bridge triage:
* `source-facing`: the Stacks equivalence saying that `S` is Cohen-Macaulay iff both `R` and the
  closed fiber are Cohen-Macaulay;
* `core/canonical`: `Module.CohenMacaulay` and `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`;
* `bridge/view`: the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`.
-/

private noncomputable def closedFiberQuotEquiv : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
  (Algebra.TensorProduct.congr (.symm <| .ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)

/-- The canonical closed fiber `ClosedFiber = (maximalIdeal R).Fiber S` is a local ring. -/
local instance closedFiber_isLocalRing : IsLocalRing ClosedFiber := by
  have h𝔪S : 𝔪S < (⊤ : Ideal S) :=
    IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
  letI : Nontrivial (S ⧸ 𝔪S) :=
    Quotient.nontrivial_iff.mpr h𝔪S.ne
  letI : IsLocalRing (S ⧸ 𝔪S) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔪S) Ideal.Quotient.mk_surjective
  exact (closedFiberQuotEquiv.toRingEquiv.symm : S ⧸ 𝔪S ≃+* ClosedFiber).isLocalRing

/-- The canonical closed fiber inherits Noetherianity from its quotient presentation `S ⧸ 𝔪S`. -/
local instance closedFiber_isNoetherianRing : IsNoetherianRing ClosedFiber :=
  isNoetherianRing_of_ringEquiv (S ⧸ 𝔪S) closedFiberQuotEquiv.toRingEquiv.symm

-- Proof sketch: combine Lemma `10.163.2`, which gives the additivity formula for the depth of
-- `S`, with Lemma `10.112.7`, which gives the corresponding dimension formula for the canonical
-- closed fiber `ClosedFiber`. Then rewrite the Cohen-Macaulay condition on `R`, `S`, and
-- `ClosedFiber` as the equality between depth and Krull dimension, using the quotient view only
-- internally, and compare the two formulas.
/-- Lemma 10.163.3: for a flat local homomorphism `R → S` of local Noetherian rings, `S` is
Cohen-Macaulay if and only if both `R` and the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently `S / 𝔪_R S`, are Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_source_and_closedFiber :
    Module.CohenMacaulay S S ↔
      Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiber ClosedFiber := sorry

end
