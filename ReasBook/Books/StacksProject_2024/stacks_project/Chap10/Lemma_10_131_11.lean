import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

variable (I : Ideal S) (n : ℕ)

local notation "Sbar" => S ⧸ I ^ (n + 1)
local notation "Tbar" => S ⧸ I ^ n

/-- The canonical quotient-transition algebra structure on `S / I^n` over `S / I^(n + 1)`. -/
instance quotientPowSuccAlgebra : Algebra Sbar Tbar :=
  RingHom.toAlgebra (Ideal.Quotient.factorPowSucc I n)

/-- The quotient transition `S → S / I^(n + 1) → S / I^n` is a scalar tower. -/
instance quotientPowSuccIsScalarTower : IsScalarTower S Sbar Tbar :=
  IsScalarTower.of_algebraMap_eq' rfl

/- Domain triage:
- primary domain: base change of Kähler differentials along the quotient tower
  `S → S / I^(n + 1) → S / I^n`;
- sampled owner API:
  `KaehlerDifferential.mapBaseChange`,
  `TensorProduct.AlgebraTensorModule.lTensor`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`,
  `Ideal.Quotient.factorPowSucc`;
- source-facing layer: the canonical comparison on the actual base-changed modules
  `Tbar ⊗[S] Ω[S⁄R]` and `Tbar ⊗[Sbar] Ω[Sbar⁄R]`;
- core/canonical owner: `KaehlerDifferential.mapBaseChange R S Sbar`, base-changed further along
  `Sbar → Tbar`;
- bridge/view: if one wants the textbook tensor order
  `Ω[S⁄R] ⊗[S] Tbar ≃ Ω[S / I^(n + 1)⁄R] ⊗[S / I^(n + 1)] Tbar`, it is obtained afterward
  from the source-facing comparison by the standard tensor symmetries.

The previous file encoded only the restricted-scalars shadow of this comparison. The primitive
owner is the base-change map on Kähler differentials, and the correct public statement is its
further base change along `Sbar → Tbar`.
-/

private noncomputable def kaehlerDifferentialTensorQuotientPowSuccLinearMap :
    Tbar ⊗[S] Ω[S⁄R] →ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R] :=
  lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar) ∘ₗ
    (cancelBaseChange S Sbar Tbar Tbar Ω[S⁄R]).symm.toLinearMap

-- Proof sketch: apply Lemma `10.131.9` to the surjection `S → S / I^(n + 1)` with kernel
-- `I^(n + 1)`, then tensor the resulting exact sequence with `S / I^n`. The map from
-- `I^(n + 1)/(I^(2n + 2))` dies modulo `I^n` because `d(I^(n + 1)) ⊆ I^n Ω[S⁄R]` by Leibniz, so
-- the induced tensor map is bijective.
private theorem kaehlerDifferentialTensorQuotientPowSuccLinearMap_bijective :
    Function.Bijective
      ((kaehlerDifferentialTensorQuotientPowSuccLinearMap I n) :
        Tbar ⊗[S] Ω[S⁄R] →ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R]) := sorry

/-- Lemma 10.131.11: the quotient morphism `S → S / I^(n + 1)` induces the canonical
`S / I^n`-linear identification of the two base changes
`S / I^n ⊗[S] Ω[S⁄R] ≃ S / I^n ⊗[S / I^(n + 1)] Ω[S / I^(n + 1)⁄R]`.
The source text states this for `n ≥ 1`, but that hypothesis is mathematically redundant: the
`n = 0` case is the trivial zero-module comparison. -/
noncomputable def kaehlerDifferentialTensorQuotientPowSuccEquiv
    : Tbar ⊗[S] Ω[S⁄R] ≃ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R] :=
  LinearEquiv.ofBijective
    (kaehlerDifferentialTensorQuotientPowSuccLinearMap I n)
    (kaehlerDifferentialTensorQuotientPowSuccLinearMap_bijective I n)

end
