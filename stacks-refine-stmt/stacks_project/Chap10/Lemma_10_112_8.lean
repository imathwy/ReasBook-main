import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

open IsLocalRing
open scoped TensorProduct

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-- The canonical quotient presentation of the closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`. -/
noncomputable def closedFiberQuotAlgEquiv : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
  (Algebra.TensorProduct.congr (.symm <| .ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)

/-- The canonical closed fiber is regular as soon as its quotient presentation
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` is regular. -/
theorem isRegularLocalRing_closedFiber_of_quotient
    [IsRegularLocalRing (S ⧸ 𝔪S)] :
    IsRegularLocalRing ClosedFiber := by
  simpa using
    (IsRegularLocalRing.of_ringEquiv closedFiberQuotAlgEquiv.toRingEquiv.symm :
      IsRegularLocalRing ClosedFiber)

end

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsRegularLocalRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain sampling pass:
* primary domain: local commutative algebra of closed fibers of local ring maps;
* sampled owner declarations:
  - `Ideal.Fiber`, the canonical fiber-ring owner `κ(p) ⊗[R] S`;
  - the induced local-ring instance on `ClosedFiber` for local maps;
  - the canonical quotient view `ClosedFiber ≃ₐ[R] S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`;
  - downstream chapter usage already centered on `((maximalIdeal A).Fiber B)`, for example in
    `Lemma_15_78_6`.

Source/core/bridge triage:
* source-facing: the regular-closed-fiber criterion for a flat local homomorphism of local rings;
* core/canonical: the owner predicate `IsRegularLocalRing` on the owner fiber ring
  `ClosedFiber`;
* bridge/view: the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`.

Primitive data are the ambient flat local algebra map and regularity of the closed fiber. The
local and Noetherian structure on `ClosedFiber` are derived from the owner assumption
`IsRegularLocalRing ClosedFiber`, so no extra wrapper or auxiliary data should be introduced here.
-/
-- Proof sketch: combine Lemma `10.112.7` with the canonical criterion
-- `isRegularLocalRing_iff` on `R`, `S`, and the owner closed fiber `ClosedFiber`. The dimension
-- formula gives `dim S = dim R + dim ClosedFiber`, while generators of `maximalIdeal R` together
-- with lifts of generators of the maximal ideal of `ClosedFiber` generate `maximalIdeal S`;
-- comparing the resulting generator count with the dimension yields regularity.
/-- Lemma 10.112.8: if `R → S` is a flat local homomorphism of local Noetherian rings, `R` is a
regular local ring, and the closed fibre `((maximalIdeal R).Fiber S)`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, is a regular local ring, then `S` is a
regular local ring. -/
theorem isRegularLocalRing_of_flat_localHom_of_regular_closedFiber
    (hclosedFiber : IsRegularLocalRing ClosedFiber) :
    IsRegularLocalRing S := sorry

end
