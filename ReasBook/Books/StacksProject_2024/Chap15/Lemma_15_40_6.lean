import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsNoetherianRing B] [IsCompleteLocalRing B]
variable [Algebra (ResidueField A) B]

local notation "κA" => ResidueField A

/- Domain-style sampling for Lemma 15.40.6:
- primary domain: complete local commutative algebra, adic formal smoothness, and closed fibers of
  local maps;
- sampled owner declarations:
  * `Ideal.Fiber`,
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.formally_smooth_for_adic_baseChange`,
  * `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`;
- best owner abstraction: the closed fiber of the sought lift is canonically
  `Ideal.Fiber (maximalIdeal A) C`; the tensor-product model `ResidueField A ⊗[A] C` is only a
  bridge/view of that owner;
- primitive data: the complete local `ResidueField A`-algebra `B` and the adic formal smoothness
  hypothesis on `ResidueField A → B`;
- derived API: existence of a complete local `A`-algebra `C` whose structure map is adically
  formally smooth together with an explicit closed-fiber equivalence
  `Ideal.Fiber (maximalIdeal A) C ≃ₐ[ResidueField A] B`.

Source/core/bridge triage:
- `source-facing`: the existence of a formally smooth complete-local lift with prescribed closed
  fiber;
- `core/canonical`: `Ideal.Fiber` and `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-product presentation of the closed fiber.
-/
-- Proof sketch: choose the power-series presentation from Lemma `15.39.3` for the local map from a
-- Cohen ring or residue-field power series ring into `B`, then use regularity of the special
-- fiber to kill generators of the kernel so that the reduced presentation has special fiber
-- exactly `B`. Proposition `15.40.5` makes the resulting source formally smooth over the base
-- presentation ring, and Lemma `15.37.8` transports formal smoothness after base change along
-- the map to `A`.
/-- Lemma 15.40.6: if `A` is a Noetherian complete local ring and `B` is a Noetherian complete
local `ResidueField A`-algebra such that `ResidueField A → B` is formally smooth for the
`maximalIdeal B`-adic topology, then there exists a Noetherian complete local `A`-algebra `C`
whose structure map `A → C` is local and formally smooth for the `maximalIdeal C`-adic topology,
and whose closed fiber `Ideal.Fiber (maximalIdeal A) C`, canonically presented by
`ResidueField A ⊗[A] C`, is isomorphic to `B` over `ResidueField A`. -/
theorem exists_completeLocal_formallySmooth_lift_with_closedFiber
    (hfs : (algebraMap κA B).formally_smooth_for_adic (maximalIdeal B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C))
      (_ : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] B),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) := sorry

end
