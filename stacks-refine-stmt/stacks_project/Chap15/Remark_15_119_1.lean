import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ExteriorAlgebra

universe u v

noncomputable section

namespace Module

/- Domain-style sampling for Remark 15.119.1:
- primary domain: determinant lines of finite projective modules, realized via exterior algebra;
- sampled owner declarations of the same kind:
  `ExteriorAlgebra.exteriorPower`,
  `ExteriorAlgebra.ι`,
  `Module.Invertible`,
  `(tensorLeft (ModuleCat.of R M)).IsEquivalence`,
  `ModuleCat.tensorLeft_isEquivalence_iff_moduleInvertible`;
- best owner abstraction:
  `source-facing`: the determinant line of a finite projective `R`-module `M`, realized by the
  annihilator owner `Module.det R M`;
  `core/canonical`: the Chapter `15` owner
  `(tensorLeft (ModuleCat.of R (Module.det R M))).IsEquivalence` for invertibility statements;
  `bridge/view`: the exterior-algebra annihilator description from the remark, together with the
  constant-rank identification with the top exterior power `⋀[R]^r M`;
- primitive vs. derived:
  primitive public data is the annihilator owner `Module.det R M` for an arbitrary `R`-module;
  the source-faithful finite-projective determinant-line interpretation, the constant-rank
  top-exterior-power comparison, and the specialized `Module.Invertible` statement are derived
  bridge API built from that owner.

This file therefore keeps the annihilator submodule as the owner, and places the finite-projective
content of Remark `15.119.1` in the derived bridge results that identify this owner with the
determinant line and its invertibility consequences.
-/

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The exterior-algebra annihilator submodule used in Remark `15.119.1` to realize the
determinant line of a finite projective module. The finite-projective content is carried by the
bridge results below, not by this owner itself. -/
abbrev det : Submodule R (ExteriorAlgebra R M) :=
  ⨅ m : M, (LinearMap.mulLeft R (ι R m)).ker

scoped[DeterminantLine] notation3:max "det(" M ")" => Module.det _ M

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped DeterminantLine

/-- Membership in `det(M)` is equivalent to being annihilated by left multiplication by
every degree-one generator of `ExteriorAlgebra R M`. -/
@[simp]
theorem mem_det_iff (x : ExteriorAlgebra R M) :
    x ∈ det(M) ↔ ∀ m : M, ι R m * x = 0 := by
  simp [Module.det]

section

variable [Module.Finite R M] [Module.Projective R M]

/-- Under a constant rank hypothesis, the determinant line agrees with the top exterior power
inside `ExteriorAlgebra R M`. This presents the exterior-algebra annihilator owner as the
standard top-exterior-power model under stronger assumptions. -/
theorem det_eq_topExteriorPower_of_rankAtStalk_eq (r : ℕ)
    (hM : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) :
    det(M) = ⋀[R]^r M := by
  sorry

/-- The determinant line of a finite projective module is invertible as an `R`-module. Via
Definition `15.118.1`, this is equivalent to the Chapter `15` tensor-left invertibility owner. -/
instance det_invertible : Module.Invertible R (Module.det R M) :=
  by
    sorry

end

end Module

end
