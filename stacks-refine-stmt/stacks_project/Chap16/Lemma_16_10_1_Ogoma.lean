import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Submodule

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (S : Submonoid A)

local notation "Aₛ" => Localization S
local notation "Mₛ" => LocalizedModule S M

/-
Domain-style sampling:
- primary domain: commutative algebra of finite modules over a Noetherian ring, localized modules,
  and scalar-torsion submodules;
- sampled owner API:
  `Submodule.torsionBy`,
  `Submodule.mem_torsionBy_iff`,
  `isSMulRegular_iff_torsionBy_eq_bot`,
  `LinearMap.lsmul_eq_distribSMultoLinearMap`;
- best owner abstraction: `Submodule.torsionBy`; the current kernel-of-`LinearMap.lsmul` phrasing
  is only the low-level bridge/view;
- primitive data: the ambient ring/module, the localization `Localization S`, and the scalar `π`;
  the kernel of scalar multiplication is derived from the owner `Submodule.torsionBy`, so it
  should not remain the public surface.

Layer triage:
- `source-facing`: Ogoma's stabilization lemma itself;
- `core/canonical`: `Submodule.torsionBy`;
- `bridge/view`: `LinearMap.ker (LinearMap.lsmul ...)`.
-/

-- Proof sketch: Let `K = M[π]` and let `K'` be the preimage in `M` of
-- `(S⁻¹M)[π^2]`. The hypothesis says that `K'/K` localizes to zero. Since
-- `K'/K` is a finite `A`-module over a Noetherian ring, some `s ∈ S` annihilates `K'/K`,
-- and then the same denominator works after replacing `s` by any positive power.
/-- Lemma 16.10.1 (Ogoma): if the `π`-torsion and `π^2`-torsion submodules of `S⁻¹M` agree, then
some `s ∈ S` makes the `s^n * π`-torsion and `(s^n * π)^2`-torsion submodules of `M` agree for
every positive integer `n`. -/
theorem exists_mem_submonoid_torsionBy_eq_of_localized (π : A)
    (htors :
      torsionBy Aₛ Mₛ (algebraMap A Aₛ π) = torsionBy Aₛ Mₛ ((algebraMap A Aₛ π) ^ 2)) :
    ∃ s : S, ∀ n : ℕ+,
      torsionBy A M (((s : A) ^ (n : ℕ)) * π) =
        torsionBy A M ((((s : A) ^ (n : ℕ)) * π) ^ 2) := sorry

end
