import Mathlib
import StacksProject_2024.Chap15.Definition_15_89_1
import StacksProject_2024.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

/- Domain-style sampling:
- primary domain: ideal-power torsion modules and derived completeness over a commutative ring;
- sampled owner-side declarations:
  `Module.IsIdealPowerTorsion`,
  `Module.isIdealPowerTorsion_iff`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `Module.exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus`;
- best owner abstraction: the source-facing theorem should take the chapter owner predicate
  `Module.IsIdealPowerTorsion I M` together with the module-level derived-completeness predicate
  `M.IsDerivedCompleteWithRespectTo I`;
- primitive data: the ideal `I`, the module `M`, finite generation of `I`, ideal-power torsion of
  `M`, and derived completeness of `M` with respect to `I`;
- derived API: the elementwise annihilation criterion
  `Module.isIdealPowerTorsion_iff` and the support/annihilator reformulation of the conclusion.

Layer triage:
- `source-facing`: Bhatt's annihilation theorem for derived-complete ideal-power torsion modules;
- `core/canonical`: `Module.IsIdealPowerTorsion` and `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: the elementwise torsion criterion and the equivalent annihilator form
  `(I ^ n) • (⊤ : Submodule A M) = ⊥`. -/

-- Proof sketch: first reduce to the principal case by choosing finitely many generators of `I`
-- and proving that each generator acts nilpotently on `M`. For `I = (f)`, use
-- Example `15.94.3` to represent `M` as the cokernel of a map `u : K → L` between `(f)`-adically
-- complete modules with zero `f`-torsion. The `f`-power torsion hypothesis implies
-- `L = ⋃ₙ {x | f^n x ∈ u(K)}`; the open mapping lemmas then show `u(K)` is open in `L`, so some
-- power of `f` lands inside `u(K)`, which means that power annihilates `M`.
/-- Lemma 15.94.8 (Bhatt): if `I` is a finitely generated ideal in a ring `A` and `M` is a
derived complete `A`-module which is `I`-power torsion, then some power of `I` annihilates `M`,
i.e. `(I ^ n) • M = 0` for some `n`. In Lean the torsion hypothesis is
`Module.IsIdealPowerTorsion I M`, and the conclusion is
`(I ^ n) • (⊤ : Submodule A M) = ⊥`. -/
theorem exists_pow_smul_top_eq_bot_of_isIdealPowerTorsion_of_isDerivedCompleteWithRespectTo
    (I : Ideal A) (M : ModuleCat A) (hI : I.FG) (hMtors : Module.IsIdealPowerTorsion I M)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    ∃ n : ℕ, (I ^ n) • (⊤ : Submodule A M) = ⊥ := sorry

end ModuleCat

end
