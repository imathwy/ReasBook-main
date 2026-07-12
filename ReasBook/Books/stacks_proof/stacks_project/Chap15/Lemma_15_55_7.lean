import StacksProject_2024.Chap15.Definition_15_55_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-!
Domain-style sampling:
- primary domain: character modules over arbitrary rings, their opposite-ring module structure, and
  the canonical evaluation map into the double character module;
- sampled owner API:
  `CharacterModule.eval`,
  `CharacterModule.eq_zero_of_character_apply`,
  `DomMulAct.smul_addMonoidHom_apply`,
  `Module.Dual.eval`;
- owner abstraction:
  `source-facing`: injectivity of the canonical evaluation map for arbitrary-ring character
    modules;
  `core/canonical`: `CharacterModule.eval R M : M → (M^∨)^∨`, where the double character module
    is viewed as an `R`-module by applying `CharacterModule.moduleOpposite` twice;
  `bridge/view`: the commutative-ring specialization `Module.Dual.eval`.
- primitive versus derived:
  the primitive data are only the ambient `R`-module `M`, while injectivity is derived from the
  canonical separation lemma `CharacterModule.eq_zero_of_character_apply`; no additional wrapper
  around the double character module or its evaluation map is mathematically needed here.
-/

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace CharacterModule

-- Proof sketch: if `m` maps to `0` in the double character module, then every character
-- `φ : M^∨` vanishes on `m`. The canonical separation theorem
-- `CharacterModule.eq_zero_of_character_apply` then forces `m = 0`.
/-- Lemma 15.55.7: for any `R`-module `M`, the canonical evaluation map
`M → (M^∨)^∨`, realized as `CharacterModule.eval`, is injective. -/
@[stacks 01DB]
theorem eval_injective : Function.Injective (eval R : M →ₗ[R] (M^∨)^∨) :=
  (injective_iff_map_eq_zero _).2 fun m hm ↦
    eq_zero_of_character_apply fun φ ↦ by
      simpa [eval_apply] using DFunLike.congr_fun hm φ

end CharacterModule

end
