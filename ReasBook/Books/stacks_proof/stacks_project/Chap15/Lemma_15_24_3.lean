import stacks_proof.stacks_project.Chap10.Lemma_10_82_13
import stacks_proof.stacks_project.Chap15.Definition_15_24_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open LinearMap

namespace IsContentIdeal

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/- Domain triage:
- primary domain: commutative algebra of content ideals and universally injective linear maps;
- sampled owner declarations of the same kind:
  `IsContentIdeal`,
  `LinearMap.UniversallyInjective`,
  `LinearMap.quotientMapByIdeal`;
  `LinearMap.injective_quotientMapByIdeal_of_universallyInjective`;
- best owner abstraction: the source-facing owner predicate `IsContentIdeal x I`, together with
  the canonical transport owner `LinearMap.UniversallyInjective`; the Chapter 10 bridge theorem
  `LinearMap.injective_quotientMapByIdeal_of_universallyInjective` supplies the quotient-level
  injectivity needed by the source-facing transport proof;
- primitive data: a linear map `u : M →ₗ[A] N`, an element `x : M`, and an ideal `I : Ideal A`;
- derived API: the owner-level transport theorem below and its local maximal-ideal specialization.

Layering:
- `source-facing`: the local maximal-ideal transport statement later in the file;
- `core/canonical`: the owner theorem `map_of_universallyInjective`;
- `bridge/view`: `LinearMap.quotientMapByIdeal` together with the Chapter 10 bridge theorem
  `LinearMap.injective_quotientMapByIdeal_of_universallyInjective`.
-/

variable {x : M} {I : Ideal A}

-- Proof sketch: transport the containment `x ∈ IM` across `u` for the existence part. For
-- minimality, if `u x ∈ JN`, then the class of `u x` vanishes in `N / JN`; injectivity of
-- `u.quotientMapByIdeal J`, supplied by universal injectivity, forces the class of `x` to vanish
-- in `M / JM`, hence `x ∈ JM`, and the defining minimality of the content ideal yields `I ≤ J`.
/-- Content ideals are preserved by universally injective linear maps. -/
theorem map_of_universallyInjective (hI : IsContentIdeal x I) (u : M →ₗ[A] N)
    (hu : UniversallyInjective.{u, v, w, u} u) :
    IsContentIdeal (u x) I := by
  classical
  refine ⟨?_, ?_⟩
  · have hux : u x ∈ Submodule.map u (I • (⊤ : Submodule A M)) :=
      Submodule.mem_map_of_mem hI.mem_smul_top
    have hux' : u x ∈ I • LinearMap.range u := by
      simpa [Submodule.map_smul'', Submodule.map_top] using hux
    exact
      (Submodule.smul_mono le_rfl
        (by simp : LinearMap.range u ≤ (⊤ : Submodule A N))) hux'
  · intro J hxJ
    have hu' : Function.Injective (u.quotientMapByIdeal J) :=
      injective_quotientMapByIdeal_of_universallyInjective u hu J
    have hxmem : x ∈ J • (⊤ : Submodule A M) := by
      apply (Submodule.Quotient.mk_eq_zero (J • (⊤ : Submodule A M))).1
      apply hu'
      simpa [LinearMap.quotientMapByIdeal] using
        (Submodule.Quotient.mk_eq_zero (J • (⊤ : Submodule A N))).2 hxJ
    exact hI.le hxmem

end

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Flat A N]

open IsLocalRing

/- Domain triage:
- primary domain: local commutative algebra of flat modules and content ideals under reduction
  modulo the maximal ideal;
- sampled owner declarations of the same kind:
  `IsContentIdeal`,
  `IsContentIdeal.map_of_universallyInjective`,
  `LinearMap.UniversallyInjective`,
  `LinearMap.quotientMapByIdeal`,
  `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`;
- best owner abstraction: the source-facing owner predicate `IsContentIdeal x I`, together with
  the canonical transport owner `LinearMap.UniversallyInjective`; the finite-ideal criterion from
  `LinearMap.universallyInjective_iff_injective_mod_finite_ideal` and the closed-fiber map
  `u.quotientMapByIdeal (maximalIdeal A)` are bridge API into the owner-level local criterion
  proved below;
- primitive data: a linear map `u : M →ₗ[A] N`, an element `x : M`, and an ideal `I : Ideal A`;
- derived API: the owner theorem `IsContentIdeal.map_of_universallyInjective` and the
  source-facing local specialization below;
  the maximal-ideal bridge criterion is internal proof support only.

Layering:
- `source-facing`: the local content-ideal transport statement below;
- `core/canonical`: `IsContentIdeal.map_of_universallyInjective`;
- `bridge/view`: the internal owner-level criterion upgrading closed-fiber injectivity to
  the public owner-level criterion
  `LinearMap.universallyInjective_of_injective_mod_maximalIdeal`.
-/

variable {x : M} {I : Ideal A}

-- Proof sketch: apply the owner-level local criterion
-- `LinearMap.universallyInjective_of_injective_mod_maximalIdeal` and then transport the content
-- ideal along the canonical owner theorem `IsContentIdeal.map_of_universallyInjective`.
/-- Lemma 15.24.3: over a local ring, if the induced map `M/𝔪M → N/𝔪N` is injective, then any
content ideal of `x` is also a content ideal of its image under a map of flat modules. -/
@[stacks 0ASC]
theorem map_of_injective_mod_maximalIdeal (hI : IsContentIdeal x I) (u : M →ₗ[A] N)
    (hu : Function.Injective (u.quotientMapByIdeal (maximalIdeal A))) :
    IsContentIdeal (u x) I :=
  hI.map_of_universallyInjective u <| universallyInjective_of_injective_mod_maximalIdeal u hu

end

end IsContentIdeal
