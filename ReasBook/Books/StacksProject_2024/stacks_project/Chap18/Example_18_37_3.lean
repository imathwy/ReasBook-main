import Mathlib

universe u v w

variable {G : Type u} [Monoid G]
variable {R : Type v} [Semiring R] [MulSemiringAction G R]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/- Domain-style sampling for Example 18.37.3:
- primary domain: modules of maps out of a group with scalars twisted by the group action on the
  coefficient ring;
- sampled owner declarations:
  `Module.compHom`,
  `MulSemiringAction.toRingHom`,
  `LinearMap.proj`,
  `LinearMap.const`,
  `Pi.constAddMonoidHom`,
  `LinearMap.ker`;
- best owner abstraction:
  `source-facing`: the module `Map(G, M)` from the source text, with the twisted scalar action
    `(r • f)(σ) = σ(r) • f(σ)`;
  `core/canonical`: the dependent function-space owner whose coordinate modules are
    `Module.compHom M (MulSemiringAction.toRingHom G R σ)`, together with `LinearMap.proj`,
    `Pi.constAddMonoidHom`, and kernels of linear maps;
  `bridge/view`: the canonical projection `LinearMap.proj 1`, whose kernel is the source
    submodule `I(M)`.

Primitive-vs-derived split:
- primitive data: the underlying function type `G → M` together with the coordinatewise scalar
  restriction `Module.compHom M (MulSemiringAction.toRingHom G R σ)`;
- derived API: the constant-map section `Pi.constAddMonoidHom G M`, the evaluation map
  `LinearMap.proj 1`, the submodule `I(M)`, and the membership criterion
  `f ∈ I(M) ↔ f(1_G) = 0`. -/

namespace GroupSitePoint

def Coeff (G : Type u) (_ : Type v) (M : Type w) (_ : G) : Type w :=
  M

scoped instance (σ : G) : AddCommMonoid (Coeff G R M σ) := by
  dsimp [Coeff]
  infer_instance

scoped instance (σ : G) : Module R (Coeff G R M σ) :=
  Module.compHom M (MulSemiringAction.toRingHom G R σ)

/-- The source-facing module `Map(G, M)` from Example 18.37.3. Its scalar action is
`(r • f)(σ) = σ(r) • f(σ)`. -/
def Map (R : Type v) (G : Type u) (M : Type w) : Type (max u w) :=
  (σ : G) → Coeff G R M σ

set_option quotPrecheck false in
scoped notation "Map[" R "](" G ", " M ")" => GroupSitePoint.Map R G M

set_option quotPrecheck false in
scoped notation "Map(" G ", " M ")" => GroupSitePoint.Map _ G M

open scoped GroupSitePoint

scoped instance : AddCommMonoid (Map R G M) :=
  inferInstanceAs (AddCommMonoid ((σ : G) → Coeff G R M σ))

scoped instance : Module R (Map R G M) :=
  inferInstanceAs (Module R ((σ : G) → Coeff G R M σ))

section

variable {G : Type u} {R : Type v} {M : Type w} [AddCommMonoid M]

/-- The constant-function map is the additive section `M → Map(G, M)` from Lemma 18.37.1. -/
@[simp] theorem const_apply (m : M) (σ : G) :
    (Pi.constAddMonoidHom G M m : Map[R](G, M)) σ = m :=
  rfl

end

variable (G) (R)

/-- Example 18.37.3: `I(M)` is the submodule of `Map(G, M)` consisting of those maps `f`
with `f(1_G) = 0`. -/
def augmentationSubmodule (M : Type w) [AddCommMonoid M] [Module R M] :
    Submodule R (Map[R](G, M)) :=
  let π : Map[R](G, M) →ₗ[R] Coeff G R M 1 := LinearMap.proj 1
  LinearMap.ker π

set_option quotPrecheck false in
scoped notation "I[" G ", " R "](" M ")" => GroupSitePoint.augmentationSubmodule G R M

set_option quotPrecheck false in
scoped notation "I(" M ")" => GroupSitePoint.augmentationSubmodule _ _ M

variable {G} {R}

/-- Membership in `I(M)` is the vanishing condition at `1_G`. -/
theorem mem_augmentationSubmodule_iff (f : Map[R](G, M)) :
    f ∈ I(M) ↔ f 1 = 0 := by
  let π : Map[R](G, M) →ₗ[R] Coeff G R M 1 := LinearMap.proj 1
  change f ∈ LinearMap.ker π ↔ f 1 = 0
  rfl

end GroupSitePoint
