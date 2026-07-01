import Mathlib

universe u v w

section

variable {G : Type u} [Group G]
variable {R : Type v} [Semiring R] [MulSemiringAction G R]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/- Domain-style sampling for Example 18.37.3:
- primary domain: modules obtained by twisting scalars along a group action on a ring;
- sampled owner declarations:
  `Module.compHom`,
  `MulSemiringAction.toRingHom`,
  `LinearMap.ker`,
  `AddMonoidHom`;
- best owner abstraction: the source-facing owner is `Map(G, M)` with scalar action
  `(r • f)(σ) = σ(r) • f(σ)`, whose components are the restricted-scalars modules coming from
  `MulSemiringAction.toRingHom`.

Primitive-vs-derived split:
- primitive data: the underlying function type `G → M` together with the twisted scalar action;
- derived API: evaluation at `1_G`, the augmentation submodule `I(M)` as a kernel, its
  membership criterion, and the constant-function additive map `M → Map(G, M)`.

Source/core/bridge triage:
- `source-facing`: `Map(G, M)` with its twisted `R`-module structure and the submodule `I(M)`;
- `core/canonical`: scalar restriction via `Module.compHom` along `MulSemiringAction.toRingHom`
  and kernels of linear maps;
- `bridge/view`: the evaluation-at-`1_G` linear map and the constant-function additive map. -/

/-- The source-facing module `Map(G, M)` from Example 18.37.3, with scalar action
`(r • f)(σ) = σ(r) • f(σ)`. -/
@[nolint unusedArguments]
def groupSitePointMapModule (G : Type u) (_R : Type v) (M : Type w) : Type (max u w) :=
  G → M

instance : AddCommMonoid (groupSitePointMapModule G R M) :=
  inferInstanceAs (AddCommMonoid (G → M))

omit [Group G] [Semiring R] [MulSemiringAction G R] [AddCommMonoid M] [Module R M] in
@[ext] theorem groupSitePointMapModule_ext
    {f g : groupSitePointMapModule G R M} (h : ∀ σ : G, f σ = g σ) : f = g :=
  funext h

instance : SMul R (groupSitePointMapModule G R M) where
  smul r f σ := (σ • r) • f σ

@[simp] theorem groupSitePointMapModule_smul_apply
    (r : R) (f : groupSitePointMapModule G R M) (σ : G) :
    (r • f) σ = (σ • r) • f σ :=
  rfl

instance : Module R (groupSitePointMapModule G R M) where
  one_smul f := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    change (σ • (1 : R)) • f σ = f σ
    simp
  mul_smul r s f := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    rw [groupSitePointMapModule_smul_apply, groupSitePointMapModule_smul_apply]
    change (σ • (r * s)) • f σ = (σ • r) • ((σ • s) • f σ)
    simp [mul_smul]
  smul_zero r := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    change (σ • r) • (0 : M) = 0
    simp
  smul_add r f g := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    change (σ • r) • (f σ + g σ) = (σ • r) • f σ + (σ • r) • g σ
    simp
  add_smul r s f := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    change (σ • (r + s)) • f σ = (r • f) σ + (s • f) σ
    rw [groupSitePointMapModule_smul_apply, groupSitePointMapModule_smul_apply]
    simp [add_smul]
  zero_smul f := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    change (σ • (0 : R)) • f σ = 0
    simp

/-- Evaluation at the identity element is `R`-linear for the twisted module `Map(G, M)`. -/
def groupSitePointEvalOne (G : Type u) (R : Type v) (M : Type w) [Group G] [Semiring R]
    [MulSemiringAction G R] [AddCommMonoid M] [Module R M] :
    groupSitePointMapModule G R M →ₗ[R] M where
  toFun f := f 1
  map_add' _ _ := rfl
  map_smul' r f := by
    rw [groupSitePointMapModule_smul_apply]
    simp

/-- Example 18.37.3: the submodule `I(M)` consists of those functions `f : G → M` such that
`f(1_G) = 0`. -/
def groupSitePointAugmentationSubmodule (G : Type u) (R : Type v) (M : Type w) [Group G]
    [Semiring R] [MulSemiringAction G R] [AddCommMonoid M] [Module R M] :
    Submodule R (groupSitePointMapModule G R M) :=
  LinearMap.ker (groupSitePointEvalOne G R M)

/-- Membership in `I(M)` is the vanishing condition at `1_G`. -/
theorem mem_groupSitePointAugmentationSubmodule_iff (f : groupSitePointMapModule G R M) :
    f ∈ groupSitePointAugmentationSubmodule G R M ↔ f 1 = 0 := by
  simp [groupSitePointAugmentationSubmodule, groupSitePointEvalOne]

/-- Example 18.37.3: the canonical map `M → Map(G, M)` sends `m` to the constant function with
value `m`. For the twisted module structure this map is additive, not `R`-linear in general. -/
def groupSitePointConstantMap (G : Type u) (R : Type v) (M : Type w) [Group G] [Semiring R]
    [MulSemiringAction G R] [AddCommMonoid M] [Module R M] :
    M →+ groupSitePointMapModule G R M where
  toFun m _ := m
  map_zero' := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    rfl
  map_add' m n := by
    refine groupSitePointMapModule_ext ?_
    intro σ
    rfl

@[simp] theorem groupSitePointConstantMap_apply (m : M) (σ : G) :
    groupSitePointConstantMap G R M m σ = m :=
  rfl

end
