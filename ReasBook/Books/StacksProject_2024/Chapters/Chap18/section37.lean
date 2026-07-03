import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_37_1 (from Chap18) -/
open CategoryTheory Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Φ : GrothendieckTopology.Point J)

/- Domain-style sampling:
- primary domain: the stalk/skyscraper adjunction attached to a site point and the resulting
  exactness statement for the direct image on abelian sheaves;
- sampled owner declarations:
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.skyscraperSheafFunctor`,
  `GrothendieckTopology.Point.skyscraperSheafAdjunction`,
  `exactFunctor`;
- best owner abstraction: the adjunction `Φ.skyscraperSheafAdjunction`, with source-facing
  functor `Φ.skyscraperSheafFunctor`;
- primitive data: the point `Φ`, together with the canonical fiber functor and its
  skyscraper-sheaf right adjoint;
- derived API: exactness of `Φ.skyscraperSheafFunctor` and the split-epi property of the counit;
- source/core/bridge triage:
  `source-facing`: the two Stacks statements below;
  `core/canonical`: `Φ.skyscraperSheafFunctor` and `Φ.skyscraperSheafAdjunction`;
  `bridge/view`: none.

The deleted public abbreviations for `p⁻¹ p_*`, its counit, and the kernel complement were only
derived wrappers around this owner API, so the public surface is refined to the owner declarations
directly. -/

-- Proof sketch: `Φ.skyscraperSheafFunctor` is right adjoint to `Φ.sheafFiber`, hence left exact.
-- For right exactness, use that the counit `p⁻¹ p_* A ⟶ A` admits a functorial section, so
-- `p⁻¹ p_*` splits as `𝟭 ⊞ I`; this forces `p_*` to carry epimorphisms to epimorphisms.
/-- Lemma 18.37.1: for a point `p` of a site, the skyscraper-sheaf functor
`p_* : Ab ⥤ Ab(\mathcal C)` is exact. -/
theorem point_skyscraper_sheaf_functor_exact :
    exactFunctor AddCommGrpCat.{max u v} (Sheaf J AddCommGrpCat.{max u v})
      Φ.skyscraperSheafFunctor := sorry

-- Proof sketch: the unit-counit identities give a functorial section of the counit
-- `p⁻¹ p_* ⟶ 𝟭`; in an abelian category, this split epimorphism is equivalent to a functorial
-- biproduct decomposition.
/-- The counit `p⁻¹ p_* ⟶ 𝟭` of the skyscraper-sheaf adjunction is a split epimorphism. -/
theorem point_skyscraper_counit_isSplitEpi :
    IsSplitEpi
      (Φ.skyscraperSheafAdjunction.counit : _ ⟶ 𝟭 AddCommGrpCat.{max u v}) := sorry

/-! ### Lemma_18_37_2 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Φ : GrothendieckTopology.Point.{w} J)
variable [HasWeakSheafify J RingCat.{u}]
variable [HasWeakSheafify typesGrothendieckTopology RingCat.{u}]
variable [(Φ.fiber.sheafPushforwardContinuous RingCat.{u} J typesGrothendieckTopology).IsRightAdjoint]
variable (𝒪 : Sheaf J RingCat.{u})

private abbrev pointUnit :
    𝒪 ⟶
      (Φ.fiber.sheafPushforwardContinuous RingCat.{u} J typesGrothendieckTopology).obj
        ((Φ.fiber.sheafPullback RingCat.{u} J typesGrothendieckTopology).obj 𝒪) :=
  ((Φ.fiber.sheafAdjunctionContinuous RingCat.{u} J
    typesGrothendieckTopology).unit.app 𝒪)

/-
Domain-style sampling for Lemma 18.37.2:
- primary domain: pullback and pushforward of sheaves of modules along the morphism of topoi
  attached to a site point;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `CategoryTheory.Functor.sheafOfModules_pushforward_exact_of_isAlmostCocontinuous`,
  `groupSitePointConstantMap`,
  the built-in instance `(SheafOfModules.pushforward φ).IsRightAdjoint`;
- best owner abstraction: the adjunction
  `SheafOfModules.pullbackPushforwardAdjunction` for the canonical unit map `pointUnit Φ 𝒪`;
- primitive data: the point `Φ`, the ring sheaf `𝒪`, and that canonical unit map
  `pointUnit Φ 𝒪 : 𝒪 ⟶ p_* p⁻¹ 𝒪`;
- derived API: exactness of the corresponding module pushforward, the inferable epimorphism
  structure on the underlying abelian counit from Lemma `18.37.1`, the `𝒪_p`-linear counit
  component in `SheafOfModules`, and the source-facing nonlinearity of the explicit constant-map
  section from Example `18.37.3`;
- source/core/bridge triage:
  `source-facing`: the exactness and counit-splitting statements of Lemma 18.37.2;
  `core/canonical`: `SheafOfModules.pushforward`, `SheafOfModules.pullback`, and
    `SheafOfModules.pullbackPushforwardAdjunction` on the unit map;
  `bridge/view`: the specialization of those owners to the point `Φ`, plus the group-site model
    from Example `18.37.3` used only to witness that the additive section from Lemma `18.37.1`
    need not be `𝒪_p`-linear.

The deleted public abbreviations in the old version were only local renamings of this owner API,
so the public surface is refined to the canonical declarations directly. -/

-- Proof sketch: the point direct image on modules is the pushforward functor along the unit map
-- `\mathcal O \to p_* p^{-1} \mathcal O`; exactness is proved by reducing to the exactness of the
-- underlying skyscraper functor on abelian sheaves from Lemma `18.37.1`.
/-- Lemma 18.37.2 (1): for a ringed topos `(Sh(\mathcal C), \mathcal O)` and a point `p`, the
direct-image functor `p_*` on modules over `p^{-1} \mathcal O` is exact. -/
theorem point_module_pushforward_exact :
    exactFunctor
      (SheafOfModules
        ((Φ.fiber.sheafPullback RingCat.{u} J typesGrothendieckTopology).obj 𝒪))
      (SheafOfModules 𝒪)
      (SheafOfModules.pushforward (pointUnit Φ 𝒪)) := by
  sorry

variable
  [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint]
  (M : SheafOfModules
    ((Φ.fiber.sheafPullback RingCat.{u} J typesGrothendieckTopology).obj 𝒪))

-- Proof sketch: forgetting scalars identifies the underlying abelian sheaf map of the module
-- counit with the split-epimorphic counit from Lemma `18.37.1`; since `SheafOfModules.toSheaf`
-- reflects epimorphisms, the canonical module counit is epic.
/-- Lemma 18.37.2 (2): for any `p^{-1}\mathcal O`-module `M`, the canonical counit
`p^{-1} p_* M ⟶ M`, namely
`(SheafOfModules.pullbackPushforwardAdjunction (pointUnit Φ 𝒪)).counit.app M`, is an
epimorphism. -/
theorem point_module_counit_epi :
    Epi ((SheafOfModules.pullbackPushforwardAdjunction (pointUnit Φ 𝒪)).counit.app M) := by
  sorry

-- Proof sketch: in the group-site model from Example `18.37.3`, the additive section from
-- Lemma `18.37.1` is the constant-function map `M → Map(G, M)`. Example `18.37.3` shows that
-- this map is not `R`-linear in general for the twisted module structure, so the additive
-- section from Lemma `18.37.1` does not in general upgrade to an `R`-linear splitting of the
-- module counit, identified in that model with `groupSitePointEvalOne`.
/-- Lemma 18.37.2 (3): in the group-site model from Example `18.37.3`, the additive section of
the counit from Lemma `18.37.1`, realized by the constant-function map `M → Map(G, M)`, does not
in general extend to an `R`-linear splitting of the canonical module counit
`groupSitePointEvalOne G R M : Map(G, M) →ₗ[R] M`. -/
theorem point_module_counit_section_not_linear_in_general :
    ¬ ∀ {G : Type u} [Group G] {R : Type v} [Semiring R] [MulSemiringAction G R]
        {M : Type w} [AddCommMonoid M] [Module R M],
        ∃ s : M →ₗ[R] groupSitePointMapModule G R M,
          (groupSitePointEvalOne G R M).comp s = LinearMap.id ∧
            ∀ m : M, s m = groupSitePointConstantMap G R M m := by
  sorry

/-! ### Example_18_37_3 (from Chap18) -/
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
