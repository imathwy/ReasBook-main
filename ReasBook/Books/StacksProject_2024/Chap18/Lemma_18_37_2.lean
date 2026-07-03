import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap07.Lemma_7_32_8
import StacksProject_2024.Chap18.Example_18_37_3

-- Declarations for this item will be appended below by the statement pipeline.

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
