module

public import Topology_Munkres_2000.Book.Theorem_81_5.OrbitCovering
public import Topology_Munkres_2000.Book.Definition_81_4.Regular
public import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
public import Topology_Munkres_2000.Book.Definition_81_6.ProperlyDiscontinuous
import Topology_Munkres_2000.Book.Corollary_81_3
import Mathlib.Topology.Covering.Quotient

public section

open scoped HomeomorphGroup

universe u

namespace HomeomorphGroup

/-- Helper for Theorem 81.5: the orbit projection is invariant under the action. -/
lemma mk_smul {X : Type u} [TopologicalSpace X] (G : Subgroup (X ≃ₜ X))
    (g : G) (x : X) :
    mk G (g • x) = mk G x := by
  -- Reverse the orbit relation exposed by `mk_eq_mk_iff`, then use `g` as witness.
  apply (mk_eq_mk_iff G).mpr
  exact MulAction.mem_orbit_symm.mpr ⟨g, rfl⟩

/-- Helper for Theorem 81.5: mathlib's quotient-covering package is equivalent to the
textbook neighborhood-disjointness condition for the orbit projection. -/
lemma isQuotientCoveringMap_mk_iff_properlyDiscontinuous
    {X : Type u} [TopologicalSpace X] (G : Subgroup (X ≃ₜ X)) :
    IsQuotientCoveringMap (mk G) G ↔ ProperlyDiscontinuousMulAction G X := by
  constructor
  · intro hquotient
    -- A nonidentity translate cannot have a point in the intersection supplied by `disjoint`.
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨U, hU, hdisjoint⟩ := hquotient.disjoint x
    refine ⟨U, hU, fun g hg ↦ Set.disjoint_left.mpr ?_⟩
    intro y hyTranslate hyU
    exact hg (hdisjoint g ⟨y, hyTranslate, hyU⟩)
  · intro hproper
    -- Package the quotient map, orbit-fiber relation, and chosen disjoint neighborhoods.
    refine
      { toIsQuotientMap := isQuotientMap_mk G
        toContinuousConstSMul := inferInstance
        apply_eq_iff_mem_orbit := ?_
        disjoint := ?_ }
    · intro x y
      exact (mk_eq_mk_iff G).trans MulAction.mem_orbit_symm
    · intro x
      obtain ⟨U, hU, hdisjoint⟩ :=
        hproper.exists_nhds_disjoint_image x
      refine ⟨U, hU, fun g hnonempty ↦ ?_⟩
      by_contra hg
      obtain ⟨y, hyTranslate, hyU⟩ := hnonempty
      exact Set.disjoint_left.mp (hdisjoint g hg) hyTranslate hyU

/-- Helper for Theorem 81.5: a covering orbit projection forces the evaluation action to
be cancellative. -/
private lemma isCancelSMul_of_isCoveringMap_mk
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (G : Subgroup (X ≃ₜ X)) (hp : IsCoveringMap (mk G)) :
    IsCancelSMul G X := by
  -- Two acting homeomorphisms are lifts of the same map; agreement at one point identifies them.
  constructor
  intro g g' x hgg'
  apply Subtype.ext
  apply Homeomorph.ext
  -- Apply lift uniqueness at the point where the two acting maps agree.
  exact congrFun (hp.eq_of_comp_eq (g : X ≃ₜ X).continuous (g' : X ≃ₜ X).continuous
    (funext fun y ↦ (mk_smul G g y).trans (mk_smul G g' y).symm) x hgg')

/-- Helper for Theorem 81.5: every acting homeomorphism is a covering transformation of
the orbit projection. -/
lemma le_coveringTransformationGroup
    {X : Type u} [TopologicalSpace X] (G : Subgroup (X ≃ₜ X)) :
    G ≤ CoveringTransformation.group (mk G) := by
  intro g hg
  -- Orbit invariance is exactly membership in the covering-transformation group.
  apply (CoveringTransformation.mem_group (mk G) g).mpr
  funext x
  exact mk_smul G ⟨g, hg⟩ x

/-- Helper for Theorem 81.5: lift uniqueness puts every covering transformation of a
covering orbit projection back in the acting subgroup. -/
private lemma coveringTransformationGroup_le
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (G : Subgroup (X ≃ₜ X)) (hp : IsCoveringMap (mk G)) :
    CoveringTransformation.group (mk G) ≤ G := by
  intro h hh
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · -- On the empty space every self-homeomorphism is the identity, hence lies in `G`.
    have hOne : h = 1 := by
      apply Homeomorph.ext
      intro x
      exact isEmptyElim x
    rw [hOne]
    exact G.one_mem
  · obtain ⟨x⟩ := hX
    have hhProjection : mk G ∘ h = mk G :=
      (CoveringTransformation.mem_group (mk G) h).mp hh
    -- At the chosen point, orbit equality supplies an acting element agreeing with `h`.
    have hOrbitEq : mk G x = mk G (h x) := (congrFun hhProjection x).symm
    obtain ⟨g, hg⟩ := (mem_orbit_iff G).mp ((mk_eq_mk_iff G).mp hOrbitEq)
    have hgProjection : mk G ∘ (g : X ≃ₜ X) = mk G := by
      funext y
      exact mk_smul G g y
    -- The two lifts agree at `x`, so their underlying homeomorphisms agree everywhere.
    have hHomeomorph : h = (g : X ≃ₜ X) := by
      apply Homeomorph.ext
      exact congrFun (hp.eq_of_comp_eq h.continuous (g : X ≃ₜ X).continuous
        (hhProjection.trans hgProjection.symm) x hg.symm)
    rw [hHomeomorph]
    exact g.property

/-- Theorem 81.5 (1). For a path-connected, locally path-connected space, the canonical
orbit projection is a covering map exactly when the homeomorphism action is properly
discontinuous. -/
theorem isCoveringMap_iff_properlyDiscontinuous
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (G : Subgroup (X ≃ₜ X)) :
    IsCoveringMap (mk G) ↔ ProperlyDiscontinuousMulAction G X := by
  constructor
  · intro hp
    -- Reconstruct the quotient-covering package from covering, quotient, and freeness data.
    apply (isQuotientCoveringMap_mk_iff_properlyDiscontinuous G).mp
    apply (isQuotientCoveringMap_iff_isCoveringMap_and (mk G) G).mpr
    refine ⟨hp, (isQuotientMap_mk G).surjective, inferInstance,
      isCancelSMul_of_isCoveringMap_mk G hp, ?_⟩
    intro x y
    exact (mk_eq_mk_iff G).trans MulAction.mem_orbit_symm
  · intro hproper
    -- Forget the quotient-covering structure obtained from proper discontinuity.
    exact (isQuotientCoveringMap_mk_iff_properlyDiscontinuous G).mpr hproper |>.isCoveringMap

/-- Theorem 81.5 (2). An orbit projection that is a covering map is a regular connected
covering. -/
instance instIsRegularCovering {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (G : Subgroup (X ≃ₜ X))
    (hp : IsCoveringMap (mk G)) : (covering G hp).IsRegular := by
  constructor
  intro b₀ x₀ hx₀
  -- Corollary 81.3 reduces normality to transitivity on the chosen fiber.
  apply (hp.fundamentalGroupMapRange_normal_iff_fiber_transitive
    (mk G) x₀ b₀ hx₀).mpr
  intro x₁ x₂
  have hOrbitEq : mk G x₁ = mk G x₂ := x₁.property.trans x₂.property.symm
  obtain ⟨g, hg⟩ := (mem_orbit_iff G).mp ((mk_eq_mk_iff G).mp hOrbitEq)
  -- The acting element is a covering transformation and carries `x₁` to `x₂`.
  exact ⟨⟨g, le_coveringTransformationGroup G g.property⟩, hg⟩

/-- Normality of the subgroup induced by a regular orbit covering at a chosen point. -/
theorem covering_fundamentalGroupMapRange_normal
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (G : Subgroup (X ≃ₜ X))
    (hp : IsCoveringMap (mk G)) (b₀ : X / G) (x₀ : X)
    (hx₀ : mk G x₀ = b₀) :
    (hp.fundamentalGroupMapRange hx₀).Normal :=
  by
    simpa [covering, ConnectedCovering.of] using
      (inferInstance : (covering G hp).IsRegular).normal b₀ x₀ hx₀

/-- Theorem 81.5 (3). If the canonical orbit projection is a covering map, its group of
covering transformations is exactly the acting subgroup of homeomorphisms. -/
theorem coveringTransformationGroup
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (G : Subgroup (X ≃ₜ X))
    (hp : IsCoveringMap (mk G)) :
    CoveringTransformation.group (mk G) = G := by
  -- The two inclusions are orbit invariance and uniqueness of lifts, respectively.
  exact le_antisymm (coveringTransformationGroup_le G hp)
    (le_coveringTransformationGroup G)

end HomeomorphGroup
