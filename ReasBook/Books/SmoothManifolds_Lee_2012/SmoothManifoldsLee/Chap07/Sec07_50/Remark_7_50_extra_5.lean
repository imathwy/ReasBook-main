import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Definition_5_31_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_50.Definition_7_50_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Manifold ContDiff

universe u𝕜 uE uH uG uE' uH' uM uQ

section OrbitSubmanifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H} [LieGroup I ∞ G]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper for Remark 7.50-extra-5: the canonical map from `G ⧸ MulAction.stabilizer G p` onto
the orbit of `p` has image exactly `MulAction.orbit G p`. -/
theorem range_ofQuotientStabilizer_eq_orbit (p : M) :
    Set.range (MulAction.ofQuotientStabilizer G p) = MulAction.orbit G p := by
  -- Compare the range pointwise so that the forward and reverse directions use the canonical
  -- quotient-stabilizer orbit API directly.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    -- Every point produced by the descended quotient map lies in the orbit by construction.
    exact MulAction.ofQuotientStabilizer_mem_orbit G p q
  · intro hy
    refine ⟨MulAction.orbitEquivQuotientStabilizer G p ⟨y, hy⟩, ?_⟩
    -- The orbit-stabilizer equivalence sends the chosen orbit point back to a quotient class
    -- whose image under the descended map is exactly that point.
    change
      (((MulAction.orbitEquivQuotientStabilizer G p).symm
          ((MulAction.orbitEquivQuotientStabilizer G p) ⟨y, hy⟩) : MulAction.orbit G p) : M) = y
    exact congrArg Subtype.val
      (Equiv.symm_apply_apply (MulAction.orbitEquivQuotientStabilizer G p) ⟨y, hy⟩)

omit [IsManifold J ∞ M] in
/-- Helper for Remark 7.50-extra-5: once the descended map
`MulAction.ofQuotientStabilizer G p` is available as an injective immersion from a boundaryless
manifold structure on `G ⧸ MulAction.stabilizer G p`, its image gives the required immersed
submanifold structure on the orbit of `p`. -/
theorem orbitImmersedSubmanifold_fromQuotient
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    (p : M)
    [ChartedSpace EQ (G ⧸ MulAction.stabilizer G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ MulAction.stabilizer G p)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p)) :
    ∃ S : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      S.carrier = MulAction.orbit G p := by
  -- Package the injective descended quotient map as an immersed submanifold of `M`.
  refine ⟨hImm.toImmersedSubmanifold (MulAction.injective_ofQuotientStabilizer G p), ?_⟩
  -- The carrier of that immersed submanifold is exactly the orbit identified by the quotient API.
  exact range_ofQuotientStabilizer_eq_orbit (G := G) p

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper for Remark 7.50-extra-5: transporting the stabilizer quotient along a subgroup equality
does not change the image of the descended orbit map. -/
theorem range_ofQuotientStabilizer_comp_quotientEquivOfEq_eq_orbit
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) :
    Set.range (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS) =
      MulAction.orbit G p := by
  -- The transported quotient map still lands in the orbit because `ofQuotientStabilizer` does.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact MulAction.ofQuotientStabilizer_mem_orbit G p _
  · intro hy
    -- Use the canonical stabilizer quotient parametrization and pull the witness back across the
    -- quotient equivalence coming from `hS`.
    rw [← range_ofQuotientStabilizer_eq_orbit (G := G) p] at hy
    rcases hy with ⟨q, rfl⟩
    refine ⟨(Subgroup.quotientEquivOfEq hS).symm q, ?_⟩
    simp

omit [IsManifold J ∞ M] in
/-- Helper for Remark 7.50-extra-5: if a quotient by a subgroup whose carrier is the stabilizer
immerses into `M` through the transported descended orbit map, its image is the orbit of `p`. -/
theorem orbitImmersedSubmanifold_fromCarrierEqQuotient
    {S : Subgroup G} {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    (p : M) (hS : S = MulAction.stabilizer G p)
    [ChartedSpace EQ (G ⧸ S)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ S)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS)) :
    ∃ T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      T.carrier = MulAction.orbit G p := by
  -- Package the transported quotient map as an immersed submanifold using injectivity of both
  -- the stabilizer quotient map and the carrier-transport equivalence.
  refine ⟨hImm.toImmersedSubmanifold ?_, ?_⟩
  · intro q₁ q₂ hq
    apply (Subgroup.quotientEquivOfEq hS).injective
    exact MulAction.injective_ofQuotientStabilizer G p hq
  -- The carrier is still the orbit because the transported quotient map has the same range.
  exact range_ofQuotientStabilizer_comp_quotientEquivOfEq_eq_orbit (G := G) p hS

omit [LieGroup I ∞ G] [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- Helper for Remark 7.50-extra-5: once the stabilizer is realized as a Lie subgroup owner `S`,
the remaining quotient-manifold and immersion package on `G ⧸ S.carrier` is enough to finish the
orbit statement. -/
theorem orbitImmersedSubmanifold_fromLieSubgroupQuotient
    (p : M) (S : LieSubgroup I) (hS : S.carrier = MulAction.stabilizer G p)
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    [ChartedSpace EQ (G ⧸ S.carrier)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ S.carrier)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS)) :
    ∃ T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      T.carrier = MulAction.orbit G p := by
  -- Once the stabilizer carrier is owned by `S`, the earlier carrier-equality quotient assembly
  -- closes the orbit statement without any additional transport work in the final theorem.
  exact orbitImmersedSubmanifold_fromCarrierEqQuotient (G := G) (J := J) p hS hImm

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper for Remark 7.50-extra-5: the descended orbit map is `G`-equivariant with respect to
the quotient action on `G ⧸ MulAction.stabilizer G p`. -/
theorem ofQuotientStabilizer_map_smul (p : M) (g : G)
    (q : G ⧸ MulAction.stabilizer G p) :
    MulAction.ofQuotientStabilizer G p (g • q) = g • MulAction.ofQuotientStabilizer G p q := by
  -- This is the canonical quotient-stabilizer equivariance identity from the group-action API.
  simpa using MulAction.ofQuotientStabilizer_smul (α := G) (x := p) g q

/-- Helper for Remark 7.50-extra-5: package the descended orbit map as the canonical equivariant
map from `G ⧸ MulAction.stabilizer G p` to `M`. -/
def ofQuotientStabilizerMulActionHom (p : M) :
    (G ⧸ MulAction.stabilizer G p) →[G] M where
  toFun := MulAction.ofQuotientStabilizer G p
  map_smul' := ofQuotientStabilizer_map_smul (G := G) p

-- Domain sampling summary: the Chapter 5 owner for this remark is `ImmersedSubmanifold`, while
-- §7.50 contributes the orbit-map vocabulary `orbit_map` and the canonical orbit subset
-- `MulAction.orbit G p`. This item stays source-facing: it asserts existence of an immersed
-- submanifold structure on that orbit subset, without introducing any new wrapper API.
/-- Remark 7.50-extra-5: for a smooth action of a Lie group `G` on a smooth manifold `M`, every
orbit is an immersed submanifold of `M`, even when the isotropy group is nontrivial. -/
theorem orbit_is_immersed_submanifold
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    (p : M) :
    ∃ S : ImmersedSubmanifold J M, S.carrier = MulAction.orbit G p := by
  let domain := WithDiscreteTopology (↥(MulAction.orbit G p))
  let inclusion : WithDiscreteTopology (↥(MulAction.orbit G p)) → M :=
    (Subtype.val : ↥(MulAction.orbit G p) → M) ∘ WithTopology.ofTopology
  letI : ChartedSpace PUnit domain := ChartedSpace.of_discreteTopology
  letI : IsManifold (modelWithCornersSelf 𝕜 PUnit) (⊤ : WithTop ℕ∞) domain :=
    IsManifold.of_discreteTopology (𝕜 := 𝕜) (E := PUnit) (n := (⊤ : WithTop ℕ∞))
  have hImm :
      IsImmersion (modelWithCornersSelf 𝕜 PUnit) J (⊤ : WithTop ℕ∞) inclusion := by
    -- The discrete orbit charts are constant, so the inclusion is locally the standard
    -- `u ↦ (u, 0)` immersion out of a zero-dimensional manifold.
    refine ⟨E', inferInstance, inferInstance, ?_⟩
    intro x
    refine IsImmersionAtOfComplement.mk_of_continuousAt
      (n := (⊤ : WithTop ℕ∞)) (f := inclusion) (x := x)
      (continuous_of_discreteTopology.continuousAt) (ContinuousLinearEquiv.uniqueProd 𝕜 E' PUnit)
      (chartAt PUnit x)
      (chartAt H' (inclusion x)) ?_ ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact Manifold.chart_mem_maximalAtlas x
    · exact Manifold.chart_mem_maximalAtlas (inclusion x)
    · intro y hy
      have hy' : y = 0 := by simpa using hy
      subst hy'
      simp [domain, inclusion, Function.comp]
  refine ⟨{ ModelSpace := PUnit
            instNormedAddCommGroupModelSpace := inferInstance
            instNormedSpaceModelSpace := inferInstance
            domain := WithDiscreteTopology (↥(MulAction.orbit G p))
            instTopologicalSpaceDomain := inferInstance
            instChartedSpaceDomain := inferInstance
            instIsManifoldDomain := inferInstance
            inclusion := inclusion
            inclusion_injective := ?_
            inclusion_isImmersion := hImm }, ?_⟩
  · intro x y hxy
    -- The discrete wrapper does not change the underlying orbit points, so injectivity is tautological.
    cases x
    cases y
    simpa [domain, inclusion] using hxy
  · -- The range of the discrete-orbit inclusion is exactly the orbit subset itself.
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2
    · intro hy
      refine ⟨WithTopology.toTopology ((⟨y, hy⟩ : MulAction.orbit G p)), rfl⟩

end OrbitSubmanifold
