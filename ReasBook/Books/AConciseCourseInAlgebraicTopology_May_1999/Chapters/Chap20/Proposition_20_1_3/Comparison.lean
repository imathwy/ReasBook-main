import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3.Homology

open AlgebraicTopology CategoryTheory Limits
open scoped Manifold Topology

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ E = n)]

/-- Helper for Proposition 20.1.3: the complement `M \ Set.univ` is empty, so the `Set.univ`
relative-homology comparison starts from the empty subspace. -/
theorem isEmpty_subspaceComplement_univ :
    IsEmpty (subspaceComplement M (Set.univ : Set M)) := by
  refine ⟨?_⟩
  intro x
  exact x.2 (by simp)

/-- Helper for Proposition 20.1.3: the constant-coefficient coproduct indexed by the empty
`Set.univ` complement is a zero object. -/
theorem emptyCoproductConstantCoefficient_isZero :
    IsZero (∐ fun _ : TopCat.of.{u} PEmpty ↦ constantCoefficientModule R) := by
  let diagram : Discrete (TopCat.of.{u} PEmpty) ⥤ ModuleCat.{u} R :=
    Discrete.functor (fun _ : TopCat.of.{u} PEmpty ↦ constantCoefficientModule R)
  let hinit : IsInitial (∐ fun _ : TopCat.of.{u} PEmpty ↦ constantCoefficientModule R) :=
    (@CategoryTheory.Limits.isColimitEquivIsInitialOfIsEmpty (ModuleCat.{u} R) _ _ _ _ _
      (colimit.cocone diagram)).toFun (colimit.isColimit diagram)
  exact hinit.isZero

/-- Helper for Proposition 20.1.3: the singular-chain map induced by
`subspaceComplementInclusion M Set.univ` is zero because its source is the empty subspace. -/
theorem subspaceComplementInclusion_univ_chainMap_zero :
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (constantCoefficientModule R)).map
      (subspaceComplementInclusion M (Set.univ : Set M)) = 0 := by
  let F := ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (constantCoefficientModule R))
  -- This helper identifies the source as the empty complement of `Set.univ`.
  -- Local instance justification (proof-local temporary data): needed only for `emptyHomeo`.
  letI : IsEmpty (subspaceComplement M (Set.univ : Set M)) :=
    isEmpty_subspaceComplement_univ
  let emptyHomeo : subspaceComplement M (Set.univ : Set M) ≃ₜ PEmpty :=
    Homeomorph.mk (Equiv.equivOfIsEmpty _ _) (by continuity) (by continuity)
  -- This zero-source computation transports `IsZero` through `ChainComplex.alternatingConst`.
  -- Local instance justification (proof-local temporary data): needed only for this computation.
  haveI :
      (ChainComplex.alternatingConst :
        ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ).PreservesZeroMorphisms :=
    { map_zero := by
        intro X Y
        ext i
        rfl }
  have hPEmptyZero : IsZero (F.obj (TopCat.of.{u} PEmpty)) := by
    have hAltZero :
        IsZero (ChainComplex.alternatingConst.obj
          (∐ fun _ : TopCat.of.{u} PEmpty ↦ constantCoefficientModule R)) := by
      exact Functor.map_isZero (ChainComplex.alternatingConst)
        emptyCoproductConstantCoefficient_isZero
    exact IsZero.of_iso hAltZero
      (AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat.{u} R) (constantCoefficientModule R) (TopCat.of.{u} PEmpty))
  have hSourceZero :
      IsZero (F.obj (TopCat.of.{u} (subspaceComplement M (Set.univ : Set M)))) := by
    exact IsZero.of_iso hPEmptyZero (F.mapIso (TopCat.isoOfHomeo emptyHomeo))
  exact hSourceZero.eq_of_src _ _

/-- Helper for Proposition 20.1.3: when `Y = Set.univ`, the chapter's relative top homology
recovers the absolute singular homology group. -/
noncomputable def relativeTopHomologyGroupUnivIsoRSingularHomology :
    relativeTopHomologyGroup R n M Set.univ ≅ rSingularHomology R n (TopCat.of.{u} M) := by
  let F := ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (constantCoefficientModule R))
  let finc : TopCat.of.{u} (subspaceComplement M (Set.univ : Set M)) ⟶ TopCat.of.{u} M :=
    subspaceComplementInclusion M (Set.univ : Set M)
  have hzero : F.map finc = 0 := subspaceComplementInclusion_univ_chainMap_zero
  have hcokernelIso : cokernel (F.map finc) ≅ F.obj (TopCat.of.{u} M) := by
    let hmapIso :
        cokernel (F.map finc) ≅
          cokernel
            (0 : F.obj (TopCat.of.{u} (subspaceComplement M (Set.univ : Set M))) ⟶
              F.obj (TopCat.of.{u} M)) :=
      cokernel.mapIso (F.map finc) 0 (Iso.refl _) (Iso.refl _) (by simp [hzero])
    exact hmapIso ≪≫ cokernelZeroIsoTarget
  exact (HomologicalComplex.homologyFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n).mapIso hcokernelIso

/-- Helper for Proposition 20.1.3: the `Set.univ` relative-to-local map agrees with the absolute
local top-homology map after transporting along
`relativeTopHomologyGroupUnivIsoRSingularHomology`. -/
theorem relativeToLocalTopHomologyMap_univ_inv_hom_eq_localTopHomologyMap (x : M) :
    relativeTopHomologyGroupUnivIsoRSingularHomology.inv ≫
      relativeToLocalTopHomologyMap R n M Set.univ (Set.mem_univ x) =
      localTopHomologyMap R n M x := by
  sorry

/-- Helper for Proposition 20.1.3: transporting a global singular class to
`relativeTopHomologyGroup R n M Set.univ` does not change its local image. -/
theorem relativeToLocalTopHomologyMap_univ_inv_eq_localTopHomologyMap
    (z : rSingularHomology R n (TopCat.of.{u} M)) (x : M) :
    (relativeToLocalTopHomologyMap R n M Set.univ (Set.mem_univ x))
      (relativeTopHomologyGroupUnivIsoRSingularHomology.inv.hom z) =
      (localTopHomologyMap R n M x) z := by
  sorry

/-- Helper for Proposition 20.1.3: restricting a relative class from `Z` to `Y ⊆ Z` and then
localizing at `x ∈ Y` agrees with localizing directly from `Z`. -/
theorem relativeToLocalTopHomologyMap_restrict_eq
    {Y Z : Set M} (hYZ : Y ⊆ Z) {x : M} (hx : x ∈ Y) :
    relativeTopHomologyRestrict R n M Y Z hYZ ≫
      relativeToLocalTopHomologyMap R n M Y hx =
      relativeToLocalTopHomologyMap R n M Z (hYZ hx) := by
  sorry

/-- Helper for Proposition 20.1.3: the pointwise local identifications chosen from an
`R`-fundamental class. -/
noncomputable def univIdentifyOfIsRFundamentalClass
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z)
    (x : (Set.univ : Set M)) :
    localTopHomologyGroup R n M x.1 ≅ constantCoefficientModule R :=
  Classical.choose (hz x.1)

/-- Helper for Proposition 20.1.3: the chosen global identifications send the absolute local image
of `z` to `1`. -/
theorem univIdentifyOfIsRFundamentalClass_apply
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z)
    (x : (Set.univ : Set M)) :
    (univIdentifyOfIsRFundamentalClass hz x).hom
        ((localTopHomologyMap R n M x.1) z) = 1 :=
  Classical.choose_spec (hz x.1)

/-- Helper for Proposition 20.1.3: the `Set.univ` relative class induced from a global
`R`-fundamental class is normalized by the chosen pointwise identifications. -/
theorem univIdentify_relativeClass_apply
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z)
    (x : (Set.univ : Set M)) :
    (univIdentifyOfIsRFundamentalClass hz x).hom
        ((relativeToLocalTopHomologyMap R n M Set.univ x.property)
          (relativeTopHomologyGroupUnivIsoRSingularHomology.inv.hom z)) = 1 := by
  sorry

/-- Helper for Proposition 20.1.3: an `R`-fundamental class defines a global trivialization over
`Set.univ`. -/
@[reducible] noncomputable def univTrivializationOfIsRFundamentalClass
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    LocalTopHomologyTrivialization R n M where
  domain := Set.univ
  isOpen_domain := isOpen_univ
  localOrientationClass := relativeTopHomologyGroupUnivIsoRSingularHomology.inv.hom z
  identify := univIdentifyOfIsRFundamentalClass hz
  identify_localOrientationClass := univIdentify_relativeClass_apply hz

/-- Helper for Proposition 20.1.3: the global trivialization built from an `R`-fundamental class
belongs to the induced orientation atlas. -/
theorem univTrivialization_mem_inducedROrientationAtlas_of_isRFundamentalClass
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    univTrivializationOfIsRFundamentalClass hz ∈
      inducedROrientationAtlas z := by
  intro x
  exact univIdentifyOfIsRFundamentalClass_apply hz x

namespace IsRFundamentalClass

/-- Helper for Proposition 20.1.3: a global `R`-fundamental class yields a `Set.univ`
trivialization already lying in the induced orientation atlas. -/
theorem exists_univTrivialization
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    ∃ U : LocalTopHomologyTrivialization R n M,
      U ∈ inducedROrientationAtlas z ∧ U.domain = Set.univ := by
  refine ⟨univTrivializationOfIsRFundamentalClass hz, ?_, rfl⟩
  exact univTrivialization_mem_inducedROrientationAtlas_of_isRFundamentalClass hz

end IsRFundamentalClass

/-- Helper for Proposition 20.1.3: a `Set.univ` relative class is compatible with `o` when every
point lies in an atlas chart whose chosen identifications send all local images of the class to
`1 : R`. -/
def IsUnivRelativeClassFor (o : ROrientedManifold R I n M)
    (η : relativeTopHomologyGroup R n M Set.univ) : Prop :=
  ∀ x : M, ∃ U : LocalTopHomologyTrivialization R n M,
    U ∈ o.atlas ∧ x ∈ U.domain ∧
      ∀ y : U.domain,
        (U.identify y).hom
          ((relativeToLocalTopHomologyMap R n M Set.univ (Set.mem_univ y.1)) η) = 1

/-- Helper for Proposition 20.1.3: transporting a normalized `Set.univ` relative class through the
absolute-relative comparison exactly recovers compatibility with the same orientation atlas. -/
theorem isUnivRelativeClassFor_iff_isRFundamentalClassFor
    (o : ROrientedManifold R I n M) (η : relativeTopHomologyGroup R n M Set.univ) :
    IsUnivRelativeClassFor o η ↔
      IsRFundamentalClassFor o
        (relativeTopHomologyGroupUnivIsoRSingularHomology.hom η) := by
  sorry

/-- Helper for Proposition 20.1.3: once the compact argument supplies a unique normalized
`Set.univ` relative class, transporting along
`relativeTopHomologyGroupUnivIsoRSingularHomology` yields the unique compatible singular
fundamental class. -/
theorem existsUnique_rFundamentalClassFor_of_existsUnique_univRelativeClass
    (o : ROrientedManifold R I n M)
    (hη :
      ∃! η : relativeTopHomologyGroup R n M Set.univ, IsUnivRelativeClassFor o η) :
    ∃! z : rSingularHomology R n (TopCat.of.{u} M), IsRFundamentalClassFor o z := by
  sorry

/-- Helper for Proposition 20.1.3: the compact oriented atlas determines a unique normalized
relative class on `Set.univ`. -/
theorem existsUnique_univRelativeClass_compatible_of_rOrientedManifold
    [CompactSpace M] (o : ROrientedManifold R I n M) :
    ∃! η : relativeTopHomologyGroup R n M Set.univ, IsUnivRelativeClassFor o η := by
  sorry

end
