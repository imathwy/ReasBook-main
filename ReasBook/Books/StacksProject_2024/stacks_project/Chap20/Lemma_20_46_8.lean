import StacksProject_2024.Chap20.Open_subspace_module_core
import StacksProject_2024.Chap21.Lemma_21_44_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules
local notation "CpxX" => CochainComplex ModX ℤ
local notation "ResCpx" U => moduleRestrictionComplexToOpen X U
local notation "DRes" U => moduleRestrictionToOpenDerived X U

/- Domain-style sampling for Lemma 20.46.8:
- primary domain: source-facing local realizability of derived morphisms from a strictly perfect
  source by actual morphisms of restricted complexes, together with the resulting local
  null-homotopy criterion for vanishing derived morphisms;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasLocalChainMapRepresentation`,
  `SheafOfModules.RingedSite.exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect`,
  `SheafOfModules.RingedSite.exists_cover_homotopicToZero_of_isStrictlyPerfect_of_Q_map_eq_zero`,
  `CochainComplex.IsStrictlyPerfect`,
  `moduleRestrictionComplexToOpen`,
  `moduleRestrictionToOpenDerived`,
  `moduleRestrictionToOpenDerivedFactors`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the pointwise open-neighborhood statements on the ringed space `X`;
  `core/canonical`: the Chapter 21 opens-site owner theorems
    `exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect` and
    `exists_cover_homotopicToZero_of_isStrictlyPerfect_of_Q_map_eq_zero`, together with the
    Chapter 20 restriction owners `moduleRestrictionComplexToOpen X U`,
    `moduleRestrictionToOpenDerived X U`, and the canonical comparison isomorphism
    `moduleRestrictionToOpenDerivedFactors X U K`;
  `bridge/view`: the open-cover companions below, and the source-facing neighborhood extraction
    from those coverwise statements.

This file should therefore keep the source-facing neighborhood statements, but it should express
the derived comparison in the canonical `CommSq` form and expose the open-cover bridge needed to
reuse the Chapter 21 owner theorems on the opens site of `X`. -/

-- Proof sketch: specialize the Chapter `21.44.8` coverwise owner theorem to the canonical site of
-- opens of `X`. The open-cover companion records the resulting restricted chain maps in the
-- canonical `CommSq` form, and the neighborhood theorem then extracts a member of the cover
-- containing the chosen point `x`.
/-- Companion bridge: if `E` is strictly perfect, then every morphism
`α : E ⟶ F` in `D(𝒪_X)` is represented on the members of some open cover by morphisms of
restricted complexes fitting into the canonical comparison square. -/
theorem exists_open_cover_restriction_commSq_of_isStrictlyPerfect
    (E F : CpxX)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    ∃ (ι : Type u) (cover : ι → Opens X.carrier), IsOpenCover cover ∧
      ∀ i : ι,
        ∃ αi : (ResCpx (cover i)).obj E ⟶ (ResCpx (cover i)).obj F,
          CommSq
            ((DRes (cover i)).map α)
            (moduleRestrictionToOpenDerivedFactors X (cover i) E).hom
            (moduleRestrictionToOpenDerivedFactors X (cover i) F).hom
            (DerivedCategory.Q.map αi) := sorry

/-- Lemma 20.46.8 (1): if `E` is strictly perfect, then every morphism
`α : E ⟶ F` in `D(𝒪_X)` is locally represented by a morphism of complexes after restricting to a
suitable open neighborhood. -/
@[stacks 08C9]
theorem exists_open_neighborhood_restriction_commSq_of_isStrictlyPerfect
    (E F : CpxX)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (x : X) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ αU : (ResCpx U).obj E ⟶ (ResCpx U).obj F,
        CommSq
          ((DRes U).map α)
          (moduleRestrictionToOpenDerivedFactors X U E).hom
          (moduleRestrictionToOpenDerivedFactors X U F).hom
          (DerivedCategory.Q.map αU) := by
  obtain ⟨ι, cover, hcover, hα⟩ :=
    exists_open_cover_restriction_commSq_of_isStrictlyPerfect E F α hE
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  exact ⟨cover i, hxi, hα i⟩

/-- Companion form of Lemma 20.46.8 (1): the local chain-map representation may be written as an
equality in the restricted derived category by composing with the inverse comparison isomorphism.
-/
theorem exists_open_neighborhood_restriction_eq_Q_map_of_isStrictlyPerfect
    (E F : CpxX)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (x : X) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ αU : (ResCpx U).obj E ⟶ (ResCpx U).obj F,
        (DRes U).map α =
          (moduleRestrictionToOpenDerivedFactors X U E).hom ≫
            DerivedCategory.Q.map αU ≫
            (moduleRestrictionToOpenDerivedFactors X U F).inv := by
  obtain ⟨U, hxU, αU, hsq⟩ :=
    exists_open_neighborhood_restriction_commSq_of_isStrictlyPerfect E F α hE x
  refine ⟨U, hxU, αU, ?_⟩
  calc
    (DRes U).map α =
        (DRes U).map α ≫
          (moduleRestrictionToOpenDerivedFactors X U F).hom ≫
          (moduleRestrictionToOpenDerivedFactors X U F).inv := by
      simpa [Category.assoc] using
        (congrArg
          (fun k ↦ (DRes U).map α ≫ k)
          (moduleRestrictionToOpenDerivedFactors X U F).hom_inv_id).symm
    _ =
        (moduleRestrictionToOpenDerivedFactors X U E).hom ≫
          DerivedCategory.Q.map αU ≫
          (moduleRestrictionToOpenDerivedFactors X U F).inv := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (moduleRestrictionToOpenDerivedFactors X U F).inv)
          hsq.w

-- Proof sketch: specialize the Chapter `21.44.8` local-null-homotopy owner theorem to the opens
-- site of `X`. The open-cover companion keeps the reusable coverwise form, and the source-facing
-- statement below again extracts a point-containing member of the cover.
/-- Companion bridge: if `E` is strictly perfect and a morphism of complexes `α : E ⟶ F`
becomes zero in `D(𝒪_X)`, then after restricting to the members of some open cover of `X` it is
homotopic to zero. -/
theorem exists_open_cover_homotopy_zero_of_Q_map_eq_zero_of_isStrictlyPerfect
    (E F : CpxX) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hα : DerivedCategory.Q.map α = 0) :
    ∃ (ι : Type u) (cover : ι → Opens X.carrier), IsOpenCover cover ∧
      ∀ i : ι, Nonempty (Homotopy ((ResCpx (cover i)).map α) 0) := by
  sorry

/-- Lemma 20.46.8 (2): if `E` is strictly perfect and a morphism of complexes `α : E ⟶ F`
becomes zero in `D(𝒪_X)`, then after restricting to a suitable open neighborhood it is homotopic
to zero. -/
@[stacks 08C9]
theorem exists_open_neighborhood_homotopy_zero_of_Q_map_eq_zero_of_isStrictlyPerfect
    (E F : CpxX) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hα : DerivedCategory.Q.map α = 0)
    (x : X) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (Homotopy ((ResCpx U).map α) 0) := by
  obtain ⟨ι, cover, hcover, hαU⟩ :=
    exists_open_cover_homotopy_zero_of_Q_map_eq_zero_of_isStrictlyPerfect E F α hE hα
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  exact ⟨cover i, hxi, hαU i⟩

end AlgebraicGeometry.RingedSpace
