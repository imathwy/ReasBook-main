import Mathlib
import stacks_proof.stacks_project.Chap18.Definition_18_40_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

/-- The inverse-image commutative structure sheaf attached to a site-presented morphism of
topoi. -/
abbrev inverseImageStructureSheafForLocallyRingedMorphism
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪D : Sheaf JD CommRingCat.{max u v}) :
    Sheaf JC CommRingCat.{max u v} :=
  (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D

/-- The set-theoretic pullback of the units inclusion along a commutative ring homomorphism. -/
def unitsSquarePullbackForLocallyRingedMorphism
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :=
  { x : Sˣ × R // (x.1 : S) = φ x.2 }

/-- The canonical comparison from source units to the pullback of the units square. -/
def unitsSquareComparisonForLocallyRingedMorphism
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    Rˣ → unitsSquarePullbackForLocallyRingedMorphism φ :=
  fun u ↦ ⟨⟨Units.map φ u, (u : R)⟩, rfl⟩

/-- The units square of a commutative ring map is cartesian when the canonical comparison to the
set-theoretic pullback is bijective. -/
def unitsSquareCartesianForLocallyRingedMorphism
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  Function.Bijective (unitsSquareComparisonForLocallyRingedMorphism φ)

/-- The inverse-image units square is cartesian when it is objectwise cartesian on every object of
the source site. -/
def inverseImageUnitsCartesianForLocallyRingedMorphism
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) : Prop :=
  ∀ U : C,
    unitsSquareCartesianForLocallyRingedMorphism ((fSharp.hom.app (Opposite.op U)).hom)

/-- Helper for Definition 18.40.9: a site-presented morphism of locally ringed topoi carries the
cartesian inverse-image units condition as structure. -/
class IsMorphismOfLocallyRingedTopoi
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) : Prop where
  /-- The inverse-image units square attached to the structure-sheaf map is cartesian. -/
  inverseImage_units_cartesian :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp

/-- A morphism of locally ringed topoi carries the canonical inverse-image cartesian-units
condition. -/
instance
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C)
    [IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp] :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp :=
  IsMorphismOfLocallyRingedTopoi.inverseImage_units_cartesian

-- Proof sketch: unpack the class field in one direction, and in the other direction rebuild the
-- class from the cartesian-units hypothesis.
/-- Definition 18.40.9: a morphism of locally ringed topoi is equivalently characterized by the
cartesianness of its inverse-image units square. -/
@[stacks 04HA]
theorem isMorphismOfLocallyRingedTopoi_iff
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) :
    IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp ↔
      inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := by
  constructor
  · intro h
    -- Project the unique field of the locally ringed-topos morphism structure.
    exact h.inverseImage_units_cartesian
  · intro h
    -- Repackage the cartesian-units condition as the one-field class instance.
    exact ⟨h⟩

/-- Helper for Definition 18.40.9: in the site-presented setting, a morphism of locally ringed
sites is simply a morphism of locally ringed topoi for the associated morphism of topoi. -/
abbrev IsMorphismOfLocallyRingedSites
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) : Prop :=
  IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp

/-- The site-level and topos-level locally ringed morphism predicates coincide in the presented
setting. -/
theorem isMorphismOfLocallyRingedSites_iff
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) :
    IsMorphismOfLocallyRingedSites F 𝒪C 𝒪D fSharp ↔
      IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp :=
  Iff.rfl

end CategoryTheory
