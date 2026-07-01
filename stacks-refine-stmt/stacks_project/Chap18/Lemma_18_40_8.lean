import Mathlib
import stacks_project.Chap18.Lemma_18_36_4
import stacks_project.Chap18.Definition_18_40_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

/-
Domain-style sampling for Lemma 18.40.8:
- primary domain: locally ringed morphisms of site-presented topoi, with the induced stalk maps
  viewed through both the source-side cartesian-units condition and the ring-theoretic bridge
  predicate `IsLocalHom`;
- sampled owner declarations:
  `IsLocallyRingedSite`,
  `IsLocalHom`,
  `inverseImageUnitsCartesianForLocallyRingedMorphism`,
  `unitsSquareCartesianForLocallyRingedMorphism`,
  `CategoryTheory.IsMorphismOfLocallyRingedTopoi`;
- best owner abstraction: the source-facing Chapter 18 owner is the global cartesian-units
  condition `inverseImageUnitsCartesianForLocallyRingedMorphism`, interpreted in the locally
  ringed setting via `IsLocallyRingedSite`; the stalkwise predicate `IsLocalHom` is only a bridge
  reformulation and becomes the textbook local-ring-homomorphism condition only after separately
  knowing the relevant stalk rings are local;
- primitive data: the unbundled inverse-image structure-sheaf morphism `fSharp`, together with
  the ambient locally ringed-site hypotheses when the source text speaks about local ring
  homomorphisms on stalks;
- derived API: the induced objectwise maps `fSharp.hom.app (op U)`, the stalk maps
  `p.sheafFiber.map fSharp`, the objectwise/stalkwise cartesian-units conditions, and the
  `IsLocalHom` bridge criterion on those stalk maps.

Source/core/bridge triage:
- `source-facing`: the sectionwise-to-stalkwise implications and conservative-family criteria of
  Lemma 18.40.8, with clauses `(3)` and `(5)` read in the locally ringed setting;
- `core/canonical`: `IsLocallyRingedSite`,
  `inverseImageUnitsCartesianForLocallyRingedMorphism`, and
  `unitsSquareCartesianForLocallyRingedMorphism`;
- `bridge/view`: the direct stalkwise map `p.sheafFiber.map fSharp` and its ring-theoretic
  `IsLocalHom` reformulation.

This file should therefore reuse the existing Chapter 18 owner for the global units-square
condition, and keep the direct `IsLocalHom` reformulation only as bridge data rather than as the
main source-facing locally ringed statement.
-/

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S]

-- Proof sketch: an element of the pullback is a source element whose image is a unit; lifting it
-- to a source unit is exactly the unit-reflection property, namely `IsLocalHom φ`.
/-- The units square for a ring map is cartesian exactly when the map reflects units. -/
theorem unitsSquareCartesian_iff_isLocalHom (φ : R →+* S) :
    unitsSquareCartesianForLocallyRingedMorphism φ ↔ IsLocalHom φ := sorry

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [(F.sheafPushforwardContinuous CommRingCat.{u} JD JC).IsRightAdjoint]
variable (𝒪C : Sheaf JC CommRingCat.{u}) (𝒪D : Sheaf JD CommRingCat.{u})

local notation "f⁻¹𝒪" => inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D

variable (fSharp : f⁻¹𝒪 ⟶ 𝒪C)

-- Proof sketch: taking the stalk at a point preserves finite limits, so an objectwise cartesian
-- units square on the source site yields a cartesian units square on every stalk.
/-- Lemma 18.40.8 (1): the cartesian units square on the inverse-image structure sheaf implies the
corresponding cartesian units square on every stalk. -/
theorem inverseImageUnitsCartesian_implies_stalkUnitsCartesian :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp →
      ∀ p : GrothendieckTopology.Point.{u} JC,
        unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom) := sorry

-- Proof sketch: with enough points, cartesianness of the units square can be checked stalkwise,
-- since the comparison morphism to the pullback is an isomorphism exactly when it is so on all
-- stalks.
/-- Lemma 18.40.8 (2): if the source site has enough points, the cartesian units square condition
for `f^\sharp` is equivalent to the stalkwise cartesian units square condition. -/
theorem inverseImageUnitsCartesian_iff_stalkUnitsCartesian_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} JC] :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp ↔
      ∀ p : GrothendieckTopology.Point.{u} JC,
        unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom) := sorry

-- Proof sketch: for each point, the displayed stalk square is cartesian exactly when the stalk map
-- reflects units, which is precisely the owner predicate `IsLocalHom`.
/-- Companion bridge: the stalkwise cartesian units square condition is equivalent to the
ring-theoretic unit-reflection predicate `IsLocalHom` on the induced stalk maps. By itself this
does not assert that the stalk rings are local. -/
theorem stalkUnitsCartesian_iff_stalkMapsAreLocalHom :
    (∀ p : GrothendieckTopology.Point.{u} JC,
      unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom)) ↔
      ∀ p : GrothendieckTopology.Point.{u} JC,
        IsLocalHom ((p.sheafFiber.map fSharp).hom) := sorry

-- Proof sketch: after assuming both structure sheaves are locally ringed, every source and target
-- stalk ring is local, so the previous `IsLocalHom` bridge becomes the textbook local-ring-map
-- condition on stalks.
/-- Lemma 18.40.8 (3): if both structure sheaves define locally ringed sites, then the stalkwise
cartesian units square condition is equivalent to requiring the induced stalk maps to be local
ring homomorphisms. -/
theorem stalkUnitsCartesian_iff_stalkMapsAreLocal
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D] :
    (∀ p : GrothendieckTopology.Point.{u} JC,
      unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom)) ↔
      ∀ p : GrothendieckTopology.Point.{u} JC,
        IsLocalRing (sourcePointRing f⁻¹𝒪 p) ∧
          IsLocalRing (sourcePointRing 𝒪C p) ∧
        IsLocalHom ((p.sheafFiber.map fSharp).hom) := sorry

variable (P : ObjectProperty (GrothendieckTopology.Point.{u} JC))

-- Proof sketch: apply conservativity of the chosen family of point functors to the comparison map
-- from `f^{-1}(\mathcal O_\mathcal D^*)` to the pullback sheaf; if all stalk squares in the
-- family are cartesian, then the comparison is an isomorphism globally.
/-- Lemma 18.40.8 (4): if a conservative family of points of the source site satisfies the
stalkwise cartesian units square condition, then the global units square for `f^\sharp` is
cartesian. -/
theorem inverseImageUnitsCartesian_of_stalkUnitsCartesian_of_conservativeFamily
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ p : GrothendieckTopology.Point.{u} JC, P p →
      unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom)) :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := sorry

-- Proof sketch: convert the stalkwise `IsLocalHom` hypothesis into the stalkwise cartesian units
-- square hypothesis using the previous bridge equivalence, then apply the conservative-family
-- criterion.
/-- Companion bridge: if a conservative family of source points yields stalk maps satisfying
`IsLocalHom`, then the global units square for `f^\sharp` is cartesian. This is the ring-theoretic
bridge underlying Lemma 18.40.8 (5). -/
theorem inverseImageUnitsCartesian_of_stalkMapsAreLocalHom_of_conservativeFamily
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ p : GrothendieckTopology.Point.{u} JC, P p →
      IsLocalHom ((p.sheafFiber.map fSharp).hom)) :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := sorry

-- Proof sketch: in the locally ringed setting, the stalk hypotheses assert that the induced maps
-- are local ring homomorphisms, and hence satisfy the `IsLocalHom` bridge criterion; the previous
-- companion theorem then yields the canonical owner condition that `f^\sharp` defines a morphism
-- of locally ringed topoi.
/-- Lemma 18.40.8 (5): if both structure sheaves define locally ringed sites and a conservative
family of source points yields local ring maps on the stalks of `f^\sharp`, then the global units
square for `f^\sharp` is cartesian, equivalently `f^\sharp` is a morphism of locally ringed
topoi. -/
theorem isMorphismOfLocallyRingedTopoi_of_stalkMapsAreLocal_of_conservativeFamily
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ p : GrothendieckTopology.Point.{u} JC, P p →
      IsLocalRing (sourcePointRing f⁻¹𝒪 p) ∧
        IsLocalRing (sourcePointRing 𝒪C p) ∧
      IsLocalHom ((p.sheafFiber.map fSharp).hom)) :
    IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp := sorry

end
