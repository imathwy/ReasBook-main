import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the generic scheme-morphism owner
`AlgebraicGeometry.affineLocally` and the specific analogue
`AlgebraicGeometry.LocallyOfFiniteType`. Those owners quantify over affine opens after
restriction, while the source item is the pointwise existential neighborhood condition, so this
file keeps the source-faithful existential owner. -/

/-- Definition 29.14.2: the morphism `f : X ⟶ Y` is locally of type `P` if every point of `X`
lies in an affine open `U` mapping into an affine open `V` of `Y` such that the induced ring map
`\Gamma(Y, V) \to \Gamma(X, U)` has property `P`. -/
@[stacks 01SS]
class LocallyOfType
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  property :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : Y.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          P (CommRingCat.Hom.hom (f.appLE V U e))

/-- `LocallyOfType` structures are proposition-valued. -/
instance instSubsingletonLocallyOfType
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Subsingleton (LocallyOfType P f) :=
  inferInstance

/-- A `LocallyOfType` hypothesis can be used through its pointwise affine-neighborhood witness
condition from Definition 29.14.2. -/
@[stacks 01SS]
theorem LocallyOfType.exists_affineNeighborhood
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : LocallyOfType P f) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : Y.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          P (CommRingCat.Hom.hom (f.appLE V U e)) :=
  hf.property x

/-- Unfold `LocallyOfType` into the source-style pointwise affine-neighborhood witness condition
from Definition 29.14.2. -/
@[stacks 01SS]
theorem locallyOfType_iff
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyOfType P f ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : Y.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            P (CommRingCat.Hom.hom (f.appLE V U e)) := by
  constructor
  · intro hf
    exact hf.property
  · intro hf
    exact ⟨hf⟩

/-- Bridge the source-facing existential owner to mathlib's canonical affine-open owner whenever
`P` is a local property of ring maps. -/
@[stacks 01SS]
theorem locallyOfType_iff_affineLocally
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔ affineLocally P f := by
  sorry

end AlgebraicGeometry
