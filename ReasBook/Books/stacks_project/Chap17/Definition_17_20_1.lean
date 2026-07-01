import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Definition 17.20.1:
- primary domain: flatness of morphisms of ringed spaces, expressed stalkwise;
- sampled owner declarations:
  `AlgebraicGeometry.Flat`,
  `AlgebraicGeometry.Flat.stalkMap`,
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`;
- owner abstraction: the project-level owner for ringed-space morphisms is the global predicate
  `RingedSpace.Hom.IsFlat`, while the scheme specialization is already owned upstream by
  `AlgebraicGeometry.Flat`;
- primitive data: the family of flat stalk maps;
- derived API: the pointwise source-facing predicate `FlatAt` and the scheme bridge
  `Scheme.Hom.isFlat_iff_flat`.

Source/core/bridge triage:
- `source-facing`: `FlatAt`;
- `core/canonical`: `IsFlat`;
- `bridge/view`: `Scheme.Hom.isFlat_iff_flat`.

The public owner should therefore be `IsFlat`, with `FlatAt` retained only as the pointwise view
named in the source, and the scheme specialization connected directly to the mathlib owner
`AlgebraicGeometry.Flat`. -/

/-- Definition 17.20.1: a morphism of ringed spaces is flat at `x` when the induced stalk map
`\mathcal O_{Y, f(x)} \to \mathcal O_{X, x}` is a flat ring homomorphism. -/
abbrev FlatAt (x : X) : Prop :=
  (f.hom.stalkMap x).hom.Flat

/-- A morphism of ringed spaces is flat when it is flat at every point of the source. -/
@[mk_iff]
class IsFlat : Prop where
  flatAt : ∀ x : X, FlatAt f x

end RingedSpace.Hom

namespace Scheme.Hom

open RingedSpace.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Under the scheme specialization, the ringed-space flatness owner agrees with mathlib's
canonical scheme-theoretic flatness predicate. -/
theorem isFlat_iff_flat :
    IsFlat f.toLRSHom.toShHom ↔ Flat f := by
  rw [Flat.iff_flat_stalkMap]
  constructor
  · intro hf x
    simpa [RingedSpace.Hom.FlatAt] using hf.flatAt x
  · intro hf
    exact ⟨fun x ↦ by simpa [RingedSpace.Hom.FlatAt] using hf x⟩

instance instIsFlat [Flat f] : IsFlat f.toLRSHom.toShHom :=
  (isFlat_iff_flat f).2 inferInstance

instance instFlat [IsFlat f.toLRSHom.toShHom] : Flat f :=
  (isFlat_iff_flat f).1 inferInstance

end Scheme.Hom
