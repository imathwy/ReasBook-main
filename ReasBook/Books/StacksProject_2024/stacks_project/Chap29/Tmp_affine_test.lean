import Mathlib.AlgebraicGeometry.Morphisms.Affine
open AlgebraicGeometry CategoryTheory Limits
universe u
example {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom f] : IsAffineHom (pullback.snd f g) := by infer_instance
