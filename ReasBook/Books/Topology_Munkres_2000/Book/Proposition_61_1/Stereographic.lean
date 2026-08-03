module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Geometry.Manifold.Instances.Sphere

public section

open Set
open scoped EuclideanSpace

namespace StandardSphere

/-- Stereographic projection identifies the two-sphere punctured at `b` with the plane. -/
noncomputable def puncturedHomeomorphPlane (b : StandardSphere 2) :
    ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  ((Homeomorph.setCongr (stereographic'_source b).symm).trans
    (stereographic' 2 b).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target b)).trans (Homeomorph.Set.univ _))

@[simp]
theorem puncturedHomeomorphPlane_apply
    (b : StandardSphere 2) (x : ({b}ᶜ : Set (StandardSphere 2))) :
    puncturedHomeomorphPlane b x = stereographic' 2 b x := by
  rfl

end StandardSphere
