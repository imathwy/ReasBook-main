module

public import Topology_Munkres_2000.Book.Definition_35_2.Extension

public section

universe u v w

namespace UniversalExtensionProperty

/-- The universal extension property is preserved by retracts. -/
theorem ofRetract {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [UniversalExtensionProperty.{u} Z] (ι : C(Y, Z)) (r : C(Z, Y))
    (h : r.comp ι = .id Y) : UniversalExtensionProperty.{u} Y where
  exists_restrict_eq A hA f := by
    obtain ⟨g, hg⟩ := UniversalExtensionProperty.exists_restrict_eq A hA (ι.comp f)
    use r.comp g
    ext x
    change r (g x) = f x
    have hgx := ContinuousMap.congr_fun hg x
    change g x = ι (f x) at hgx
    rw [hgx]
    exact ContinuousMap.congr_fun h (f x)

/-- The universal extension property is invariant under homeomorphism. -/
theorem ofHomeo {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [UniversalExtensionProperty.{u} Z] (e : Y ≃ₜ Z) : UniversalExtensionProperty.{u} Y :=
  ofRetract (e : C(Y, Z)) (e.symm : C(Z, Y)) (by simp)

end UniversalExtensionProperty
