module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Topology_Munkres_2000.Book.Definition_74_5.OrientablePasting
public import Topology_Munkres_2000.Book.Definition_74_6.Presentation

public section

/-- A space belongs to the list of closed-surface homeomorphism types distinguished in
Theorem 75.5. -/
inductive ClassifiedClosedSurface (X : Type) [TopologicalSpace X] : Prop where
  /-- The space is a 2-sphere. -/
  | sphere : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      ClassifiedClosedSurface X
  /-- The space is an orientable surface of positive genus. -/
  | orientable (n : ℕ) (hn : 0 < n) :
      Nonempty (X ≃ₜ OrientableSurfacePresentation.nFoldTorus n hn) →
        ClassifiedClosedSurface X
  /-- The space is a real projective plane. -/
  | projective : Nonempty (X ≃ₜ RealProjectivePlane) → ClassifiedClosedSurface X
  /-- The space is a nonorientable surface of genus greater than one. -/
  | nonorientable (m : ℕ) (hm : 1 < m) :
      Nonempty (X ≃ₜ NonorientableSurfacePresentation.mFoldProjectivePlane m hm) →
        ClassifiedClosedSurface X

/-- A classified closed surface is homeomorphic to one of the standard
families appearing in the surface classification theorem. -/
theorem classifiedClosedSurface_iff (X : Type) [TopologicalSpace X] :
    ClassifiedClosedSurface X ↔
      Nonempty (X ≃ₜ StandardSphere 2) ∨
        (∃ (n : ℕ) (hn : 0 < n),
          Nonempty (X ≃ₜ OrientableSurfacePresentation.nFoldTorus n hn)) ∨
        Nonempty (X ≃ₜ RealProjectivePlane) ∨
        ∃ (m : ℕ) (hm : 1 < m),
          Nonempty (X ≃ₜ NonorientableSurfacePresentation.mFoldProjectivePlane m hm) := by
  constructor
  · intro h
    cases h with
    | sphere hX => exact Or.inl hX
    | orientable n hn hX => exact Or.inr (Or.inl ⟨n, hn, hX⟩)
    | projective hX => exact Or.inr (Or.inr (Or.inl hX))
    | nonorientable m hm hX => exact Or.inr (Or.inr (Or.inr ⟨m, hm, hX⟩))
  · rintro (hX | ⟨n, hn, hX⟩ | hX | ⟨m, hm, hX⟩)
    · exact .sphere hX
    · exact .orientable n hn hX
    · exact .projective hX
    · exact .nonorientable m hm hX
