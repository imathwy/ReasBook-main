import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- A source-facing presentation of a relative `Proj` morphism `p : X ⟶ S`: the underlying graded
`\mathcal O_S`-algebra together with the twist family `\mathcal O_X(d)`.

This is the minimal local owner needed in the current environment, where a built-in relative
`Proj_S` construction and its twisting-sheaf API are not yet available. -/
structure RelativeProjPresentation (p : X ⟶ S) where
  /-- The nonnegative degree pieces of the quasi-coherent graded `\mathcal O_S`-algebra whose
  relative `Proj` is represented by `p : X ⟶ S`. -/
  degreePiece : ℕ → S.Modules
  /-- Each nonnegative graded piece is quasi-coherent on `S`. -/
  degreePiece_isQuasicoherent : ∀ d : ℕ, (degreePiece d).IsQuasicoherent
  /-- The degree-zero piece is the structure sheaf on `S`. -/
  degree_zero : degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf
  /-- The twist family `\mathcal O_X(d)` attached to the relative `Proj` presentation. -/
  twist : ℤ → X.Modules
  /-- Each twist `\mathcal O_X(d)` is quasi-coherent on `X`. -/
  twist_isQuasicoherent : ∀ d : ℤ, (twist d).IsQuasicoherent
  /-- The degree-zero twist is the structure sheaf on `X`. -/
  twist_zero : twist 0 ≅ SheafOfModules.unit X.ringCatSheaf

/-- The degree-`d` piece of a relative `Proj` presentation is quasi-coherent on `S`. -/
instance instIsQuasicoherentDegreePiece (P : RelativeProjPresentation p) (d : ℕ) :
    (P.degreePiece d).IsQuasicoherent :=
  P.degreePiece_isQuasicoherent d

/-- The twist `\mathcal O_X(d)` in a relative `Proj` presentation is quasi-coherent on `X`. -/
instance instIsQuasicoherentTwist (P : RelativeProjPresentation p) (d : ℤ) :
    (P.twist d).IsQuasicoherent :=
  P.twist_isQuasicoherent d

end AlgebraicGeometry.Scheme.Hom
