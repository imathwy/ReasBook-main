import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

noncomputable section

open scoped LinearAlgebra.Projectivization

/-- The standard projectivization model of `CP^n`. -/
abbrev ComplexProjectiveSpace (n : ℕ) :=
  ℙ ℂ (Fin (n + 1) → ℂ)

/-- The quotient topology on the projectivization model of `CP^n`. -/
instance (n : ℕ) : TopologicalSpace (ComplexProjectiveSpace n) :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient
        (projectivizationSetoid ℂ (Fin (n + 1) → ℂ))))

/-- The projectivization model of `CP^n` is Hausdorff. -/
instance (n : ℕ) : T2Space (ComplexProjectiveSpace n) := sorry

/-- A concrete basepoint of `CP^n`, represented by the line spanned by the first standard basis
vector of `ℂ^(n + 1)`. -/
def complexProjectiveSpaceBasepoint (n : ℕ) : ComplexProjectiveSpace n :=
  Projectivization.mk ℂ (Pi.single 0 (1 : ℂ)) <| by
    intro h
    have h0 := congrArg (fun f : Fin (n + 1) → ℂ ↦ f 0) h
    simp at h0
