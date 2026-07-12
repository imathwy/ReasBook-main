import StacksProject_2024.Chap10.Lemma_10_136_13
import StacksProject_2024.Chap29.Definition_29_30_1

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

private abbrev appTopRingHom [IsAffine X] [IsAffine S] :
    Scheme.Γ.obj (Opposite.op S) →+* Scheme.Γ.obj (Opposite.op X) :=
  CommRingCat.Hom.hom (Scheme.Hom.appTop f)

/-- Definition 29.30.1 (4): for an affine morphism `f : X ⟶ S`, being standard syntomic means
that the induced map on global sections is a relative global complete intersection. -/
abbrev StandardSyntomic [IsAffine X] [IsAffine S] : Prop :=
  let _ : Algebra (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X)) :=
    (appTopRingHom f).toAlgebra
  Algebra.IsRelativeGlobalCompleteIntersection
    (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X))

/-- A standard syntomic affine morphism induces a relative-global-complete-intersection map on
global sections. -/
theorem standardSyntomic_isRelativeGlobalCompleteIntersection
    [IsAffine X] [IsAffine S] (hf : StandardSyntomic f) :
      let _ : Algebra (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X)) :=
        (appTopRingHom f).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection
        (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X)) :=
  hf

/-- The global-sections ring map of a standard syntomic affine morphism is syntomic. -/
theorem standardSyntomic_appTop_syntomic
    [IsAffine X] [IsAffine S] (hf : StandardSyntomic f) :
    RingHom.Syntomic (appTopRingHom f) := by
  let _ : Algebra (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X)) :=
    (appTopRingHom f).toAlgebra
  exact Algebra.IsRelativeGlobalCompleteIntersection.syntomic
    (R := Scheme.Γ.obj (Opposite.op S))
    (S := Scheme.Γ.obj (Opposite.op X))
    hf

/-- A standard syntomic affine morphism is syntomic as a morphism of schemes. -/
theorem standardSyntomic_syntomic
    [IsAffine X] [IsAffine S] (hf : StandardSyntomic f) :
    Syntomic f := by
  refine ⟨fun x ↦ ?_⟩
  refine ⟨⟨⊤, isAffineOpen_top _⟩, by simp, ⟨⟨⊤, isAffineOpen_top _⟩, ⟨by simp, ?_⟩⟩⟩
  simpa [appTopRingHom] using standardSyntomic_appTop_syntomic (f := f) hf

end AlgebraicGeometry
