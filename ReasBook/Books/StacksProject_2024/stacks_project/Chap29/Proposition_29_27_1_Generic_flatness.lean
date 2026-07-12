import Mathlib
import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Definition_29_21_1
import StacksProject_2024.Chap29.Lemma_29_25_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall / owner check:
- `lean_leansearch` surfaced the canonical morphism-side flatness owner `AlgebraicGeometry.Flat`
  and the sheaf-side finite-presentation owner `SheafOfModules.IsFinitePresentation`;
- local Chapter 29 precedent records “of finite type” and “of finite presentation” for scheme
  morphisms via `Scheme.Hom.FiniteType` and `Scheme.Hom.FinitePresentation`;
- `Lemma_29_25_2.lean` already packages relative flatness of an `\mathcal O_X`-module over a base
  morphism through `relativeModuleOver`.

The source-facing statement therefore stays on an open `U : S.Opens`, with the restricted morphism
`f ∣_ U` and the restricted module on the inverse-image open subscheme. -/

noncomputable section

section

variable {X S : Scheme.{u}}

/-- Restrict `\mathcal F` to the open subscheme `X_U = f^{-1}(U)` over an open `U ⊆ S`. -/
abbrev genericFlatnessRestrictModule
    (f : X ⟶ S) (ℱ : X.Modules) (U : S.Opens) :
    (f ⁻¹ᵁ U).toScheme.Modules :=
  ℱ.restrict ((f ⁻¹ᵁ U).ι)

/-- Unfolding form of `genericFlatnessRestrictModule`. -/
theorem genericFlatnessRestrictModule_def
    (f : X ⟶ S) (ℱ : X.Modules) (U : S.Opens) :
    genericFlatnessRestrictModule f ℱ U = ℱ.restrict ((f ⁻¹ᵁ U).ι) := sorry

/-- An open subset `U ⊆ S` satisfies the generic-flatness conclusion for `f` and `\mathcal F`
when the restricted morphism `X_U → U` is flat and of finite presentation, and the restricted
module `\mathcal F|_{X_U}` is flat over `U` and of finite presentation over `\mathcal O_{X_U}`.
-/
@[stacks 052A]
class GenericFlatnessOn
    (f : X ⟶ S) (ℱ : X.Modules) (U : S.Opens) : Prop extends
    Scheme.Hom.FinitePresentation (f ∣_ U), Flat (f ∣_ U) where
  restrictModule_isFlat :
    (relativeModuleOver (genericFlatnessRestrictModule f ℱ U) (f ∣_ U)).IsFlat
  restrictModule_isFinitePresentation :
    (genericFlatnessRestrictModule f ℱ U).IsFinitePresentation

/-- On a generic-flatness open, the restricted module is flat over the restricted base morphism. -/
instance instIsFlatRestrictModuleOfGenericFlatnessOn
    (f : X ⟶ S) (ℱ : X.Modules) (U : S.Opens) [h : GenericFlatnessOn f ℱ U] :
    (relativeModuleOver (genericFlatnessRestrictModule f ℱ U) (f ∣_ U)).IsFlat :=
  h.restrictModule_isFlat

/-- On a generic-flatness open, the restricted module is of finite presentation over
`\mathcal O_{X_U}`. -/
instance instIsFinitePresentationRestrictModuleOfGenericFlatnessOn
    (f : X ⟶ S) (ℱ : X.Modules) (U : S.Opens) [h : GenericFlatnessOn f ℱ U] :
    (genericFlatnessRestrictModule f ℱ U).IsFinitePresentation :=
  h.restrictModule_isFinitePresentation

/-- Proposition 29.27.1 (Generic flatness): let `f : X ⟶ S` be a morphism of schemes and let `ℱ`
be a quasi-coherent `\mathcal O_X`-module. Assume `S` is integral, `f` is of finite type, and
`ℱ` is of finite type. Then there exists an open dense subscheme `U ⊆ S` such that `X_U → U` is
flat and of finite presentation and `ℱ|_{X_U}` is flat over `U` and of finite presentation over
`\mathcal O_{X_U}`. -/
@[stacks 052A]
theorem exists_dense_open_genericFlatness
    (f : X ⟶ S) [IsIntegral S] [Scheme.Hom.FiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ∃ U : S.Opens, Dense (U : Set S) ∧ GenericFlatnessOn f ℱ U := sorry

end
end

end AlgebraicGeometry.Scheme.Modules
