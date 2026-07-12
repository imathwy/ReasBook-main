import StacksProject_2024.Chap21.Lemma_21_7_4_core
import StacksProject_2024.Chap29.Definition_29_25_1
import StacksProject_2024.Chap30.Lemma_30_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped RingedSite.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the source-facing owner here is the tensor flat-base-change comparison for
-- higher direct images. The flatness predicate is the Chapter 29 owner `Scheme.Modules.flatOver`,
-- the base-changed module on `X ×_S S'` is the Chapter 30 owner `baseChangeModule f g ℱ`, the
-- pullback square is expressed by the canonical `pullback f g` with projections `pullback.fst f g`
-- and `pullback.snd f g`, and higher direct images are written through the Chapter 21 owner
-- notation `R^{i}_[f](ℱ)`.

variable {X S S' : Scheme.{u}}
variable [MonoidalCategory S'.Modules]

local notation:max f:max "^*" => Scheme.Modules.pullback f

/-- Lemma 30.7.4: for a cartesian square of schemes
`\xymatrix{
X' \ar[r]^{g'} \ar[d]_{f'} & X \ar[d]^f \\
S' \ar[r]^g & S
}`
with `f` quasi-compact and quasi-separated, a quasi-coherent `\mathcal O_X`-module `\mathcal F`,
and a quasi-coherent `\mathcal O_{S'}`-module `\mathcal G` flat over `S`, the degree-`i` higher
direct image satisfies the flat base-change identification
`\mathcal G \otimes_{\mathcal O_{S'}} g^* R^i f_* \mathcal F \cong
R^i f'_* ((f')^* \mathcal G \otimes_{\mathcal O_{X'}} (g')^* \mathcal F)`. -/
@[stacks 0GN5]
theorem flatBaseChange_higherDirectImage_isomorphic
    (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (pullback f g : Scheme.{u}).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (pullback f g : Scheme.{u}).Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (𝒢 : S'.Modules) [𝒢.IsQuasicoherent]
    (hflat : Scheme.Modules.flatOver 𝒢 g)
    (i : ℕ) :
    IsIsomorphic
      (𝒢 ⊗ ((g^*).obj (R^{i}_[f](ℱ))))
      (R^{i}_[pullback.snd f g]
        (((pullback.snd f g)^*).obj 𝒢 ⊗ baseChangeModule f g ℱ)) := sorry

end AlgebraicGeometry.Scheme
