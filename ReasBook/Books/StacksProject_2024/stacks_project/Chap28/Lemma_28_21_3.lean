import StacksProject_2024.Chap17.Lemma_17_10_4
import StacksProject_2024.Chap28.Definition_28_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance pullback_isQuasicoherent
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj 𝒢).IsQuasicoherent := by
  simpa using ringedSpaceModulePullback_isQuasicoherent f 𝒢

-- Semantic recall note: the source-facing owner is `IsLocallyProjective` on scheme modules. The
-- supporting canonical APIs are the ringed-site quasi-coherence pullback theorem
-- `ringedSpaceModulePullback_isQuasicoherent`, the affine-cover criterion
-- `isLocallyProjective_iff_exists_affineOpenCover_projectiveSections`, and the module-theoretic
-- base-change projectivity recall `Projective.tensorProduct`.

-- Proof sketch: apply the affine-cover criterion from `Lemma 28.21.2`, pull that affine cover
-- back along `f`, and on each affine preimage use that pullback sections identify with a scalar
-- extension of the original affine sections. Then Lemma `10.94.1` supplies projectivity after
-- base change.
namespace IsLocallyProjective

/-- Lemma 28.21.3: if `f : X ⟶ Y` is a morphism of schemes and `\mathcal G` is a locally
projective quasi-coherent `\mathcal O_Y`-module, then `f^*\mathcal G` is locally projective on
`X`. -/
@[stacks 060M]
theorem pullback
    (f : X ⟶ Y) {𝒢 : Y.Modules} [𝒢.IsQuasicoherent]
    (h𝒢 : IsLocallyProjective 𝒢) :
    IsLocallyProjective ((Scheme.Modules.pullback f).obj 𝒢) := sorry

end IsLocallyProjective

/-- Pullback along a morphism of schemes preserves locally projective quasi-coherent modules. -/
instance instIsLocallyProjective_pullback
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] [h𝒢 : IsLocallyProjective 𝒢] :
    IsLocallyProjective ((Scheme.Modules.pullback f).obj 𝒢) :=
  h𝒢.pullback f

end AlgebraicGeometry.Scheme.Modules
