import Mathlib.AlgebraicGeometry.Pullbacks

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Pullback

-- Semantic recall: `lean_leansearch` pointed to `Scheme.Pullback.openCoverOfBase` and
-- `Scheme.Pullback.openCoverOfLeftRight` as the canonical cover constructors for this statement.

variable {S X Y : Scheme}

section

variable (f : X ⟶ S) (g : Y ⟶ S) (𝒰 : S.AffineOpenCover)
variable (𝒱 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover)
variable (𝒲 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ g).X i).AffineOpenCover)

/-- Helper for Lemma 26.17.4: the canonical open cover of `X ×_S Y` obtained from an affine open
cover of `S` and affine open covers of the corresponding local preimages in `X` and `Y`. -/
@[simps! I₀ X f]
noncomputable def pullbackOpenCover
    :
    (pullback f g).OpenCover :=
  (openCoverOfBase 𝒰.openCover f g).bind fun i ↦
    openCoverOfLeftRight
      (𝒱 i).openCover
      (𝒲 i).openCover
      (𝒰.openCover.pullbackHom f i)
      (𝒰.openCover.pullbackHom g i)

/-- Lemma 26.17.4 (1): for an affine open cover `𝒰` of `S` and affine open covers `𝒱 i`,
`𝒲 i` of the local preimages in `X` and `Y`, each member of the induced cover of `X ×_S Y`
is affine. -/
@[stacks 01JS]
theorem pullbackOpenCover_isAffine
    (I : (pullbackOpenCover f g 𝒰 𝒱 𝒲).I₀) :
    IsAffine ((pullbackOpenCover f g 𝒰 𝒱 𝒲).X I) := by
  rcases I with ⟨i, j⟩
  change
    IsAffine
      ((openCoverOfLeftRight
        (𝒱 i).openCover
        (𝒲 i).openCover
        (𝒰.openCover.pullbackHom f i)
        (𝒰.openCover.pullbackHom g i)).X j)
  rcases j with ⟨j, k⟩
  rw [openCoverOfLeftRight_X]
  letI : IsAffine ((𝒱 i).openCover.X j) := inferInstance
  letI : IsAffine ((𝒲 i).openCover.X k) := inferInstance
  letI : IsAffine (𝒰.openCover.X i) := inferInstance
  infer_instance

/-- Lemma 26.17.4 (1): for an affine open cover `𝒰` of `S` and affine open covers `𝒱 i`,
`𝒲 i` of the local preimages in `X` and `Y`, each member of the induced cover of `X ×_S Y`
is an affine open subset. -/
@[stacks 01JS]
theorem pullbackOpenCover_isAffineOpen
    (I : (pullbackOpenCover f g 𝒰 𝒱 𝒲).I₀) :
    IsAffineOpen (((pullbackOpenCover f g 𝒰 𝒱 𝒲).f I).opensRange) := by
  letI : IsAffine ((pullbackOpenCover f g 𝒰 𝒱 𝒲).X I) := by
    simpa using pullbackOpenCover_isAffine f g 𝒰 𝒱 𝒲 I
  simpa using isAffineOpen_opensRange ((pullbackOpenCover f g 𝒰 𝒱 𝒲).f I)

/-- Lemma 26.17.4 (2): the affine open subsets coming from the local fibre products over the
members of `𝒰` cover the ambient fibre product `X ×_S Y`. -/
@[stacks 01JS]
theorem pullbackOpenCover_isOpenCover
    :
    TopologicalSpace.IsOpenCover
      (fun I : (pullbackOpenCover f g 𝒰 𝒱 𝒲).I₀ ↦
        ((pullbackOpenCover f g 𝒰 𝒱 𝒲).f I).opensRange) :=
  (pullbackOpenCover f g 𝒰 𝒱 𝒲).isOpenCover_opensRange

end

end AlgebraicGeometry
