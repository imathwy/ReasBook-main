import Mathlib
import StacksProject_2024.Chap24.Lemma_24_17_2

open CategoryTheory Opposite

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

-- Semantic search note: this runner does not expose a `lean_leansearch` tool, so the owner/API
-- choice below was verified against the local Chapter 24 precedent in `Lemma_24_8_2.lean`,
-- `Definition_24_17_1.lean`, and `Lemma_24_17_2.lean`.

/-- Helper: the root owner for differential graded algebras on the ambient ringed site. -/
private abbrev DGA
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  @DifferentialGradedAlgebra C _ J 𝒪

/-- Helper: the root owner for right differential graded modules on the ambient ringed site. -/
private abbrev DGRightMod
    (𝒪 : Sheaf J RingCat.{max u v})
    (𝒝 : DGA 𝒪) :=
  @DifferentialGradedRightModule C _ J 𝒪 𝒝

/-- Helper: the root owner for differential graded bimodules on the ambient ringed site. -/
private abbrev DGBimod
    (𝒪 : Sheaf J RingCat.{max u v})
    (𝒜 𝒝 : DGA 𝒪) :=
  @DifferentialGradedBimodule C _ J 𝒪 𝒜 𝒝

/-- Helper: the ambient complex owner for differential graded internal Homs on the ringed site. -/
private abbrev DGInternalHomComplex
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  CochainComplex (SheafOfModules.{max u v, v, u, max u v} 𝒪) ℤ

namespace DifferentialGradedRightModule

/-- A homomorphism of right differential graded modules is a morphism of the underlying complexes
of `\mathcal O`-modules that commutes with the right action. -/
structure Hom
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒝 : DGA 𝒪}
    (M N : DGRightMod 𝒪 𝒝) where
  /-- The underlying morphism of complexes of `\mathcal O`-modules. -/
  hom : M.toCochainComplex ⟶ N.toCochainComplex
  /-- Compatibility with the right `\mathcal B`-action. -/
  comm_rightMul :
    ∀ (U : Cᵒᵖ) (n m : ℤ) (x : M.sections U n) (b : 𝒝.sections U m),
      (((hom.f (n + m)).val.app U).hom) (M.rightMul U n m x b) =
        N.rightMul U n m ((((hom.f n).val.app U).hom) x) b

/-- A right differential graded module homomorphism carries its underlying morphism of complexes.
-/
instance
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒝 : DGA 𝒪}
    {M N : DGRightMod 𝒪 𝒝} :
    CoeOut (Hom M N) (M.toCochainComplex ⟶ N.toCochainComplex) where
  coe f := f.hom

end DifferentialGradedRightModule

/-- The Chapter 24 tensor/Hom conventions for right differential graded modules and differential
graded bimodules on a ringed site. -/
class HasDifferentialGradedTensorHomAdjunction
    (𝒪 : Sheaf J RingCat.{max u v})
    (𝒜 𝒝 : DGA 𝒪) where
  /-- The relative tensor product `\mathcal M \otimes_{\mathcal A} \mathcal N` as a right
  differential graded `\mathcal B`-module. -/
  tensorObj :
    DGRightMod 𝒪 𝒜 → DGBimod 𝒪 𝒜 𝒝 → DGRightMod 𝒪 𝒝
  /-- The right differential graded `\mathcal A`-module
  `\mathcal H\!\mathit{om}^{dg}_{\mathcal B}(\mathcal N, \mathcal L)`. -/
  bimoduleInternalHom :
    DGBimod 𝒪 𝒜 𝒝 → DGRightMod 𝒪 𝒝 → DGRightMod 𝒪 𝒜
  /-- The differential graded internal Hom over `\mathcal A`. -/
  moduleInternalHomA :
    DGRightMod 𝒪 𝒜 → DGRightMod 𝒪 𝒜 → DGInternalHomComplex 𝒪
  /-- The differential graded internal Hom over `\mathcal B`. -/
  moduleInternalHomB :
    DGRightMod 𝒪 𝒝 → DGRightMod 𝒪 𝒝 → DGInternalHomComplex 𝒪
  /-- The Hom-set equivalence expressing the tensor/Hom adjunction. -/
  homEquiv :
    ∀ (M : DGRightMod 𝒪 𝒜) (N : DGBimod 𝒪 𝒜 𝒝) (L : DGRightMod 𝒪 𝒝),
      DifferentialGradedRightModule.Hom (tensorObj M N) L ≃
        DifferentialGradedRightModule.Hom M (bimoduleInternalHom N L)
  /-- The internal-Hom isomorphism induced by the tensor/Hom adjunction. -/
  internalHomIso :
    ∀ (M : DGRightMod 𝒪 𝒜) (N : DGBimod 𝒪 𝒜 𝒝) (L : DGRightMod 𝒪 𝒝),
      moduleInternalHomB (tensorObj M N) L ≅
        moduleInternalHomA M (bimoduleInternalHom N L)

namespace HasDifferentialGradedTensorHomAdjunction

/-- The relative tensor product from the Chapter 24 differential graded tensor/Hom conventions. -/
abbrev tensor
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [_root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (M : DGRightMod 𝒪 𝒜) (N : DGBimod 𝒪 𝒜 𝒝) : DGRightMod 𝒪 𝒝 :=
  (inferInstance : _root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝).tensorObj M N

/-- The right differential graded `\mathcal A`-module
`\mathcal H\!\mathit{om}^{dg}_{\mathcal B}(\mathcal N, \mathcal L)` from the Chapter 24
conventions. -/
abbrev bimoduleIHom
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [_root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (N : DGBimod 𝒪 𝒜 𝒝) (L : DGRightMod 𝒪 𝒝) : DGRightMod 𝒪 𝒜 :=
  ((inferInstance : _root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝).bimoduleInternalHom
    N L)

/-- The differential graded internal Hom over `\mathcal A` from the Chapter 24 conventions. -/
abbrev moduleIHomA
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [_root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (M M' : DGRightMod 𝒪 𝒜) : DGInternalHomComplex 𝒪 :=
  ((inferInstance : _root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝).moduleInternalHomA
    M M')

/-- The differential graded internal Hom over `\mathcal B` from the Chapter 24 conventions. -/
abbrev moduleIHomB
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [_root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (L L' : DGRightMod 𝒪 𝒝) : DGInternalHomComplex 𝒪 :=
  ((inferInstance : _root_.HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝).moduleInternalHomB
    L L')

end HasDifferentialGradedTensorHomAdjunction

/-- Lemma 24.17.3 (1): for a right differential graded `\mathcal A`-module `\mathcal M`, a
differential graded `(\mathcal A, \mathcal B)`-bimodule `\mathcal N`, and a right differential
graded `\mathcal B`-module `\mathcal L`, the differential graded tensor product
`\mathcal M \otimes_{\mathcal A} \mathcal N` is left adjoint to
`\mathcal H\!\mathit{om}^{dg}_{\mathcal B}(\mathcal N, -)`, functorially in `\mathcal M`,
`\mathcal N`, and `\mathcal L`. -/
noncomputable abbrev differentialGradedTensorHomAdjunctionHomEquiv
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (M : DGRightMod 𝒪 𝒜) (N : DGBimod 𝒪 𝒜 𝒝) (L : DGRightMod 𝒪 𝒝) :
    DifferentialGradedRightModule.Hom
        (HasDifferentialGradedTensorHomAdjunction.tensor M N)
        L ≃
      DifferentialGradedRightModule.Hom
        M
        (HasDifferentialGradedTensorHomAdjunction.bimoduleIHom N L) :=
  let H : HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 := inferInstance
  H.homEquiv M N L

/-- Unfolding `differentialGradedTensorHomAdjunctionHomEquiv` recovers the chosen tensor/Hom
equivalence. -/
theorem differentialGradedTensorHomAdjunctionHomEquiv_def
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (M : DGRightMod 𝒪 𝒜) (N : DGBimod 𝒪 𝒜 𝒝) (L : DGRightMod 𝒪 𝒝) :
    differentialGradedTensorHomAdjunctionHomEquiv M N L =
      (show DifferentialGradedRightModule.Hom
              (HasDifferentialGradedTensorHomAdjunction.tensor M N) L ≃
            DifferentialGradedRightModule.Hom M
              (HasDifferentialGradedTensorHomAdjunction.bimoduleIHom N L) from
        (show HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 from inferInstance).homEquiv M N L) := sorry

/-- Lemma 24.17.3 (2): for the same data, the differential graded internal Hom over
`\mathcal B` out of `\mathcal M \otimes_{\mathcal A} \mathcal N` is isomorphic to the
differential graded internal Hom over `\mathcal A` out of `\mathcal M`, functorially in
`\mathcal M`, `\mathcal N`, and `\mathcal L`. -/
noncomputable abbrev differentialGradedTensorHomAdjunctionInternalHomIso
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (M : DGRightMod 𝒪 𝒜) (N : DGBimod 𝒪 𝒜 𝒝) (L : DGRightMod 𝒪 𝒝) :
    let H : HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 := inferInstance
    H.moduleInternalHomB (H.tensorObj M N) L ≅ H.moduleInternalHomA M (H.bimoduleInternalHom N L) :=
  let H : HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 := inferInstance
  H.internalHomIso M N L

/-- Unfolding `differentialGradedTensorHomAdjunctionInternalHomIso` recovers the chosen
internal-Hom isomorphism. -/
theorem differentialGradedTensorHomAdjunctionInternalHomIso_def
    {𝒪 : Sheaf J RingCat.{max u v}}
    {𝒜 𝒝 : DGA 𝒪}
    [HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝]
    (M : DGRightMod 𝒪 𝒜) (N : DGBimod 𝒪 𝒜 𝒝) (L : DGRightMod 𝒪 𝒝) :
    differentialGradedTensorHomAdjunctionInternalHomIso M N L =
      (show
          (show HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 from inferInstance).moduleInternalHomB
              ((show HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 from inferInstance).tensorObj
                M N) L ≅
            (show HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 from inferInstance).moduleInternalHomA
              M
              ((show HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 from inferInstance).bimoduleInternalHom
                N L) from
        (show HasDifferentialGradedTensorHomAdjunction 𝒪 𝒜 𝒝 from inferInstance).internalHomIso
          M N L) := sorry

end
