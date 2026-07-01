import Mathlib
import stacks_project.Chap20.Lemma_20_32_3
import stacks_project.Chap20.Lemma_20_32_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section CohomologyPart

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/-- Basiswise vanishing of negative hypercohomology on the preimages `f^{-1}(V)` of basis opens
`V ⊆ Y`. -/
abbrev basiswiseNegativePreimageHypercohomologyVanishing
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (K : DModX) : Prop :=
  ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 →
    ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) K i)

-- Proof sketch: apply Lemma `20.32.6` with `i < 0`. The basiswise vanishing hypothesis says that
-- the presheaf whose sheafification is `H^i(Rf_* K)` is zero on a topological basis, so its
-- sheafification, hence the cohomology sheaf itself, is zero.
/-- Lemma 20.45.2 (1): if `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` is a morphism of ringed
spaces, `𝓑` is a basis for the topology on `Y`, and `K ∈ D(\mathcal O_X)` has
`H^i(f^{-1}(V), K) = 0` for every `V ∈ 𝓑` and every `i < 0`, then the negative cohomology
sheaves of `Rf_* K` vanish. -/
theorem pushforward_negative_cohomologySheaf_isZero_of_basiswise_negative_preimage_hypercohomology
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K : DModX)
    (hK : basiswiseNegativePreimageHypercohomologyVanishing f 𝓑 K) :
    ∀ i : ℤ, i < 0 →
      IsZero (ringedSpaceCohomologySheaf Y ((moduleDerivedPushforward f).obj K) i) := sorry

-- Proof sketch: first use the previous clause to show `H^i(Rf_* K) = 0` for `i < 0`. Then apply
-- Lemma `20.32.6` again to identify `H^i(f^{-1}(V), K)` with sections of the zero sheaf
-- `H^i(Rf_* K)` on an arbitrary open `V ⊆ Y`.
/-- Lemma 20.45.2 (2): under the same basiswise negative-vanishing hypothesis on `K`, one has
`H^i(f^{-1}(V), K) = 0` for every open subset `V ⊆ Y` and every `i < 0`. -/
theorem preimage_negative_hypercohomology_isZero_on_all_opens
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K : DModX)
    (hK : basiswiseNegativePreimageHypercohomologyVanishing f 𝓑 K) :
    ∀ V : Opens Y.carrier, ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) K i) := sorry

section ZeroPresheaf

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]

/-- The presheaf on `Y` given by `V ↦ H^0(f^{-1}(V), K)`, realized as the degree-zero objectwise
cohomology presheaf of `Rf_* K`. -/
abbrev preimageZeroHypercohomologyPresheaf
    (f : X ⟶ Y) (K : DModX) : (Opens Y.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) 0

-- Proof sketch: the previous clause kills the negative cohomology sheaves of `Rf_* K`. Hence
-- `Rf_* K` is concentrated in degrees `≥ 0`, so Lemma `20.32.6` identifies `H^0(Rf_* K)` with the
-- sheafification of the presheaf `V ↦ H^0(f^{-1}(V), K)`, while concentration in nonnegative
-- degrees implies this presheaf already satisfies the sheaf condition.
/-- Lemma 20.45.2 (3): under the same hypotheses, the rule
`V ↦ H^0(f^{-1}(V), K)` is a sheaf on `Y`. In Lean this is the degree-zero objectwise cohomology
presheaf of `Rf_* K`. -/
theorem preimage_zero_hypercohomology_presheaf_isSheaf
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K : DModX)
    (hK : basiswiseNegativePreimageHypercohomologyVanishing f 𝓑 K) :
    TopCat.Presheaf.IsSheaf (preimageZeroHypercohomologyPresheaf f K) := sorry

end ZeroPresheaf

end CohomologyPart

section ExtPart

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

/-- Basiswise vanishing of negative local Ext groups on the preimages `f^{-1}(V)` of basis opens
`V ⊆ Y`, formalized via the negative hypercohomology of the derived internal-Hom object. -/
abbrev basiswiseNegativePreimageExtVanishing
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (K L : DModX) : Prop :=
  ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 →
    ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) ((ihom K).obj L) i)

-- Proof sketch: apply the cohomology part of the lemma to the derived internal-Hom object
-- `R\mathcal H\!\mathit{om}(K, L)`. This is exactly the translation described in
-- Lemma `20.42.1`.
/-- Lemma 20.45.2 (4): if `K, L ∈ D(\mathcal O_X)` satisfy
`\operatorname{Ext}^i(K|_{f^{-1}(V)}, L|_{f^{-1}(V)}) = 0` for every `V ∈ 𝓑` and every `i < 0`,
then the same vanishing holds for every open subset `V ⊆ Y`. In Lean this is stated using the
negative hypercohomology of `R\mathcal H\!\mathit{om}(K, L)` on `f^{-1}(V)`. -/
theorem preimage_negative_ext_isZero_on_all_opens
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K L : DModX)
    (hKL : basiswiseNegativePreimageExtVanishing f 𝓑 K L) :
    ∀ V : Opens Y.carrier, ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) ((ihom K).obj L) i) := sorry

section ZeroDerivedHomPresheaf

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]

/-- The presheaf on `Y` given by the degree-zero local Ext groups
`V ↦ H^0(f^{-1}(V), R\mathcal H\!\mathit{om}(K, L))`; by Lemma `20.42.1` its sections are
canonically identified pointwise with `Hom_{D(\mathcal O_{f^{-1}(V)})}(K|_{f^{-1}(V)},
L|_{f^{-1}(V)})`. -/
abbrev preimageZeroDerivedHomPresheaf
    (f : X ⟶ Y) (K L : DModX) : (Opens Y.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ringedSpaceObjectwiseCohomologyPresheaf Y
    ((moduleDerivedPushforward f).obj ((ihom K).obj L)) 0

-- Proof sketch: apply the zero-degree sheaf statement from the cohomology part to the object
-- `R\mathcal H\!\mathit{om}(K, L)`. Lemma `20.42.1` then identifies this zero-degree Ext presheaf
-- with the presheaf of local derived-Hom groups.
/-- Lemma 20.45.2 (5): under the same basiswise negative Ext-vanishing hypothesis, the rule
`V ↦ \operatorname{Hom}(K|_{f^{-1}(V)}, L|_{f^{-1}(V)})` is a sheaf on `Y`; in Lean this is
formalized via the canonically identified degree-zero internal-Hom presheaf. -/
theorem preimage_zero_derivedHom_presheaf_isSheaf
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K L : DModX)
    (hKL : basiswiseNegativePreimageExtVanishing f 𝓑 K L) :
    TopCat.Presheaf.IsSheaf (preimageZeroDerivedHomPresheaf f K L) := sorry

end ZeroDerivedHomPresheaf

end ExtPart

end AlgebraicGeometry.RingedSpace
