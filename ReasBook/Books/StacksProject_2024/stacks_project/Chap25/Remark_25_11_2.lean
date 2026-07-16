import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace SSet
namespace OpenHypercovering

-- Semantic search note: `lean_leansearch` recalled `SimplicialObject.Augmented` and
-- `Sheaf.H`/`Sheaf.cohomologyPresheafFunctor`. The local source owner remains
-- `SSet.OpenHypercovering`, with the associated simplicial topological space recorded degreewise.
-- The construction is stated in one universe, matching the fixed-small-universe convention of the
-- source.

variable {X : TopCat.{u}} (H : OpenHypercovering.{u, u} X)

/-- The degree-`n` topological space `U_n = \coprod_{i \in I_n} U_i` associated to an open
hypercovering by indexed opens. -/
@[stacks 02N9]
abbrev simplicialSpaceObj (n : ℕ) : TopCat.{u} :=
  TopCat.of (Σ i : H.I.obj (op <| SimplexCategory.mk n), H.family.openAt i)

/-- The underlying function on degreewise coproducts induced by a simplicial operator. -/
def simplicialSpaceMapFun {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (Σ i : H.I.obj Δ, H.family.openAt i) →
      (Σ i : H.I.obj Δ', H.family.openAt i) :=
  fun x ↦ ⟨H.I.map f x.1, (H.family.map_eq f x.1).symm ▸ x.2⟩

/-- The underlying function on degreewise coproducts induced by a simplicial operator is
continuous. -/
theorem simplicialSpaceMapFun_continuous {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    Continuous (H.simplicialSpaceMapFun f) := sorry

/-- The map of spaces induced by a simplicial operator on the degreewise coproducts of opens. -/
@[stacks 02N9]
def simplicialSpaceMap {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    TopCat.of (Σ i : H.I.obj Δ, H.family.openAt i) ⟶
      TopCat.of (Σ i : H.I.obj Δ', H.family.openAt i) :=
  TopCat.ofHom ⟨H.simplicialSpaceMapFun f, H.simplicialSpaceMapFun_continuous f⟩

/-- The degreewise maps induced by identities are identity maps. -/
theorem simplicialSpaceMap_id (Δ : SimplexCategoryᵒᵖ) :
    H.simplicialSpaceMap (𝟙 Δ) =
      𝟙 (TopCat.of (Σ i : H.I.obj Δ, H.family.openAt i)) := sorry

/-- The degreewise maps induced by composable simplicial operators compose as expected. -/
theorem simplicialSpaceMap_comp {Δ Δ' Δ'' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (g : Δ' ⟶ Δ'') :
    H.simplicialSpaceMap (f ≫ g) =
      H.simplicialSpaceMap f ≫ H.simplicialSpaceMap g := sorry

/-- The explicit simplicial topological space attached to an open hypercovering. -/
@[stacks 02N9]
def simplicialSpace : SimplicialObject TopCat.{u} where
  obj Δ := TopCat.of (Σ i : H.I.obj Δ, H.family.openAt i)
  map f := H.simplicialSpaceMap f
  map_id Δ := H.simplicialSpaceMap_id Δ
  map_comp f g := H.simplicialSpaceMap_comp f g

/-- The underlying map from a degreewise coproduct space to the target topological space. -/
def degreeToBaseFun (n : ℕ) : H.simplicialSpaceObj n → X :=
  fun x ↦ (x.2 : X)

/-- The underlying map from a degreewise coproduct space to the target topological space is
continuous. -/
theorem degreeToBaseFun_continuous (n : ℕ) :
    Continuous (H.degreeToBaseFun n) := sorry

/-- The structure morphism `U_n → X` from the degree-`n` space of the associated simplicial
topological space. -/
@[stacks 02N9]
def degreeToBase (n : ℕ) : H.simplicialSpaceObj n ⟶ X :=
  TopCat.ofHom ⟨H.degreeToBaseFun n, H.degreeToBaseFun_continuous n⟩

/-- The augmentation map from degree `0` of the associated simplicial space to the target
topological space. -/
@[stacks 02N9]
abbrev augmentationZero :
    H.simplicialSpace.obj (op <| SimplexCategory.mk 0) ⟶ X :=
  H.degreeToBase 0

/-- The degree-zero augmentation is compatible with all maps from `0`-simplices, so it defines an
augmented simplicial topological space. -/
theorem augmentationZero_compatible :
    ∀ (i : SimplexCategory) (g₁ g₂ : SimplexCategory.mk 0 ⟶ i),
      H.simplicialSpace.map g₁.op ≫ H.augmentationZero =
        H.simplicialSpace.map g₂.op ≫ H.augmentationZero := sorry

/-- The associated augmented simplicial topological space `U_\bullet → X`. -/
@[stacks 02N9]
def augmentedSimplicialSpace : SimplicialObject.Augmented TopCat.{u} :=
  H.simplicialSpace.augment X H.augmentationZero H.augmentationZero_compatible

/-- The pullback of a sheaf on `X` to the degree-`p` space of the associated simplicial
topological space. -/
@[stacks 02N9]
abbrev degreePullbackSheaf (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (H.simplicialSpaceObj p).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat (H.degreeToBase p)).obj ℱ

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
variable [∀ p : ℕ,
  HasSheafify (Opens.grothendieckTopology (H.simplicialSpaceObj p)) AddCommGrpCat.{u}]
variable [∀ p : ℕ,
  HasExt.{u} ((H.simplicialSpaceObj p).Sheaf AddCommGrpCat.{u})]

/-- Cohomology of an abelian sheaf pulled back to the augmented simplicial topological space
associated to an open hypercovering. This is the source-facing placeholder owner for the
simplicial-space cohomology groups appearing in Remark 25.11.2. -/
@[stacks 02N9]
structure AugmentedSimplicialSpaceCohomology
    (H : OpenHypercovering.{u, u} X)
    (ℱ : X.Sheaf AddCommGrpCat.{u}) where
  /-- The degree-`n` cohomology group of the pulled-back sheaf on `U_\bullet`. -/
  cohomology : ℕ → AddCommGrpCat.{u}
  /-- Cohomological descent identifies the simplicial-space cohomology with sheaf cohomology on
  `X`. -/
  descentIso : ∀ n : ℕ,
    cohomology n ≅ ℱ.H' n (⊤ : Opens X)

/-- Spectral-sequence data comparing the total cohomology of the pullback to the cohomology groups
of the coefficient sheaf over the pieces `U_p` of the associated simplicial topological space. -/
@[stacks 02N9]
structure AugmentedSimplicialSpaceDescentSpectralSequence
    (H : OpenHypercovering.{u, u} X)
    (ℱ : X.Sheaf AddCommGrpCat.{u}) where
  /-- The cohomology groups of the pulled-back sheaf on the associated augmented simplicial space. -/
  simplicialCohomology : AugmentedSimplicialSpaceCohomology H ℱ
  /-- The spectral sequence with source `E₁`-page. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{u} 1
  /-- Its `E₁`-page is `H^q(U_p, ε_p^* ℱ)`, represented here as the cohomology of `ℱ` over the
  degree-`p` coproduct space of the open hypercovering. -/
  pageOneIso :
    ∀ p q : ℕ,
      (spectralSequence.page 1).X (Int.ofNat p, Int.ofNat q) ≅
        (H.degreePullbackSheaf ℱ p).H' q (⊤ : Opens (H.simplicialSpaceObj p))
  /-- The abutment in total degree `n`. -/
  abutment : ℕ → AddCommGrpCat.{u}
  /-- The abutment agrees with the total cohomology of the pulled-back sheaf on `U_\bullet`. -/
  abutmentIso : ∀ n : ℕ, abutment n ≅ simplicialCohomology.cohomology n
  /-- Combining the abutment with cohomological descent gives the cohomology of `X`. -/
  abutmentDescentIso :
    ∀ n : ℕ, abutment n ≅ ℱ.H' n (⊤ : Opens X)

/-- Remark 25.11.2: an open hypercovering gives an augmented simplicial topological space
`U_\bullet → X` along which cohomological descent holds, and for every abelian sheaf `ℱ` on `X`
there is a spectral sequence
`E₁^{p,q} = H^q(U_p, ε_p^*ℱ) ⇒ H^{p+q}(U_\bullet, ε^*ℱ) = H^{p+q}(X, ℱ)`. -/
@[stacks 02N9]
theorem augmentedSimplicialSpace_descentSpectralSequence_exists
    (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    Nonempty (AugmentedSimplicialSpaceDescentSpectralSequence H ℱ) := sorry

end OpenHypercovering
end SSet
