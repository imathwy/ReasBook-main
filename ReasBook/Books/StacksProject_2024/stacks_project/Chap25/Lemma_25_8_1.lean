import Mathlib
import StacksProject_2024.Chap14.Lemma_14_21_7
import StacksProject_2024.Chap14.Lemma_14_21_11
import StacksProject_2024.Chap25.Lemma_25_3_2
import StacksProject_2024.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open CategoryTheory.Limits
open Opposite
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` recalled mathlib's simplex-boundary owners, but the
-- source-facing Chapter 25 statement lives on the verified local internal-hom restriction map
-- and the covering-morphism predicate on `SR(C, X)`.

/-- Fixed-target semi-representable families inherit binary coproducts from the coproducts
constructed earlier for `SR(C, X)`. This is the canonical coproduct layer needed by the simplicial
mapping-object owner `simplicialHom`. -/
instance semiRepresentableFamilyOver_hasBinaryCoproducts (X : C) :
    HasBinaryCoproducts (SemiRepresentableFamily.Over.{v, u, w} X) := by
  infer_instance

/-- Fixed-target semi-representable families inherit finite limits from the Chapter 25 finite-limit
construction on `SR(C, X)`. This is the canonical limit layer needed by simplicial mapping
objects with target in `SR(C, X)`. -/
instance semiRepresentableFamilyOver_hasFiniteLimits (X : C) :
    HasFiniteLimits (SemiRepresentableFamily.Over.{v, u, w} X) := by
  infer_instance

/-- For a finite simplicial set with a `0`-simplex, the Chapter 14 simplicial mapping-object
presheaf is representable. The only additional input is the canonical eventual-dimension bound
coming from `SSet.hasDimensionLT_of_finite`. -/
instance simplicialHomPresheaf_isRepresentable_of_finite
    (U : SSet.{w}) [U.Finite] [Nonempty (U _⦋0⦌)]
    (T : SimplicialObject C)
    [HasBinaryCoproducts C] [HasFiniteLimits C]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)] :
    Functor.IsRepresentable (simplicialHomPresheaf U T) := by
  let _ : Fact (∃ d : ℕ, U.HasDimensionLE d) := ⟨by
    have hdim : ∃ d : ℕ, U.HasDimensionLT d := SSet.hasDimensionLT_of_finite U
    rcases hdim with ⟨d, hd⟩
    let _ : U.HasDimensionLT d := hd
    exact ⟨d, (by infer_instance : U.HasDimensionLE d)⟩⟩
  infer_instance

/-- Precomposition by a simplicial-set morphism induces the corresponding morphism on simplicial
mapping objects. This is the local Chapter 25 bridge to the Chapter 14 internal-hom owner
`simplicialHom`, avoiding any parallel wrapper on `Hom(U, T)`. -/
def simplicialHomPrecomp
    {U V : SSet.{w}} (a : U ⟶ V) (T : SimplicialObject C)
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    [Functor.IsRepresentable (simplicialHomPresheaf U T)]
    [Functor.IsRepresentable (simplicialHomPresheaf V T)] :
    simplicialHom V T ⟶ simplicialHom U T :=
  let eU :
      (simplicialHom V T ⟶ simplicialHom U T) ≃
        (U × simplicialHom V T ⟶ T) :=
    (simplicialHomPresheaf U T).representableBy.homEquiv
  let eV :
      (simplicialHom V T ⟶ simplicialHom V T) ≃
        (V × simplicialHom V T ⟶ T) :=
    (simplicialHomPresheaf V T).representableBy.homEquiv
  eU.symm (simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _))

/-- Unfolding `simplicialHomPrecomp` gives the representing-equivalence formula defining the
restriction morphism on simplicial mapping objects. -/
theorem simplicialHomPrecomp_def
    {U V : SSet.{w}} (a : U ⟶ V) (T : SimplicialObject C)
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    [Functor.IsRepresentable (simplicialHomPresheaf U T)]
    [Functor.IsRepresentable (simplicialHomPresheaf V T)] :
    simplicialHomPrecomp a T =
      let eU :
          (simplicialHom V T ⟶ simplicialHom U T) ≃
            (U × simplicialHom V T ⟶ T) :=
        (simplicialHomPresheaf U T).representableBy.homEquiv
      let eV :
          (simplicialHom V T ⟶ simplicialHom V T) ≃
            (V × simplicialHom V T ⟶ T) :=
        (simplicialHomPresheaf V T).representableBy.homEquiv
      eU.symm (simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _)) := sorry

/-- Lemma 25.8.1: let `K` be a hypercovering of `X`, and let `U ⊆ V` be obtained by adjoining one
nondegenerate simplex whose boundary already lands in `U`. In Lean, the source's single-step
extension data are encoded by a subcomplex `U : V.Subcomplex`, a missing nondegenerate simplex
`x : U.N`, the boundary condition `x.boundary_range_le`, the generation condition
`U ⊔ SSet.Subcomplex.ofSimplex x.simplex = ⊤`, the ambient finiteness instance `V.Finite`, and the
degreewise nonemptiness assumptions on `U` and `V`. Then the induced restriction morphism
`Hom(V, K)_0 ⟶ Hom(U, K)_0` in `SR(C, X)` is covering, formalized as the degree-`0` component of
`simplicialHomPrecomp U.ι K.toSimplicialObject`. -/
@[stacks 01GM]
theorem hypercoveringHomZeroPrecomp_isCovering_of_singleSimplexExtension
    {X : C} {V : SSet.{w}} [V.Finite]
    (U : V.Subcomplex)
    [Nonempty ((U : SSet) _⦋0⦌)]
    [Nonempty (V _⦋0⦌)]
    (hU_nonempty : ∀ n : ℕ, Nonempty ((U : SSet) _⦋n⦌))
    (hV_nonempty : ∀ n : ℕ, Nonempty (V _⦋n⦌))
    (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ SSet.Subcomplex.ofSimplex x.simplex = ⊤)
    (K : @Hypercovering C _ J X) :
    Hom.IsCovering J
      ((simplicialHomPrecomp U.ι K.toSimplicialObject).app (op ⦋0⦌)) := sorry

end CategoryTheory
