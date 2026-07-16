import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import stacks_proof.stacks_project.Chap14.Lemma_14_13_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe uC vC uS uI

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

/-- A `0`-simplex of a simplicial set induces a simplex in every degree by pulling back along the
unique map to `[0]`. -/
theorem nonempty_obj_of_nonempty_zero (U : SSet.{uS}) [Nonempty (U _⦋0⦌)]
    (Δ : SimplexCategoryᵒᵖ) : Nonempty (U.obj Δ) :=
  ⟨U.map (SimplexCategory.isTerminalZero.from Δ.unop).op (Classical.choice inferInstance)⟩

/-- Degreewise finite simplicial sets remain degreewise finite after tensoring with a standard
simplex. -/
instance degreewiseFinite_tensor_stdSimplex (U : SSet.{uS})
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] (n : ℕ) :
    ∀ Δ : SimplexCategoryᵒᵖ, Finite ((U ⊗ Δ[n]).obj Δ) := by
  intro Δ
  change Finite (U.obj Δ × (Δ[n] : SSet.{uS}).obj Δ)
  infer_instance

/-- If `U` has a `0`-simplex, then `U ⊗ Δ[n]` also has a `0`-simplex. -/
instance tensor_stdSimplex_objZero_nonempty (U : SSet.{uS}) [Nonempty (U _⦋0⦌)] (n : ℕ) :
    Nonempty ((U ⊗ Δ[n]) _⦋0⦌) := by
  change Nonempty (U _⦋0⦌ × (Δ[n] : SSet.{uS}) _⦋0⦌)
  exact ⟨Classical.choice inferInstance, obj₀Equiv.symm 0⟩

section FiniteNonemptyCoproducts

variable [HasBinaryCoproducts C]

omit [HasBinaryCoproducts C] in
private theorem hasCoproduct_singleton (f : Fin 1 → C) : HasCoproduct f := by
  let c : Cofan f :=
    Cofan.mk (f 0) (fun i ↦ eqToHom (by simpa using congrArg f (Subsingleton.elim i 0)))
  refine HasColimit.mk ⟨c, ?_⟩
  refine mkCofanColimit c (fun s ↦ s.ι.app ⟨0⟩) ?_ ?_
  · intro s j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [c, Cofan.inj]
  · intro s m h
    simpa [c, Cofan.inj] using h 0

/-- A finite nonempty family in a category with binary coproducts admits a coproduct. -/
private theorem hasCoproduct_finSucc (n : ℕ) (f : Fin (n + 1) → C) : HasCoproduct f := by
  induction n with
  | zero =>
      exact hasCoproduct_singleton f
  | succ n ih =>
      let tail : Fin (n + 1) → C := fun i ↦ f i.succ
      haveI : HasCoproduct tail := ih tail
      let c₁ : Cofan tail := colimit.cocone (Discrete.functor tail)
      let c₂ : BinaryCofan (f 0) c₁.pt := colimit.cocone (pair (f 0) c₁.pt)
      exact HasColimit.mk
        ⟨extendCofan c₁ c₂,
          extendCofanIsColimit f (colimit.isColimit (Discrete.functor tail))
            (colimit.isColimit (pair (f 0) c₁.pt))⟩

/-- A finite nonempty family in a category with binary coproducts has a coproduct. This is the
auxiliary existence route used later to construct simplicial copowers from degreewise finiteness
plus one `0`-simplex. -/
noncomputable instance hasCoproduct_of_finite_nonempty {ι : Type uI} [Finite ι] [Nonempty ι]
    (f : ι → C) : HasCoproduct f := by
  classical
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  cases n with
  | zero =>
      exfalso
      exact Fin.elim0 (e (Classical.choice inferInstance))
  | succ n =>
      let g : Fin (n + 1) → C := fun j ↦ f (e.symm j)
      haveI : HasCoproduct g := hasCoproduct_finSucc n g
      exact hasCoproduct_of_equiv_of_iso g f e (fun j ↦ eqToIso (by simp [g]))

/-- Degreewise finiteness plus a `0`-simplex is a sufficient route to the coproduct hypotheses
needed for the simplicial copower owner `U × X`. -/
instance simplicialCopower_hasCoproducts_of_finite_nonempty_zero (U : SSet.{uS})
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)] :
    ∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ) := by
  intro X Δ
  letI : Nonempty (U.obj Δ) := nonempty_obj_of_nonempty_zero U Δ
  infer_instance

end FiniteNonemptyCoproducts

section MappingObject

variable (U : SSet.{uS})
variable
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]

/-- The presheaf `W ↦ Mor(U × W, V)` on simplicial objects, assuming the chapter copower
`U × W` exists for every simplicial object `W`. -/
def simplicialHomPresheaf (V : SimplicialObject C) : (SimplicialObject C)ᵒᵖ ⥤ Type vC :=
  (simplicialCopowerFunctor U).op ⋙ yoneda.obj V

/- Source/core/bridge triage for Definition 14.17.1:
- sampled owner-style declarations in this domain:
  `simplicialCopower`,
  `simplicialCopowerFunctor`,
  `Functor.reprX`,
  `RepresentableBy.homEquiv`
- best owner abstraction: the simplicial mapping object `simplicialHom U V`
- `source-facing`: the mapping object `simplicialHom U V`
- `core/canonical`: the chosen representing object `(simplicialHomPresheaf U V).reprX`
  with representing data `(simplicialHomPresheaf U V).representableBy`
- `bridge/view`: the presheaf `simplicialHomPresheaf U V`
- primitive data: the bridge presheaf `simplicialHomPresheaf U V` together with the chapter owner
  hypothesis that the simplicial copower `U × W` exists for every simplicial object `W`
- auxiliary existence route: under binary coproducts, degreewise finiteness of `U` and one
  `0`-simplex supply those copower hypotheses through the instance
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`
- derived API: the mapping object `simplicialHom U V`; its universal bijection is the canonical
  owner data `(simplicialHomPresheaf U V).representableBy.homEquiv`
- notation decision: the textbook surface `Hom(U, V)` clashes with ordinary morphism notation, and
  mathlib already reserves `SimplicialCategory.sHom` for simplicial categories, so the short owner
  name `simplicialHom` is the public surface here.
-/
/-- Definition 14.17.1: assuming the copowers `U × W` exist for simplicial objects `W`, when the
presheaf `W ↦ Mor(U × W, V)` is representable, its representing object is the simplicial mapping
object from `U` to `V`. -/
@[stacks 017I]
noncomputable abbrev simplicialHom (V : SimplicialObject C)
    [Functor.IsRepresentable (simplicialHomPresheaf U V)] :
    SimplicialObject C :=
  (simplicialHomPresheaf U V).reprX

/- Companion recall: the universal bijection for `simplicialHom U V` is already the canonical
owner data `(simplicialHomPresheaf U V).representableBy.homEquiv`; no parallel local wrapper is
needed. -/

end MappingObject

end CategoryTheory
