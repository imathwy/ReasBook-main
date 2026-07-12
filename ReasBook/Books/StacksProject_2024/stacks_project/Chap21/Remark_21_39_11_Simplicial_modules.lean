import StacksProject_2024.Chap14.Lemma_14_23_1
import StacksProject_2024.Chap14.Example_14_26_7
import StacksProject_2024.Chap21.Lemma_21_39_7
import StacksProject_2024.Chap21.Lemma_21_39_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicTopology
open Opposite
open scoped DoldKan Simplicial

noncomputable section

universe u

namespace CategoryTheory

/- Domain-style sampling for Remark 21.39.11:
- primary domain: simplicial `B`-modules and their associated alternating-face-map chain complexes;
- sampled owner/bridge declarations:
  `AlgebraicTopology.alternatingFaceMapComplex`,
  `AlgebraicTopology.DoldKan` notation `s[_]`,
  `CategoryTheory.moduleCosimplicialEvaluationChainComplex`,
  `CategoryTheory.categoryOverPointDerivedColimit_tensorProjectionInverseImages_isomorphic`;
- best owner abstraction: the chapter-owner functor `alternatingFaceMapComplex (ModuleCat B)`,
  used on the theorem surface through the canonical notation `s[M]`;
- primitive data: the simplicial modules `M`, `M'` and the source-facing termwise-flatness
  hypotheses `∀ n, Module.Flat B (M _⦋n⦌)` and `∀ n, Module.Flat B (M' _⦋n⦌)`;
- derived API here: the quasi-isomorphism statement for the simplicial tensor comparison.

Source/core/bridge triage:
- `source-facing`: the quasi-isomorphism statement for simplicial modules in the Stacks remark;
- `core/canonical`: `alternatingFaceMapComplex (ModuleCat B)` and its notation `s[_]`;
- `bridge/view`: none beyond using the canonical owner notation directly in place of a local
  duplicate wrapper. -/

/-- Helper for Remark 21.39.11 (Simplicial modules): the identity cosimplicial object on
`SimplexCategory` satisfies the pointlike-hom-spaces hypothesis from Lemma `21.39.7`. -/
lemma simplex_identity_has_pointlike_hom_spaces :
    CosimplicialObjectHasPointlikeHomSpaces (𝟭 SimplexCategory) := by
  intro U
  induction U using SimplexCategory.rec with
  | _ m =>
      -- For `U = [m]`, the simplicial mapping set is the standard simplex `Δ[m]`.
      -- Example `14.26.7` contracts `Δ[m]` to the point `Δ[0]`.
      refine ⟨?_⟩
      let hrepr : (cosimplicialHomSSet (𝟭 SimplexCategory) ⦋m⦌).RepresentableBy ⦋m⦌ := by
        refine ⟨?_, ?_⟩
        · intro X
          refine
            { toFun := fun g ↦ by
                simpa [CategoryTheory.cosimplicialSimplicialEquiv_functor_obj_obj] using g
              invFun := fun g ↦ by
                simpa [CategoryTheory.cosimplicialSimplicialEquiv_functor_obj_obj] using g
              left_inv := by
                intro g
                simp [CategoryTheory.cosimplicialSimplicialEquiv_functor_obj_obj]
              right_inv := by
                intro g
                simp [CategoryTheory.cosimplicialSimplicialEquiv_functor_obj_obj] }
        · intro X Y f g
          rfl
      let e : (Δ[m] : SSet) ≅ cosimplicialHomSSet (𝟭 SimplexCategory) ⦋m⦌ :=
        SSet.stdSimplex.isoOfRepresentableBy hrepr
      exact (SimplicialObject.HomotopyEquiv.ofIso e.symm).trans
        (SSet.stdSimplex.homotopyEquivPoint m)

-- Proof sketch: specialize Lemma `21.39.10` to `𝒞 = Δ`, where `Lπ!` is computed
-- by the alternating face map complex. Termwise flatness identifies the derived tensor products
-- with ordinary tensor products, and the resulting comparison map is the simplicial
-- Eilenberg-Zilber quasi-isomorphism.
/-- Remark 21.39.11 (Simplicial modules): if `M_•` and `M'_•` are termwise flat simplicial
`B`-modules, then the associated complex of their pointwise tensor product is quasi-isomorphic to
the tensor product of the associated complexes `s[M_•]` and `s[M'_•]`. -/
@[stacks 08QD]
theorem exists_quasiIso_alternatingFaceMapComplex_tensor_of_termwiseFlat
    {B : Type u} [CommRing B] (M M' : SimplicialObject (ModuleCat B))
    (hM : ∀ n : ℕ, Module.Flat B (M _⦋n⦌))
    (hM' : ∀ n : ℕ, Module.Flat B (M' _⦋n⦌)) :
    ∃ α : s[M ⊗ M'] ⟶ s[M] ⊗ s[M'], QuasiIso α := sorry

end CategoryTheory
