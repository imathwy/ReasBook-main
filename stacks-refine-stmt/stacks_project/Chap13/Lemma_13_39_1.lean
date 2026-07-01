import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v} D]

/-
Domain-style sampling for Lemma 13.39.1:
- primary domain: Brown representability in triangulated categories, with the canonical
  representability layer owned by Yoneda/preadditive-Yoneda API;
- sampled owner declarations:
  `Functor.IsRepresentable`,
  `Functor.IsRepresentable.mk'`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`,
  `whiskering_preadditiveYoneda`;
- best owner abstraction for the representability conclusion:
  `Functor.IsRepresentable (H ⋙ forget AddCommGrpCat)`;
- primitive data: the subset `S : Set D` together with the source-specific Brown hypotheses
  packaged by `IsBrownRepresentabilitySet S`, the functor `H`, its homologicality, and the
  product-preservation hypothesis `hprod`;
- derived API: the source-facing additive representability statement
  `∃ X, Nonempty (preadditiveYoneda.obj X ≅ H)` and the canonical representability companion for
  the underlying `Type`-valued functor;
- source/core/bridge triage:
  `source-facing`: `brown_representability_of_detecting_factorization_set`;
  `core/canonical`: `(H ⋙ forget AddCommGrpCat).IsRepresentable`;
  `bridge/view`: whiskering the additive Yoneda isomorphism along `forget AddCommGrpCat` and
  rewriting with `whiskering_preadditiveYoneda`.

The Brown-set hypothesis itself stays source-facing primitive data: there is no upstream owner in
the chapter or mathlib for the countable factorization clause, and the nonzero-detection clause is
not merely a duplicate of the stronger separating-owner API. -/

/-- A set of objects satisfying the Stacks-project hypotheses used in Brown representability:
it detects nonzero objects and maps from its objects to countable direct sums factor through
countable direct sums of objects of the same set. -/
structure IsBrownRepresentabilitySet (S : Set D) : Prop where
  /-- Every nonzero object receives a nonzero morphism from some object of `S`. -/
  detects_nonzero_objects {X : D} (hX : ¬ IsZero X) :
    ∃ E : D, E ∈ S ∧ ∃ f : E ⟶ X, f ≠ 0
  /-- Every map from an object of `S` to a countable direct sum factors through a countable direct
  sum of objects of `S`, componentwise. -/
  factors_through_countable_coproducts (X : ℕ → D) {E : D} (hE : E ∈ S) (α : E ⟶ ∐ X) :
    ∃ (E' : ℕ → D), (∀ n : ℕ, E' n ∈ S) ∧
      ∃ (β : ∀ n : ℕ, E' n ⟶ X n) (γ : E ⟶ ∐ E'),
        γ ≫ Limits.Sigma.map β = α

-- Proof sketch: enlarge `S` by all shifts and run the standard Brown approximation argument.
-- Build the tower `X₁ ⟶ X₂ ⟶ ⋯` from all elements of `H(E)` and of the successive kernels, take
-- its homotopy colimit, and use the factorization hypothesis to show the induced comparison
-- `preadditiveYoneda.obj X ⟶ H` is bijective on `S`. The full subcategory on which this
-- comparison is an isomorphism is triangulated and closed under direct sums, so the detecting
-- hypothesis forces it to be all of `D`.
/-- Lemma 13.39.1: if a triangulated category with direct sums admits a set `S` of objects that
detects nonzero objects and through which maps to countable direct sums factor componentwise, then
every contravariant cohomological functor `H : Dᵒᵖ ⥤ AddCommGrpCat` sending direct sums to
products is representable. -/
theorem brown_representability_of_detecting_factorization_set
    (S : Set D) (hS : IsBrownRepresentabilitySet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- Canonical companion: Brown representability for a detecting factorization set implies
representability of the underlying `Type`-valued presheaf, which is the owner abstraction used by
adjoint-functor criteria. -/
theorem brown_representability_of_detecting_factorization_set_isRepresentable
    (S : Set D) (hS : IsBrownRepresentabilitySet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  rcases brown_representability_of_detecting_factorization_set S hS H hH hprod with ⟨X, ⟨e⟩⟩
  exact Functor.IsRepresentable.mk' <| by
    simpa [whiskering_preadditiveYoneda] using
      (Functor.isoWhiskerRight e (forget AddCommGrpCat) :
        preadditiveYoneda.obj X ⋙ forget AddCommGrpCat ≅ H ⋙ forget AddCommGrpCat)

end

end CategoryTheory
