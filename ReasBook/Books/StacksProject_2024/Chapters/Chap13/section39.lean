import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_39_1 (from Chap13) -/
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

/-! ### Proposition_13_39_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']
  [HasCoproducts.{max u₁ v₁} D]

/-
Domain-style sampling for Proposition 13.39.2:
- primary domain: Brown representability and adjunction criteria for exact functors between
  triangulated categories;
- sampled owner declarations:
  `brown_representability_of_detecting_factorization_set_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`,
  `Adjunction.ofIsLeftAdjoint`,
  `Adjunction.isTriangulated_rightAdjoint`;
- best owner abstraction:
  `F.IsLeftAdjoint` for the left-adjoint conclusion, with exactness of the chosen right adjoint
  expressed canonically by `F.rightAdjoint.IsTriangulated`;
- primitive data: the functor `F`, the Brown-representability-set hypothesis `hD`, exactness
  `[F.IsTriangulated]`, and coproduct preservation;
- derived API: the chosen adjunction `Adjunction.ofIsLeftAdjoint F`, its induced right-adjoint
  shift compatibility, and the resulting triangulated structure on `F.rightAdjoint`.

Source/core/bridge triage:
- `source-facing`: the two theorems below, which keep the Brown-representability-set hypothesis
  explicit;
- `core/canonical`: `brown_representability_of_detecting_factorization_set_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`, and
  `Adjunction.isTriangulated_rightAdjoint`;
- `bridge/view`: the chosen adjunction `Adjunction.ofIsLeftAdjoint F` together with
  `Adjunction.rightAdjointCommShift`.
-/

-- Proof sketch: unpack the existence of a Brown-representability set `S`. For each `Y : D'`,
-- apply the canonical Brown-representability companion
-- `brown_representability_of_detecting_factorization_set_isRepresentable` to the contravariant
-- functor `W ↦ Hom(F.obj W, Y)`, using exactness of `F` to get a cohomological functor and
-- preservation of direct sums by `F` to turn coproducts in `D` into products in `AddCommGrpCat`.
-- The resulting objectwise representability hypothesis yields `F.IsLeftAdjoint` via the owner
-- criterion `F.isLeftAdjoint_of_objwise_hom_isRepresentable`.
/-- A coproduct-preserving exact functor out of a triangulated category satisfying the Brown
representability-set hypothesis of Lemma 13.39.1 is a left adjoint. -/
theorem exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, IsBrownRepresentabilitySet S) :
    F.IsLeftAdjoint := sorry

-- Proof sketch: first apply
-- `exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet` to get the chosen adjunction
-- `Adjunction.ofIsLeftAdjoint F`. Then use the canonical shift-compatibility of right adjoints
-- together with `Adjunction.isTriangulated_rightAdjoint` to conclude that the canonical chosen
-- right adjoint `F.rightAdjoint` is triangulated, hence exact.
/-- Proposition 13.39.2: if `D` admits a set of objects satisfying conditions (1) and (2) of
Lemma 13.39.1, then every exact functor `F : D ⥤ D'` of triangulated categories that preserves
arbitrary direct sums has an exact right adjoint. In the canonical API, this is expressed by the
fact that the chosen right adjoint `F.rightAdjoint` is triangulated. -/
theorem exactFunctor_hasExactRightAdjoint_of_exists_brownRepresentabilitySet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, IsBrownRepresentabilitySet S) :
    letI := exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet F hD
    let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
    letI := adj.rightAdjointCommShift ℤ
    F.rightAdjoint.IsTriangulated := by
  letI := exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet F hD
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  exact adj.isTriangulated_rightAdjoint

end

end CategoryTheory
