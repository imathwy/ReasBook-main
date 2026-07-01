import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open DerivedCategory

universe w v u uI

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.33.5:
- primary domain: coproducts in derived categories, with the colimit structure owned by
  `IsColimit` and transported along a functor through preservation of the corresponding discrete
  colimit;
- inspected owner declarations:
  `CategoryTheory.Limits.coproductIsCoproduct`,
  `CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit`,
  `CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit`,
  `CategoryTheory.Limits.hasCoproducts_of_colimit_cofans`,
  `CategoryTheory.CountableAB4`;
- best owner abstraction: `PreservesColimit (Discrete.functor K) DerivedCategory.Q`, together with
  the induced canonical `IsColimit` witness on `DerivedCategory.Q.obj (∐ K)` and the resulting
  countable-coproduct owner on `DerivedCategory 𝒜`;
- primitive-vs-derived split:
  the primitive data in this item are the countable family `K` and the exactness hypothesis
  encoded by `CountableAB4 𝒜`, which already carries countable coproducts; the explicit
  `IsColimit` witness for the canonical cofan and the ambient countable-coproduct structure on
  `DerivedCategory 𝒜` are derived API and should be obtained from the owner preservation
  predicate rather than stored primitively.
-/

/-
Source/core/bridge triage for Lemma 13.33.5:
- source-facing: the Stacks lemma says that `DerivedCategory.Q.obj (∐ K)` with the canonical maps
  from the summands is a coproduct of the images of `K`, so the file should expose the resulting
  canonical `IsColimit` witness directly and package it into the ambient countable-coproduct owner
  for `DerivedCategory 𝒜`;
- core/canonical: coproduct preservation for `DerivedCategory.Q`, expressed as
  `PreservesColimit (Discrete.functor K) DerivedCategory.Q`;
- bridge/view: the source-facing coproduct witness is obtained by applying
  `Limits.isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q K` after establishing the
  owner instance below, and arbitrary countable derived families are then handled by choosing
  representatives with `DerivedCategory.Q.objPreimage`; downstream files should reuse these
  bridges instead of rebuilding bespoke `HasCoproduct` witnesses.
-/

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable {α : Type uI}

section

variable [HasCoproductsOfShape α 𝒜] [HasExactColimitsOfShape (Discrete α) 𝒜]

-- Proof sketch: exact countable coproducts imply that the localization functor to the derived
-- category preserves the coproduct of any countable family of cochain complexes.
private theorem derivedCategory_Q_preserves_coproduct_of_exact
    (K : α → CochainComplex 𝒜 ℤ) :
    PreservesColimit (Discrete.functor K) Q := by
  sorry

end

-- `CountableAB4.ofShape` is small-universe, so transport it across `Shrink` for arbitrary
-- countable index types.
private theorem hasExactColimitsOfShape_of_countable
    {C : Type u} [Category.{v} C] [HasCountableCoproducts C] [CountableAB4 C]
    (α : Type uI) [Countable α] :
    HasExactColimitsOfShape (Discrete α) C := by
  letI : Countable (Shrink.{0} α) := Countable.of_equiv α (equivShrink.{0} α)
  letI : HasExactColimitsOfShape (Discrete (Shrink.{0} α)) C :=
    CountableAB4.ofShape (Shrink.{0} α)
  exact HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence (equivShrink.{0} α)).symm

section

variable [HasCountableCoproducts 𝒜] [CountableAB4 𝒜] [Countable α]

-- Proof sketch: recover exactness of `α`-indexed coproducts from the countable `AB4` owner on
-- `𝒜`, then apply the exact-coproduct preservation lemma above.
/-- Exact countable direct sums make the localization functor `DerivedCategory.Q` preserve the
coproduct of any countable family of cochain complexes. -/
theorem derivedCategory_Q_preserves_countableCoproduct
    (K : α → CochainComplex 𝒜 ℤ) :
    PreservesColimit (Discrete.functor K) Q := by
  letI : HasExactColimitsOfShape (Discrete α) 𝒜 := hasExactColimitsOfShape_of_countable α
  exact derivedCategory_Q_preserves_coproduct_of_exact K

/-- The image in the derived category of the termwise direct sum of a countable family of
cochain complexes is a coproduct of the corresponding family of derived-category objects. -/
noncomputable def derivedCategory_coproduct_isColimit_of_termwise_countableDirectSums
    (K : α → CochainComplex 𝒜 ℤ) :
    IsColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i)) :=
  letI := derivedCategory_Q_preserves_countableCoproduct K
  isColimitOfHasCoproductOfPreservesColimit Q K

attribute [instance] derivedCategory_Q_preserves_countableCoproduct

end

section

variable [HasCountableCoproducts 𝒜] [CountableAB4 𝒜]

-- Proof sketch: for each countable index type `α`, transport the small-universe owner
-- `CountableAB4.ofShape` across `Shrink` to recover exactness of `α`-indexed coproducts in `𝒜`,
-- then apply the canonical cofan theorem above to each family of complexes.
/-- Exact countable coproducts in `𝒜` induce `α`-indexed coproducts in `D(\mathcal A)`. -/
noncomputable instance derivedCategory_hasCoproductsOfShape_of_exactCountableCoproducts
    (α : Type uI) [Countable α] :
    HasCoproductsOfShape α (DerivedCategory 𝒜) where
  has_colimit F := by
    letI : HasExactColimitsOfShape (Discrete α) 𝒜 := hasExactColimitsOfShape_of_countable α
    let X : α → DerivedCategory 𝒜 := fun i ↦ F.obj ⟨i⟩
    let K : α → CochainComplex 𝒜 ℤ := fun i ↦ Q.objPreimage (X i)
    let eK : ∀ i, Q.obj (K i) ≅ X i := fun i ↦ Q.objObjPreimageIso (X i)
    let e : Discrete.functor (fun i ↦ Q.obj (K i)) ≅ Discrete.functor X :=
      Discrete.natIso fun i : Discrete α ↦ eK i.as
    have hX :
        IsColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ (eK i).inv ≫ Q.map (Sigma.ι K i)) := by
      exact (IsColimit.precomposeInvEquiv e
        (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i))).symm
        (derivedCategory_coproduct_isColimit_of_termwise_countableDirectSums K)
    refine HasColimit.mk
      ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj
          (Cofan.mk (Q.obj (∐ K)) fun i ↦ (eK i).inv ≫ Q.map (Sigma.ι K i)),
        ?_⟩
    exact (IsColimit.precomposeHomEquiv _ _).symm hX

/-- Exact countable coproducts in `𝒜` induce countable coproducts in `D(\mathcal A)`. -/
noncomputable instance derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts :
    HasCountableCoproducts (DerivedCategory 𝒜) where
  out _ := inferInstance

end

end

end CategoryTheory
