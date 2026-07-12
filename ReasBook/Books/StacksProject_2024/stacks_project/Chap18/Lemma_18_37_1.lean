import Mathlib
import StacksProject_2024.Chap12.Lemma_12_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Φ : GrothendieckTopology.Point J)

/- Domain-style sampling:
- primary domain: the stalk/skyscraper adjunction attached to a site point and the resulting
  exactness statement for the direct image on abelian sheaves;
- sampled owner declarations:
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.skyscraperSheafFunctor`,
  `GrothendieckTopology.Point.skyscraperSheafAdjunction`,
  `exactFunctor`;
- best owner abstraction: the adjunction `Φ.skyscraperSheafAdjunction`, with source-facing
  functor `Φ.skyscraperSheafFunctor`;
- primitive data: the point `Φ`, together with the canonical fiber functor and its
  skyscraper-sheaf right adjoint;
- derived API: exactness of `Φ.skyscraperSheafFunctor` and the split-epi property of the counit;
- source/core/bridge triage:
  `source-facing`: the two Stacks statements below;
  `core/canonical`: `Φ.skyscraperSheafFunctor` and `Φ.skyscraperSheafAdjunction`;
  `bridge/view`: none.

The deleted public abbreviations for `p⁻¹ p_*`, its counit, and the kernel complement were only
derived wrappers around this owner API, so the public surface is refined to the owner declarations
directly. -/

/-- Helper for Lemma 18.37.1: forgetting additive structure reflects epimorphisms of abelian
sheaves back from the underlying sheaves of types. -/
private lemma sheafEpiOfForgetAddCommGrpEpi
    {X Y : Sheaf J AddCommGrpCat.{max u v}} (φ : X ⟶ Y)
    [Epi ((sheafCompose J (forget AddCommGrpCat.{max u v})).map φ)] :
    Epi φ := by
  -- Proof comment: faithful forgetting reflects right-cancellability back to abelian sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (sheafCompose J (forget AddCommGrpCat.{max u v})).map_injective
  apply (cancel_epi ((sheafCompose J (forget AddCommGrpCat.{max u v})).map φ)).1
  simpa using congrArg ((sheafCompose J (forget AddCommGrpCat.{max u v})).map) hgh

/-- Helper for Lemma 18.37.1: the skyscraper-sheaf functor preserves epimorphisms on abelian
sheaves because its underlying set-valued functor maps surjective homomorphisms to split epis. -/
private theorem pointSkyscraperFunctorPreservesEpimorphisms :
    Functor.PreservesEpimorphisms
      (Φ.skyscraperSheafFunctor : AddCommGrpCat.{max u v} ⥤ Sheaf J AddCommGrpCat.{max u v}) := by
  constructor
  intro A B f hf
  let Fadd :
      AddCommGrpCat.{max u v} ⥤ Sheaf J AddCommGrpCat.{max u v} :=
    Φ.skyscraperSheafFunctor
  let Fset :
      Type (max u v) ⥤ Sheaf J (Type (max u v)) :=
    Φ.skyscraperSheafFunctor
  let _ : Epi f := hf
  have hsurj : Function.Surjective ((forget AddCommGrpCat.{max u v}).map f) :=
    (epi_iff_surjective ((forget AddCommGrpCat.{max u v}).map f)).1 inferInstance
  letI : IsSplitEpi ((forget AddCommGrpCat.{max u v}).map f) :=
    (CategoryTheory.isSplitEpi_iff_surjective _).2 hsurj
  -- Proof comment: the underlying set-valued skyscraper map is split epic, hence epic.
  letI : Epi (Fset.map ((forget AddCommGrpCat.{max u v}).map f)) := by infer_instance
  letI : Epi ((sheafCompose J (forget AddCommGrpCat.{max u v})).map (Fadd.map f)) := by
    change Epi (Fset.map ((forget AddCommGrpCat.{max u v}).map f))
    infer_instance
  exact sheafEpiOfForgetAddCommGrpEpi (J := J) (φ := Fadd.map f)

-- Proof sketch: `Φ.skyscraperSheafFunctor` is right adjoint to `Φ.sheafFiber`, hence left exact.
-- For right exactness, use that the counit `p⁻¹ p_* A ⟶ A` admits a functorial section, so
-- `p⁻¹ p_*` splits as `𝟭 ⊞ I`; this forces `p_*` to carry epimorphisms to epimorphisms.
/-- Lemma 18.37.1: for a point `p` of a site, the skyscraper-sheaf functor
`p_* : Ab ⥤ Ab(\mathcal C)` is exact. -/
theorem point_skyscraper_sheaf_functor_exact :
    exactFunctor AddCommGrpCat.{max u v} (Sheaf J AddCommGrpCat.{max u v})
      Φ.skyscraperSheafFunctor := by
  let F := (Φ.skyscraperSheafFunctor : AddCommGrpCat.{max u v} ⥤ Sheaf J AddCommGrpCat.{max u v})
  -- Route correction: `ExactFunctor.of` does not synthesize finite-colimit preservation directly,
  -- so we rebuild exactness from right-adjoint left exactness plus preserved epimorphisms.
  let _ : F.IsRightAdjoint := Φ.skyscraperSheafAdjunction.isRightAdjoint
  let _ : PreservesFiniteLimits F := inferInstance
  have hLeft : leftExactFunctor _ _ F := by
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits F)
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F) (.inl hLeft)
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let _ : F.PreservesEpimorphisms := pointSkyscraperFunctorPreservesEpimorphisms (Φ := Φ)
  -- Proof comment: in the abelian target, preserving epis and kernels upgrades to finite colimits.
  let _ : F.PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels F
  let _ : PreservesFiniteColimits F :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology F
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

-- Proof sketch: the unit-counit identities give a functorial section of the counit
-- `p⁻¹ p_* ⟶ 𝟭`; in an abelian category, this split epimorphism is equivalent to a functorial
-- biproduct decomposition.
/-- The counit `p⁻¹ p_* ⟶ 𝟭` of the skyscraper-sheaf adjunction is a split epimorphism. -/
theorem point_skyscraper_counit_isSplitEpi :
    IsSplitEpi
      (Φ.skyscraperSheafAdjunction.counit : _ ⟶ 𝟭 AddCommGrpCat.{max u v}) := by
  -- TODO: build a natural section by transporting the presheaf-fiber constant-family generator
  -- through the bundled `sheafFiber`/counit API. The remaining blocker is a canonical bridge from
  -- the presheaf-fiber formulas `toPresheafFiber` and `skyscraperPresheafHomEquiv.symm` to the
  -- bundled sheaf-level counit component without unfolding the full sheaf wrapper by hand.
  sorry
