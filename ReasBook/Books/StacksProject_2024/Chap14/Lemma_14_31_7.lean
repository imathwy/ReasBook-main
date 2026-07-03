import StacksProject_2024.Chap14.Lemma_14_31_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Simplicial HomotopicalAlgebra

open scoped SSet.modelCategoryQuillen Simplicial

universe u

section

variable {X Y : SimplicialObject GrpCat.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Lemma 14.31.7:
- primary domain: simplicial groups as functor-category objects, together with the Quillen
  fibration predicate on the underlying simplicial-set map;
- sampled owner declarations:
  `NatTrans.epi_iff_epi_app'`,
  `GrpCat.epi_iff_surjective`,
  `HomotopicalAlgebra.Fibration`,
  the source-facing owner theorem `simplicialGroup_kanComplex X`;
- best owner abstraction: the canonical owner bridge from `[Epi f]` to
  `Fibration (Functor.whiskerRight f (forget GrpCat))`, with termwise surjectivity obtained as the
  source-facing bridge to `Epi f`;
- primitive-vs-derived split:
  primitive data: the morphism `f : X ⟶ Y`;
  derived API: the owner hypothesis `[Epi f]`, the induced `Fibration` instance on the underlying
  simplicial-set map, and the termwise-surjectivity bridge to that instance.

Source/core/bridge triage:
- `source-facing`: termwise-surjective morphisms of simplicial groups;
- `core/canonical`: the owner instance
  `[Epi f] : Fibration (Functor.whiskerRight f (forget GrpCat))`;
- `bridge/view`: `NatTrans.epi_iff_epi_app'` together with `GrpCat.epi_iff_surjective`.

The simplicial-abelian-group statements below are only a specialization layer for downstream use;
they are not a second owner abstraction. -/
-- Proof sketch: choose a degreewise preimage of any simplex in `Y`, divide it out to reduce the
-- lifting problem to the kernel simplicial group of `f`, and then apply the canonical
-- Kan-complex theorem from Lemma 14.31.6 to the underlying simplicial set of that simplicial
-- group.
instance [Epi f] :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := sorry

/-- Lemma 14.31.7: a termwise surjective morphism of simplicial groups induces a Kan fibration on
the underlying simplicial sets. -/
theorem simplicialGroup_fibration_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := by
  letI : Epi f := by
    rw [NatTrans.epi_iff_epi_app']
    intro n
    exact (GrpCat.epi_iff_surjective (f.app n)).2 (hsurj n)
  infer_instance

end

section

variable {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)

/-- Specialization of Lemma 14.31.7 to simplicial abelian groups. -/
theorem simplicialAbelianGroup_fibration_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  let g :=
    Functor.whiskerRight
      (Functor.whiskerRight f AddCommGrpCat.toCommGrp)
      (forget₂ CommGrpCat GrpCat)
  have hsurj' :
      ∀ n : SimplexCategoryᵒᵖ,
        Function.Surjective (g.app n) := by
    simpa [g] using hsurj
  simpa [g] using simplicialGroup_fibration_of_termwise_surjective g hsurj'

instance [Epi f] :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  have hf : ∀ n : SimplexCategoryᵒᵖ, Epi (f.app n) := by
    rw [← NatTrans.epi_iff_epi_app']
    infer_instance
  apply simplicialAbelianGroup_fibration_of_termwise_surjective f
  intro n
  exact (AddCommGrpCat.epi_iff_surjective (f.app n)).1 (hf n)

end
