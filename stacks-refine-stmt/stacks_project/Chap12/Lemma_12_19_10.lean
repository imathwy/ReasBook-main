import stacks_project.Chap12.Definition_12_19_3

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

open FilteredObject.Hom

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.10:
- source-facing: strictness of the right map in a filtered pushout square, and the resulting
  existence statement
- core/canonical owner: `IsPushout f g g' f'`, specialized to `HasPushout f g` and `pushout.inr f g`
- bridge/view: the stagewise-image filtration model on the ambient pushout of `f.hom` and `g.hom`
-/

private noncomputable def pushoutStageMap (f : A ⟶ B) (g : A ⟶ C) (p : ℤ) :
    ((B.filtration p : 𝒜) ⊞ (C.filtration p : 𝒜)) ⟶ pushout f.hom g.hom :=
  biprod.desc
    ((B.filtration p).arrow ≫ pushout.inl f.hom g.hom)
    ((C.filtration p).arrow ≫ pushout.inr f.hom g.hom)

private theorem pushoutFiltration_antitone (f : A ⟶ B) (g : A ⟶ C) :
    Antitone fun p ↦ imageSubobject (pushoutStageMap f g p) := by
  sorry

private noncomputable def pushoutModel (f : A ⟶ B) (g : A ⟶ C) : FilteredObject 𝒜 where
  obj := pushout f.hom g.hom
  filtration :=
    { toFun := fun p ↦ imageSubobject (pushoutStageMap f g p)
      monotone' := by
        intro p q hpq
        exact pushoutFiltration_antitone f g hpq }

private theorem pushoutModelInl_preserves (f : A ⟶ B) (g : A ⟶ C) :
    ∀ p : ℤ,
      ((pushoutModel f g).filtration p).Factors
        ((B.filtration p).arrow ≫ pushout.inl f.hom g.hom) :=
  by
    sorry

private theorem pushoutModelInr_preserves (f : A ⟶ B) (g : A ⟶ C) :
    ∀ p : ℤ,
      ((pushoutModel f g).filtration p).Factors
        ((C.filtration p).arrow ≫ pushout.inr f.hom g.hom) :=
  by
    sorry

private noncomputable def pushoutModelInl (f : A ⟶ B) (g : A ⟶ C) : B ⟶ pushoutModel f g where
  hom := pushout.inl f.hom g.hom
  preserves := pushoutModelInl_preserves f g

private noncomputable def pushoutModelInr (f : A ⟶ B) (g : A ⟶ C) : C ⟶ pushoutModel f g where
  hom := pushout.inr f.hom g.hom
  preserves := pushoutModelInr_preserves f g

private theorem pushoutModel_isPushout (f : A ⟶ B) (g : A ⟶ C) :
    IsPushout f g (pushoutModelInl f g) (pushoutModelInr f g) := by
  sorry

noncomputable instance hasPushout (f : A ⟶ B) (g : A ⟶ C) : HasPushout f g :=
  (pushoutModel_isPushout f g).hasPushout

/-- In a pushout square of filtered objects, strictness of the left map forces strictness of the
right map. -/
theorem strict_inr_of_isPushout_of_strict
    {P : FilteredObject 𝒜} {g' : B ⟶ P} {f' : C ⟶ P}
    (sq : IsPushout f g g' f') (hf : Strict f) :
    Strict f' := by
  sorry

/-- In the canonical pushout square of filtered objects, strictness of the left map forces
strictness of the induced map on the right. -/
theorem strict_pushout_inr_of_strict (f : A ⟶ B) (g : A ⟶ C) (hf : Strict f) :
    Strict (pushout.inr f g : C ⟶ pushout f g) := by
  exact strict_inr_of_isPushout_of_strict (IsPushout.of_hasPushout f g) hf

end FilteredObject.Hom

-- Proof sketch: first realize the filtered pushout by endowing the ambient pushout of `f.hom` and
-- `g.hom` with the stagewise image filtration coming from `F^p B ⊕ F^p C`; this yields the
-- canonical `HasPushout f g` instance. The strictness statement is proved first for an arbitrary
-- pushout square via `strict_inr_of_isPushout_of_strict`, then specialized to `pushout.inr f g`.
/-- Lemma 12.19.10: for morphisms `f : A ⟶ B` and `g : A ⟶ C` of filtered objects in an abelian
category, there exists a pushout square in the filtered category, and if `f` is strict, then the
induced morphism `f' : C ⟶ C ⨿_A B` is strict. -/
theorem exists_filtered_pushout_preserving_strictness
    {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : A ⟶ C) :
    ∃ (P : FilteredObject 𝒜) (g' : B ⟶ P) (f' : C ⟶ P),
      IsPushout f g g' f' ∧ (Strict f → Strict f') := by
  refine ⟨pushout f g, pushout.inl f g, pushout.inr f g, IsPushout.of_hasPushout f g, ?_⟩
  exact strict_pushout_inr_of_strict f g

end CategoryTheory
