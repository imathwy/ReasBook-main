import stacks_project.Chap12.Lemma_12_19_2
import stacks_project.Chap12.Lemma_12_19_4

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

open FilteredObject.Hom

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.11:
- source-facing: existence of a filtered pullback square with strict projection to `C`
- core/canonical owner: `IsPullback g' f' f g`, together with the chosen `HasPullback f g`
- primitive data: the canonical comparison morphism `B ⊞ C ⟶ A`
  induced by `(f, -g)`
- bridge/view: the kernel model of that comparison morphism inside `B ⊞ C`,
  together with the derived projections to `B` and `C`
-/

private abbrev pullbackDifference (f : B ⟶ A) (g : C ⟶ A) :
    (B ⊞ C : FilteredObject 𝒜) ⟶ A :=
  biprod.desc f (show C ⟶ A from -g)

private abbrev kernelPullback (f : B ⟶ A) (g : C ⟶ A) : FilteredObject 𝒜 :=
  ((B ⊞ C : FilteredObject 𝒜)).subobjectFilteredObject
    (kernelSubobject (pullbackDifference f g).hom)

private abbrev kernelPullbackι (f : B ⟶ A) (g : C ⟶ A) :
    kernelPullback f g ⟶ (B ⊞ C : FilteredObject 𝒜) :=
  ((B ⊞ C : FilteredObject 𝒜)).subobjectInclusion
    (kernelSubobject (pullbackDifference f g).hom)

private abbrev kernelPullbackFst (f : B ⟶ A) (g : C ⟶ A) : kernelPullback f g ⟶ B :=
  kernelPullbackι f g ≫ biprod.fst

private abbrev kernelPullbackSnd (f : B ⟶ A) (g : C ⟶ A) : kernelPullback f g ⟶ C :=
  kernelPullbackι f g ≫ biprod.snd

private theorem kernelPullback_isPullback (f : B ⟶ A) (g : C ⟶ A) :
    IsPullback (kernelPullbackFst f g) (kernelPullbackSnd f g) f g := by
  sorry

noncomputable instance hasPullback (f : B ⟶ A) (g : C ⟶ A) : HasPullback f g :=
  (kernelPullback_isPullback f g).hasPullback

/-- In a pullback square of filtered objects, strictness of the left map forces strictness of the
right map. -/
theorem strict_snd_of_isPullback_of_strict
    (f : B ⟶ A) (g : C ⟶ A) {P : FilteredObject 𝒜} {g' : P ⟶ B} {f' : P ⟶ C}
    (sq : IsPullback g' f' f g) (hf : Strict f) :
    Strict f' := by
  sorry

/-- In the canonical pullback square of filtered objects, strictness of the left map forces
strictness of the induced projection to the right factor. -/
theorem strict_pullback_snd_of_strict (f : B ⟶ A) (g : C ⟶ A) (hf : Strict f) :
    Strict (pullback.snd f g : pullback f g ⟶ C) := by
  exact strict_snd_of_isPullback_of_strict f g (IsPullback.of_hasPullback f g) hf

end FilteredObject.Hom

-- Proof sketch: realize the pullback in `FilteredObject` via the owner-level `HasPullback f g`
-- instance coming from the kernel presentation inside `B ⊞ C`; then package
-- the canonical pullback object and projections. The strictness clause is the square-level theorem
-- `strict_snd_of_isPullback_of_strict` applied to the canonical pullback square.
/-- Lemma 12.19.11: for morphisms `f : B ⟶ A` and `g : C ⟶ A` of filtered objects in an abelian
category, there exists a fibre product square in the filtered category, and if `f` is strict, then
the induced morphism `f' : B ×[A] C ⟶ C` is strict. -/
theorem exists_filtered_pullback_preserving_strictness
    {A B C : FilteredObject 𝒜} (f : B ⟶ A) (g : C ⟶ A) :
    ∃ (P : FilteredObject 𝒜) (g' : P ⟶ B) (f' : P ⟶ C),
      IsPullback g' f' f g ∧ (Strict f → Strict f') := by
  refine ⟨pullback f g, pullback.fst f g, pullback.snd f g, IsPullback.of_hasPullback f g, ?_⟩
  exact strict_pullback_snd_of_strict f g

end CategoryTheory
