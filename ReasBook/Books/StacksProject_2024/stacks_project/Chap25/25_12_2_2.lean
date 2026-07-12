import StacksProject_2024.Chap25.Lemma_25_3_7
import StacksProject_2024.Chap25.«25_12_2_1»

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

namespace SemiRepresentableFamily
namespace Over

/-- Adjoin a single arrow `U' ⟶ X` to a fixed-target family over `X`. -/
abbrev addSingleton {X U' : C} (𝒰 : SR(C, X)) (f : U' ⟶ X) : SR(C, X) :=
  ofArrows
    (fun s : Sum 𝒰.index Unit ↦
      match s with
      | .inl i => (𝒰.obj i).left
      | .inr _ => U')
    (fun s : Sum 𝒰.index Unit ↦
      match s with
      | .inl i => (𝒰.obj i).hom
      | .inr _ => f)

omit [HasPullbacks C] in
/-- Unfolding `addSingleton` gives the disjoint union of the original family with the singleton
family `\{U' \to X\}`. -/
@[simp] theorem addSingleton_def {X U' : C} (𝒰 : SR(C, X)) (f : U' ⟶ X) :
    𝒰.addSingleton f =
      ofArrows
        (fun s : Sum 𝒰.index Unit ↦
          match s with
          | .inl i => (𝒰.obj i).left
          | .inr _ => U')
        (fun s : Sum 𝒰.index Unit ↦
          match s with
          | .inl i => (𝒰.obj i).hom
          | .inr _ => f) :=
  rfl

omit [HasPullbacks C] in
/-- The source objects of `addSingleton` lie in `B` exactly when the original family does and the
adjoined source object lies in `B`. -/
@[simp] theorem addSingleton_objectsIn_iff
    {X U' : C} (𝒰 : SR(C, X)) (f : U' ⟶ X) (B : Set C) :
    (𝒰.addSingleton f).objectsIn B ↔ 𝒰.objectsIn B ∧ U' ∈ B := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      exact h (.inl i)
    · exact h (.inr ())
  · rintro ⟨h𝒰, hU'⟩ s
    cases s with
    | inl i => exact h𝒰 i
    | inr _ => simpa using hU'

end Over
end SemiRepresentableFamily

namespace Hypercovering

open SemiRepresentableFamily.Over

variable {X : C}

/-- A hypercovering lies degreewise in `B` if every source object in every simplicial degree lies
in `B`. -/
def degreewiseObjectsIn (K : Hypercovering J X) (B : Set C) : Prop :=
  ∀ n : ℕ, (K.family n).objectsIn B

omit [HasPullbacks C] in
/-- Unfolding `degreewiseObjectsIn` says exactly that each simplicial degree family of `K` lies in
`B`. -/
@[simp] theorem degreewiseObjectsIn_iff (K : Hypercovering J X) (B : Set C) :
    K.degreewiseObjectsIn B ↔
      ∀ n : ℕ, (K.family n).objectsIn B :=
  Iff.rfl

end Hypercovering

end CategoryTheory
