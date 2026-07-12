import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced the canonical module-sheaf functors
`Scheme.Modules.pushforward`, `Scheme.Modules.pullback`, and
`Scheme.Modules.instIsRightAdjointPushforward`.  Nearby Chapter 29 files use
`ℱ.IsQuasicoherent` as the quasi-coherent owner, so the source functor on
`QCoh(\mathcal O_X)` is recorded as the full subcategory of `X.Modules` cut out by that
predicate. -/

/-- The object property of quasi-coherent modules on a scheme. -/
abbrev quasiCoherentObjectProperty (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun ℱ : X.Modules ↦ ℱ.IsQuasicoherent

/-- The full subcategory of quasi-coherent modules on a scheme. -/
abbrev QuasiCoherent (X : Scheme.{u}) : Type (u + 1) :=
  (quasiCoherentObjectProperty X).FullSubcategory

/-- The pushforward functor restricted to quasi-coherent modules, given a proof that pushforward
preserves quasi-coherence for the morphism in question. -/
abbrev quasiCoherentPushforwardOf {X Z : Scheme.{u}} (i : Z ⟶ X)
    (hpush : ∀ ℱ : Z.Modules, ℱ.IsQuasicoherent → ((pushforward i).obj ℱ).IsQuasicoherent) :
    QuasiCoherent Z ⥤ QuasiCoherent X :=
  ObjectProperty.lift (quasiCoherentObjectProperty X)
    ((quasiCoherentObjectProperty Z).ι ⋙ pushforward i)
    (fun ℱ ↦ hpush ℱ.obj ℱ.property)

/-- The chosen right adjoint to a restricted quasi-coherent pushforward once its left-adjoint
structure is available; this is the functor denoted `i^!` in the closed-immersion case. -/
noncomputable abbrev quasiCoherentShriekOfLeftAdjoint {X Z : Scheme.{u}} (i : Z ⟶ X)
    (hpush : ∀ ℱ : Z.Modules, ℱ.IsQuasicoherent → ((pushforward i).obj ℱ).IsQuasicoherent)
    [(quasiCoherentPushforwardOf i hpush).IsLeftAdjoint] :
    QuasiCoherent X ⥤ QuasiCoherent Z :=
  (quasiCoherentPushforwardOf i hpush).rightAdjoint

/-- The adjunction associated to the chosen right adjoint of a restricted quasi-coherent
pushforward. -/
noncomputable abbrev quasiCoherentPushforwardShriekAdjunctionOf {X Z : Scheme.{u}}
    (i : Z ⟶ X)
    (hpush : ∀ ℱ : Z.Modules, ℱ.IsQuasicoherent → ((pushforward i).obj ℱ).IsQuasicoherent)
    [(quasiCoherentPushforwardOf i hpush).IsLeftAdjoint] :
    quasiCoherentPushforwardOf i hpush ⊣ quasiCoherentShriekOfLeftAdjoint i hpush :=
  Adjunction.ofIsLeftAdjoint (quasiCoherentPushforwardOf i hpush)

/-- Pushforward along a closed immersion preserves quasi-coherence, allowing `i_*` to be viewed
as a functor on quasi-coherent modules. -/
theorem quasiCoherentPushforward_preserves_of_isClosedImmersion {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (ℱ : Z.Modules) (hℱ : ℱ.IsQuasicoherent) :
    ((pushforward i).obj ℱ).IsQuasicoherent := sorry

/-- Lemma 29.4.3: for a closed immersion `i : Z \to X` of schemes, the pushforward functor
`i_* : QCoh(\mathcal O_Z) \to QCoh(\mathcal O_X)` admits a right adjoint, denoted `i^!`. -/
@[stacks 01R0, instance]
theorem quasiCoherentPushforward_isLeftAdjoint_of_isClosedImmersion {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (quasiCoherentPushforwardOf i
      (quasiCoherentPushforward_preserves_of_isClosedImmersion i)).IsLeftAdjoint := sorry

end AlgebraicGeometry.Scheme.Modules
