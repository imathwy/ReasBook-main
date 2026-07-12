import StacksProject_2024.Chap04.Definition_4_33_1
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomOldObjectComposition

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace LocallyDefinedHomTotal

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.6/2.7: the single cartesian calculation
needed to show that the locally-defined-Hom projection is fibred and that the old-object
comparison preserves strongly cartesian arrows.

This is kept as an explicit frontier because its proof is the source text's local factorization
argument: a locally defined morphism into the target of a cartesian arrow is represented on a
cover, factored locally through the cartesian arrow, and then reassembled as a locally defined
morphism. -/
structure SourceCartesianFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Ordinary strongly cartesian arrows remain strongly cartesian after being represented as
  locally-defined morphisms on the trivial cover. -/
  ordinaryStronglyCartesian :
    ∀ ⦃x y : X.S⦄ (φ : x ⟶ y),
      X.p.IsStronglyCartesian (X.p.map φ) φ →
        letI := sourceCategory (J := J) X
        (sourceProjection (J := J) X).IsStronglyCartesian
          (X.p.map φ) (ordinaryHomToLocallyDefinedHom (J := J) X φ)

namespace SourceCartesianFrontier

/-- Source stage 2.6: once the local factorization calculation is supplied, the old-object
comparison preserves strongly cartesian arrows. -/
theorem oldObjectToSourceBasedFunctor_preservesStronglyCartesian
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceCartesianFrontier (J := J) X) :
    (oldObjectToSourceBasedFunctor (J := J) X).PreservesStronglyCartesian := by
  intro x y φ hφ
  letI := sourceCategory (J := J) X
  simpa [oldObjectToSourceBasedFunctor, oldObjectToSourceBasedFunctorOfFrontier,
    oldObjectToSourceFunctor, oldObjectToSourceFunctorOfFrontier, sourceBasedCategory] using
    H.ordinaryStronglyCartesian φ hφ

/-- Source stage 2.7: the locally-defined-Hom projection is fibred once the old-object
representatives of cartesian lifts are known to be strongly cartesian in the source projection. -/
noncomputable def sourceProjectionFiberedFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceCartesianFrontier (J := J) X) :
    SourceProjectionFiberedFrontier (J := J) X where
  isFibered := by
    letI := sourceCategory (J := J) X
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro y R f
    cases y with
    | mk y =>
        let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
        let xφ : X.S := (f ^*[canonicalPullbackChoice X.p] yF).1
        let φ : xφ ⟶ y :=
          (canonicalPullbackChoice X.p).map f yF
        let φLD : ofObj (J := J) X xφ ⟶ ofObj (J := J) X y :=
          ordinaryHomToLocallyDefinedHom (J := J) X (x := xφ) (y := y) φ
        have hφ : X.p.IsStronglyCartesian f φ :=
          (canonicalPullbackChoice X.p).isStronglyCartesian f yF
        have hφMap : X.p.IsStronglyCartesian (X.p.map φ) φ :=
          isStronglyCartesian_rebase_of_isHomLift X.p hφ (IsHomLift.map X.p φ)
        have hsourceMap :=
          H.ordinaryStronglyCartesian (x := xφ) (y := y) φ hφMap
        have hsourceLift :
            (sourceProjection (J := J) X).IsHomLift f φLD := by
          refine IsHomLift.of_fac' (sourceProjection (J := J) X) f φLD
            (IsHomLift.domain_eq X.p f φ) rfl ?_
          simpa [φLD, sourceProjection] using IsHomLift.fac' X.p f φ
        refine ⟨ofObj (J := J) X xφ, φLD, ?_⟩
        exact
          isStronglyCartesian_rebase_of_isHomLift
            (sourceProjection (J := J) X) hsourceMap hsourceLift

end SourceCartesianFrontier

/-- Source stage 2.6 at the raw-representative level.

This is the exact point where the eventual proof should use the chosen representative of a
locally-defined morphism, factor its local arrows through `φ`, and check the overlap condition.
The statement is fixed-base, so equality of locally-defined morphisms is the concrete
common-refinement equivalence of representatives. -/
structure RawSourceCartesianFactorizationFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Raw fixed-base existence and uniqueness of the factorization through an ordinary cartesian
  arrow, with uniqueness stated in the common-refinement equivalence relation on representatives.
  Literal equality is only available after passing to the plus quotient. -/
  factorization :
    ∀ ⦃x y z : X.S⦄ (φ : x ⟶ y),
      X.p.IsStronglyCartesian (X.p.map φ) φ →
      ∀ (g : X.p.obj z ⟶ X.p.obj x)
        (α : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map φ)),
        ∃ β : LocallyDefinedHomRepresentativeOver (J := J) X g,
          LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
            (LocallyDefinedHomRepresentativeOver.composeOver (J := J) β
              (ordinaryHomToRepresentativeOver (J := J) X φ))
            α ∧
          ∀ β' : LocallyDefinedHomRepresentativeOver (J := J) X g,
            LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
              (LocallyDefinedHomRepresentativeOver.composeOver (J := J) β'
                (ordinaryHomToRepresentativeOver (J := J) X φ))
              α →
            LocallyDefinedHomRepresentativeOver.Equivalent (J := J) β' β

/-- Source stage 2.6 in the literal source notation, before Lean's heterogeneous Hom-lift
owner transports are introduced.

Here `α.1 = g ≫ p φ` and `β.1 = g` are definitional-base equalities in the concrete
locally-defined Hom type.  This is the surface on which the eventual local representative proof
should be carried out. -/
structure StrictSourceCartesianFactorizationFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Literal-base local existence and uniqueness of the factorization through an ordinary
  cartesian arrow. -/
  factorization :
    ∀ ⦃x y z : X.S⦄ (φ : x ⟶ y),
      X.p.IsStronglyCartesian (X.p.map φ) φ →
      ∀ (g : X.p.obj z ⟶ X.p.obj x)
        (α : locallyDefinedHom (J := J) X z y),
        α.1 = g ≫ X.p.map φ →
          ∃! β : locallyDefinedHom (J := J) X z x,
            β.1 = g ∧
              LocallyDefinedHom.comp (J := J) β
                (ordinaryHomToLocallyDefinedHom (J := J) X φ) = α

namespace RawSourceCartesianFactorizationFrontier

/-- Recasting a representative along a displayed base equality does not change the plus-packaged
locally-defined morphism it presents. -/
theorem castRepresentative_toLocallyDefinedHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y : X.S} (ρ : LocallyDefinedHomRepresentative (J := J) X x y)
    {α : locallyDefinedHom (J := J) X x y} (hρ : ρ.toLocallyDefinedHom = α)
    {f : X.p.obj x ⟶ X.p.obj y} (hbase : ρ.base = f) :
    (LocallyDefinedHomRepresentative.toLocallyDefinedHom (J := J)
      ({ base := f
         representative :=
          LocallyDefinedHomRepresentativeOver.castBase (J := J) hbase
            ρ.representative } :
        LocallyDefinedHomRepresentative (J := J) X x y)) = α := by
  cases hbase
  exact hρ

/-- A raw-representative factorization frontier gives the literal source-form plus-level
factorization frontier.  This bridges from common-refinement equivalence of representatives to
equality in the plus-packaged locally-defined Hom type. -/
theorem toStrictSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : RawSourceCartesianFactorizationFrontier (J := J) X) :
    StrictSourceCartesianFactorizationFrontier (J := J) X where
  factorization := by
    intro x y z φ hφ g α hbase
    let αrep := LocallyDefinedHom.chooseRepresentative (J := J) α
    have hαrep : αrep.toLocallyDefinedHom = α :=
      LocallyDefinedHom.chooseRepresentative_spec (J := J) α
    have hαrepBase : αrep.base = g ≫ X.p.map φ := by
      exact (LocallyDefinedHom.chooseRepresentative_base (J := J) α).trans hbase
    let αcast : LocallyDefinedHomRepresentative (J := J) X z y :=
      { base := g ≫ X.p.map φ
        representative :=
          LocallyDefinedHomRepresentativeOver.castBase (J := J) hαrepBase αrep.representative }
    have hαcast : αcast.toLocallyDefinedHom = α := by
      exact castRepresentative_toLocallyDefinedHom (J := J) αrep hαrep hαrepBase
    obtain ⟨βrep, hβrep, hβuniq⟩ :=
      H.factorization φ hφ g αcast.representative
    let βraw : LocallyDefinedHomRepresentative (J := J) X z x :=
      { base := g, representative := βrep }
    refine ⟨βraw.toLocallyDefinedHom, ?_, ?_⟩
    · refine ⟨rfl, ?_⟩
      calc
        LocallyDefinedHom.comp (J := J) βraw.toLocallyDefinedHom
            (ordinaryHomToLocallyDefinedHom (J := J) X φ)
            =
          (LocallyDefinedHomRepresentative.compose (J := J) βraw
            (ordinaryHomToRepresentative (J := J) X φ)).toLocallyDefinedHom := by
            exact LocallyDefinedHom.comp_toLocallyDefinedHom (J := J) βraw
              (ordinaryHomToRepresentative (J := J) X φ)
        _ = αcast.toLocallyDefinedHom := by
          apply (LocallyDefinedHomRepresentative.sameBase_toLocallyDefinedHom_eq_iff
            (J := J)
            (LocallyDefinedHomRepresentativeOver.composeOver (J := J) βrep
              (ordinaryHomToRepresentativeOver (J := J) X φ))
            αcast.representative).2
          exact hβrep
        _ = α := hαcast
    · intro β hβ
      obtain ⟨βrep', hβrep'⟩ :=
        LocallyDefinedHomRepresentative.toLocallyDefinedHom_surjective
          (J := J) (X := X) (x := z) (y := x) β
      have hβrep'Base : βrep'.base = g := by
        exact (congrArg Sigma.fst hβrep').trans hβ.1
      let βraw' : LocallyDefinedHomRepresentative (J := J) X z x :=
        { base := g
          representative :=
            LocallyDefinedHomRepresentativeOver.castBase (J := J) hβrep'Base
              βrep'.representative }
      have hβraw' : βraw'.toLocallyDefinedHom = β := by
        exact castRepresentative_toLocallyDefinedHom
          (J := J) βrep' hβrep' hβrep'Base
      have hcompRaw' :
          LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
            (LocallyDefinedHomRepresentativeOver.composeOver (J := J)
              βraw'.representative
              (ordinaryHomToRepresentativeOver (J := J) X φ))
            αcast.representative := by
        apply (LocallyDefinedHomRepresentative.sameBase_toLocallyDefinedHom_eq_iff
          (J := J)
          (LocallyDefinedHomRepresentativeOver.composeOver (J := J)
            βraw'.representative
            (ordinaryHomToRepresentativeOver (J := J) X φ))
          αcast.representative).1
        calc
          (LocallyDefinedHomRepresentative.toLocallyDefinedHom (J := J)
            ({ base := g ≫ X.p.map φ
               representative :=
                LocallyDefinedHomRepresentativeOver.composeOver (J := J)
                  βraw'.representative
                  (ordinaryHomToRepresentativeOver (J := J) X φ) } :
              LocallyDefinedHomRepresentative (J := J) X z y))
              =
            LocallyDefinedHom.comp (J := J) β
              (ordinaryHomToLocallyDefinedHom (J := J) X φ) := by
              rw [← hβraw']
              exact (LocallyDefinedHom.comp_toLocallyDefinedHom (J := J) βraw'
                (ordinaryHomToRepresentative (J := J) X φ)).symm
          _ = α := hβ.2
          _ = αcast.toLocallyDefinedHom := hαcast.symm
      have hβeq : LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
          βraw'.representative βrep := by
        exact hβuniq βraw'.representative hcompRaw'
      calc
        β = βraw'.toLocallyDefinedHom := hβraw'.symm
        _ = βraw.toLocallyDefinedHom := by
          apply (LocallyDefinedHomRepresentative.sameBase_toLocallyDefinedHom_eq_iff
            (J := J) βraw'.representative βrep).2
          exact hβeq

end RawSourceCartesianFactorizationFrontier

/-- Source stage 2.6, factored at the exact point where the Stacks proof uses local
factorization through a cartesian arrow.

For a strongly cartesian ordinary arrow `φ : x ⟶ y`, any locally-defined morphism
`α : z ⟶ y` whose displayed base factors as `g ≫ p φ` has a unique locally-defined factor
`β : z ⟶ x` over `g`.  The intended proof is the source argument: choose a representative of
`α`, factor each local representative through `φ`, check compatibility on overlaps by the
cartesian uniqueness of `φ`, and pass to the plus quotient. -/
structure SourceCartesianFactorizationFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Local existence and uniqueness of the factorization through an ordinary cartesian arrow,
  stated on the owner-level Hom-lift surface.  The `IsHomLift` hypotheses are the Lean form of
  the source equalities `p(α) = g ≫ p(φ)` and `p(β) = g`, with the unavoidable domain/codomain
  transports left explicit. -/
  factorization :
    letI := sourceCategory (J := J) X
    ∀ ⦃x y z : X.S⦄ (φ : x ⟶ y),
      X.p.IsStronglyCartesian (X.p.map φ) φ →
      ∀ {R : C} (g : R ⟶ X.p.obj x)
        (α : ofObj (J := J) X z ⟶ ofObj (J := J) X y),
        (sourceProjection (J := J) X).IsHomLift (g ≫ X.p.map φ) α →
          ∃! β : ofObj (J := J) X z ⟶ ofObj (J := J) X x,
            (sourceProjection (J := J) X).IsHomLift g β ∧
              β ≫ ordinaryHomToLocallyDefinedHom (J := J) X φ = α

namespace SourceCartesianFactorizationFrontier

/-- The local factorization statement from source stage 2.6 is exactly the universal property
needed to make the trivial-cover representative of an ordinary cartesian arrow strongly
cartesian in the locally-defined-Hom source projection. -/
theorem ordinaryStronglyCartesian
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceCartesianFactorizationFrontier (J := J) X)
    ⦃x y : X.S⦄ (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    letI := sourceCategory (J := J) X
    (sourceProjection (J := J) X).IsStronglyCartesian
      (X.p.map φ) (ordinaryHomToLocallyDefinedHom (J := J) X φ) := by
  letI := sourceCategory (J := J) X
  apply (Functor.isStronglyCartesian_iff_universal_property
    (sourceProjection (J := J) X)
    (X.p.map φ) (ordinaryHomToLocallyDefinedHom (J := J) X φ)).2
  constructor
  · refine IsHomLift.of_fac (sourceProjection (J := J) X)
      (X.p.map φ) (ordinaryHomToLocallyDefinedHom (J := J) X φ) rfl rfl ?_
    simpa [sourceProjection, projectionMap] using
      (ordinaryHomToLocallyDefinedHom_base (J := J) X φ).symm
  · intro R' z g α hα
    exact H.factorization φ hφ g α hα

/-- Package source stage 2.6 as the cartesian frontier used by the later source projection and
old-object comparison helpers. -/
theorem toSourceCartesianFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceCartesianFactorizationFrontier (J := J) X) :
    SourceCartesianFrontier (J := J) X where
  ordinaryStronglyCartesian := by
    intro x y φ hφ
    exact H.ordinaryStronglyCartesian φ hφ

end SourceCartesianFactorizationFrontier

namespace StrictSourceCartesianFactorizationFrontier

/-- The literal source-form factorization frontier implies the owner-level Hom-lift frontier.
This isolates all domain transport introduced by `Functor.IsHomLift`, so the actual source proof
of stage 2.6 can stay on the concrete locally-defined-Hom surface. -/
theorem toSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : StrictSourceCartesianFactorizationFrontier (J := J) X) :
    SourceCartesianFactorizationFrontier (J := J) X where
  factorization := by
    letI := sourceCategory (J := J) X
    intro x y z φ hφ R g α hα
    let hz : X.p.obj z = R :=
      IsHomLift.domain_eq (sourceProjection (J := J) X) (g ≫ X.p.map φ) α
    let g' : X.p.obj z ⟶ X.p.obj x := eqToHom hz ≫ g
    have hbase : α.1 = g' ≫ X.p.map φ := by
      have hfac :=
        IsHomLift.fac' (sourceProjection (J := J) X) (g ≫ X.p.map φ) α
      dsimp [g'] at hfac ⊢
      simpa [sourceProjection, projectionMap, Category.assoc] using hfac
    obtain ⟨β, hβ, huniq⟩ := H.factorization φ hφ g' α hbase
    refine ⟨β, ?_, ?_⟩
    · refine ⟨?_, hβ.2⟩
      refine IsHomLift.of_fac (sourceProjection (J := J) X) g β hz rfl ?_
      dsimp [g'] at hβ ⊢
      simpa [sourceProjection, projectionMap, hβ.1, Category.assoc]
    · intro β' hβ'
      apply huniq β'
      refine ⟨?_, hβ'.2⟩
      letI : (sourceProjection (J := J) X).IsHomLift g β' := hβ'.1
      have hfac :=
        IsHomLift.fac' (sourceProjection (J := J) X) g β'
      dsimp [g'] at hfac ⊢
      simpa [sourceProjection, projectionMap, Category.assoc] using hfac

/-- Package the literal source-form frontier directly as the cartesian frontier used by stage
2.7. -/
theorem toSourceCartesianFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : StrictSourceCartesianFactorizationFrontier (J := J) X) :
    SourceCartesianFrontier (J := J) X :=
  H.toSourceCartesianFactorizationFrontier.toSourceCartesianFrontier

end StrictSourceCartesianFactorizationFrontier

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
