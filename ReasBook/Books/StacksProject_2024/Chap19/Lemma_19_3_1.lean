import Mathlib
import StacksProject_2024.Chap12.Lemma_12_29_5

open CategoryTheory Limits

universe u v

noncomputable section

namespace CategoryTheory

/- Domain-style sampling for Lemma 19.3.1:
- primary domain: continuous actions of a topological group on discrete `R`-modules;
- sampled owner declarations:
  `DiscreteContAction`,
  `Action.IsContinuous`,
  `ContAction.IsDiscrete`,
  `ObjectProperty.ι`,
  `hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms`;
- best owner abstraction: mathlib's intrinsic owner
  `DiscreteContAction (ModuleCat R) G` after viewing every `R`-module with the discrete topology;
- primitive data: the discrete-topology forgetful functor `ModuleCat R ⥤ TopCat` and the
  continuous-action predicate on `Action (ModuleCat R) G`;
- derived API: the source-facing notation `Mod_{R,G}`, implemented by the thin bridge
  `RGModuleCat R G` to the canonical owner `DiscreteContAction (ModuleCat R) G`, together with
  functorial injective embeddings on that source-facing surface; the purely algebraic action
  category is only an internal bridge for the proof.

Source/core/bridge triage:
- `source-facing`: `Mod_{R,G}`, the category of discrete `R`-modules with continuous `G`-action;
- `core/canonical`: `DiscreteContAction` as mathlib's owner for continuous actions on discrete
  objects;
- `bridge/view`: the source-facing notation `Mod_{R,G}` carried by the thin bridge
  `RGModuleCat R G`, together with the purely algebraic action category `Action (ModuleCat R) G`;
  the latter is used below only as private implementation data rather than as a second public
  owner. -/

section SourceFacing

variable (R : Type u) [Ring R]

/-- View `ModuleCat R` in `TopCat` by equipping each module with the discrete topology. This is
implementation data for the source-facing category `Mod_{R,G}`. -/
private abbrev moduleCatDiscreteHasForget₂ :
    HasForget₂ (ModuleCat.{max u v} R) TopCat.{max u v} where
  forget₂ :=
    { obj := fun M ↦ by
        letI : TopologicalSpace M := ⊥
        letI : DiscreteTopology M := ⟨rfl⟩
        exact TopCat.of M
      map := fun {M N} f ↦ by
        letI : TopologicalSpace M := ⊥
        letI : TopologicalSpace N := ⊥
        letI : DiscreteTopology M := ⟨rfl⟩
        letI : DiscreteTopology N := ⟨rfl⟩
        exact TopCat.ofHom ⟨f.hom, continuous_of_discreteTopology⟩ }

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Bridge abbreviation underlying the source-facing notation `Mod_{R,G}` for discrete
`R`-modules with continuous `G`-action. This remains a thin bridge to the canonical mathlib owner
`DiscreteContAction`; the discrete topology on each module stays internal implementation data. -/
abbrev RGModuleCat
    (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  let _ : HasForget₂ (ModuleCat.{max u v} R) TopCat.{max u v} := moduleCatDiscreteHasForget₂ R
  DiscreteContAction (ModuleCat.{max u v} R) G

namespace RGModuleCat

scoped notation3:max "Mod_{" R "," G "}" => CategoryTheory.RGModuleCat R G

end RGModuleCat

open scoped RGModuleCat

/-- Lemma 19.3.1: for a topological group `G`, the category `Mod_{R,G}` of discrete `R`-modules
with continuous `G`-action, exposed publicly through the notation `Mod_{R,G}` and implemented
canonically via `DiscreteContAction`, has functorial injective embeddings. -/
instance :
    HasFunctorialInjectiveEmbeddings (Mod_{R,G}) := by
  let _ : HasForget₂ (ModuleCat.{max u v} R) TopCat.{max u v} := moduleCatDiscreteHasForget₂ R
  change HasFunctorialInjectiveEmbeddings
    (DiscreteContAction (ModuleCat.{max u v} R) G)
  sorry

end SourceFacing

section AlgebraicSpecialization

variable (R : Type u) (G : Type v) [Ring R] [Monoid G]

/-- The cofree algebraic `R`-linear `G`-action on a module `M`, given by right translation on
`G → M`. -/
private abbrev actionModuleCatCofreeObj (M : ModuleCat.{max u v} R) :
    Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (G → M)
  ρ :=
    { toFun := fun g ↦
        ModuleCat.ofHom
          { toFun := fun f h ↦ f (h * g)
            map_add' := fun _ _ ↦ by
              ext h
              rfl
            map_smul' := fun _ _ ↦ by
              ext h
              rfl }
      map_one' := by
        apply ModuleCat.hom_ext
        ext f h
        simp
      map_mul' := fun g h ↦ by
        apply ModuleCat.hom_ext
        ext f x
        simp [mul_assoc] }

/-- Postcomposition by a module morphism defines the map part of the cofree algebraic action
functor. -/
private abbrev actionModuleCatCofreeMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    actionModuleCatCofreeObj R G M ⟶ actionModuleCatCofreeObj R G N where
  hom := ModuleCat.ofHom
    { toFun := fun x g ↦ f.hom (x g)
      map_add' := fun _ _ ↦ by
        ext g
        simp
      map_smul' := fun _ _ ↦ by
        ext g
        simp }
  comm g := by
    ext x h
    rfl

/-- The cofree algebraic action functor right adjoint to forgetting the `G`-action. -/
private abbrev actionModuleCatCofree : ModuleCat.{max u v} R ⥤ Action (ModuleCat.{max u v} R) G
    where
  obj := actionModuleCatCofreeObj R G
  map := actionModuleCatCofreeMap R G
  map_id M := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x g
    simp
  map_comp f g := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x h
    simp

/-- The hom-set bijection for the forgetful/cofree adjunction on algebraic `R`-linear
`G`-actions. -/
private abbrev actionModuleCatForgetCofreeHomEquiv
    (X : Action (ModuleCat.{max u v} R) G) (M : ModuleCat.{max u v} R) :
    ((Action.forget (ModuleCat.{max u v} R) G).obj X ⟶ M) ≃
      (X ⟶ (actionModuleCatCofree R G).obj M) where
  toFun φ :=
    { hom := ModuleCat.ofHom
        { toFun := fun x g ↦ φ.hom ((X.ρ g).hom x)
          map_add' := fun _ _ ↦ by
            ext g
            simp
          map_smul' := fun _ _ ↦ by
            ext g
            simp }
      comm := fun g ↦ by
        ext x h
        simp [actionModuleCatCofreeObj] }
  invFun ψ := ModuleCat.ofHom
    { toFun := fun x ↦ ψ.hom.hom x 1
      map_add' := fun _ _ ↦ by simp
      map_smul' := fun _ _ ↦ by simp }
  left_inv φ := by
    ext x
    change φ.hom ((X.ρ 1).hom x) = φ.hom x
    simp [Action.ρ_one]
  right_inv ψ := by
    ext x g
    have hcomm := congrArg (fun k ↦ k x 1) (ModuleCat.hom_ext_iff.mp (ψ.comm g))
    simpa using hcomm

/-- The forgetful functor from algebraic `R`-linear `G`-actions to `R`-modules is left adjoint to
the cofree algebraic action functor. -/
private noncomputable def actionModuleCatForgetCofreeAdjunction :
    Action.forget (ModuleCat.{max u v} R) G ⊣ actionModuleCatCofree R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := actionModuleCatForgetCofreeHomEquiv R G
      homEquiv_naturality_left_symm := by
        intro X Y M f φ
        ext x
        rfl
      homEquiv_naturality_right := by
        intro X M N f φ
        ext x
        rfl }

/-- Algebraic bridge: forgetting continuity and discreteness leaves the underlying
`R`-linear `G`-action category, which still has functorial injective embeddings. This stays
private because `Action (ModuleCat R) G` is only implementation data for the source-facing owner
`DiscreteContAction (ModuleCat R) G`. -/
private instance actionModuleCat_hasFunctorialInjectiveEmbeddings :
    HasFunctorialInjectiveEmbeddings (Action (ModuleCat.{max u v} R) G) := by
  letI : EnoughInjectives (ModuleCat.{max u v} R) := ModuleCat.enoughInjectives R
  letI : HasFunctorialInjectiveEmbeddings (ModuleCat.{max u v} R) :=
    hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian
  let hzero : ∀ X : Action (ModuleCat.{max u v} R) G,
      IsZero ((Action.forget (ModuleCat.{max u v} R) G).obj X) → IsZero X := by
    intro X hX
    refine ⟨fun Y ↦ ?_, fun Y ↦ ?_⟩
    · refine ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩
      exact Action.hom_ext _ _ (hX.eq_of_src f.hom 0)
    · refine ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩
      exact Action.hom_ext _ _ (hX.eq_of_tgt f.hom 0)
  exact hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms
    (actionModuleCatCofree R G) (Action.forget (ModuleCat.{max u v} R) G)
    (actionModuleCatForgetCofreeAdjunction R G) hzero

end AlgebraicSpecialization

end CategoryTheory
