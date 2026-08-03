module

public import Topology_Munkres_2000.Book.Theorem_62_1.CechCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ulift

public section

namespace InvarianceOfDomainSupport

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CechFiniteOpenCover

/-- Helper for Theorem 62.1: reduced finite-stage mod-two face-nerve cohomology,
using the augmentation kernel in degree zero. -/
noncomputable def reducedFaceNerveCohomology {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) (q : ℕ) : ModuleCat.{v} (ZMod 2) :=
  match q with
  | 0 => ModuleCat.of (ZMod 2) (reducedNerveCohomologyZero U)
  | q + 1 => ModuleCat.of (ZMod 2) (faceNerveCohomology U (q + 1))

/-- Helper for Theorem 62.1: a refinement choice induces the unified reduced
finite-stage cohomology map. -/
noncomputable def RefinementMap.reducedFaceNerveCohomologyMap
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} (f : RefinementMap U V) (q : ℕ) :
    reducedFaceNerveCohomology U q ⟶ reducedFaceNerveCohomology V q :=
  letI : DecidableEq U.Index := Classical.decEq U.Index
  match q with
  | 0 => ModuleCat.ofHom f.reducedNerveCohomologyZeroMap
  | q + 1 => ModuleCat.ofHom (f.faceNerveCohomologyMap (q + 1))

/-- Helper for Theorem 62.1: the unified finite-stage map is independent of
the refinement choice. -/
lemma RefinementMap.reducedFaceNerveCohomologyMap_eq
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} (f g : RefinementMap U V) (q : ℕ) :
    f.reducedFaceNerveCohomologyMap q = g.reducedFaceNerveCohomologyMap q := by
  -- Split off reduced degree zero; every positive degree uses ordinary dual cohomology.
  classical
  cases q with
  | zero =>
      exact congrArg ModuleCat.ofHom (f.reducedNerveCohomologyZeroMap_eq g)
  | succ q =>
      exact congrArg ModuleCat.ofHom (f.faceNerveCohomologyMap_eq g (q + 1))

/-- Helper for Theorem 62.1: identity refinement acts identically on unified
reduced finite-stage cohomology. -/
lemma RefinementMap.reducedFaceNerveCohomologyMap_id
    {X : Type u} [TopologicalSpace X] (U : CechFiniteOpenCover.{u, v} X) (q : ℕ) :
    (RefinementMap.id U).reducedFaceNerveCohomologyMap q =
      𝟙 (reducedFaceNerveCohomology U q) := by
  -- Apply the established identity law in the appropriate degree branch.
  classical
  cases q with
  | zero =>
      exact congrArg ModuleCat.ofHom
        (RefinementMap.reducedNerveCohomologyZeroMap_id U)
  | succ q =>
      exact congrArg ModuleCat.ofHom
        (RefinementMap.faceNerveCohomologyMap_id U (q + 1))

/-- Helper for Theorem 62.1: unified reduced finite-stage cohomology maps
respect composition of refinement choices. -/
lemma RefinementMap.reducedFaceNerveCohomologyMap_comp
    {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    (f : RefinementMap U V) (g : RefinementMap V W) (q : ℕ) :
    (f.comp g).reducedFaceNerveCohomologyMap q =
      f.reducedFaceNerveCohomologyMap q ≫
        g.reducedFaceNerveCohomologyMap q := by
  -- Both degree branches obey the same covariant composition formula on cohomology.
  classical
  cases q with
  | zero =>
      exact (congrArg ModuleCat.ofHom
        (RefinementMap.reducedNerveCohomologyZeroMap_comp f g)).trans
          (ModuleCat.ofHom_comp _ _)
  | succ q =>
      exact (congrArg ModuleCat.ofHom
        (RefinementMap.faceNerveCohomologyMap_comp f g (q + 1))).trans
          (ModuleCat.ofHom_comp _ _)

/-- Helper for Theorem 62.1: choose a refinement map witnessing a relation of
finite open covers. -/
noncomputable def refinementMapOfLE {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} (h : U ≤ V) : RefinementMap U V :=
  Classical.choice (refinementMap_nonempty h)

/-- Helper for Theorem 62.1: the cohomology map attached to a refinement
relation, independent of its hidden choice. -/
noncomputable def reducedFaceNerveCohomologyMapOfLE
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} (h : U ≤ V) (q : ℕ) :
    reducedFaceNerveCohomology U q ⟶ reducedFaceNerveCohomology V q :=
  (refinementMapOfLE h).reducedFaceNerveCohomologyMap q

/-- Helper for Theorem 62.1: every reflexive refinement relation induces the
identity map. -/
lemma reducedFaceNerveCohomologyMapOfLE_refl
    {X : Type u} [TopologicalSpace X] (U : CechFiniteOpenCover.{u, v} X)
    (h : U ≤ U) (q : ℕ) :
    reducedFaceNerveCohomologyMapOfLE h q =
      𝟙 (reducedFaceNerveCohomology U q) := by
  -- Replace the hidden choice by the canonical identity refinement.
  calc
    reducedFaceNerveCohomologyMapOfLE h q =
        (RefinementMap.id U).reducedFaceNerveCohomologyMap q :=
      (refinementMapOfLE h).reducedFaceNerveCohomologyMap_eq _ q
    _ = 𝟙 (reducedFaceNerveCohomology U q) :=
      RefinementMap.reducedFaceNerveCohomologyMap_id U q

/-- Helper for Theorem 62.1: maps chosen from composable refinement relations
compose independently of all three hidden choices. -/
lemma reducedFaceNerveCohomologyMapOfLE_trans
    {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    (hUV : U ≤ V) (hVW : V ≤ W) (hUW : U ≤ W) (q : ℕ) :
    reducedFaceNerveCohomologyMapOfLE hUW q =
      reducedFaceNerveCohomologyMapOfLE hUV q ≫
        reducedFaceNerveCohomologyMapOfLE hVW q := by
  -- Compare the direct hidden choice with the composite of the two chosen witnesses.
  calc
    reducedFaceNerveCohomologyMapOfLE hUW q =
        ((refinementMapOfLE hUV).comp
          (refinementMapOfLE hVW)).reducedFaceNerveCohomologyMap q :=
      (refinementMapOfLE hUW).reducedFaceNerveCohomologyMap_eq _ q
    _ = reducedFaceNerveCohomologyMapOfLE hUV q ≫
          reducedFaceNerveCohomologyMapOfLE hVW q :=
      RefinementMap.reducedFaceNerveCohomologyMap_comp _ _ q

/-- Helper for Theorem 62.1: the raw module morphism assigned to an identity
cover morphism is the categorical identity. -/
lemma reducedFaceNerveCohomologyRawMap_id
    {X : Type u} [TopologicalSpace X] (U : CechFiniteOpenCover.{u, v} X) (q : ℕ) :
    reducedFaceNerveCohomologyMapOfLE (leOfHom (𝟙 U)) q =
      𝟙 (reducedFaceNerveCohomology U q) := by
  -- Normalize the hidden refinement choice to the categorical identity.
  exact reducedFaceNerveCohomologyMapOfLE_refl U _ q

/-- Helper for Theorem 62.1: the raw module morphisms preserve categorical
composition of cover refinements. -/
lemma reducedFaceNerveCohomologyRawMap_comp
    {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    (f : U ⟶ V) (g : V ⟶ W) (q : ℕ) :
    reducedFaceNerveCohomologyMapOfLE (leOfHom (f ≫ g)) q =
      reducedFaceNerveCohomologyMapOfLE (leOfHom f) q ≫
        reducedFaceNerveCohomologyMapOfLE (leOfHom g) q := by
  -- Choice-independent transitivity supplies the functor composition law.
  exact reducedFaceNerveCohomologyMapOfLE_trans _ _ _ q

/-- Helper for Theorem 62.1: the raw reduced finite-stage cohomology diagram
before lifting its module universe. -/
noncomputable def reducedCechCohomologyRawDiagram
    {X : Type u} [TopologicalSpace X] (q : ℕ) :
    CechFiniteOpenCover.{u, v} X ⥤ ModuleCat.{v} (ZMod 2) :=
  { obj := fun U ↦ reducedFaceNerveCohomology U q
    map := fun f ↦ reducedFaceNerveCohomologyMapOfLE (leOfHom f) q
    map_id := fun U ↦ reducedFaceNerveCohomologyRawMap_id U q
    map_comp := fun f g ↦ reducedFaceNerveCohomologyRawMap_comp f g q }

/-- Helper for Theorem 62.1: the universe-safe filtered diagram of reduced
finite-stage mod-two face-nerve cohomology modules. -/
noncomputable def reducedCechCohomologyDiagram
    {X : Type u} [TopologicalSpace X] (q : ℕ) :
    CechFiniteOpenCover.{u, v} X ⥤ ModuleCat.{max u (v + 1)} (ZMod 2) :=
  reducedCechCohomologyRawDiagram q ⋙
    ModuleCat.uliftFunctor.{max u (v + 1), v} (ZMod 2)

end CechFiniteOpenCover

/-- Helper for Theorem 62.1: reduced mod-two Čech cohomology is the colimit
of the universe-lifted finite-cover nerve diagram. -/
noncomputable def reducedCechCohomologyModTwo
    {X : Type u} [TopologicalSpace X] (q : ℕ) :
    ModuleCat.{max u (v + 1)} (ZMod 2) :=
  colimit
    (CechFiniteOpenCover.reducedCechCohomologyDiagram.{u, v} (X := X) q)

/-- Helper for Theorem 62.1: the canonical map from a finite cover stage into
reduced mod-two Čech cohomology. -/
noncomputable def reducedCechCohomologyι
    {X : Type u} [TopologicalSpace X] (q : ℕ)
    (U : CechFiniteOpenCover.{u, v} X) :
    (CechFiniteOpenCover.reducedCechCohomologyDiagram.{u, v} q).obj U ⟶
      reducedCechCohomologyModTwo.{u, v} (X := X) q :=
  colimit.ι
    (CechFiniteOpenCover.reducedCechCohomologyDiagram.{u, v} (X := X) q) U

/-- Helper for Theorem 62.1: refinement followed by the target-stage inclusion
equals the source-stage inclusion into reduced Čech cohomology. -/
lemma reducedCechCohomologyι_naturality
    {X : Type u} [TopologicalSpace X] (q : ℕ)
    {U V : CechFiniteOpenCover.{u, v} X} (f : U ⟶ V) :
    (CechFiniteOpenCover.reducedCechCohomologyDiagram.{u, v} q).map f ≫
        reducedCechCohomologyι.{u, v} q V =
      reducedCechCohomologyι.{u, v} q U := by
  -- This is the defining cocone compatibility of the filtered colimit.
  exact colimit.w
    (CechFiniteOpenCover.reducedCechCohomologyDiagram.{u, v} q) f

end InvarianceOfDomainSupport

end
