import Mathlib
import StacksProject_2024.Chap21.Definition_21_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u

namespace TopCat.SheafOfGroups

/- Domain-style sampling for Definition 20.4.1:
- primary domain: sheaves of groups and torsors on a topological space;
- sampled owner declarations:
  `CategoryTheory.Sheaf.PseudoTorsor`,
  `CategoryTheory.Sheaf.Torsor`,
  `CategoryTheory.Sheaf.Torsor.IsTrivial`,
  `CategoryTheory.Sheaf.Torsor.trivial`;
- best owner abstraction: keep the source-facing topological-space owner
  `TopCat.SheafOfGroups.Torsor`, but reuse the canonical opens-site owner
  `CategoryTheory.Sheaf.PseudoTorsor G` for the action data, the owner
  `CategoryTheory.Sheaf.Torsor G` for the covering-sieve bridge and site-level triviality;
- primitive data: the canonical opens-site pseudo-torsor data together with the source-facing
  topological local-nonemptiness condition;
- derived API: the opens-site bridge `toSiteTorsor`, the site-level pseudo-torsor morphism API,
  the source-facing triviality predicate `IsTrivial`, and the tautological torsor `Torsor.trivial`.

Primitive-vs-derived split:
- primitive data are the parent `CategoryTheory.Sheaf.PseudoTorsor G` together with
  `locally_nonempty`;
- the later site-level torsor owner already packages the covering-sieve local-nonemptiness on the
  opens site, so the Chapter 20 file should derive that bridge instead of duplicating the whole
  pseudo-torsor payload locally;
- triviality should be read through the existing `CategoryTheory.Sheaf.Torsor.IsTrivial` owner
  rather than a second local trivialization structure;
- the Chapter 20 local-nonemptiness formulation remains source-facing data because it is stated at
  the topological-space level rather than by covering sieves.

Source/core/bridge triage:
- `source-facing`: `TopCat.SheafOfGroups.Torsor`;
- `core/canonical`: `CategoryTheory.Sheaf.Torsor G` together with
  `CategoryTheory.Sheaf.Torsor.IsTrivial`;
- `bridge/view`: `toSiteTorsor` and `ofSiteTorsor`.
-/

variable {X : TopCat.{u}}

/-- Definition 20.4.1: a `\mathcal G`-torsor on `X` is a sheaf of types with a sectionwise left
action of `\mathcal G` that is natural under restriction, locally nonempty, and simply transitive
on sections over each open set. The action data are the canonical opens-site pseudo-torsor owner;
the Chapter 20 source-facing content is the topological local-nonemptiness condition. -/
structure Torsor (G : X.Sheaf GrpCat.{u}) extends CategoryTheory.Sheaf.PseudoTorsor G where
  /-- Every point admits a neighborhood with a local section. -/
  locally_nonempty (x : X) : ∃ U : Opens X, x ∈ U ∧ Nonempty (carrier.obj.obj (op U))

namespace Torsor

variable {G : X.Sheaf GrpCat.{u}}

/-- A torsor can be used as its underlying sheaf of types. -/
instance : CoeOut (Torsor G) (X.Sheaf (Type u)) where
  coe P := P.carrier

/-- Sections of the underlying sheaf of a torsor over an open subset of `X`. -/
abbrev Sections (P : Torsor G) (U : Opens X) : Type u :=
  P.carrier.obj.obj (op U)

/-- The Chapter 20 torsor viewed as a torsor on the opens site of `X`. -/
def toSiteTorsor (P : Torsor G) :
    CategoryTheory.Sheaf.Torsor G where
  toPseudoTorsor := P.toPseudoTorsor
  locallyNonempty U := by
    let S : Sieve U := {
      arrows := fun {_} i ↦ Nonempty (P.Sections _)
      downward_closed := fun h g ↦ by
        rcases h with ⟨s⟩
        exact ⟨P.carrier.obj.map g.op s⟩
    }
    refine ⟨S, ?_, ?_⟩
    · intro x hx
      rcases P.locally_nonempty x with ⟨V, hxV, ⟨s⟩⟩
      refine ⟨V ⊓ U, homOfLE inf_le_right, ?_, ?_⟩
      · exact ⟨P.carrier.obj.map (homOfLE inf_le_left).op s⟩
      · exact ⟨hxV, hx⟩
    · intro V i hi
      exact hi

/-- A torsor on the opens site of `X` yields the Chapter 20 source-facing torsor. -/
def ofSiteTorsor (P : CategoryTheory.Sheaf.Torsor G) :
    Torsor G where
  toPseudoTorsor := P.toPseudoTorsor
  locally_nonempty x := by
    rcases P.locallyNonempty (⊤ : Opens X) with ⟨S, hS, hSections⟩
    rcases hS x (by simp : x ∈ (⊤ : Opens X)) with ⟨U, i, hi, hxU⟩
    exact ⟨U, hxU, hSections i hi⟩

/-- A morphism of `G`-torsors is the canonical opens-site pseudo-torsor morphism. -/
abbrev Hom (P Q : Torsor G) :=
  CategoryTheory.Sheaf.PseudoTorsor.Hom P.toPseudoTorsor Q.toPseudoTorsor

variable (G : X.Sheaf GrpCat.{u})

/-- The trivial `G`-torsor whose underlying sheaf is the underlying sheaf of types of `G`. -/
noncomputable def trivial : Torsor G :=
  ofSiteTorsor (CategoryTheory.Sheaf.Torsor.trivial G)

/-- A `G`-torsor is trivial when its canonical group-sheaf torsor bridge is trivial. -/
abbrev IsTrivial (P : Torsor G) : Prop :=
  P.toSiteTorsor.IsTrivial

end Torsor

end TopCat.SheafOfGroups
