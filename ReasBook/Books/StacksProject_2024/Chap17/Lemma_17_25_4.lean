import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap17.Definition_17_25_1
import StacksProject_2024.Chap18.Lemma_18_40_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

/- Domain-style sampling for Lemma 17.25.4:
- primary domain: invertible `\mathcal O_X`-modules and finite locally free rank-one modules on a
  ringed space, viewed as the opens-site specialization of the Chapter 18 ringed-site theory;
- inspected owner declarations:
  `CategoryTheory.HasLocalUnitDichotomy`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one`,
  `RingedSpace.isUnit_res_basicOpen`;
- best owner abstraction: the public statements should stay at the canonical owners
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, and the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one`; the only genuinely
  local bridge in this file is that stalk-locality on a ringed space implies the opens-site
  local-unit dichotomy;
- primitive data: a module sheaf `ℒ : RingedSpace.Modules X`, plus in clause `(2)` the stalkwise
  local-ring hypothesis;
- derived API: the Chapter 18 rank-one invertibility owner specialized by direct recall, and the
  converse rank-one local freeness statement obtained by feeding the local-unit-dichotomy bridge
  into the Chapter 18 owner theorem.

Source/core/bridge triage:
- `source-facing`: the two clauses of Stacks Lemma 17.25.4 on a ringed space;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, `CategoryTheory.HasLocalUnitDichotomy`, and the
  Chapter 18 owner theorem
  `SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one`;
- `bridge/view`: the opens-site local-unit-dichotomy theorem derived from the stalk-local-ring
  hypothesis, then used to specialize the Chapter 18 converse theorem. -/

theorem hasLocalUnitDichotomy_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    HasLocalUnitDichotomy (Opens.grothendieckTopology X) X.sheaf := by
  refine ⟨?_⟩
  intro U f
  let f' : X.presheaf.obj (op U) := f
  let Y : Bool → Opens X := fun
    | false => X.basicOpen f'
    | true => X.basicOpen (1 - f')
  let π : (b : Bool) → Y b ⟶ U := fun
    | false => homOfLE (X.basicOpen_le f')
    | true => homOfLE (X.basicOpen_le (1 - f'))
  let S : (Opens.grothendieckTopology X).Cover U := ⟨Sieve.ofArrows Y π, by
    intro x hxU
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ U x hxU f') with h | h
    · refine ⟨Y false, π false, Sieve.ofArrows_mk Y π false, ?_⟩
      exact (X.mem_basicOpen f' x hxU).2 h
    · refine ⟨Y true, π true, Sieve.ofArrows_mk Y π true, ?_⟩
      exact (X.mem_basicOpen (1 - f') x hxU).2 (by simpa using h)⟩
  refine ⟨S, ?_⟩
  intro I
  change
    IsUnit ((X.presheaf.map I.f.op).hom f') ∨
      IsUnit (1 - (X.presheaf.map I.f.op).hom f')
  rcases (Sieve.mem_ofArrows_iff Y π I.f).1 I.hf with ⟨b, a, ha⟩
  cases b with
  | false =>
      left
      simpa [π, ha] using
        RingHom.isUnit_map ((X.presheaf.map a.op).hom) (X.isUnit_res_basicOpen f')
  | true =>
      right
      have hunit :
          IsUnit ((X.presheaf.map I.f.op).hom (1 - f')) := by
        simpa [π, ha] using
          RingHom.isUnit_map ((X.presheaf.map a.op).hom) (X.isUnit_res_basicOpen (1 - f'))
      simpa [map_sub] using hunit

variable [MonoidalCategory (RingedSpace.Modules X)]

/- Lemma 17.25.4 (1): on a ringed space, rank-one finite locally free modules are invertible by
direct specialization of the Chapter 18 owner theorem on ringed sites. -/
recall SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one

-- Proof sketch: invertibility gives that each stalk `ℒ_x` is an invertible module over the stalk
-- ring `𝒪_{X, x}`. Over a local ring, every invertible module is free of rank `1`; then Lemma
-- `17.11.7` upgrades the stalkwise free rank-one statement to a neighbourhood trivialization,
-- yielding finite local freeness of rank `1`.
/-- Lemma 17.25.4 (2): if every stalk `\mathcal O_{X, x}` is a local ring, then every invertible
`\mathcal O_X`-module is locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    (ℒ : (RingedSpace.Modules X)) [IsInvertible ℒ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 ℒ := by
  let _ : HasLocalUnitDichotomy (Opens.grothendieckTopology X) X.sheaf :=
    hasLocalUnitDichotomy_of_stalk_isLocalRing hlocal
  sorry

end AlgebraicGeometry.RingedSpace
