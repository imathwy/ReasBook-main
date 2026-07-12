import Mathlib.Data.Finite.Sum
import StacksProject_2024.Chap25.«25_12_2_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` again surfaced mathlib's `OneHypercover` owner, but
-- this source item is about the local Chapter 25 `Hypercovering` API together with finiteness of
-- the degreewise fixed-target family index types.

-- Source/core/bridge triage:
-- `source-facing`: a hypercovering of `X` whose simplicial degree families stay in `B` and have
--   finite index types;
-- `core/canonical`: the `Finite` typeclass on each simplicial degree index type;
-- `bridge/view`: `Hypercovering.degreewiseFinite` and
--   `SemiRepresentableFamily.Over.IsFiniteBasisCovering`, which package the extra finiteness
--   conditions without changing the underlying Chapter 25 hypercovering owner.

namespace Hypercovering

variable {X : C}

/-- A hypercovering is degreewise finite when each simplicial degree family has a finite index
type. -/
def degreewiseFinite (K : Hypercovering J X) : Prop :=
  ∀ n : ℕ, Finite ((K.family n).index)

omit [HasPullbacks C] in
/-- Unfolding `degreewiseFinite` says exactly that every simplicial degree family index type is
finite. -/
theorem degreewiseFinite_iff (K : Hypercovering J X) :
    K.degreewiseFinite ↔ ∀ n : ℕ, Finite ((K.family n).index) :=
  Iff.rfl

/-- Every simplicial degree family index type of a degreewise finite hypercovering is finite. -/
omit [HasPullbacks C] in
theorem degreewiseFinite.finite
    {K : Hypercovering J X} (hK : K.degreewiseFinite) (n : ℕ) :
    Finite ((K.family n).index) :=
  hK n

/-- The degree-`0` family of a degreewise finite hypercovering has finite index type. -/
theorem degreewiseFinite.zero
    {K : Hypercovering J X} (hK : K.degreewiseFinite) :
    Finite ((K.family 0).index) :=
  hK.finite 0

/-- The degree-`1` family of a degreewise finite hypercovering has finite index type. -/
theorem degreewiseFinite.one
    {K : Hypercovering J X} (hK : K.degreewiseFinite) :
    Finite ((K.family 1).index) :=
  hK.finite 1

/-- Every degree-`n + 1` family of a degreewise finite hypercovering has finite index type. -/
theorem degreewiseFinite.succ
    {K : Hypercovering J X} (hK : K.degreewiseFinite) (n : ℕ) :
    Finite ((K.family (n + 1)).index) :=
  hK.finite (n + 1)

end Hypercovering

namespace SemiRepresentableFamily
namespace Over

variable {X : C}

/-- A fixed-target family over `X` is a finite `B`-covering family when it is a basis covering
family for `J.toPrecoverage` with sources in `B` and has finite index type. -/
def IsFiniteBasisCovering (J : GrothendieckTopology C) (B : Set C) (𝒰 : SR(C, X)) : Prop :=
  𝒰.IsBasisCovering J.toPrecoverage B ∧ Finite 𝒰.index

/-- Unfolding `IsFiniteBasisCovering` recovers the canonical conjunction of the basis-covering
condition and finiteness of the index type. -/
omit [HasPullbacks C] in
@[simp] theorem isFiniteBasisCovering_iff
    (J : GrothendieckTopology C) (B : Set C) (𝒰 : SR(C, X)) :
    𝒰.IsFiniteBasisCovering J B ↔ 𝒰.IsBasisCovering J.toPrecoverage B ∧ Finite 𝒰.index :=
  Iff.rfl

/-- For a Grothendieck topology, a finite basis covering family is exactly a covering family whose
source objects lie in `B` and whose index type is finite. -/
@[simp] theorem isFiniteBasisCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (B : Set C) (𝒰 : SR(C, X)) :
    𝒰.IsFiniteBasisCovering J B ↔
      𝒰.toSieve ∈ J X ∧ 𝒰.objectsIn B ∧ Finite 𝒰.index := by
  rw [isFiniteBasisCovering_iff, isBasisCovering_toPrecoverage_iff]
  constructor
  · rintro ⟨hcover, hfinite⟩
    exact ⟨hcover.1, hcover.2, hfinite⟩
  · rintro ⟨hcover, hobjects, hfinite⟩
    exact ⟨⟨hcover, hobjects⟩, hfinite⟩

/-- A finite basis covering family is a basis covering family. -/
omit [HasPullbacks C] in
theorem IsFiniteBasisCovering.isBasisCovering
    {J : GrothendieckTopology C} {B : Set C} {𝒰 : SR(C, X)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    𝒰.IsBasisCovering J.toPrecoverage B :=
  h𝒰.1

/-- Every source object of a finite basis covering family lies in `B`. -/
theorem IsFiniteBasisCovering.mem_basis
    {J : GrothendieckTopology C} {B : Set C} {𝒰 : SR(C, X)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) (i : 𝒰.index) :
    (𝒰.obj i).left ∈ B :=
  h𝒰.isBasisCovering.mem_basis i

/-- The source objects of a finite basis covering family lie in `B`. -/
theorem IsFiniteBasisCovering.objectsIn
    {J : GrothendieckTopology C} {B : Set C} {𝒰 : SR(C, X)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    𝒰.objectsIn B :=
  h𝒰.isBasisCovering.objectsIn

/-- The generated sieve of a finite basis covering family is covering. -/
theorem IsFiniteBasisCovering.toSieve_mem
    {J : GrothendieckTopology C} {B : Set C} {𝒰 : SR(C, X)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    𝒰.toSieve ∈ J X := by
  exact (isFiniteBasisCovering_toPrecoverage_iff J B 𝒰).1 h𝒰 |>.1

/-- A finite basis covering family has finite index type. -/
omit [HasPullbacks C] in
theorem IsFiniteBasisCovering.finiteIndex
    {J : GrothendieckTopology C} {B : Set C} {𝒰 : SR(C, X)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    Finite 𝒰.index :=
  h𝒰.2

/-- Adjoining one arrow from an object of `B` to a finite basis covering family again yields a
finite basis covering family as soon as the enlarged family is covering. -/
theorem IsFiniteBasisCovering.addSingleton
    {J : GrothendieckTopology C} {B : Set C} {𝒰 : SR(C, X)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B)
    {U' : C} (f : U' ⟶ X) (hU' : U' ∈ B)
    (hcover : (𝒰.addSingleton f).toSieve ∈ J X) :
    (𝒰.addSingleton f).IsFiniteBasisCovering J B := by
  rw [isFiniteBasisCovering_toPrecoverage_iff]
  refine ⟨hcover, ?_, ?_⟩
  · rw [addSingleton_objectsIn_iff]
    exact ⟨h𝒰.objectsIn, hU'⟩
  · let _ : Finite 𝒰.index := h𝒰.finiteIndex
    let _ : Finite Unit := Finite.of_fintype Unit
    simpa only [SemiRepresentableFamily.Over.addSingleton] using
      (inferInstance : Finite (Sum 𝒰.index Unit))

end Over
end SemiRepresentableFamily

open SemiRepresentableFamily.Over

/-- Lemma 25.12.6: let `\mathcal{C}` be a site and `\mathcal{B}` a subset of its objects. Assume
`C` has fibre products, every object admits a finite covering family whose source objects lie in
`B`, and adjoining a single arrow `U' \to U` with `U' ∈ B` to any finite `B`-covering family over
`U` again gives a covering family. Then every object `X` admits a hypercovering whose simplicial
degree families have source objects in `B` and finite index types. -/
@[stacks 094K]
theorem existsHypercoveringDegreewiseObjectsIn_degreewiseFinite
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : SR(C, U), 𝒰.IsFiniteBasisCovering J B)
    (hadd : ∀ {U : C} (𝒰 : SR(C, U)) (_ : 𝒰.IsFiniteBasisCovering J B)
      {U' : C} (f : U' ⟶ U) (_ : U' ∈ B), (𝒰.addSingleton f).toSieve ∈ J U)
    (X : C) :
    ∃ K : Hypercovering J X, K.degreewiseObjectsIn B ∧ K.degreewiseFinite := sorry

/-- Source-facing companion to Lemma 25.12.6: the finite hypercovering can be chosen so that the
degree-`0`, degree-`1`, and degree-`n + 1` simplicial families all have finite index types. -/
theorem existsHypercoveringDegreewiseObjectsIn_finite_zero_one_succ
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : SR(C, U), 𝒰.IsFiniteBasisCovering J B)
    (hadd : ∀ {U : C} (𝒰 : SR(C, U)) (_ : 𝒰.IsFiniteBasisCovering J B)
      {U' : C} (f : U' ⟶ U) (_ : U' ∈ B), (𝒰.addSingleton f).toSieve ∈ J U)
    (X : C) :
    ∃ K : Hypercovering J X,
      K.degreewiseObjectsIn B ∧
      Finite ((K.family 0).index) ∧
      Finite ((K.family 1).index) ∧
      ∀ n : ℕ, Finite ((K.family (n + 1)).index) := by
  rcases existsHypercoveringDegreewiseObjectsIn_degreewiseFinite B hcover hadd X with
    ⟨K, hKB, hKfin⟩
  exact ⟨K, hKB, hKfin.zero, hKfin.one, fun n ↦ hKfin.succ n⟩

end CategoryTheory
