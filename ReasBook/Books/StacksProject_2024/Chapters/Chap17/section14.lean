import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_14_1 (from Chap17) -/
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

private abbrev FreeOn (U : Opens X) (I : Type u) :
    SheafOfModules (X.ringCatSheaf.over U) :=
  SheafOfModules.free.{u} I

/- Domain-style sampling for Definition 17.14.1:
- primary domain: locally free sheaves of modules on ringed spaces;
- inspected owner declarations:
  `Module.LocallyFree`,
  `Module.FiniteLocallyFree`,
  `Module.FiniteLocallyFreeOfRank`,
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`;
- best owner abstraction: the ringed-space module owner `(RingedSpace.Modules X)`, together with the
  localized restriction owner `ℱ.over U` and the canonical free and unit sheaves over
  `(RingedSpace.ringCatSheaf X)`;
- primitive data: local trivializations of `ℱ.over U` by free sheaves, with finiteness or fixed
  rank carried only by the local basis type;
- derived API: freeness implies local freeness, finite local freeness implies local freeness,
  constant rank implies finite local freeness, and the structure sheaf has rank `1`.

Source/core/bridge triage:
- `source-facing`: the Stacks Project definitions of locally free, finite locally free, and
  finite locally free of constant rank on a ringed space;
- `core/canonical`: the ambient owner category `(RingedSpace.Modules X)`;
- `bridge/view`: the derived instances and theorem below, which keep the owner abstraction and
  avoid parallel wrapper data. -/

/-- Definition 17.14.1 (1): an `\mathcal O_X`-module sheaf is locally free if every point has an
open neighbourhood on which the restricted sheaf is free. -/
class IsLocallyFree (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to a free module sheaf on some open
  neighbourhood. -/
  exists_open_neighborhood_iso_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u),
      Nonempty (ℱ.over U ≅ FreeOn U I)

/-- Definition 17.14.1 (2): an `\mathcal O_X`-module sheaf is finite locally free if every point
has an open neighbourhood on which the restricted sheaf is free on a finite index set. -/
class IsFiniteLocallyFree (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to a finite free module sheaf on some open
  neighbourhood. -/
  exists_open_neighborhood_iso_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
        Nonempty (ℱ.over U ≅ FreeOn U I)

/-- An `\mathcal O_X`-module sheaf is locally a direct summand of a finite free module if every
point has an open neighbourhood on which the restricted sheaf is a retract of a finite free
module sheaf. -/
class IsLocallyDirectSummandOfFiniteFree (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes a retract of a finite free module sheaf on some open
  neighbourhood. -/
  exists_open_neighborhood_retract_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
        Nonempty (Retract (ℱ.over U) (FreeOn U I))

/-- Definition 17.14.1 (3): an `\mathcal O_X`-module sheaf is finite locally free of rank `r` if
every point has an open neighbourhood on which the restricted sheaf is isomorphic to
`\mathcal O_U^{\oplus r}`. -/
class IsFiniteLocallyFreeOfRank (r : ℕ) (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to the free rank-`r` module sheaf on some
  open neighbourhood. -/
  exists_open_neighborhood_iso_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U),
        Nonempty (ℱ.over U ≅ FreeOn U (ULift.{u} (Fin r)))

-- Proof sketch: use the whole space `X` as the neighbourhood of each point; the restriction of a
-- free sheaf to any open remains free on the same basis.
/-- A free `\mathcal O_X`-module sheaf is locally free. -/
instance free_isLocallyFree
    (ι : Type u) :
    IsLocallyFree (SheafOfModules.free.{u} ι : X.Modules) :=
  sorry

-- Proof sketch: forget the finiteness data in each local finite free trivialization and keep the
-- same open neighbourhoods and free local models.
/-- A finite locally free sheaf is locally free. -/
instance isFiniteLocallyFree_to_isLocallyFree
    (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    ℱ.IsLocallyFree := sorry

-- Proof sketch: each local isomorphism with a finite free module exhibits the sheaf as a retract
-- of that finite free module via the inverse isomorphism.
/-- A finite locally free sheaf is locally a direct summand of a finite free sheaf. -/
instance isFiniteLocallyFree_to_isLocallyDirectSummandOfFiniteFree
    (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    ℱ.IsLocallyDirectSummandOfFiniteFree := by
  classical
  refine ⟨?_⟩
  intro x
  rcases (inferInstance : IsFiniteLocallyFree ℱ).exists_open_neighborhood_iso_free x with
    ⟨U, hxU, I, hI, hIso⟩
  rcases hIso with ⟨e⟩
  exact ⟨U, hxU, I, hI, ⟨e.retract⟩⟩

-- Proof sketch: a local isomorphism with `\mathcal O_U^{\oplus r}` is in particular a local
-- isomorphism with a finite free module sheaf, since `Fin r` is finite.
/-- A finite locally free sheaf of rank `r` is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (r : ℕ)
    (ℱ : X.Modules) [IsFiniteLocallyFreeOfRank r ℱ] :
    IsFiniteLocallyFree ℱ := sorry

-- Proof sketch: for each point, take the whole space `X` as the neighbourhood; the structure
-- sheaf is already the free rank-one module sheaf over itself.
/-- The structure sheaf of a ringed space is finite locally free of rank `1`. -/
instance (X : RingedSpace.{u}) :
    IsFiniteLocallyFreeOfRank 1 (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

/-- The structure sheaf of a ringed space is finite locally free. -/
instance (X : RingedSpace.{u}) :
    IsFiniteLocallyFree (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank 1
    (SheafOfModules.unit X.ringCatSheaf)

end SheafOfModules

/-! ### Lemma_17_14_2 (from Chap17) -/
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 17.14.2:
- primary domain: locally free and quasi-coherent sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.IsQuasicoherent`,
  `RingedSpace.Modules`,
  `SheafOfModules.free`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X`, with
  `ℱ.IsLocallyFree` as primitive source-facing data and `ℱ.IsQuasicoherent` as derived API;
- primitive data: a module sheaf `ℱ` on `X` together with its local trivializations by free
  sheaves from `Definition_17_14_1`;
- derived API: the quasi-coherence instance attached to a locally free module.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that a locally free `\mathcal O_X`-module is
  quasi-coherent;
- `core/canonical`: the owner predicates `SheafOfModules.IsLocallyFree` and
  `SheafOfModules.IsQuasicoherent` on `RingedSpace.Modules X`;
- `bridge/view`: this file should expose the result directly as the canonical instance rather than
  as a separate theorem plus an anonymous wrapper instance.
-/

-- Proof sketch: a local trivialization by free modules gives a local presentation on the same
-- neighbourhood, since free sheaves are quasi-coherent and quasi-coherence is local on the base.
/-- Lemma 17.14.2: if `\mathcal F` is a locally free sheaf of `\mathcal O_X`-modules on a ringed
space `(X, \mathcal O_X)`, then `\mathcal F` is quasi-coherent. -/
instance ringedSpaceModule_isQuasicoherent_of_isLocallyFree
    (ℱ : RingedSpace.Modules X) [ℱ.IsLocallyFree] :
    ℱ.IsQuasicoherent := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_14_3 (from Chap17) -/
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.14.3:
- primary domain: local freeness of module sheaves on ringed spaces and its stability under
  pullback;
- inspected owner declarations:
  `SheafOfModules.IsLocallyFree`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.pullback`,
  `RingedSpace.Hom.toRingCatSheafHom`;
- best owner abstraction: the canonical pullback functor `f^*` on module sheaves together with
  the owner predicate `SheafOfModules.IsLocallyFree`;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y`, a module sheaf `𝒢` on `Y`, and the
  local-freeness structure on `𝒢`;
- derived API: the pullback-stability theorem and instance below. -/

/- Source/core/bridge triage for Lemma 17.14.3:
- `source-facing`: the Stacks assertion that pulling back a locally free module along a morphism of
  ringed spaces again gives a locally free module;
- `core/canonical`: the pullback owner `f^*` and the typeclass owner `SheafOfModules.IsLocallyFree`;
- `bridge/view`: the ringed-space specialization of pullback-stability for the canonical owner.

This file should therefore expose local freeness under pullback in the same theorem-plus-instance
shape as the analogous flatness file, so downstream code can infer local freeness of `((f^*).obj 𝒢)`
from `[𝒢.IsLocallyFree]` without a separate wrapper theorem. -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

-- Proof sketch: for each `x : X`, pick a neighbourhood of `f x` on which `𝒢` is free. Pull that
-- neighbourhood back along `f`; the restriction of `f^*𝒢` to the preimage is the pullback of a
-- free sheaf, hence free of the same rank, so these pulled-back neighbourhoods witness local
-- freeness of `f^*𝒢`.
/-- Lemma 17.14.3: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `\mathcal G` is a locally free `\mathcal O_Y`-module, then `f^*\mathcal G` is a
locally free `\mathcal O_X`-module. -/
theorem pullback_isLocallyFree
    (𝒢 : Y.Modules) [𝒢.IsLocallyFree] :
    ((f^*).obj 𝒢).IsLocallyFree := sorry

/-- Pullback along a morphism of ringed spaces preserves locally free module sheaves. -/
instance (𝒢 : Y.Modules) [𝒢.IsLocallyFree] :
    ((f^*).obj 𝒢).IsLocallyFree :=
  pullback_isLocallyFree f 𝒢

end AlgebraicGeometry

/-! ### Lemma_17_14_4 (from Chap17) -/
open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : RingedSpace.{u}}

private abbrev IsFreeOn (ℱ : RingedSpace.Modules X) (U : Opens X) (I : Type u) : Prop :=
  Nonempty
    (ℱ.over U ≅
      (SheafOfModules.free.{u} I :
        SheafOfModules.{u} ((RingedSpace.ringCatSheaf X).over U)))

/- Domain-style sampling for Lemma 17.14.4:
- primary domain: locally free sheaves of modules on ringed spaces and their rank functions;
- sampled owner declarations of the same kind:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsLocallyFree`,
  `ENat.card`,
  `Module.isLocallyConstant_rankAtStalk`;
- best owner abstraction: the ambient owner category `(RingedSpace.Modules X)` together with the owner
  predicate `SheafOfModules.IsLocallyFree`; the basis-size value is the canonical `ENat.card`;
- primitive data: a ringed space `X`, a module sheaf `ℱ : (RingedSpace.Modules X)`, and local freeness of
  `ℱ`;
- derived API: existence of a locally constant rank function whose value agrees with any local free
  trivialization.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting existence of a locally constant rank function for a
  locally free module sheaf;
- `core/canonical`: `(RingedSpace.Modules X)`, `SheafOfModules.IsLocallyFree`, and `ENat.card`;
- `bridge/view`: this theorem identifies the source rank value with the canonical cardinality of a
  free basis index type. -/

-- Proof sketch: for each point `x`, choose a neighbourhood on which `ℱ` is free. Since the stalk
-- ring `𝒪_{X, x}` is nontrivial, invariant basis number for free modules over the stalk shows that
-- any two local free trivializations around `x` have the same finite-or-infinite basis size. This
-- defines a rank value at `x`, and shrinking local trivializations shows that these values are
-- locally constant.
/-- Lemma 17.14.4: if all stalks of the structure sheaf of a ringed space are nontrivial and
`\mathcal F` is a locally free `\mathcal O_X`-module, then there is a locally constant rank
function `X → {0,1,2,\ldots} ∪ {\infty}` whose value at `x` is the finite cardinality, or `∞`, of
any local basis of `\mathcal F` near `x`. -/
theorem exists_locallyConstant_rank_of_isLocallyFree
    (ℱ : RingedSpace.Modules X)
    (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x)) [ℱ.IsLocallyFree] :
    ∃ rankℱ : LocallyConstant X (WithTop ℕ),
      ∀ (x : X) (U : Opens X) (_ : x ∈ U) (I : Type u) (htriv : IsFreeOn ℱ U I),
        rankℱ x = ENat.card I := sorry

end AlgebraicGeometry

/-! ### Lemma_17_14_5 (from Chap17) -/
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.14.5:
- primary domain: finite locally free sheaves of modules of constant rank on a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank`;
- best owner abstraction:
  the ambient owner category `RingedSpace.Modules X` together with the owner predicate
  `SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ`;
- primitive data:
  only the module sheaves `ℱ`, `𝒢`, the common rank `r`, and the owner instances asserting their
  local rank-`r` trivializations;
- derived API:
  the source-facing comparison `IsIso φ ↔ Epi φ` for a morphism between such sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks Project criterion that a morphism between finite locally free sheaves
  of the same rank is an isomorphism exactly when it is surjective;
- `core/canonical`: the ambient owner `RingedSpace.Modules X` and the owner predicate
  `SheafOfModules.IsFiniteLocallyFreeOfRank`;
- `bridge/view`: this file should use those owners directly rather than restating the ambient
  module category by its raw `SheafOfModules (RingedSpace.ringCatSheaf X)` presentation. -/

variable {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules}

-- Proof sketch: the forward implication is categorical. For the converse, surjectivity may be
-- checked on stalks, where both source and target become free modules of rank `r` over the local
-- ring `𝒪_{X,x}`; then Algebra, Lemma `10.16.4` upgrades surjectivity to bijectivity, and stalkwise
-- bijectivity implies that `φ` is an isomorphism.
/-- Lemma 17.14.5: for a morphism `φ : \mathcal F \to \mathcal G` of finite locally free
`\mathcal O_X`-modules of the same rank `r` on a ringed space `(X,\mathcal O_X)`, `φ` is an
isomorphism if and only if it is surjective, i.e. an epimorphism. -/
theorem moduleHom_isIso_iff_epi_of_isFiniteLocallyFreeOfRank
    (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r 𝒢]
    (φ : ℱ ⟶ 𝒢) :
    IsIso φ ↔ Epi φ := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_14_6 (from Chap17) -/
open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.14.6:
- primary domain: finite locally free sheaves of modules on a ringed space and their behavior
  under direct-summand constructions;
- sampled owner declarations:
  `SheafOfModules.IsFiniteLocallyFree`,
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `CategoryTheory.Retract`;
- best owner abstraction: the chapter owner for the local direct-summand condition is
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`; a global retract into a finite locally free
  sheaf is only bridge data producing that owner locally;
- primitive data: a module sheaf `ℱ : ModX`, local-ring stalks on `X`, finite presentation of `ℱ`,
  and local retracts of finite free restrictions of `ℱ`;
- derived API: the source-facing global retract theorem below.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a direct summand of a finite locally free sheaf
  is finite locally free;
- `core/canonical`: `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`;
- `bridge/view`: a global categorical retract `Retract ℱ ℋ` with `ℋ` finite locally free. -/

-- Proof sketch: for each `x : X`, the owner hypothesis gives a neighbourhood `U` on which
-- `ℱ.over U` is a retract of a finite free sheaf. Passing to the stalk at `x`, the stalk module
-- `ℱ_x` is therefore a retract of a finite free module over the local ring `𝒪_{X, x}`, hence is
-- finite free by Algebra, Lemma `10.78.2`. Lemma `17.11.7` then upgrades these stalkwise finite
-- free models to finite free neighbourhoods because `ℱ` is finitely presented.
/-- Owner-level form of Lemma 17.14.6: on a ringed space whose stalk rings are local, a finitely
presented `\mathcal O_X`-module that is locally a direct summand of a finite free module is finite
locally free. -/
theorem isFiniteLocallyFree_of_isLocallyDirectSummandOfFiniteFree_of_stalk_isLocalRing
    (ℱ : ModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    [ℱ.IsFinitePresentation] [ℱ.IsLocallyDirectSummandOfFiniteFree] :
    ℱ.IsFiniteLocallyFree := sorry

-- Proof sketch: a global retract of a finite locally free sheaf restricts on each neighbourhood
-- where `ℋ` is finite free to a local retract of a finite free sheaf, so `ℱ` satisfies the owner
-- predicate `IsLocallyDirectSummandOfFiniteFree`. A retract of a finitely presented sheaf is again
-- finitely presented, so the owner theorem applies.
/-- Lemma 17.14.6: if every stalk `\mathcal O_{X, x}` is a local ring, then any direct summand of
a finite locally free `\mathcal O_X`-module is finite locally free. Here the direct-summand
hypothesis is expressed by a categorical retract. -/
theorem isFiniteLocallyFree_of_retract_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    {ℱ ℋ : ModX} [ℋ.IsFiniteLocallyFree] (hret : Retract ℱ ℋ) :
    ℱ.IsFiniteLocallyFree := sorry

end SheafOfModules
