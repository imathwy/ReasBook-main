import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksProject_2024.Chap06.Definition_6_25_1
import StacksProject_2024.Chap20.«20_9_0_2»
import StacksProject_2024.Chap20.«20_14_1_2»
import StacksProject_2024.Chap20.«20_11_0_2»
import StacksProject_2024.Chap20.Lemma_20_11_2
import StacksProject_2024.Chap20.Lemma_20_19_3
import StacksProject_2024.Chap20.«20_25_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry HomologicalComplex
open CategoryTheory.Sheaf
open CategoryTheory.Limits
open scoped AlgebraicGeometry RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules Y)]

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "TopOpenX" => (⊤ : Opens X.carrier)
local notation "TopOpenY" => (⊤ : Opens Y.carrier)

private theorem cechComplex_pushforward_eq_preimage
    {J : Type u} (f : X ⟶ Y) (𝒱 : J → Opens Y.carrier) (ℱ : ModX) :
    (cechComplexFunctor 𝒱).obj ((moduleUnderlyingPresheaf Y).obj ((f _*).obj ℱ)) =
      (cechComplexFunctor (fun j ↦ preimageOpen f (𝒱 j))).obj ((moduleUnderlyingPresheaf X).obj ℱ) :=
  by
    sorry

/-- A morphism on module Čech cohomology is the one induced by an `f`-map together with a
refinement of the source cover by the inverse-image cover if it is the homology map of the
canonical morphism of Čech complexes. -/
def IsModuleCechCohomologyMapOfFMapAndRefinement
    {I J : Type u}
    (f : X ⟶ Y) (𝒢 : ModY) (ℱ : ModX) (φ : 𝒢 ⟶ (f _*).obj ℱ)
    (𝒰 : I → Opens X.carrier) (𝒱 : J → Opens Y.carrier)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (𝒱 j)) 𝒰 c) (p : ℕ)
    (top : moduleCechCohomology 𝒱 𝒢 p ⟶ moduleCechCohomology 𝒰 ℱ p) : Prop :=
  top =
    (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
      (((cechComplexFunctor 𝒱).map ((moduleUnderlyingPresheaf Y).map φ)) ≫
        eqToHom (cechComplex_pushforward_eq_preimage f 𝒱 ℱ) ≫
        (cechRefinementNatTrans (fun j ↦ preimageOpen f (𝒱 j)) 𝒰 c hc).app
          ((moduleUnderlyingPresheaf X).obj ℱ))

/-- The underlying morphism of abelian sheaves attached to a module `f`-map. -/
abbrev underlyingSheafMapOfFMap
    (f : X ⟶ Y) {𝒢 : ModY} {ℱ : ModX} (φ : 𝒢 ⟶ (f _*).obj ℱ) :
    (moduleUnderlyingSheaf Y).obj 𝒢 ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj ((moduleUnderlyingSheaf X).obj ℱ) :=
  (moduleUnderlyingSheaf Y).map φ

/-
The canonical owner-level comparison identifying the cohomology of the pushforward of the
underlying abelian sheaf of `ℱ` on `Y` with the cohomology of the underlying abelian sheaf of `ℱ`
on `X`, specialized to the top open.
-/
omit [HasInjectiveResolutions (RingedSpace.Modules X)]
  [HasInjectiveResolutions (RingedSpace.Modules Y)] in
theorem pushforward_underlyingSheafCohomologyOnTop_isomorphic_preimage
    (f : X ⟶ Y) (ℱ : ModX) (p : ℕ) :
    IsIsomorphic
      (((moduleUnderlyingSheaf Y).obj ((f _*).obj ℱ)).H' p TopOpenY)
      (((moduleUnderlyingSheaf X).obj ℱ).H' p TopOpenX) := by
  simpa using
    pushforward_cohomologyOnOpen_isomorphic_preimage
      f.hom.base ((moduleUnderlyingSheaf X).obj ℱ) TopOpenY p

/-- A morphism on the underlying-sheaf cohomology groups is the lower horizontal map in
Lemma 20.15.1 if it is the cohomology map induced by `φ`, followed by a representative of the
canonical pushforward/preimage comparison supplied by
`pushforward_underlyingSheafCohomologyOnTop_isomorphic_preimage`. -/
def IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison
    (f : X ⟶ Y) (𝒢 : ModY) (ℱ : ModX) (φ : 𝒢 ⟶ (f _*).obj ℱ) (p : ℕ)
    (bottom :
      ((moduleUnderlyingSheaf Y).obj 𝒢).H' p TopOpenY ⟶
        ((moduleUnderlyingSheaf X).obj ℱ).H' p TopOpenX) : Prop :=
  ∃ e :
    (((moduleUnderlyingSheaf Y).obj ((f _*).obj ℱ)).H' p TopOpenY) ≅
      (((moduleUnderlyingSheaf X).obj ℱ).H' p TopOpenX),
    bottom = cohomologyMapOfFMap f.hom.base p (underlyingSheafMapOfFMap f φ) ≫ e.hom

/-
There exists a lower horizontal map for Lemma 20.15.1 satisfying the canonical
pushforward/preimage comparison specification.
-/
omit [HasInjectiveResolutions (RingedSpace.Modules X)]
  [HasInjectiveResolutions (RingedSpace.Modules Y)] in
theorem exists_underlyingSheafCohomologyMapOfFMapAndPushforwardComparison
    (f : X ⟶ Y) (𝒢 : ModY) (ℱ : ModX) (φ : 𝒢 ⟶ (f _*).obj ℱ) (p : ℕ) :
    ∃ bottom :
      ((moduleUnderlyingSheaf Y).obj 𝒢).H' p TopOpenY ⟶
        ((moduleUnderlyingSheaf X).obj ℱ).H' p TopOpenX,
      IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison
        f 𝒢 ℱ φ p bottom := by
  rcases pushforward_underlyingSheafCohomologyOnTop_isomorphic_preimage f ℱ p with ⟨e⟩
  refine ⟨cohomologyMapOfFMap f.hom.base p (underlyingSheafMapOfFMap f φ) ≫ e.hom, ?_⟩
  exact ⟨e, rfl⟩

/- Domain-style sampling for Lemma 20.15.1:
- primary domain: Čech cohomology, sheaf cohomology, and pushforward for `𝒪_X`-modules on
  ringed spaces;
- sampled owner declarations:
  `moduleCechCohomology`,
  `underlyingSheafMapOfFMap`,
  `IsModuleCechToUnderlyingSheafCohomologyMap`,
  `IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison`,
  `IsModuleCechCohomologyMapOfFMapAndRefinement`,
  `cechRefinementNatTrans`,
  `Sheaf.cohomologyMapOfFMap`,
  `Sheaf.pushforward_cohomologyOnOpen_isomorphic_preimage`,
  `CategoryTheory.CommSq`,
  `IsRefinement`;
- best owner abstraction: the source-facing square should keep the bottom edge as the canonical
  cohomology map induced by `φ`, while the two vertical Čech-to-cohomology edges are candidate
  comparison morphisms satisfying `IsModuleCechToUnderlyingSheafCohomologyMap`; the top edge is
  an arbitrary morphism carrying the companion witness
  `IsModuleCechCohomologyMapOfFMapAndRefinement`, so the induced homology map built from the
  presheaf morphism induced by `φ` and the refinement owner `IsRefinement` stays theorem-level,
  and the bottom edge should be specified by the proposition
  `IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison`, which packages the cohomology
  map induced by `φ` together with a representative of the canonical owner-level comparison
  `pushforward_underlyingSheafCohomologyOnTop_isomorphic_preimage f ℱ p`, rather than by a bare
  existential conclusion choosing an isomorphism in the main theorem statement;
- primitive data: a morphism `f`, an `f`-map `φ : 𝒢 ⟶ f_* ℱ`, indexed covers `𝒰` and `𝒱`, an
  explicit refinement map `c : I → J`, and the chapter owner witness
  `IsRefinement (fun j ↦ preimageOpen f (𝒱 j)) 𝒰 c`;
- derived API: the induced map on sheaf cohomology of the underlying abelian sheaves, the
  theorem-level pushforward identification from `H^p(Y, f_* ℱ)` to
  `H^p(X, ℱ)`, the bottom-edge existence theorem
  `exists_underlyingSheafCohomologyMapOfFMapAndPushforwardComparison`, and the resulting
  commutative square for any bottom morphism satisfying the source-facing specification.

Source/core/bridge triage:
- `source-facing`: the cohomology square attached to an `f`-map and a refinement of covers;
- `core/canonical`: `moduleCechCohomology`, `cechRefinementNatTrans`,
  `IsModuleCechToUnderlyingSheafCohomologyMap`, `Sheaf.cohomologyMapOfFMap`,
  `Sheaf.pushforward_cohomologyOnOpen_isomorphic_preimage`, and `CommSq`;
- `bridge/view`: the companion predicate
  `IsModuleCechCohomologyMapOfFMapAndRefinement`, recording that the chosen top horizontal
  morphism is obtained by applying `homologyFunctor` to the presheaf map induced by `φ`,
  followed by the inverse-image identification and the canonical Čech refinement map, together
  with `underlyingSheafMapOfFMap`, the owner-level comparison theorem
  `pushforward_underlyingSheafCohomologyOnTop_isomorphic_preimage`, and the source-facing
  bottom-edge specification `IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison`.

Primitive data versus derived API:
- primitive data: `f`, `φ`, the two covers, the explicit refinement map `c`, and the refinement
  witness `hc : IsRefinement (fun j ↦ preimageOpen f (𝒱 j)) 𝒰 c`;
  - derived API: the existence of a left comparison edge on `Y`, the existence of a right
  comparison edge for `𝒰` on `X`, a chosen top horizontal morphism together with the witness
  `IsModuleCechCohomologyMapOfFMapAndRefinement f 𝒢 ℱ φ 𝒰 𝒱 c hc p top`, and the
  refinement, and a chosen bottom horizontal morphism satisfying
  `IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison f 𝒢 ℱ φ p bottom`.
-/

-- Proof sketch: choose a function `c : I → J` witnessing that `𝒰` refines `f⁻¹𝒱`, and use it
-- together with `φ` to build the usual morphism of Čech complexes from `Čech(𝒱, 𝒢)` to
-- `Čech(𝒰, ℱ)`, and let `top` be any induced map on homology satisfying
-- `IsModuleCechCohomologyMapOfFMapAndRefinement`.
-- Compare the source Čech-to-sheaf-cohomology morphism on `Y` with the cohomology map induced by
-- `φ` on the underlying abelian sheaves, and let the lower horizontal map be any morphism
-- satisfying `IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison`, which already
-- packages a representative of the canonical theorem
-- `pushforward_cohomologyOnOpen_isomorphic_preimage` identifying `H^p(Y, f_* ℱ)` with
-- `H^p(X, ℱ)`. The derived double-complex argument from the source text then yields the
-- commutative square for any chosen Čech-to-cohomology comparison morphisms on the two sides.
/-- Lemma 20.15.1: if `f : X ⟶ Y` is a morphism of ringed spaces and
`φ : 𝒢 ⟶ f_* ℱ` is an `f`-map, while `𝒰` and `𝒱` are open coverings of `X` and `Y` with
`𝒰` refining `f⁻¹𝒱` via `c : I → J`, then for every degree `p` any chosen induced
map on Čech cohomology fits into a commutative square with any chosen Čech-to-cohomology
comparison morphisms for `𝒱` and `𝒰`, and with any chosen lower horizontal morphism satisfying
`IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison f 𝒢 ℱ φ p bottom`;
this keeps the pushforward-cohomology identification at the canonical theorem-level owner
`pushforward_cohomologyOnOpen_isomorphic_preimage` instead of replacing it by a bare existential
isomorphism witness in the conclusion. This is the cohomology-level form of the commutative
derived diagram in the textbook statement. -/
@[stacks 01FD]
theorem cech_cohomology_square_of_f_map_and_refinement
    {I J : Type u}
    (f : X ⟶ Y)
    (𝒢 : ModY) (ℱ : ModX)
    (φ : 𝒢 ⟶ (f _*).obj ℱ)
    (𝒰 : I → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (𝒱 : J → Opens Y.carrier) (h𝒱 : iSup 𝒱 = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (𝒱 j)) 𝒰 c) (p : ℕ)
    (top : moduleCechCohomology 𝒱 𝒢 p ⟶ moduleCechCohomology 𝒰 ℱ p)
    (htop : IsModuleCechCohomologyMapOfFMapAndRefinement f 𝒢 ℱ φ 𝒰 𝒱 c hc p top)
    (left :
      moduleCechCohomology 𝒱 𝒢 p ⟶ ((moduleUnderlyingSheaf Y).obj 𝒢).H' p TopOpenY)
    (hleft : IsModuleCechToUnderlyingSheafCohomologyMap TopOpenY 𝒱 h𝒱 𝒢 p left)
    (right :
      moduleCechCohomology 𝒰 ℱ p ⟶ ((moduleUnderlyingSheaf X).obj ℱ).H' p TopOpenX)
    (hright : IsModuleCechToUnderlyingSheafCohomologyMap TopOpenX 𝒰 h𝒰 ℱ p right)
    (bottom :
      ((moduleUnderlyingSheaf Y).obj 𝒢).H' p TopOpenY ⟶
        ((moduleUnderlyingSheaf X).obj ℱ).H' p TopOpenX)
    (hbottom : IsUnderlyingSheafCohomologyMapOfFMapAndPushforwardComparison
      f 𝒢 ℱ φ p bottom) :
    CommSq left top bottom right := by
  sorry

end

end AlgebraicGeometry.RingedSpace
