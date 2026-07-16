import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_36_4
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic
import StacksProject_2024.stacks_project.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [LocallySmall.{u} C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => ringedSiteModuleCategory J 𝒪

private noncomputable abbrev sourcePointStalkRingEquiv
    (p : GrothendieckTopology.Point.{u} J) :
    ↑(p.stalkRing (ringSheaf J 𝒪)) ≃+* ↑(sourcePointRing 𝒪 p) :=
  ((p.presheafFiberCompIso (forget₂ CommRingCat RingCat)).app 𝒪.obj).ringCatIsoToRingEquiv

private instance sheafModuleStalkFunctor_additive
    (p : GrothendieckTopology.Point.{u} J) :
    (p.sheafModuleStalkFunctor (ringSheaf J 𝒪)).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (p.sheafModuleStalk_exact (ringSheaf J 𝒪))

/-- The stalk functor on `𝒪`-modules at the site point `p`, transported to the canonical
commutative stalk ring `sourcePointRing 𝒪 p`. -/
noncomputable abbrev stalkFunctor
    (p : GrothendieckTopology.Point.{u} J) :
    Mod ⥤ ModuleCat (sourcePointRing 𝒪 p) :=
  p.sheafModuleStalkFunctor (ringSheaf J 𝒪) ⋙
    ModuleCat.restrictScalars (sourcePointStalkRingEquiv 𝒪 p).symm.toRingHom

instance stalkFunctor_additive
    (p : GrothendieckTopology.Point.{u} J) :
    (stalkFunctor 𝒪 p).Additive := by infer_instance

/-- The stalk complex `K_p` of a cochain complex of `𝒪`-modules at the site point `p`. -/
noncomputable abbrev stalkComplex
    (K : CochainComplex Mod ℤ) (p : GrothendieckTopology.Point.{u} J) :
    CochainComplex (ModuleCat (sourcePointRing 𝒪 p)) ℤ :=
  ((stalkFunctor 𝒪 p).mapHomologicalComplex (up ℤ)).obj K

/-- The source-facing stalk complex is the degreewise image of `K` under `stalkFunctor`. -/
@[simp] theorem stalkComplex_eq_mapHomologicalComplex_obj
    (K : CochainComplex Mod ℤ) (p : GrothendieckTopology.Point.{u} J) :
    stalkComplex 𝒪 K p =
      ((stalkFunctor 𝒪 p).mapHomologicalComplex (up ℤ)).obj K :=
  rfl

/-- In degree `n`, `stalkComplex 𝒪 K p` is the stalk of the term `K.X n`. -/
@[simp] theorem stalkComplex_X
    (K : CochainComplex Mod ℤ) (p : GrothendieckTopology.Point.{u} J) (n : ℤ) :
    (stalkComplex 𝒪 K p).X n = (stalkFunctor 𝒪 p).obj (K.X n) :=
  rfl

/-- Stalkwise `K`-flatness may be read directly on the mapped homological complex. -/
@[simp] theorem stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
    (K : CochainComplex Mod ℤ) (p : GrothendieckTopology.Point.{u} J) :
    (stalkComplex 𝒪 K p).IsKFlat ↔
      (((stalkFunctor 𝒪 p).mapHomologicalComplex (up ℤ)).obj K).IsKFlat := by
  rfl

/-
Domain-style sampling for Lemma 21.18.6:
- primary domain: K-flat cochain complexes of sheaves of modules and their stalk complexes;
- inspected owner declarations:
  `CategoryTheory.sourcePointRing`,
  `GrothendieckTopology.Point.stalkRing`,
  `GrothendieckTopology.Point.sheafModuleStalkFunctor`,
  `GrothendieckTopology.Point.sheafModuleStalk_exact`,
  `GrothendieckTopology.Point.presheafFiberCompIso`,
  `ModuleCat.restrictScalars`,
  `CochainComplex.IsKFlat`;
- best owner abstraction: the owner of stalk modules is already the canonical ring-valued stalk
  functor `GrothendieckTopology.Point.sheafModuleStalkFunctor (ringSheaf J 𝒪)`; to expose the
  monoidal/K-flat owner on stalk complexes over the commutative source stalk ring, this file
  keeps only the thin bridge that retargets the stalk module action along the canonical ring
  equivalence from `p.stalkRing (ringSheaf J 𝒪)` to `CategoryTheory.sourcePointRing 𝒪 p`, while
  K-flatness remains owned by the postfix predicate `K.IsKFlat`.
- primitive data: a complex `K`, a point `p`, and the canonical stalk-ring owner
  `CategoryTheory.sourcePointRing 𝒪 p`.
- derived API: the stalkwise K-flatness assertions for the mapped source-point stalk complexes.

Source/core/bridge triage:
- `source-facing`: the stalk complex `stalkComplex 𝒪 K p`;
- `core/canonical`: `GrothendieckTopology.Point.stalkRing`,
  `CategoryTheory.sourcePointRing`,
  `GrothendieckTopology.Point.sheafModuleStalkFunctor (ringSheaf J 𝒪)`,
  `GrothendieckTopology.Point.sheafModuleStalk_exact`,
  `GrothendieckTopology.Point.presheafFiberCompIso`,
  `ModuleCat.restrictScalars`, and the owner predicate `K.IsKFlat`;
- `bridge/view`: the restriction-of-scalars transport from
  `p.stalkRing (ringSheaf J 𝒪)` to the canonical commutative stalk `sourcePointRing 𝒪 p`,
  together with its `mapHomologicalComplex` view `stalkFunctor p`.
-/
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: choose a quasi-isomorphism from a K-flat complex with flat terms using Lemma
-- `21.17.11`, apply stalkwise preservation of K-flatness for pullbacks from Lemma `21.18.1`,
-- and reduce to the acyclic case. For an acyclic K-flat complex, use finite-presentation tests
-- for module-theoretic K-flatness and the exactness of taking stalks.
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Lemma 21.18.6 (1): if a cochain complex of `𝒪`-modules on a ringed site is K-flat, then for
every point `p` of the site its stalk complex `K_p` is K-flat as a cochain complex of
`𝒪_p`-modules. -/
@[stacks 0DEN]
theorem stalkComplex_isKFlat_of_isKFlat
    (K : CochainComplex Mod ℤ)
    (hK : K.IsKFlat)
    (p : GrothendieckTopology.Point.{u} J) :
    (stalkComplex 𝒪 K p).IsKFlat := sorry

-- Proof sketch: for an acyclic test complex `F` of `𝒪`-modules, exactness of the total tensor
-- product with `K` can be checked on stalks when the site has enough points. Stalk formation
-- commutes with tensor products and direct sums, so the stalkwise
-- K-flatness assumptions identify every stalk tensor complex with an acyclic module-theoretic
-- tensor product.
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Lemma 21.18.6 (2): if the site has enough points and every stalk complex `K_p` is K-flat over
`𝒪_p`, then `K` is K-flat on the ringed site. -/
@[stacks 0DEN]
theorem isKFlat_of_stalkComplex_isKFlat_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (K : CochainComplex Mod ℤ)
    (hK : ∀ p : GrothendieckTopology.Point.{u} J,
      (stalkComplex 𝒪 K p).IsKFlat) :
    K.IsKFlat := sorry

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If the site has enough points, K-flatness is equivalent to K-flatness of all stalk complexes. -/
theorem isKFlat_iff_stalkComplex_isKFlat_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (K : CochainComplex Mod ℤ) :
    K.IsKFlat ↔ ∀ p : GrothendieckTopology.Point.{u} J, (stalkComplex 𝒪 K p).IsKFlat := by
  constructor
  · intro hK p
    exact stalkComplex_isKFlat_of_isKFlat 𝒪 K hK p
  · intro hK
    exact isKFlat_of_stalkComplex_isKFlat_of_hasEnoughPoints 𝒪 K hK

end

end SheafOfModules.RingedSite
