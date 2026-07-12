import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Lemma_17_18_2
import StacksProject_2024.Chap18.Lemma_18_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦
    Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))
local notation "IsLocallyDirectSummandOfFiniteFreeX" =>
  @SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree _ _
    (Opens.grothendieckTopology X) _ X.sheaf

/- Domain-style sampling for Lemma 17.25.2:
- primary domain: invertible `\mathcal O_X`-modules on a ringed space, viewed through the
  canonical ringed-site owner `SheafOfModules.RingedSite.IsInvertible` and its standard Chapter 18
  consequences;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible`,
  `RingedSite.IsLocallyDirectSummandOfFiniteFree.exists_open_neighborhood_retract_free`,
  `SheafOfModules.RingedSite.iso_internalHom_unit_of_tensor_inverse`;
- best owner abstraction: the core owner is `SheafOfModules.RingedSite.IsInvertible`,
  specialized to `RingedSpace.Modules X`; the point-neighborhood retract statement is only the
  source-facing bridge unpacking the canonical Chapter 18 local direct-summand owner, while the
  other three clauses are exact opens-site specializations and should be handled by direct owner
  recall;
- primitive data: a module `ℒ : ModX`, and for the internal-Hom clause an explicit tensor
  trivialization `e : ℒ ⊗ₘ 𝒩 ≅ 𝒪X`, where `𝒪X` is the canonical tensor unit of `ModX`;
- derived API: the tensor-inverse characterization of invertibility, the induced local
  direct-summand owner, its neighborhood-wise retract form, and the canonical internal-Hom
  comparison isomorphism, all reused from the Chapter 18 owners except for the neighborhood bridge.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 17.25.2 on a ringed space;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible`,
  `SheafOfModules.RingedSite.iso_internalHom_unit_of_tensor_inverse`;
- `bridge/view`: the neighborhood retract theorem from
  `SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree`.
-/

section TensorInverse

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]

/- Lemma 17.25.2 (1): on a ringed space, the tensor-inverse characterization of invertibility is
the exact opens-site specialization of the Chapter 18 owner theorem. -/
recall SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse

end TensorInverse

section LocalDirectSummand

variable [MonoidalCategory (RingedSpace.Modules X)]

/- Companion recall: the local direct-summand owner is already provided in Chapter 18 and
specializes directly to ringed spaces. -/
recall SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible

/-- Lemma 17.25.2 (2): an invertible `\mathcal O_X`-module is locally a direct summand of a
finite free `\mathcal O_X`-module. -/
theorem exists_open_neighborhood_retract_free_of_isInvertible
    (ℒ : ModX)
    [IsInvertibleX ℒ]
    (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
      Nonempty (Retract (ℒ.over U) (SheafOfModules.free.{u} I)) := by
  -- This statement is a ringed-space bridge for the Chapter 18 owner theorem.  Avoid forcing
  -- extra symmetric-monoidal instance synthesis in this upstream statement file.
  sorry

end LocalDirectSummand

section InternalHom

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat]
variable [∀ U : Opens X,
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : Opens X,
  ((Opens.grothendieckTopology X).over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : Opens X, ∀ V : Over U,
  HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat]
variable [∀ U : Opens X, ∀ V : Over U,
  (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : Opens X, ∀ V : Over U,
  (((Opens.grothendieckTopology X).over U).over V).HasSheafCompose
    (forget₂ RingCat AddCommGrpCat)]
local notation "𝒪X" => (𝟙_ ModX : ModX)
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

/- Lemma 17.25.2 (3): if `\mathcal L \otimes_{\mathcal O_X} \mathcal N \cong \mathcal O_X`,
then `\mathcal N` is canonically isomorphic to `\mathcal L ⟶[ModX] \mathcal O_X`. This is the
same opens-site specialization of the Chapter 18 owner theorem. -/
recall SheafOfModules.RingedSite.iso_internalHom_unit_of_tensor_inverse

end InternalHom

end SheafOfModules
