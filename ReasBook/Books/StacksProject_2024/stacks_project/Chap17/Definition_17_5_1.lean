import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Zero
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry

/-
Domain-style sampling for Definition 17.5.1:
- primary domain: supports of local sections and sheaves on topological spaces and ringed spaces,
  detected by nonvanishing germs and nonzero stalks;
- sampled owner declarations:
  `abelianSheafSectionSupport`,
  `abelianSheafSupport`,
  `SheafOfModules.support`,
  `RingedSpace.ringCatSheaf`,
  `RingedSpace.Modules`,
  `SheafOfModules.toSheaf`,
  `RingedSpace.stalkModuleCat`;
- best owner abstraction:
  `abelianSheafSectionSupport` and `abelianSheafSupport` are the core owners;
  `SheafOfModules.support` is the canonical module-sheaf support bridge, while `ringSheafSupport`,
  `RingedSpace.ringSectionSupport`, `moduleSectionSupport`, and `moduleSupport` are further
  specializations along `RingedSpace.ringCatSheaf` and `SheafOfModules.toSheaf`;
- primitive data:
  an additive sheaf together with a local section, germ formation, and stalk formation;
- derived API:
  the ring/module support abbreviations and their membership lemmas.

Source/core/bridge triage:
- `source-facing`: the support notions named in Definition 17.5.1;
- `core/canonical`: `abelianSheafSectionSupport` and `abelianSheafSupport`;
- `bridge/view`: `SheafOfModules.support`, `ringSheafSupport`, `ringSectionSupport`,
  `moduleSectionSupport`, and `moduleSupport`. -/

section

variable {X : TopCat.{u}}
variable {U : Opens X}

/-- The support of a local section of an abelian sheaf over an open set `U` is the set of points
of `U` where the germ is nonzero. -/
def abelianSheafSectionSupport (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op U)) :
    Set U :=
  { x | ℱ.presheaf.germ U x.1 x.2 s ≠ 0 }

/-- Membership in the support of a local section of an abelian sheaf is nonvanishing of its germ.
-/
@[simp] theorem mem_abelianSheafSectionSupport_iff
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op U)) (x : U) :
    x ∈ abelianSheafSectionSupport ℱ s ↔ ℱ.presheaf.germ U x.1 x.2 s ≠ 0 := by
  rfl

/-- Definition 17.5.1: the support of an abelian sheaf on `X` is the set of points where the
stalk is nonzero. This is the canonical support owner; module support below is its specialization
along `SheafOfModules.toSheaf`. -/
def abelianSheafSupport (ℱ : X.Sheaf AddCommGrpCat.{u}) : Set X :=
  { x | ¬ IsZero (ℱ.presheaf.stalk x) }

/-- Membership in the support of an abelian sheaf is nonvanishing of the stalk. -/
@[simp] theorem mem_abelianSheafSupport_iff (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    x ∈ abelianSheafSupport ℱ ↔ ¬ IsZero (ℱ.presheaf.stalk x) := by
  rfl

end

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}

/-- Definition 17.5.1: the support of a sheaf of rings on `X` is the support of its canonical
underlying additive sheaf. -/
abbrev ringSheafSupport (ℱ : X.Sheaf RingCat.{u}) : Set X :=
  abelianSheafSupport
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj ℱ)

end

end TopCat.Sheaf

namespace SheafOfModules

section

variable {X : TopCat.{u}} {𝒪 : X.Sheaf RingCat.{u}}

/-- Definition 17.5.1: the support of a sheaf of `𝒪`-modules on `X` is the support of its
canonical underlying additive sheaf. -/
abbrev support (ℱ : SheafOfModules 𝒪) : Set X :=
  abelianSheafSupport ((toSheaf 𝒪).obj ℱ)

end

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {U : Opens X.carrier}

/-- The support of a local section of the structure sheaf is the ringed-space bridge/view
specialization of `abelianSheafSectionSupport` along `RingedSpace.ringCatSheaf`. -/
abbrev ringSectionSupport (f : X.presheaf.obj (op U)) : Set U :=
  { x | X.presheaf.germ U x.1 x.2 f ≠ 0 }

/-- Membership in the support of a local ring section is nonvanishing of its germ. -/
@[simp] theorem mem_ringSectionSupport_iff (f : X.presheaf.obj (op U)) (x : U) :
    x ∈ ringSectionSupport f ↔ X.presheaf.germ U x.1 x.2 f ≠ 0 := by
  rfl

end

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}
variable {ℱ : RingedSpace.Modules X}
variable {U : Opens X.carrier}

/-- Definition 17.5.1: the support of a section of an `\mathcal O_X`-module over an open set `U`
is the specialization of `abelianSheafSectionSupport` along `SheafOfModules.toSheaf`. -/
abbrev moduleSectionSupport (s : ℱ.val.obj (op U)) : Set U :=
  { x | TopCat.Presheaf.germ ℱ.val.presheaf U x.1 x.2 s ≠ 0 }

/-- Membership in the support of a local section is nonvanishing of its germ. -/
@[simp] theorem mem_moduleSectionSupport_iff (s : ℱ.val.obj (op U)) (x : U) :
    x ∈ moduleSectionSupport s ↔ TopCat.Presheaf.germ ℱ.val.presheaf U x.1 x.2 s ≠ 0 := by
  rfl

/-- Definition 17.5.1: the support of an `\mathcal O_X`-module is the set of points where the
stalk is nonzero. This is the support of its canonical underlying additive sheaf. -/
abbrev moduleSupport (ℱ : RingedSpace.Modules X) : Set X :=
  SheafOfModules.support ℱ

/-- Membership in the support of an `\mathcal O_X`-module is existence of a nonzero stalk
element. -/
@[simp] theorem mem_moduleSupport_iff
    (ℱ : RingedSpace.Modules X) (x : X) :
    x ∈ moduleSupport ℱ ↔ ∃ m : ↑(RingedSpace.stalkModuleCat ℱ x), m ≠ 0 := by
  rw [moduleSupport, mem_abelianSheafSupport_iff]
  change ¬ IsZero (TopCat.Presheaf.stalk ℱ.val.presheaf x) ↔ _
  rw [AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]
  simpa [RingedSpace.stalkModuleCat] using
    (nontrivial_iff_exists_ne (0 : ↑(RingedSpace.stalkModuleCat ℱ x)))

end

end AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-- The object property on `\mathcal O_X`-modules of being supported on the subset `T`. This is
the support-owner specialization of `moduleSupport`. -/
abbrev moduleSupportedOn (X : RingedSpace.{u}) (T : Set X) :
    ObjectProperty (RingedSpace.Modules X) :=
  fun M ↦ moduleSupport M ⊆ T

end

end AlgebraicGeometry.RingedSpace
