import Mathlib
import stacks_project.Chap17.Definition_17_4_1
import stacks_project.Chap06.Definition_6_26_1

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry

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

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {U : Opens X}

/-- The support of a local section of the structure sheaf is the set of points where its germ in
the stalk is nonzero. -/
def ringSectionSupport (f : X.presheaf.obj (op U)) : Set U :=
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
variable {ℱ : X.Modules}
variable {U : Opens X}

/-- Definition 17.5.1: the support of a section of an `\mathcal O_X`-module over an open set `U`
is the specialization of `abelianSheafSectionSupport` along
`SheafOfModules.toSheaf`. -/
abbrev moduleSectionSupport (s : ℱ.val.obj (op U)) : Set U :=
  abelianSheafSectionSupport ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) s

/-- Membership in the support of a local section is nonvanishing of its germ. -/
@[simp] theorem mem_moduleSectionSupport_iff (s : ℱ.val.obj (op U)) (x : U) :
    x ∈ moduleSectionSupport s ↔
      TopCat.Presheaf.germ (PresheafOfModules.presheaf ℱ.val) U x.1 x.2 s ≠ 0 := by
  rfl

/-- Definition 17.5.1: the support of an `\mathcal O_X`-module is the set of points where the
stalk is nonzero. This is the support of its canonical underlying additive sheaf. -/
abbrev moduleSupport (ℱ : X.Modules) : Set X :=
  abelianSheafSupport ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ)

/-- Membership in the support of an `\mathcal O_X`-module is existence of a nonzero stalk
element. -/
@[simp] theorem mem_moduleSupport_iff
    (ℱ : X.Modules) (x : X) :
    x ∈ moduleSupport ℱ ↔ ∃ m : ↑(RingedSpace.stalkModuleCat ℱ x), m ≠ 0 := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ
  have hmem :
      x ∈ moduleSupport ℱ ↔
        ¬ IsZero (TopCat.Presheaf.stalk (PresheafOfModules.presheaf ℱ.val) x) := by
    change x ∈ abelianSheafSupport F ↔
      ¬ IsZero (TopCat.Presheaf.stalk (TopCat.Sheaf.presheaf F) x)
    exact mem_abelianSheafSupport_iff F x
  rw [hmem]
  rw [AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]
  change Nontrivial ↑(RingedSpace.stalkModuleCat ℱ x) ↔
    ∃ m : ↑(RingedSpace.stalkModuleCat ℱ x), m ≠ 0
  rw [nontrivial_iff_exists_ne (0 : ↑(RingedSpace.stalkModuleCat ℱ x))]

end

end AlgebraicGeometry
