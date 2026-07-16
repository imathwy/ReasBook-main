import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import StacksProject_2024.stacks_project.Chap22.Definition_22_11_1

open CategoryTheory
open CochainDGAlgebra

universe u

/- Source/core/bridge triage:
- source-facing: left differential graded `A`-modules and right differential graded
  `A.opposite`-modules;
- core/canonical: downstream Chapter 22 files reuse the left-owner
  `LeftDifferentialGradedModule` directly;
- bridge/view: right modules are expressed through the opposite-algebra view
  `RightDifferentialGradedModule`, and Lemma 22.11.2 is the induced equivalence coming from the
  canonical identification `A.opposite.opposite = A`. -/

section

variable {R : Type u} [CommRing R]

local notation "DGA[" R "]" => CochainDGAlgebra R

/-- The degree-`0` part of a left differential graded module action on `M^p` lands in `M^(0 + p)`.
-/
theorem leftDGModuleZeroTargetEq {M : ℤ → ModuleCat.{u} R} (p : ℤ) :
    (M p : Type u) = M (0 + p) := by
  rw [zero_add]

/-- Composing degree-`i` and degree-`j` left action maps lands in degree `((i + j) + p)`. -/
theorem leftDGModuleMulTargetEq {M : ℤ → ModuleCat.{u} R} (p i j : ℤ) :
    (M (i + (j + p)) : Type u) = M ((i + j) + p) := by
  rw [add_assoc]

/-- In the left Leibniz rule, applying `d_M` after a degree-`m` action lands in degree
`((m + 1) + p)`. -/
theorem leftDGModuleDLeftTargetEq {M : ℤ → ModuleCat.{u} R} (p m : ℤ) :
    (M ((m + p) + 1) : Type u) = M ((m + 1) + p) := by
  rw [add_assoc, add_comm p 1, ← add_assoc]

/-- In the left Leibniz rule, acting after `d_M` also lands in degree `((m + 1) + p)`. -/
theorem leftDGModuleDRightTargetEq {M : ℤ → ModuleCat.{u} R} (p m : ℤ) :
    (M (m + (p + 1)) : Type u) = M ((m + 1) + p) := by
  rw [add_assoc, add_comm p 1, ← add_assoc]

/-- A left differential graded module over a fixed differential graded algebra, recorded by its
degreewise `R`-modules, differential, and homogeneous left action. -/
structure LeftDifferentialGradedModule (A : DGA[R]) where
  /-- The degree-`n` term of the graded module. -/
  X : ℤ → ModuleCat.{u} R
  /-- The degree-raising differential on the graded module. -/
  d : ∀ n : ℤ, X n →ₗ[R] X (n + 1)
  /-- The left action `Aⁿ × Mᵐ → Mⁿ⁺ᵐ`. -/
  smul : ∀ n m : ℤ, A.X n →ₗ[R] X m →ₗ[R] X (n + m)
  /-- The degree-`0` unit of `A` acts by scalar multiplication. -/
  smul_one :
    ∀ (r : R) (p : ℤ) (x : X p),
      smul 0 p (r • A.one) x = cast (leftDGModuleZeroTargetEq p) (r • x)
  /-- Multiplication in `A` acts by successive left multiplication. -/
  smul_mul :
    ∀ (i j p : ℤ) (a : A.X i) (b : A.X j) (x : X p),
      smul (i + j) p (A.mul i j a b) x =
        cast (leftDGModuleMulTargetEq p i j) (smul i (j + p) a (smul j p b x))
  /-- The differential satisfies the graded Leibniz rule for the left action. -/
  comm_d :
    ∀ (i p : ℤ) (a : A.X i) (x : X p),
      smul (i + 1) p (A.d i a) x =
        cast (leftDGModuleDLeftTargetEq p i) (d (i + p) (smul i p a x)) -
          (((-1 : R) ^ Int.natAbs i) : R) •
            cast (leftDGModuleDRightTargetEq p i) (smul i (p + 1) a (d p x))

namespace LeftDifferentialGradedModule

variable {A : DGA[R]}

/-- Morphisms of left differential graded modules are degree-preserving maps commuting with the
differential and the left action. -/
structure Hom (M N : LeftDifferentialGradedModule A) where
  /-- The degree-`n` component of the morphism. -/
  hom : ∀ n : ℤ, M.X n →ₗ[R] N.X n
  /-- Compatibility with the differential. -/
  comm_d : ∀ (n : ℤ) (x : M.X n), hom (n + 1) (M.d n x) = N.d n (hom n x)
  /-- Compatibility with the left action. -/
  comm_smul :
    ∀ (n m : ℤ) (a : A.X n) (x : M.X m),
      hom (n + m) (M.smul n m a x) = N.smul n m a (hom m x)

/-- The identity morphism of a left differential graded module. -/
def id (M : LeftDifferentialGradedModule A) : Hom M M where
  hom _ := LinearMap.id
  comm_d _ _ := rfl
  comm_smul _ _ _ _ := rfl

/-- Composition of morphisms of left differential graded modules. -/
def comp {L M N : LeftDifferentialGradedModule A} (g : Hom M N) (f : Hom L M) : Hom L N where
  hom n := (g.hom n).comp (f.hom n)
  comm_d n x := by
    calc
      g.hom (n + 1) (f.hom (n + 1) (L.d n x)) = g.hom (n + 1) (M.d n (f.hom n x)) := by
        rw [f.comm_d]
      _ = N.d n (g.hom n (f.hom n x)) := by
        rw [g.comm_d]
  comm_smul n m a x := by
    calc
      g.hom (n + m) (f.hom (n + m) (L.smul n m a x)) =
          g.hom (n + m) (M.smul n m a (f.hom m x)) := by
            rw [f.comm_smul]
      _ = N.smul n m a (g.hom m (f.hom m x)) := by
            rw [g.comm_smul]

/-- Extensionality for morphisms of left differential graded modules. -/
theorem hom_ext {M N : LeftDifferentialGradedModule A} {f g : Hom M N}
    (h : ∀ n : ℤ, f.hom n = g.hom n) : f = g := by
  cases f with
  | mk homf comm_df comm_smulf =>
      cases g with
      | mk homg comm_dg comm_smulg =>
          dsimp at h
          have hhom : homf = homg := funext h
          subst hhom
          have hcomm_d : comm_df = comm_dg := Subsingleton.elim _ _
          subst hcomm_d
          have hcomm_smul : comm_smulf = comm_smulg := Subsingleton.elim _ _
          subst hcomm_smul
          rfl

/-- The category law `𝟙_M ≫ f = f` for left differential graded module morphisms. -/
theorem id_comp {M N : LeftDifferentialGradedModule A} (f : Hom M N) :
    comp (id N) f = f := by
  cases f
  rfl

/-- The category law `f ≫ 𝟙_N = f` for left differential graded module morphisms. -/
theorem comp_id {M N : LeftDifferentialGradedModule A} (f : Hom M N) :
    comp f (id M) = f := by
  cases f
  rfl

/-- Associativity of composition for left differential graded module morphisms. -/
theorem assoc {L M N P : LeftDifferentialGradedModule A}
    (h : Hom N P) (g : Hom M N) (f : Hom L M) :
    comp h (comp g f) = comp (comp h g) f := by
  cases h
  cases g
  cases f
  rfl

/-- Left differential graded modules over `A` form a category. -/
instance : Category (LeftDifferentialGradedModule A) where
  Hom M N := Hom M N
  id M := id M
  comp f g := comp g f
  id_comp := id_comp
  comp_id := comp_id
  assoc f g h := assoc h g f

end LeftDifferentialGradedModule

/-- A right differential graded module over `A` is the chapter's left differential graded module
owner applied to the opposite differential graded algebra `A.opposite`. -/
abbrev RightDifferentialGradedModule (A : DGA[R]) :=
  LeftDifferentialGradedModule A.opposite

private theorem dgaCastAddCommCancel {A : DGA[R]} (i j : ℤ) (x : A.X (i + j)) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm j i))
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm i j)) x) = x := by
  rw [cast_cast]
  simp

private theorem dgaCastSmul {A : DGA[R]} {i j : ℤ} (h : i = j) (r : R) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) x := by
  cases h
  rfl

private theorem opposite_opposite_mul_apply (A : DGA[R]) (i j : ℤ) (a : A.X i) (b : A.X j) :
    (A.opposite.opposite).mul i j a b = A.mul i j a b := by
  rw [opposite_mul_apply, opposite_mul_apply]
  change
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm j i))
        (oppositeSign R i j •
          cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm i j))
            (oppositeSign R j i • A.mul i j a b)) =
      A.mul i j a b
  rw [dgaCastSmul (add_comm j i)]
  rw [dgaCastAddCommCancel i j (oppositeSign R j i • A.mul i j a b)]
  rw [oppositeSign_comm i j]
  exact oppositeSign_smul_oppositeSign j i (A.mul i j a b)

namespace LeftDifferentialGradedModule

private def toRightOppositeObj {A : DGA[R]} (M : LeftDifferentialGradedModule A) :
    RightDifferentialGradedModule A.opposite where
  X := M.X
  d := M.d
  smul := M.smul
  smul_one := by
    intro r p x
    exact M.smul_one r p x
  smul_mul := by
    intro i j p a b x
    rw [opposite_opposite_mul_apply A i j a b]
    exact M.smul_mul i j p a b x
  comm_d := by
    intro i p a x
    simpa using M.comm_d i p a x

private def toLeftOfRightOppositeObj {A : DGA[R]} (M : RightDifferentialGradedModule A.opposite) :
    LeftDifferentialGradedModule A where
  X := M.X
  d := M.d
  smul := M.smul
  smul_one := by
    intro r p x
    exact M.smul_one r p x
  smul_mul := by
    intro i j p a b x
    have h := M.smul_mul i j p a b x
    rwa [opposite_opposite_mul_apply A i j a b] at h
  comm_d := by
    intro i p a x
    simpa using M.comm_d i p a x

private def toRightOppositeHom {A : DGA[R]} {M N : LeftDifferentialGradedModule A}
    (f : Hom M N) : Hom (toRightOppositeObj M) (toRightOppositeObj N) where
  hom := f.hom
  comm_d := f.comm_d
  comm_smul := by
    intro n m a x
    simpa using f.comm_smul n m a x

private def toLeftOfRightOppositeHom {A : DGA[R]}
    {M N : RightDifferentialGradedModule A.opposite} (f : Hom M N) :
    Hom (toLeftOfRightOppositeObj M) (toLeftOfRightOppositeObj N) where
  hom := f.hom
  comm_d := f.comm_d
  comm_smul := by
    intro n m a x
    simpa using f.comm_smul n m a x

private def toRightOppositeUnitIso {A : DGA[R]} (M : LeftDifferentialGradedModule A) :
    M ≅ toLeftOfRightOppositeObj (toRightOppositeObj M) where
  hom :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := by
        intro n x
        rfl
      comm_smul := by
        intro n m a x
        rfl }
  inv :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := by
        intro n x
        rfl
      comm_smul := by
        intro n m a x
        rfl }
  hom_inv_id := by
    apply hom_ext
    intro n
    rfl
  inv_hom_id := by
    apply hom_ext
    intro n
    rfl

private def toLeftOfRightOppositeCounitIso {A : DGA[R]}
    (M : RightDifferentialGradedModule A.opposite) :
    toRightOppositeObj (toLeftOfRightOppositeObj M) ≅ M where
  hom :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := by
        intro n x
        rfl
      comm_smul := by
        intro n m a x
        rfl }
  inv :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := by
        intro n x
        rfl
      comm_smul := by
        intro n m a x
        rfl }
  hom_inv_id := by
    apply hom_ext
    intro n
    rfl
  inv_hom_id := by
    apply hom_ext
    intro n
    rfl

end LeftDifferentialGradedModule

/-- Lemma 22.11.2: in the chapter's cochain-DGA owner, the source-facing passage between left
differential graded `A`-modules and right differential graded `A.opposite`-modules is the
equivalence induced by the canonical identification `A.opposite.opposite = A`. -/
@[stacks 0FQ0]
def leftDGModuleOppositeEquivalence (A : DGA[R]) :
    LeftDifferentialGradedModule A ≌ RightDifferentialGradedModule A.opposite :=
  { functor :=
      { obj := LeftDifferentialGradedModule.toRightOppositeObj
        map := LeftDifferentialGradedModule.toRightOppositeHom
        map_id := by
          intro M
          apply LeftDifferentialGradedModule.hom_ext
          intro n
          rfl
        map_comp := by
          intro M N P f g
          apply LeftDifferentialGradedModule.hom_ext
          intro n
          rfl }
    inverse :=
      { obj := LeftDifferentialGradedModule.toLeftOfRightOppositeObj
        map := LeftDifferentialGradedModule.toLeftOfRightOppositeHom
        map_id := by
          intro M
          apply LeftDifferentialGradedModule.hom_ext
          intro n
          rfl
        map_comp := by
          intro M N P f g
          apply LeftDifferentialGradedModule.hom_ext
          intro n
          rfl }
    unitIso :=
      NatIso.ofComponents
        LeftDifferentialGradedModule.toRightOppositeUnitIso
        (by
          intro M N f
          apply LeftDifferentialGradedModule.hom_ext
          intro n
          rfl)
    counitIso :=
      NatIso.ofComponents
        LeftDifferentialGradedModule.toLeftOfRightOppositeCounitIso
        (by
          intro M N f
          apply LeftDifferentialGradedModule.hom_ext
          intro n
          rfl) }

/-- Present a left differential graded `A`-module as a right differential graded
`A.opposite`-module through the opposite-algebra owner. -/
abbrev leftDGModuleToRightOppositeFunctor (A : DGA[R]) :
    LeftDifferentialGradedModule A ⥤ RightDifferentialGradedModule A.opposite :=
  (leftDGModuleOppositeEquivalence A).functor

/-- Present a right differential graded `A.opposite`-module as a left differential graded
`A`-module through the opposite-algebra owner. -/
abbrev rightOppositeDGModuleToLeftFunctor (A : DGA[R]) :
    RightDifferentialGradedModule A.opposite ⥤ LeftDifferentialGradedModule A :=
  (leftDGModuleOppositeEquivalence A).inverse

/-- The source-facing passage to right differential graded `A.opposite`-modules keeps the
underlying graded `R`-module unchanged. -/
@[simp] theorem leftDGModuleToRightOppositeFunctor_obj_X {A : DGA[R]}
    (M : LeftDifferentialGradedModule A) (n : ℤ) :
    ((leftDGModuleToRightOppositeFunctor A).obj M).X n = M.X n :=
  rfl

/-- The source-facing passage to right differential graded `A.opposite`-modules keeps the
underlying differential unchanged. -/
@[simp] theorem leftDGModuleToRightOppositeFunctor_obj_d {A : DGA[R]}
    (M : LeftDifferentialGradedModule A) (n : ℤ) :
    ((leftDGModuleToRightOppositeFunctor A).obj M).d n = M.d n :=
  rfl

/-- The source-facing passage to right differential graded `A.opposite`-modules keeps the
underlying homogeneous action map unchanged. -/
@[simp] theorem leftDGModuleToRightOppositeFunctor_obj_smul {A : DGA[R]}
    (M : LeftDifferentialGradedModule A) (n m : ℤ) :
    ((leftDGModuleToRightOppositeFunctor A).obj M).smul n m = M.smul n m :=
  rfl

/-- The source-facing passage to right differential graded `A.opposite`-modules acts as the given
degreewise map on morphisms. -/
@[simp] theorem leftDGModuleToRightOppositeFunctor_map_hom {A : DGA[R]}
    {M N : LeftDifferentialGradedModule A} (f : M ⟶ N) (n : ℤ) :
    ((leftDGModuleToRightOppositeFunctor A).map f).hom n = f.hom n :=
  rfl

/-- The passage back to left differential graded `A`-modules keeps the underlying graded
`R`-module unchanged. -/
@[simp] theorem rightOppositeDGModuleToLeftFunctor_obj_X {A : DGA[R]}
    (M : RightDifferentialGradedModule A.opposite) (n : ℤ) :
    ((rightOppositeDGModuleToLeftFunctor A).obj M).X n = M.X n :=
  rfl

/-- The passage back to left differential graded `A`-modules keeps the underlying differential
unchanged. -/
@[simp] theorem rightOppositeDGModuleToLeftFunctor_obj_d {A : DGA[R]}
    (M : RightDifferentialGradedModule A.opposite) (n : ℤ) :
    ((rightOppositeDGModuleToLeftFunctor A).obj M).d n = M.d n :=
  rfl

/-- The passage back to left differential graded `A`-modules keeps the underlying homogeneous
action map unchanged. -/
@[simp] theorem rightOppositeDGModuleToLeftFunctor_obj_smul {A : DGA[R]}
    (M : RightDifferentialGradedModule A.opposite) (n m : ℤ) :
    ((rightOppositeDGModuleToLeftFunctor A).obj M).smul n m = M.smul n m :=
  rfl

/-- The passage back to left differential graded `A`-modules acts as the given degreewise map on
morphisms. -/
@[simp] theorem rightOppositeDGModuleToLeftFunctor_map_hom {A : DGA[R]}
    {M N : RightDifferentialGradedModule A.opposite} (f : M ⟶ N) (n : ℤ) :
    ((rightOppositeDGModuleToLeftFunctor A).map f).hom n = f.hom n :=
  rfl

/-- The forward functor of Lemma 22.11.2 is an equivalence. -/
instance leftDGModuleToRightOppositeFunctor_isEquivalence (A : DGA[R]) :
    (leftDGModuleToRightOppositeFunctor A).IsEquivalence :=
  (leftDGModuleOppositeEquivalence A).isEquivalence_functor

/-- The inverse functor of Lemma 22.11.2 is an equivalence. -/
instance rightOppositeDGModuleToLeftFunctor_isEquivalence (A : DGA[R]) :
    (rightOppositeDGModuleToLeftFunctor A).IsEquivalence :=
  (leftDGModuleOppositeEquivalence A).symm.isEquivalence_functor

/-- The forward functor of `leftDGModuleOppositeEquivalence` is the named source-facing passage to
right differential graded `A.opposite`-modules. -/
@[simp] theorem leftDGModuleOppositeEquivalence_functor (A : DGA[R]) :
    (leftDGModuleOppositeEquivalence A).functor = leftDGModuleToRightOppositeFunctor A :=
  rfl

/-- The inverse functor of `leftDGModuleOppositeEquivalence` is the named passage back to left
differential graded `A`-modules. -/
@[simp] theorem leftDGModuleOppositeEquivalence_inverse (A : DGA[R]) :
    (leftDGModuleOppositeEquivalence A).inverse = rightOppositeDGModuleToLeftFunctor A :=
  rfl

end
