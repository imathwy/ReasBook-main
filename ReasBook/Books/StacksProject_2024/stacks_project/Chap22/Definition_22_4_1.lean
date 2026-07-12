import StacksProject_2024.Chap22.DifferentialGradedModuleBasic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory

section

variable {R : Type u} [CommRing R]

/-- Definition 22.4.1 (1): a right differential graded module over `A` consists of degreewise
`R`-modules `M^n`, a degree-`+1` differential, and homogeneous right actions
`M^p × A^i → M^(p + i)` satisfying the unit, associativity, and graded Leibniz rules. -/
@[stacks 09JI]
structure DifferentialGradedModule (A : CochainDGAlgebra R) where
  /-- The degree-`n` term of the graded module. -/
  X : ℤ → ModuleCat.{v} R
  /-- The degree-raising differential. -/
  d (n : ℤ) : X n →ₗ[R] X (n + 1)
  /-- The homogeneous right action `M^p × A^i → M^(p + i)`. -/
  smul (p i : ℤ) : X p →ₗ[R] A.X i →ₗ[R] X (p + i)
  /-- The differential squares to zero. -/
  d_sq (n : ℤ) (x : X n) : d (n + 1) (d n x) = 0
  /-- The degree-`0` unit of `A` acts by scalar multiplication. -/
  smul_one (r : R) (p : ℤ) (x : X p) :
    smul p 0 x (r • A.one) = cast (rightDGModuleZeroTargetEq p) (r • x)
  /-- Multiplication in `A` acts by successive right multiplication. -/
  smul_mul (p i j : ℤ) (x : X p) (a : A.X i) (b : A.X j) :
    smul p (i + j) x (A.mul i j a b) =
      cast (rightDGModuleMulTargetEq p i j) (smul (p + i) j (smul p i x a) b)
  /-- The differential satisfies the graded Leibniz rule for the right action. -/
  comm_d (p i : ℤ) (x : X p) (a : A.X i) :
    d (p + i) (smul p i x a) =
      cast (rightDGModuleDLeftTargetEq p i) (smul (p + 1) i (d p x) a) +
        (p.negOnePow : R) •
          cast (rightDGModuleDRightTargetEq p i) (smul p (i + 1) x (A.d i a))

namespace DifferentialGradedModule

section

variable {A : CochainDGAlgebra R}

/-- Applying the differential twice is zero on homogeneous elements. -/
theorem d_sq_apply (M : DifferentialGradedModule A) (n : ℤ) (x : M.X n) :
    M.d (n + 1) (M.d n x) = 0 :=
  M.d_sq n x

end

end DifferentialGradedModule

namespace DifferentialGradedModule

section

variable {A : CochainDGAlgebra R}

/-- Definition 22.4.1 (2): a homomorphism of right differential graded `A`-modules is a
degree-preserving family of linear maps commuting with the differential and the right action. -/
@[stacks 09JI]
structure Hom (M N : DifferentialGradedModule A) where
  /-- The degree-`n` component of the morphism. -/
  hom (n : ℤ) : M.X n →ₗ[R] N.X n
  /-- Compatibility with the differential. -/
  comm_d (n : ℤ) (x : M.X n) : hom (n + 1) (M.d n x) = N.d n (hom n x)
  /-- Compatibility with the right action. -/
  comm_smul (p i : ℤ) (x : M.X p) (a : A.X i) :
    hom (p + i) (M.smul p i x a) = N.smul p i (hom p x) a

namespace Hom

/-- The identity morphism of a right differential graded module. -/
def id (M : DifferentialGradedModule A) : Hom M M where
  hom _ := LinearMap.id
  comm_d _ _ := rfl
  comm_smul _ _ _ _ := rfl

/-- Composition of morphisms of right differential graded modules. -/
def comp {L M N : DifferentialGradedModule A} (g : Hom M N) (f : Hom L M) : Hom L N where
  hom n := (g.hom n).comp (f.hom n)
  comm_d n x := by
    calc
      g.hom (n + 1) (f.hom (n + 1) (L.d n x)) = g.hom (n + 1) (M.d n (f.hom n x)) := by
        simpa using congrArg (g.hom (n + 1)) (f.comm_d n x)
      _ = N.d n (g.hom n (f.hom n x)) := by
        simpa using g.comm_d n (f.hom n x)
  comm_smul p i x a := by
    calc
      g.hom (p + i) (f.hom (p + i) (L.smul p i x a)) =
          g.hom (p + i) (M.smul p i (f.hom p x) a) := by
            simpa using congrArg (g.hom (p + i)) (f.comm_smul p i x a)
      _ = N.smul p i (g.hom p (f.hom p x)) a := by
            simpa using g.comm_smul p i (f.hom p x) a

@[simp] theorem id_hom (M : DifferentialGradedModule A) (n : ℤ) :
    (id M).hom n = LinearMap.id :=
  rfl

@[simp] theorem id_apply (M : DifferentialGradedModule A) (n : ℤ) (x : M.X n) :
    (id M).hom n x = x :=
  rfl

@[simp] theorem comp_hom {L M N : DifferentialGradedModule A} (g : Hom M N) (f : Hom L M)
    (n : ℤ) :
    (comp g f).hom n = (g.hom n).comp (f.hom n) :=
  rfl

@[simp] theorem comp_apply {L M N : DifferentialGradedModule A} (g : Hom M N) (f : Hom L M)
    (n : ℤ) (x : L.X n) :
    (comp g f).hom n x = g.hom n (f.hom n x) :=
  rfl

end Hom

/-- Extensionality for morphisms of right differential graded modules. -/
@[ext] theorem hom_ext
    {M N : DifferentialGradedModule A}
    {f g : Hom M N}
    (h : ∀ n : ℤ, ∀ x : M.X n, f.hom n x = g.hom n x) : f = g := by
  have hhom : ∀ n : ℤ, f.hom n = g.hom n := by
    intro n
    ext x
    exact h n x
  cases f with
  | mk homf comm_df comm_smulf =>
      cases g with
      | mk homg comm_dg comm_smulg =>
          dsimp at hhom
          have hhom' : homf = homg := funext hhom
          subst hhom'
          have hcomm_d : comm_df = comm_dg := Subsingleton.elim _ _
          subst hcomm_d
          have hcomm_smul : comm_smulf = comm_smulg := Subsingleton.elim _ _
          subst hcomm_smul
          rfl

instance {M N : DifferentialGradedModule A} :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M.X n → N.X n) where
  coe f := fun n x ↦ f.hom n x

@[simp] theorem coe_apply {M N : DifferentialGradedModule A} (f : Hom M N) (n : ℤ) (x : M.X n) :
    f n x = f.hom n x :=
  rfl

@[simp] theorem map_d_apply {M N : DifferentialGradedModule A} (f : Hom M N) (n : ℤ)
    (x : M.X n) :
    f (n + 1) (M.d n x) = N.d n (f n x) :=
  f.comm_d n x

@[simp] theorem map_smul_apply {M N : DifferentialGradedModule A} (f : Hom M N) (p i : ℤ)
    (x : M.X p) (a : A.X i) :
    f (p + i) (M.smul p i x a) = N.smul p i (f p x) a :=
  f.comm_smul p i x a

/-- Right differential graded modules over `A` form a category. -/
instance instCategory (A : CochainDGAlgebra R) : Category (DifferentialGradedModule A) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp g f
  id_comp := by
    intro M N f
    cases f
    rfl
  comp_id := by
    intro M N f
    cases f
    rfl
  assoc := by
    intro L M N P f g h
    cases h
    cases g
    cases f
    rfl

end

end DifferentialGradedModule

end
