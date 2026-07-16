import StacksProject_2024.stacks_project.Chap22.Definition_22_4_3
import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R
local notation "Mod_(" A ")" => DifferentialGradedModule A

-- Semantic recall note: `lean_leansearch` only returned broad homological-complex owners, so the
-- construction below follows the checked Chapter 22 shift notation `M[k]` from
-- `Definition_22_4_3` and `DifferentialGradedCategory` / `K` from `Lemma_22_26_5`.

/-- Reassociate the target degree for the right `A`-action on a degree-`k` graded morphism. -/
private theorem dgModuleGradedHom_smul_index (n m k : ℤ) :
    (n + k) + m = (n + m) + k := by
  omega

/-- Reassociate the first differential term in the Hom differential to degree `n + (k + 1)`. -/
private theorem dgModuleGradedHom_differential_left_index (n k : ℤ) :
    (n + k) + 1 = n + (k + 1) := by
  omega

/-- Reassociate the second differential term in the Hom differential to degree `n + (k + 1)`. -/
private theorem dgModuleGradedHom_differential_right_index (n k : ℤ) :
    (n + 1) + k = n + (k + 1) := by
  omega

/-- Reassociate the target degree of a composite of homogeneous maps. -/
private theorem dgModuleGradedHom_comp_index (n i j : ℤ) :
    (n + i) + j = n + (i + j) := by
  omega

/-- The degree-`k` Hom object between differential graded `A`-modules: families of degree-`k`
right-`A`-linear maps on the underlying graded modules. -/
def dgModuleGradedHomSubmodule
    (A : DGA) (L M : Mod_(A)) (k : ℤ) :
    Submodule R (∀ n : ℤ, L.X n →ₗ[R] M.X (n + k)) where
  carrier := { f | ∀ n m (x : L.X n) (a : A.X m),
    f (n + m) (L.smul n m x a) =
      cast (congrArg (fun t : ℤ ↦ (M.X t : Type u)) (dgModuleGradedHom_smul_index n m k))
        (M.smul (n + k) m (f n x) a) }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- The degree-`k` graded morphisms between two differential graded `A`-modules. -/
abbrev dgModuleGradedHom
    (A : DGA) (L M : Mod_(A)) (k : ℤ) : Type _ :=
  ↥(dgModuleGradedHomSubmodule A L M k)

instance instCoeFunDgModuleGradedHom
    {A : DGA} {L M : Mod_(A)} {k : ℤ} :
    CoeFun (dgModuleGradedHom A L M k)
      (fun _ ↦ ∀ n : ℤ, L.X n →ₗ[R] M.X (n + k)) where
  coe f := f.1

/-- Coercing a graded morphism recovers its degreewise linear maps. -/
@[simp] theorem dgModuleGradedHom_coe
    {A : DGA} {L M : Mod_(A)} {k : ℤ} (f : dgModuleGradedHom A L M k) :
    ((f : ∀ n : ℤ, L.X n →ₗ[R] M.X (n + k))) = f.1 :=
  rfl

/-- Coercing a graded morphism and evaluating it agrees with the underlying family. -/
@[simp] theorem dgModuleGradedHom_coe_apply
    {A : DGA} {L M : Mod_(A)} {k : ℤ}
    (f : dgModuleGradedHom A L M k) (n : ℤ) (x : L.X n) :
    f n x = f.1 n x :=
  rfl

/-- Two graded morphisms are equal when they agree in every degree on every homogeneous element. -/
@[ext] theorem dgModuleGradedHom_ext
    {A : DGA} {L M : Mod_(A)} {k : ℤ}
    {f g : dgModuleGradedHom A L M k}
    (h : ∀ n : ℤ, ∀ x : L.X n, f n x = g n x) :
    f = g := by
  apply Subtype.ext
  funext n
  ext x
  exact h n x

/-- A graded morphism is right `A`-linear in every bidegree. -/
@[simp] theorem dgModuleGradedHom_comm_smul
    {A : DGA} {L M : Mod_(A)} {k : ℤ}
    (f : dgModuleGradedHom A L M k)
    (n m : ℤ) (x : L.X n) (a : A.X m) :
    f (n + m) (L.smul n m x a) =
      cast (congrArg (fun t : ℤ ↦ (M.X t : Type u)) (dgModuleGradedHom_smul_index n m k))
        (M.smul (n + k) m (f n x) a) :=
  f.2 n m x a

/-- The differential on the graded Hom object of differential graded modules. -/
def dgModuleGradedHomDifferential
    {A : DGA} {L M : Mod_(A)} (k : ℤ) :
    dgModuleGradedHom A L M k → dgModuleGradedHom A L M (k + 1) :=
  fun f ↦
    ⟨fun n ↦
      castLinearMap
          (congrArg M.X (dgModuleGradedHom_differential_left_index n k))
          ((M.d (n + k)).comp (f n)) -
        (k.negOnePow : R) •
          castLinearMap
            (congrArg M.X (dgModuleGradedHom_differential_right_index n k))
            ((f (n + 1)).comp (L.d n)),
      sorry⟩

/-- On degree `n`, the Hom differential is `d_M ∘ f - (-1)^k f ∘ d_L` after reindexing. -/
@[simp] theorem dgModuleGradedHomDifferential_apply
    {A : DGA} {L M : Mod_(A)} (k : ℤ)
    (f : dgModuleGradedHom A L M k) (n : ℤ) :
    dgModuleGradedHomDifferential k f n =
      castLinearMap
        (congrArg M.X (dgModuleGradedHom_differential_left_index n k))
        ((M.d (n + k)).comp (f n)) -
          (k.negOnePow : R) •
            castLinearMap
              (congrArg M.X (dgModuleGradedHom_differential_right_index n k))
              ((f (n + 1)).comp (L.d n)) :=
  rfl

/-- The degree-`0` identity element in the graded Hom object of differential graded modules. -/
private def dgModuleGradedHomId
    {A : DGA} (L : Mod_(A)) :
    dgModuleGradedHom A L L 0 :=
  ⟨fun n ↦
      castLinearMap
        (congrArg L.X (add_zero n).symm)
        (LinearMap.id),
    sorry⟩

/-- Graded composition of homogeneous right-`A`-linear maps between differential graded modules.
-/
private def dgModuleGradedHomComp
    {A : DGA} {K L M : Mod_(A)} {i j : ℤ}
    (g : dgModuleGradedHom A L M j) (f : dgModuleGradedHom A K L i) :
    dgModuleGradedHom A K M (i + j) :=
  ⟨fun n ↦
      castLinearMap
        (congrArg M.X (dgModuleGradedHom_comp_index n i j))
        ((g (n + i)).comp (f n)),
    sorry⟩

/-- Example 22.26.8 (Differential graded category of differential graded modules): for a
differential graded algebra `A`, the differential graded `A`-modules form a differential graded
category over `R`. The degree-`k` Hom object is the graded `R`-module of homogeneous right-`A`-
linear maps of degree `k`, the differential is `d_M ∘ f - (-1)^k f ∘ d_L`, and composition is
the usual graded composition. Its category of closed degree-`0` morphisms is `Comp R
(DifferentialGradedModule A)`, and its homotopy category is `K R (DifferentialGradedModule A)`.
-/
@[reducible] instance dgModulesDifferentialGradedCategory
    (A : DGA) :
    DifferentialGradedCategory R (Mod_(A)) where
  Hom L M k := dgModuleGradedHom A L M k
  homAddCommGroup := fun _ _ _ ↦ inferInstance
  homModule := fun _ _ _ ↦ inferInstance
  d := fun k f ↦ dgModuleGradedHomDifferential k f
  id := dgModuleGradedHomId
  comp := fun {K L M} {i j} g f ↦ dgModuleGradedHomComp g f
  d_sq := sorry
  d_id := sorry
  id_comp_hom := sorry
  comp_id_hom := sorry
  comp_assoc := sorry
  comp_add_left := sorry
  comp_add_right := sorry
  comp_smul_left := sorry
  comp_smul_right := sorry
  d_add := sorry
  d_smul := sorry
  d_comp := sorry

/-- The Hom objects in the differential graded category of differential graded modules are the
graded Hom objects of homogeneous right-`A`-linear maps. -/
@[simp] theorem dgModulesDifferentialGradedCategory_hom
    (A : DGA) (L M : Mod_(A)) (k : ℤ) :
    (L ⟶[k] M) = dgModuleGradedHom A L M k :=
  rfl

/-- The closed degree-`k` homogeneous maps in the Hom object of differential graded modules. -/
abbrev dgModuleClosedHom
    (A : DGA) (L M : Mod_(A)) (k : ℤ) : Type _ :=
  { f : dgModuleGradedHom A L M k | dgModuleGradedHomDifferential k f = 0 }

/-- A closed degree-`k` homogeneous map is closed by definition. -/
@[simp] theorem dgModuleClosedHom_closed
    {A : DGA} {L M : Mod_(A)} {k : ℤ}
    (f : dgModuleClosedHom A L M k) :
    dgModuleGradedHomDifferential k f.1 = 0 :=
  f.2

/-- Closed degree-`k` homogeneous maps are exactly morphisms of differential graded modules into
the shift by `k`. -/
def dgModuleClosedHomEquivShiftHom
    (A : DGA) (L M : Mod_(A)) (k : ℤ) :
    dgModuleClosedHom A L M k ≃ (L ⟶ M[k]) where
  toFun f :=
    { hom := fun n ↦
        castLinearMap
          (DifferentialGradedModule.shift_X M k n).symm
          (f.1 n)
      comm_d := sorry
      comm_smul := sorry }
  invFun g :=
    ⟨⟨fun n ↦
          castLinearMap
            (DifferentialGradedModule.shift_X M k n)
            (g.hom n),
        sorry⟩,
      sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- On degree `n`, `dgModuleClosedHomEquivShiftHom` is the canonical reindexing into the shift. -/
@[simp] theorem dgModuleClosedHomEquivShiftHom_hom
    (A : DGA) (L M : Mod_(A)) (k : ℤ)
    (f : dgModuleClosedHom A L M k)
    (n : ℤ) :
    (dgModuleClosedHomEquivShiftHom A L M k f).hom n =
      castLinearMap (DifferentialGradedModule.shift_X M k n).symm (f.1 n) :=
  rfl

/-- The inverse of `dgModuleClosedHomEquivShiftHom` is the degreewise map of a shifted morphism. -/
@[simp] theorem dgModuleClosedHomEquivShiftHom_symm_apply
    (A : DGA) (L M : Mod_(A)) (k : ℤ)
    (g : L ⟶ M[k]) (n : ℤ) :
    (((dgModuleClosedHomEquivShiftHom A L M k).symm g).1 : dgModuleGradedHom A L M k) n =
      castLinearMap (DifferentialGradedModule.shift_X M k n) (g.hom n) :=
  rfl

end
