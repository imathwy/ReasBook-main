import StacksProject_2024.Chap22.Definition_22_11_1
import StacksProject_2024.Chap22.Lemma_22_13_3
import StacksProject_2024.Chap22.Definition_22_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {𝒜 : Type v} [D : DifferentialGradedCategory.{u, v, u} R 𝒜]

open scoped DifferentialGradedCategory

local notation "DGA" => CochainDGAlgebra R

-- Source/core/bridge triage:
-- * source-facing: the endomorphism DGA `Hom_𝒜(x, x)` and the represented right DG module
--   `Hom_𝒜(x, y)` with right action by precomposition;
-- * core/canonical: the existing Chapter 22 owners `CochainDGAlgebra` and
--   `DifferentialGradedModule.WithFixedUnderlying` built on `RightDifferentialGradedModule`;
-- * bridge/view: the ordinary functor on closed degree-`0` morphisms
--   `Comp R 𝒜 ⥤ RightDifferentialGradedModule (representedEndomorphismDGA x)`.

private theorem ring_negOnePow_mul_self (n : ℤ) :
    ((n.negOnePow : R) * (n.negOnePow : R)) = (1 : R) := by
  rcases Int.even_or_odd n with hEven | hOdd
  · rw [Int.negOnePow_even _ hEven]
    norm_num
  · rw [Int.negOnePow_odd _ hOdd]
    norm_num

private theorem representedEndomorphismMul_assoc_left_index (i j k : ℤ) :
    k + (j + i) = i + (j + k) := by
  omega

private theorem representedEndomorphismMul_assoc_right_index (i j k : ℤ) :
    (k + j) + i = i + (j + k) := by
  omega

private theorem representedEndomorphismMul_assoc_left_comm_index (i j k : ℤ) :
    k + (j + i) = k + (i + j) := by
  simpa [add_assoc] using congrArg (fun t ↦ k + t) (Int.add_comm j i)

private theorem representedEndomorphismMul_assoc_right_comm_index (i j k : ℤ) :
    (k + j) + i = (j + k) + i := by
  simpa [add_assoc] using congrArg (fun t ↦ t + i) (Int.add_comm k j)

/-- The degree-`n` piece of the represented Hom construction `Hom_𝒜(x, y)`. -/
abbrev representedHomFamily (x y : 𝒜) (n : ℤ) : ModuleCat R :=
  ModuleCat.of R (x ⟶[n] y)

/-- The differential on the represented Hom construction, viewed as a linear map on homogeneous
pieces. -/
def representedHomDLinear (x y : 𝒜) (n : ℤ) :
    representedHomFamily x y n →ₗ[R] representedHomFamily x y (n + 1) :=
    { toFun := D.d n
      map_add' := D.d_add n
      map_smul' := D.d_smul n }

/-- The differential on the represented Hom construction is the differential of the ambient DG
category. -/
abbrev representedHomD (x y : 𝒜) (n : ℤ) :
    representedHomFamily x y n ⟶ representedHomFamily x y (n + 1) :=
  ModuleCat.ofHom (representedHomDLinear x y n)

/-- The represented Hom differential squares to zero. -/
theorem representedHomD_sq (x y : 𝒜) (n : ℤ) :
    representedHomD x y n ≫ representedHomD x y (n + 1) = 0 := by
  ext f
  exact D.d_sq n f

/-- The cochain complex underlying the endomorphism DGA attached to `x`. -/
def representedEndomorphismComplex (x : 𝒜) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of
    (representedHomFamily x x)
    (representedHomD x x)
    (representedHomD_sq x x)

private def representedEndomorphismMul (x : 𝒜) (n m : ℤ) :
    (x ⟶[n] x) →ₗ[R] (x ⟶[m] x) →ₗ[R] (x ⟶[n + m] x) :=
  { toFun := fun a ↦
      { toFun := fun b ↦ castHom (Int.add_comm m n) (D.comp a b)
        map_add' := by
          intro b₁ b₂
          calc
            castHom (Int.add_comm m n) (D.comp a (b₁ + b₂)) =
                castHom (Int.add_comm m n) (D.comp a b₁ + D.comp a b₂) := by
                  simpa using congrArg (castHom (Int.add_comm m n)) (D.comp_add_right a b₁ b₂)
            _ =
                castHom (Int.add_comm m n) (D.comp a b₁) +
                  castHom (Int.add_comm m n) (D.comp a b₂) := by
                  exact castHom_add (Int.add_comm m n) (D.comp a b₁) (D.comp a b₂)
        map_smul' := by
          intro r b
          calc
            castHom (Int.add_comm m n) (D.comp a (r • b)) =
                castHom (Int.add_comm m n) (r • D.comp a b) := by
                  simpa using congrArg (castHom (Int.add_comm m n)) (D.comp_smul_right r a b)
            _ = r • castHom (Int.add_comm m n) (D.comp a b) := by
                  exact castHom_smul (Int.add_comm m n) r (D.comp a b) }
    map_add' := by
      intro a₁ a₂
      ext b
      calc
        castHom (Int.add_comm m n) (D.comp (a₁ + a₂) b) =
            castHom (Int.add_comm m n) (D.comp a₁ b + D.comp a₂ b) := by
              simpa using congrArg (castHom (Int.add_comm m n)) (D.comp_add_left a₁ a₂ b)
        _ =
            castHom (Int.add_comm m n) (D.comp a₁ b) +
              castHom (Int.add_comm m n) (D.comp a₂ b) := by
              exact castHom_add (Int.add_comm m n) (D.comp a₁ b) (D.comp a₂ b)
    map_smul' := by
      intro r a
      ext b
      calc
        castHom (Int.add_comm m n) (D.comp (r • a) b) =
            castHom (Int.add_comm m n) (r • D.comp a b) := by
              simpa using congrArg (castHom (Int.add_comm m n)) (D.comp_smul_left r a b)
        _ = r • castHom (Int.add_comm m n) (D.comp a b) := by
              exact castHom_smul (Int.add_comm m n) r (D.comp a b) }

@[simp] private theorem representedEndomorphismMul_apply (x : 𝒜) (n m : ℤ)
    (a : representedHomFamily x x n) (b : representedHomFamily x x m) :
    representedEndomorphismMul x n m a b = castHom (Int.add_comm m n) (D.comp a b) :=
  rfl

private theorem representedEndomorphismMul_assoc_left (x : 𝒜) (i j k : ℤ)
    (a : representedHomFamily x x i) (b : representedHomFamily x x j)
    (c : representedHomFamily x x k) :
    castHom (add_assoc i j k)
        (representedEndomorphismMul x (i + j) k (representedEndomorphismMul x i j a b) c) =
      castHom (representedEndomorphismMul_assoc_left_index i j k) (D.comp (D.comp a b) c) := by
  sorry

private theorem representedEndomorphismMul_assoc_right (x : 𝒜) (i j k : ℤ)
    (a : representedHomFamily x x i) (b : representedHomFamily x x j)
    (c : representedHomFamily x x k) :
    representedEndomorphismMul x i (j + k) a (representedEndomorphismMul x j k b c) =
      castHom (representedEndomorphismMul_assoc_right_index i j k) (D.comp a (D.comp b c)) := by
  sorry

private theorem representedEndomorphismMul_left_unit (x : 𝒜) (n : ℤ)
    (a : representedHomFamily x x n) :
    castHom (zero_add n) (representedEndomorphismMul x 0 n (D.id x) a) = a := by
  calc
    castHom (zero_add n) (representedEndomorphismMul x 0 n (D.id x) a) =
        castHom (zero_add n) (castHom (Int.add_comm n 0) (D.comp (D.id x) a)) := by
          rfl
    _ = castHom ((Int.add_comm n 0).trans (zero_add n)) (D.comp (D.id x) a) := by
          exact castHom_trans (Int.add_comm n 0) (zero_add n) (D.comp (D.id x) a)
    _ = castHom (add_zero n) (D.comp (D.id x) a) := by
          exact castHom_congr ((Int.add_comm n 0).trans (zero_add n)) (add_zero n)
            (D.comp (D.id x) a)
    _ = a := D.id_comp_hom a

private theorem representedEndomorphismMul_right_unit (x : 𝒜) (n : ℤ)
    (a : representedHomFamily x x n) :
    castHom (add_zero n) (representedEndomorphismMul x n 0 a (D.id x)) = a := by
  calc
    castHom (add_zero n) (representedEndomorphismMul x n 0 a (D.id x)) =
        castHom (add_zero n) (castHom (Int.add_comm 0 n) (D.comp a (D.id x))) := by
          rfl
    _ = castHom ((Int.add_comm 0 n).trans (add_zero n)) (D.comp a (D.id x)) := by
          exact castHom_trans (Int.add_comm 0 n) (add_zero n) (D.comp a (D.id x))
    _ = castHom (zero_add n) (D.comp a (D.id x)) := by
          exact castHom_congr ((Int.add_comm 0 n).trans (add_zero n)) (zero_add n)
            (D.comp a (D.id x))
    _ = a := D.comp_id_hom a

/-- Lemma 22.26.10, endomorphism-DGA part: the graded endomorphism object `Hom_𝒜(x, x)` of an
object `x` in a differential graded category carries the canonical cochain DGA structure coming
from composition, the identity, and the DG-category differential. -/
@[stacks 09LE]
def representedEndomorphismDGA (x : 𝒜) : DGA where
  toCochainComplex := representedEndomorphismComplex x
  mul := representedEndomorphismMul x
  one := by
    simpa [representedEndomorphismComplex, representedHomFamily] using (D.id x)
  mul_assoc := by
    sorry
  one_mul := by
    intro n a
    simpa [representedEndomorphismComplex, representedHomFamily, cast_eq_castHom] using
      representedEndomorphismMul_left_unit x n a
  mul_one := by
    intro n a
    simpa [representedEndomorphismComplex, representedHomFamily, cast_eq_castHom] using
      representedEndomorphismMul_right_unit x n a
  leibniz := by
    sorry

/-- The underlying left action of `(representedEndomorphismDGA x).opposite` corresponding to the
source-facing right action by precomposition. -/
def representedHomUnderlyingLeftAction (x y : 𝒜) (q p : ℤ) :
    representedHomFamily x x q →ₗ[R] representedHomFamily x y p →ₗ[R]
      representedHomFamily x y (q + p) :=
  { toFun := fun a ↦
      { toFun := fun f ↦
          (CochainDGAlgebra.oppositeSign R q p) • D.comp f a
        map_add' := by
          intro f₁ f₂
          simp [D.comp_add_left, smul_add]
        map_smul' := by
          intro r f
          simp [D.comp_smul_left, smul_smul, mul_comm] }
    map_add' := by
      intro a₁ a₂
      ext f
      simp [D.comp_add_right, smul_add]
    map_smul' := by
      intro r a
      ext f
      simp [D.comp_smul_right, smul_smul, mul_comm] }

@[simp] theorem representedHomUnderlyingLeftAction_apply (x y : 𝒜) (q p : ℤ)
    (a : representedHomFamily x x q) (f : representedHomFamily x y p) :
    representedHomUnderlyingLeftAction x y q p a f =
      (CochainDGAlgebra.oppositeSign R q p) • D.comp f a :=
  rfl

/-- The fixed-underlying right module structure on `Hom_𝒜(x, y)` coming from precomposition. -/
def representedHomRightDGModuleWithFixedUnderlying (x y : 𝒜) :
    DifferentialGradedModule.WithFixedUnderlying (representedEndomorphismDGA x)
      (representedHomFamily x y) (representedHomDLinear x y) where
  toRightDifferentialGradedModule :=
    { X := representedHomFamily x y
      d := representedHomDLinear x y
      smul := representedHomUnderlyingLeftAction x y
      smul_one := by
        sorry
      smul_mul := by
        sorry
      comm_d := by
        sorry
    }
  X_eq := rfl
  d_eq := rfl

/-- The source-facing right action on `Hom_𝒜(x, y)` in `representedHomRightDGModule x y` is
ordinary precomposition. The statement is spelled on the fixed-underlying bridge so the
homogeneous source and target families remain explicit. -/
@[simp] theorem representedHomRightDGModule_smul (x y : 𝒜)
    (p q : ℤ) (f : representedHomFamily x y p) (a : representedHomFamily x x q) :
    (representedHomRightDGModuleWithFixedUnderlying x y).smul p q f a =
      castHom (add_comm q p) (D.comp f a) := by
  sorry

/-- Lemma 22.26.10, module part: for each object `y`, the represented graded Hom object
`Hom_𝒜(x, y)` carries the canonical right differential graded module structure over
`representedEndomorphismDGA x`, with the fixed-underlying source-facing bridge still available as
`representedHomRightDGModuleWithFixedUnderlying x y`. -/
@[stacks 09LE]
def representedHomRightDGModule (x y : 𝒜) :
    RightDifferentialGradedModule (representedEndomorphismDGA x) :=
  (representedHomRightDGModuleWithFixedUnderlying x y).toRightDifferentialGradedModule

@[simp] theorem representedHomRightDGModule_X (x y : 𝒜) (n : ℤ) :
    (representedHomRightDGModule x y).X n = representedHomFamily x y n :=
  rfl

@[simp] theorem representedHomRightDGModule_d (x y : 𝒜) (n : ℤ) :
    (representedHomRightDGModule x y).d n = representedHomDLinear x y n :=
  rfl

/-- Postcomposition with a closed degree-`0` morphism on each homogeneous represented Hom piece. -/
@[stacks 09LE]
def representedHomPostcomp {x y z : 𝒜} (f : CompHom y z) (n : ℤ) :
    (x ⟶[n] y) →ₗ[R] (x ⟶[n] z) :=
  { toFun := fun g ↦ castHom (add_zero n) (D.comp f.val g)
    map_add' := by
      intro g₁ g₂
      calc
        castHom (add_zero n) (D.comp f.val (g₁ + g₂)) =
            castHom (add_zero n) (D.comp f.val g₁ + D.comp f.val g₂) := by
              simpa using congrArg (castHom (add_zero n)) (D.comp_add_right f.val g₁ g₂)
        _ = castHom (add_zero n) (D.comp f.val g₁) +
              castHom (add_zero n) (D.comp f.val g₂) := by
              exact castHom_add (add_zero n) (D.comp f.val g₁) (D.comp f.val g₂)
    map_smul' := by
      intro r g
      calc
        castHom (add_zero n) (D.comp f.val (r • g)) =
            castHom (add_zero n) (r • D.comp f.val g) := by
              simpa using congrArg (castHom (add_zero n)) (D.comp_smul_right r f.val g)
        _ = r • castHom (add_zero n) (D.comp f.val g) := by
              exact castHom_smul (add_zero n) r (D.comp f.val g) }

/-- The degree-`n` postcomposition map is ordinary composition with the underlying closed
degree-`0` morphism. -/
@[simp] theorem representedHomPostcomp_apply {x y z : 𝒜} (f : CompHom y z)
    (n : ℤ) (g : representedHomFamily x y n) :
    representedHomPostcomp f n g = castHom (add_zero n) (D.comp f.val g) :=
  rfl

/-- Postcomposition commutes with the represented Hom differential. -/
theorem representedHomPostcomp_comm_d {x y z : 𝒜} (f : CompHom y z)
    (n : ℤ) (g : representedHomFamily x y n) :
    representedHomDLinear x z n (representedHomPostcomp f n g) =
      representedHomPostcomp f (n + 1) (representedHomDLinear x y n g) := by
  sorry

/-- Postcomposition is compatible with the represented right action by precomposition. -/
theorem representedHomPostcomp_smul {x y z : 𝒜} (f : CompHom y z)
    (p q : ℤ) (g : representedHomFamily x y p) (a : representedHomFamily x x q) :
    representedHomPostcomp f (p + q)
        ((representedHomRightDGModuleWithFixedUnderlying x y).smul p q g a) =
      (representedHomRightDGModuleWithFixedUnderlying x z).smul p q
        (representedHomPostcomp f p g) a := by
  sorry

/-- Postcomposition by the identity closed degree-`0` morphism is the identity. -/
@[simp] theorem representedHomPostcomp_id (x y : 𝒜)
    (n : ℤ) (g : representedHomFamily x y n) :
    representedHomPostcomp (CompHom.id y) n g = g := by
  rw [representedHomPostcomp_apply]
  simpa using D.id_comp_hom g

/-- Postcomposition is functorial on closed degree-`0` morphisms. -/
theorem representedHomPostcomp_comp {x y z w : 𝒜} (f : CompHom y z) (g : CompHom z w)
    (n : ℤ) (h : representedHomFamily x y n) :
    representedHomPostcomp (CompHom.comp f g) n h =
      representedHomPostcomp g n (representedHomPostcomp f n h) := by
  sorry

/-- Postcomposition by a closed degree-`0` morphism defines a morphism of represented right
differential graded modules. -/
def representedHomMap (x : 𝒜) {y z : 𝒜} (f : CompHom y z) :
    representedHomRightDGModule x y ⟶ representedHomRightDGModule x z where
  hom n := representedHomPostcomp f n
  comm_d n g := by
    simpa using (representedHomPostcomp_comm_d f n g).symm
  comm_smul n m a g := by
    sorry

/-- The degree-`n` component of `representedHomMap f` is postcomposition with `f`. -/
@[simp] theorem representedHomMap_hom (x : 𝒜) {y z : 𝒜} (f : CompHom y z) (n : ℤ) :
    (representedHomMap x f).hom n = representedHomPostcomp f n :=
  rfl

/-- Evaluating the degree-`n` component of `representedHomMap f` is postcomposition with `f`. -/
@[simp] theorem representedHomMap_hom_apply (x : 𝒜) {y z : 𝒜} (f : CompHom y z)
    (n : ℤ) (g : representedHomFamily x y n) :
    (representedHomMap x f).hom n g = representedHomPostcomp f n g :=
  rfl

/-- The represented-Hom module morphism attached to an identity closed degree-`0` morphism is the
identity. -/
@[simp] theorem representedHomMap_id (x y : 𝒜) :
    representedHomMap x (CompHom.id y) = 𝟙 (representedHomRightDGModule x y) := by
  apply LeftDifferentialGradedModule.hom_ext
  intro n
  ext g
  exact representedHomPostcomp_id x y n g

/-- The represented-Hom module morphism attached to a composite closed degree-`0` morphism is the
composite of the associated represented-Hom module morphisms. -/
@[simp] theorem representedHomMap_comp (x : 𝒜) {y z w : 𝒜} (f : CompHom y z) (g : CompHom z w) :
    representedHomMap x (CompHom.comp f g) =
      representedHomMap x f ≫ representedHomMap x g := by
  apply LeftDifferentialGradedModule.hom_ext
  intro n
  ext h
  exact representedHomPostcomp_comp f g n h

/-- The represented right differential graded modules form a functor on `Comp R 𝒜` by
postcomposition. -/
def representedHomFunctor (x : 𝒜) :
    Comp R 𝒜 ⥤ RightDifferentialGradedModule (representedEndomorphismDGA x) where
  obj y := representedHomRightDGModule x y
  map f := representedHomMap x f
  map_id y := representedHomMap_id x y
  map_comp f g := representedHomMap_comp x f g

@[simp] theorem representedHomFunctor_obj (x : 𝒜) (y : Comp R 𝒜) :
    (representedHomFunctor x).obj y = representedHomRightDGModule x y :=
  rfl

@[simp] theorem representedHomFunctor_map {x : 𝒜} {y z : Comp R 𝒜} (f : y ⟶ z) :
    (representedHomFunctor x).map f = representedHomMap x f :=
  rfl

end
