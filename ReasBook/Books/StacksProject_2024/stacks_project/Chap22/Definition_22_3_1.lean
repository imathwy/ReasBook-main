import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

variable {R : Type u} [CommRing R]

-- Semantic search note: `lean_leansearch` was unavailable in this runner, so the owner choice
-- below follows local project precedent for source-facing structures built on canonical
-- `ChainComplex` / `CochainComplex` owners.

/-- Transport the left Leibniz term for a chain differential graded algebra to degree
`n + m - 1`. -/
theorem chainDGAlgebra_leftLeibniz_index (n m : ℤ) :
    (n - 1) + m = n + m - 1 := by
  omega

/-- Transport the right Leibniz term for a chain differential graded algebra to degree
`n + m - 1`. -/
theorem chainDGAlgebra_rightLeibniz_index (n m : ℤ) :
    n + (m - 1) = n + m - 1 := by
  omega

/-- Definition 22.3.1 (1): a chain differential graded algebra over `R` is a chain complex of
`R`-modules indexed by `ℤ` together with degreewise `R`-bilinear multiplication, a unit in degree
`0`, associativity and unit laws, and the chain Leibniz rule. -/
@[stacks 061V]
structure ChainDGAlgebra (R : Type u) [CommRing R] where
  /-- The underlying chain complex of `R`-modules. -/
  toChainComplex : ChainComplex (ModuleCat R) ℤ
  /-- The degreewise multiplication maps. -/
  mul (n m : ℤ) : toChainComplex.X n →ₗ[R] toChainComplex.X m →ₗ[R] toChainComplex.X (n + m)
  /-- The unit element in degree `0`. -/
  one : toChainComplex.X 0
  /-- The multiplication is associative on homogeneous elements. -/
  mul_assoc (i j k : ℤ) (a : toChainComplex.X i) (b : toChainComplex.X j)
      (c : toChainComplex.X k) :
      cast (congrArg (fun n : ℤ ↦ (toChainComplex.X n : Type u)) (add_assoc i j k))
        (mul (i + j) k (mul i j a b) c) =
        mul i (j + k) a (mul j k b c)
  /-- The unit acts on the left. -/
  one_mul (n : ℤ) (a : toChainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type u)) (zero_add n))
        (mul 0 n one a) = a
  /-- The unit acts on the right. -/
  mul_one (n : ℤ) (a : toChainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type u)) (add_zero n))
        (mul n 0 a one) = a
  /-- The differential satisfies the chain Leibniz rule. -/
  leibniz (n m : ℤ) (a : toChainComplex.X n) (b : toChainComplex.X m) :
      toChainComplex.d (n + m) (n + m - 1) (mul n m a b) =
        cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type u))
          (chainDGAlgebra_leftLeibniz_index n m))
          (mul (n - 1) m (toChainComplex.d n (n - 1) a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type u))
            (chainDGAlgebra_rightLeibniz_index n m))
            (mul n (m - 1) a (toChainComplex.d m (m - 1) b))

namespace ChainDGAlgebra

/-- A chain differential graded algebra can be used as its underlying chain complex. -/
instance : CoeOut (ChainDGAlgebra R) (ChainComplex (ModuleCat R) ℤ) where
  coe A := A.toChainComplex

/-- The underlying chain complex of a chain differential graded algebra has homology in every
degree because `ModuleCat R` is abelian. -/
noncomputable instance (A : ChainDGAlgebra R) (n : ℤ) : A.toChainComplex.HasHomology n := by
  exact ⟨⟨ShortComplex.HomologyData.ofAbelian (A.toChainComplex.sc n)⟩⟩

/-- The degree-`n` term of a chain differential graded algebra. -/
abbrev X (A : ChainDGAlgebra R) (n : ℤ) : ModuleCat R :=
  A.toChainComplex.X n

/-- The differential of a chain differential graded algebra on degree `n`. -/
abbrev d (A : ChainDGAlgebra R) (n : ℤ) : A.X n ⟶ A.X (n - 1) :=
  A.toChainComplex.d n (n - 1)

/-- The cycles object of a chain differential graded algebra in degree `n`. -/
noncomputable abbrev cycles (A : ChainDGAlgebra R) (n : ℤ) :=
  A.toChainComplex.cycles n

/-- The canonical inclusion of cycles into the degree-`n` term. -/
noncomputable abbrev iCycles (A : ChainDGAlgebra R) (n : ℤ) : A.cycles n ⟶ A.X n :=
  A.toChainComplex.iCycles n

/-- The homology object of a chain differential graded algebra in degree `n`. -/
noncomputable abbrev homology (A : ChainDGAlgebra R) (n : ℤ) :=
  A.toChainComplex.homology n

/-- The canonical projection from cycles to homology in degree `n`. -/
noncomputable abbrev homologyπ (A : ChainDGAlgebra R) (n : ℤ) : A.cycles n ⟶ A.homology n :=
  A.toChainComplex.homologyπ n

/-- The `X` accessor agrees with the underlying chain complex. -/
@[simp] theorem X_eq_toChainComplex_X (A : ChainDGAlgebra R) (n : ℤ) :
    A.X n = A.toChainComplex.X n :=
  rfl

/-- The `d` accessor agrees with the underlying chain-complex differential. -/
@[simp] theorem d_eq_toChainComplex_d (A : ChainDGAlgebra R) (n : ℤ) :
    A.d n = A.toChainComplex.d n (n - 1) :=
  rfl

/-- In a chain differential graded algebra, homogeneous multiplication is associative. -/
theorem mul_assoc_apply (A : ChainDGAlgebra R) (i j k : ℤ)
    (a : A.X i) (b : A.X j) (c : A.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_assoc i j k))
      (A.mul (i + j) k (A.mul i j a b) c) =
      A.mul i (j + k) a (A.mul j k b c) :=
  A.mul_assoc i j k a b c

/-- In a chain differential graded algebra, the left unit law holds on homogeneous elements. -/
@[simp] theorem one_mul_apply (A : ChainDGAlgebra R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type u)) (zero_add n))
      (A.mul 0 n A.one a) = a :=
  A.one_mul n a

/-- In a chain differential graded algebra, the right unit law holds on homogeneous elements. -/
@[simp] theorem mul_one_apply (A : ChainDGAlgebra R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type u)) (add_zero n))
      (A.mul n 0 a A.one) = a :=
  A.mul_one n a

/-- The chain differential satisfies the graded Leibniz rule on homogeneous elements. -/
theorem leibniz_apply (A : ChainDGAlgebra R) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    A.d (n + m) (A.mul n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
          (chainDGAlgebra_leftLeibniz_index n m))
          (A.mul (n - 1) m (A.d n a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
              (chainDGAlgebra_rightLeibniz_index n m))
            (A.mul n (m - 1) a (A.d m b)) :=
  A.leibniz n m a b

end ChainDGAlgebra

/-- A homomorphism `f : (A, d) → (B, d)` of chain differential graded `R`-algebras is a morphism
of the underlying chain complexes that preserves the unit and the homogeneous multiplication. On
the canonical Chapter 22 owner `ChainDGAlgebra R`, the condition that `f` commute with the
differentials is encoded by the chain-map field `toChainMap`. -/
@[stacks 061W]
structure ChainDGAlgebra.Hom (A B : ChainDGAlgebra R) where
  /-- The underlying morphism of chain complexes. -/
  toChainMap : A.toChainComplex ⟶ B.toChainComplex
  /-- The unit is preserved. -/
  map_one : toChainMap.f 0 A.one = B.one
  /-- The multiplication is preserved on homogeneous elements. -/
  map_mul (n m : ℤ) (a : A.X n) (b : A.X m) :
    toChainMap.f (n + m) (A.mul n m a b) = B.mul n m (toChainMap.f n a) (toChainMap.f m b)

namespace ChainDGAlgebra.Hom

variable {A B C : ChainDGAlgebra R}

/-- The identity homomorphism of a chain differential graded algebra. -/
def id (A : ChainDGAlgebra R) : Hom A A where
  toChainMap := 𝟙 A.toChainComplex
  map_one := rfl
  map_mul _ _ _ _ := rfl

/-- Composition of chain differential graded algebra homomorphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  toChainMap := f.toChainMap ≫ g.toChainMap
  map_one := by
    change g.toChainMap.f 0 (f.toChainMap.f 0 A.one) = C.one
    rw [f.map_one, g.map_one]
  map_mul n m a b := by
    change
      g.toChainMap.f (n + m) (f.toChainMap.f (n + m) (A.mul n m a b)) =
        C.mul n m (g.toChainMap.f n (f.toChainMap.f n a))
          (g.toChainMap.f m (f.toChainMap.f m b))
    rw [f.map_mul, g.map_mul]

@[simp] theorem id_toChainMap (A : ChainDGAlgebra R) :
    (id A).toChainMap = 𝟙 A.toChainComplex :=
  rfl

@[simp] theorem comp_toChainMap (g : Hom B C) (f : Hom A B) :
    (comp g f).toChainMap = f.toChainMap ≫ g.toChainMap :=
  rfl

/-- Extensionality for chain differential graded algebra homomorphisms reduces to the
underlying chain-complex map. -/
theorem ext_toChainMap {f g : Hom A B} (h : f.toChainMap = g.toChainMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

end ChainDGAlgebra.Hom

namespace ChainDGAlgebra

/-- A chain differential graded algebra homomorphism can be used as its underlying chain map. -/
instance {A B : ChainDGAlgebra R} : Coe (Hom A B) (A.toChainComplex ⟶ B.toChainComplex) where
  coe f := f.toChainMap

/-- A chain differential graded algebra homomorphism can be applied degreewise to homogeneous
elements. -/
instance {A B : ChainDGAlgebra R} : CoeFun (Hom A B) (fun _ ↦ ∀ n : ℤ, A.X n → B.X n) where
  coe f := fun n a ↦ f.toChainMap.f n a

/-- Coercing a chain differential graded algebra homomorphism to a function recovers the
degreewise action of the underlying chain map. -/
@[simp] theorem coe_apply {A B : ChainDGAlgebra R} (f : Hom A B) (n : ℤ) (a : A.X n) :
    f n a = f.toChainMap.f n a :=
  rfl

/-- A chain differential graded algebra homomorphism commutes with the differentials because its
underlying chain map does. -/
@[simp] theorem map_d_apply {A B : ChainDGAlgebra R} (f : Hom A B) (n : ℤ) (a : A.X n) :
    f (n - 1) (A.d n a) = B.d n (f n a) := by
  change (f.toChainMap.f (n - 1)).hom ((A.toChainComplex.d n (n - 1)).hom a) =
      (B.toChainComplex.d n (n - 1)).hom ((f.toChainMap.f n).hom a)
  exact (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.toChainMap.comm n (n - 1))) a).symm

/-- A chain differential graded algebra homomorphism preserves the unit. -/
@[simp] theorem map_one_apply {A B : ChainDGAlgebra R} (f : Hom A B) :
    f 0 A.one = B.one :=
  f.map_one

/-- A chain differential graded algebra homomorphism preserves homogeneous multiplication. -/
@[simp] theorem map_mul_apply {A B : ChainDGAlgebra R} (f : Hom A B)
    (n m : ℤ) (a : A.X n) (b : A.X m) :
    f (n + m) (A.mul n m a b) = B.mul n m (f n a) (f m b) :=
  f.map_mul n m a b

/-- Composition acts degreewise by composing the underlying maps on each homogeneous piece. -/
@[simp] theorem comp_apply {A B C : ChainDGAlgebra R} (g : Hom B C) (f : Hom A B)
    (n : ℤ) (a : A.X n) :
    Hom.comp g f n a = g n (f n a) :=
  rfl

/-- Extensionality for chain differential graded algebra homomorphisms can be checked degreewise
on homogeneous elements. -/
@[ext] theorem hom_ext
    {A B : ChainDGAlgebra R} {f g : Hom A B}
    (h : ∀ n : ℤ, ∀ a : A.X n, f n a = g n a) : f = g := by
  apply Hom.ext_toChainMap
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  exact h n a

end ChainDGAlgebra

/-- Transport the left Leibniz term for a cochain differential graded algebra to degree
`n + m + 1`. -/
theorem cochainDGAlgebra_leftLeibniz_index (n m : ℤ) :
    (n + 1) + m = n + m + 1 := by
  omega

/-- Transport the right Leibniz term for a cochain differential graded algebra to degree
`n + m + 1`. -/
theorem cochainDGAlgebra_rightLeibniz_index (n m : ℤ) :
    n + (m + 1) = n + m + 1 := by
  omega

/-- Definition 22.3.1 (2): a cochain differential graded algebra over `R` is a cochain complex of
`R`-modules indexed by `ℤ` together with degreewise `R`-bilinear multiplication, a unit in degree
`0`, associativity and unit laws, and the cochain Leibniz rule. -/
@[stacks 061V]
structure CochainDGAlgebra (R : Type u) [CommRing R] where
  /-- The underlying cochain complex of `R`-modules. -/
  toCochainComplex : CochainComplex (ModuleCat R) ℤ
  /-- The degreewise multiplication maps. -/
  mul (n m : ℤ) :
      toCochainComplex.X n →ₗ[R] toCochainComplex.X m →ₗ[R] toCochainComplex.X (n + m)
  /-- The unit element in degree `0`. -/
  one : toCochainComplex.X 0
  /-- The multiplication is associative on homogeneous elements. -/
  mul_assoc (i j k : ℤ) (a : toCochainComplex.X i) (b : toCochainComplex.X j)
      (c : toCochainComplex.X k) :
      cast (congrArg (fun n : ℤ ↦ (toCochainComplex.X n : Type u)) (add_assoc i j k))
        (mul (i + j) k (mul i j a b) c) =
        mul i (j + k) a (mul j k b c)
  /-- The unit acts on the left. -/
  one_mul (n : ℤ) (a : toCochainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type u)) (zero_add n))
        (mul 0 n one a) = a
  /-- The unit acts on the right. -/
  mul_one (n : ℤ) (a : toCochainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type u)) (add_zero n))
        (mul n 0 a one) = a
  /-- The differential satisfies the cochain Leibniz rule. -/
  leibniz (n m : ℤ) (a : toCochainComplex.X n) (b : toCochainComplex.X m) :
      toCochainComplex.d (n + m) (n + m + 1) (mul n m a b) =
        cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type u))
          (cochainDGAlgebra_leftLeibniz_index n m))
          (mul (n + 1) m (toCochainComplex.d n (n + 1) a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type u))
            (cochainDGAlgebra_rightLeibniz_index n m))
            (mul n (m + 1) a (toCochainComplex.d m (m + 1) b))

namespace CochainDGAlgebra

/-- A cochain differential graded algebra can be used as its underlying cochain complex. -/
instance : CoeOut (CochainDGAlgebra R) (CochainComplex (ModuleCat R) ℤ) where
  coe A := A.toCochainComplex

/-- The underlying cochain complex of a cochain differential graded algebra has homology in every
degree because `ModuleCat R` is abelian. -/
noncomputable instance (A : CochainDGAlgebra R) (n : ℤ) : A.toCochainComplex.HasHomology n := by
  exact ⟨⟨ShortComplex.HomologyData.ofAbelian (A.toCochainComplex.sc n)⟩⟩

/-- The degree-`n` term of a cochain differential graded algebra. -/
abbrev X (A : CochainDGAlgebra R) (n : ℤ) : ModuleCat R :=
  A.toCochainComplex.X n

/-- The differential of a cochain differential graded algebra on degree `n`. -/
abbrev d (A : CochainDGAlgebra R) (n : ℤ) : A.X n ⟶ A.X (n + 1) :=
  A.toCochainComplex.d n (n + 1)

/-- The cycles object of a cochain differential graded algebra in degree `n`. -/
noncomputable abbrev cycles (A : CochainDGAlgebra R) (n : ℤ) :=
  A.toCochainComplex.cycles n

/-- The canonical inclusion of cycles into the degree-`n` term. -/
noncomputable abbrev iCycles (A : CochainDGAlgebra R) (n : ℤ) : A.cycles n ⟶ A.X n :=
  A.toCochainComplex.iCycles n

/-- The homology object of a cochain differential graded algebra in degree `n`. -/
noncomputable abbrev homology (A : CochainDGAlgebra R) (n : ℤ) :=
  A.toCochainComplex.homology n

/-- The canonical projection from cycles to homology in degree `n`. -/
noncomputable abbrev homologyπ (A : CochainDGAlgebra R) (n : ℤ) : A.cycles n ⟶ A.homology n :=
  A.toCochainComplex.homologyπ n

/-- The `X` accessor agrees with the underlying cochain complex. -/
@[simp] theorem X_eq_toCochainComplex_X (A : CochainDGAlgebra R) (n : ℤ) :
    A.X n = A.toCochainComplex.X n :=
  rfl

/-- The `d` accessor agrees with the underlying cochain-complex differential. -/
@[simp] theorem d_eq_toCochainComplex_d (A : CochainDGAlgebra R) (n : ℤ) :
    A.d n = A.toCochainComplex.d n (n + 1) :=
  rfl

/-- In a cochain differential graded algebra, homogeneous multiplication is associative. -/
theorem mul_assoc_apply (A : CochainDGAlgebra R) (i j k : ℤ)
    (a : A.X i) (b : A.X j) (c : A.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_assoc i j k))
      (A.mul (i + j) k (A.mul i j a b) c) =
      A.mul i (j + k) a (A.mul j k b c) :=
  A.mul_assoc i j k a b c

/-- In a cochain differential graded algebra, the left unit law holds on homogeneous elements. -/
@[simp] theorem one_mul_apply (A : CochainDGAlgebra R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type u)) (zero_add n))
      (A.mul 0 n A.one a) = a :=
  A.one_mul n a

/-- In a cochain differential graded algebra, the right unit law holds on homogeneous elements. -/
@[simp] theorem mul_one_apply (A : CochainDGAlgebra R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type u)) (add_zero n))
      (A.mul n 0 a A.one) = a :=
  A.mul_one n a

/-- The cochain differential satisfies the graded Leibniz rule on homogeneous elements. -/
theorem leibniz_apply (A : CochainDGAlgebra R) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    A.d (n + m) (A.mul n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
          (cochainDGAlgebra_leftLeibniz_index n m))
          (A.mul (n + 1) m (A.d n a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
              (cochainDGAlgebra_rightLeibniz_index n m))
            (A.mul n (m + 1) a (A.d m b)) :=
  A.leibniz n m a b

end CochainDGAlgebra
