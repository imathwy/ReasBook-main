module

public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
public import Topology_Munkres_2000.Book.Exercise_58_9.BasedClassification
public import Mathlib.Topology.Algebra.Group.Basic

public section

open Function

namespace Circle

/-- Translation of `ℝ` by an integer, regarded as a self-homeomorphism. -/
def integerTranslation (n : ℤ) : ℝ ≃ₜ ℝ :=
  Homeomorph.addRight (n : ℝ)

/-- Integer translation sends `x` to `x + n`. -/
theorem integerTranslation_apply (n : ℤ) (x : ℝ) :
    integerTranslation n x = x + n := by
  -- Unfold the evaluation rule of the additive homeomorphism.
  rfl

/-- Every integer translation lies over the standard covering `Circle.turnExp`. -/
theorem integerTranslation_mem (n : ℤ) :
    integerTranslation n ∈ CoveringTransformation.group Circle.turnExp := by
  -- Integer shifts preserve every fiber of the standard circle covering.
  apply (CoveringTransformation.mem_group _ _).2
  funext x
  simp only [comp_apply, integerTranslation_apply]
  exact turnExp_add_int x n

/-- Helper for Example 81.1: translation by zero is the identity homeomorphism. -/
theorem integerTranslation_one : integerTranslation 0 = 1 := by
  -- Compare the two homeomorphisms pointwise.
  ext x
  simp only [integerTranslation_apply, Int.cast_zero, add_zero, Homeomorph.one_apply]

/-- Helper for Example 81.1: composing integer translations adds their translation indices. -/
theorem integerTranslation_comp (m n : ℤ) :
    integerTranslation (m + n) = integerTranslation m * integerTranslation n := by
  -- Pointwise evaluation reduces composition to associativity and commutativity of addition.
  ext x
  simp only [integerTranslation_apply, Int.cast_add, Homeomorph.mul_apply]
  ring

/-- Helper for Example 81.1: the group-valued integer translation sends the identity to the
identity covering transformation. -/
theorem integerTranslationToGroup_one :
    (⟨integerTranslation 0, integerTranslation_mem 0⟩ :
      CoveringTransformation.group Circle.turnExp) = 1 := by
  -- Equality in the subgroup follows from equality of the underlying homeomorphisms.
  apply Subtype.ext
  exact integerTranslation_one

/-- Helper for Example 81.1: the group-valued integer translation preserves multiplication. -/
theorem integerTranslationToGroup_mul (m n : Multiplicative ℤ) :
    (⟨integerTranslation (m * n).toAdd, integerTranslation_mem (m * n).toAdd⟩ :
      CoveringTransformation.group Circle.turnExp) =
      ⟨integerTranslation m.toAdd, integerTranslation_mem m.toAdd⟩ *
        ⟨integerTranslation n.toAdd, integerTranslation_mem n.toAdd⟩ := by
  -- Reduce subgroup equality to the composition law for translations.
  apply Subtype.ext
  exact integerTranslation_comp m.toAdd n.toAdd

/-- Integer translations define a homomorphism into the standard covering transformation group. -/
def integerTranslationHom : Multiplicative ℤ →* CoveringTransformation.group Circle.turnExp where
  toFun n := ⟨integerTranslation n.toAdd, integerTranslation_mem n.toAdd⟩
  map_one' := integerTranslationToGroup_one
  map_mul' := integerTranslationToGroup_mul

/-- The integer-translation homomorphism evaluates as translation by the underlying integer. -/
theorem integerTranslationHom_apply (n : Multiplicative ℤ) :
    (integerTranslationHom n : ℝ ≃ₜ ℝ) = integerTranslation n.toAdd := by
  -- The homomorphism stores exactly the corresponding translation homeomorphism.
  rfl

/-- The covering transformations of `Circle.turnExp` are exactly the integer translations. -/
theorem mem_coveringTransformationGroup_iff_integerTranslation (h : ℝ ≃ₜ ℝ) :
    h ∈ CoveringTransformation.group Circle.turnExp ↔
      ∃ n : ℤ, h = integerTranslation n := by
  constructor
  · intro hmem
    -- Evaluating the covering equation at zero places `h 0` in the integer fiber.
    have hzero_fiber : turnExp (h 0) = 1 := by
      have hcomp := (CoveringTransformation.mem_group _ _).1 hmem
      exact (congrFun hcomp 0).trans turnExp_zero
    obtain ⟨n, hzero⟩ := (turnExp_eq_one_iff (h 0)).1 hzero_fiber
    refine ⟨n, ?_⟩
    -- The two lifts have the same composite and agree at zero, hence are equal.
    have hlifts : (h : ℝ → ℝ) = integerTranslation n := by
      have hcomp := (CoveringTransformation.mem_group _ _).1 hmem
      have htranslation :=
        (CoveringTransformation.mem_group _ _).1 (integerTranslation_mem n)
      have hbase : h 0 = integerTranslation n 0 := by
        simpa only [integerTranslation_apply, zero_add] using hzero
      exact isCoveringMap_turnExp.eq_of_comp_eq h.continuous
        (integerTranslation n).continuous (hcomp.trans htranslation.symm) 0 hbase
    apply Homeomorph.ext
    exact congrFun hlifts
  · rintro ⟨n, rfl⟩
    -- Every displayed integer translation already satisfies the covering equation.
    exact integerTranslation_mem n

/-- Helper for Example 81.1: evaluation at zero recovers the integer translation index. -/
theorem integerTranslationInverse_left (n : Multiplicative ℤ) :
    Multiplicative.ofAdd ⌊(integerTranslationHom n : ℝ ≃ₜ ℝ) 0⌋ = n := by
  -- Pass to additive coordinates and compute the floor of the integer value at zero.
  simp only [integerTranslationHom_apply, integerTranslation_apply, zero_add,
    Int.floor_intCast, ofAdd_toAdd]

/-- Helper for Example 81.1: the integer coordinate extracted at zero reconstructs a covering
transformation. -/
theorem integerTranslationInverse_right
    (h : CoveringTransformation.group Circle.turnExp) :
    integerTranslationHom (Multiplicative.ofAdd ⌊(h : ℝ ≃ₜ ℝ) 0⌋) = h := by
  -- Classify the underlying homeomorphism, then normalize its value at zero.
  obtain ⟨n, hn⟩ :=
    (mem_coveringTransformationGroup_iff_integerTranslation (h : ℝ ≃ₜ ℝ)).1 h.property
  have hzero : (h : ℝ ≃ₜ ℝ) 0 = (n : ℝ) := by
    rw [hn, integerTranslation_apply, zero_add]
  apply Subtype.ext
  rw [integerTranslationHom_apply, hzero, Int.floor_intCast]
  exact hn.symm

/-- Integer translation identifies `Multiplicative ℤ` with the covering transformation group of
`Circle.turnExp`. -/
noncomputable def integerTranslationEquiv :
    Multiplicative ℤ ≃* CoveringTransformation.group Circle.turnExp where
  toFun := integerTranslationHom
  invFun h := Multiplicative.ofAdd ⌊(h : ℝ ≃ₜ ℝ) 0⌋
  left_inv := integerTranslationInverse_left
  right_inv := integerTranslationInverse_right
  map_mul' := integerTranslationHom.map_mul

/-- The integer-translation equivalence sends an integer to translation by that integer. -/
@[simp]
theorem integerTranslationEquiv_apply (n : Multiplicative ℤ) :
    (integerTranslationEquiv n : ℝ ≃ₜ ℝ) = integerTranslation n.toAdd :=
  integerTranslationHom_apply n

end Circle
