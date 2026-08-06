import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_6

open CategoryTheory Bundle

noncomputable section

universe v

-- Theorem 23.7.6 fixes the ordinary integral cohomology owner canonically as
-- `integralSingularCohomologyFunctor` and packages Chern classes as complex characteristic
-- classes. This file records Pontryagin classes by composing an even Chern class with a chosen
-- complexification of real bundle classes.

section

variable {n : ℕ}

/-- A chosen assignment sending each class of real `n`-plane bundles to a class of complex
`n`-plane bundles on the same base. -/
abbrev RealBundleComplexification (n : ℕ) :=
  ∀ {B : TopCat}, RealPlaneBundle.classes n B → ComplexPlaneBundle.classes n B

namespace RealBundleComplexification

variable (complexification : RealBundleComplexification n)

/-- The source-facing evaluation of a complexification on a raw real bundle family. -/
noncomputable abbrev onBundle {B : Type _} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    ComplexPlaneBundle.classes n (TopCat.of B) :=
  complexification (RealPlaneBundle.classOf n E)

end RealBundleComplexification

variable (complexification : RealBundleComplexification n)

namespace RealBundleComplexification

/-- Pullback-naturality is the bridge condition needed to precompose a complex characteristic
class with a chosen complexification of real bundle classes. -/
class IsNatural (complexification : RealBundleComplexification n) : Prop where
  /-- Pulling back a real bundle class pulls back the chosen complexification class. -/
  natural {B B' : TopCat} (f : B' ⟶ B) (ξ : RealPlaneBundle.classes n B) :
      ComplexPlaneBundle.pullbackOnClasses f.hom (complexification ξ) =
        complexification (RealPlaneBundle.pullbackOnClasses n f.hom ξ)

end RealBundleComplexification

/-- A chosen assignment of complex bundle classes to real bundle classes is a genuine
complexification when it is pullback-natural and each assigned class is represented by a complex
bundle whose fibers are the tensor-product complexifications of the real fibers. -/
class IsRealBundleComplexification
    (complexification : RealBundleComplexification n) : Prop extends
    RealBundleComplexification.IsNatural complexification where
  /-- Each chosen complexification class of a raw real bundle family is represented by a complex
  bundle with the expected fiberwise complex-linear model. -/
  isComplexification {B : Type _} [TopologicalSpace B] (E : B → Type v)
      [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
      [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
      [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
      [VectorBundle ℝ (Fin n → ℝ) E] :
      ∃ F : ComplexPlaneBundle n (TopCat.of B),
        complexification.onBundle E =
            (ComplexPlaneBundle.classOf F : ComplexPlaneBundle.classes n (TopCat.of B)) ∧
          ∀ b, Nonempty (F.fiber b ≃ₗ[ℂ] TensorProduct ℝ ℂ (E b))

namespace RealBundleComplexification

/-- Precomposing a complex characteristic class with a chosen real bundle complexification gives
a characteristic class of real `n`-plane bundles. -/
def toCharacteristicClass (complexification : RealBundleComplexification n)
    {q : ℕ} {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat} (c : ComplexCharacteristicClass n q k)
    [RealBundleComplexification.IsNatural complexification] : CharacteristicClass n q k where
  value ξ := c (complexification ξ)
  natural f ξ := by
    have h :
        ComplexPlaneBundle.pullbackOnClasses f.hom (complexification ξ) =
          complexification (RealPlaneBundle.pullbackOnClasses n f.hom ξ) :=
      (inferInstance : RealBundleComplexification.IsNatural complexification).natural f ξ
    exact Eq.trans (c.natural f (complexification ξ)) (congrArg (fun η ↦ c η) h)

@[simp] theorem toCharacteristicClass_value (complexification : RealBundleComplexification n)
    {q : ℕ} {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat} (c : ComplexCharacteristicClass n q k)
    [RealBundleComplexification.IsNatural complexification] {B : TopCat}
    (ξ : RealPlaneBundle.classes n B) :
    toCharacteristicClass complexification c ξ = c (complexification ξ) :=
  rfl

@[simp] theorem toCharacteristicClass_onBundle (complexification : RealBundleComplexification n)
    {q : ℕ} {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat} (c : ComplexCharacteristicClass n q k)
    [RealBundleComplexification.IsNatural complexification] {B : Type _} [TopologicalSpace B]
    (E : B → Type v) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (toCharacteristicClass complexification c).onBundle E = c (complexification.onBundle E) :=
  rfl

end RealBundleComplexification

variable (c : ChernClassFamily)

/-- The degree of the even Chern class `c_{2 * i}` is `4 * i`. -/
theorem pontryaginClass_degree (i : ℕ) :
    2 * (2 * i) = 4 * i := by
  rw [← Nat.mul_assoc]

/-- Definition 23.7.7. For a chosen complexification of real `n`-plane bundle classes, the
`i`-th Pontryagin class is the degree-`4 * i` characteristic class obtained from the even Chern
class of the complexification with sign convention `p_i = (-1)^i c_{2 * i}`. -/
def pontryaginClass (c : ChernClassFamily) (complexification : RealBundleComplexification n)
    [RealBundleComplexification.IsNatural complexification] (i : ℕ) :
    CharacteristicClass n (4 * i) integralSingularCohomologyFunctor :=
  (pontryaginClass_degree i) ▸
    { value := fun {B} ξ ↦
        ((-1 : ℤ) ^ i) •
          (RealBundleComplexification.toCharacteristicClass complexification (c n (2 * i)) ξ)
      natural := by
        intro B B' f ξ
        rw [map_zsmul]
        exact
          congrArg (fun x ↦ ((-1 : ℤ) ^ i) • x)
            ((RealBundleComplexification.toCharacteristicClass complexification
              (c n (2 * i))).natural f ξ) }

/-- Evaluating `pontryaginClass` on a real bundle class gives the signed even Chern class of its
chosen complexification. -/
@[simp] theorem pontryaginClass_value (c : ChernClassFamily)
    (complexification : RealBundleComplexification n)
    [RealBundleComplexification.IsNatural complexification] (i : ℕ)
    {B : TopCat} (ξ : RealPlaneBundle.classes n B) :
    pontryaginClass c complexification i ξ =
      (pontryaginClass_degree i) ▸
        (((-1 : ℤ) ^ i) • ((c n (2 * i)) (complexification ξ))) := by
  sorry

/-- Evaluating `pontryaginClass` on a raw real bundle family recovers the signed even Chern class
of its chosen complexification. -/
@[simp] theorem pontryaginClass_apply (c : ChernClassFamily)
    (complexification : RealBundleComplexification n)
    [RealBundleComplexification.IsNatural complexification] (i : ℕ)
    {B : Type _} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (pontryaginClass c complexification i).onBundle E =
      (pontryaginClass_degree i) ▸
        (((-1 : ℤ) ^ i) • ((c n (2 * i)) (complexification.onBundle E))) := by
  sorry

/-- The source-facing `onFamily` spelling for `pontryaginClass` evaluates to the same signed even
Chern class of the chosen complexification. -/
@[simp] theorem pontryaginClass_onFamily (c : ChernClassFamily)
    (complexification : RealBundleComplexification n)
    [RealBundleComplexification.IsNatural complexification] (i : ℕ)
    {B : Type _} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (pontryaginClass c complexification i).onFamily E =
      (pontryaginClass_degree i) ▸
        (((-1 : ℤ) ^ i) • ((c n (2 * i)) (complexification.onBundle E))) := by
  rw [CharacteristicClass.onFamily_eq_onBundle]
  exact pontryaginClass_apply c complexification i E

end
