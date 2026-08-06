import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Principle_1_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1

noncomputable section

open CategoryTheory Bundle
open scoped Topology

universe u v w

-- Semantic recall via `lean_leansearch` did not surface an existing imported owner for
-- characteristic classes of complex vector bundles. Local Chapter 23 precedent packages these as
-- natural assignments out of bundle-class owners, using the quotient-model `BU(n)` API from
-- Theorem 23.7.1.

section

variable {n q : ℕ}
variable {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- A degree-`q` characteristic class of complex `n`-plane bundles is a natural assignment from
complex bundle classes to the degree-`q` cohomology groups of their bases. -/
structure ComplexCharacteristicClass
    (n q : ℕ) (k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) where
  /-- The cohomology class assigned to a complex `n`-plane bundle class. -/
  value {B : TopCat.{u}} (ξ : ComplexPlaneBundle.classes.{u, v} n B) :
      (k q).obj (Opposite.op B)
  /-- Pulling back a complex `n`-plane bundle pulls back its characteristic class. -/
  natural {B B' : TopCat.{u}} (f : B' ⟶ B)
      (ξ : ComplexPlaneBundle.classes.{u, v} n B) :
      (k q).map f.op (value ξ) =
        value (ComplexPlaneBundle.pullbackOnClasses f.hom ξ)

namespace ComplexCharacteristicClass

variable {n q : ℕ}
variable {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- A complex characteristic class evaluates on any complex `n`-plane bundle class. -/
instance complexCharacteristicClassCoeFun :
    CoeFun (ComplexCharacteristicClass n q k) fun _ ↦
      ∀ {B : TopCat.{u}},
        ComplexPlaneBundle.classes.{u, v} n B →
          (k q).obj (Opposite.op B) where
  coe c := c.value

/-- Evaluating a complex characteristic class on a complex `n`-plane bundle family means
evaluating it on its class in `ComplexPlaneBundle.classes n B`. -/
noncomputable abbrev onBundle (c : ComplexCharacteristicClass n q k) {B : Type u}
    [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℂ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    (k q).obj (Opposite.op (TopCat.of B)) :=
  c ((ComplexPlaneBundle.classOf E) : ComplexPlaneBundle.classes.{u, v} n (TopCat.of B))

/-- `onFamily` is the source-facing spelling for evaluating on a raw complex bundle family. -/
noncomputable abbrev onFamily (c : ComplexCharacteristicClass n q k) {B : Type u}
    [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℂ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    (k q).obj (Opposite.op (TopCat.of B)) :=
  c.onBundle E

/-- Evaluating a complex characteristic class on a complex bundle family is evaluation on its
class. -/
@[simp] theorem coe_classOf (c : ComplexCharacteristicClass n q k) {B : Type u}
    [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℂ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    c ((ComplexPlaneBundle.classOf E) : ComplexPlaneBundle.classes.{u, v} n (TopCat.of B)) =
      c.onBundle E :=
  rfl

/-- The source-facing `onFamily` spelling is definitional equal to `onBundle`. -/
@[simp] theorem onFamily_eq_onBundle (c : ComplexCharacteristicClass n q k) {B : Type u}
    [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℂ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    c.onFamily E = c.onBundle E :=
  rfl

/-- Evaluating a complex characteristic class on the pullback of a complex bundle family. -/
noncomputable abbrev pullbackValue (c : ComplexCharacteristicClass n q k) {B B' : Type u}
    [TopologicalSpace B] [TopologicalSpace B'] (f : C(B', B)) (E : B → Type v)
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    (k q).obj (Opposite.op (TopCat.of B')) :=
  c (ComplexPlaneBundle.pullbackClass f E)

/-- Complex characteristic classes are invariant under isomorphism of complex `n`-plane bundle
families. -/
theorem iso_invariant (c : ComplexCharacteristicClass n q k) {B : Type u}
    [TopologicalSpace B] {E E' : B → Type v}
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)]
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E')] [∀ b, TopologicalSpace (E b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle (Fin n → ℂ) E] [FiberBundle (Fin n → ℂ) E']
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)] [∀ b, Module ℂ (E b)]
    [∀ b, Module ℂ (E' b)] [VectorBundle ℂ (Fin n → ℂ) E] [VectorBundle ℂ (Fin n → ℂ) E']
    (e : ComplexPlaneBundleIso n B E E') :
    c.onBundle E = c.onBundle E' := by
  simpa [ComplexCharacteristicClass.onBundle] using
    congrArg
      (fun ξ : ComplexPlaneBundle.classes.{u, v} n (TopCat.of B) ↦ c ξ)
      (ComplexPlaneBundle.classOf_eq_of_iso e)

/-- Pulling back a complex `n`-plane bundle along `f` pulls back the value of a complex
characteristic class along the induced cohomology map. -/
theorem naturality (c : ComplexCharacteristicClass n q k) {B B' : Type u}
    [TopologicalSpace B] [TopologicalSpace B'] (f : C(B', B)) (E : B → Type v)
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    (k q).map (TopCat.ofHom f).op (c.onBundle E) =
      c.pullbackValue f E := by
  simpa [ComplexCharacteristicClass.onBundle, ComplexCharacteristicClass.pullbackValue] using
    c.natural (TopCat.ofHom f)
      (ComplexPlaneBundle.classOf E :
        ComplexPlaneBundle.classes.{u, v} n (TopCat.of B))

end ComplexCharacteristicClass

section

variable {EU : Type u} [TopologicalSpace EU]
variable [MulAction (U n) EU] [ContinuousSMul (U n) EU]
variable [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
variable {γBU : BU[n, EU] → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γBU)]
variable [∀ b, TopologicalSpace (γBU b)]
variable [FiberBundle (Fin n → ℂ) γBU]
variable [∀ b, AddCommGroup (γBU b)]
variable [∀ b, Module ℂ (γBU b)]
variable [VectorBundle ℂ (Fin n → ℂ) γBU]

/-- Evaluating a complex characteristic class on the universal complex `n`-plane bundle over the
quotient-model classifying space `BU(n)`. -/
abbrev complexCharacteristicClassEvalOnUniversalBundle
    (γBU : BU[n, EU] → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γBU)]
    [∀ b, TopologicalSpace (γBU b)]
    [FiberBundle (Fin n → ℂ) γBU]
    [∀ b, AddCommGroup (γBU b)]
    [∀ b, Module ℂ (γBU b)]
    [VectorBundle ℂ (Fin n → ℂ) γBU]
    [ComplexPlaneBundleQuotientModel n EU γBU] :
    ComplexCharacteristicClass n q k →
      (k q).obj
        (Opposite.op (TopCat.of BU[n, EU])) :=
  fun c ↦ c.onBundle γBU

@[simp] theorem complexCharacteristicClassEvalOnUniversalBundle_apply
    [ComplexPlaneBundleQuotientModel n EU γBU] (c : ComplexCharacteristicClass n q k) :
    complexCharacteristicClassEvalOnUniversalBundle γBU c =
      c.onBundle γBU :=
  rfl

/-- Lemma 23.7.3. Evaluation on the universal complex bundle identifies degree-`q` characteristic
classes of complex `n`-plane bundles with `k^q(BU(n))`. In the local Chapter 23 API, complex
bundles are recorded by `ComplexPlaneBundle.classes`, and the universal bundle is the quotient-model
bundle over `BU[n, EU]`. -/
theorem complexCharacteristicClassEvalOnUniversalBundle_bijective [ContractibleSpace EU]
    [ComplexPlaneBundleQuotientModel n EU γBU]
    [(k q).rightOp.IsHomotopyInvariant] :
    Function.Bijective
      ((complexCharacteristicClassEvalOnUniversalBundle
          γBU) :
        ComplexCharacteristicClass n q k →
          (k q).obj
            (Opposite.op (TopCat.of BU[n, EU]))) := sorry

end
end
