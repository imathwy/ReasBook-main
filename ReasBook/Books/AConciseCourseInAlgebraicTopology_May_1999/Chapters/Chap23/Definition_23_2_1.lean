import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_1_5

open CategoryTheory Bundle

noncomputable section

universe u v w

/-- Definition 23.2.1. A characteristic class of degree `q` for real `n`-plane bundles is a
natural assignment from real `n`-plane bundle classes to the degree-`q` cohomology groups of
their bases. -/
structure CharacteristicClass
    (n q : ℕ) (k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) where
  /-- The cohomology class assigned to a real `n`-plane bundle class. -/
  value {B : TopCat.{u}} (ξ : RealPlaneBundle.classes.{u, v} n B) :
      (k q).obj (Opposite.op B)
  /-- Pulling back a real `n`-plane bundle pulls back its characteristic class in degree `q`. -/
  natural {B B' : TopCat.{u}} (f : B' ⟶ B)
      (ξ : RealPlaneBundle.classes.{u, v} n B) :
      (k q).map f.op (value ξ) =
        value (RealPlaneBundle.pullbackOnClasses n f.hom ξ)

namespace CharacteristicClass

variable {n q : ℕ} {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- A characteristic class evaluates on real `n`-plane bundle classes. -/
instance characteristicClassCoeFun :
    CoeFun (CharacteristicClass n q k) fun _ ↦
      ∀ {B : TopCat.{u}},
        RealPlaneBundle.classes.{u, v} n B →
          (k q).obj (Opposite.op B) where
  coe c := c.value

/-- Evaluating a family-level assignment on the pullback of a real bundle family. This is the
raw-bundle target that appears in the pullback-naturality input for `ofBundle`. -/
noncomputable abbrev pullbackBundleValue
    (value :
      ∀ {B : Type u} [TopologicalSpace B] (E : B → Type v),
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        (k q).obj (Opposite.op (TopCat.of B)))
    {B B' : Type u} [TopologicalSpace B] [TopologicalSpace B']
    (f : C(B', B)) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (k q).obj (Opposite.op (TopCat.of B')) :=
  @value B' inferInstance (f *ᵖ E)
    inferInstance inferInstance inferInstance
    (fun b ↦ continuousMapPullbackAddCommGroup f E b)
    (continuousMapCoePullbackModules f E)
    (VectorBundle.pullback ℝ f :
      VectorBundle ℝ (Fin n → ℝ) (f *ᵖ E))

/-- Evaluating a characteristic class on a real `n`-plane bundle family means evaluating it on
its class in `E_n(B)`. -/
noncomputable abbrev onBundle (c : CharacteristicClass n q k) {B : Type u} [TopologicalSpace B]
    (E : B → Type v) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (k q).obj (Opposite.op (TopCat.of B)) :=
  c ((RealPlaneBundle.classOf n E) : RealPlaneBundle.classes.{u, v} n (TopCat.of B))

/-- `onFamily` is the source-facing spelling for evaluating on a raw bundle family. -/
noncomputable abbrev onFamily (c : CharacteristicClass n q k) {B : Type u} [TopologicalSpace B]
    (E : B → Type v) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (k q).obj (Opposite.op (TopCat.of B)) :=
  c.onBundle E

/-- Evaluating a characteristic class on a real bundle family is evaluation on its class. -/
@[simp] theorem coe_classOf (c : CharacteristicClass n q k) {B : Type u} [TopologicalSpace B]
    (E : B → Type v) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    c ((RealPlaneBundle.classOf n E) : RealPlaneBundle.classes.{u, v} n (TopCat.of B)) =
      c.onBundle E :=
  rfl

/-- The source-facing `onFamily` spelling is definitional equal to `onBundle`. -/
@[simp] theorem onFamily_eq_onBundle (c : CharacteristicClass n q k) {B : Type u}
    [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    c.onFamily E = c.onBundle E :=
  rfl

/-- The class-based owner can be constructed from a raw bundle-family assignment together with its
bundle-isomorphism invariance and pullback naturality. -/
noncomputable def ofBundle
    (value :
      ∀ {B : Type u} [TopologicalSpace B] (E : B → Type v),
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        (k q).obj (Opposite.op (TopCat.of B)))
    (invariant :
      ∀ {B : Type u} [TopologicalSpace B] {E E' : B → Type v},
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')] →
        [∀ b, TopologicalSpace (E b)] →
        [∀ b, TopologicalSpace (E' b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [FiberBundle (Fin n → ℝ) E'] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, AddCommGroup (E' b)] →
        [∀ b, Module ℝ (E b)] →
        [∀ b, Module ℝ (E' b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        [VectorBundle ℝ (Fin n → ℝ) E'] →
        RealPlaneBundleIso n B E E' →
          value E = value E')
    (natural :
      ∀ {B B' : Type u} [TopologicalSpace B] [TopologicalSpace B']
        (f : C(B', B)) (E : B → Type v),
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        (k q).map (TopCat.ofHom f).op (value E) = pullbackBundleValue value f E) :
    CharacteristicClass n q k where
  value := fun {B} ↦ RealPlaneBundle.liftClasses n (fun E ↦ value E) (fun e ↦ invariant e)
  natural := by
    intro B B' f ξ
    refine RealPlaneBundle.inductionOnClasses n ξ ?_
    intro E _ _ _ _ _ _
    simpa [RealPlaneBundle.pullbackOnClasses_classOf, pullbackBundleValue] using natural f.hom E

/-- Evaluating a class built by `ofBundle` on a raw bundle family recovers the original
family-level assignment. -/
@[simp] theorem ofBundle_onBundle
    (value :
      ∀ {B : Type u} [TopologicalSpace B] (E : B → Type v),
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        (k q).obj (Opposite.op (TopCat.of B)))
    (invariant :
      ∀ {B : Type u} [TopologicalSpace B] {E E' : B → Type v},
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')] →
        [∀ b, TopologicalSpace (E b)] →
        [∀ b, TopologicalSpace (E' b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [FiberBundle (Fin n → ℝ) E'] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, AddCommGroup (E' b)] →
        [∀ b, Module ℝ (E b)] →
        [∀ b, Module ℝ (E' b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        [VectorBundle ℝ (Fin n → ℝ) E'] →
        RealPlaneBundleIso n B E E' →
          value E = value E')
    (natural :
      ∀ {B B' : Type u} [TopologicalSpace B] [TopologicalSpace B']
        (f : C(B', B)) (E : B → Type v),
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        (k q).map (TopCat.ofHom f).op (value E) = pullbackBundleValue value f E)
    {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (CharacteristicClass.ofBundle value invariant natural).onBundle E = value E := by
  change
    RealPlaneBundle.liftClasses n
        (fun E ↦ value E)
        (fun e ↦ invariant e)
        (RealPlaneBundle.classOf n E) =
      value E
  exact
    RealPlaneBundle.liftClasses_classOf n
      (fun E ↦ value E)
      (fun e ↦ invariant e)
      E

/-- The source-facing `onFamily` surface for `ofBundle` also evaluates to the original
family-level assignment. -/
@[simp] theorem ofBundle_onFamily
    (value :
      ∀ {B : Type u} [TopologicalSpace B] (E : B → Type v),
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        (k q).obj (Opposite.op (TopCat.of B)))
    (invariant :
      ∀ {B : Type u} [TopologicalSpace B] {E E' : B → Type v},
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')] →
        [∀ b, TopologicalSpace (E b)] →
        [∀ b, TopologicalSpace (E' b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [FiberBundle (Fin n → ℝ) E'] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, AddCommGroup (E' b)] →
        [∀ b, Module ℝ (E b)] →
        [∀ b, Module ℝ (E' b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        [VectorBundle ℝ (Fin n → ℝ) E'] →
        RealPlaneBundleIso n B E E' →
          value E = value E')
    (natural :
      ∀ {B B' : Type u} [TopologicalSpace B] [TopologicalSpace B']
        (f : C(B', B)) (E : B → Type v),
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] →
        [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] →
        [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] →
        (k q).map (TopCat.ofHom f).op (value E) = pullbackBundleValue value f E)
    {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (CharacteristicClass.ofBundle value invariant natural).onFamily E = value E := by
  exact ofBundle_onBundle value invariant natural E

/-- Evaluating a characteristic class on the pullback of a real bundle family. -/
noncomputable abbrev pullbackValue (c : CharacteristicClass n q k) {B B' : Type u}
    [TopologicalSpace B] [TopologicalSpace B'] (f : C(B', B)) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (k q).obj (Opposite.op (TopCat.of B')) :=
  c (RealPlaneBundle.pullbackClass n f E)

/-- Characteristic classes are invariant under isomorphism of real `n`-plane bundle families. -/
theorem iso_invariant (c : CharacteristicClass n q k) {B : Type u} [TopologicalSpace B]
    {E E' : B → Type v} [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')] [∀ b, TopologicalSpace (E b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle (Fin n → ℝ) E] [FiberBundle (Fin n → ℝ) E']
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)] [∀ b, Module ℝ (E b)]
    [∀ b, Module ℝ (E' b)] [VectorBundle ℝ (Fin n → ℝ) E] [VectorBundle ℝ (Fin n → ℝ) E']
    (e : RealPlaneBundleIso n B E E') :
    c.onBundle E = c.onBundle E' := by
  simpa [CharacteristicClass.onBundle] using
    congrArg
      (fun ξ : RealPlaneBundle.classes.{u, v} n (TopCat.of B) ↦ c ξ)
      (RealPlaneBundle.classOf_eq_of_iso n e)

/-- Pulling back a real `n`-plane bundle along `f` pulls back the value of a characteristic class
along the induced cohomology map. -/
theorem naturality (c : CharacteristicClass n q k) {B B' : Type u} [TopologicalSpace B]
    [TopologicalSpace B'] (f : C(B', B)) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (k q).map (TopCat.ofHom f).op (c.onBundle E) =
      c.pullbackValue f E := by
  simpa [CharacteristicClass.onBundle, CharacteristicClass.pullbackValue] using
    c.natural (TopCat.ofHom f)
      (RealPlaneBundle.classOf n E :
        RealPlaneBundle.classes.{u, v} n (TopCat.of B))

end CharacteristicClass

end
