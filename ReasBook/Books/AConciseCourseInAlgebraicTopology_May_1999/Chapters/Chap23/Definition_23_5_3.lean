import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v w

-- Semantic recall via `lean_leansearch` did not surface a canonical Thom-class owner in the
-- current environment. Local Chapter 23 precedent already fixes `ThomSpace n E`, and Chapter 19
-- fixes `reducedCohomology`, so this file records the source definition using those owners and
-- explicit fiber-restriction maps.

section

variable {R : Type w} [CommRing R]
variable {B : Type u} {n : ℕ} {E : B → Type u}
variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [VectorBundle ℝ (Fin n → ℝ) E]
variable (H : ℤ → (X : TopCat.{u}) → Set X → Type w)
variable [∀ q (X : TopCat.{u}) (A : Set X), AddCommGroup (H q X A)]
variable [∀ q (X : TopCat.{u}) (A : Set X), Module R (H q X A)]

/-- The one-point compactification of a space, based at the point at infinity. This is the
fiber-sphere owner used for each compactified fiber in Definition 23.5.3. -/
abbrev compactifiedFiberSphere (A : Type u) [TopologicalSpace A] :
    BasedSpace.{u} :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (OnePoint.infty : OnePoint A)))

/-- The basepoint of `compactifiedFiberSphere A` is the point at infinity. -/
@[simp] theorem underTopBasepoint_compactifiedFiberSphere
    (A : Type u) [TopologicalSpace A] :
    underTopBasepoint (compactifiedFiberSphere A) = (OnePoint.infty : OnePoint A) :=
  rfl

/-- A chosen based-space model of `ThomSpace n F`, using the common collapsed point at infinity
represented in the fiber over `b_inf`. -/
abbrev thomBasedSpace
    (n : ℕ) (F : B → Type u)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) F)]
    [∀ b, TopologicalSpace (F b)] [FiberBundle (Fin n → ℝ) F]
    [∀ b, NormedAddCommGroup (F b)] [∀ b, NormedSpace ℝ (F b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module ℝ (F b)]
    [VectorBundle ℝ (Fin n → ℝ) F]
    (b_inf : B) : BasedSpace.{u} :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom
        (ContinuousMap.const PUnit
          (thomSpaceMk n F b_inf (OnePoint.infty : OnePoint (F b_inf)))))

/-- The basepoint of `thomBasedSpace n E b_inf` is the collapsed point at infinity in
`ThomSpace n E`. -/
@[simp] theorem underTopBasepoint_thomBasedSpace (b_inf : B) :
    underTopBasepoint (thomBasedSpace n E b_inf) =
      ((thomSpaceMk n E b_inf (OnePoint.infty : OnePoint (E b_inf))) :
        TopCat.of (ThomSpace n E)) :=
  rfl

/-- The canonical infinity subset of `ThomSpace n E`, consisting of the common collapsed point
represented by any fiberwise point at infinity. -/
def thomInfinitySubset {B : Type u} (n : ℕ) (E : B → Type v) : Set (ThomSpace n E) :=
  {x | ∃ b : B, x = thomSpaceMk n E b (OnePoint.infty : OnePoint (E b))}

section

variable {B : Type u} {n : ℕ} {E : B → Type v}

/-- Every chosen fiberwise point at infinity lies in the canonical infinity subset of
`ThomSpace n E`. -/
theorem thomSpaceMk_infty_mem_thomInfinitySubset (b : B) :
    thomSpaceMk n E b (OnePoint.infty : OnePoint (E b)) ∈ thomInfinitySubset n E :=
  ⟨b, rfl⟩

/-- The canonical infinity subset of `ThomSpace n E` is the singleton determined by any chosen
fiberwise point at infinity. -/
theorem thomInfinitySubset_eq_singleton (b_inf : B) :
    thomInfinitySubset n E =
      ({thomSpaceMk n E b_inf (OnePoint.infty : OnePoint (E b_inf))} : Set (ThomSpace n E)) := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact Set.mem_singleton_iff.mpr (thomSpaceMk_infty_eq n E b b_inf)
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact thomSpaceMk_infty_mem_thomInfinitySubset b_inf

end

/-- The infinity subset of `ThomSpace n E` agrees with the singleton basepoint subset of any
chosen based-space model `thomBasedSpace n E b_inf`. -/
theorem thomInfinitySubset_eq_basepointSingleton (b_inf : B) :
    thomInfinitySubset n E =
      ({underTopBasepoint (thomBasedSpace n E b_inf)} : Set (TopCat.of (ThomSpace n E))) := by
  rw [thomInfinitySubset_eq_singleton b_inf]
  simp [underTopBasepoint_thomBasedSpace]

/-- The reduced cohomology of the Thom space, expressed canonically as relative cohomology of the
underlying Thom space with respect to its collapsed infinity subset. -/
abbrev thomReducedCohomology
    (n : ℕ) (E : B → Type u)
    [TopologicalSpace B]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E]
    (H : ℤ → (X : TopCat.{u}) → Set X → Type w)
    (q : ℤ) : Type w :=
  H q (TopCat.of (ThomSpace n E)) (thomInfinitySubset n E)

/-- The canonical Thom-space reduced cohomology inherits its additive-group structure from the
underlying relative cohomology group of `ThomSpace n E` relative to the infinity subset. -/
instance thomReducedCohomologyAddCommGroup (q : ℤ) :
    AddCommGroup (thomReducedCohomology n E H q) := by
  unfold thomReducedCohomology
  infer_instance

/-- The canonical Thom-space reduced cohomology inherits its `R`-module structure from the
underlying relative cohomology group of `ThomSpace n E` relative to the infinity subset. -/
instance thomReducedCohomologyModule (q : ℤ) :
    Module R (thomReducedCohomology n E H q) := by
  unfold thomReducedCohomology
  infer_instance

section

omit [∀ q (X : TopCat.{u}) (A : Set X), AddCommGroup (H q X A)]

/-- The canonical Thom-space reduced cohomology agrees with the reduced cohomology of any chosen
based-space model `thomBasedSpace n E b_inf`. -/
theorem thomReducedCohomology_eq_reducedCohomology
    (q : ℤ) (b_inf : B) :
    thomReducedCohomology n E H q =
      reducedCohomology H q (thomBasedSpace n E b_inf) := by
  unfold thomReducedCohomology
  rw [reducedCohomology_def]
  change
    H q (TopCat.of (ThomSpace n E)) (thomInfinitySubset n E) =
      H q (TopCat.of (ThomSpace n E))
        ({underTopBasepoint (thomBasedSpace n E b_inf)} : Set (TopCat.of (ThomSpace n E)))
  rw [thomInfinitySubset_eq_basepointSingleton b_inf]

end

/-- Definition 23.5.3. Relative to a chosen based-space model of `Tξ` and chosen restriction maps
from the reduced cohomology of `Tξ` to the compactified fibers, a Thom class or `R`-orientation
of `ξ` is a class `μ ∈ H̃^n(Tξ; R)` whose restriction to each fiber sphere generates the
degree-`n` reduced cohomology of that fiber sphere as an `R`-module. -/
structure ThomClass
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) where
  /-- The underlying reduced cohomology class `μ ∈ H̃^n(Tξ; R)`. -/
  toReducedCohomology : thomReducedCohomology n E H (n : ℤ)
  /-- On every compactified fiber, the restriction of `μ` generates the degree-`n` reduced
  cohomology group as an `R`-module. -/
  restricts_to_generator
      (b : B)
      (x : reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) :
      ∃ r : R, r • ((fiberRestriction b) toReducedCohomology) = x

/-- A Thom class can be used as its underlying reduced cohomology class on the Thom space. -/
instance instCoeOutThomClass
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) :
    CoeOut (ThomClass H fiberRestriction)
      (thomReducedCohomology n E H (n : ℤ)) where
  coe := ThomClass.toReducedCohomology

/-- The defining generator property of a Thom class says that every degree-`n` reduced
cohomology class on a compactified fiber is an `R`-multiple of the restricted Thom class. -/
theorem ThomClass.exists_smul_eq
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (μ : ThomClass H fiberRestriction)
    (b : B)
    (x : reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) :
    ∃ r : R,
      r • (fiberRestriction b) μ = x :=
  μ.restricts_to_generator b x

end
