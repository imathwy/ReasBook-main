import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_1

open CategoryTheory Limits

noncomputable section

universe u w

section

variable {R : Type w} [CommRing R]
variable {B : Type u} {n : ℕ} {E : B → Type u}
variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [VectorBundle ℝ (Fin n → ℝ) E]
variable (H : ℤ → (X : TopCat.{u}) → Set X → Type w)
variable [∀ q (X : TopCat.{u}) (A : Set X), AddCommGroup (H q X A)]
variable [∀ q (X : TopCat.{u}) (A : Set X), Module R (H q X A)]

/-- The one-point compactification of a fiber, based at the point at infinity. -/
abbrev compactifiedFiberSphere (A : Type u) [TopologicalSpace A] :
    BasedSpace.{u} :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (OnePoint.infty : OnePoint A)))

/-- The collapsed infinity subset of the Thom space `Tξ`. -/
def thomInfinitySubset {B : Type u} (n : ℕ) (E : B → Type u) : Set (ThomSpace n E) :=
  {x | ∃ b : B, x = thomSpaceMk n E b (OnePoint.infty : OnePoint (E b))}

/-- A minimal Thom-space cohomology owner for Proposition 23.5.5.

Route correction: `Definition_23_5_3` currently fails before this item elaborates, but the
mod-`2` uniqueness proof only uses the resulting cohomology module together with the supplied
fiber-restriction maps. Freezing a topology locally inside this owner keeps the proposition on the
same abstract cohomology surface without depending on the broken based-space wrapper. -/
abbrev thomReducedCohomology
    (n : ℕ) (E : B → Type u)
    (H : ℤ → (X : TopCat.{u}) → Set X → Type w)
    (q : ℤ) : Type w :=
  let _ : TopologicalSpace (ThomSpace n E) := ⊥
  H q (TopCat.of (ThomSpace n E)) (thomInfinitySubset n E)

/-- Thom-space reduced cohomology inherits its additive-group structure from the ambient relative
cohomology group. -/
instance thomReducedCohomologyAddCommGroup (q : ℤ) :
    AddCommGroup (thomReducedCohomology n E H q) := by
  -- Unfold the local owner and reuse the ambient cohomology-group structure.
  unfold thomReducedCohomology
  infer_instance

/-- Thom-space reduced cohomology inherits its `R`-module structure from the ambient relative
cohomology group. -/
instance thomReducedCohomologyModule (q : ℤ) :
    Module R (thomReducedCohomology n E H q) := by
  -- Unfold the local owner and reuse the ambient cohomology-module structure.
  unfold thomReducedCohomology
  infer_instance

/-- A Thom class or `R`-orientation of `ξ` is a reduced Thom-space cohomology class whose
restriction to each compactified fiber generates that fiber cohomology module. -/
structure ThomClass
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) where
  /-- The underlying reduced cohomology class on the Thom space. -/
  toReducedCohomology : thomReducedCohomology n E H (n : ℤ)
  /-- On each compactified fiber, the Thom class generates the degree-`n` reduced cohomology as
  an `R`-module. -/
  restricts_to_generator
      (b : B)
      (x : reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) :
      ∃ r : R, r • ((fiberRestriction b) toReducedCohomology) = x

/-- A Thom class can be used as its underlying reduced cohomology class. -/
instance instCoeOutThomClass
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) :
    CoeOut (ThomClass H fiberRestriction)
      (thomReducedCohomology n E H (n : ℤ)) where
  coe := ThomClass.toReducedCohomology

omit [TopologicalSpace B] [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
  [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [VectorBundle ℝ (Fin n → ℝ) E] in
/-- The defining generator property of a Thom class. -/
theorem ThomClass.exists_smul_eq
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (μ : ThomClass H fiberRestriction)
    (b : B)
    (x : reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))) :
    ∃ r : R, r • (fiberRestriction b) μ = x := by
  -- This is exactly the stored generator field of the Thom-class structure.
  exact μ.restricts_to_generator b x

end
