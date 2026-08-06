import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.ModTwoCohomologyTheory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Problem_9_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_2_1

open CategoryTheory Bundle
open scoped BigOperators

universe u v w

-- Chapter 22 owns the ambient ordinary mod-`2` cohomology and Steenrod-square surfaces used
-- here; this file adds the Stiefel-Whitney layer built on that shared cohomology owner.

noncomputable section

/-- The degree-`i` Whitney-sum expression built from a cup product on the chosen mod-`2`
cohomology theory `H2`. -/
def whitneySumExpansion
    (H2 : ModTwoCohomologyTheory)
    {i : ℕ} {B : TopCat}
    (α : ∀ p : ℕ, (H2.cohomology p).obj (Opposite.op B))
    (β : ∀ q : ℕ, (H2.cohomology q).obj (Opposite.op B)) :
    (H2.cohomology i).obj (Opposite.op B) :=
  ∑ p : Fin (i + 1),
    cast
      (by
        rw [Nat.add_sub_of_le (Nat.le_of_lt_succ p.2)])
      (H2.cup (α p) (β (i - p)))

/-- A family of degree-`i` Stiefel-Whitney characteristic classes for real `n`-plane bundles in
the chosen ambient ordinary mod-`2` cohomology theory `H2`. -/
abbrev StiefelWhitneyClassFamily (H2 : ModTwoCohomologyTheory) :=
  ∀ n i : ℕ, CharacteristicClass n i H2.cohomology

-- Semantic recall via `lean_leansearch` did not surface a ready-made tautological real line-bundle
-- owner over the relevant real projective base in the current environment, so the normalization
-- setup is kept explicit here rather than weakened to only the degree-zero unit class.

/-- A chosen `RP^∞` normalization datum for degree-`1` Stiefel-Whitney classes in the ambient
mod-`2` cohomology theory `H2`: the tautological real line bundle over the canonical projective
space model `RealProjectiveInfinity` and the distinguished degree-`1` class used in the
normalization axiom. -/
structure StiefelWhitneyNormalization (H2 : ModTwoCohomologyTheory) where
  /-- The tautological real line bundle over the canonical projective-space base
  `RealProjectiveInfinity`. -/
  tautologicalLineBundle : RealPlaneBundle 1 (TopCat.of RealProjectiveInfinity)
  /-- The chosen bundle fibers are exactly the canonical projective-space tautological lines,
  up to the ambient universe lift used by this file's bundle conventions. -/
  tautologicalLineBundle_spec :
    tautologicalLineBundle.fiber =
      fun ℓ : TopCat.of RealProjectiveInfinity ↦ ULift.{v} (Projectivization.submodule ℓ)
  /-- The distinguished degree-`1` class on `RealProjectiveInfinity`. -/
  degreeOneClass : (H2.cohomology 1).obj (Opposite.op (TopCat.of RealProjectiveInfinity))

/-- A degree-`1` mod-`2` singular cohomology class on `RealProjectiveInfinity` is standard when
it corresponds to `1 : ZMod 2` under some chosen identification
`H¹(RP^∞; ZMod 2) ≃ ZMod 2`. -/
def IsStandardRealProjectiveGenerator
    (α : modTwoSingularCohomology (TopCat.of RealProjectiveInfinity) 1) : Prop :=
  ∃ e : modTwoSingularCohomology (TopCat.of RealProjectiveInfinity) 1 ≅
      ModuleCat.of ℤ (ZMod 2),
    e.hom α = 1

/-- A `RP^∞` normalization datum whose ambient degree-`1` class is identified with the standard
generator of ordinary mod-`2` singular cohomology. -/
structure StandardStiefelWhitneyNormalization (H2 : ModTwoCohomologyTheory)
    extends StiefelWhitneyNormalization H2 where
  /-- The chosen singular degree-`1` generator on `RP^∞`. -/
  singularDegreeOneGenerator :
    modTwoSingularCohomology (TopCat.of RealProjectiveInfinity) 1
  /-- The ambient normalization class corresponds to the chosen singular generator. -/
  comparison_degreeOneClass :
    (H2.comparison 1 (TopCat.of RealProjectiveInfinity)).hom
      toStiefelWhitneyNormalization.degreeOneClass =
        singularDegreeOneGenerator
  /-- The chosen singular class is the standard generator of `H¹(RP^∞; ZMod 2)`. -/
  singularDegreeOneGenerator_spec :
    IsStandardRealProjectiveGenerator singularDegreeOneGenerator

namespace StandardStiefelWhitneyNormalization

/-- The ambient degree-`1` Stiefel-Whitney normalization class of a standard normalization datum,
viewed as the standard generator on `RP^∞`. -/
abbrev degreeOneGenerator
    {H2 : ModTwoCohomologyTheory} (normalizationData : StandardStiefelWhitneyNormalization H2) :
    (H2.cohomology 1).obj (Opposite.op (TopCat.of RealProjectiveInfinity)) :=
  normalizationData.degreeOneClass

/-- The ambient degree-`1` normalization class of a standard normalization datum corresponds to
its chosen singular generator. -/
theorem comparison_degreeOneGenerator
    {H2 : ModTwoCohomologyTheory} (normalizationData : StandardStiefelWhitneyNormalization H2) :
    (H2.comparison 1 (TopCat.of RealProjectiveInfinity)).hom
      normalizationData.degreeOneGenerator =
        normalizationData.singularDegreeOneGenerator :=
  normalizationData.comparison_degreeOneClass

/-- The ambient degree-`1` normalization class of a standard normalization datum is the standard
generator of `H¹(RP^∞; ZMod 2)`. -/
theorem degreeOneGenerator_isStandard
    {H2 : ModTwoCohomologyTheory} (normalizationData : StandardStiefelWhitneyNormalization H2) :
    IsStandardRealProjectiveGenerator
      ((H2.comparison 1 (TopCat.of RealProjectiveInfinity)).hom
        normalizationData.degreeOneGenerator) := by
  rw [comparison_degreeOneGenerator]
  exact normalizationData.singularDegreeOneGenerator_spec

end StandardStiefelWhitneyNormalization

/-- The Stiefel-Whitney axioms for a family of characteristic classes in the chosen ambient
ordinary mod-`2` cohomology theory `H2`. Naturality is built into `CharacteristicClass`. The
normalization clauses fix the degree-`0` unit class on every bundle and the degree-`1` class of
the chosen tautological real line bundle over `RealProjectiveInfinity`. The Whitney-sum clause is
stated for the chosen bundled Whitney sum `RealPlaneBundle.whitneySum E₁ E₂`. -/
structure IsStiefelWhitneyTheory
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    (w : StiefelWhitneyClassFamily H2) : Prop where
  /-- The degree-`0` class of every real vector bundle is the unit class. -/
  zeroClass : ∀ {n : ℕ} {B : TopCat} (E : RealPlaneBundle n B),
    (w n 0) ((RealPlaneBundle.classOf n E) : RealPlaneBundle.classes n B) =
      H2.oneClass B
  /-- The degree-`1` class of the chosen tautological real line bundle is the distinguished
  normalization class. -/
  normalization :
    (w 1 1)
        ((RealPlaneBundle.classOf 1 normalizationData.tautologicalLineBundle) :
          RealPlaneBundle.classes 1 (TopCat.of RealProjectiveInfinity)) =
      normalizationData.degreeOneClass
  /-- The degree-`i` class of an `n`-plane bundle vanishes for `i > n`. -/
  dimension : ∀ {n i : ℕ} {B : TopCat} (E : RealPlaneBundle n B),
    n < i →
      (w n i) ((RealPlaneBundle.classOf n E) : RealPlaneBundle.classes n B) = 0
  /-- The classes of a Whitney sum are given by the cup-product expansion of the summand classes
  on the bundled direct sum `RealPlaneBundle.whitneySum E₁ E₂`. -/
  whitneySum :
    ∀ {n m i : ℕ} {B : TopCat}
      (E₁ : RealPlaneBundle n B) (E₂ : RealPlaneBundle m B)
      [TopologicalSpace (Bundle.TotalSpace (Fin (n + m) → ℝ) (E₁.fiber ×ᵇ E₂.fiber))]
      [FiberBundle (Fin (n + m) → ℝ) (E₁.fiber ×ᵇ E₂.fiber)]
      [VectorBundle ℝ (Fin (n + m) → ℝ) (E₁.fiber ×ᵇ E₂.fiber)],
      (w (n + m) i)
          ((RealPlaneBundle.classOf (n + m)
            (RealPlaneBundle.whitneySum E₁ E₂)) :
              RealPlaneBundle.classes (n + m) B) =
        whitneySumExpansion H2
          (fun p ↦ (w n p) ((RealPlaneBundle.classOf n E₁) : RealPlaneBundle.classes n B))
          (fun q ↦ (w m q) ((RealPlaneBundle.classOf m E₂) : RealPlaneBundle.classes m B))

/-- A Stiefel-Whitney theory has the usual degree-zero unit class on every real `n`-plane bundle. -/
theorem IsStiefelWhitneyTheory.zeroClass_eq_oneClass
    {H2 : ModTwoCohomologyTheory}
    {normalizationData : StiefelWhitneyNormalization H2}
    {w : StiefelWhitneyClassFamily H2}
    (hw : IsStiefelWhitneyTheory H2 normalizationData w)
    (n : ℕ) {B : TopCat} (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)]
    [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    (w n 0).onFamily E = H2.oneClass B := by
  simpa [CharacteristicClass.onFamily, CharacteristicClass.onBundle] using
    hw.zeroClass (RealPlaneBundle.ofFamily n E)

section

variable (H2 : ModTwoCohomologyTheory)
variable (normalizationData : StiefelWhitneyNormalization H2)

/-- For a fixed chosen degree-`1` normalization class on the tautological real line bundle over
`RP^∞`, any two Stiefel-Whitney theories satisfying the remaining axioms agree. This is the
generic uniqueness surface used by later Chapter 23 constructions that supply their own
normalization class. -/
theorem subsingleton_stiefelWhitneyTheory_of_normalization
    {w w' : StiefelWhitneyClassFamily H2}
    (hw : IsStiefelWhitneyTheory H2 normalizationData w)
    (hw' : IsStiefelWhitneyTheory H2 normalizationData w') :
    w = w' := sorry

/-- For a fixed chosen degree-`1` normalization class on `RP^∞`, the corresponding
Stiefel-Whitney theories form a subsingleton. -/
theorem stiefelWhitneyTheory_subsingleton_of_normalization :
    Subsingleton { w : StiefelWhitneyClassFamily H2 //
      IsStiefelWhitneyTheory H2 normalizationData w } := by
  refine ⟨?_⟩
  intro a b
  apply Subtype.ext
  exact
    subsingleton_stiefelWhitneyTheory_of_normalization H2 normalizationData
      a.property b.property

instance instSubsingletonStiefelWhitneyTheoryOfNormalization :
    Subsingleton { w : StiefelWhitneyClassFamily H2 //
      IsStiefelWhitneyTheory H2 normalizationData w } :=
  stiefelWhitneyTheory_subsingleton_of_normalization H2 normalizationData

end

section

variable (H2 : ModTwoCohomologyTheory)
variable (normalizationData : StandardStiefelWhitneyNormalization H2)

/-- Theorem 23.3.1 (1). For the chosen ambient ordinary mod-`2` cohomology theory `H2`, there
exists a family of characteristic classes `w_i` for real `n`-plane bundles satisfying
normalization on the chosen tautological real line bundle over `RealProjectiveInfinity` by the
standard generator of `H¹(RP^∞; ZMod 2)`,
dimension,
naturality, and Whitney sum behavior. Naturality is encoded by `CharacteristicClass`. -/
theorem exists_stiefelWhitneyTheory :
    ∃ w : StiefelWhitneyClassFamily H2,
      IsStiefelWhitneyTheory H2 normalizationData.toStiefelWhitneyNormalization w := sorry

/-- Theorem 23.3.1 (2). For the chosen ambient ordinary mod-`2` cohomology theory `H2`, any two
families of Stiefel-Whitney characteristic classes satisfying normalization on the chosen
tautological real line bundle over `RealProjectiveInfinity` by the standard generator of
`H¹(RP^∞; ZMod 2)`, dimension, naturality, and the Whitney sum formula agree. -/
theorem subsingleton_stiefelWhitneyTheory
    {w w' : StiefelWhitneyClassFamily H2}
    (hw : IsStiefelWhitneyTheory H2 normalizationData.toStiefelWhitneyNormalization w)
    (hw' : IsStiefelWhitneyTheory H2 normalizationData.toStiefelWhitneyNormalization w') :
    w = w' :=
  subsingleton_stiefelWhitneyTheory_of_normalization
    H2 normalizationData.toStiefelWhitneyNormalization hw hw'

/-- The Stiefel-Whitney theories normalized by `normalizationData` form a subsingleton. This is
the automation-friendly uniqueness surface underlying Theorem 23.3.1 (2). -/
theorem stiefelWhitneyTheory_subsingleton :
    Subsingleton { w : StiefelWhitneyClassFamily H2 //
      IsStiefelWhitneyTheory H2 normalizationData.toStiefelWhitneyNormalization w } :=
  stiefelWhitneyTheory_subsingleton_of_normalization
    H2 normalizationData.toStiefelWhitneyNormalization

instance instSubsingletonStiefelWhitneyTheory :
    Subsingleton { w : StiefelWhitneyClassFamily H2 //
      IsStiefelWhitneyTheory H2 normalizationData.toStiefelWhitneyNormalization w } :=
  stiefelWhitneyTheory_subsingleton H2 normalizationData

/-- Theorem 23.3.1 packaged as existence and uniqueness of the normalized Stiefel-Whitney
theory. This companion bundles parts (1) and (2) into the canonical `∃!` surface used by later
construction files. -/
theorem existsUnique_stiefelWhitneyTheory :
    ∃! w : StiefelWhitneyClassFamily H2,
      IsStiefelWhitneyTheory H2 normalizationData.toStiefelWhitneyNormalization w := by
  rcases exists_stiefelWhitneyTheory H2 normalizationData with ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  exact subsingleton_stiefelWhitneyTheory H2 normalizationData hw' hw

end
