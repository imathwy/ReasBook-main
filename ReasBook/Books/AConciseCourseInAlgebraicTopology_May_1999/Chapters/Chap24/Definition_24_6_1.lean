import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Theorem_11_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Mathlib.Topology.Category.TopCat.Sphere

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical topological Hopf-invariant owner for a map
-- `S^(2n - 1) → S^n` surfaced in the current environment, so this item uses the local Chapter 11
-- mapping-cone owner together with the Chapter 18 singular-cohomology cup product.

/-- A map `S^(2n - 1) → S^n`, the source datum for the Hopf-invariant construction. -/
abbrev HopfSphereMap (n : ℕ) :=
  C(TopCat.sphere (2 * n - 1), TopCat.sphere n)

/-- The mapping cone `C_f` attached to `f : S^(2n - 1) → S^n`. -/
abbrev hopfMappingCone {n : ℕ} (f : HopfSphereMap n) : TopCat :=
  TopCat.of (mappingCone f)

/-- The integral singular cohomology of `C_f` in degree `q`. -/
abbrev hopfMappingConeCohomology {n : ℕ} (f : HopfSphereMap n) (q : ℕ) :=
  singularCohomologyClasses ℤ (hopfMappingCone f) q

/-- Integer scaling on `H^q(C_f; ℤ)`. -/
abbrev hopfMappingConeCohomologyZsmul {n : ℕ} (f : HopfSphereMap n) (q : ℕ) (m : ℤ) :
    hopfMappingConeCohomology f q → hopfMappingConeCohomology f q :=
  singularCohomologyClassZsmul ℤ (hopfMappingCone f) q m

/-- The cup square `a^2` of a degree-`n` cohomology class on `C_f`, viewed in degree `2n`. -/
def hopfMappingConeCupSquare {n : ℕ} (f : HopfSphereMap n)
    (a : hopfMappingConeCohomology f n) :
    hopfMappingConeCohomology f (2 * n) :=
  cast (by simp [two_mul]) (singularCohomologyCup ℤ (hopfMappingCone f) n n a a)

/-- Definition 24.6.1. For `f : S^(2n - 1) → S^n`, `IsHopfInvariant f h`
asserts that in the mapping cone `C_f` there are generators `a ∈ H^n(C_f; ℤ)` and
`b ∈ H^(2n)(C_f; ℤ)` whose cup-square satisfies `a^2 = h • b`; the source-side
positivity condition appears explicitly as `1 ≤ n`. -/
class IsHopfInvariant {n : ℕ} (f : HopfSphereMap n) (h : ℤ) : Prop where
  /-- The source-side positivity hypothesis in Definition 24.6.1. -/
  one_le : 1 ≤ n
  /-- There are generators `a ∈ H^n(C_f; ℤ)` and `b ∈ H^(2n)(C_f; ℤ)` whose
  `ℤ`-multiple maps are bijective and satisfy `a^2 = h • b`. -/
  exists_generators :
    ∃ a : hopfMappingConeCohomology f n, ∃ b : hopfMappingConeCohomology f (2 * n),
      Function.Bijective (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f n m a) ∧
      Function.Bijective (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f (2 * n) m b) ∧
      hopfMappingConeCupSquare f a =
        hopfMappingConeCohomologyZsmul f (2 * n) h b

/-- `IsHopfInvariant f h` expands to the positivity condition `1 ≤ n` together with the
existence of generators in degrees `n` and `2n` whose `ℤ`-multiple maps are bijective and
satisfy `a^2 = h • b`. -/
theorem isHopfInvariant_iff {n : ℕ} {f : HopfSphereMap n} {h : ℤ} :
    IsHopfInvariant f h ↔
      1 ≤ n ∧
        ∃ a : hopfMappingConeCohomology f n, ∃ b : hopfMappingConeCohomology f (2 * n),
          Function.Bijective (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f n m a) ∧
          Function.Bijective
            (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f (2 * n) m b) ∧
          hopfMappingConeCupSquare f a =
            hopfMappingConeCohomologyZsmul f (2 * n) h b := by
  constructor
  · intro hf
    exact ⟨hf.one_le, hf.exists_generators⟩
  · rintro ⟨hn, hgenerators⟩
    exact ⟨hn, hgenerators⟩

/-- A choice of generators in `H^n(C_f; ℤ)` and `H^(2n)(C_f; ℤ)` realizing a Hopf invariant. -/
structure MappingConeHopfInvariantDatum {n : ℕ} (f : HopfSphereMap n) where
  /-- The chosen generator `a ∈ H^n(C_f; ℤ)`. -/
  degreeNClass : hopfMappingConeCohomology f n
  /-- The chosen generator `b ∈ H^(2n)(C_f; ℤ)`. -/
  degreeTwoNClass : hopfMappingConeCohomology f (2 * n)
  /-- The map `m ↦ m • a` is a bijection `ℤ ≃ H^n(C_f; ℤ)`. -/
  degreeNClass_generates :
    Function.Bijective (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f n m degreeNClass)
  /-- The map `m ↦ m • b` is a bijection `ℤ ≃ H^(2n)(C_f; ℤ)`. -/
  degreeTwoNClass_generates :
    Function.Bijective
      (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f (2 * n) m degreeTwoNClass)
  /-- The integer `h(f)` appearing in the relation `a^2 = h(f) b`. -/
  hopfInvariant : ℤ
  /-- The defining cup-square relation `a^2 = h(f) b` in `H^(2n)(C_f; ℤ)`. -/
  cupSquare_eq :
    hopfMappingConeCupSquare f degreeNClass =
      hopfMappingConeCohomologyZsmul f (2 * n) hopfInvariant degreeTwoNClass

/-- The packaged source semantics of `MappingConeHopfInvariantDatum f`: the chosen classes
identify `H^n(C_f; ℤ)` and `H^(2n)(C_f; ℤ)` with `ℤ` via their `ℤ`-multiple maps, and the
cup square of the degree-`n` generator is the Hopf invariant times the degree-`2n` generator. -/
theorem MappingConeHopfInvariantDatum.spec {n : ℕ} {f : HopfSphereMap n}
    (d : MappingConeHopfInvariantDatum f) :
    Function.Bijective (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f n m d.degreeNClass) ∧
    Function.Bijective
      (fun m : ℤ ↦ hopfMappingConeCohomologyZsmul f (2 * n) m d.degreeTwoNClass) ∧
    hopfMappingConeCupSquare f d.degreeNClass =
      hopfMappingConeCohomologyZsmul f (2 * n) d.hopfInvariant d.degreeTwoNClass :=
  ⟨d.degreeNClass_generates, d.degreeTwoNClass_generates, d.cupSquare_eq⟩

namespace IsHopfInvariant

/-- A Hopf-invariant witness furnishes a packaged choice of generators realizing that invariant. -/
theorem exists_datum {n : ℕ} {f : HopfSphereMap n} {h : ℤ} (hf : IsHopfInvariant f h) :
    ∃ d : MappingConeHopfInvariantDatum f, d.hopfInvariant = h := by
  rcases hf.exists_generators with ⟨a, b, ha, hb, hcup⟩
  exact ⟨
    { degreeNClass := a
      degreeTwoNClass := b
      degreeNClass_generates := ha
      degreeTwoNClass_generates := hb
      hopfInvariant := h
      cupSquare_eq := hcup },
    rfl⟩

end IsHopfInvariant

/-- `IsHopfInvariant f h` is equivalent to the source positivity condition `1 ≤ n` together with
the existence of packaged chosen generators whose Hopf invariant is exactly `h`. -/
theorem isHopfInvariant_iff_exists_datum {n : ℕ} {f : HopfSphereMap n} {h : ℤ} :
    IsHopfInvariant f h ↔ 1 ≤ n ∧ ∃ d : MappingConeHopfInvariantDatum f, d.hopfInvariant = h := by
  constructor
  · intro hf
    exact ⟨hf.one_le, hf.exists_datum⟩
  · rintro ⟨hn, d, rfl⟩
    refine ⟨hn, ?_⟩
    exact ⟨d.degreeNClass, d.degreeTwoNClass, d.degreeNClass_generates,
      d.degreeTwoNClass_generates, d.cupSquare_eq⟩

/-- Any chosen Hopf-invariant datum yields the corresponding source-facing invariant statement. -/
theorem MappingConeHopfInvariantDatum.isHopfInvariant {n : ℕ} (hn : 1 ≤ n)
    {f : HopfSphereMap n} (d : MappingConeHopfInvariantDatum f) :
    IsHopfInvariant f d.hopfInvariant := by
  refine ⟨hn, ?_⟩
  exact ⟨d.degreeNClass, d.degreeTwoNClass, d.degreeNClass_generates,
    d.degreeTwoNClass_generates, d.cupSquare_eq⟩
