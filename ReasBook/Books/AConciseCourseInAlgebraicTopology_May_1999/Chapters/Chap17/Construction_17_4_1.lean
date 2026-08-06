import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_1_3

noncomputable section

open CategoryTheory

universe u

-- Semantic recall via `lean_leansearch`: `HomologicalComplex.toCycles` packages textbook
-- boundaries as a map into cycles, and
-- `CategoryTheory.ShortComplex.ShortExact.splittingOfProjective` identifies the canonical
-- abstract splitting criterion. The labeled source-facing content here is
-- the short exact sequence `0 ⟶ Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X) ⟶ 0` together with the free/PID
-- splitting hypothesis used in the universal-coefficient argument; the abstract projective
-- boundary criterion is kept as an unlabeled helper.

/-- The boundary module hit by the degree-`n` differential of `X`, realized as the range of
`X.toCycles n ((ComplexShape.down ℕ).next n)`.

For `n = i + 1`, this is the textbook boundary module `B_i(X)`. -/
abbrev boundaryModule
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    ModuleCat R :=
  ModuleCat.of R
    (LinearMap.range
      (ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n))))

/-- The inclusion of `boundaryModule R X n` into the cycle module
`X.cycles ((ComplexShape.down ℕ).next n)`. -/
abbrev boundaryInclusion
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    boundaryModule R X n ⟶ X.cycles ((ComplexShape.down ℕ).next n) :=
  ModuleCat.ofHom
    (LinearMap.range
      (ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n)))).subtype

/-- The canonical surjection from `X.X n` onto `boundaryModule R X n`. -/
def toBoundary
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    X.X n ⟶ boundaryModule R X n :=
  ModuleCat.ofHom
    ((ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n))).codRestrict
      (LinearMap.range
        (ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n))))
      (fun x ↦ ⟨x, rfl⟩))

/-- Composing `toBoundary R X n` with the inclusion into cycles recovers the canonical boundary
map `X.toCycles n ((ComplexShape.down ℕ).next n)`. -/
@[reassoc, simp]
theorem toBoundary_comp_boundaryInclusion
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    toBoundary R X n ≫ boundaryInclusion R X n =
      X.toCycles n ((ComplexShape.down ℕ).next n) := sorry

/-- The cycle inclusion followed by the boundary projection is zero. -/
@[reassoc, simp]
theorem iCycles_comp_toBoundary
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    X.iCycles n ≫ toBoundary R X n = 0 := sorry

/-- The short complex `Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X)` used in the universal-coefficient proof. -/
def cycleBoundaryShortComplex
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (X.iCycles n) (toBoundary R X n)
    (iCycles_comp_toBoundary R X n)

/-- Construction 17.4.1 (1). The cycles, chains, and boundaries in degree `n` fit into the short
exact sequence
`0 ⟶ X.cycles n ⟶ X.X n ⟶ boundaryModule R X n ⟶ 0`,
which is the textbook sequence `0 ⟶ Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X) ⟶ 0`. -/
theorem cycleBoundaryShortComplex_shortExact
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (cycleBoundaryShortComplex R X n).ShortExact := sorry

/-- The right-hand term of `cycleBoundaryShortComplex R X n` is
`boundaryModule R X n`, so projectivity of the latter is the canonical
typeclass input for splitting the short exact sequence. -/
instance cycleBoundaryShortComplex_projectiveX₃
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [Projective (boundaryModule R X n)] :
    Projective (cycleBoundaryShortComplex R X n).X₃ :=
  inferInstanceAs (Projective (boundaryModule R X n))

/-- Construction 17.4.1 (2). Over a PID, if the chain groups of `X` are flat, then the cycle
module `X.cycles n = Z_n(X)` is flat. Together with `cycleBoundaryShortComplex_shortExact` and
the assumed flatness of `X.X n`, this realizes
`0 ⟶ Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X) ⟶ 0`
as the flat resolution used in Theorem 17.1.3. -/
theorem cycleBoundaryShortComplex_cycles_flat
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    Module.Flat R (X.cycles n) := sorry

/-- The flatness conclusion of `cycleBoundaryShortComplex_cycles_flat` is available to typeclass
search when the flatness of the chain groups is supplied instance-wise. -/
instance cycleBoundaryShortComplex_cycles_moduleFlat
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [hX : ∀ i : ℕ, Module.Flat R (X.X i)] :
    Module.Flat R (X.cycles n) :=
  cycleBoundaryShortComplex_cycles_flat R X n hX

/-- If `boundaryModule R X n`, representing the textbook `B_(n - 1)(X)`, is projective, then the
short exact sequence
`0 ⟶ Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X) ⟶ 0`
admits a splitting. -/
theorem cycleBoundaryShortComplex_splitting_of_projectiveBoundary
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [Projective (boundaryModule R X n)] :
    Nonempty ((cycleBoundaryShortComplex R X n).Splitting) :=
  ⟨ShortComplex.ShortExact.splittingOfProjective
    (cycleBoundaryShortComplex_shortExact R X n)⟩

/-- Construction 17.4.1 (3). Under the free/PID hypothesis on the chain groups used in the
cohomological universal-coefficient argument,
the short exact sequence
`0 ⟶ Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X) ⟶ 0`
admits a splitting. This is the source-facing specialization of
`cycleBoundaryShortComplex_splitting_of_projectiveBoundary`. -/
theorem cycleBoundaryShortComplex_splitting
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Free R (X.X i)) :
    Nonempty ((cycleBoundaryShortComplex R X n).Splitting) := sorry
