import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_2
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open AlgebraicTopology CategoryTheory Limits
open scoped Manifold Topology

noncomputable section

-- Semantic recall via `lean_leansearch`: the available canonical connecting morphism owner is
-- `CategoryTheory.ShortComplex.ShortExact.δ`. Local Chapter 20/21 precedent already fixes
-- `relativeTopHomologyGroup`, `rSingularHomology`, `ROrientedManifoldWithBoundary`, and
-- `manifoldBoundary`, so this item keeps the source-facing notation `H_n(M, ∂M; R)` only as a
-- bridge to the Chapter 20 relative-homology owner and states the uniqueness theorem on that
-- canonical surface.

section

variable (n : ℕ) [NeZero n]
variable (M : Type) [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]

/-- The inclusion `∂M ↪ M` as a morphism in `TopCat`. -/
abbrev manifoldBoundaryInclusion :
    TopCat.of (manifoldBoundary n M) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

end

section

variable (R : Type) [CommRing R]
variable (n : ℕ) [NeZero n]
variable (M : Type) [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]

/-- The relative homology group `H_n(M, ∂M; R)` as the Chapter 20 owner
`relativeTopHomologyGroup R n M ((𝓡∂ n).interior M)`. This keeps the textbook pair notation as a
thin bridge over the canonical current-repository surface. -/
abbrev boundaryRelativeSingularHomology : ModuleCat R :=
  relativeTopHomologyGroup R n M ((𝓡∂ n).interior M)

/-- Lean notation for the boundary-relative homology group `H_n(M, ∂M; R)`. -/
syntax "H[" term "](" term ", " "∂" term "; " term ")" : term

macro_rules
  | `(H[$n]($M, ∂$N; $R)) =>
      if M.raw == N.raw then
        `(boundaryRelativeSingularHomology $R $n $M)
      else
        Lean.Macro.throwUnsupported

/-- Unfolding `boundaryRelativeSingularHomology` gives the Chapter 20 owner for `H_n(M, ∂M; R)`. -/
theorem boundaryRelativeSingularHomology_eq_relativeTopHomologyGroup :
    H[n](M, ∂M; R) =
      relativeTopHomologyGroup R n M ((𝓡∂ n).interior M) :=
  rfl

/-- The complement of the manifold interior is canonically the boundary `∂M`. -/
private abbrev boundaryComplementHomeomorph :
    subspaceComplement M ((𝓡∂ n).interior M) ≃ₜ manifoldBoundary n M := by
  simpa [manifoldBoundary, subspaceComplement] using
    Homeomorph.setCongr ((𝓡∂ n).compl_interior)

/-- Singular homology identifies the complement `M \ interior(M)` with the boundary `∂M`. -/
private abbrev boundaryComplementSingularHomologyIso :
    rSingularHomology R (n - 1) (TopCat.of (subspaceComplement M ((𝓡∂ n).interior M))) ≅
      rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M)) :=
  (((singularHomologyFunctor (ModuleCat R) (n - 1)).obj (constantCoefficientModule R)).mapIso
    (TopCat.isoOfHomeo (boundaryComplementHomeomorph n M)))

/-- The singular-chain short complex `C_*(M \ interior(M)) ⟶ C_*(M) ⟶ C_*(M, ∂M)` defining the
Chapter 20 relative-homology owner `boundaryRelativeSingularHomology R n M`. Via
`boundaryComplementHomeomorph`, the first term is canonically `C_*(∂M)`. -/
abbrev boundaryRelativeSingularShortComplex :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  let F := (singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)
  let f := F.map (subspaceComplementInclusion M ((𝓡∂ n).interior M))
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

/-- The singular-chain short complex `C_*(M \ interior(M)) ⟶ C_*(M) ⟶ C_*(M, ∂M)` is short
exact. Via `boundaryComplementHomeomorph`, this is the short exact sequence
`C_*(∂M) ⟶ C_*(M) ⟶ C_*(M, ∂M)` used for the pair `(M, ∂M)`. -/
theorem boundaryRelativeSingularShortComplexShortExact :
    (boundaryRelativeSingularShortComplex R n M).ShortExact := sorry

/-- The connecting morphism produced by a proof that the boundary relative singular-chain short
complex is short exact, transported along the canonical identification
`M \ interior(M) ≃ ∂M`. -/
def boundaryRelativeSingularHomologyBoundaryOfShortExact
    (hS : (boundaryRelativeSingularShortComplex R n M).ShortExact) :
    H[n](M, ∂M; R) ⟶
      rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M)) :=
  hS.δ n (n - 1)
      (ComplexShape.down_mk n (n - 1)
        (Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_neZero n)))) ≫
    (boundaryComplementSingularHomologyIso R n M).hom

/-- A morphism `δ : H_n(M, ∂M; R) ⟶ H_(n - 1)(∂M; R)` is a boundary morphism for the pair
`(M, ∂M)` when it is the connecting morphism of the boundary relative singular-chain short exact
sequence `C_*(∂M) ⟶ C_*(M) ⟶ C_*(M, ∂M)`, expressed on the canonical Chapter 20 owner
`boundaryRelativeSingularHomology R n M`. -/
def IsBoundaryRelativeSingularHomologyBoundary
    (δ : H[n](M, ∂M; R) ⟶
      rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M))) : Prop :=
  ∃ hS : (boundaryRelativeSingularShortComplex R n M).ShortExact,
    boundaryRelativeSingularHomologyBoundaryOfShortExact R n M hS = δ

/-- Unfolding `IsBoundaryRelativeSingularHomologyBoundary` says that `δ` is exactly some
connecting morphism attached to a proof that the boundary relative singular-chain short exact
sequence `C_*(∂M) ⟶ C_*(M) ⟶ C_*(M, ∂M)` is short exact. -/
theorem isBoundaryRelativeSingularHomologyBoundary_iff
    (δ : H[n](M, ∂M; R) ⟶
      rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M))) :
    IsBoundaryRelativeSingularHomologyBoundary R n M δ ↔
      ∃ hS : (boundaryRelativeSingularShortComplex R n M).ShortExact,
        boundaryRelativeSingularHomologyBoundaryOfShortExact R n M hS = δ :=
  Iff.rfl

/-- A boundary morphism for `(M, ∂M)` comes from some proof that the boundary relative singular
chain short complex is short exact. -/
theorem IsBoundaryRelativeSingularHomologyBoundary.exists_shortExact
    {δ : H[n](M, ∂M; R) ⟶
      rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M))}
    (hδ : IsBoundaryRelativeSingularHomologyBoundary R n M δ) :
    ∃ hS : (boundaryRelativeSingularShortComplex R n M).ShortExact,
      boundaryRelativeSingularHomologyBoundaryOfShortExact R n M hS = δ :=
  hδ

end

section

variable {R : Type} [CommRing R]
variable {n : ℕ} [NeZero n]
variable {M : Type} [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]

/-- A relative class `z ∈ H_n(M, ∂M; R)` is a boundary relative fundamental class when, in the
Chapter 20 relative-homology owner, it is a fundamental class at the interior subspace
`(𝓡∂ n).interior M` in the sense of Definition 20.3.1. -/
abbrev IsBoundaryRelativeFundamentalClassFor
    (z : H[n](M, ∂M; R)) : Prop :=
  isFundamentalClassAtSubspace R n M ((𝓡∂ n).interior M) z

/-- Unfolding `IsBoundaryRelativeFundamentalClassFor z` expresses `z` as a fundamental class at
the interior subspace `(𝓡∂ n).interior M` in the Chapter 20 relative-homology owner. -/
theorem isBoundaryRelativeFundamentalClassFor_iff
    (z : H[n](M, ∂M; R)) :
    IsBoundaryRelativeFundamentalClassFor z ↔
      isFundamentalClassAtSubspace R n M ((𝓡∂ n).interior M) z :=
  Iff.rfl

/-- A boundary relative fundamental class is, by definition, a fundamental class at the interior
subspace `(𝓡∂ n).interior M`. -/
theorem IsBoundaryRelativeFundamentalClassFor.isFundamentalClassAtSubspace
    {z : H[n](M, ∂M; R)} (hz : IsBoundaryRelativeFundamentalClassFor z) :
    isFundamentalClassAtSubspace R n M ((𝓡∂ n).interior M) z :=
  hz

end

section

variable {R : Type} [CommRing R]
variable {n : ℕ} [NeZero n]
variable {M : Type} [TopologicalSpace M] [CompactSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]
variable [ROrientedManifoldWithBoundary R n M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) (manifoldBoundary n M)]
variable [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) = n - 1)]

/-- For a chosen proof that the boundary relative singular-chain short complex of `(M, ∂M)` is
short exact, every induced boundary fundamental class `zBoundary` on `∂M` has a unique relative
fundamental class whose boundary under the resulting connecting morphism is `zBoundary`. This is
the bridge theorem on the concrete canonical owner
`boundaryRelativeSingularHomologyBoundaryOfShortExact R n M hS`. -/
theorem existsUnique_boundaryRelativeFundamentalClass_of_boundaryRelativeShortExact
    (hS : (boundaryRelativeSingularShortComplex R n M).ShortExact)
    (zBoundary : rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M)))
    (hzBoundary : IsRFundamentalClassFor
      (ROrientedManifoldWithBoundary.toBoundaryROrientedManifold R n M) zBoundary) :
    ∃! z : H[n](M, ∂M; R),
      IsBoundaryRelativeFundamentalClassFor z ∧
        boundaryRelativeSingularHomologyBoundaryOfShortExact R n M hS z = zBoundary := sorry

/-- Proposition 21.4.3. If `M` is compact and `R`-oriented, then for every induced boundary
fundamental class `zBoundary` on `∂M`, and for every boundary morphism `δ` for the pair
`(M, ∂M)`, recorded by `IsBoundaryRelativeSingularHomologyBoundary R n M δ`, there exists a unique
relative fundamental class `z ∈ H_n(M, ∂M; R)`, recorded by
`IsBoundaryRelativeFundamentalClassFor z`, whose boundary under `δ` is `zBoundary`. -/
theorem existsUnique_boundaryRelativeFundamentalClass_of_rOrientedManifoldWithBoundary
    (δ : H[n](M, ∂M; R) ⟶
      rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M)))
    (hδ : IsBoundaryRelativeSingularHomologyBoundary R n M δ)
    (zBoundary : rSingularHomology R (n - 1) (TopCat.of (manifoldBoundary n M)))
    (hzBoundary : IsRFundamentalClassFor
      (ROrientedManifoldWithBoundary.toBoundaryROrientedManifold R n M) zBoundary) :
    ∃! z : H[n](M, ∂M; R),
      IsBoundaryRelativeFundamentalClassFor z ∧ δ z = zBoundary := by
  rcases hδ.exists_shortExact with ⟨hS, rfl⟩
  simpa using
    existsUnique_boundaryRelativeFundamentalClass_of_boundaryRelativeShortExact
      hS zBoundary hzBoundary

end
