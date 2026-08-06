import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Proposition_12_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_1_2
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

-- Semantic recall via `Definition_17_1_1`: `ModuleCat.tor` and `ModuleCat.torFunctor` are the
-- source-facing Chapter 17 surface for degree-one Tor, and `HomologicalComplex.tensorHom`
-- together with
-- `HomologicalComplex.homologyMap` gives the canonical coefficient-change map on
-- `homologyWithCoefficients`. Because this chapter's homology is `ℕ`-indexed, the faithful
-- formulation uses degree `n + 1` so that the right-hand term is `Tor(H_n(X), M)`.

/-- The left tensor term `H_(n + 1)(X) ⊗ M` in the nat-indexed universal coefficient sequence for
homology. -/
abbrev universalCoefficientHomologyTensorTerm
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    ModuleCat R :=
  X.homology (n + 1) ⊗ M

/-- `universalCoefficientHomologyTensorTerm R X M n` is the module `H_(n + 1)(X) ⊗ M`. -/
@[simp] theorem universalCoefficientHomologyTensorTerm_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    universalCoefficientHomologyTensorTerm R X M n = X.homology (n + 1) ⊗ M :=
  rfl

/-- The middle homology term `H_(n + 1)(X; M)` in the nat-indexed universal coefficient sequence
for homology. -/
abbrev universalCoefficientHomologyTerm
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    ModuleCat R :=
  homologyWithCoefficients R X M (n + 1)

/-- `universalCoefficientHomologyTerm R X M n` is the coefficient homology module
`H_(n + 1)(X; M)`. -/
@[simp] theorem universalCoefficientHomologyTerm_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    universalCoefficientHomologyTerm R X M n = homologyWithCoefficients R X M (n + 1) :=
  rfl

/-- The right `Tor` term `Tor(H_n(X), M)` in the nat-indexed universal coefficient sequence for
homology. -/
abbrev universalCoefficientHomologyTorTerm
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    ModuleCat R :=
  ModuleCat.tor R (X.homology n) M

/-- `universalCoefficientHomologyTorTerm R X M n` is the module `Tor(H_n(X), M)`. -/
@[simp] theorem universalCoefficientHomologyTorTerm_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    universalCoefficientHomologyTorTerm R X M n =
      ModuleCat.tor R (X.homology n) M :=
  rfl

/-- The tensor functor `M ↦ H_(n + 1)(X) ⊗ M` appearing on the left of the universal coefficient
sequence. -/
abbrev universalCoefficientHomologyTensorFunctor
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    ModuleCat R ⥤ ModuleCat R :=
  tensorLeft (X.homology (n + 1))

/-- Evaluating `universalCoefficientHomologyTensorFunctor R X n` at `M` gives
`universalCoefficientHomologyTensorTerm R X M n`. -/
@[simp] theorem universalCoefficientHomologyTensorFunctor_obj
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    (universalCoefficientHomologyTensorFunctor R X n).obj M =
      universalCoefficientHomologyTensorTerm R X M n :=
  rfl

/-- The `Tor` functor `M ↦ Tor(H_n(X), M)` appearing on the right of the universal coefficient
sequence. -/
abbrev universalCoefficientHomologyTorFunctor
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    ModuleCat R ⥤ ModuleCat R :=
  (ModuleCat.torFunctor R).obj (X.homology n)

/-- Evaluating `universalCoefficientHomologyTorFunctor R X n` at `M` gives
`universalCoefficientHomologyTorTerm R X M n`. -/
@[simp] theorem universalCoefficientHomologyTorFunctor_obj
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    (universalCoefficientHomologyTorFunctor R X n).obj M =
      universalCoefficientHomologyTorTerm R X M n :=
  rfl

/-- The canonical coefficient-change morphism on `H_(n + 1)(X; M)` induced by a map of
coefficient modules. -/
abbrev universalCoefficientHomologyCoefficientMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientHomologyTerm R X M n ⟶ universalCoefficientHomologyTerm R X N n :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f))
    (n + 1)

/-- `universalCoefficientHomologyCoefficientMap R X n f` is the homology map induced by
tensoring `𝟙 X` with the map of degree-zero coefficient complexes determined by `f`. -/
@[simp] theorem universalCoefficientHomologyCoefficientMap_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientHomologyCoefficientMap R X n f =
      HomologicalComplex.homologyMap
        (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f))
        (n + 1) :=
  rfl

/-- The canonical coefficient-change morphism on homology with coefficients respects identities.
-/
theorem universalCoefficientHomologyCoefficientMap_id
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (M : ModuleCat R) :
    universalCoefficientHomologyCoefficientMap R X n (𝟙 M) =
      𝟙 (universalCoefficientHomologyTerm R X M n) := by
  rw [universalCoefficientHomologyCoefficientMap_def]
  have htensor :
      HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R (𝟙 M)) =
        𝟙 (X ⊗ coefficientComplex R M) := by
    change (𝟙 X ⊗ₘ coefficientComplexMap R (𝟙 M)) = _
    simp [coefficientComplexMap]
  rw [htensor]
  exact HomologicalComplex.homologyMap_id (X ⊗ coefficientComplex R M) (n + 1)

/-- The canonical coefficient-change morphism on homology with coefficients respects
composition. -/
theorem universalCoefficientHomologyCoefficientMap_comp
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {L M N : ModuleCat R} (f : L ⟶ M) (g : M ⟶ N) :
    universalCoefficientHomologyCoefficientMap R X n (f ≫ g) =
      universalCoefficientHomologyCoefficientMap R X n f ≫
        universalCoefficientHomologyCoefficientMap R X n g := by
  rw [universalCoefficientHomologyCoefficientMap_def]
  rw [universalCoefficientHomologyCoefficientMap_def]
  rw [universalCoefficientHomologyCoefficientMap_def]
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  change X ◁ coefficientComplexMap R (f ≫ g) = _
  rw [show coefficientComplexMap R (f ≫ g) =
      coefficientComplexMap R f ≫ coefficientComplexMap R g by
    simp [coefficientComplexMap]]
  rw [whiskerLeft_comp]
  change X ◁ coefficientComplexMap R f ≫ X ◁ coefficientComplexMap R g =
    X ◁ coefficientComplexMap R f ≫ X ◁ coefficientComplexMap R g
  rfl

/-- A short exact sequence realizing the nat-indexed universal coefficient sequence for homology
in degree `n + 1`. -/
structure UniversalCoefficientHomologySequence
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) where
  tensorToHomology :
    universalCoefficientHomologyTensorTerm R X M n ⟶ universalCoefficientHomologyTerm R X M n
  homologyToTor :
    universalCoefficientHomologyTerm R X M n ⟶ universalCoefficientHomologyTorTerm R X M n
  zero : tensorToHomology ≫ homologyToTor = 0
  shortExact : (ShortComplex.mk tensorToHomology homologyToTor zero).ShortExact

namespace UniversalCoefficientHomologySequence

/-- The underlying short complex of a universal coefficient homology sequence. -/
abbrev toShortComplex
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {M : ModuleCat R} {n : ℕ}
    (S : UniversalCoefficientHomologySequence R X M n) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk S.tensorToHomology S.homologyToTor S.zero

/-- Coercion from a universal coefficient homology sequence to its underlying short complex. -/
instance instCoeOut
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {M : ModuleCat R} {n : ℕ} :
    CoeOut (UniversalCoefficientHomologySequence R X M n) (ShortComplex (ModuleCat R)) where
  coe S := S.toShortComplex

end UniversalCoefficientHomologySequence

/-- Helper for Theorem 17.1.3: the short complex underlying a chosen universal coefficient
homology sequence is short exact. -/
theorem UniversalCoefficientHomologySequence.toShortComplex_shortExact
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {M : ModuleCat R} {n : ℕ}
    (S : UniversalCoefficientHomologySequence R X M n) :
    S.toShortComplex.ShortExact := by
  -- This is exactly the short exactness field stored in the sequence package.
  exact S.shortExact

/-- A natural family of universal coefficient short exact sequences in the coefficient module
`M`, using the canonical coefficient-change maps on `H_(n + 1)(X; M)`. -/
structure UniversalCoefficientHomologyNaturality
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) where
  seq : ∀ M : ModuleCat R, UniversalCoefficientHomologySequence R X M n
  comm₁₂ :
    ∀ {M N : ModuleCat R} (f : M ⟶ N),
      (universalCoefficientHomologyTensorFunctor R X n).map f ≫ (seq N).tensorToHomology =
        (seq M).tensorToHomology ≫ universalCoefficientHomologyCoefficientMap R X n f
  comm₂₃ :
    ∀ {M N : ModuleCat R} (f : M ⟶ N),
      universalCoefficientHomologyCoefficientMap R X n f ≫ (seq N).homologyToTor =
        (seq M).homologyToTor ≫ (universalCoefficientHomologyTorFunctor R X n).map f

namespace UniversalCoefficientHomologyNaturality

/-- Coercion from a natural universal coefficient package to its family of short exact
sequences. -/
instance instCoeFun
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ} :
    CoeFun (UniversalCoefficientHomologyNaturality R X n)
      (fun _ ↦ ∀ M : ModuleCat R, UniversalCoefficientHomologySequence R X M n) where
  coe S := S.seq

/-- The middle morphism induced by a coefficient-module map in a universal coefficient package is
the canonical coefficient-change map on homology with coefficients. -/
abbrev homologyMap
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : UniversalCoefficientHomologyNaturality R X n)
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientHomologyTerm R X M n ⟶ universalCoefficientHomologyTerm R X N n :=
  let _ := S
  universalCoefficientHomologyCoefficientMap R X n f

/-- In a universal coefficient homology package, the coefficient-change map on the middle term
respects identities. -/
theorem map_id
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : UniversalCoefficientHomologyNaturality R X n) (M : ModuleCat R) :
    S.homologyMap (𝟙 M) = 𝟙 (universalCoefficientHomologyTerm R X M n) := by
  change universalCoefficientHomologyCoefficientMap R X n (𝟙 M) =
    𝟙 (universalCoefficientHomologyTerm R X M n)
  exact universalCoefficientHomologyCoefficientMap_id R X n M

/-- In a universal coefficient homology package, the coefficient-change map on the middle term
respects composition. -/
theorem map_comp
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : UniversalCoefficientHomologyNaturality R X n)
    {L M N : ModuleCat R} (f : L ⟶ M) (g : M ⟶ N) :
    S.homologyMap (f ≫ g) = S.homologyMap f ≫ S.homologyMap g := by
  change universalCoefficientHomologyCoefficientMap R X n (f ≫ g) =
    universalCoefficientHomologyCoefficientMap R X n f ≫
      universalCoefficientHomologyCoefficientMap R X n g
  exact universalCoefficientHomologyCoefficientMap_comp R X n f g

/-- The morphism of short complexes induced by a coefficient-module morphism. -/
def map
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : UniversalCoefficientHomologyNaturality R X n)
    {M N : ModuleCat R} (f : M ⟶ N) :
    (S M).toShortComplex ⟶ (S N).toShortComplex :=
  ShortComplex.homMk
    ((universalCoefficientHomologyTensorFunctor R X n).map f)
    (S.homologyMap f)
    ((universalCoefficientHomologyTorFunctor R X n).map f)
    (S.comm₁₂ f)
    (S.comm₂₃ f)

end UniversalCoefficientHomologyNaturality

/-- Helper for Theorem 17.1.3: each fixed-coefficient short complex extracted from a natural
universal coefficient package is short exact. -/
theorem UniversalCoefficientHomologyNaturality.shortExact
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (S : UniversalCoefficientHomologyNaturality R X n) (M : ModuleCat R) :
    ((S M).toShortComplex).ShortExact := by
  -- Evaluate the package at `M` and read off the stored short exactness witness.
  exact (S M).shortExact

/-- Helper for Theorem 17.1.3: `boundaryModule R X n` is the textbook boundary module
`B_(n - 1)(X)`, realized as the range of the canonical map from degree `n` chains to
`(n - 1)`-cycles. -/
private abbrev boundaryModule
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    ModuleCat R :=
  ModuleCat.of R
    (LinearMap.range
      (ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n))))

/-- Helper for Theorem 17.1.3: the canonical inclusion of
`boundaryModule R X n = B_(n - 1)(X)` into `X.cycles ((ComplexShape.down ℕ).next n)`. -/
private abbrev boundaryInclusion
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    boundaryModule R X n ⟶ X.cycles ((ComplexShape.down ℕ).next n) :=
  ModuleCat.ofHom
    (LinearMap.range
      (ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n)))).subtype

/-- Helper for Theorem 17.1.3: the canonical surjection from degree `n` chains onto the boundary
module `boundaryModule R X n`. -/
private def toBoundary
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    X.X n ⟶ boundaryModule R X n :=
  ModuleCat.ofHom
    ((ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n))).codRestrict
      (LinearMap.range
        (ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n))))
      (fun x ↦ ⟨x, rfl⟩))

/-- Helper for Theorem 17.1.3: composing the boundary projection with the boundary inclusion
recovers the canonical map from chains to cycles. -/
@[reassoc, simp] private theorem toBoundary_comp_boundaryInclusion
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    toBoundary R X n ≫ boundaryInclusion R X n =
      X.toCycles n ((ComplexShape.down ℕ).next n) := by
  -- Both morphisms are the same codomain restriction of `X.toCycles`.
  rfl

/-- Helper for Theorem 17.1.3: the boundary projection is surjective because the target is
defined as the range of the underlying linear map. -/
private theorem toBoundary_surjective
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    Function.Surjective (toBoundary R X n) := by
  -- Unpack an element of the range and reuse its defining preimage.
  intro y
  rcases y.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

/-- Helper for Theorem 17.1.3: cycles map to zero in the boundary module because their
image under the differential vanishes. -/
@[reassoc, simp] private theorem iCycles_comp_toBoundary
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    X.iCycles n ≫ toBoundary R X n = 0 := by
  -- Local instance justification (non-inferable subtype mono): `boundaryInclusion R X n` is the
  -- subtype map of a linear range, so we register its injectivity locally to use
  -- `cancel_mono`.
  letI : Mono (boundaryInclusion R X n) :=
    (ModuleCat.mono_iff_injective _).2 (fun _ _ h ↦ Subtype.ext h)
  -- Postcompose with the boundary inclusion to recover the genuine map into cycles.
  apply (cancel_mono (boundaryInclusion R X n)).1
  rw [Category.assoc, toBoundary_comp_boundaryInclusion]
  -- Then postcompose with the cycles inclusion and reduce to `iCycles ≫ d = 0`.
  apply (cancel_mono (X.iCycles ((ComplexShape.down ℕ).next n))).1
  simpa [Category.assoc, HomologicalComplex.toCycles_i] using
    (HomologicalComplex.iCycles_d
      (K := X) (i := n) (j := (ComplexShape.down ℕ).next n))

/-- Helper for Theorem 17.1.3: the degreewise sequence
`0 ⟶ Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X) ⟶ 0` is exact on underlying modules. -/
private theorem iCycles_exact_toBoundary
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    Function.Exact (X.iCycles n) (toBoundary R X n) := by
  -- Translate the kernel condition for `toBoundary` into the kernel of `(X.sc n).g`,
  -- then return to the abstract cycles object via `moduleCatCyclesIso`.
  intro x
  constructor
  · intro hx
    have htoCycles :
        ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n)) x = 0 := by
      simpa using congrArg (ModuleCat.Hom.hom (boundaryInclusion R X n)) hx
    have hxker' :
        ModuleCat.Hom.hom
            (X.toCycles n ((ComplexShape.down ℕ).next n) ≫
              X.iCycles ((ComplexShape.down ℕ).next n)) x = 0 := by
      change ModuleCat.Hom.hom (X.iCycles ((ComplexShape.down ℕ).next n))
          (ModuleCat.Hom.hom (X.toCycles n ((ComplexShape.down ℕ).next n)) x) = 0
      simpa using congrArg
        (ModuleCat.Hom.hom (X.iCycles ((ComplexShape.down ℕ).next n))) htoCycles
    have hxker : ModuleCat.Hom.hom ((X.sc n).g) x = 0 := by
      simpa [HomologicalComplex.toCycles_i] using hxker'
    let xKer : (X.sc n).moduleCatLeftHomologyData.K := ⟨x, hxker⟩
    refine ⟨ModuleCat.Hom.hom (X.sc n).moduleCatCyclesIso.inv xKer, ?_⟩
    -- Apply the concrete cycles inclusion and then cancel the comparison isomorphism.
    simpa using congrArg
      (fun f ↦ ModuleCat.Hom.hom f xKer)
      (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_iCycles (S := X.sc n))
  · rintro ⟨γ, rfl⟩
    -- The short complex was built so that boundaries vanish on cycles.
    simpa using
      (CategoryTheory.ShortComplex.moduleCat_zero_apply
        (S := ShortComplex.mk (X.iCycles n) (toBoundary R X n) (iCycles_comp_toBoundary R X n))
        γ)

/-- Helper for Theorem 17.1.3: the normalized cycle-boundary sequence
`0 ⟶ Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X) ⟶ 0` is short exact. -/
private def cycleBoundaryShortComplex
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next n)] :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (X.iCycles n) (toBoundary R X n)
    (iCycles_comp_toBoundary R X n)

/-- Helper for Theorem 17.1.3: the cycle-boundary short complex is short exact. -/
private theorem cycleBoundaryShortComplexShortExact
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (cycleBoundaryShortComplex R X n).ShortExact := by
  -- Package the normalized exactness, injectivity, and surjectivity data.
  refine ModuleCat.shortComplex_shortExact (cycleBoundaryShortComplex R X n) ?_ ?_ ?_
  · simpa [cycleBoundaryShortComplex] using iCycles_exact_toBoundary R X n
  · simpa [cycleBoundaryShortComplex] using
      (ModuleCat.mono_iff_injective (X.iCycles n)).1 (inferInstance : Mono (X.iCycles n))
  · simpa [cycleBoundaryShortComplex] using toBoundary_surjective R X n

/-- Helper for Theorem 17.1.3: the cycle-boundary row `Z_n(X) ⟶ X_n ⟶ B_(n - 1)(X)` is exact.
-/
private theorem cycleBoundaryShortComplexExact
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (cycleBoundaryShortComplex R X n).Exact := by
  -- Extract the exactness field from the previously packaged short exact sequence.
  exact (cycleBoundaryShortComplexShortExact R X n).exact

/-- Helper for Theorem 17.1.3: tensoring the cycle-boundary row on the right by a flat module
preserves exactness. -/
private theorem cycleBoundaryTensorExactOfFlat
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (M : ModuleCat R)
    [Module.Flat R M] :
    ((cycleBoundaryShortComplex R X n).map (tensorRight M)).Exact := by
  -- This is the exactness input used when the coefficient module is replaced by a flat
  -- projective-resolution term.
  exact Module.Flat.rTensor_shortComplex_exact M
    (cycleBoundaryShortComplex R X n)
    (cycleBoundaryShortComplexExact R X n)

/-- Helper for Theorem 17.1.3: if the degree-`n` chain group is flat over the domain `R`, then
the cycle module `X.cycles n` is torsion-free because it injects into `X.X n`. -/
private theorem cyclesIsTorsionFreeOfFlatChainGroups
    (R : Type u) [CommRing R] [IsDomain R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    Module.IsTorsionFree R (X.cycles n) := by
  let f : X.cycles n → X.X n := ModuleCat.Hom.hom (X.iCycles n)
  have hf : Function.Injective f := by
    -- The cycle inclusion is monic, hence injective on underlying modules.
    exact (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (X.iCycles n))
  have hXTorsionFree : Module.IsTorsionFree R (X.X n) := by
    -- Flat modules over a domain have trivial torsion.
    rw [Submodule.isTorsionFree_iff_torsion_eq_bot]
    exact Module.Flat.torsion_eq_bot (R := R) (M := X.X n)
  -- Pull torsion-freeness back along the cycle inclusion.
  exact hf.moduleIsTorsionFree f
    (fun r x ↦ (ModuleCat.Hom.hom (X.iCycles n)).map_smul r x)

/-- Helper for Theorem 17.1.3: over a PID, flat chain groups force the cycle module `X.cycles n`
to be flat as well. -/
private theorem cyclesFlatOfFlatChainGroups
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    Module.Flat R (X.cycles n) := by
  -- Over a PID, flatness is equivalent to torsion-freeness.
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact cyclesIsTorsionFreeOfFlatChainGroups R X n hX

/-- Helper for Theorem 17.1.3: a boundary cycle represents the zero homology class. -/
@[reassoc, simp] private theorem boundaryInclusion_comp_homologyπ
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (k : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next k)] :
    boundaryInclusion R X k ≫ X.homologyπ ((ComplexShape.down ℕ).next k) = 0 := by
  -- Unpack a boundary element as an actual image under `X.toCycles`, then use the standard
  -- vanishing of boundaries in homology.
  ext y
  rcases y with ⟨y, ⟨x, hx⟩⟩
  change ModuleCat.Hom.hom (X.homologyπ ((ComplexShape.down ℕ).next k)) y = 0
  rw [← hx]
  have hzero :
      ModuleCat.Hom.hom
          (X.toCycles k ((ComplexShape.down ℕ).next k) ≫
            X.homologyπ ((ComplexShape.down ℕ).next k)) =
        ModuleCat.Hom.hom
          (0 : X.X k ⟶ X.homology ((ComplexShape.down ℕ).next k)) := by
    exact congrArg ModuleCat.Hom.hom
      (HomologicalComplex.toCycles_comp_homologyπ
        (K := X) (i := k) (j := (ComplexShape.down ℕ).next k))
  have hzeroEval :
      ModuleCat.Hom.hom
          (X.toCycles k ((ComplexShape.down ℕ).next k) ≫
            X.homologyπ ((ComplexShape.down ℕ).next k)) x =
        ModuleCat.Hom.hom
          (0 : X.X k ⟶ X.homology ((ComplexShape.down ℕ).next k)) x := by
    exact congrArg (fun f ↦ f x) hzero
  exact hzeroEval

/-- Helper for Theorem 17.1.3: the canonical short complex
`B_(k - 1)(X) ⟶ Z_(k - 1)(X) ⟶ H_(k - 1)(X)`. -/
private def boundaryCyclesHomologyShortComplex
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (k : ℕ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℕ).next k)] :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (boundaryInclusion R X k)
    (X.homologyπ ((ComplexShape.down ℕ).next k))
    (boundaryInclusion_comp_homologyπ R X k)

/-- Helper for Theorem 17.1.3: the normalized row
`B_n(X) ⟶ Z_n(X) ⟶ H_n(X)` is exact on underlying modules. -/
private theorem boundaryInclusion_exact_homologyπ
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    Function.Exact
      (boundaryInclusion R X (n + 1))
      (X.homologyπ ((ComplexShape.down ℕ).next (n + 1))) := by
  let m : ℕ := (ComplexShape.down ℕ).next (n + 1)
  let S := X.sc m
  intro z
  constructor
  · intro hz
    -- Route correction: move to the concrete quotient model of `X.sc n` before extracting a
    -- boundary witness, rather than trying to compare the two range owners directly.
    -- Rewriting through `moduleCatHomologyIso` turns vanishing in homology into quotient-zero.
    have hzConcrete :
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.π
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z) = 0 := by
      have hzIso :
          ModuleCat.Hom.hom (X.homologyπ m ≫ S.moduleCatHomologyIso.hom) z = 0 := by
        change ModuleCat.Hom.hom S.moduleCatHomologyIso.hom
            (ModuleCat.Hom.hom (X.homologyπ m) z) = 0
        rw [hz]
        simpa using (LinearMap.map_zero (ModuleCat.Hom.hom S.moduleCatHomologyIso.hom))
      have hπEval :
          ModuleCat.Hom.hom (X.homologyπ m ≫ S.moduleCatHomologyIso.hom) z =
            ModuleCat.Hom.hom (S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π) z := by
        exact congrArg
          (fun f ↦ ModuleCat.Hom.hom f z)
          (by simpa [S] using
            (CategoryTheory.ShortComplex.π_moduleCatCyclesIso_hom (S := S)))
      rw [hπEval] at hzIso
      simpa using hzIso
    have hzRange :
        ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z ∈ LinearMap.range S.moduleCatToCycles := by
      exact
        (Submodule.Quotient.mk_eq_zero
          (p := LinearMap.range S.moduleCatToCycles)
          (x := ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z)).1 <| by
            simpa [S] using hzConcrete
    rcases hzRange with ⟨x, hx⟩
    have hCyclesIso_injective :
        Function.Injective (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom) :=
      (ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance
    -- Transport the concrete range witness back to the project owner `boundaryModule`.
    have htoCycles :
        ModuleCat.Hom.hom S.toCycles x = z := by
      apply hCyclesIso_injective
      change ModuleCat.Hom.hom (S.toCycles ≫ S.moduleCatCyclesIso.hom) x =
        ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z
      rw [CategoryTheory.ShortComplex.toCycles_moduleCatCyclesIso_hom (S := S)]
      simpa using hx
    have hprev : (ComplexShape.down ℕ).prev m = n + 1 := by
      dsimp [m]
      rw [ChainComplex.next_nat_succ, ChainComplex.prev]
    let x₀ : X.X ((ComplexShape.down ℕ).prev m) := x
    let x' : X.X (n + 1) :=
      ModuleCat.Hom.hom (X.XIsoOfEq hprev).hom x₀
    have htoCycles' :
        ModuleCat.Hom.hom (X.toCycles (n + 1) m) x' = z := by
      apply (ModuleCat.mono_iff_injective (X.iCycles m)).1 inferInstance
      have hleft :
          ModuleCat.Hom.hom (X.iCycles m)
              (ModuleCat.Hom.hom (X.toCycles (n + 1) m) x') =
            ModuleCat.Hom.hom (X.d (n + 1) m) x' := by
        change ModuleCat.Hom.hom (X.toCycles (n + 1) m ≫ X.iCycles m) x' = _
        simpa using congrArg
          (fun f ↦ ModuleCat.Hom.hom f x')
          (HomologicalComplex.toCycles_i (K := X) (i := n + 1) (j := m))
      have htransport :
          ModuleCat.Hom.hom (X.d (n + 1) m) x' =
            ModuleCat.Hom.hom S.f x := by
        dsimp [x', x₀]
        change ModuleCat.Hom.hom ((X.XIsoOfEq hprev).hom ≫ X.d (n + 1) m) _ =
          ModuleCat.Hom.hom S.f x
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d (K := X) hprev m]
        rfl
      have hshort :
          ModuleCat.Hom.hom S.f x =
            ModuleCat.Hom.hom S.iCycles (ModuleCat.Hom.hom S.toCycles x) := by
        change ModuleCat.Hom.hom S.f x =
          ModuleCat.Hom.hom (S.toCycles ≫ S.iCycles) x
        simpa using
          (congrArg
            (fun f ↦ ModuleCat.Hom.hom f x)
            (CategoryTheory.ShortComplex.toCycles_i (S := S))).symm
      have hcycles :
          ModuleCat.Hom.hom S.iCycles (ModuleCat.Hom.hom S.toCycles x) =
            ModuleCat.Hom.hom S.iCycles z := by
        simpa using congrArg (ModuleCat.Hom.hom S.iCycles) htoCycles
      have hiCycles :
          ModuleCat.Hom.hom S.iCycles z =
            ModuleCat.Hom.hom (X.iCycles m) z := by
        rfl
      exact hleft.trans (htransport.trans (hshort.trans (hcycles.trans hiCycles)))
    have htoCyclesNext :
        ModuleCat.Hom.hom
            (X.toCycles (n + 1) ((ComplexShape.down ℕ).next (n + 1))) x' = z := by
      simpa [m, ChainComplex.next_nat_succ] using htoCycles'
    refine ⟨⟨z, ?_⟩, rfl⟩
    exact ⟨x', htoCyclesNext⟩
  · rintro ⟨y, rfl⟩
    -- Evaluating the short-complex zero relation shows every boundary cycle maps to zero.
    simpa [boundaryCyclesHomologyShortComplex] using
      (CategoryTheory.ShortComplex.moduleCat_zero_apply
        (S := boundaryCyclesHomologyShortComplex R X (n + 1))
        y)

/-- Helper for Theorem 17.1.3: the normalized row
`B_n(X) ⟶ Z_n(X) ⟶ H_n(X)` is short exact. -/
private theorem boundaryCyclesHomologyShortExact
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesHomologyShortComplex R X (n + 1)).ShortExact := by
  -- Package exactness with the obvious injective/surjective endpoint maps.
  refine ModuleCat.shortComplex_shortExact
    (boundaryCyclesHomologyShortComplex R X (n + 1)) ?_ ?_ ?_
  · simpa [boundaryCyclesHomologyShortComplex, ChainComplex.next_nat_succ] using
      boundaryInclusion_exact_homologyπ R X n
  · -- The boundary inclusion is the subtype embedding of a linear-map range.
    show Function.Injective (boundaryInclusion R X (n + 1))
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    exact Subtype.ext hxy
  · -- Homology is defined as a cokernel, so `homologyπ` is an epimorphism.
    have hsurj :
        Function.Surjective (X.homologyπ ((ComplexShape.down ℕ).next (n + 1))) := by
      exact (ModuleCat.epi_iff_surjective
        (X.homologyπ ((ComplexShape.down ℕ).next (n + 1)))).1 inferInstance
    simpa [boundaryCyclesHomologyShortComplex] using hsurj

/-- Helper for Theorem 17.1.3: the normalized row `B_n(X) ⟶ Z_n(X) ⟶ H_n(X)` is exact. -/
private theorem boundaryCyclesHomologyExact
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesHomologyShortComplex R X (n + 1)).Exact := by
  -- Extract the exactness field from the short exact packaging of the normalized row.
  exact (boundaryCyclesHomologyShortExact R X n).exact

/-- Helper for Theorem 17.1.3: tensoring the normalized boundary-cycles-homology row on the
right by a flat module preserves exactness. -/
private theorem boundaryCyclesHomologyTensorExactOfFlat
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (M : ModuleCat R)
    [HomologicalComplex.HasHomology X n] [Module.Flat R M] :
    ((boundaryCyclesHomologyShortComplex R X (n + 1)).map (tensorRight M)).Exact := by
  -- This is the owner-level exactness statement needed before deriving the Tor row in the
  -- coefficient variable.
  exact Module.Flat.rTensor_shortComplex_exact M
    (boundaryCyclesHomologyShortComplex R X (n + 1))
    (boundaryCyclesHomologyExact R X n)

/-- Helper for Theorem 17.1.3: over a PID, flat chain groups force the boundary module
`boundaryModule R X k` to be flat. -/
private theorem boundaryModuleFlatOfFlatChainGroups
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (k : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    Module.Flat R (boundaryModule R X k) := by
  -- First pull torsion-freeness back from the ambient cycle module along the boundary inclusion.
  let f : boundaryModule R X k → X.cycles ((ComplexShape.down ℕ).next k) :=
    ModuleCat.Hom.hom (boundaryInclusion R X k)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext hxy
  have hCyclesTorsionFree :
      Module.IsTorsionFree R (X.cycles ((ComplexShape.down ℕ).next k)) := by
    exact cyclesIsTorsionFreeOfFlatChainGroups R X ((ComplexShape.down ℕ).next k) hX
  have hBoundaryTorsionFree :
      Module.IsTorsionFree R (boundaryModule R X k) := by
    exact hf.moduleIsTorsionFree f
      (fun r x ↦ (ModuleCat.Hom.hom (boundaryInclusion R X k)).map_smul r x)
  -- Over a PID, torsion-free modules are flat.
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact hBoundaryTorsionFree

/-- Helper for Theorem 17.1.3: tensor a module on the left with the chosen projective resolution
of `M` degreewise. -/
private abbrev tensorProjectiveResolutionFunctor
    (R : Type u) [CommRing R] (M : ModuleCat R) :
    ModuleCat R ⥤ ChainComplex (ModuleCat R) ℕ where
  obj A := (((tensoringLeft (ModuleCat R)).obj A).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (CategoryTheory.projectiveResolution M).complex
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map f)
    (ComplexShape.down ℕ)).app (CategoryTheory.projectiveResolution M).complex
  map_id A := by
    ext n x
    simp
  map_comp f g := by
    ext n x
    simp

/-- Helper for Theorem 17.1.3: the tensor-projective-resolution functor preserves zero
morphisms. -/
private instance tensorProjectiveResolutionFunctor_preservesZeroMorphisms
    (R : Type u) [CommRing R] (M : ModuleCat R) :
    (tensorProjectiveResolutionFunctor R M).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext n x
    simp [tensorProjectiveResolutionFunctor]
    rfl

/-- Helper for Theorem 17.1.3: tensoring the normalized row
`B_n(X) ⟶ Z_n(X) ⟶ H_n(X)` degreewise with the chosen projective resolution of `M`. -/
private abbrev boundaryCyclesResolutionShortComplex
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  (boundaryCyclesHomologyShortComplex R X (n + 1)).map
    (tensorProjectiveResolutionFunctor R M)

/-- Helper for Theorem 17.1.3: evaluating the tensor-projective-resolution row in degree `i`
recovers tensoring the normalized row with the projective-resolution term `P_i`. -/
private theorem boundaryCyclesResolutionShortComplex_map_eval
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n i : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionShortComplex R X M n).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) i) =
      (boundaryCyclesHomologyShortComplex R X (n + 1)).map
        (tensorRight ((CategoryTheory.projectiveResolution M).complex.X i)) :=
  rfl

/-- Helper for Theorem 17.1.3: the degreewise tensor of
`B_n(X) ⟶ Z_n(X) ⟶ H_n(X)` with the chosen projective resolution of `M` is short exact as a row
of chain complexes. -/
private theorem boundaryCyclesResolutionShortExact
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionShortComplex R X M n).ShortExact := by
  -- Evaluate in each degree so the existing flat-tensor short exactness owner applies.
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  haveI : Module.Flat R ((CategoryTheory.projectiveResolution M).complex.X i) := by
    infer_instance
  letI :
      Limits.PreservesFiniteLimits
        (tensorRight ((CategoryTheory.projectiveResolution M).complex.X i)) :=
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso
      (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight
        ((CategoryTheory.projectiveResolution M).complex.X i))
  letI :
      Limits.PreservesFiniteColimits
        (tensorRight ((CategoryTheory.projectiveResolution M).complex.X i)) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso
      (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight
        ((CategoryTheory.projectiveResolution M).complex.X i))
  simpa [boundaryCyclesResolutionShortComplex_map_eval] using
    (boundaryCyclesHomologyShortExact R X n).map_of_exact
      (tensorRight ((CategoryTheory.projectiveResolution M).complex.X i))

/-- Helper for Theorem 17.1.3: tensoring the chosen projective resolution of `M` on the left by
a flat module is exact at degree `1`. -/
private theorem tensorProjectiveResolutionExactAtOneOfFlat
    (R : Type u) [CommRing R] (A M : ModuleCat R) [Module.Flat R A] :
    ((((tensoringLeft (ModuleCat R)).obj A).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        (CategoryTheory.projectiveResolution M).complex).ExactAt 1 := by
  -- Rewrite exactness at degree `1` to the visible short complex
  -- `A ⊗ P₂ ⟶ A ⊗ P₁ ⟶ A ⊗ P₀`.
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  simpa using
    Module.Flat.lTensor_shortComplex_exact A
      (ShortComplex.mk
        ((CategoryTheory.projectiveResolution M).complex.d 2 1)
        ((CategoryTheory.projectiveResolution M).complex.d 1 0)
        ((CategoryTheory.projectiveResolution M).complex.d_comp_d 2 1 0))
      ((CategoryTheory.projectiveResolution M).exact_succ 0)

/-- Helper for Theorem 17.1.3: degree-`0` homology of `A ⊗ P•` computes the ordinary tensor
product `A ⊗ M`, where `P•` is the chosen projective resolution of `M`. -/
private noncomputable def tensorProjectiveResolutionH0IsoTensor
    (R : Type u) [CommRing R] (A M : ModuleCat R) :
    ((((tensoringLeft (ModuleCat R)).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryTheory.projectiveResolution M).complex).homology 0 ≅
      A ⊗ M := by
  let F : ModuleCat R ⥤ ModuleCat R := (tensoringLeft (ModuleCat R)).obj A
  -- First compute the left derived tensor functor on the chosen projective resolution, then use
  -- right exactness of tensoring to return to the ordinary tensor product.
  simpa [F] using
    ((CategoryTheory.projectiveResolution M).isoLeftDerivedObj F 0).symm ≪≫
      (CategoryTheory.Functor.leftDerivedZeroIsoSelf F).app M

/-- Helper for Theorem 17.1.3: degree-`1` homology of `A ⊗ P•` computes `Tor(A, M)`, where
`P•` is the chosen projective resolution of `M`. -/
private noncomputable def tensorProjectiveResolutionH1IsoTor
    (R : Type u) [CommRing R] (A M : ModuleCat R) :
    ((((tensoringLeft (ModuleCat R)).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryTheory.projectiveResolution M).complex).homology 1 ≅
      ModuleCat.tor R A M := by
  let F : ModuleCat R ⥤ ModuleCat R := (tensoringLeft (ModuleCat R)).obj A
  -- By definition, `Tor(A, M)` is the first left derived tensor functor evaluated at `M`.
  simpa [ModuleCat.tor_def, ModuleCat.torFunctor_def, F] using
    ((CategoryTheory.projectiveResolution M).isoLeftDerivedObj F 1).symm

/-- Helper for Theorem 17.1.3: if the left module `A` is flat, then `Tor(A, M)` vanishes. -/
private theorem moduleCatTorIsZeroOfFlatLeft
    (R : Type u) [CommRing R] (A M : ModuleCat R) [Module.Flat R A] :
    CategoryTheory.Limits.IsZero (ModuleCat.tor R A M) := by
  -- Compute `Tor(A, M)` by the chosen projective resolution and kill the resulting `H₁` term by
  -- exactness of `A ⊗ P•`.
  refine CategoryTheory.Limits.IsZero.of_iso ?_ (tensorProjectiveResolutionH1IsoTor R A M).symm
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact tensorProjectiveResolutionExactAtOneOfFlat R A M

/-- Helper for Theorem 17.1.3: the degree-`1` tensor-projective-resolution term for the cycle
module vanishes because the cycle module is flat. -/
private theorem tensorProjectiveResolutionH1IsZeroCycles
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    CategoryTheory.Limits.IsZero
      (((((tensoringLeft (ModuleCat R)).obj
            (X.cycles ((ComplexShape.down ℕ).next (n + 1)))).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution M).complex).homology
        1) := by
  -- First turn flatness of cycles into Tor-vanishing, then transport back to the `H₁` owner.
  letI : Module.Flat R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) :=
    cyclesFlatOfFlatChainGroups R X ((ComplexShape.down ℕ).next (n + 1)) hX
  exact CategoryTheory.Limits.IsZero.of_iso
    (moduleCatTorIsZeroOfFlatLeft
      R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M)
    (tensorProjectiveResolutionH1IsoTor
      R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M)

/-- Helper for Theorem 17.1.3: the degree-`1` tensor-projective-resolution term for the boundary
module vanishes because the boundary module is flat. -/
private theorem tensorProjectiveResolutionH1IsZeroBoundary
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    CategoryTheory.Limits.IsZero
      (((((tensoringLeft (ModuleCat R)).obj
            (boundaryModule R X (n + 1))).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution M).complex).homology
        1) := by
  -- Apply the same flat-left Tor vanishing argument to the boundary module.
  letI : Module.Flat R (boundaryModule R X (n + 1)) :=
    boundaryModuleFlatOfFlatChainGroups R X (n + 1) hX
  exact CategoryTheory.Limits.IsZero.of_iso
    (moduleCatTorIsZeroOfFlatLeft R (boundaryModule R X (n + 1)) M)
    (tensorProjectiveResolutionH1IsoTor R (boundaryModule R X (n + 1)) M)

/-- Helper for Theorem 17.1.3: the middle four-term homology row extracted from the degree-`0`
five-arrow segment of `boundaryCyclesResolutionShortExact`. Its objects are the raw homology terms
`H₁(H_n(X) ⊗ P•)`, `H₀(B_n(X) ⊗ P•)`, `H₀(Z_n(X) ⊗ P•)`, and `H₀(H_n(X) ⊗ P•)`. -/
private noncomputable def boundaryCyclesResolutionHomologyRow
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    ComposableArrows (ModuleCat R) 3 := by
  let rawFive :=
    shortExactChainComplexHomologyComposableArrows₅
      (boundaryCyclesResolutionShortComplex R X M n)
      (boundaryCyclesResolutionShortExact R X M n) 0
  -- This isolates the middle row before any Tor/tensor transport is attempted.
  exact ComposableArrows.mk₃
    (rawFive.map' 2 3)
    (rawFive.map' 3 4)
    (rawFive.map' 4 5)

/-- Helper for Theorem 17.1.3: the raw middle homology row extracted from
`boundaryCyclesResolutionShortExact` is exact. -/
private theorem boundaryCyclesResolutionHomologyRow_exact
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionHomologyRow R X M n).Exact := by
  let rawFive :=
    shortExactChainComplexHomologyComposableArrows₅
      (boundaryCyclesResolutionShortComplex R X M n)
      (boundaryCyclesResolutionShortExact R X M n) 0
  let rawRow : ComposableArrows (ModuleCat R) 3 := ComposableArrows.mk₃
    (rawFive.map' 2 3)
    (rawFive.map' 3 4)
    (rawFive.map' 4 5)
  have hRawFive : rawFive.Exact := by
    -- Start from the degree-`0` five-arrow segment of the long exact sequence attached to the
    -- boundary-cycles-homology short exact row tensored with the chosen projective resolution.
    simpa [rawFive] using
      shortExactChainComplexHomologyExactFiveTerm
        (boundaryCyclesResolutionShortComplex R X M n)
        (boundaryCyclesResolutionShortExact R X M n) 0
  have hRawRow : rawRow.Exact := by
    -- Route correction: isolate the middle four-term exact row before transporting it to the
    -- textbook Tor/tensor terms, instead of mixing exactness and transport in one proof.
    simpa [rawRow] using (hRawFive.δ₀).δ₀
  simpa [boundaryCyclesResolutionHomologyRow, rawFive] using hRawRow

/-- Helper for Theorem 17.1.3: transport the raw projective-resolution homology row to the
textbook `Tor/tensor` row
`Tor(H_n(X), M) ⟶ B_n(X) ⊗ M ⟶ Z_n(X) ⊗ M ⟶ H_n(X) ⊗ M`. -/
private noncomputable abbrev boundaryCyclesResolutionTransportedRow
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    ComposableArrows (ModuleCat R) 3 := by
  let raw := boundaryCyclesResolutionHomologyRow R X M n
  exact ComposableArrows.mk₃
    ((tensorProjectiveResolutionH1IsoTor
        R (X.homology ((ComplexShape.down ℕ).next (n + 1))) M).inv ≫
      raw.map' 0 1 ≫
      (tensorProjectiveResolutionH0IsoTensor R (boundaryModule R X (n + 1)) M).hom)
    ((tensorProjectiveResolutionH0IsoTensor R (boundaryModule R X (n + 1)) M).inv ≫
      raw.map' 1 2 ≫
        (tensorProjectiveResolutionH0IsoTensor
          R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M).hom)
    ((tensorProjectiveResolutionH0IsoTensor
        R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M).inv ≫
      raw.map' 2 3 ≫
      (tensorProjectiveResolutionH0IsoTensor
        R (X.homology ((ComplexShape.down ℕ).next (n + 1))) M).hom)

/-- Helper for Theorem 17.1.3: the transported `Tor/tensor` row is exact. -/
private theorem boundaryCyclesResolutionTransportedRowExact
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionTransportedRow R X M n).Exact := by
  let raw := boundaryCyclesResolutionHomologyRow R X M n
  let e₀ :=
    tensorProjectiveResolutionH1IsoTor
      R (X.homology ((ComplexShape.down ℕ).next (n + 1))) M
  let e₁ := tensorProjectiveResolutionH0IsoTensor R (boundaryModule R X (n + 1)) M
  let e₂ :=
    tensorProjectiveResolutionH0IsoTensor
      R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M
  let e₃ :=
    tensorProjectiveResolutionH0IsoTensor
      R (X.homology ((ComplexShape.down ℕ).next (n + 1))) M
  let target : ComposableArrows (ModuleCat R) 3 := ComposableArrows.mk₃
    (e₀.inv ≫ raw.map' 0 1 ≫ e₁.hom)
    (e₁.inv ≫ raw.map' 1 2 ≫ e₂.hom)
    (e₂.inv ≫ raw.map' 2 3 ≫ e₃.hom)
  have hRaw : raw.Exact := by
    -- Start from the already isolated exact row on the raw homology objects.
    simpa [raw] using boundaryCyclesResolutionHomologyRow_exact R X M n
  have e : raw ≅ target := by
    -- Route correction: transport the whole row once, instead of rewriting each map separately
    -- inside the final universal coefficient construction.
    refine ComposableArrows.isoMk₃
      e₀ e₁ e₂ e₃
      ?_ ?_ ?_
    · -- The first arrow is defined by conjugating the raw connecting map through the
      -- `H₁ ≅ Tor` and `H₀ ≅ tensor` identifications.
      change raw.map' 0 1 ≫ e₁.hom = e₀.hom ≫ (e₀.inv ≫ raw.map' 0 1 ≫ e₁.hom)
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl
    · -- The middle arrow is the same raw homology map rewritten through the adjacent `H₀`
      -- identifications.
      change raw.map' 1 2 ≫ e₂.hom = e₁.hom ≫ (e₁.inv ≫ raw.map' 1 2 ≫ e₂.hom)
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl
    · -- The last arrow is again the raw homology map transported through the `H₀` tensor
      -- identifications on cycles and homology.
      change raw.map' 2 3 ≫ e₃.hom = e₂.hom ≫ (e₂.inv ≫ raw.map' 2 3 ≫ e₃.hom)
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl
  -- Fold the local transport row back to the named Chapter 17 owner.
  change target.Exact
  exact ComposableArrows.exact_of_iso e hRaw

/-- Helper for Theorem 17.1.3: the left map
`Tor(H_n(X), M) ⟶ B_n(X) ⊗ M` in the transported row is monic because the preceding
`H₁(Z_n(X) ⊗ P•)` term in the exact five-term sequence vanishes. -/
private theorem boundaryCyclesResolutionTransportedRow_monoFirst
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    [HomologicalComplex.HasHomology X n] :
    Mono ((boundaryCyclesResolutionTransportedRow R X M n).map' 0 1) := by
  let rawFive :=
    shortExactChainComplexHomologyComposableArrows₅
      (boundaryCyclesResolutionShortComplex R X M n)
      (boundaryCyclesResolutionShortExact R X M n) 0
  have hRawFive : rawFive.Exact := by
    -- Start from the exact five-term sequence attached to the tensor-projective-resolution row.
    simpa [rawFive] using
      shortExactChainComplexHomologyExactFiveTerm
        (boundaryCyclesResolutionShortComplex R X M n)
        (boundaryCyclesResolutionShortExact R X M n) 0
  have hZeroCycles :
      CategoryTheory.Limits.IsZero (rawFive.obj 1) := by
    -- Route correction: isolate the vanishing `H₁(Z_n(X) ⊗ P•)` owner before applying
    -- `Exact.mono_g`, instead of trying to prove monicity after transporting the whole row.
    change CategoryTheory.Limits.IsZero
      (((((tensoringLeft (ModuleCat R)).obj
              (X.cycles ((ComplexShape.down ℕ).next (n + 1)))).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution M).complex).homology 1)
    exact tensorProjectiveResolutionH1IsZeroCycles R X M n hX
  have hZeroMap : rawFive.map' 1 2 = 0 := by
    -- Any map out of a zero object is the zero morphism.
    exact hZeroCycles.eq_of_src _ _
  have hMonoRaw : Mono (rawFive.map' 2 3) := by
    -- Exactness at `Tor(H_n(X), M)` turns the zero previous map into monicity of the next one.
    exact (hRawFive.exact' 1 2 3).mono_g hZeroMap
  have hMonoHomologyRow :
      Mono ((boundaryCyclesResolutionHomologyRow R X M n).map' 0 1) := by
    -- The raw homology row was defined by taking this middle segment of the five-term sequence.
    simpa [boundaryCyclesResolutionHomologyRow, rawFive] using hMonoRaw
  -- Transport monicity through the comparison isomorphisms one composition at a time so instance
  -- search does not have to reconstruct the whole composite owner at once.
  let e₀ :=
    tensorProjectiveResolutionH1IsoTor
      R (X.homology ((ComplexShape.down ℕ).next (n + 1))) M
  let e₁ := tensorProjectiveResolutionH0IsoTensor R (boundaryModule R X (n + 1)) M
  -- Local instance justification (transported mono owner): the visible map is the composite of
  -- `e₀.inv`, the already proved monic raw middle map, and `e₁.hom`, so we register that
  -- composite monicity explicitly instead of relying on a brittle whole-term search.
  have hMonoLeftComposite :
      Mono (e₀.inv ≫ (boundaryCyclesResolutionHomologyRow R X M n).map' 0 1) := by
    exact mono_comp' (inferInstance : Mono e₀.inv) hMonoHomologyRow
  have hMonoVisible :
      Mono ((e₀.inv ≫ (boundaryCyclesResolutionHomologyRow R X M n).map' 0 1) ≫ e₁.hom) := by
    exact mono_comp' hMonoLeftComposite (inferInstance : Mono e₁.hom)
  change Mono ((e₀.inv ≫ (boundaryCyclesResolutionHomologyRow R X M n).map' 0 1) ≫ e₁.hom)
  exact hMonoVisible

/-- Helper for Theorem 17.1.3: the visible `(k, 0)` summand map in the tensor complex is
natural in the coefficient module. -/
private theorem homologyTensorZeroSummandNaturality
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) {M N : ModuleCat R} (f : M ⟶ N) (k : ℕ) :
    ((X.iCycles k ⊗ₘ 𝟙 M) ≫
        HomologicalComplex.ιTensorObj X (coefficientComplex R M) k 0 k rfl) ≫
        (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)).f k =
      (X.iCycles k ⊗ₘ f) ≫
        HomologicalComplex.ιTensorObj X (coefficientComplex R N) k 0 k rfl := by
  -- Route correction: normalize the `(k, 0)` summand once at the owner level before using it in
  -- the cycle-level naturality proof.
  have hι :
      HomologicalComplex.ιTensorObj X (coefficientComplex R M) k 0 k rfl ≫
          (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)).f k =
        ((𝟙 (X.X k)) ⊗ₘ f) ≫
          HomologicalComplex.ιTensorObj X (coefficientComplex R N) k 0 k rfl := by
    simpa only [coefficientComplexMap] using
      (GradedObject.Monoidal.ι_tensorHom
        (𝟙 X.X) (coefficientComplexMap R f).f k 0 k rfl)
  calc
    ((X.iCycles k ⊗ₘ 𝟙 M) ≫
          HomologicalComplex.ιTensorObj X (coefficientComplex R M) k 0 k rfl) ≫
          (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)).f k =
        (X.iCycles k ⊗ₘ 𝟙 M) ≫
          (HomologicalComplex.ιTensorObj X (coefficientComplex R M) k 0 k rfl ≫
            (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)).f k) := by
          simp [Category.assoc]
    _ =
        ((X.iCycles k ⊗ₘ 𝟙 M) ≫
          ((𝟙 (X.X k)) ⊗ₘ f)) ≫
            HomologicalComplex.ιTensorObj X (coefficientComplex R N) k 0 k rfl := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ (X.iCycles k ⊗ₘ 𝟙 M) ≫ t) hι
    _ =
        (X.iCycles k ⊗ₘ f) ≫
          HomologicalComplex.ιTensorObj X (coefficientComplex R N) k 0 k rfl := by
          rw [tensorHom_comp_tensorHom]
          simp

/-- Helper for Theorem 17.1.3: the cycle-level tensor comparison is natural in the coefficient
module. -/
private theorem homologyTensorCycleMapNatural
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) {M N : ModuleCat R} (f : M ⟶ N) (k : ℕ)
    [HomologicalComplex.HasHomology X k]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) k]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R N) k] :
    (𝟙 (X.cycles k) ⊗ₘ f) ≫ homologyTensorCycleMap R X N k =
      homologyTensorCycleMap R X M k ≫
        HomologicalComplex.cyclesMap
          (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)) k := by
  -- Compare both sides after postcomposing with the target cycles inclusion.
  apply (cancel_mono ((X ⊗ coefficientComplex R N).iCycles k)).1
  calc
    ((𝟙 (X.cycles k) ⊗ₘ f) ≫ homologyTensorCycleMap R X N k) ≫
          (X ⊗ coefficientComplex R N).iCycles k =
        (𝟙 (X.cycles k) ⊗ₘ f) ≫
          (homologyTensorCycleMap R X N k ≫
            (X ⊗ coefficientComplex R N).iCycles k) := by
          simp [Category.assoc]
    _ =
        (𝟙 (X.cycles k) ⊗ₘ f) ≫
          ((X.iCycles k ⊗ₘ 𝟙 N) ≫
            HomologicalComplex.ιTensorObj X (coefficientComplex R N) k 0 k rfl) := by
          rw [(homologyTensorCycleMap_iCycles R X N k).w]
    _ =
        ((𝟙 (X.cycles k) ⊗ₘ f) ≫ (X.iCycles k ⊗ₘ 𝟙 N)) ≫
          HomologicalComplex.ιTensorObj X (coefficientComplex R N) k 0 k rfl := by
          simp [Category.assoc]
    _ =
        (X.iCycles k ⊗ₘ f) ≫
          HomologicalComplex.ιTensorObj X (coefficientComplex R N) k 0 k rfl := by
          rw [tensorHom_comp_tensorHom]
          simp
    _ =
        ((X.iCycles k ⊗ₘ 𝟙 M) ≫
          HomologicalComplex.ιTensorObj X (coefficientComplex R M) k 0 k rfl) ≫
            (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)).f k := by
          symm
          exact homologyTensorZeroSummandNaturality R X f k
    _ =
        (homologyTensorCycleMap R X M k ≫ (X ⊗ coefficientComplex R M).iCycles k) ≫
          (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)).f k := by
          rw [(homologyTensorCycleMap_iCycles R X M k).w]
    _ =
        homologyTensorCycleMap R X M k ≫
          ((X ⊗ coefficientComplex R M).iCycles k ≫
            (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)).f k) := by
          simp [Category.assoc]
    _ =
        homologyTensorCycleMap R X M k ≫
          (HomologicalComplex.cyclesMap
              (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)) k ≫
            (X ⊗ coefficientComplex R N).iCycles k) := by
          exact congrArg (fun t ↦ homologyTensorCycleMap R X M k ≫ t)
            (HomologicalComplex.cyclesMap_i
              (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)) k).symm
    _ =
        (homologyTensorCycleMap R X M k ≫
          HomologicalComplex.cyclesMap
            (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)) k) ≫
            (X ⊗ coefficientComplex R N).iCycles k := by
          rw [← Category.assoc]

/-- Helper for Theorem 17.1.3: factor the source tensor map through the cycle-level
coefficient-change morphism before applying `homologyTensorComparison_spec`. -/
private theorem homologyProjectionTensorMapFactor
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) {M N : ModuleCat R} (f : M ⟶ N) (k : ℕ) :
    (X.homologyπ k ⊗ₘ f) =
      (𝟙 (X.cycles k) ⊗ₘ f) ≫ (X.homologyπ k ⊗ₘ 𝟙 N) := by
  -- Normalize the tensor functor map into the exact factorization used by the cycle-level square.
  rw [tensorHom_comp_tensorHom]
  simp

/-- Helper for Theorem 17.1.3: `homologyTensorComparison` is natural in the coefficient module.
-/
private theorem homologyTensorComparisonNaturalPrecomp
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    ((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
        (universalCoefficientHomologyTensorFunctor R X n).map f ≫
        homologyTensorComparison R X N (n + 1)) =
      ((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
        homologyTensorComparison R X M (n + 1) ≫
        universalCoefficientHomologyCoefficientMap R X n f) := by
  -- Route correction: rewrite the source tensor map into the cycle-level spelling consumed by
  -- `homologyTensorComparison_spec` before descending to homology classes.
  calc
    ((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
          (universalCoefficientHomologyTensorFunctor R X n).map f ≫
          homologyTensorComparison R X N (n + 1)) =
        ((X.homologyπ (n + 1) ⊗ₘ f) ≫
          homologyTensorComparison R X N (n + 1)) := by
          -- First collapse the tensor-functor composition on the source.
          have hmap :
              (X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
                  (universalCoefficientHomologyTensorFunctor R X n).map f =
                X.homologyπ (n + 1) ⊗ₘ f := by
            change
              ((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
                  ((𝟙 (X.homology (n + 1))) ⊗ₘ f)) =
                X.homologyπ (n + 1) ⊗ₘ f
            rw [tensorHom_comp_tensorHom]
            simp
          change
            (((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
                (universalCoefficientHomologyTensorFunctor R X n).map f) ≫
              homologyTensorComparison R X N (n + 1)) =
            ((X.homologyπ (n + 1) ⊗ₘ f) ≫
              homologyTensorComparison R X N (n + 1))
          rw [hmap]
          rfl
    _ =
        ((𝟙 (X.cycles (n + 1)) ⊗ₘ f) ≫
          (X.homologyπ (n + 1) ⊗ₘ 𝟙 N) ≫
            homologyTensorComparison R X N (n + 1)) := by
          -- Put the source map into the exact normal form needed by the comparison square.
          rw [homologyProjectionTensorMapFactor R X f (n + 1)]
          rw [Category.assoc]
    _ =
        ((𝟙 (X.cycles (n + 1)) ⊗ₘ f) ≫
          homologyTensorCycleMap R X N (n + 1) ≫
            (X ⊗ coefficientComplex R N).homologyπ (n + 1)) := by
          -- Replace the target comparison map by its defining quotient square.
          rw [(homologyTensorComparison_spec R X N (n + 1)).w]
    _ =
        (homologyTensorCycleMap R X M (n + 1) ≫
          HomologicalComplex.cyclesMap
              (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)) (n + 1) ≫
            (X ⊗ coefficientComplex R N).homologyπ (n + 1)) := by
          -- Naturality is already proved on cycles, so move the coefficient change there first.
          rw [← Category.assoc]
          rw [homologyTensorCycleMapNatural R X f (n + 1)]
          rw [Category.assoc]
    _ =
        (homologyTensorCycleMap R X M (n + 1) ≫
          (X ⊗ coefficientComplex R M).homologyπ (n + 1) ≫
            universalCoefficientHomologyCoefficientMap R X n f) := by
          -- Then identify the induced map on homology with the canonical coefficient-change map.
          have hπ :
              HomologicalComplex.cyclesMap
                  (HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f)) (n + 1) ≫
                (X ⊗ coefficientComplex R N).homologyπ (n + 1) =
              (X ⊗ coefficientComplex R M).homologyπ (n + 1) ≫
                universalCoefficientHomologyCoefficientMap R X n f := by
            simpa only [universalCoefficientHomologyCoefficientMap_def] using
              (HomologicalComplex.homologyπ_naturality
                (φ := HomologicalComplex.tensorHom (𝟙 X) (coefficientComplexMap R f))
                (i := n + 1)).symm
          simpa only [Category.assoc] using
            congrArg (fun t ↦ homologyTensorCycleMap R X M (n + 1) ≫ t) hπ
    _ =
        ((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
          homologyTensorComparison R X M (n + 1) ≫
            universalCoefficientHomologyCoefficientMap R X n f) := by
          -- Finally fold the cycle-level square back into the source comparison map.
          rw [← Category.assoc]
          rw [← (homologyTensorComparison_spec R X M (n + 1)).w]
          rw [Category.assoc]

/-- Helper for Theorem 17.1.3: `homologyTensorComparison` is natural in the coefficient module.
-/
private theorem homologyTensorComparisonNatural
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    (universalCoefficientHomologyTensorFunctor R X n).map f ≫
        homologyTensorComparison R X N (n + 1) =
      homologyTensorComparison R X M (n + 1) ≫
        universalCoefficientHomologyCoefficientMap R X n f := by
  -- Compare the two morphisms on arbitrary homology tensors by pulling representatives back along
  -- the surjective quotient map from cycles to homology.
  apply ModuleCat.hom_ext
  ext z
  have hsurj :
      Function.Surjective (X.homologyπ (n + 1)).hom := by
    exact (ModuleCat.epi_iff_surjective (X.homologyπ (n + 1))).mp inferInstance
  have htensorSurj :
      Function.Surjective ((X.homologyπ (n + 1) ⊗ₘ 𝟙 M).hom) := by
    simpa using LinearMap.rTensor_surjective (Q := M) hsurj
  obtain ⟨w, rfl⟩ := htensorSurj z
  -- Evaluate both sides on the chosen representative and use the precomposed square.
  have hpre :=
    ModuleCat.hom_ext_iff.mp (homologyTensorComparisonNaturalPrecomp R X n f)
  change
    (((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
        (universalCoefficientHomologyTensorFunctor R X n).map f ≫
        homologyTensorComparison R X N (n + 1)).hom w) =
      (((X.homologyπ (n + 1) ⊗ₘ 𝟙 M) ≫
          homologyTensorComparison R X M (n + 1) ≫
          universalCoefficientHomologyCoefficientMap R X n f).hom w)
  exact DFunLike.congr_fun hpre w

/-- Helper for Theorem 17.1.3: a pointwise family of short exact sequences together with the two
canonical coefficient-change squares packages into `UniversalCoefficientHomologyNaturality`. -/
private def mkUniversalCoefficientHomologyNaturality
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (seq : ∀ M : ModuleCat R, UniversalCoefficientHomologySequence R X M n)
    (comm₁₂ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        (universalCoefficientHomologyTensorFunctor R X n).map f ≫ (seq N).tensorToHomology =
          (seq M).tensorToHomology ≫ universalCoefficientHomologyCoefficientMap R X n f)
    (comm₂₃ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        universalCoefficientHomologyCoefficientMap R X n f ≫ (seq N).homologyToTor =
          (seq M).homologyToTor ≫ (universalCoefficientHomologyTorFunctor R X n).map f) :
    UniversalCoefficientHomologyNaturality R X n where
  -- This isolates the final assembly step so the main theorem only has to supply the pointwise
  -- short exact sequences and the two canonical naturality squares.
  seq := seq
  comm₁₂ := comm₁₂
  comm₂₃ := comm₂₃

/-- Helper for Theorem 17.1.3: once the pointwise short exact sequences and the two canonical
coefficient-change squares are constructed, the universal coefficient package exists. -/
private theorem nonempty_universalCoefficientHomologyNaturality_of_data
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    (seq : ∀ M : ModuleCat R, UniversalCoefficientHomologySequence R X M n)
    (comm₁₂ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        (universalCoefficientHomologyTensorFunctor R X n).map f ≫ (seq N).tensorToHomology =
          (seq M).tensorToHomology ≫ universalCoefficientHomologyCoefficientMap R X n f)
    (comm₂₃ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        universalCoefficientHomologyCoefficientMap R X n f ≫ (seq N).homologyToTor =
          (seq M).homologyToTor ≫ (universalCoefficientHomologyTorFunctor R X n).map f) :
    Nonempty (UniversalCoefficientHomologyNaturality R X n) := by
  -- Package the pointwise data into the naturality structure, then witness nonemptiness.
  exact ⟨mkUniversalCoefficientHomologyNaturality seq comm₁₂ comm₂₃⟩

/-- Helper for Theorem 17.1.3: normalize the first map in the transported
`Tor ⟶ B_n(X) ⊗ M ⟶ Z_n(X) ⊗ M ⟶ H_n(X) ⊗ M` row. -/
private theorem boundaryCyclesResolutionTransportedRow_map01
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionTransportedRow R X M n).map' 0 1 =
      (tensorProjectiveResolutionH1IsoTor
          R (X.homology ((ComplexShape.down ℕ).next (n + 1))) M).inv ≫
        (boundaryCyclesResolutionHomologyRow R X M n).map' 0 1 ≫
        (tensorProjectiveResolutionH0IsoTensor R (boundaryModule R X (n + 1)) M).hom :=
  rfl

/-- Helper for Theorem 17.1.3: normalize the middle map in the transported
`Tor ⟶ B_n(X) ⊗ M ⟶ Z_n(X) ⊗ M ⟶ H_n(X) ⊗ M` row. -/
private theorem boundaryCyclesResolutionTransportedRow_map12
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionTransportedRow R X M n).map' 1 2 =
      (tensorProjectiveResolutionH0IsoTensor R (boundaryModule R X (n + 1)) M).inv ≫
        (boundaryCyclesResolutionHomologyRow R X M n).map' 1 2 ≫
        (tensorProjectiveResolutionH0IsoTensor
          R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M).hom :=
  rfl

/-- Helper for Theorem 17.1.3: the transported middle map is the `H₀` map induced by
`boundaryInclusion R X (n + 1)` after the standard `H₀ ≅ - ⊗ M` transports. -/
private theorem boundaryCyclesResolutionTransportedRow_map12_eq_h0Map
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionTransportedRow R X M n).map' 1 2 =
      (tensorProjectiveResolutionH0IsoTensor R (boundaryModule R X (n + 1)) M).inv ≫
        HomologicalComplex.homologyMap
          ((tensorProjectiveResolutionFunctor R M).map (boundaryInclusion R X (n + 1)))
          0 ≫
        (tensorProjectiveResolutionH0IsoTensor
          R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M).hom := by
  -- This is the explicit `H₀` spelling of the second arrow in the extracted five-term row.
  rfl

/-- Helper for Theorem 17.1.3: the degree-`0` left-derived tensor map induced by `f`
is computed by the homology map of the chosen tensor-projective-resolution chain map. -/
private theorem tensorProjectiveResolutionLeftDerivedMap_eq
    (R : Type u) [CommRing R] {A B : ModuleCat R} (f : A ⟶ B) (M : ModuleCat R) :
    (NatTrans.leftDerived ((tensoringLeft (ModuleCat R)).map f) 0).app M =
      ((CategoryTheory.projectiveResolution M).isoLeftDerivedObj
          ((tensoringLeft (ModuleCat R)).obj A) 0).hom ≫
        HomologicalComplex.homologyMap ((tensorProjectiveResolutionFunctor R M).map f) 0 ≫
          ((CategoryTheory.projectiveResolution M).isoLeftDerivedObj
            ((tensoringLeft (ModuleCat R)).obj B) 0).inv := by
  -- Compute the left-derived map on the chosen projective resolution of `M`.
  simpa [tensorProjectiveResolutionFunctor] using
    (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
      (α := ((tensoringLeft (ModuleCat R)).map f))
      (P := CategoryTheory.projectiveResolution M) (n := 0))

/-- Helper for Theorem 17.1.3: after the standard `H₀ ≅ - ⊗ M` transports, the middle map in the
transported row is literally `boundaryInclusion R X (n + 1) ⊗ₘ 𝟙 M`. -/
private theorem boundaryCyclesResolutionTransportedRow_map12_eq_boundaryTensor
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionTransportedRow R X M n).map' 1 2 =
      boundaryInclusion R X (n + 1) ⊗ₘ 𝟙 M := by
  -- First expose the transported middle map as the degree-`0` left-derived tensor map attached
  -- to `boundaryInclusion R X (n + 1)`.
  rw [boundaryCyclesResolutionTransportedRow_map12_eq_h0Map]
  have hdesc :
      HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex
                ((tensoringLeft (ModuleCat R)).map (boundaryInclusion R X (n + 1)))
                (ComplexShape.down ℕ)).app
              (CategoryTheory.projectiveResolution M).complex)
            0 ≫
        (CategoryTheory.projectiveResolution M).fromLeftDerivedZero'
          ((tensoringLeft (ModuleCat R)).obj (X.cycles ((ComplexShape.down ℕ).next (n + 1)))) =
      (CategoryTheory.projectiveResolution M).fromLeftDerivedZero'
          ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1))) ≫
        (boundaryInclusion R X (n + 1) ⊗ₘ 𝟙 M) := by
    dsimp [CategoryTheory.ProjectiveResolution.fromLeftDerivedZero']
    rw [HomologicalComplex.opcyclesMap_comp_descOpcycles]
    apply (cancel_epi
      (((((tensoringLeft (ModuleCat R)).obj
            (boundaryModule R X (n + 1))).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution M).complex).pOpcycles 0)).1
    rw [HomologicalComplex.p_descOpcycles, HomologicalComplex.p_descOpcycles_assoc]
    simpa [Category.assoc] using
      (((tensoringLeft (ModuleCat R)).map (boundaryInclusion R X (n + 1))).naturality
        ((CategoryTheory.projectiveResolution M).π.f 0)).symm
  -- Then rewrite the derived-level comparison through the chosen projective resolution and
  -- collapse the two standard `H₀ ≅ opcycles₀` identifications.
  have hnatural :
      (((CategoryTheory.Functor.leftDerivedZeroIsoSelf
            ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).inv ≫
          (NatTrans.leftDerived
              ((tensoringLeft (ModuleCat R)).map (boundaryInclusion R X (n + 1))) 0).app M ≫
            ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                ((tensoringLeft (ModuleCat R)).obj
                  (X.cycles ((ComplexShape.down ℕ).next (n + 1))))).app M).hom) =
        boundaryInclusion R X (n + 1) ⊗ₘ 𝟙 M := by
    have hmiddle :
        (NatTrans.leftDerived
            ((tensoringLeft (ModuleCat R)).map (boundaryInclusion R X (n + 1))) 0).app M ≫
          ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
              ((tensoringLeft (ModuleCat R)).obj
                (X.cycles ((ComplexShape.down ℕ).next (n + 1))))).app M).hom =
        ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
            ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).hom ≫
          (boundaryInclusion R X (n + 1) ⊗ₘ 𝟙 M) := by
      simp
      rw [CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          (P := CategoryTheory.projectiveResolution M)
          (α := ((tensoringLeft (ModuleCat R)).map (boundaryInclusion R X (n + 1))))]
      rw [CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq
          (P := CategoryTheory.projectiveResolution M)
          (F := (tensoringLeft (ModuleCat R)).obj
            (X.cycles ((ComplexShape.down ℕ).next (n + 1))))]
      rw [CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq
          (P := CategoryTheory.projectiveResolution M)
          (F := (tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))]
      simp [Category.assoc]
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1))).mapHomologicalComplex
                  (ComplexShape.down ℕ)).obj
                (CategoryTheory.projectiveResolution M).complex).homologyι 0) ≫
              t)
          hdesc
    have hpre :
        (((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).inv ≫
              (NatTrans.leftDerived
                  ((tensoringLeft (ModuleCat R)).map (boundaryInclusion R X (n + 1))) 0).app M) ≫
            ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                ((tensoringLeft (ModuleCat R)).obj
                  (X.cycles ((ComplexShape.down ℕ).next (n + 1))))).app M).hom =
          ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).inv ≫
              (((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                  ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).hom ≫
                (boundaryInclusion R X (n + 1) ⊗ₘ 𝟙 M)) := by
      simpa [Category.assoc] using congrArg
        (fun t ↦
          ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
              ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).inv ≫
            t)
        hmiddle
    have hpre' :
        ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).inv ≫
              (NatTrans.leftDerived
                  ((tensoringLeft (ModuleCat R)).map (boundaryInclusion R X (n + 1))) 0).app M ≫
                ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                    ((tensoringLeft (ModuleCat R)).obj
                      (X.cycles ((ComplexShape.down ℕ).next (n + 1))))).app M).hom =
          ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).inv ≫
              ((CategoryTheory.Functor.leftDerivedZeroIsoSelf
                  ((tensoringLeft (ModuleCat R)).obj (boundaryModule R X (n + 1)))).app M).hom ≫
                (boundaryInclusion R X (n + 1) ⊗ₘ 𝟙 M) := by
      simpa [Category.assoc] using hpre
    rw [hpre']
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simpa only [tensorProjectiveResolutionH0IsoTensor, tensorProjectiveResolutionLeftDerivedMap_eq,
    Category.assoc] using hnatural

/-- Helper for Theorem 17.1.3: normalize the last map in the transported
`Tor ⟶ B_n(X) ⊗ M ⟶ Z_n(X) ⊗ M ⟶ H_n(X) ⊗ M` row. -/
private theorem boundaryCyclesResolutionTransportedRow_map23
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (boundaryCyclesResolutionTransportedRow R X M n).map' 2 3 =
      (tensorProjectiveResolutionH0IsoTensor
          R (X.cycles ((ComplexShape.down ℕ).next (n + 1))) M).inv ≫
        (boundaryCyclesResolutionHomologyRow R X M n).map' 2 3 ≫
        (tensorProjectiveResolutionH0IsoTensor
          R (X.homology ((ComplexShape.down ℕ).next (n + 1))) M).hom :=
  rfl

/-- Helper for Theorem 17.1.3: a fixed-coefficient right edge can be packaged together with its
zero relation and short exactness on the public Chapter 17 surface. -/
private theorem fixedCoefficientRightEdgeShortExactData
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    ∃ homologyToTor :
        universalCoefficientHomologyTerm R X M n ⟶ universalCoefficientHomologyTorTerm R X M n,
      ∃ zero :
          homologyTensorComparison R X M (n + 1) ≫ homologyToTor = 0,
        (ShortComplex.mk
            (homologyTensorComparison R X M (n + 1))
            homologyToTor
            zero).ShortExact := by
  -- Route correction: expose the public right edge first, then let every concrete quotient-model
  -- map be obtained by precomposing with `moduleCatLeftHomologyData.π`.
  -- TODO: use `boundaryCyclesResolutionTransportedRow_map01/map12/map23` to keep the
  -- transported row on the raw-owner surface, then construct the missing concrete
  -- `((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.K ⟶
  -- boundaryModule R X (n + 1) ⊗ M` bridge whose composite with the normalized `map' 1 2`
  -- vanishes; after that, descend once to the public right edge and package short exactness.
  sorry

/-- Helper for Theorem 17.1.3: the missing right-hand morphism from homology with coefficients to
`Tor(H_n(X), M)` for a fixed coefficient module `M`. -/
private noncomputable def fixedCoefficientHomologyToTor
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    universalCoefficientHomologyTerm R X M n ⟶ universalCoefficientHomologyTorTerm R X M n :=
  -- Read the public right edge from the single packaged short-exact-data theorem.
  Classical.choose (fixedCoefficientRightEdgeShortExactData R X n hX M)

/-- Helper for Theorem 17.1.3: the concrete quotient-model owner of the right edge is obtained by
precomposing the public right edge with the target cycles quotient. -/
private noncomputable def fixedCoefficientCyclesToTor
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.K ⟶
      universalCoefficientHomologyTorTerm R X M n :=
  -- Keep the concrete quotient-model owner secondary to the public right edge.
  ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.π ≫
    ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatHomologyIso.inv ≫
      fixedCoefficientHomologyToTor R X n hX M

/-- Helper for Theorem 17.1.3: the concrete `K → Tor` owner kills coefficient boundaries because
the quotient map `π` already kills them before the public right edge is applied. -/
private theorem fixedCoefficientCyclesToTor_desc_zero
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.f' ≫
        fixedCoefficientCyclesToTor R X n hX M = 0 := by
  -- The adapter begins with `π`, so coefficient boundaries vanish before any Tor map appears.
  have hπ :
      ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.f' ≫
          ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.π =
        0 := by
    simpa using
      (((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.f'_π)
  -- Postcompose the concrete quotient-model zero relation with the public right edge adapter.
  calc
    ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.f' ≫
          fixedCoefficientCyclesToTor R X n hX M =
        ((((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.f' ≫
              ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.π) ≫
            ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatHomologyIso.inv) ≫
          fixedCoefficientHomologyToTor R X n hX M := by
            simp only [fixedCoefficientCyclesToTor, Category.assoc]
    _ = 0 := by
          rw [hπ, Category.assoc]
          exact CategoryTheory.Limits.zero_comp

/-- Helper for Theorem 17.1.3: descend the concrete quotient-model map `K ⟶ Tor` to the
concrete homology quotient `H`. -/
private noncomputable def fixedCoefficientConcreteHomologyToTor
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.H ⟶
      universalCoefficientHomologyTorTerm R X M n :=
  ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.descH
    (fixedCoefficientCyclesToTor R X n hX M)
    (fixedCoefficientCyclesToTor_desc_zero R X n hX M)

/-- Helper for Theorem 17.1.3: the descended concrete homology map restricts to the concrete
quotient-model `K ⟶ Tor` map after precomposing with `π`. -/
private theorem fixedCoefficientConcreteHomologyToTor_spec
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.π ≫
        fixedCoefficientConcreteHomologyToTor R X n hX M =
      fixedCoefficientCyclesToTor R X n hX M := by
  -- The defining property of `descH` records the descended map on the quotient owner.
  rw [fixedCoefficientConcreteHomologyToTor]
  exact CategoryTheory.ShortComplex.LeftHomologyData.π_descH
    (h := ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData)
    (k := fixedCoefficientCyclesToTor R X n hX M)
    (hk := fixedCoefficientCyclesToTor_desc_zero R X n hX M)

/-- Helper for Theorem 17.1.3: precomposing the descended right edge with the coefficient
homology quotient recovers the concrete target-side `K → Tor` owner. -/
private theorem fixedCoefficientHomologyToTor_spec
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    (X ⊗ coefficientComplex R M).homologyπ (n + 1) ≫
        fixedCoefficientHomologyToTor R X n hX M =
      ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.hom ≫
        fixedCoefficientCyclesToTor R X n hX M := by
  -- Insert the concrete cycles comparison isomorphism once, then rewrite the quotient map to the
  -- explicit `K ⟶ H` presentation used by the adapter.
  have hinsert :
      ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.hom ≫
          (((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.inv ≫
            (X ⊗ coefficientComplex R M).homologyπ (n + 1)) ≫
            fixedCoefficientHomologyToTor R X n hX M =
        (X ⊗ coefficientComplex R M).homologyπ (n + 1) ≫
          fixedCoefficientHomologyToTor R X n hX M := by
    calc
      ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.hom ≫
            (((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.inv ≫
              (X ⊗ coefficientComplex R M).homologyπ (n + 1)) ≫
              fixedCoefficientHomologyToTor R X n hX M =
          ((((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.hom ≫
                ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.inv) ≫
                  (X ⊗ coefficientComplex R M).homologyπ (n + 1)) ≫
                fixedCoefficientHomologyToTor R X n hX M := by
            simpa only [Category.assoc]
      _ =
          (X ⊗ coefficientComplex R M).homologyπ (n + 1) ≫
            fixedCoefficientHomologyToTor R X n hX M := by
            rw [Iso.hom_inv_id, Category.id_comp]
            rfl
  have hπ :
      ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.inv ≫
          (X ⊗ coefficientComplex R M).homologyπ (n + 1) =
        ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatLeftHomologyData.π ≫
          ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatHomologyIso.inv := by
    simpa only using
      (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_π
        (S := (X ⊗ coefficientComplex R M).sc (n + 1)))
  calc
    (X ⊗ coefficientComplex R M).homologyπ (n + 1) ≫
          fixedCoefficientHomologyToTor R X n hX M =
        ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.hom ≫
          (((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.inv ≫
            (X ⊗ coefficientComplex R M).homologyπ (n + 1)) ≫
              fixedCoefficientHomologyToTor R X n hX M := by
          exact hinsert.symm
    _ =
        ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.hom ≫
          fixedCoefficientCyclesToTor R X n hX M := by
          simpa only [fixedCoefficientCyclesToTor, Category.assoc] using
            congrArg
              (fun t ↦
                ((X ⊗ coefficientComplex R M).sc (n + 1)).moduleCatCyclesIso.hom ≫
                  t ≫ fixedCoefficientHomologyToTor R X n hX M)
              hπ

/-- Helper for Theorem 17.1.3: the left comparison map lands in the kernel of the fixed
coefficient right edge. -/
private theorem fixedCoefficientHomologyToTor_zero
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    homologyTensorComparison R X M (n + 1) ≫
        fixedCoefficientHomologyToTor R X n hX M = 0 := by
  -- Read the public zero relation from the single packaged short-exact-data theorem.
  exact Classical.choose (Classical.choose_spec (fixedCoefficientRightEdgeShortExactData R X n hX M))

/-- Helper for Theorem 17.1.3: the fixed-coefficient universal coefficient row is short exact. -/
private theorem fixedCoefficientUniversalCoefficientHomologySequence_shortExact
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    (ShortComplex.mk
        (homologyTensorComparison R X M (n + 1))
        (fixedCoefficientHomologyToTor R X n hX M)
        (fixedCoefficientHomologyToTor_zero R X n hX M)).ShortExact := by
  -- Read the public short exactness witness from the same packaged fixed-coefficient owner.
  simpa only [fixedCoefficientHomologyToTor, fixedCoefficientHomologyToTor_zero] using
    (Classical.choose_spec
      (Classical.choose_spec (fixedCoefficientRightEdgeShortExactData R X n hX M)))

/-- Helper for Theorem 17.1.3: for fixed `M`, package the universal coefficient sequence on the
public Chapter 17 surface. -/
private noncomputable def fixedCoefficientUniversalCoefficientHomologySequence
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    (M : ModuleCat R) :
    UniversalCoefficientHomologySequence R X M n :=
  { tensorToHomology := homologyTensorComparison R X M (n + 1)
    homologyToTor := fixedCoefficientHomologyToTor R X n hX M
    zero := fixedCoefficientHomologyToTor_zero R X n hX M
    shortExact := fixedCoefficientUniversalCoefficientHomologySequence_shortExact
      R X n hX M }

/-- Helper for Theorem 17.1.3: the fixed-coefficient right edge is natural in the coefficient
module. -/
private theorem fixedCoefficientHomologyToTorNatural
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i))
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientHomologyCoefficientMap R X n f ≫
        fixedCoefficientHomologyToTor R X n hX N =
      fixedCoefficientHomologyToTor R X n hX M ≫
        (universalCoefficientHomologyTorFunctor R X n).map f := by
  -- Route correction: keep the Tor-side coefficient transport localized to the descended right
  -- edge, instead of reopening the left comparison square.
  -- TODO: once the public right edge is rebuilt canonically, precompose with
  -- `(X ⊗ coefficientComplex R M).homologyπ (n + 1)`, rewrite through
  -- `fixedCoefficientHomologyToTor_spec`, `HomologicalComplex.homologyπ_naturality`, and the
  -- normalized transported-row maps above, then cancel against the monic normalized `map' 0 1`.
  sorry

/-- Theorem 17.1.3. If `X` is a chain complex of flat `R`-modules over a PID `R`, then for each
`n` there exists a `UniversalCoefficientHomologyNaturality R X n`, i.e. a natural short exact
sequence of `R`-modules
`0 ⟶ H_(n + 1)(X) ⊗ M ⟶ H_(n + 1)(X; M) ⟶ Tor(H_n(X), M) ⟶ 0`
in the coefficient module `M`. This is the nat-indexed form of the textbook sequence
`0 ⟶ H_n(X) ⊗ M ⟶ H_n(X; M) ⟶ Tor(H_(n - 1)(X), M) ⟶ 0`. -/
theorem universalCoefficientHomologyShortExact
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hX : ∀ i : ℕ, Module.Flat R (X.X i)) :
    Nonempty (UniversalCoefficientHomologyNaturality R X n) := by
  -- Route correction: the theorem body now only assembles the fixed-coefficient short exact
  -- sequence and the two coefficient-change squares. The remaining work has been isolated into the
  -- right-edge helpers above.
  refine nonempty_universalCoefficientHomologyNaturality_of_data
    (fun M ↦ fixedCoefficientUniversalCoefficientHomologySequence R X n hX M)
    ?_ ?_
  · intro M N f
    exact homologyTensorComparisonNatural R X n f
  · intro M N f
    exact fixedCoefficientHomologyToTorNatural R X n hX f
