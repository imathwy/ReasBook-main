import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Proposition_12_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_2

noncomputable section

open CategoryTheory
open Topology

universe u

-- Semantic recall via `lean_leansearch`: the canonical owner for the long exact sequence coming
-- from a short exact sequence of chain complexes is
-- `HomologicalComplex.HomologySequence.composableArrows₅`, with connecting morphism
-- `shortExactChainComplexHomologyBoundary`. In the present environment the subcomplex cellular
-- chains of `A` are canonically available degreewise as
-- `subcomplexCellularChainSubmodule X A n ⊆ C_n(X)`, so the pair sequence is built from that
-- actual chain subcomplex of `cellularChainComplex X data`.

/-- The degree-`n` term of the canonical chain subcomplex of `cellularChainComplex X data`
determined by the cells of the subcomplex `A`. -/
abbrev subcomplexCellularChainComplexObj
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (n : ℕ) :
    ModuleCat ℤ :=
  ModuleCat.of ℤ (subcomplexCellularChainSubmodule X A n)

/-- The ambient cellular differential restricts to the canonical degreewise submodules generated
by the cells of `A`. -/
def subcomplexCellularDifferential
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (n : ℕ) :
    subcomplexCellularChainComplexObj X A (n + 1) ⟶
      subcomplexCellularChainComplexObj X A n :=
  ModuleCat.ofHom <|
    ((data.differential n).toIntLinearMap).restrict
      fun _ hx ↦ subcomplexCellularChainSubmodule_le_comap X A data n hx

/-- Consecutive restricted cellular differentials on the canonical subcomplex of `A` compose to
zero. -/
theorem subcomplexCellularChainComplex_sq
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (n : ℕ) :
    subcomplexCellularDifferential X A data (n + 1) ≫
      subcomplexCellularDifferential X A data n = 0 := by
  ext x
  change (data.differential n).toIntLinearMap
      ((data.differential (n + 1)).toIntLinearMap x.1) = 0
  simpa using
    congrArg (fun f ↦ f x.1) (cellularDifferential_squareZero X data n)

/-- The canonical chain subcomplex `C_*(A) ⊆ C_*(X)` determined by the cells of `A`, realized
inside `cellularChainComplex X data` by the degreewise submodules
`subcomplexCellularChainSubmodule X A n`. -/
abbrev subcomplexCellularChainComplex
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (subcomplexCellularChainComplexObj X A)
    (subcomplexCellularDifferential X A data)
    (subcomplexCellularChainComplex_sq X A data)

/-- The differential of `subcomplexCellularChainComplex X A data` in degree `n` is the
restriction of the ambient cellular differential to the canonical subcomplex of `A`. -/
@[simp] theorem subcomplexCellularChainComplex_d
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (n : ℕ) :
    (subcomplexCellularChainComplex X A data).d (n + 1) n =
      subcomplexCellularDifferential X A data n := by
  exact
    ChainComplex.of_d
      (subcomplexCellularChainComplexObj X A)
      (subcomplexCellularDifferential X A data)
      (subcomplexCellularChainComplex_sq X A data)
      n

/-- The canonical inclusion of the chain subcomplex `C_*(A)` into the ambient cellular chain
complex `C_*(X)`. -/
abbrev subcomplexCellularChainComplexInclusion
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] :
    subcomplexCellularChainComplex X A data ⟶ cellularChainComplex X data :=
  ChainComplex.ofHom
    (subcomplexCellularChainComplexObj X A)
    (subcomplexCellularDifferential X A data)
    (subcomplexCellularChainComplex_sq X A data)
    (fun n ↦ ModuleCat.of ℤ (cellularChainGroup X n))
    (fun n ↦ ModuleCat.ofHom (data.differential n).toIntLinearMap)
    (cellularChainComplex_sq X data)
    (fun n ↦ ModuleCat.ofHom (subcomplexCellularChainSubmodule X A n).subtype)
    fun n ↦ by
      apply ModuleCat.hom_ext
      simpa [subcomplexCellularDifferential] using
        (LinearMap.subtype_comp_restrict
          (fun x hx ↦ show
            (data.differential n).toIntLinearMap x ∈ subcomplexCellularChainSubmodule X A n from
              subcomplexCellularChainSubmodule_le_comap X A data n hx))

/-- The canonical quotient map from the ambient cellular chain complex `C_*(X)` to the relative
cellular chain complex `C_*(X, A)`. -/
abbrev relativeCellularChainComplexQuotient
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] :
    cellularChainComplex X data ⟶ relativeCellularChainComplex X A data :=
  ChainComplex.ofHom
    (fun n ↦ ModuleCat.of ℤ (cellularChainGroup X n))
    (fun n ↦ ModuleCat.ofHom (data.differential n).toIntLinearMap)
    (cellularChainComplex_sq X data)
    (relativeCellularChainGroup X A)
    (relativeCellularDifferential X A data)
    (relativeCellularChainComplex_sq X A data)
    (fun n ↦ ModuleCat.ofHom (subcomplexCellularChainSubmodule X A n).mkQ)
    fun n ↦ by
      apply ModuleCat.hom_ext
      simpa [relativeCellularDifferential] using
        (Submodule.mapQ_mkQ
          (subcomplexCellularChainSubmodule X A (n + 1))
          (subcomplexCellularChainSubmodule X A n)
          (data.differential n).toIntLinearMap)

/-- The short complex `C_*(A) ⟶ C_*(X) ⟶ C_*(X, A)` attached to the canonical chain subcomplex of
the cells of `A`. -/
abbrev relativeCellularPairShortComplex
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk
    (subcomplexCellularChainComplexInclusion X A data)
    (relativeCellularChainComplexQuotient X A data)
    (by
      ext n x
      change (subcomplexCellularChainSubmodule X A n).mkQ x.1 = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 x.2)

private abbrev relativeCellularPairDegreewiseShortComplex
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (n : ℕ) :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk
    (ModuleCat.ofHom (subcomplexCellularChainSubmodule X A n).subtype)
    (ModuleCat.ofHom (subcomplexCellularChainSubmodule X A n).mkQ)
    (by
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).2 x.2)

private theorem relativeCellularPairDegreewiseShortExact
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (n : ℕ) :
    (relativeCellularPairDegreewiseShortComplex X A n).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    constructor
    · intro hy
      refine ⟨⟨y, ?_⟩, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).1 hy
    · rintro ⟨x, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 x.2
  · exact (subcomplexCellularChainSubmodule X A n).injective_subtype
  · exact (subcomplexCellularChainSubmodule X A n).mkQ_surjective

/-- The canonical pair short complex `C_*(A) ⟶ C_*(X) ⟶ C_*(X, A)` is short exact degreewise,
hence short exact as a short complex of chain complexes. -/
theorem relativeCellularPairShortComplex_shortExact
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] :
    (relativeCellularPairShortComplex X A data).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact
    (relativeCellularPairShortComplex X A data) ?_
  intro n
  simpa [relativeCellularPairShortComplex, relativeCellularPairDegreewiseShortComplex,
    subcomplexCellularChainComplexInclusion, relativeCellularChainComplexQuotient] using
    relativeCellularPairDegreewiseShortExact X A n

/-- The connecting homomorphism `H_(n + 1)(X, A) ⟶ H_n(A)` attached to the canonical short exact
sequence `0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X, A) ⟶ 0`, where `H_n(A)` is represented by the degree-`n`
homology of the canonical subcomplex chain complex of `A`. -/
noncomputable abbrev relativeCellularHomologyBoundary
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (n : ℕ) :
    relativeCellularHomology X A data (n + 1) ⟶
      (subcomplexCellularChainComplex X A data).homology n :=
  shortExactChainComplexHomologyBoundary
    (relativeCellularPairShortComplex X A data)
    (relativeCellularPairShortComplex_shortExact X A data) n

/-- The degree-`n` five-arrow segment in the long exact homology sequence of the pair `(X, A)`,
built from the canonical chain subcomplex `C_*(A) ⊆ C_*(X)`. -/
noncomputable abbrev relativeCellularHomologyExactSegment
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (n : ℕ) :
    ComposableArrows (ModuleCat ℤ) 5 :=
  shortExactChainComplexHomologyComposableArrows₅
    (relativeCellularPairShortComplex X A data)
    (relativeCellularPairShortComplex_shortExact X A data) n

/-- The connecting homomorphism of the pair sequence is the middle map of the associated
degree-`n` five-arrow homology segment. -/
theorem relativeCellularHomologyBoundary_def
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (n : ℕ) :
    relativeCellularHomologyBoundary X A data n =
      (relativeCellularHomologyExactSegment X A data n).map' 2 3 := by
  simpa [relativeCellularHomologyBoundary, relativeCellularHomologyExactSegment] using
    shortExactChainComplexHomologyBoundary_def
      (relativeCellularPairShortComplex X A data)
      (relativeCellularPairShortComplex_shortExact X A data) n

/-- The degree-`n` five-arrow segment in the long exact homology sequence of the pair `(X, A)`
after transporting the left-hand homology terms of the canonical subcomplex model for `A` to a
preferred family of homology objects. -/
noncomputable abbrev relativeCellularHomologyExactSegmentOnChosenHomology
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (cellularHomologyA : ℕ → ModuleCat ℤ)
    (hCellularHomologyA :
      ∀ n, (subcomplexCellularChainComplex X A data).homology n ≅ cellularHomologyA n)
    (n : ℕ) :
    ComposableArrows (ModuleCat ℤ) 5 :=
  ComposableArrows.mk₅
    ((hCellularHomologyA (n + 1)).inv ≫
      HomologicalComplex.homologyMap (subcomplexCellularChainComplexInclusion X A data) (n + 1))
    (HomologicalComplex.homologyMap (relativeCellularChainComplexQuotient X A data) (n + 1))
    (relativeCellularHomologyBoundary X A data n ≫ (hCellularHomologyA n).hom)
    ((hCellularHomologyA n).inv ≫
      HomologicalComplex.homologyMap (subcomplexCellularChainComplexInclusion X A data) n)
    (HomologicalComplex.homologyMap (relativeCellularChainComplexQuotient X A data) n)

/-- Construction 13.3.3. For a CW pair `(X, A)`, the canonical short exact sequence
`0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X, A) ⟶ 0` coming from the cellular chain subcomplex of `A`
induces the exact degree-`n` homology segment
`H_(n + 1)(A) ⟶ H_(n + 1)(X) ⟶ H_(n + 1)(X, A) ⟶ H_n(A) ⟶ H_n(X) ⟶ H_n(X, A)`, where
`H_k(A)` is represented by the degree-`k` homology of the canonical subcomplex chain complex of
`A`. -/
theorem relativeCellularHomologyExactFiveTerm
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (n : ℕ) :
    (relativeCellularHomologyExactSegment X A data n).Exact := by
  simpa [relativeCellularHomologyExactSegment] using
    shortExactChainComplexHomologyExactFiveTerm
      (relativeCellularPairShortComplex X A data)
      (relativeCellularPairShortComplex_shortExact X A data) n

/-- Transporting the exactness of the pair homology segment along chosen identifications of the
left-hand terms with a preferred family of homology objects for `A`. -/
theorem relativeCellularHomologyExactFiveTermOnChosenHomology
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (cellularHomologyA : ℕ → ModuleCat ℤ)
    (hCellularHomologyA :
      ∀ n, (subcomplexCellularChainComplex X A data).homology n ≅ cellularHomologyA n)
    (n : ℕ) :
    (relativeCellularHomologyExactSegmentOnChosenHomology
      X A data cellularHomologyA hCellularHomologyA n).Exact := by
  let S : ComposableArrows (ModuleCat ℤ) 5 := ComposableArrows.mk₅
    (HomologicalComplex.homologyMap (subcomplexCellularChainComplexInclusion X A data) (n + 1))
    (HomologicalComplex.homologyMap (relativeCellularChainComplexQuotient X A data) (n + 1))
    (relativeCellularHomologyBoundary X A data n)
    (HomologicalComplex.homologyMap (subcomplexCellularChainComplexInclusion X A data) n)
    (HomologicalComplex.homologyMap (relativeCellularChainComplexQuotient X A data) n)
  let T : ComposableArrows (ModuleCat ℤ) 5 :=
    relativeCellularHomologyExactSegmentOnChosenHomology
      X A data cellularHomologyA hCellularHomologyA n
  have hExact : S.Exact := by
    simpa [relativeCellularHomologyBoundary, relativeCellularHomologyExactSegment,
      shortExactChainComplexHomologyComposableArrows₅, S] using
      relativeCellularHomologyExactFiveTerm X A data n
  have e : S ≅ T := by
    refine ComposableArrows.isoMk₅
      (hCellularHomologyA (n + 1))
      (Iso.refl _)
      (Iso.refl _)
      (hCellularHomologyA n)
      (Iso.refl _)
      (Iso.refl _)
      ?_ ?_ ?_ ?_ ?_
    · change HomologicalComplex.homologyMap
          (subcomplexCellularChainComplexInclusion X A data) (n + 1) ≫ 𝟙 _ =
        (hCellularHomologyA (n + 1)).hom ≫
          ((hCellularHomologyA (n + 1)).inv ≫
            HomologicalComplex.homologyMap
              (subcomplexCellularChainComplexInclusion X A data) (n + 1))
      simp
    · change HomologicalComplex.homologyMap
          (relativeCellularChainComplexQuotient X A data) (n + 1) ≫ 𝟙 _ =
        𝟙 _ ≫ HomologicalComplex.homologyMap
          (relativeCellularChainComplexQuotient X A data) (n + 1)
      simp
    · change relativeCellularHomologyBoundary X A data n ≫ (hCellularHomologyA n).hom =
        𝟙 _ ≫
          (relativeCellularHomologyBoundary X A data n ≫ (hCellularHomologyA n).hom)
      simp
    · change HomologicalComplex.homologyMap
          (subcomplexCellularChainComplexInclusion X A data) n ≫ 𝟙 _ =
        (hCellularHomologyA n).hom ≫
          ((hCellularHomologyA n).inv ≫
            HomologicalComplex.homologyMap
              (subcomplexCellularChainComplexInclusion X A data) n)
      simp
    · change HomologicalComplex.homologyMap
          (relativeCellularChainComplexQuotient X A data) n ≫ 𝟙 _ =
        𝟙 _ ≫ HomologicalComplex.homologyMap
          (relativeCellularChainComplexQuotient X A data) n
      simp
  exact ComposableArrows.exact_of_iso
    e hExact
