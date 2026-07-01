import Mathlib
import stacks_project.Chap13.Definition_13_33_1
import stacks_project.Chap13.Lemma_13_33_5
import stacks_project.Chap13.Lemma_13_33_6
import stacks_project.Chap13.Definition_13_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Example 13.41.2:
- primary domain: the brutal left-truncation tower in `CochainComplex 𝒜 ℤ` and its induced
  Postnikov-style stage triangles in `D(𝒜)` for a bounded-above complex
  `(... ⟶ A₂ ⟶ A₁ ⟶ A₀ ⟶ 0 ⟶ ...)`;
- inspected owner declarations:
  `CochainComplex.IsStrictlyLE`,
  `CochainComplex.minus`,
  `HomologicalComplex.stupidTrunc`,
  `HomologicalComplex.stupidTruncXIso`,
  `PostnikovSystem`,
  `termwise_colimit_is_homotopy_colimit`;
- best owner abstraction:
  the primitive owner is the cochain complex `K` itself, because the brutal truncation stages,
  their transition maps, the sequential tower, and the finite row `Xₙ ⟶ ⋯ ⟶ X₀` are canonical
  for every `K`. The bounded-above hypothesis `[K.IsStrictlyLE 0]` belongs only to the theorem
  layer where those primitive constructions are identified with the source finite-stage picture.
  The core truncation engine is still the canonical mathlib owner
  `HomologicalComplex.stupidTrunc`, while the finite-row packaging is handled by the chapter
  owner `PostnikovSystem`, and the infinite `hocolim` statement is owned by the Chapter `13`
  telescope theorem `termwise_colimit_is_homotopy_colimit`;
- primitive-vs-derived split:
  primitive data: the source complex `K`, the brutal finite stage complexes `Yₙ[n]`, the stage
    maps `Yₙ[n] ⟶ Yₙ₊₁[n + 1]`, the projections `Yₙ[n] ⟶ Aₙ[-n]`, and the induced derived-stage
    objects `Yₙ` and `Xₙ`;
  derived API: the stage triangles and comparison maps in `D(𝒜)`, the finite `PostnikovSystem`
    bridge on the row `Xₙ ⟶ ⋯ ⟶ X₀`, and the homotopy colimit theorem for the shifted tower
    `Y₀ ⟶ Y₁[1] ⟶ Y₂[2] ⟶ ⋯`, with `[K.IsStrictlyLE 0]` imposed only where the bounded-above
    source interpretation is used.

Source/core/bridge triage:
- source-facing:
  `boundedAbovePostnikovX`,
  `boundedAbovePostnikovY`,
  `boundedAbovePostnikovXMap`,
  `boundedAboveTermSequence`,
  `boundedAbovePostnikovToX`,
  `boundedAbovePostnikovToNext`,
  `boundedAbovePostnikovConnecting`,
  `boundedAbovePostnikovToX_zero_isIso`,
  `boundedAbovePostnikov_distinguished`,
  `boundedAbovePostnikov_comp`,
  `boundedAboveTermSequencePostnikovSystem`;
- core/canonical:
  `CochainComplex.IsStrictlyLE`,
  `CochainComplex.minus`,
  `HomologicalComplex.stupidTrunc`,
  `PostnikovSystem`,
  `IsHomotopyColimitOf`;
-- bridge/view:
  `brutalLeftTruncationStage`,
  `brutalLeftTruncationStep`,
  `brutalLeftTruncationTower`,
  `brutalLeftTruncationColimitComparison`,
  `brutalLeftTruncationColimitComparison_isIso`,
  `brutalLeftTruncation_isHomotopyColimitOf`,
  the left-to-right `Fin (n + 1)` reindexing used to present the source family `Yₙ, …, Y₀`
  as the auxiliary-object function of a finite `PostnikovSystem`,
  together with the internal single-complex, stage-triangle, and colimit-comparison bridges used
  to build the finite `PostnikovSystem` and the sequential colimit comparison. -/

private abbrev boundedAboveTermIndex (n : ℕ) (i : Fin (n + 1)) : ℕ :=
  n - i.1

private theorem boundedAboveTermIndex_succ_add_one
    (n : ℕ) (i : Fin n) :
    boundedAboveTermIndex n i.succ + 1 = boundedAboveTermIndex n i.castSucc := by
  dsimp [boundedAboveTermIndex]
  omega

variable (K : CochainComplex 𝒜 ℤ)

section

/-- The `n`th stage of the brutal left-truncation tower of `K`, starting in degree `-n`. Under
`[K.IsStrictlyLE 0]`, its nonzero degrees are `-n, …, 0`, so it is the source complex `Y_n[n]`. -/
abbrev brutalLeftTruncationStage (n : ℕ) :
    CochainComplex 𝒜 ℤ :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ)))

/-- The single cochain complex with `A_n` in degree `-n`, representing the source term `X_n`
before shifting it to degree `0`. -/
private noncomputable abbrev boundedAbovePostnikovXComplex (n : ℕ) :
    CochainComplex 𝒜 ℤ :=
  (CochainComplex.singleFunctor 𝒜 (-((n : ℕ) : ℤ))).obj (K.X (-((n : ℕ) : ℤ)))

/-- The canonical projection
`Y_n[n] ⟶ A_n[-n]`
onto the leftmost term of the brutal left-truncation stage. -/
private noncomputable def brutalLeftTruncationToSingle (n : ℕ) :
    brutalLeftTruncationStage K n ⟶ boundedAbovePostnikovXComplex K n :=
  let hGE : (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))).f 0 = -((n : ℕ) : ℤ) := by
    simp [ComplexShape.embeddingUpIntGE]
  HomologicalComplex.mkHomToSingle
    ((K.stupidTruncXIso (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) hGE).hom)
    (fun i hi ↦ by
      sorry)

/-- The canonical inclusion
`Y_n[n] ⟶ Y_{n + 1}[n + 1]`
between consecutive brutal left-truncation stages. -/
noncomputable def brutalLeftTruncationStep (n : ℕ) :
    brutalLeftTruncationStage K n ⟶ brutalLeftTruncationStage K (n + 1) where
  f i :=
    if hi : -((n : ℕ) : ℤ) ≤ i then
      let j : ℕ := Int.toNat (i + (n : ℤ))
      let hj : (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))).f j = i := by
        dsimp [j, ComplexShape.embeddingUpIntGE]
        rw [Int.toNat_of_nonneg]
        · linarith
        · linarith
      let hj' : (ComplexShape.embeddingUpIntGE (-(((n + 1 : ℕ)) : ℤ))).f (j + 1) = i := by
        dsimp [j, ComplexShape.embeddingUpIntGE]
        rw [Int.toNat_of_nonneg]
        · linarith
        · linarith
      let sourceIso :
          (brutalLeftTruncationStage K n).X i ≅
            K.X i :=
        K.stupidTruncXIso
          (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) hj
      let targetIso :
          (brutalLeftTruncationStage K (n + 1)).X i ≅
            K.X i :=
        K.stupidTruncXIso
          (ComplexShape.embeddingUpIntGE (-(((n + 1 : ℕ)) : ℤ))) hj'
      sourceIso.hom ≫ targetIso.inv
    else
      0
  comm' i j hij := by
    sorry

/-- The short exact sequence
`Y_n[n] ⟶ Y_{n + 1}[n + 1] ⟶ A_{n + 1}[-(n + 1)]`
whose quotient is the new leftmost term of the next brutal left-truncation stage. -/
private noncomputable def boundedAbovePostnikovStageShortComplex (n : ℕ) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (brutalLeftTruncationStep K n)
    (brutalLeftTruncationToSingle K (n + 1))
    (by
      sorry)

/-- The stage short complex is short exact. -/
private theorem boundedAbovePostnikovStageShortExact (n : ℕ) :
    (boundedAbovePostnikovStageShortComplex K n).ShortExact := by
  sorry

/-- The sequential tower
`Y_0[0] ⟶ Y_1[1] ⟶ Y_2[2] ⟶ ⋯`
of shifted brutal left-truncation stages. -/
noncomputable abbrev brutalLeftTruncationTower :
    ℕ ⥤ CochainComplex 𝒜 ℤ :=
  Functor.ofSequence (brutalLeftTruncationStep K)

/-- The canonical inclusion of the `n`th brutal left-truncation stage into the source complex
`K`. -/
noncomputable def brutalLeftTruncationInclusion (n : ℕ) :
    brutalLeftTruncationStage K n ⟶ K where
  f i :=
    if hi : -((n : ℕ) : ℤ) ≤ i then
      let j : ℕ := Int.toNat (i + (n : ℤ))
      let hj : (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))).f j = i := by
        dsimp [j, ComplexShape.embeddingUpIntGE]
        rw [Int.toNat_of_nonneg]
        · linarith
        · linarith
      let stageIso :
          (brutalLeftTruncationStage K n).X i ≅
            K.X i :=
        K.stupidTruncXIso
          (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) hj
      stageIso.hom
    else
      0
  comm' i j hij := by
    sorry

-- Proof sketch: on each degree, both composites are the identity on the shared source term when
-- that degree lies in the stage `Y_n[n]`, and are zero otherwise.
/-- The tower maps are compatible with the canonical inclusions into the source complex `K`. -/
theorem brutalLeftTruncationStep_comp_inclusion (n : ℕ) :
    brutalLeftTruncationStep K n ≫ brutalLeftTruncationInclusion K (n + 1) =
      brutalLeftTruncationInclusion K n := sorry

/-- The canonical cocone from the brutal-stage tower to the source complex `K`. -/
private noncomputable def brutalLeftTruncationCocone :
    Cocone (brutalLeftTruncationTower K) where
  pt := K
  ι := NatTrans.ofSequence
    (fun n ↦ brutalLeftTruncationInclusion K n)
    (fun n ↦ by
      simpa [brutalLeftTruncationTower] using
        brutalLeftTruncationStep_comp_inclusion K n)

section

variable [HasColimitsOfShape ℕ 𝒜]

/-- The canonical map from the sequential colimit of the brutal left-truncation tower to the
source complex `K`. -/
noncomputable def brutalLeftTruncationColimitComparison :
    colimit (brutalLeftTruncationTower K) ⟶ K :=
  colimit.desc (brutalLeftTruncationTower K) (brutalLeftTruncationCocone K)

section

-- Proof sketch: the tower consists of the intrinsic inclusions of the brutal left-truncation stages into
-- one another. Degreewise, every term stabilizes after finitely many stages, so the termwise
-- colimit is exactly the source complex `K`.
/-- The brutal left-truncation tower stabilizes degreewise, so its colimit maps isomorphically to
the source complex `K`. Under `[K.IsStrictlyLE 0]`, this is the source tower
`Y_0[0] ⟶ Y_1[1] ⟶ Y_2[2] ⟶ ⋯` from Example 13.41.2 (3). -/
theorem brutalLeftTruncationColimitComparison_isIso :
    IsIso (brutalLeftTruncationColimitComparison K) := by
  sorry

end

end

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable (K : CochainComplex 𝒜 ℤ)

/-- The stage object `X_n = A_n` of the source example, viewed in `D(𝒜)` as an object
concentrated in degree `0`. -/
abbrev boundedAbovePostnikovX (n : ℕ) : DerivedCategory 𝒜 :=
  (DerivedCategory.singleFunctor 𝒜 (0 : ℤ)).obj (K.X (-((n : ℕ) : ℤ)))

/-- The differential map `X_{n + 1} ⟶ X_n` in the source row
`⋯ ⟶ X₂ ⟶ X₁ ⟶ X₀`. -/
abbrev boundedAbovePostnikovXMap (n : ℕ) :
    boundedAbovePostnikovX K (n + 1) ⟶ boundedAbovePostnikovX K n :=
  (DerivedCategory.singleFunctor 𝒜 (0 : ℤ)).map
    (K.d (-((n + 1 : ℕ) : ℤ)) (-((n : ℕ) : ℤ)))

/-- The source stage object
obtained from the brutal truncation stage. Under `[K.IsStrictlyLE 0]`, this is the source stage
object `Y_n = (A_n ⟶ A_{n - 1} ⟶ ⋯ ⟶ A_0)[-n]`, and equivalently `Y_n[n]` is
`brutalLeftTruncationStage K n`. -/
abbrev boundedAbovePostnikovY (n : ℕ) : DerivedCategory 𝒜 :=
  (Q.obj (brutalLeftTruncationStage K n))⟦(-((n : ℕ) : ℤ))⟧

/-- Shifting the single complex `A_n[-n]` by `-n` identifies it with the stage object
`X_n = A_n[0]`. -/
private noncomputable def boundedAbovePostnikovXShiftIso (n : ℕ) :
    (Q.obj (boundedAbovePostnikovXComplex K n))⟦(-((n : ℕ) : ℤ))⟧ ≅
      boundedAbovePostnikovX K n :=
  ((DerivedCategory.singleFunctors 𝒜).shiftIso (-((n : ℕ) : ℤ)) 0
      (-((n : ℕ) : ℤ)) (by simp)).app (K.X (-((n : ℕ) : ℤ)))

/-- The finite row
attached to the terms `A_n, …, A_0` of a cochain complex. Under `[K.IsStrictlyLE 0]`, this is
the finite row appearing in Example 13.41.2. -/
private abbrev boundedAboveTermSequenceMap
    (n : ℕ) (i : Fin n) :
    boundedAbovePostnikovX K (boundedAboveTermIndex n i.castSucc) ⟶
      boundedAbovePostnikovX K (boundedAboveTermIndex n i.succ) :=
  cast
    (by rw [← boundedAboveTermIndex_succ_add_one n i])
    (boundedAbovePostnikovXMap K (boundedAboveTermIndex n i.succ))

def boundedAboveTermSequence (n : ℕ) :
    ComposableArrows (DerivedCategory 𝒜) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ boundedAbovePostnikovX K (boundedAboveTermIndex n i))
    (fun i ↦ boundedAboveTermSequenceMap K n i)

/-- The canonical shifted-and-rotated triangle
`Y_{n + 1} ⟶ A_{n + 1}[0] ⟶ Y_n ⟶ Y_{n + 1}[1]`
attached to consecutive brutal left-truncation stages. -/
private noncomputable def boundedAbovePostnikovStageTriangle (n : ℕ) :
    Triangle (DerivedCategory 𝒜) :=
  (((shiftFunctor (Triangle (DerivedCategory 𝒜)) (-((n + 1 : ℕ) : ℤ))).obj
      (DerivedCategory.triangleOfSES (boundedAbovePostnikovStageShortExact K n))).rotate)

/-- The third object of the shifted-and-rotated stage triangle is canonically `Y_n`. -/
private noncomputable def boundedAbovePostnikovStageTriangleObj3Iso (n : ℕ) :
    (boundedAbovePostnikovStageTriangle K n).obj₃ ≅ boundedAbovePostnikovY K n :=
  ((shiftFunctorAdd' (DerivedCategory 𝒜) (-((n + 1 : ℕ) : ℤ)) (1 : ℤ)
      (-((n : ℕ) : ℤ)) (by omega)).app (Q.obj (brutalLeftTruncationStage K n))).symm

/-- The canonical comparison map `Y_n ⟶ X_n` attached to the brutal left-truncation stage of `K`. -/
noncomputable def boundedAbovePostnikovToX (n : ℕ) :
    boundedAbovePostnikovY K n ⟶ boundedAbovePostnikovX K n :=
  (Q.map (brutalLeftTruncationToSingle K n))⟦(-((n : ℕ) : ℤ))⟧' ≫
    (boundedAbovePostnikovXShiftIso K n).hom

/-- The canonical map `X_{n + 1} ⟶ Y_n` attached to consecutive brutal left-truncation stages
of `K`. -/
noncomputable def boundedAbovePostnikovToNext (n : ℕ) :
    boundedAbovePostnikovX K (n + 1) ⟶ boundedAbovePostnikovY K n :=
  (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
    (boundedAbovePostnikovStageTriangle K n).mor₂ ≫
    (boundedAbovePostnikovStageTriangleObj3Iso K n).hom

/-- The canonical connecting map `Y_n ⟶ Y_{n + 1}[1]` attached to consecutive brutal
left-truncation stages of `K`. -/
noncomputable def boundedAbovePostnikovConnecting (n : ℕ) :
    boundedAbovePostnikovY K n ⟶ (boundedAbovePostnikovY K (n + 1))⟦(1 : ℤ)⟧ :=
  (boundedAbovePostnikovStageTriangleObj3Iso K n).inv ≫
    (boundedAbovePostnikovStageTriangle K n).mor₃

section

variable [K.IsStrictlyLE 0]

-- Proof sketch: the brutal left-truncation stages and their canonical short exact sequences define the
-- maps `Y_n ⟶ X_n`, `X_{n + 1} ⟶ Y_n`, and `Y_n ⟶ Y_{n + 1}[1]`; the shifted truncation triangles
-- give the distinguished triangles of the infinite Postnikov system, and the composites recover
-- the differentials `X_{n + 1} ⟶ X_n`.

/-- The right end of the canonical bounded-above Postnikov system identifies `Y₀` with `X₀`. -/
theorem boundedAbovePostnikovToX_zero_isIso :
    IsIso (boundedAbovePostnikovToX K 0) := by
  sorry

/-- Each stage of the canonical bounded-above Postnikov system is a distinguished triangle. -/
theorem boundedAbovePostnikov_distinguished (n : ℕ) :
    Triangle.mk
        (boundedAbovePostnikovToX K (n + 1))
        (boundedAbovePostnikovToNext K n)
        (boundedAbovePostnikovConnecting K n) ∈
      distTriang (DerivedCategory 𝒜) := by
  sorry

/-- The canonical bounded-above Postnikov maps recover the differentials
`X_{n + 1} ⟶ X_n`. -/
theorem boundedAbovePostnikov_comp (n : ℕ) :
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
      boundedAbovePostnikovXMap K n := by
  sorry

private theorem boundedAboveTermSequence_delta₀ (n : ℕ) :
    (boundedAboveTermSequence K (n + 1)).δ₀ = boundedAboveTermSequence K n := by
  sorry

private noncomputable def boundedAboveTermSequencePostnikovSystemZero :
    PostnikovSystem (boundedAboveTermSequence K 0) :=
  @PostnikovSystem.mk₀ _ _ _ _ _ _ _
    (boundedAboveTermSequence K 0)
    (boundedAbovePostnikovY K 0)
    (boundedAbovePostnikovToX K 0)
    (boundedAbovePostnikovToX_zero_isIso K)

/-- Example 13.41.2 (2): each finite row
`X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0`
inherits the canonical finite `PostnikovSystem` coming from the brutal truncation tower. -/
noncomputable def boundedAboveTermSequencePostnikovSystem :
    (n : ℕ) → PostnikovSystem (boundedAboveTermSequence K n)
  | 0 =>
      boundedAboveTermSequencePostnikovSystemZero K
  | n + 1 =>
      let tail : PostnikovSystem ((boundedAboveTermSequence K (n + 1)).δ₀) :=
        cast (by rw [boundedAboveTermSequence_delta₀ K n])
          (boundedAboveTermSequencePostnikovSystem n)
      let headEq : tail.head = boundedAbovePostnikovY K n := by
        sorry
      PostnikovSystem.mkSucc tail
        (boundedAbovePostnikovY K (n + 1))
        (boundedAbovePostnikovToX K (n + 1))
        (cast (by
          simp [boundedAboveTermSequence, boundedAboveTermIndex, headEq])
          (boundedAbovePostnikovToNext K n))
        (cast (by
          simp [boundedAboveTermSequence, boundedAboveTermIndex, headEq])
          (boundedAbovePostnikovConnecting K n))
        (by
          sorry)
        (by
          sorry)

/-- The canonical finite `PostnikovSystem` on the row
`X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0`
has auxiliary object `Y_{n - i}` at index `i`. -/
@[simp] theorem boundedAboveTermSequencePostnikovSystem_apply
    (n : ℕ) (i : Fin (n + 1)) :
    boundedAboveTermSequencePostnikovSystem K n i =
      boundedAbovePostnikovY K (n - i.1) := by
  simpa [boundedAboveTermIndex]
    using
      (show boundedAboveTermSequencePostnikovSystem K n i =
          boundedAbovePostnikovY K (boundedAboveTermIndex n i) by
        sorry)

end

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable (K : CochainComplex 𝒜 ℤ)
variable [HasColimitsOfShape ℕ 𝒜]

local instance : HasCountableCoproducts 𝒜 := hasCountableCoproducts_of_sequentialColimits

section

variable [HasExactColimitsOfShape ℕ 𝒜]

/-- The shifted brutal left-truncation tower has the countable coproduct needed to form its
telescope in `D(𝒜)`, obtained by combining the Chapter `13` countable-coproduct bridge in `𝒜`
with the termwise-coproduct bridge for `DerivedCategory.Q`. -/
noncomputable local instance brutalLeftTruncationTower_hasCoproduct
    :
    HasCoproduct (brutalLeftTruncationTower K ⋙ Q).obj := by
  let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
  let _ : CountableAB4 𝒜 := CountableAB4.of_countableAB5 𝒜
  infer_instance

-- Proof sketch: apply `termwise_colimit_is_homotopy_colimit` to the canonical brutal
-- left-truncation tower,
-- and use `brutalLeftTruncationColimitComparison_isIso` to identify its termwise colimit
-- with the source complex `K`.
/-- Under exact sequential colimits, every cochain complex is a homotopy colimit of its brutal
left-truncation tower. Under `[K.IsStrictlyLE 0]`, this recovers the source tower
`Q(Y_0[0]) ⟶ Q(Y_1[1]) ⟶ Q(Y_2[2]) ⟶ ⋯` from Example 13.41.2 (3). -/
theorem brutalLeftTruncation_isHomotopyColimitOf :
    IsHomotopyColimitOf
      (brutalLeftTruncationTower K ⋙ Q)
      (Q.obj K) := sorry

end

end

end

end CategoryTheory
