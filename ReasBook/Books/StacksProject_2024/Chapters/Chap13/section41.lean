import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_41_1 (from Chap13) -/
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Definition 13.41.1:
- primary domain: finite complexes in a triangulated category, together with their recursive
  Postnikov-stage distinguished triangles;
- inspected owner declarations:
  `ComposableArrows.δ₀`,
  `ComposableArrows.precomp`,
  `Triangle`,
  `TriangleMorphism`,
  `CommSq`;
- best owner abstraction: the source-facing owner is a `PostnikovSystem X` over a fixed finite row
  `X : ComposableArrows D n`, defined recursively on `n` by a Postnikov system on the truncated
  row `X.δ₀` together with one new distinguished triangle over the leftmost stage; each stage is
  still exposed through the canonical triangle owner `P.triangle i`, and each compatibility
  condition of a morphism of Postnikov systems is exposed through the canonical square owner
  `CommSq`;
- primitive-vs-derived split:
  primitive data: for `n = 0`, an auxiliary object `Y₀` with an isomorphism `Y₀ ⟶ X₀`; for
    `n + 1`, a Postnikov system on `X.δ₀`, one new auxiliary object over `X.obj 0`, and one new
    distinguished triangle whose composite recovers `X.map' 0 1`;
  derived API: the function-like access to the whole auxiliary family, the stage maps `P.toX`,
    `P.toNext`, `P.connecting`, the stage triangles `P.triangle i`, and the stagewise triangle
    morphisms `ψ.triangleMorphism i`. -/

/- Source/core/bridge triage for Definition 13.41.1:
- source-facing: `PostnikovSystem` and `PostnikovSystemMorphism`, which record the textbook
  Postnikov-system data itself;
- core/canonical: `ComposableArrows`, `Triangle`, `TriangleMorphism`, and `CommSq`;
- bridge/view: the canonical triangle-valued view `P.triangle i` and the induced stagewise
  triangle morphism `ψ.triangleMorphism i`. -/

namespace PostnikovSystem

/-- The recursive core of a Postnikov system. For `n = 0`, it is an isomorphism `Y₀ ⟶ X₀`. For
`n + 1`, it is a Postnikov system on the truncated row `X.δ₀` together with one new distinguished
triangle `Y_{n + 1} ⟶ X_{n + 1} ⟶ Y_n ⟶ Y_{n + 1}[1]` whose composite recovers the next
differential. -/
inductive Step : {n : ℕ} → (X : ComposableArrows D n) → (Y : D) → (toX : Y ⟶ X.obj 0) → Type (max u v)
  | zero {X : ComposableArrows D 0} {Y : D} (toX : Y ⟶ X.obj 0) [IsIso toX] :
      Step X Y toX
  | succ {n : ℕ} {X : ComposableArrows D (n + 1)} {Y : D} {toX : Y ⟶ X.obj 0}
      {Y' : D} {toX' : Y' ⟶ X.δ₀.obj 0} (tail : Step X.δ₀ Y' toX')
      (toNext : X.obj 0 ⟶ Y') (connecting : Y' ⟶ Y⟦(1 : ℤ)⟧)
      (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
      (comp : toNext ≫ toX' = X.map' 0 1) :
      Step X Y toX

end PostnikovSystem

/-- Definition 13.41.1: a Postnikov system on a length-`n` complex in a triangulated category is
defined recursively by length. For `n = 0`, it is an isomorphism `Y₀ ⟶ X₀`. For `n + 1`, it is a
Postnikov system on the truncated row `X.δ₀` together with one new distinguished triangle over the
leftmost stage. The stagewise family `Y_i` and the maps
`Y_i ⟶ X_i`, `X_i ⟶ Y_{i - 1}`, `Y_{i - 1} ⟶ Y_i[1]` are derived accessors from this recursive
owner. -/
structure PostnikovSystem {n : ℕ} (X : ComposableArrows D n) where
  /-- The leftmost auxiliary object in the recursive Postnikov construction. For a row written as
  `X_n ⟶ ⋯ ⟶ X_0`, this is the object `Y_n`. -/
  head : D
  /-- The comparison morphism from the leftmost auxiliary object to the leftmost object of the
  row. -/
  headToX : head ⟶ X.obj 0
  /-- The recursive Postnikov-step data. -/
  step : PostnikovSystem.Step X head headToX

namespace PostnikovSystem

variable {n : ℕ} {X : ComposableArrows D n}

/-- Constructor for the base case `n = 0`, where a Postnikov system is just an isomorphism
`Y₀ ⟶ X₀`. -/
def mk₀ {X : ComposableArrows D 0} (Y : D) (toX : Y ⟶ X.obj 0) [IsIso toX] :
    PostnikovSystem X :=
  ⟨Y, toX, .zero toX⟩

/-- Constructor for the recursive step: a Postnikov system on `X.δ₀` together with one new
distinguished triangle over `X.obj 0`. -/
def mkSucc {n : ℕ} {X : ComposableArrows D (n + 1)} (tail : PostnikovSystem X.δ₀) (Y : D)
    (toX : Y ⟶ X.obj 0) (toNext : X.obj 0 ⟶ tail.head) (connecting : tail.head ⟶ Y⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
    (comp : toNext ≫ tail.headToX = X.map' 0 1) :
    PostnikovSystem X :=
  ⟨Y, toX, .succ tail.step toNext connecting distinguished comp⟩

/-- The recursive truncation of a nonzero-length Postnikov system. -/
def tail {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    PostnikovSystem X.δ₀ :=
  match P.step with
  | .succ tail _ _ _ _ => ⟨_, _, tail⟩

/-- The new stage map `X.obj 0 ⟶ P.tail.head` in the recursive step. -/
def headToNext {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    X.obj 0 ⟶ P.tail.head :=
  match P with
  | ⟨_, _, .succ _ toNext _ _ _⟩ => toNext

/-- The new connecting morphism `P.tail.head ⟶ P.head[1]` in the recursive step. -/
def headConnecting {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.tail.head ⟶ P.head⟦(1 : ℤ)⟧ :=
  match P with
  | ⟨_, _, .succ _ _ connecting _ _⟩ => connecting

/-- The new stage triangle in the recursive step is distinguished. -/
theorem head_distinguished {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    Triangle.mk P.headToX P.headToNext P.headConnecting ∈ distTriang D :=
  match P with
  | ⟨_, _, .succ _ _ _ distinguished _⟩ => distinguished

/-- The new stage maps recover the first differential of the finite row. -/
theorem head_comp {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.headToNext ≫ P.tail.headToX = X.map' 0 1 :=
  match P with
  | ⟨_, _, .succ _ _ _ _ comp⟩ => comp

/-- The auxiliary objects `Y_i` of a Postnikov system, indexed in the same left-to-right order as
the objects of the finite complex `X`. -/
def Y {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin (n + 1)) : D :=
  match n, X, P, i with
  | 0, _, P, _ => P.head
  | _ + 1, _, P, ⟨0, _⟩ => P.head
  | _ + 1, _, P, ⟨i + 1, hi⟩ => P.tail.Y ⟨i, Nat.lt_of_succ_lt_succ hi⟩

@[simp] theorem Y_zero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.Y 0 = P.head :=
  rfl

@[simp] theorem Y_succ {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X)
    (i : Fin (n + 1)) :
    P.Y i.succ = P.tail.Y i :=
  rfl

@[simp] theorem Y_one {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.Y 1 = P.tail.head := sorry

/-- A Postnikov system can be evaluated at an index to recover its auxiliary object `Y_i`. -/
instance : CoeFun (PostnikovSystem X) (fun _ ↦ Fin (n + 1) → D) where
  coe P := P.Y

/-- The comparison morphism `Y_i ⟶ X_i` at each stage. -/
def toX {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin (n + 1)) :
    P i ⟶ X.obj i :=
  match n, X, P, i with
  | 0, _, P, ⟨0, _⟩ => P.headToX
  | _ + 1, _, P, ⟨0, _⟩ => P.headToX
  | _ + 1, _, P, ⟨i + 1, hi⟩ => P.tail.toX ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The rightmost comparison morphism `Y_0 ⟶ X_0` is an isomorphism. -/
instance toX_last_isIso {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) :
    IsIso (P.toX (Fin.last n)) := by
  match n, X, P with
  | 0, _, P =>
      change IsIso P.headToX
      cases P with
      | mk head headToX step =>
          cases step
          infer_instance
  | _ + 1, _, P =>
      simpa [toX, tail] using PostnikovSystem.toX_last_isIso P.tail

/-- The morphism `X_i ⟶ Y_{i - 1}` completing the distinguished triangle at stage `i`. -/
def toNext {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    X.obj i.castSucc ⟶ P i.succ :=
  match n, X, P, i with
  | 0, _, P, i => nomatch i
  | _ + 1, _, P, ⟨0, _⟩ =>
      cast (by
        cases P with
        | mk head headToX step =>
            cases step
            simp [tail]) P.headToNext
  | _ + 1, _, P, ⟨i + 1, hi⟩ =>
      cast (by cases P; rfl) (P.tail.toNext ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/-- The connecting morphism `Y_{i - 1} ⟶ Y_i[1]` of the distinguished triangle at stage `i`. -/
def connecting {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    P i.succ ⟶ (P i.castSucc)⟦(1 : ℤ)⟧ :=
  match n, X, P, i with
  | 0, _, P, i => nomatch i
  | _ + 1, _, P, ⟨0, _⟩ =>
      cast (by
        cases P with
        | mk head headToX step =>
            cases step
            simp [tail]) P.headConnecting
  | _ + 1, _, P, ⟨i + 1, hi⟩ =>
      cast (by cases P; rfl) (P.tail.connecting ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

theorem head_distinguished_stage {n : ℕ} {X : ComposableArrows D (n + 1)}
    (P : PostnikovSystem X) :
    Triangle.mk (P.toX 0) (P.toNext 0) (P.connecting 0) ∈ distTriang D := sorry

theorem head_comp_stage {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.toNext 0 ≫ P.toX 1 = X.map' 0 1 := sorry

/-- Each step of the Postnikov system is a distinguished triangle
`Y_i ⟶ X_i ⟶ Y_{i - 1} ⟶ Y_i[1]`. -/
theorem distinguished {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    Triangle.mk (P.toX i.castSucc) (P.toNext i) (P.connecting i) ∈ distTriang D := by
  match n, X, P, i with
  | 0, _, P, i => exact Fin.elim0 i
  | _ + 1, _, P, ⟨0, _⟩ =>
      exact P.head_distinguished_stage
  | _ + 1, _, P, ⟨i + 1, hi⟩ =>
      simpa [toX, toNext, connecting, tail, Y] using
        P.tail.distinguished ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The morphism `X_i ⟶ Y_{i - 1}` composed with `Y_{i - 1} ⟶ X_{i - 1}` is the given
differential of the finite complex. -/
theorem comp {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    P.toNext i ≫ P.toX i.succ = X.map' i.1 i.1.succ := by
  match n, X, P, i with
  | 0, _, P, i => exact Fin.elim0 i
  | _ + 1, _, P, ⟨0, _⟩ =>
      exact P.head_comp_stage
  | _ + 1, _, P, ⟨i + 1, hi⟩ =>
      simpa [toX, toNext, tail, Y] using P.tail.comp ⟨i, Nat.lt_of_succ_lt_succ hi⟩

attribute [reassoc] PostnikovSystem.comp
attribute [simp] PostnikovSystem.comp_assoc

/-- The distinguished triangle at stage `i` of a Postnikov system. -/
abbrev triangle (P : PostnikovSystem X) (i : Fin n) : Triangle D :=
  Triangle.mk (P.toX i.castSucc) (P.toNext i) (P.connecting i)

/-- Each stage triangle of a Postnikov system is distinguished. -/
theorem triangle_distinguished (P : PostnikovSystem X) (i : Fin n) :
    P.triangle i ∈ distTriang D :=
  P.distinguished i

end PostnikovSystem

/-- A morphism of Postnikov systems over a morphism of finite complexes is a compatible family of
maps on the auxiliary objects `Y_i` commuting with the comparison morphisms and with each
distinguished triangle step. -/
structure PostnikovSystemMorphism {n : ℕ} {X X' : ComposableArrows D n}
    (P : PostnikovSystem X) (P' : PostnikovSystem X') (φ : X ⟶ X') where
  /-- The component maps `Y_i ⟶ Y'_i` between the auxiliary objects. -/
  yMap (i : Fin (n + 1)) : P i ⟶ P' i
  /-- The maps `Y_i ⟶ X_i` are compatible with the given morphism of complexes. -/
  comm_toX (i : Fin (n + 1)) : CommSq (P.toX i) (yMap i) (φ.app i) (P'.toX i)
  /-- The maps `X_i ⟶ Y_{i - 1}` commute with the morphism of complexes and the maps on the
  auxiliary objects. -/
  comm_toNext (i : Fin n) :
    CommSq (P.toNext i) (φ.app i.castSucc) (yMap i.succ) (P'.toNext i)
  /-- The connecting morphisms `Y_{i - 1} ⟶ Y_i[1]` commute with the shifted maps on the
  auxiliary objects. -/
  comm_connecting (i : Fin n) :
    CommSq (P.connecting i) (yMap i.succ) ((yMap i.castSucc)⟦(1 : ℤ)⟧') (P'.connecting i)

namespace PostnikovSystemMorphism

variable {n : ℕ} {X X' : ComposableArrows D n}
variable {P : PostnikovSystem X} {P' : PostnikovSystem X'} {φ : X ⟶ X'}

/-- A morphism of Postnikov systems induces a morphism between the stage triangles. This is the
canonical bridge from the source-facing owner `PostnikovSystemMorphism` to the triangle-category
owner. -/
@[simps!]
def triangleMorphism (ψ : PostnikovSystemMorphism P P' φ) (i : Fin n) :
    P.triangle i ⟶ P'.triangle i :=
  Triangle.homMk _ _ (ψ.yMap i.castSucc) (φ.app i.castSucc) (ψ.yMap i.succ)
    (ψ.comm_toX i.castSucc).w (ψ.comm_toNext i).w (ψ.comm_connecting i).w

/-- The comparison maps `Y_i ⟶ X_i` commute with the maps of the underlying finite rows. -/
@[reassoc]
theorem comm_toX_w (ψ : PostnikovSystemMorphism P P' φ) (i : Fin (n + 1)) :
    P.toX i ≫ φ.app i = ψ.yMap i ≫ P'.toX i :=
  (ψ.comm_toX i).w

/-- The maps `X_i ⟶ Y_{i - 1}` commute with the maps of Postnikov systems. -/
@[reassoc]
theorem comm_toNext_w (ψ : PostnikovSystemMorphism P P' φ) (i : Fin n) :
    P.toNext i ≫ ψ.yMap i.succ = φ.app i.castSucc ≫ P'.toNext i :=
  (ψ.comm_toNext i).w

/-- The connecting morphisms commute with the shifted maps of Postnikov systems. -/
@[reassoc]
theorem comm_connecting_w (ψ : PostnikovSystemMorphism P P' φ) (i : Fin n) :
    P.connecting i ≫ (ψ.yMap i.castSucc)⟦(1 : ℤ)⟧' = ψ.yMap i.succ ≫ P'.connecting i :=
  (ψ.comm_connecting i).w

attribute [simp] PostnikovSystemMorphism.comm_toX_w_assoc
attribute [simp] PostnikovSystemMorphism.comm_toNext_w_assoc
attribute [simp] PostnikovSystemMorphism.comm_connecting_w_assoc

end PostnikovSystemMorphism

end

end CategoryTheory

/-! ### Example_13_41_2 (from Chap13) -/
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

/-! ### Lemma_13_41_3 (from Chap13) -/
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.41.3:
- primary domain: low-length Postnikov systems in a pretriangulated category;
- inspected canonical owner declarations:
  `PostnikovSystem`,
  `PostnikovSystemMorphism`,
  `CommSq`,
  `PostnikovSystem.mk₀`,
  `ComposableArrows.homMk₀` / `ComposableArrows.hom_ext₀`,
  `ComposableArrows.homMk₁` / `ComposableArrows.hom_ext₁`;
- best owner abstraction: the source-facing objects remain `PostnikovSystem X` and
  `PostnikovSystemMorphism P P' φ`, while the core/canonical low-length bookkeeping is handled by
  the existing `ComposableArrows` owners and the triangle API from `Definition_13_41_1`;
- primitive-vs-derived split:
  primitive data: a Postnikov system and a morphism of Postnikov systems;
  derived API: the length-`0` and length-`1` componentwise descriptions coming from the canonical
    `ComposableArrows` small-length API, the triangle view of a stage of a Postnikov system, and
    the induced complexness of the underlying `ComposableArrows` object.

Source/core/bridge triage:
- source-facing: the existence and uniqueness statements about `PostnikovSystem` and
  `PostnikovSystemMorphism`;
- core/canonical: `ComposableArrows` in lengths `0`, `1`, and `2`, together with the
  distinguished-triangle API;
- bridge/view: identifying the length-`1` case with extending an arrow to a distinguished triangle
  and the length-`0` case with the unique component map on the sole auxiliary object.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

-- Proof sketch: a length-`0` complex is just one object, so the source-facing owner
-- `PostnikovSystem X` is given directly by the canonical base constructor `PostnikovSystem.mk₀`.
/-- Lemma 13.41.3 (1): every length-`0` complex in a triangulated category admits a Postnikov
system. -/
theorem length_zero_postnikovSystem_exists (X : ComposableArrows D 0) :
    Nonempty (PostnikovSystem X) :=
  ⟨PostnikovSystem.mk₀ (X.obj 0) (𝟙 (X.obj 0))⟩

-- Proof sketch: for `n = 0`, the only square to satisfy is the compatibility with
-- `Y₀ ⟶ X₀`, so the extension problem is governed by the unique component map in
-- `ComposableArrows D 0`.
/-- Lemma 13.41.3 (2): for length `0`, every morphism of complexes extends to a morphism of
Postnikov systems. -/
theorem length_zero_morphism_extension_exists
    {X X' : ComposableArrows D 0} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Nonempty (PostnikovSystemMorphism P P' φ) := by
  let e : P' 0 ≅ X'.obj 0 := by
    simpa using asIso (P'.toX (Fin.last 0))
  let yMap : (i : Fin (0 + 1)) → P i ⟶ P' i := fun i ↦
    match i with
    | ⟨0, _⟩ => P.toX 0 ≫ φ.app 0 ≫ e.inv
  refine ⟨{
    yMap := yMap
    comm_toX := ?_
    comm_toNext := fun i ↦ Fin.elim0 i
    comm_connecting := fun i ↦ Fin.elim0 i
  }⟩
  intro i
  fin_cases i
  refine CommSq.mk ?_
  simp [yMap, e]

-- Proof sketch: for `n = 0`, a morphism of Postnikov systems is determined by its only component
-- on `Y₀`, and the compatibility with `Y₀ ⟶ X₀` forces that component uniquely.
/-- Lemma 13.41.3 (3): for length `0`, the extension of a morphism of complexes to Postnikov
systems is unique. -/
theorem length_zero_morphism_extension_subsingleton
    {X X' : ComposableArrows D 0} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Subsingleton (PostnikovSystemMorphism P P' φ) := by
  let e : P' 0 ≅ X'.obj 0 := by
    simpa using asIso (P'.toX (Fin.last 0))
  refine ⟨?_⟩
  intro ψ ψ'
  have h0 : ψ.yMap 0 = ψ'.yMap 0 := by
    have hcomm : ψ.yMap 0 ≫ P'.toX 0 = ψ'.yMap 0 ≫ P'.toX 0 := by
      simpa using (ψ.comm_toX 0).w.symm.trans (ψ'.comm_toX 0).w
    have := congrArg (fun f ↦ f ≫ e.inv) hcomm
    simpa [Category.assoc, e] using this
  have hy : ψ.yMap = ψ'.yMap := by
    funext i
    fin_cases i
    exact h0
  cases ψ
  cases ψ'
  cases hy
  simp

-- Proof sketch: every arrow in a triangulated category extends to a distinguished triangle, and
-- that core triangle owner is exactly the data of a length-`1` Postnikov system.
/-- Lemma 13.41.3 (4): every length-`1` complex in a triangulated category admits a Postnikov
system. -/
theorem length_one_postnikovSystem_exists (X : ComposableArrows D 1) :
    Nonempty (PostnikovSystem X) := sorry

-- Proof sketch: after choosing distinguished triangles for the two length-`1` Postnikov systems,
-- TR3 extends the given morphism of arrows to a morphism of triangles, hence to a morphism of
-- Postnikov systems.
/-- Lemma 13.41.3 (5): for length `1`, every morphism of complexes extends to a morphism of
Postnikov systems. -/
theorem length_one_morphism_extension_exists
    {X X' : ComposableArrows D 1} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Nonempty (PostnikovSystemMorphism P P' φ) := sorry

-- Proof sketch: choose a Postnikov system for the tail `X₁ ⟶ X₀`, factor `X₂ ⟶ X₁` through the
-- auxiliary object using the vanishing of the composite `X₂ ⟶ X₁ ⟶ X₀`, and complete that factor
-- to a distinguished triangle.
/-- Lemma 13.41.3 (6): every length-`2` complex in a triangulated category admits a Postnikov
system. This is the first non-formal existence step beyond the vacuous length-`0` and triangle
length-`1` owner cases. -/
theorem length_two_postnikovSystem_exists (X : ComposableArrows D 2) (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := sorry

end

-- Proof sketch: the textbook statement is a non-universality claim. One exhibits a triangulated
-- category, two length-`2` complexes with chosen Postnikov systems, and a morphism of complexes
-- for which no compatible morphism of Postnikov systems exists.
/-- Lemma 13.41.3 (7): for length `2`, it is not true in general that every morphism of complexes
extends to a morphism of Postnikov systems. -/
theorem length_two_morphism_extension_not_universal :
    ¬ ∀ {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] {X X' : ComposableArrows D 2}
        (P : PostnikovSystem X) (P' : PostnikovSystem X') (φ : X ⟶ X'),
          Nonempty (PostnikovSystemMorphism P P' φ) := sorry

-- Proof sketch: for each `n > 2`, one uses a standard counterexample showing that some
-- length-`n` complex in a triangulated category does not admit any Postnikov system.
/-- Lemma 13.41.3 (8): for every `n > 2`, it is not true in general that every length-`n` complex
in a triangulated category admits a Postnikov system. -/
theorem length_gt_two_postnikovSystem_existence_not_universal (n : ℕ) (hn : 2 < n) :
    ¬ ∀ {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] (X : ComposableArrows D n)
        (hX : X.IsComplex), Nonempty (PostnikovSystem X) := sorry

end CategoryTheory

/-! ### Lemma_13_41_4 (from Chap13) -/
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.41.4:
- primary domain: Postnikov systems in a pretriangulated category and stagewise Hom-vanishing;
- inspected owner declarations:
  `shifted_hom_vanishes_above_successor`,
  `ComposableArrows.intFamily`,
  `PostnikovSystem.intFamily`,
  `PostnikovSystem`,
  `PostnikovSystemMorphism`;
- best owner abstraction: the familywise vanishing condition is already owned by
  `shifted_hom_vanishes_above_successor` on ℤ-indexed object families, and the finite-row
  bookkeeping should be routed through the owner bridges `X.intFamily` and `P'.intFamily`;
- source/core/bridge triage:
  `source-facing`: the extension existence statement for morphisms of Postnikov systems,
  `core/canonical`: the owner vanishing predicate `shifted_hom_vanishes_above_successor`,
  `bridge/view`: the owner-level auxiliary-family view `P'.intFamily`;
- primitive-vs-derived split:
  primitive data: a Postnikov system `P'` and the owner vanishing hypothesis on `X` and `X'`,
  derived API: the entrywise zero-morphism conclusion for maps into the auxiliary objects of `P'`.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

-- Proof sketch: induct on the stage `b` of the Postnikov system `P'`. For the inductive step,
-- use the distinguished triangle `Y'_b ⟶ X'_b ⟶ Y'_{b-1} ⟶ Y'_b[1]` and the resulting exact
-- sequence of Hom groups; the outer terms vanish by the induction hypothesis and the assumed
-- vanishing into `X'_b`.
/-- Lemma 13.41.4 (1): if `P'` is a Postnikov system on `X'` and
`Hom(X_i[i - j - 1], X'_j) = 0` for `i > j + 1`, then also
`Hom(X_i[i - j - 1], Y'_j) = 0` for `i > j + 1`, where `Y'_j` is the `j`th auxiliary object of
`P'`. The main statement is kept at the owner level
`shifted_hom_vanishes_above_successor X.intFamily P'.intFamily`; the pointwise
zero-morphism
form is the companion theorem `postnikov_auxiliary_vanishing_apply`. -/
theorem postnikov_auxiliary_vanishing
    {n : ℕ} {X X' : ComposableArrows D n} (P' : PostnikovSystem X')
    (h : shifted_hom_vanishes_above_successor X.intFamily X'.intFamily) :
    shifted_hom_vanishes_above_successor X.intFamily P'.intFamily := sorry

/-- The owner-level vanishing result of Lemma 13.41.4 (1), specialized back to the original
entrywise zero-morphism form for maps into the auxiliary objects of `P'`. -/
theorem postnikov_auxiliary_vanishing_apply
    {n : ℕ} {X X' : ComposableArrows D n} (P' : PostnikovSystem X')
    (h : shifted_hom_vanishes_above_successor X.intFamily X'.intFamily)
    {a b : Fin (n + 1)} (hab : a.1 + 1 < b.1)
    (f : ShiftedHom (X.obj a) (P' b) ((a.1 : ℤ) + 1 - b.1)) :
    f = 0 := by
  have hsub :
      Subsingleton (ShiftedHom (X.obj a) (P' b) ((a.1 : ℤ) + 1 - b.1)) :=
    P'.subsingleton_hom_of_shifted_hom_vanishes_above_successor
      (postnikov_auxiliary_vanishing P' h) hab
  exact hsub.elim f 0

-- Proof sketch: induct on the length of the Postnikov system extension problem. After extending
-- the morphism on the shorter truncation, the obstruction to commutativity at the top stage
-- factors through `Y'_{j-1}[-1]`; part (1) makes that obstruction vanish, and then TR3 supplies
-- the missing morphism of distinguished triangles.
/-- Lemma 13.41.4 (2): if `P` and `P'` are Postnikov systems on two complexes and
`Hom(X_i[i - j - 1], X'_j) = 0` for `i > j + 1`, then any morphism of complexes `φ : X ⟶ X'`
extends to a morphism of Postnikov systems. The vanishing hypothesis is taken directly in the
owner form `shifted_hom_vanishes_above_successor X.intFamily X'.intFamily`. -/
theorem morphism_extends_to_postnikovSystemMorphism
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (h : shifted_hom_vanishes_above_successor X.intFamily X'.intFamily) :
    Nonempty (PostnikovSystemMorphism P P' φ) := sorry

end

end CategoryTheory

/-! ### Lemma_13_41_5 (from Chap13) -/
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.41.5:
- primary domain: uniqueness of morphisms of Postnikov systems in a pretriangulated category under
  Hom-vanishing hypotheses;
- inspected owner declarations:
  `ShiftedHom`,
  `shifted_hom_vanishes_above_successor`,
  `PostnikovSystemMorphism`,
  `PostnikovSystemMorphism.triangleMorphism`,
  `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`;
- best owner abstraction:
  `source-facing`: the three global textbook Hom-vanishing alternatives for Postnikov systems,
  `core/canonical`: the triangle category owner together with the stagewise uniqueness theorem
    `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`, the shifted-Hom owner `ShiftedHom`, and
    the chapter-level familywise vanishing owner `shifted_hom_vanishes_above_successor`,
  `bridge/view`: the stagewise triangle morphisms `ψ.triangleMorphism i` and the canonical
    translation between the source-facing index formulas and those owner-level shifted-Hom
    vanishing predicates;
- primitive-vs-derived split:
  primitive data: the two Postnikov systems and the source-facing global vanishing alternative,
  derived API: the induced triangle-level uniqueness statements obtained by applying
    `triangleMorphism_eq_of_outer_eq_of_hom_vanishing` to the stage triangles. The third
  alternative remains source-facing here, rather than being repackaged, because this file does
    not yet have an upstream owner predicate for the paired cross-vanishing hypothesis. -/

-- Proof sketch: argue by induction on the length of the Postnikov systems. In the first two
-- vanishing cases, the successive maps to or from the extreme auxiliary object are forced stage by
-- stage by the distinguished triangles of the Postnikov systems. In the third case, compare two
-- candidate morphisms on the top distinguished triangles and apply
-- `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`, using the stated cross-vanishing together
-- with the inductive description of the auxiliary objects exactly as in Lemmas 13.41.4 and 13.4.8.
/-- Lemma 13.41.5: if any one of the three textbook Hom-vanishing hypotheses holds for two
Postnikov systems over a morphism `φ : X ⟶ X'`, then there exists at most one morphism of
Postnikov systems lying over `φ`. -/
theorem postnikovSystemMorphism_subsingleton_of_hom_vanishing
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (hvan :
      (∀ a : Fin n, Subsingleton (ShiftedHom (X.obj a.castSucc) (P' 0) (a.1 : ℤ))) ∨
        (∀ a : Fin n,
          Subsingleton (ShiftedHom (P 0) (X'.obj a.succ) (-((a.1 : ℤ) + 1)))) ∨
          (∀ ⦃a b : Fin (n + 1)⦄, b < a →
            Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
              Subsingleton (ShiftedHom (X.obj b) (X'.obj a) ((b.1 : ℤ) - a.1)))) :
    Subsingleton (PostnikovSystemMorphism P P' φ) := sorry

end

end CategoryTheory

/-! ### Lemma_13_41_6 (from Chap13) -/
universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.41.6:
- primary domain: existence and uniqueness of finite Postnikov systems in a pretriangulated
  category under stagewise Hom-vanishing;
- inspected owner declarations:
  `PostnikovSystem`,
  `shifted_hom_vanishes_above_successor`,
  `morphism_extends_to_postnikovSystemMorphism`,
  `Pretriangulated.isIso₃_of_isIso₁₂`;
- best owner abstraction:
  `source-facing`: existence of `PostnikovSystem X` and isomorphism between two such systems;
  `core/canonical`: the extension owner `morphism_extends_to_postnikovSystemMorphism` and the
    stagewise distinguished-triangle two-out-of-three theorem
    `Pretriangulated.isIso₃_of_isIso₁₂`;
  `bridge/view`: the triangle-valued view `P.triangle i` of each Postnikov stage;
- primitive-vs-derived split:
  primitive data: the complex `X`, its complexness hypothesis, and the source-facing vanishing
  predicate `shifted_hom_vanishes_above_successor`;
  derived API: existence of an identity-over morphism of Postnikov systems and the resulting
    stagewise isomorphism statement. -/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]
variable {n : ℕ}

open PostnikovSystemMorphism

namespace PostnikovSystemMorphism

-- Proof sketch: for the induced morphism between the stage triangles of `P` and `P'`, the middle
-- component is the identity on `X`, hence an isomorphism. Starting from the rightmost stage, where
-- `toX` is an isomorphism by definition, apply `Pretriangulated.isIso₃_of_isIso₁₂` inductively to
-- the stage triangle morphisms to show that each auxiliary component map `ψ.yMap i` is an
-- isomorphism.
/-- Under the vanishing hypothesis of Lemma 13.41.6 (2), any morphism of Postnikov systems over the
identity of `X` is stagewise an isomorphism on the auxiliary objects. This is the derived
stagewise-isomorphism API attached to the source-facing uniqueness statement. -/
theorem yMap_isIso_of_extension_vanishing
    {X : ComposableArrows D n} {P P' : PostnikovSystem X}
    (ψ : PostnikovSystemMorphism P P' (𝟙 X))
    (h : shifted_hom_vanishes_above_successor X.intFamily X.intFamily)
    (i : Fin (n + 1)) : IsIso (ψ.yMap i) := sorry

end PostnikovSystemMorphism

-- Proof sketch: induct on the length `n`. The cases `n = 0, 1, 2` are Lemma 13.41.3. For the
-- inductive step, choose a Postnikov system on the tail complex, use the long exact Hom sequence
-- of the last distinguished triangle to reduce extension to a vanishing statement for
-- `Hom(X_n, Y_{n - 3}[-1])`, and then deduce that vanishing from the stated hypothesis exactly as
-- in Lemma 13.41.4 (1).
/-- Lemma 13.41.6 (1): if `X` is a finite complex and `Hom(X_i[i - j - 2], X_j) = 0` for
`i > j + 2`, then `X` admits a Postnikov system. This is expressed via the owner hypothesis
`shifted_hom_vanishes_above_successor X.intFamily (fun i ↦ X.intFamily (i - 1))`. -/
theorem postnikovSystem_exists_of_existence_vanishing
    (X : ComposableArrows D n) (hX : X.IsComplex)
    (h : shifted_hom_vanishes_above_successor
      X.intFamily (fun i ↦ X.intFamily (i - 1))) :
    Nonempty (PostnikovSystem X) := sorry

-- Proof sketch: Lemma 13.41.4 (2) applied to the identity morphism of `X` gives a morphism
-- `P ⟶ P'`. Applying `Pretriangulated.isIso₃_of_isIso₁₂` to the induced morphism between the
-- stage triangles of `P` and `P'`, and inducting from the rightmost stage where `toX` is an
-- isomorphism by definition, shows that every component map on the auxiliary objects is an
-- isomorphism.
/-- Lemma 13.41.6 (2): if `Hom(X_i[i - j - 1], X_j) = 0` for `i > j + 1`, then any two
Postnikov systems on `X` are isomorphic. The vanishing hypothesis is taken directly in the owner
form `shifted_hom_vanishes_above_successor X.intFamily X.intFamily`. -/
theorem postnikovSystem_isomorphic_of_extension_vanishing
    {X : ComposableArrows D n} (P P' : PostnikovSystem X)
    (h : shifted_hom_vanishes_above_successor X.intFamily X.intFamily) :
    ∃ ψ : PostnikovSystemMorphism P P' (𝟙 X), ∀ i, IsIso (ψ.yMap i) := by
  rcases morphism_extends_to_postnikovSystemMorphism P P' (𝟙 X) h with ⟨ψ⟩
  exact ⟨ψ, yMap_isIso_of_extension_vanishing ψ h⟩

end

end CategoryTheory
