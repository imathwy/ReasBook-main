import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 0D7Z]
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
    P.Y 1 = P.tail.head := by
  -- The first successor stage reduces to the zero stage of the truncated Postnikov system.
  cases P with
  | mk head headToX step =>
      cases step with
      | succ tail toNext connecting distinguished comp =>
          cases tail <;> rfl

/-- Helper for Definition 13.41.1: the first successor index of `Y` is `P.tail.head`. -/
@[simp] theorem Y_succZero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.Y (Fin.succ 0) = P.tail.head := by
  -- This is the `i = 0` instance of the recursive successor formula for `Y`.
  simpa using (P.Y_succ 0)

/-- Helper for Definition 13.41.1: the first cast-successor index of `Y` is `P.head`. -/
@[simp] theorem Y_castSuccZero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.Y (Fin.castSucc 0) = P.head := by
  rfl

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
  | 0, _, _, i => nomatch i
  | _ + 1, _, P, ⟨0, _⟩ =>
      P.headToNext.cast rfl P.Y_succZero.symm
  | _ + 1, _, P, ⟨i + 1, hi⟩ =>
      let j : Fin _ := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      (P.tail.toNext j).cast rfl (P.Y_succ j.succ).symm

/-- The connecting morphism `Y_{i - 1} ⟶ Y_i[1]` of the distinguished triangle at stage `i`. -/
def connecting {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    P i.succ ⟶ (P i.castSucc)⟦(1 : ℤ)⟧ :=
  match n, X, P, i with
  | 0, _, _, i => nomatch i
  | _ + 1, _, P, ⟨0, _⟩ =>
      P.headConnecting.cast P.Y_succZero.symm
        (congrArg (fun Y ↦ Y⟦(1 : ℤ)⟧) P.Y_castSuccZero.symm)
  | _ + 1, _, P, ⟨i + 1, hi⟩ =>
      let j : Fin _ := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      (P.tail.connecting j).cast (P.Y_succ j.succ).symm
        (congrArg (fun Y ↦ Y⟦(1 : ℤ)⟧) (P.Y_succ j.castSucc).symm)

/-- Helper for Definition 13.41.1: the stage-0 `toNext` accessor is the stored head-step map. -/
@[simp] theorem toNext_zero_def {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.toNext 0 = P.headToNext.cast rfl P.Y_succZero.symm := by
  -- The zero branch of `toNext` is definitionally the stored head-step morphism.
  rfl

/-- Helper for Definition 13.41.1: the stage-0 `connecting` accessor is the stored head
connecting morphism. -/
@[simp] theorem connecting_zero_def {n : ℕ} {X : ComposableArrows D (n + 1)}
    (P : PostnikovSystem X) :
    P.connecting 0 = P.headConnecting.cast P.Y_succZero.symm
      (congrArg (fun Y ↦ Y⟦(1 : ℤ)⟧) P.Y_castSuccZero.symm) := by
  -- The zero branch of `connecting` is definitionally the stored head-step morphism.
  rfl

/-- Helper for Definition 13.41.1: the successor branch of `toNext` is inherited from the tail
Postnikov system. -/
@[simp] theorem toNext_succ_def {n : ℕ} {X : ComposableArrows D (n + 2)} (P : PostnikovSystem X)
    (i : Fin (n + 1)) :
    P.toNext i.succ = (P.tail.toNext i).cast rfl (P.Y_succ i.succ).symm := by
  -- Expanding the recursive accessor at a successor index lands in the tail branch.
  cases i using Fin.cases with
  | zero =>
      rfl
  | succ i =>
      rfl

/-- Helper for Definition 13.41.1: the successor branch of `connecting` is inherited from the tail
Postnikov system. -/
@[simp] theorem connecting_succ_def {n : ℕ} {X : ComposableArrows D (n + 2)}
    (P : PostnikovSystem X) (i : Fin (n + 1)) :
    P.connecting i.succ = (P.tail.connecting i).cast (P.Y_succ i.succ).symm
      (congrArg (fun Y ↦ Y⟦(1 : ℤ)⟧) (P.Y_succ i.castSucc).symm) := by
  -- Expanding the recursive accessor at a successor index lands in the tail branch.
  cases i using Fin.cases with
  | zero =>
      rfl
  | succ i =>
      rfl

theorem head_distinguished_stage {n : ℕ} {X : ComposableArrows D (n + 1)}
    (P : PostnikovSystem X) :
    Triangle.mk (P.toX 0) (P.toNext 0) (P.connecting 0) ∈ distTriang D := by
  -- Route correction: reduce the recursive constructor and its tail until the endpoint casts are
  -- literally `rfl`, so the goal becomes the stored distinguished triangle.
  cases P with
  | mk head headToX step =>
      cases step with
      | succ tail toNext connecting distinguished comp =>
          cases tail <;>
            simpa [PostnikovSystem.toX, PostnikovSystem.toNext, PostnikovSystem.connecting,
              PostnikovSystem.tail, PostnikovSystem.Y, Quiver.Hom.cast_rfl_rfl] using
              distinguished

theorem head_comp_stage {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.toNext 0 ≫ P.toX 1 = X.map' 0 1 := by
  -- Route correction: reduce the recursive constructor and tail until the stage-0 comparison map
  -- is literally the stored factorization of the first differential.
  cases P with
  | mk head headToX step =>
      cases step with
      | succ tail toNext connecting distinguished comp =>
          cases tail <;>
            simpa [PostnikovSystem.toX, PostnikovSystem.toNext, PostnikovSystem.tail,
              PostnikovSystem.Y, Quiver.Hom.cast_rfl_rfl] using comp

/-- Each step of the Postnikov system is a distinguished triangle
`Y_i ⟶ X_i ⟶ Y_{i - 1} ⟶ Y_i[1]`. -/
theorem distinguished {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    Triangle.mk (P.toX i.castSucc) (P.toNext i) (P.connecting i) ∈ distTriang D := by
  match n, X, P, i with
  | 0, _, P, i => exact Fin.elim0 i
  | _ + 1, _, P, ⟨0, _⟩ =>
      exact P.head_distinguished_stage
  | _ + 1, _, P, ⟨i + 1, hi⟩ =>
      -- Successor stages are inherited verbatim from the tail Postnikov system.
      simpa [toX, PostnikovSystem.toNext_succ_def, PostnikovSystem.connecting_succ_def] using
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
      -- The successor comparison map is exactly the one from the tail Postnikov system.
      simpa [toX, PostnikovSystem.toNext_succ_def] using
        P.tail.comp ⟨i, Nat.lt_of_succ_lt_succ hi⟩

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
