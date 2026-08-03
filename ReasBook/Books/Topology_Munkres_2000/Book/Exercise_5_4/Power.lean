module

public import Topology_Munkres_2000.Book.Notation_5_3.Tuples
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.PNat.Equiv
public import Mathlib.Data.Set.Inclusion
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Logic.Equiv.Prod

public section

universe u v

open scoped Book

namespace Power

/-- Reindex a finite block followed by a positive-integer-indexed sequence as one
positive-integer-indexed sequence. -/
def finSumPNatEquiv (n : ℕ) : Fin n ⊕ ℕ+ ≃ ℕ+ :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) Equiv.pnatEquivNat).trans
    ((finSumNatEquiv n).trans Equiv.pnatEquivNat.symm)

/-- Reindex two positive-integer-indexed sequences as one such sequence. -/
def pnatSumPNatEquiv : ℕ+ ⊕ ℕ+ ≃ ℕ+ :=
  (Equiv.sumCongr Equiv.pnatEquivNat Equiv.pnatEquivNat).trans
    (Equiv.natSumNatEquivNat.trans Equiv.pnatEquivNat.symm)

/-- Extend a finite power to a larger finite power, filling new coordinates with `x`. -/
noncomputable def finiteEmbedding {X : Type u} (x : X) {m n : ℕ+} (h : m ≤ n) :
    (Fin m → X) ↪ (Fin n → X) :=
  ⟨fun f ↦ Function.extend (Fin.castLEEmb h) f (fun _ ↦ x),
    Function.extend_injective (Fin.castLEEmb h).injective _⟩

/-- Extension to a larger finite power agrees with the original function on old coordinates. -/
@[simp]
theorem finiteEmbedding_apply {X : Type u} (x : X) {m n : ℕ+} (h : m ≤ n)
    (f : Fin m → X) (i : Fin m) :
    finiteEmbedding x h f (Fin.castLE h i) = f i :=
  (Fin.castLEEmb h).injective.extend_apply f (fun _ ↦ x) i

/-- A finite power times a positive-integer-indexed power is equivalent to one
positive-integer-indexed power. -/
def finiteProdSequenceEquiv {X : Type u} (n : ℕ+) :
    ((Fin n → X) × (ℕ+ → X)) ≃ (ℕ+ → X) :=
  (Equiv.sumArrowEquivProdArrow (Fin n) ℕ+ X).symm.trans
    ((finSumPNatEquiv n).arrowCongr (Equiv.refl X))

/-- Embed a finite power into a positive-integer-indexed power by adjoining a
constant tail. -/
def finiteSequenceEmbedding {X : Type u} (x : X) (n : ℕ+) :
    (Fin n → X) ↪ (ℕ+ → X) where
  toFun f := finiteProdSequenceEquiv n (f, fun _ ↦ x)
  inj' _ _ h := congrArg Prod.fst ((finiteProdSequenceEquiv n).injective h)

/-- Adjoining a constant tail agrees with the original function on the finite block. -/
@[simp]
theorem finiteSequenceEmbedding_apply {X : Type u} (x : X) (n : ℕ+)
    (f : Fin n → X) (i : Fin n) :
    finiteSequenceEmbedding x n f (finSumPNatEquiv n (.inl i)) = f i := by
  simp [finiteSequenceEmbedding, finiteProdSequenceEquiv]

/-- Adjoining a constant tail has value `x` on every tail coordinate. -/
@[simp]
theorem finiteSequenceEmbedding_apply_tail {X : Type u} (x : X) (n : ℕ+)
    (f : Fin n → X) (i : ℕ+) :
    finiteSequenceEmbedding x n f (finSumPNatEquiv n (.inr i)) = x := by
  simp [finiteSequenceEmbedding, finiteProdSequenceEquiv]

/-- Two positive-integer-indexed powers can be interleaved into one. -/
def sequenceProdEquiv {X : Type u} :
    ((ℕ+ → X) × (ℕ+ → X)) ≃ (ℕ+ → X) :=
  (Equiv.sumArrowEquivProdArrow ℕ+ ℕ+ X).symm.trans
    (pnatSumPNatEquiv.arrowCongr (Equiv.refl X))

/-- Extend a book-style `m`-tuple to an `n`-tuple, filling new coordinates with `x`. -/
noncomputable def tupleEmbedding {X : Type u} (x : X) {m n : ℕ+} (h : m ≤ n) :
    X ^ m ↪ X ^ n :=
  (Book.Tuple.finEquiv X m).toEmbedding.trans <|
    (finiteEmbedding x h).trans (Book.Tuple.finEquiv X n).symm.toEmbedding

/-- Concatenation of book-style finite tuples. -/
def tupleAppendEquiv {X : Type u} (m n : ℕ+) : (X ^ m × X ^ n) ≃ X ^ (m + n) :=
  (Equiv.prodCongr (Book.Tuple.finEquiv X m) (Book.Tuple.finEquiv X n)).trans <|
    (Fin.appendEquiv m n).trans (Book.Tuple.finEquiv X (m + n)).symm

/-- Embed a book-style finite tuple into an `ω`-tuple by adjoining a constant tail. -/
def tupleSequenceEmbedding {X : Type u} (x : X) (n : ℕ+) : X ^ n ↪ X ^ω :=
  (Book.Tuple.finEquiv X n).toEmbedding.trans (finiteSequenceEmbedding x n)

/-- A book-style finite tuple times an `ω`-tuple is equivalent to one `ω`-tuple. -/
def tupleProdSequenceEquiv {X : Type u} (n : ℕ+) : (X ^ n × X ^ω) ≃ X ^ω :=
  (Equiv.prodCongr (Book.Tuple.finEquiv X n) (Equiv.refl (ℕ+ → X))).trans <|
    finiteProdSequenceEquiv n

/-- Extend an `A`-indexed power to a `B`-indexed power, filling coordinates
outside `A` with `x`. -/
noncomputable def subsetEmbedding {X : Type u} {ι : Type v} (x : X)
    {A B : Set ι} (h : A ⊆ B) : (A → X) ↪ (B → X) :=
  ⟨fun f ↦ Function.extend (Set.inclusion h) f (fun _ ↦ x),
    Function.extend_injective (Set.inclusion_injective h) _⟩

/-- Extension along a subset inclusion agrees with the original function on the subset. -/
@[simp]
theorem subsetEmbedding_apply {X : Type u} {ι : Type v} (x : X)
    {A B : Set ι} (h : A ⊆ B) (f : A → X) (i : A) :
    subsetEmbedding x h f (Set.inclusion h i) = f i :=
  (Set.inclusion_injective h).extend_apply f (fun _ ↦ x) i


end Power
