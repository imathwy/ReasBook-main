import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_4_17 (from Items/Chap01) -/
open scoped BigOperators

universe u v

open List

namespace Cycle

variable {X : Type u}

/-- Cyclic reduction of a representative list is invariant under cyclic permutation. -/
theorem isCyclicallyReduced_iff_of_isRotated {L₁ L₂ : List (X × Bool)} (h : L₁ ~r L₂) :
    FreeGroup.IsCyclicallyReduced L₁ ↔ FreeGroup.IsCyclicallyReduced L₂ := sorry

/-- A cyclically ordered word is reduced when one, equivalently every, representative list is a
cyclically reduced free-group word. -/
def IsCyclicallyReduced (w : Cycle (X × Bool)) : Prop :=
  Quotient.liftOn w FreeGroup.IsCyclicallyReduced fun _ _ h ↦
    propext (isCyclicallyReduced_iff_of_isRotated h)

@[simp] theorem isCyclicallyReduced_coe_iff {L : List (X × Bool)} :
    IsCyclicallyReduced (L : Cycle (X × Bool)) ↔ FreeGroup.IsCyclicallyReduced L :=
  Iff.rfl

/-- Cyclic permutation does not change the conjugacy class of the represented free-group word. -/
theorem conjClasses_mk_eq_of_isRotated {L₁ L₂ : List (X × Bool)} (h : L₁ ~r L₂) :
    ConjClasses.mk (FreeGroup.mk L₁) = ConjClasses.mk (FreeGroup.mk L₂) := by
  rw [List.isRotated_iff_mod] at h
  rcases h with ⟨n, -, rfl⟩
  let A : FreeGroup X := FreeGroup.mk (L₁.take (n % L₁.length))
  let B : FreeGroup X := FreeGroup.mk (L₁.drop (n % L₁.length))
  have hsplit : FreeGroup.mk L₁ = A * B := by
    dsimp [A, B]
    simpa only [FreeGroup.mul_mk] using
      congrArg FreeGroup.mk (List.take_append_drop (n % L₁.length) L₁).symm
  have hrotate : FreeGroup.mk (L₁.rotate n) = B * A := by
    have hrotateList : L₁.rotate n = L₁.drop (n % L₁.length) ++ L₁.take (n % L₁.length) :=
      List.rotate_eq_drop_append_take_mod
    dsimp [A, B]
    simpa [FreeGroup.mul_mk] using
      congrArg FreeGroup.mk hrotateList
  apply ConjClasses.mk_eq_mk_iff_isConj.2
  rw [isConj_iff]
  refine ⟨A⁻¹, ?_⟩
  calc
    A⁻¹ * FreeGroup.mk L₁ * (A⁻¹)⁻¹ = A⁻¹ * (A * B) * A := by rw [hsplit, inv_inv]
    _ = B * A := by group
    _ = FreeGroup.mk (L₁.rotate n) := hrotate.symm

end Cycle

/-- Definition 1-4-17: a cyclic word on the alphabet `X` is a cyclically ordered list of letters
from `X^{±1}`, understood by default to be reduced. The owner abstraction is the rotation quotient
`List.Cycle (X × Bool)`, with cyclic reduction imposed as a predicate on the quotient. -/
abbrev CyclicWord (X : Type u) :=
  { w : Cycle (X × Bool) // w.IsCyclicallyReduced }

namespace CyclicWord

variable {X : Type u}
variable {ι : Type v}

/-- The length of a cyclic word is the length of any representative list. -/
abbrev length (w : CyclicWord X) : ℕ :=
  w.1.length

@[simp] theorem length_mk {L : List (X × Bool)} (hL : (L : Cycle (X × Bool)).IsCyclicallyReduced) :
    length ⟨(L : Cycle (X × Bool)), hL⟩ = L.length :=
  rfl

/-- Forgetting signs yields the cyclic sequence of underlying letters. -/
abbrev letters (w : CyclicWord X) : Cycle X :=
  w.1.map Prod.fst

/-- The unsigned support of a cyclic word. -/
abbrev support [DecidableEq X] (w : CyclicWord X) : Finset X :=
  w.letters.toFinset

/-- A cyclic word has full support when every basis letter occurs, ignoring sign. -/
abbrev HasFullSupport (w : CyclicWord X) : Prop :=
  ∀ x : X, x ∈ w.letters

/-- A reduced cyclic word determines the conjugacy class of the corresponding free-group element. -/
def toConjClasses (w : CyclicWord X) : ConjClasses (FreeGroup X) :=
  Quotient.liftOn w.1 (ConjClasses.mk ∘ FreeGroup.mk) fun _ _ h ↦
    Cycle.conjClasses_mk_eq_of_isRotated h

@[simp] theorem toConjClasses_mk {L : List (X × Bool)}
    (hL : (L : Cycle (X × Bool)).IsCyclicallyReduced) :
    toConjClasses ⟨L, hL⟩ = ConjClasses.mk (FreeGroup.mk L) :=
  rfl

/-- Reduced cyclic words are in one-to-one correspondence with conjugacy classes in the free
group on the same alphabet. -/
private theorem toConjClasses_bijective : Function.Bijective (toConjClasses : CyclicWord X →
    ConjClasses (FreeGroup X)) := sorry

/-- The canonical equivalence between reduced cyclic words and conjugacy classes in the free group
on the same alphabet. -/
noncomputable def conjClassesEquiv : CyclicWord X ≃ ConjClasses (FreeGroup X) :=
  Equiv.ofBijective toConjClasses toConjClasses_bijective

/-- An automorphism of the free group acts on cyclic words via the canonical action on conjugacy
classes. -/
noncomputable def map (α : MulAut (FreeGroup X)) : CyclicWord X → CyclicWord X :=
  conjClassesEquiv.symm ∘ ConjClasses.map α.toMonoidHom ∘ conjClassesEquiv

@[simp] theorem toConjClasses_map (α : MulAut (FreeGroup X)) (w : CyclicWord X) :
    toConjClasses (map α w) = ConjClasses.map α.toMonoidHom (toConjClasses w) := by
  change conjClassesEquiv (map α w) = ConjClasses.map α.toMonoidHom (conjClassesEquiv w)
  simp [map, conjClassesEquiv]

/-- The canonical `Aut(F(X))`-action on cyclic words over `X`, transported from conjugacy
classes. -/
@[reducible] noncomputable instance : MulAction (MulAut (FreeGroup X)) (CyclicWord X) where
  smul α w := map α w
  one_smul w := by
    apply toConjClasses_bijective.1
    change toConjClasses (map 1 w) = toConjClasses w
    rw [toConjClasses_map]
    obtain ⟨a, ha⟩ := ConjClasses.exists_rep (toConjClasses w)
    rw [← ha]
    rfl
  mul_smul α β w := by
    apply toConjClasses_bijective.1
    change toConjClasses (map (α * β) w) = toConjClasses (map α (map β w))
    rw [toConjClasses_map, toConjClasses_map, toConjClasses_map]
    obtain ⟨a, ha⟩ := ConjClasses.exists_rep (toConjClasses w)
    rw [← ha]
    rfl

/-- The total cyclic length of a finite family of cyclic words. -/
def totalLength [Fintype ι] (w : ι → CyclicWord X) : ℕ :=
  ∑ i, (w i).length

end CyclicWord

/-! ### Proposition_1_4_22 (from Items/Chap01) -/
universe u

noncomputable section

section

variable {X : Type u}

open scoped Whitehead

/-- Proposition 1-4-22: if a cyclic word `w'` is the image of a cyclic word `w` under an
automorphism `α` of the free group and `w'` is no longer than `w`, then `α` factors as a product
of Whitehead automorphisms whose nontrivial prefix images of `w` never exceed the original cyclic
length, and are strictly shorter whenever the terminal image is strictly shorter. -/
-- Layer triage:
-- `source-facing`: the cyclic words `w` and `w'`, the ambient automorphism
-- `α : MulAut (FreeGroup X)`, and Whitehead's generating set `Ω`.
-- `core/canonical`: `CyclicWord X`, its canonical length function `CyclicWord.length`, the
-- `MulAut (FreeGroup X)`-action on cyclic words, and the prefix product API
-- `Whitehead.prefixAut`.
-- `bridge/view`: the textbook right-action notation `w α` is rendered by the canonical left
-- action `α • w`, while membership in `Ω` is rendered by `τ ∈ Ω`.
-- Domain sampling:
-- 1. `CyclicWord` from Definition `1-4-17` is the owner abstraction for reduced cyclic words.
-- 2. The `MulAction (MulAut (FreeGroup X)) (CyclicWord X)` instance from Definition `1-4-17` is
--    the canonical `Aut(F(X))`-action on cyclic words.
-- 3. `Whitehead.automorphisms` from Proposition `1-4-25` is the source-facing owner set `Ω`.
-- 4. `Whitehead.prefixAut` from Proposition `1-4-25` is the owner API for the automorphism given
--    by the first `i` Whitehead factors, composed in the textbook left-to-right order.
-- Primitive vs. derived:
-- the primitive data are only `w`, `w'`, and the ambient automorphism `α`; the individual
-- prefix automorphisms and the intermediate cyclic words are derived from the chosen factor list,
-- so the proposition uses the chapter owner declarations directly instead of introducing a
-- parallel factorization wrapper.
-- Proof sketch: start from a Whitehead factorization of `α` and apply Whitehead peak reduction to
-- eliminate every peak whose cyclic length rises above `|w|`, while keeping the same terminal
-- image `w'`. Since `|w'| ≤ |w|`, every surviving interior prefix has length at most `|w|`, and
-- if `|w'| < |w|` then the first step already drops below `|w|`, forcing every later interior
-- prefix to stay strictly below `|w|` as well.
theorem exists_whitehead_factorization_of_cyclicWord_image_length_le
    (w w' : CyclicWord X) (α : MulAut (FreeGroup X))
    (himage : α • w = w')
    (hlen : w'.length ≤ w.length) :
    ∃ τs : List (MulAut (FreeGroup X)),
      τs.reverse.prod = α ∧
        (∀ τ ∈ τs, τ ∈ Ω) ∧
        (∀ i : ℕ, 0 < i → i < τs.length →
          (Whitehead.prefixAut τs i • w).length ≤ w.length) ∧
        (w'.length < w.length →
          ∀ i : ℕ, 0 < i → i < τs.length →
            (Whitehead.prefixAut τs i • w).length < w.length) := sorry

end

/-! ### Proposition_1_4_24 (from Items/Chap01) -/
universe u v

open MulAction

section

variable {F : Type u} [Group F]

/-- The canonical automorphism-orbit relation recovers the textbook automorphism-equivalence
predicate. -/
-- Layer triage:
-- `source-facing`: two elements `w₁ w₂ : F` and the question whether some automorphism sends
-- `w₁` to `w₂`.
-- `core/canonical`: `orbitRel (MulAut F) F`.
-- `bridge/view`: the existential automorphism formulation is recovered by this theorem.
-- Domain sampling:
-- 1. `MulAut F` is mathlib's owner automorphism group of `F`.
-- 2. `orbitRel (MulAut F) F` is mathlib's owner relation for automorphism-equivalence.
-- 3. `mem_orbit_iff` is the canonical bridge from an orbit statement to the existence of a group
--    element realizing it.
theorem automorphism_orbitRel_iff_exists_automorphism_eq (w₁ w₂ : F) :
    orbitRel (MulAut F) F w₂ w₁ ↔
      ∃ α : MulAut F, α w₁ = w₂ := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, by simpa using hα⟩
  · rintro ⟨α, hα⟩
    exact ⟨α, by simpa using hα⟩

end

noncomputable section

section FiniteBasisSearch

variable {ι : Type v} {F : Type u} [Group F]

private def signedBasisLetters (ι : Type v) [Fintype ι] : List (ι × Bool) :=
  ((Fintype.elems : Finset ι).toList).flatMap fun a ↦ [(a, false), (a, true)]

private def basisWordsOfLength (ι : Type v) [Fintype ι] : ℕ → List (List (ι × Bool))
  | 0 => [[]]
  | n + 1 =>
      (basisWordsOfLength ι n).flatMap fun w ↦ (signedBasisLetters ι).map fun a ↦ a :: w

private def basisElementsUpToNorm (basis : FreeGroupBasis ι F) [Finite ι] [DecidableEq ι]
    [DecidableEq F] (m : ℕ) : Finset F := by
  let _ : Fintype ι := Fintype.ofFinite ι
  exact
    (((List.range (m + 1)).flatMap (basisWordsOfLength ι)).map fun w ↦
      basis.repr.symm (FreeGroup.mk w)).toFinset

private def elementaryNielsenGenerators (basis : FreeGroupBasis ι F) [Finite ι] [DecidableEq ι] :
    Finset (MulAut F) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let inversions :=
    ((Fintype.elems : Finset ι).toList).map (basis.elementaryNielsenInversion)
  let transvections :=
    (Fintype.elems : Finset {p : ι × ι // p.1 ≠ p.2}).toList.map
      (fun xy ↦ basis.elementaryNielsenTransvection xy.1.1 xy.1.2 xy.2)
  exact (inversions ++ transvections ++ transvections.map (·⁻¹)).toFinset

private def nextOrbitStates [DecidableEq F] (gens : Finset (MulAut F))
    (candidates states : Finset F) : Finset F :=
  states.biUnion fun w ↦ (gens.image fun σ ↦ σ w).filter fun u ↦ u ∈ candidates

private def reachableOrbitStates [DecidableEq F] (gens : Finset (MulAut F))
    (candidates : Finset F) (w : F) : ℕ → Finset F
  | 0 => {w}
  | n + 1 =>
      let states := reachableOrbitStates gens candidates w n
      states ∪ nextOrbitStates gens candidates states

private noncomputable def automorphismOrbitSearch (basis : FreeGroupBasis ι F) [Finite ι]
    [DecidableEq ι] [DecidableEq F] (w₁ w₂ : F) : Bool := by
  let m := max (FreeGroup.norm (basis.repr w₁)) (FreeGroup.norm (basis.repr w₂))
  let candidates := basisElementsUpToNorm basis m
  let gens := elementaryNielsenGenerators basis
  exact decide (w₂ ∈ reachableOrbitStates gens candidates w₁ candidates.card)

/-- Internal bounded-search specification for Proposition 1-4-24: with respect to a chosen finite
free basis, the automorphism orbit problem is detected by exploring the finite graph of words of
bounded basis length under elementary Nielsen generators. -/
-- Layer triage:
-- `source-facing`: the words `w₁`, `w₂` in a finite-rank free group.
-- `core/canonical`: `orbitRel (MulAut F) F` and the owner basis object `FreeGroupBasis ι F`.
-- `bridge/view`: the search graph is built from elementary Nielsen generators relative to `basis`.
-- Domain sampling:
-- 1. `MulAut F` is mathlib's owner automorphism group.
-- 2. `orbitRel (MulAut F) F` is the owner automorphism-equivalence relation.
-- 3. `FreeGroupBasis ι F` is the chapter/mathlib owner abstraction for a chosen free basis.
-- 4. Proposition `1-4-1` identifies elementary Nielsen automorphisms as the canonical finite-rank
--    generating family of `Aut(F)`.
private theorem automorphism_orbitRel_iff_search_true (basis : FreeGroupBasis ι F) [Finite ι]
    [DecidableEq ι] [DecidableEq F] (w₁ w₂ : F) :
    orbitRel (MulAut F) F w₂ w₁ ↔
      automorphismOrbitSearch basis w₁ w₂ = true := by
  sorry

end FiniteBasisSearch

section AbstractFreeGroup

variable {F : Type u} [Group F] [IsFreeGroup F] [Finite (IsFreeGroup.Generators F)]

/-- Proposition 1-4-24: for a finitely generated free group `F`, it is decidable whether two
elements lie in the same automorphism orbit. -/
-- Layer triage:
-- `source-facing`: the ambient finite-rank free group `F` and the two elements `w₁` and `w₂`.
-- `core/canonical`: `orbitRel (MulAut F) F`.
-- `bridge/view`: `automorphism_orbitRel_iff_exists_automorphism_eq` recovers the textbook
-- existential formulation, while the internal search theorem
-- `automorphism_orbitRel_iff_search_true` realizes Whitehead-style finite-rank decidability using
-- the canonical basis `IsFreeGroup.basis F`.
-- Primitive vs. derived:
-- the primitive public inputs are just `w₁` and `w₂`; the chosen finite basis and the bounded
-- search graph are derived implementation data and stay out of the public interface.
noncomputable def automorphism_orbitRel_decidable (w₁ w₂ : F) :
    Decidable (orbitRel (MulAut F) F w₂ w₁) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  exact
    decidable_of_iff
      (automorphismOrbitSearch basis w₁ w₂ = true)
      (automorphism_orbitRel_iff_search_true basis w₁ w₂).symm

end AbstractFreeGroup

end

/-! ### Proposition_1_4_25 (from Items/Chap01) -/
universe u

noncomputable section

section

variable {X : Type u}

-- Domain sampling for Whitehead automorphisms:
-- 1. `MulAut (FreeGroup X)` is the owner abstraction for automorphisms of the ambient free group.
-- 2. `SignedLetter X` is the project owner vocabulary for signed basis letters.
-- 3. `FreeGroup.mk [x]` is the canonical ambient free-group element represented by one signed
--    letter `x : SignedLetter X`.
-- 4. `SignedLetter` carries the owner involution on signed letters, written as `x⁻¹`.
-- Primitive data for Whitehead automorphisms of the second kind are therefore a multiplier
-- `a : SignedLetter X` together with a subset `A ⊆ X^{±1}` satisfying the textbook constraints
-- `a ∈ A` and `a⁻¹ ∉ A`; the four word-shapes are derived from the membership pattern of
-- `x` and `x⁻¹`.

/- Whitehead's textbook generating set is written `Ω`; membership is the canonical surface
`τ ∈ Ω`. -/
namespace Whitehead

open Classical in
/-- The canonical image of a signed basis letter under Whitehead's second-kind automorphism
determined by multiplier `a` and subset `A ⊆ X^{±1}`. The special letters `a` and `a⁻¹` are
fixed; for every other signed letter, the usual four Whitehead cases are derived from the
membership pattern of `x` and `x⁻¹` in `A`. -/
private def typeTwoImage (a : SignedLetter X) (A : Set (SignedLetter X))
    (x : SignedLetter X) : FreeGroup X :=
  if x = a ∨ x = a⁻¹ then
    FreeGroup.mk [x]
  else if x ∈ A then
    if x⁻¹ ∈ A then
      (FreeGroup.mk [a])⁻¹ * FreeGroup.mk [x] * FreeGroup.mk [a]
    else
      FreeGroup.mk [x] * FreeGroup.mk [a]
  else if x⁻¹ ∈ A then
    (FreeGroup.mk [a])⁻¹ * FreeGroup.mk [x]
  else
    FreeGroup.mk [x]

/-- Whitehead's generating set `Ω` of automorphisms of the free group on `X`. Membership is given
by the textbook disjunction between first-kind and second-kind Whitehead automorphisms. -/
def automorphisms : Set (MulAut (FreeGroup X)) := {τ |
  (∃ σ : Equiv.Perm X, ∃ ε : X → Bool,
      ∀ x : X,
        τ (FreeGroup.of x) = if ε x then FreeGroup.of (σ x) else (FreeGroup.of (σ x))⁻¹) ∨
    ∃ a : SignedLetter X, ∃ A : Set (SignedLetter X),
      a ∈ A ∧ a⁻¹ ∉ A ∧
        ∀ x : SignedLetter X, τ (FreeGroup.mk [x]) = typeTwoImage a A x}

scoped[Whitehead] notation "Ω" => automorphisms

/-- The automorphism given by the first `i` listed Whitehead factors, applied from left to right.
Thus the prefix `[τ₁, …, τᵢ]` acts as `τᵢ * ··· * τ₁`. -/
abbrev prefixAut (τs : List (MulAut (FreeGroup X))) (i : ℕ) : MulAut (FreeGroup X) :=
  (τs.take i).reverse.prod

end Whitehead

open scoped Whitehead

/-- Proposition 1-4-25: if the automorphic image of a finite family of cyclic words under `α` has
minimal total cyclic length among all automorphic images, then `α` admits a factorization into
Whitehead automorphisms such that the successive prefix images strictly decrease total cyclic
length until the terminal minimum is reached, and thereafter keep that minimum fixed. -/
-- Layer triage:
-- `source-facing`: the finite family `w : ι → CyclicWord X`, the automorphism
-- `α : MulAut (FreeGroup X)`, and the source set `Ω` of Whitehead automorphisms.
-- `core/canonical`: `CyclicWord X`, the owner automorphism group `MulAut (FreeGroup X)`, its
-- induced `MulAction` on `CyclicWord X` and on finite families `ι → CyclicWord X`, together
-- with ordinary `Fintype` sums of cyclic lengths.
-- `bridge/view`: `CyclicWord.map` transports the canonical action on conjugacy classes back to
-- reduced cyclic words, while `Whitehead.automorphisms` is the source-facing owner set `Ω`.
-- Domain sampling:
-- 1. `CyclicWord.toConjClasses` is the chapter's owner map from cyclic words to conjugacy classes.
-- 2. `CyclicWord.conjClassesEquiv` is the canonical equivalence used to transport the
--    automorphism action from conjugacy classes back to cyclic words.
-- 3. `ConjClasses.map` in mathlib is the canonical action of a homomorphism on conjugacy classes.
-- 4. The induced Pi-action gives the canonical owner action on finite families
--    `ι → CyclicWord X`, and `CyclicWord.totalLength` is already stated for arbitrary
--    `[Fintype ι]`, so no `Fin t`-specific family owner belongs in the public API here.
-- 5. `SignedLetter X` is the project owner vocabulary for letters of `X^{±1}`.
-- 6. `MulAut (FreeGroup X)` is the owner abstraction for automorphisms of the free group, while
--    the prefix dynamics are derived from `Whitehead.prefixAut`, the induced Pi-action, and
--    ordinary `Fintype` sums.
-- Primitive vs. derived:
-- the primitive data is the family of cyclic words together with the ambient free-group
-- automorphism `α`; the terminal family `α • w`, the cyclic-word action, the total-length
-- functional, and the prefix-stage lengths are derived.
theorem exists_whitehead_factorization_of_minimal_cyclic_word_total_length
    {ι : Type*} [Fintype ι] (w : ι → CyclicWord X) (α : MulAut (FreeGroup X))
    (hmin : ∀ α' : MulAut (FreeGroup X),
      CyclicWord.totalLength (α • w) ≤ CyclicWord.totalLength (α' • w)) :
    ∃ τs : List (MulAut (FreeGroup X)),
      τs.reverse.prod = α ∧
        (∀ τ ∈ τs, τ ∈ Ω) ∧
        ∀ i : ℕ, i < τs.length →
          let prefixLength := CyclicWord.totalLength (Whitehead.prefixAut τs i • w)
          let nextLength := CyclicWord.totalLength (Whitehead.prefixAut τs (i + 1) • w)
          let targetLength := CyclicWord.totalLength (α • w)
          nextLength ≤ prefixLength ∧
            (prefixLength ≠ targetLength → nextLength < prefixLength) := by
  sorry

end
