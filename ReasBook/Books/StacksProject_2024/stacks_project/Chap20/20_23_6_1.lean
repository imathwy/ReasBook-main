import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksProject_2024.Chap20.Lemma_20_9_3

open CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Item 20.23.6.1:
- primary domain: explicit Čech-cochain homotopies on tuple-indexed ordinary Čech terms;
- sampled owner API:
  `cechIntersection`,
  `cechTerm`,
  `cechComplexFunctor`,
  `Tuple.sort`;
- best owner abstraction for this item: the tuplewise Čech owner layer from `Lemma_20_9_3`,
  especially `cechIntersection`, `cechTerm`, and the canonical stable sorting permutation
  `Tuple.sort`; this file is the source-facing first-homotopy formula, so the sorting permutation
  `σ^{i₀ ... iₚ}` and its truncations `σₐ` should be derived canonically here rather than passed in
  as external data.

Source/core/bridge triage:
- `source-facing`: `cechFirstHomotopyToFun`;
- `core/canonical`: `cechIntersection`, `cechTerm`, and `cechComplexFunctor 𝒰`;
- `bridge/view`: the canonical sorting/truncation permutations induced by `Tuple.sort`, together
  with the induced presheaf transport written directly via `F.map`.

Primitive data versus derived API:
- primitive data: an ordinary Čech tuple `I`, the canonical sorting permutation `Tuple.sort I`,
  the truncation permutations `σₐ`, and the repeated-index tuple built from them;
- derived API: the canonical restriction from the repeated tuple intersection back to the original
  Čech intersection, used in the first homotopy formula. -/

-- Proof sketch: repeating one entry in the tuple does not change the infimum of the associated
-- family of opens.
/-- Repeating one entry in a finite Čech tuple does not change the corresponding intersection. -/
theorem cechIntersection_comp_predAbove_eq (𝒰 : ι → Opens X) {p : ℕ}
    (σ : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    cechIntersection 𝒰 (σ ∘ a.predAbove) = cechIntersection 𝒰 σ := by
  apply le_antisymm
  · refine le_iInf fun i ↦ ?_
    simpa [cechIntersection] using
      (iInf_le (fun j : Fin (p + 2) ↦ 𝒰 (σ (a.predAbove j))) (a.castSucc.succAbove i))
  · refine le_iInf fun i ↦ ?_
    simpa [cechIntersection] using
      (iInf_le (fun j : Fin (p + 1) ↦ 𝒰 (σ j)) (a.predAbove i))

/-- Helper for 20.23.6.1 and 20.23.6.2: the restriction map induced by deleting one repeated entry
from a finite Čech tuple. -/
def cechDuplicateTransport (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    F.obj (op (cechIntersection 𝒰 (σ ∘ a.predAbove))) ⟶
      F.obj (op (cechIntersection 𝒰 σ)) :=
  F.map (eqToHom (cechIntersection_comp_predAbove_eq 𝒰 σ a).symm).op

section

variable [LinearOrder ι]

private def cechFirstHomotopySplitEquiv (p : ℕ) (a : Fin (p + 1)) :
    Fin a.1 ⊕ Fin (p + 1 - a.1) ≃ Fin (p + 1) :=
  (@finSumFinEquiv a.1 (p + 1 - a.1)).trans
    (finCongr (Nat.add_sub_of_le (Nat.le_of_lt a.is_lt)))

/-- The source permutation `σₐ`: keep the first `a` positions of the stable sorting permutation of
`I`, and sort the tail positions by their original indices. -/
private def cechFirstHomotopyPerm {p : ℕ} (I : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    Equiv.Perm (Fin (p + 1)) :=
  let σ := Tuple.sort I
  let e := cechFirstHomotopySplitEquiv p a
  let tail : Fin (p + 1 - a.1) → Fin (p + 1) := fun j ↦ σ (e (Sum.inr j))
  (e.symm.trans ((Equiv.sumCongr (Equiv.refl _) (Tuple.sort tail)).trans e)).trans σ

private def cechFirstHomotopyIndexTuple {p : ℕ} (I : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    Fin (p + 2) → Fin (p + 1) :=
  let σ := Tuple.sort I
  let σa := cechFirstHomotopyPerm I a
  let e := cechFirstHomotopySplitEquiv p a
  let withoutDup : Fin (p + 1) → Fin (p + 1) := fun k ↦
    Sum.elim
      (fun i : Fin a.1 ↦ σ (e (Sum.inl i)))
      (fun j : Fin (p + 1 - a.1) ↦ σa (e (Sum.inr j)))
      (e.symm k)
  a.castSucc.insertNth (σ a) withoutDup

private def cechFirstHomotopyTuple {p : ℕ} (I : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    Fin (p + 2) → ι :=
  I ∘ cechFirstHomotopyIndexTuple I a

private theorem cechIntersection_le_firstHomotopyTuple (𝒰 : ι → Opens X) {p : ℕ}
    (I : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    cechIntersection 𝒰 I ≤ cechIntersection 𝒰 (cechFirstHomotopyTuple I a) := by
  refine le_iInf fun j ↦ ?_
  simpa [cechIntersection, cechFirstHomotopyTuple] using
    (iInf_le (fun k : Fin (p + 1) ↦ 𝒰 (I k)) (cechFirstHomotopyIndexTuple I a j))

/-- Helper for 20.23.6.1: the transport map from the repeated tuple back to the original Čech
intersection. -/
private def cechFirstHomotopyRestriction (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (I : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    F.obj (op (cechIntersection 𝒰 (cechFirstHomotopyTuple I a))) ⟶
      F.obj (op (cechIntersection 𝒰 I)) :=
  F.map (homOfLE (cechIntersection_le_firstHomotopyTuple 𝒰 I a)).op

/-- 20.23.6.1: the first homotopy on ordinary Čech cochains is the alternating sum over
`0 ≤ a ≤ p`, with coefficient `(-1)^a sign(σ_a)`, obtained by evaluating the cochain on the
canonical tuple determined by the stable sorting permutation `σ^{i₀ ... iₚ}` and its truncations
`σₐ`, and transporting back to the original Čech intersection. -/
@[stacks 01FN]
def cechFirstHomotopyToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v})
    (p : ℕ) : cechTerm 𝒰 F (p + 1) → cechTerm 𝒰 F p :=
  fun s I ↦
    ∑ a : Fin (p + 1),
      (((-1 : ℤ) ^ (a : ℕ)) * Equiv.Perm.sign (cechFirstHomotopyPerm I a)) •
        cechFirstHomotopyRestriction 𝒰 F I a (s (cechFirstHomotopyTuple I a))

/-- The first Čech homotopy is additive on cochains. -/
private theorem cechFirstHomotopyToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : cechTerm 𝒰 F (p + 1)) :
    cechFirstHomotopyToFun 𝒰 F p (s + t) =
      cechFirstHomotopyToFun 𝒰 F p s + cechFirstHomotopyToFun 𝒰 F p t := by
  sorry

/-- The degree-`p` component of the first Čech homotopy as a morphism of Čech terms. -/
def cechFirstHomotopyComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechTerm 𝒰 F (p + 1) ⟶ cechTerm 𝒰 F p :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (cechFirstHomotopyToFun 𝒰 F p)
      (cechFirstHomotopyToFun_map_add 𝒰 F p))

@[simp] theorem cechFirstHomotopyComponent_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : cechTerm 𝒰 F (p + 1)) (I : Fin (p + 1) → ι) :
    cechFirstHomotopyComponent 𝒰 F p s I =
      cechFirstHomotopyToFun 𝒰 F p s I := rfl

end
