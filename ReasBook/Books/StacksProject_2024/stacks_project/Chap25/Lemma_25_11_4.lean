import StacksProject_2024.stacks_project.Chap25.Lemma_25_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace SSet

-- Semantic search note: `lean_leansearch` recalled
-- `TopologicalSpace.Opens.IsBasis.exists_finite_of_isCompact` for finite basis covers of compact
-- opens. The owner remains the local `SSet.OpenHypercovering` from `Lemma_25_11_3`, and the new
-- finiteness condition is recorded degreewise on the simplicial index types.

-- Source/core/bridge triage:
-- `source-facing`: a Chapter 25 `SSet.OpenHypercovering` whose simplicial degree index families
--   are finite;
-- `core/canonical`: the `Finite` typeclass on the simplicial degree index types;
-- `bridge/view`: `OpenHypercovering.degreewiseFinite` and the restriction companion below.

namespace OpenHypercovering

section

variable {X : TopCat.{u}}

/-- An open hypercovering is degreewise finite when each simplicial index type `I_n` is finite. -/
def degreewiseFinite (H : OpenHypercovering X) : Prop :=
  ∀ n : ℕ, Finite (H.I.obj (op <| SimplexCategory.mk n))

/-- Unfolding `degreewiseFinite` says exactly that every simplicial degree index type is finite. -/
theorem degreewiseFinite_iff {X : TopCat.{u}} (H : OpenHypercovering X) :
    H.degreewiseFinite ↔ ∀ n : ℕ, Finite (H.I.obj (op <| SimplexCategory.mk n)) :=
  Iff.rfl

/-- Every simplicial degree index type of a degreewise finite open hypercovering is finite. -/
theorem degreewiseFinite.finite
    {H : OpenHypercovering X} (hH : H.degreewiseFinite) (n : ℕ) :
    Finite (H.I.obj (op <| SimplexCategory.mk n)) :=
  hH n

/-- The degree-`0` index type of a degreewise finite open hypercovering is finite. -/
theorem degreewiseFinite.zero
    {H : OpenHypercovering X} (hH : H.degreewiseFinite) :
    Finite (H.I.obj (op <| SimplexCategory.mk 0)) :=
  hH.finite 0

/-- The degree-`1` index type of a degreewise finite open hypercovering is finite. -/
theorem degreewiseFinite.one
    {H : OpenHypercovering X} (hH : H.degreewiseFinite) :
    Finite (H.I.obj (op <| SimplexCategory.mk 1)) :=
  hH.finite 1

/-- Every degree-`n + 1` index type of a degreewise finite open hypercovering is finite. -/
theorem degreewiseFinite.succ
    {H : OpenHypercovering X} (hH : H.degreewiseFinite) (n : ℕ) :
    Finite (H.I.obj (op <| SimplexCategory.mk (n + 1))) :=
  hH.finite (n + 1)

/-- Restricting to the nonempty simplices preserves degreewise finiteness. -/
theorem degreewiseFinite.restrictToNonempty
    {H : OpenHypercovering X} (hH : H.degreewiseFinite) :
    H.restrictToNonempty.degreewiseFinite := by
  intro n
  let _ : Finite (H.I.obj (op <| SimplexCategory.mk n)) := hH.finite n
  exact Finite.of_injective
    (fun i : H.nonemptySubfunctor.obj (op <| SimplexCategory.mk n) ↦ i.1)
    (fun a b h ↦ Subtype.ext h)

end

end OpenHypercovering

section

variable {X : TopCat.{u}}

/-- Lemma 25.11.4: let `X` be a topological space and let `\mathcal{B}` be a basis for its
topology. Assume `X` is quasi-compact, every `U ∈ \mathcal{B}` is quasi-compact, and the
intersection of any two quasi-compact opens of `X` is quasi-compact. Then there exists a
hypercovering of `X` whose indexed opens all lie in `\mathcal{B}` and whose simplicial degree
index sets are finite; in particular the covering families in degrees `0`, `1`, and `n + 1` are
finite. -/
@[stacks 01H7]
theorem exists_openHypercovering_mem_basis_degreewiseFinite
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hX : IsCompact (Set.univ : Set X))
    (hBqc : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X))
    (hInter : ∀ U V : Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
        IsCompact ((U ⊓ V : Opens X) : Set X)) :
    ∃ H : OpenHypercovering X, H.degreewiseOpensIn B ∧ H.degreewiseFinite := sorry

/-- Source-facing companion to Lemma 25.11.4: the finite hypercovering can be chosen so that the
degree-`0`, degree-`1`, and degree-`n + 1` covering families are finite. -/
theorem exists_openHypercovering_mem_basis_finite_zero_one_succ
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hX : IsCompact (Set.univ : Set X))
    (hBqc : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X))
    (hInter : ∀ U V : Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
        IsCompact ((U ⊓ V : Opens X) : Set X)) :
    ∃ H : OpenHypercovering X,
      H.degreewiseOpensIn B ∧
      Finite (H.I.obj (op <| SimplexCategory.mk 0)) ∧
      Finite (H.I.obj (op <| SimplexCategory.mk 1)) ∧
      ∀ n : ℕ, Finite (H.I.obj (op <| SimplexCategory.mk (n + 1))) := by
  rcases exists_openHypercovering_mem_basis_degreewiseFinite B hB hX hBqc hInter with
    ⟨H, hHB, hHfin⟩
  exact ⟨H, hHB, hHfin.zero, hHfin.one, fun n ↦ hHfin.succ n⟩

end

end SSet
