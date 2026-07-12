import Mathlib
import StacksProject_2024.Chap34.Definition_34_10_7

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the general scheme-cover/base-change pattern, and
-- the local Chapter 34 precedent in `Lemma_34_9_8` packages the three pretopology axioms as
-- source-facing closure lemmas on the covering predicate itself. We therefore state this item
-- directly on `IsVCovering`.

variable {T T' : Scheme.{u}} {ι : Type v} {κ : ι → Type w}

/-- Lemma 34.10.9 (1): if `f : T' ⟶ T` is an isomorphism, then the singleton family `{T' ⟶ T}` is
a `V` covering of `T`. -/
@[stacks 0ETJ]
theorem isVCovering_singleton_of_isIso (f : T' ⟶ T) [IsIso f] :
    IsVCovering T (fun _ : Unit ↦ T') (fun _ ↦ f) := sorry

/-- Lemma 34.10.9 (2): if `Tᵢ ⟶ T` is a `V` covering and each `Tᵢⱼ ⟶ Tᵢ` is a `V` covering, then
the composite family `Tᵢⱼ ⟶ T` is a `V` covering. -/
@[stacks 0ETJ]
theorem IsVCovering.comp (Ti : ι → Scheme.{u}) (f : ∀ i, Ti i ⟶ T)
    (Tij : ∀ i, κ i → Scheme.{u}) (g : ∀ i j, Tij i j ⟶ Ti i)
    (hTi : IsVCovering T Ti f) (hTij : ∀ i, IsVCovering (Ti i) (Tij i) (g i)) :
    IsVCovering T (fun p : Sigma κ ↦ Tij p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) := sorry

/-- Lemma 34.10.9 (3): if `Tᵢ ⟶ T` is a `V` covering and `T' ⟶ T` is any morphism, then the
pullback family `T' ×[T] Tᵢ ⟶ T'` is a `V` covering of `T'`. -/
@[stacks 0ETJ]
theorem IsVCovering.pullback (Ti : ι → Scheme.{u}) (f : ∀ i, Ti i ⟶ T)
    (hTi : IsVCovering T Ti f) (g : T' ⟶ T) :
    IsVCovering T' (fun i : ι ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g) := sorry

end AlgebraicGeometry
