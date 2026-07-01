import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.2 introduces, for a subset `S` and a function
  `f : S → α ∪ {+∞}`, the function `h` given by the supremum
  `h(y) = sup_{x ∈ S} (⟪x, y⟫ - f(x))`.
- `core/canonical`: the chapter owner abstraction for Fenchel conjugation is
  `convexConjugate` from `Defn_12_2`, already stated for arbitrary pairings and codomains with
  supremum and subtraction.
- `bridge/view`: restricted source data is compared to the ambient owner by the canonical subtype
  bridge `Function.extendByTop` from `Defn_12_4`, applied to the restricted branch.

Primitive data vs derived API:
- primitive source-facing data: the subset `S` and a branch `f : S → L`;
- primitive owner in this file: the restricted conjugate `convexConjugateOn f`;
- derived bridge/view: the ambient `+∞`-extension through the canonical owner
  `Function.extendByTop`, compared with `convexConjugate`.

Layer target: `source-facing`. The textbook object is a conjugate-like supremum attached to
restricted data on `S`. The ambient `convexConjugate` owner remains the canonical comparison
object, and the extension bridge reuses the existing canonical owner instead of introducing a
parallel extension definition.

Topology-language axis for this item: not applicable. This file introduces an owner and a bridge
identity for conjugation; it does not state ambient/intrinsic closure/interior claims.
-/

/-- Definition 17.2.2 owner: for `f : S → L`, the restricted conjugate is just the
Fenchel conjugate on the subtype domain. The primitive pairing assumption is only the pairing on
the source domain `S`, not an ambient pairing assumption on `X`. -/
def convexConjugateOn {L : Type*} {S : Set X} [SupSet L] [Sub L]
    [HasPairing S Y L] (f : S → L) : Y → L :=
  f⋆

section AmbientBridge

variable {L : Type*} [CompleteLattice L] [Sub L]

/-- The restricted conjugate from Definition 17.2.2 is the ambient Fenchel conjugate of the
canonical subtype-extension-by-`⊤` of the branch. The bridge uses only codomain-level data:
complete-lattice supremum, subtraction, and the off-domain law `a - ⊤ = ⊥`. -/
theorem convexConjugateOn_eq_convexConjugate_extendByTop {S : Set X}
    [HasPairing X Y L]
    (hsub_top : ∀ a : L, a - (⊤ : L) = (⊥ : L))
    (f : S → L) :
    convexConjugateOn f =
      (((Function.extendByTop f)⋆) : Y → L) := by
  let fExt : X → L := Function.extendByTop f
  change convexConjugateOn f = ((fExt)⋆ : Y → L)
  ext y
  rw [convexConjugateOn]
  rw [convexConjugate_eq_iSup_pairing_sub (f := f) (y := y)]
  rw [convexConjugate_eq_iSup_pairing_sub (f := fExt) (y := y)]
  let gS : S → L := fun x ↦ (⟪x, y⟫ₚ : L) - f x
  let gX : X → L := fun x ↦ (⟪x, y⟫ₚ : L) - fExt x
  change (iSup gS : L) = (iSup gX : L)
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    have hxext : fExt x = f x := by
      simp [fExt]
    calc
      gS x = gX x := by
        dsimp [gS, gX]
        rw [hxext]
        rfl
      _ ≤ ⨆ x : X, gX x := by
        exact le_iSup gX x
  · refine iSup_le ?_
    intro x
    by_cases hx : x ∈ S
    · let xS : S := ⟨x, hx⟩
      have hxext : fExt x = f xS := by
        simpa [fExt, xS] using
          (Function.extendByTop_apply_of_mem (g := f) (x := x) hx)
      calc
        gX x = gS xS := by
          dsimp [gS, gX]
          rw [hxext]
          rfl
        _ ≤ ⨆ x : S, gS x := by
          exact le_iSup gS xS
    · have hxTop : fExt x = (⊤ : L) := by
        simpa [fExt] using
          (Function.extendByTop_apply_of_notMem
            (g := f) (x := x) hx)
      calc
        gX x = (⊥ : L) := by
          have hpair_sub_top :
              (⟪x, y⟫ₚ : L) - (⊤ : L) = (⊥ : L) :=
            hsub_top (⟪x, y⟫ₚ : L)
          simpa [gX, hxTop] using hpair_sub_top
        _ ≤ ⨆ x : S, gS x := by
          exact (bot_le : (⊥ : L) ≤ ⨆ x : S, gS x)

end AmbientBridge

end
