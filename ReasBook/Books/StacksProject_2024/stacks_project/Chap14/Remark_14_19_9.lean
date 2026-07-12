import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable [∀ n : ℕ, ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.incl n (n + 1)).op.HasRightKanExtension F]

/- Domain-style sampling for Remark 14.19.9:
- primary domain: truncated simplicial objects, one-step coskeleton stages, and right Kan
  extensions along the inclusions `Δ≤n ↪ Δ≤(n + 1)`;
- sampled owner declarations:
  `Truncated.trunc`,
  `Functor.ran`,
  `Functor.ranAdjunction`,
  `Truncated.cosk`,
  `coskAdj`;
- best owner abstraction: the source-facing stage `U^{n + 1}` is the right Kan extension of
  `U^n` along `SimplexCategory.Truncated.incl n (n + 1)`, and the full `m`-coskeleton is the
  core canonical endpoint obtained after passing from these stages to all simplices;
- primitive data: an `m`-truncated simplicial object `U` and the one-step right Kan extensions
  along `Δ≤n ↪ Δ≤(n + 1)`;
- derived API: the one-step stage `\tilde U`, the recursive family `U^{m + k}`, the Hom-set
  equivalences expressing the universal property of each stage, and the bridge from those stages
  to the full owner `Truncated.cosk`.

Source/core/bridge triage:
- `source-facing`: the recursive stage family `U^m = U`, `U^{n + 1} = \tilde U^n`, together with
  the formulas `Mor_{Simp_{m + k}}(V, U^{m + k}) ≃ Mor_{Simp_m}(sk_m V, U)` and
  `Mor_{Simp(C)}(V, cosk_m U) ≃ Mor_{Simp_m(C)}(sk_m V, U)`;
- `core/canonical`: the generic right Kan extension owner `Functor.ran` and its adjunction
  `Functor.ranAdjunction`, plus the eventual full owner `Truncated.cosk` with adjunction
  `coskAdj`;
- `bridge/view`: the thin abbreviation `tilde`, which keeps the source surface while delegating
  all universal properties to the owner adjunctions, together with the derived comparison between
  `stage U k` and `cosk_m U` on Hom-sets. -/

namespace SimplicialObject.Truncated

/-- The one-step stage `\tilde U` of an `n`-truncated simplicial object, defined as the right Kan
extension of `U` along `Δ≤n ↪ Δ≤(n + 1)`. This is the source-facing bridge from the recursive
construction to the canonical owner `Functor.ran`. -/
abbrev tilde {n : ℕ} (U : SimplicialObject.Truncated C n) :
    SimplicialObject.Truncated C (n + 1) :=
  ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.ran).obj U

/-- The one-step universal property of `\tilde U`: morphisms into the one-step stage correspond to
morphisms from the truncation back to `U`. This is the source-facing bridge to the canonical
Hom-set equivalence of the right Kan extension adjunction. -/
noncomputable abbrev tildeHomEquiv {n : ℕ} (U : SimplicialObject.Truncated C n)
    (V : SimplicialObject.Truncated C (n + 1)) :
    (V ⟶ tilde U) ≃ ((Truncated.trunc C (n + 1) n (Nat.le_succ n)).obj V ⟶ U) :=
  (((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.ranAdjunction C).homEquiv
    V U).symm

section OneStep

variable {n : ℕ} (U : SimplicialObject.Truncated C n) (V : SimplicialObject.Truncated C (n + 1))

/- Remark 14.19.9, one-step universal property: morphisms from an `(n + 1)`-truncated simplicial
object `V` to `\tilde U` are naturally equivalent to morphisms from the `n`-truncation of `V` to
`U`. This is the symmetric form of the canonical Hom-set equivalence of the right Kan extension
adjunction along `Δ≤n ↪ Δ≤(n + 1)`. -/
#check (tildeHomEquiv U V :
  (V ⟶ tilde U) ≃ ((Truncated.trunc C (n + 1) n (Nat.le_succ n)).obj V ⟶ U))

end OneStep

/-- The recursive stages of Remark 14.19.9. Here `stage U k` is the source's object
`U^{m + k}` when `U : SimplicialObject.Truncated C m`. -/
def stage {m : ℕ} (U : SimplicialObject.Truncated C m) (k : ℕ) :
    SimplicialObject.Truncated C (m + k) :=
  match k with
  | 0 => U
  | k + 1 => tilde (stage U k)

@[simp] theorem stage_zero {m : ℕ} (U : SimplicialObject.Truncated C m) :
    stage U 0 = U := rfl

@[simp] theorem stage_succ {m : ℕ} (U : SimplicialObject.Truncated C m) (k : ℕ) :
    stage U (k + 1) = tilde (stage U k) := rfl

/-- Remark 14.19.9, recursive universal formula: for every `k`, morphisms in `Simp_{m + k}` into
the stage `U^{m + k}` are naturally equivalent to morphisms from the `m`-truncation to `U`. This
is the source's all-`n` statement, written in the exact canonical equivalent form `n = m + k`. -/
noncomputable def stageHomEquiv {m : ℕ} (U : SimplicialObject.Truncated C m) (k : ℕ)
    (V : SimplicialObject.Truncated C (m + k)) :
    (V ⟶ stage U k) ≃ ((Truncated.trunc C (m + k) m (Nat.le_add_right m k)).obj V ⟶ U) :=
  match k with
  | 0 => by
      simpa [stage] using Equiv.refl (V ⟶ U)
  | k + 1 => by
      simpa [stage] using (tildeHomEquiv (stage U k) V).trans (stageHomEquiv U k _)

section CoskeletonBridge

variable {m : ℕ}
variable [∀ F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion m).op.HasRightKanExtension F]

/-- Remark 14.19.9, bridge from the recursive stage `U^{m + k}` to the canonical full owner
`cosk_m U`: for any simplicial object `V`, maps `V ⟶ cosk_m U` are naturally equivalent to maps
from the `(m + k)`-truncation of `V` to the recursive stage `U^{m + k}`. -/
noncomputable def homEquivStage (U : SimplicialObject.Truncated C m) (k : ℕ)
    (V : SimplicialObject C) :
    (V ⟶ (Truncated.cosk m).obj U) ≃ ((truncation (m + k)).obj V ⟶ stage U k) := by
  simpa using
    (((coskAdj m).homEquiv V U).symm.trans (stageHomEquiv U k ((truncation (m + k)).obj V)).symm)

/- Remark 14.19.9 also recalls the endpoint `k = 0`, namely the canonical Hom-set equivalence of
the adjunction `truncation m ⊣ Truncated.cosk m`. -/
variable (U : SimplicialObject.Truncated C m) (V : SimplicialObject C)

#check ((((coskAdj m).homEquiv V U).symm :
  (V ⟶ (Truncated.cosk m).obj U) ≃ ((truncation m).obj V ⟶ U)))

end CoskeletonBridge

end SimplicialObject.Truncated

end CategoryTheory
