import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory SimplexCategory.Truncated
open SimplexCategory.Truncated.Hom
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SimplicialObject.Truncated

open SimplicialObject.Splitting (IndexSet)

/-
Domain-style sampling for Definition 14.18.1:
- primary domain: split simplicial objects and their truncated degreewise coproduct decompositions
- sampled owner API:
  `SimplicialObject.Splitting`,
  `SimplicialObject.Splitting.summand`,
  `SimplicialObject.Splitting.cofan'`,
  `SimplicialObject.Splitting.cofan`
- best owner abstraction: the source-facing owner
  `SimplicialObject.Truncated.Splitting X`, mirroring the established mathlib owner
  `SimplicialObject.Splitting X`
- primitive data: the chosen degreewise summands `N`, their inclusions `ι`, and the colimit
  witness `isColimit'`
- derived API: the canonical cofan `s.cofan Δ` and its colimit witness `s.isColimit Δ`
- source/core/bridge triage: this file is `source-facing`; the ordinary simplicial-object owner is
  the `core/canonical` model for statement shape, while the repeated arithmetic turning a surjection
  index into a truncated degree is only implementation bookkeeping and should stay internal
-/

namespace Splitting

private abbrev summandBound {n : ℕ} {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (A : IndexSet (op Δ.unop.obj)) : A.1.unop.len ≤ n :=
  (len_le_of_epi A.e).trans Δ.unop.property

private def summandDegree {n : ℕ} {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (A : IndexSet (op Δ.unop.obj)) : Fin (n + 1) :=
  ⟨A.1.unop.len, Nat.lt_succ_of_le (summandBound A)⟩

private abbrev summandMap {n : ℕ} {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (A : IndexSet (op Δ.unop.obj)) : Δ.unop ⟶ ⦋A.1.unop.len, summandBound A⦌ₙ :=
  tr A.e Δ.unop.property (summandBound A)

/-- For a truncated simplicial object, the summand indexed by a surjection onto `Δ` is the object
in the truncated degree of the codomain simplex. -/
@[simp, nolint unusedArguments]
def summand {n : ℕ} (N : Fin (n + 1) → C) (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (A : IndexSet (op Δ.unop.obj)) : C :=
  N (summandDegree A)

/-- The canonical cofan attached to splitting data on a truncated simplicial object. -/
def cofan' {n : ℕ} (N : Fin (n + 1) → C) (X : SimplicialObject.Truncated C n)
    (ι : ∀ m, N m ⟶ X _⦋m⦌ₙ)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Cofan (summand N Δ) :=
  Cofan.mk (X.obj Δ) fun A ↦
    ι (summandDegree A) ≫ X.map (summandMap A).op

end Splitting

/-- Definition 14.18.1: a splitting of an `n`-truncated simplicial object consists of chosen
nondegenerate summands in degrees `0` through `n` whose canonical coproduct cofan indexed by
surjections onto each degree is colimiting; for ordinary simplicial objects the corresponding
notion is `SimplicialObject.Splitting`. -/
@[stacks 017P]
structure Splitting {n : ℕ} (X : SimplicialObject.Truncated C n) where
  /-- The nondegenerate summand in each truncated degree. -/
  N : Fin (n + 1) → C
  /-- The inclusion of the nondegenerate summand into the corresponding degree. -/
  ι : ∀ m, N m ⟶ X _⦋m⦌ₙ
  /-- Each truncated degree is the coproduct of the chosen nondegenerate summands indexed by
  surjections onto that degree. -/
  isColimit' : ∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)

/-- The canonical cofan associated to a truncated splitting. -/
def Splitting.cofan {n : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Cofan (Splitting.summand s.N Δ) :=
  Cofan.mk (X.obj Δ) fun A ↦
    s.ι (summandDegree A) ≫ X.map (summandMap A).op

/-- The canonical cofan of a truncated splitting is colimiting. -/
def Splitting.isColimit {n : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) : IsColimit (s.cofan Δ) :=
  s.isColimit' Δ

end SimplicialObject.Truncated

end CategoryTheory
