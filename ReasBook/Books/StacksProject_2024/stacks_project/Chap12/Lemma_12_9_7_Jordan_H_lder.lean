import StacksProject_2024.stacks_project.Chap12.Lemma_12_9_6
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/- Domain triage:
- primary domain: Jordan-Hölder theory for composition series in the subobject lattice of an
  object of an abelian category;
- sampled owner API:
  `CompositionSeries.jordan_holder`,
  `CompositionSeries.Equivalent`,
  `Subobject.iso_iff_nonempty_subobjectSubquotient_iso`,
  `CompositionSeries.factor`;
- `source-facing`: the factors of two composition series from `0` to `A` agree up to permutation
  and isomorphism;
- `core/canonical`: `CompositionSeries.jordan_holder`;
- `bridge/view`: `Subobject.iso_iff_nonempty_subobjectSubquotient_iso` translates the owner
  `Equivalent` relation into isomorphisms between the canonical factor objects `s.factor i`;
- primitive data vs derived API: the Jordan-Hölder equivalence relation on composition series is
  primitive owner output, while the factorwise isomorphism statement is derived bridge API.
-/

/- Lemma 12.9.7 (Jordan-Hölder): for composition series in the Jordan-Hölder lattice
`Subobject A`, the canonical owner theorem is `CompositionSeries.jordan_holder`. -/
recall CompositionSeries.jordan_holder

end CategoryTheory

namespace CompositionSeries

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

-- Proof sketch: unpack the owner theorem `CompositionSeries.jordan_holder` and use the owner
-- `Iso` relation on `Subobject A`, which is defined by isomorphism of the canonical factors.
/-- Companion form of Jordan-Hölder: the factors of two composition series from `0` to `A` agree
up to a permutation and isomorphism. -/
theorem jordan_holder_factors
    (F G : CompositionSeries (Subobject A))
    (hF₀ : F.head = ⊥) (hF₁ : F.last = ⊤) (hG₀ : G.head = ⊥) (hG₁ : G.last = ⊤)
    : ∃ σ : Fin F.length ≃ Fin G.length,
        ∀ i : Fin F.length,
          Nonempty (F.factor i ≅ G.factor (σ i)) := by
  obtain ⟨σ, hσ⟩ := F.jordan_holder G (hF₀.trans hG₀.symm) (hF₁.trans hG₁.symm)
  refine ⟨σ, fun i ↦ ?_⟩
  simpa [factor] using
    (Subobject.iso_iff_nonempty_subobjectSubquotient_iso
      (F.step i).le (G.step (σ i)).le).1 (hσ i)

end CompositionSeries
