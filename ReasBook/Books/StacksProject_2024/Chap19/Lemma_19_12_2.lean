import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

section

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local notation "Cpx" => CochainComplex C ℤ

/- Domain-style sampling for Lemma 19.12.2:
- primary domain: acyclic cochain complexes in a Grothendieck abelian category, together with the
  canonical bounded-above predicate and termwise subobject-cardinality bounds;
- sampled owner declarations:
  `CochainComplex.Acyclic`,
  `CochainComplex.IsStrictlyLE`,
  `Cardinal.mk (Subobject (K.X n))`,
  `exists_subobject_surjecting_onto_of_epi_le_generator_coproduct_size`;
- best owner abstraction: the ambient owner is a cochain complex `K : CochainComplex C ℤ`, with
  boundedness expressed by `∃ b, K.IsStrictlyLE b`, acyclicity by `K.Acyclic`, and size by the
  canonical formula `∀ n, Cardinal.mk (Subobject (K.X n)) ≤ κ`;
- primitive data: a cochain complex, a cardinal `κ`, and the two source conclusions about a
  nonzero acyclic subcomplex and a coproduct presentation;
- derived API: later lemmas may consume those two conclusions as hypotheses, but they should not
  be repackaged as new public owner classes.

Source/core/bridge triage:
- `source-facing`: the existence of one cardinal `κ` controlling both the small nonzero acyclic
  subcomplexes and the coproduct presentations from the source lemma;
- `core/canonical`: `K.Acyclic`, `K.IsStrictlyLE b`, and `Cardinal.mk (Subobject (K.X n))`;
- `bridge/view`: none. The main entry should therefore remain the direct source-facing theorem,
  stated with the canonical owners rather than a bundled wrapper. -/

-- Proof sketch: choose a generator `U` of `C`, apply Lemma `19.12.1` in a descending induction to
-- every nonzero acyclic complex to obtain nonzero bounded-above acyclic subcomplexes with a
-- uniform termwise size bound, and then use these small subcomplexes through all morphisms
-- `U ⟶ M.X n` to assemble a coproduct of bounded-above acyclic small complexes surjecting onto
-- the original acyclic complex.
/-- Lemma 19.12.2: there is a cardinal `κ` such that every nonzero acyclic cochain complex has a
nonzero bounded-above acyclic subcomplex with termwise size at most `κ`, and every acyclic
cochain complex is a quotient of a coproduct of bounded-above acyclic complexes with the same
termwise size bound. -/
theorem exists_cardinal_for_small_acyclic_subcomplexes_and_coproduct_presentations :
    ∃ κ : Cardinal,
      (∀ (M : Cpx) (_ : M.Acyclic) (_ : ¬ IsZero M),
        ∃ N : Subobject M,
          ¬ IsZero (N : Cpx) ∧
            (∃ b : ℤ, (N : Cpx).IsStrictlyLE b) ∧
            (N : Cpx).Acyclic ∧
            ∀ n : ℤ, Cardinal.mk (Subobject ((N : Cpx).X n)) ≤ κ) ∧
      ∀ (M : Cpx) (_ : M.Acyclic),
        ∃ (ι : Type w) (Mi : ι → Cpx) (f : (∐ fun i : ι ↦ Mi i) ⟶ M),
          Epi f ∧
            ∀ i : ι,
              (∃ b : ℤ, (Mi i).IsStrictlyLE b) ∧
                (Mi i).Acyclic ∧
                ∀ n : ℤ, Cardinal.mk (Subobject ((Mi i).X n)) ≤ κ := sorry

end
end CategoryTheory
