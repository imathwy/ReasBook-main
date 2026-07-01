import Mathlib
import stacks_project.Chap15.Definition_15_28_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory ComplexShape HomologicalComplex
open scoped KoszulComplex

section

variable {R : Type u} [CommRing R]

-- Proof sketch: specialize Lemma `15.28.10` to the family linear form `koszulLinearForm fs`,
-- then transport the three linear-map-level Koszul complexes to the family-level complexes on
-- `Fin.snoc fs f`, `Fin.snoc fs g`, and `Fin.snoc fs (f * g)`.
/-- Lemma 15.28.11: for a finite family `fs : Fin r → R`, the Koszul complex on
`Fin.snoc fs (f * g)` is homotopy equivalent to the cone of a map from the canonical degree-one
shift `(((K^•(Fin.snoc fs f)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`
of the Koszul complex on `Fin.snoc fs f` to the Koszul complex on `Fin.snoc fs g`. -/
theorem koszulComplexOn_snoc_mul_exists_homotopyEquiv_homotopyCofiber
    {r : ℕ} (fs : Fin r → R) (f g : R) :
    ∃ α :
        (((K^•(Fin.snoc fs f)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction
            embeddingDownNat ⟶
        K^•(Fin.snoc fs g),
      Nonempty (HomotopyEquiv (K^•(Fin.snoc fs (f * g))) (homotopyCofiber α)) := sorry
