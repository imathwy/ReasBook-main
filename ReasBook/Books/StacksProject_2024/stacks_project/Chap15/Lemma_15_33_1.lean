import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace Algebra.Generators

/- Domain triage:
- primary domain: finite polynomial presentations of commutative algebras and presentation
  independence of local complete intersection kernels;
- sampled owner declarations: `Algebra.Generators.defaultHom`,
  `Algebra.Generators.presentation_cotangent_stable_equiv`,
  `Ideal.IsKoszulRegularIdeal`, and
  `RingTheory.Sequence.isKoszulRegularSequence_of_span_eq`;
- best owner abstraction: the primitive data are the two finite presentation owners
  `P : Generators A B ι` and `Q : Generators A B κ`; the kernel ideals are derived fields of
  those owners, so the independence statement belongs on `Algebra.Generators` rather than as a
  parallel global wrapper;
- primitive vs. derived: `P` and `Q` are primitive public data, while `P.ker`, `Q.ker`, and the
  resulting ring-hom notion of Definition `15.33.2` are derived from that owner data;
- layer triage:
  - `source-facing`: the theorem below asserting that Koszul-regularity of the kernel does not
    depend on the chosen finite presentation;
  - `core/canonical`: `Algebra.Generators`;
  - `bridge/view`: the stable cotangent comparison of Lemma `10.134.15` and the sequence-transfer
    lemmas `15.30.13` through `15.30.15`. -/

-- Proof sketch: compare the two presentations by adjoining both sets of variables and mapping the
-- extra variables to chosen polynomial lifts. The kernel of the combined presentation is generated
-- both by the first kernel together with the new variable differences and by the second kernel
-- together with the opposite variable differences. Lemma `10.134.15` gives the equality of the
-- local conormal ranks, Lemma `15.30.15` transfers Koszul-regularity between generating sequences
-- of the same length for the same ideal, and Lemmas `15.30.13` and `15.30.14` add and then remove
-- the obvious regular variable-difference sequences. Any auxiliary reindexing to `Fin` belongs
-- only inside that proof bridge via `Fintype.ofFinite` and `Fintype.equivFin`, not in the public
-- theorem statement.
/-- Helper for Lemma 15.33.1: one implication is reduced to transporting a localized Koszul
regular witness across the composite presentation `Q.comp P`. -/
lemma ker_isKoszulRegularIdeal_of_presentation {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Generators A B ι) (Q : Generators A B κ)
    (hP : P.ker.IsKoszulRegularIdeal) :
    Q.ker.IsKoszulRegularIdeal := by
  -- Proof comment: fix `Fintype` structures so the eventual source-faithful route can reindex both
  -- presentations to `Fin` without changing the public statement.
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  -- Route correction: the available compiled API already gives the composite-presentation kernel
  -- identities, but the current environment does not provide the compiled Koszul generator-change
  -- and append/quotient transfer lemmas needed to turn those identities into a witness for `Q.ker`.
  -- TODO(Lemma 15.33.1): reindex `P` and `Q` to `Fin`, compare both kernels inside `Q.comp P`
  -- via `Generators.ker_comp_eq_sup`, `Generators.map_toComp_ker`, and `Generators.map_ofComp_ker`,
  -- then use the missing sequence-transfer API corresponding to Lemmas `15.30.13`, `15.30.14`,
  -- and `15.30.15` to move the localized Koszul witness from `P.ker` to `Q.ker`.
  sorry

/-- Lemma 15.33.1: for two finite polynomial presentations of the same `A`-algebra `B`, the
kernel ideal of one presentation is Koszul-regular if and only if the kernel ideal of the other
presentation is Koszul-regular. Equivalently, Koszul-regularity of the kernel is independent of
the chosen finite presentation. -/
theorem ker_isKoszulRegularIdeal_iff {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Generators A B ι) (Q : Generators A B κ) :
    P.ker.IsKoszulRegularIdeal ↔ Q.ker.IsKoszulRegularIdeal := by
  constructor
  · intro hP
    -- Proof comment: the forward implication is the one-direction composite-presentation transfer.
    exact ker_isKoszulRegularIdeal_of_presentation P Q hP
  · intro hQ
    -- Proof comment: symmetry reduces the reverse implication to the same transfer lemma.
    exact ker_isKoszulRegularIdeal_of_presentation Q P hQ

end Algebra.Generators

end
