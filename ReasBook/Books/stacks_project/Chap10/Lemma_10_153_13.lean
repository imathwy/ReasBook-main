import Mathlib
import stacks_project.Chap10.Definition_10_84_1
import stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: Chapter 10 owner predicates for Mittag-Leffler modules and internal direct-sum
  decompositions of modules;
- sampled declarations of the same kind:
  `Module.IsDirectSumOfCountablyGenerated` from `Definition_10_84_1`,
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `DirectSum.IsInternal.submodule_iSupIndep`,
  `DirectSum.IsInternal.submodule_iSup_eq_top`,
  and mathlib's canonical bridge
  `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`;
- best owner abstraction: the DecidableEq-free existence of a family of submodules with
  `iSupIndep`, supremum `⊤`, and finitely presented summands; `DirectSum.IsInternal` is only a
  bridge/view because its use on a family indexed by `ι` requires a proof-only `[DecidableEq ι]`;
- primitive data: an index type, a family of submodules, independence of that family, total
  supremum, and finite presentation of each summand;
- derived API: the companion bridge theorem below converting to and from `DirectSum.IsInternal`;
- layer: `IsDirectSumOfFinitePresentation` is `source-facing`, while the internal-direct-sum
  criterion is a `bridge/view`.
-/

variable (R M)

/-- An `R`-module is a direct sum of finitely presented submodules. -/
def IsDirectSumOfFinitePresentation : Prop :=
  ∃ (ι : Type w) (A : ι → Submodule R M),
    iSupIndep A ∧ iSup A = (⊤ : Submodule R M) ∧ ∀ i, Module.FinitePresentation R (A i)

-- Proof sketch: use the canonical mathlib criterion
-- `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` to translate between the public
-- DecidableEq-free owner and the internal-direct-sum view.
/-- `Module.IsDirectSumOfFinitePresentation` is equivalent to the existence of an internal
direct-sum decomposition by finitely presented submodules. This companion theorem keeps
`DirectSum.IsInternal` as a bridge view, not as the owner predicate, because it requires a
proof-only `DecidableEq` witness on the index type. -/
theorem isDirectSumOfFinitePresentation_iff_exists_internal :
    IsDirectSumOfFinitePresentation.{u, v, w} R M ↔
      ∃ (ι : Type w) (_ : DecidableEq ι) (A : ι → Submodule R M),
        DirectSum.IsInternal A ∧ ∀ i, Module.FinitePresentation R (A i) := by
  constructor
  · rintro ⟨ι, A, hindep, htop, hfp⟩
    classical
    refine ⟨ι, inferInstance, A, ?_, hfp⟩
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hindep, htop⟩
  · rintro ⟨ι, _, A, hA, hfp⟩
    rcases (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp hA with
      ⟨hindep, htop⟩
    exact ⟨ι, A, hindep, htop, hfp⟩

section

variable [CommRing R]
variable [HenselianLocalRing R]

-- Proof sketch: for each generator of `M`, use the finite-presentation factorization lemma and the
-- henselian splitting argument from the textbook to split off a finitely presented direct summand
-- containing that generator; iterate over a countable generating family and identify `M` with the
-- internal direct sum of the resulting finitely presented summands.
/-- Lemma 10.153.13: over a henselian local ring, every countably generated Mittag-Leffler module
is an internal direct sum of finitely presented `R`-submodules. This is the canonical Lean form of
the textbook statement that such a module is a direct sum of finitely presented modules. -/
theorem isDirectSumOfFinitePresentation_of_henselianLocalRing_of_countablyGenerated_of_mittagLeffler
    (hcg : CountablyGenerated R M) (hML : MittagLeffler R M) :
    IsDirectSumOfFinitePresentation R M := sorry

end

end

end Module
