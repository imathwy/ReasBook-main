import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_84_1
import stacks_proof.stacks_project.Chap10.Lemma_10_95_1
import stacks_proof.stacks_project.Chap10.Lemma_10_95_2
import stacks_proof.stacks_project.Chap10.Theorem_10_93_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

omit [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] in
/-- Helper for Chap10 Lemma 10 95 3: a countably generated module is the internal direct sum of
the single top submodule. -/
private theorem isDirectSumOfCountablyGenerated_of_countablyGenerated
    (hcg : Module.CountablyGenerated R M) :
    Module.IsDirectSumOfCountablyGenerated.{u, w, 0} R M := by
  -- Package the trivial one-summand decomposition needed by the projectivity criterion.
  rw [Module.isDirectSumOfCountablyGenerated_iff]
  refine ⟨PUnit.{1}, fun _ ↦ (⊤ : Submodule R M), ?_, ?_, ?_⟩
  · exact iSupIndep_subsingleton _
  · simp
  · intro _
    exact hcg

/- Source/core/bridge triage:
* source-facing: descent of the countably generated projective condition along a faithfully flat
  base change;
* core/canonical owners: the chapter owner `Module.CountablyGenerated` from
  `Definition_10_84_1` and the owner predicate `Module.Projective`;
* sampled upstream declarations in this domain:
  `Module.countablyGenerated_iff`,
  `Module.countablyGenerated_of_countablyGenerated_tensorProduct_of_faithfullyFlat`,
  `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated`;
* bridge/view: the theorem below packages the source statement in terms of these owner
  predicates, so no local duplicate owner for countable generation is needed here.
-/

-- Proof sketch: descend countable generation by Lemma `10.95.2`; for projectivity, use Theorem
-- `10.93.3` on the base-changed module, descend flatness and the Mittag-Leffler property by
-- faithful flatness, and use the countably generated hypothesis to obtain the required
-- countably-generated direct-sum decomposition on the `R`-side.
/-- Chap10 Lemma 10 95 3: if the faithfully flat base change `S ⊗[R] M` is countably generated and
projective over `S`, then `M` is countably generated and projective over `R`. This is the
canonical Lean form of the textbook statement for `M ⊗_R S`. -/
@[stacks 05A6]
theorem countablyGenerated_projective_of_countablyGenerated_projective_tensorProduct_of_faithfullyFlat
    [Module.Projective S (S ⊗[R] M)] (hcg : Module.CountablyGenerated S (S ⊗[R] M)) :
    Module.CountablyGenerated R M ∧ Module.Projective R M := by
  -- First descend the countable generating set along the faithfully flat algebra.
  have hcgR : Module.CountablyGenerated R M :=
    Module.countablyGenerated_of_countablyGenerated_tensorProduct_of_faithfullyFlat
      (R := R) (S := S) (M := M) hcg
  -- Projectivity after base change supplies flatness and Mittag-Lefflerness over `S`.
  have hprojectiveDataS :=
    (Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated.{v, max v w, 0}
      (R := S) (M := S ⊗[R] M)).mp inferInstance
  have hflatTensor : Module.Flat S (S ⊗[R] M) := hprojectiveDataS.1
  have hMLTensor : Module.MittagLeffler S (S ⊗[R] M) := hprojectiveDataS.2.1
  -- Faithfully flat descent transfers the two remaining projectivity-criterion hypotheses to `R`.
  have hflatR : Module.Flat R M :=
    (Module.Flat.iff_flat_tensorProduct (R := R) (M := M) S).mp hflatTensor
  have hMLR : Module.MittagLeffler R M := by
    letI : Module.MittagLeffler S (S ⊗[R] M) := hMLTensor
    exact Module.mittagLeffler_of_mittagLeffler_tensorProduct_of_faithfullyFlat
      (R := R) (S := S) (M := M)
  have hsumR : Module.IsDirectSumOfCountablyGenerated R M :=
    isDirectSumOfCountablyGenerated_of_countablyGenerated (R := R) (M := M) hcgR
  -- The chapter projectivity criterion now reassembles projectivity over the original base.
  refine ⟨hcgR, ?_⟩
  exact (Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated.{u, w, 0}
    (R := R) (M := M)).mpr ⟨hflatR, hMLR, hsumR⟩

end

end Module
