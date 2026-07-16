import stacks_proof.stacks_project.Chap10.Lemma_10_39_12
import stacks_proof.stacks_project.Chap10.Lemma_10_81_3
import stacks_proof.stacks_project.Chap10.Theorem_10_82_3
import Mathlib.Tactic.StacksAttribute

universe u

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: for a short exact complex `S` ending in `M`, Theorem `10.82.3` identifies
-- `S.UniversallyExact` with surjectivity on `Hom` from finitely presented modules, and an
-- isomorphism `S.X₃ ≅ M` transports that condition to the criterion in Lemma `10.81.3`. For the
-- converse, realize an arbitrary surjection onto `M` as the right map of a short exact sequence
-- and apply the assumed universal exactness of every such sequence.
/-- Lemma 10.82.5: an `R`-module `M` is flat if and only if every short exact sequence of
`R`-modules whose rightmost term is isomorphic to `M` is universally exact. -/
@[stacks 058M]
theorem flat_iff_forall_universallyExact_of_shortExact_right_iso :
    Module.Flat R M ↔
      ∀ (S : ShortComplex (ModuleCat R)),
        S.ShortExact →
        Nonempty (S.X₃ ≅ ModuleCat.of R M) →
        S.UniversallyExact := by
  constructor
  · intro hM S hS ⟨e⟩
    let _ : Module.Flat R (ModuleCat.of R M) := hM
    let _ : Module.Flat R S.X₃ := Module.Flat.of_linearEquiv e.toLinearEquiv
    exact ShortExact.universallyExact_of_flat_X₃ hS
  · intro h
    refine flat_iff_postcompose_surjective_on_hom_from_finitelyPresented.2 ?_
    intro P _ _ _ N _ _ π hπ
    let S : ShortComplex (ModuleCat R) := π.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
    have hU : S.UniversallyExact := h S hS ⟨Iso.refl _⟩
    have hsurj : HomSurjectiveOnFinitelyPresented S :=
      ((universallyExact_tfae hS).out 0 4).mp hU
    intro f
    obtain ⟨g, hg⟩ := hsurj (ModuleCat.of R P) (ModuleCat.ofHom f)
    refine ⟨g.hom, ?_⟩
    simpa [S] using congrArg ModuleCat.Hom.hom hg

end

end CategoryTheory.ShortComplex
