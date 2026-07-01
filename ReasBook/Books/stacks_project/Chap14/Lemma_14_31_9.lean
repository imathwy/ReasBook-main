import Mathlib
import stacks_project.Chap14.Lemma_14_27_2
import stacks_project.Chap14.Lemma_14_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex
open AlgebraicTopology

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject AddCommGrpCat} {f : X ⟶ Y}

/-
Domain-style sampling for Lemma 14.31.9:
- primary domain: simplicial homotopy equivalences of underlying simplicial sets and the induced
  quasi-isomorphism statement for normalized Moore complexes of simplicial abelian groups;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `CategoryTheory.SimplicialObject.normalizedMooreComplex_map_isHomotopyEquivalence`,
  `CategoryTheory.SimplicialObject.Homotopic.whiskerRight`,
  `HomologicalComplex.homotopyEquivalences`,
  `homotopyEquivalences_le_quasiIso`,
  `HomologicalComplex.mem_quasiIso_iff`;
- best owner abstraction: the source-facing hypothesis is the simplicial homotopy-equivalence
  predicate on the underlying simplicial-set map `Functor.whiskerRight f (forget AddCommGrpCat)`,
  while the target-side canonical owner is the morphism property
  `HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)` and its
  `QuasiIso` consequence;
- primitive-vs-derived split:
  primitive data are only the morphism `f` and the homotopy-equivalence hypothesis on the
  underlying simplicial-set map;
  derived API is the induced homotopy-equivalence statement for the free-abelian-group simplicial
  objects after whiskering by `AddCommGrpCat.free`, and then the canonical bridge from homotopy
  equivalences of chain complexes to quasi-isomorphisms.

Source/core/bridge triage:
- `source-facing`: the Stacks hypothesis that the underlying simplicial-set map of `f` is a
  simplicial homotopy equivalence;
- `core/canonical`: `IsHomotopyEquivalence` and `QuasiIso`;
- `bridge/view`: the free-abelian-group square from the Stacks proof, where Lemma 14.28.4 turns
  the underlying simplicial-set homotopy equivalence into a simplicial homotopy equivalence after
  applying `AddCommGrpCat.free`, and Lemma 14.27.2 then yields the quasi-isomorphism input on the
  free simplicial abelian groups. The direct additive homotopy-equivalence hypothesis is only a
  stronger companion hypothesis, and the chain-level implication
  `homotopyEquivalences_le_quasiIso` is the canonical owner-side bridge rather than a separate
  local theorem.
-/

-- Proof sketch: let `ℤ[X]` and `ℤ[Y]` be the simplicial abelian groups obtained by applying
-- `AddCommGrpCat.free` degreewise to the underlying simplicial sets of `X` and `Y`. By Lemma
-- 14.28.4, the induced map `ℤ[X] ⟶ ℤ[Y]` is a simplicial homotopy equivalence, so Lemma 14.27.2
-- makes its normalized Moore complex map a homotopy equivalence and hence a quasi-isomorphism.
-- The Stacks proof then compares the resulting homology isomorphism on `ℤ[X]` and `ℤ[Y]` with the
-- canonical augmentation maps `ℤ[X] ⟶ X` and `ℤ[Y] ⟶ Y` to deduce that `N(f)` is a
-- quasi-isomorphism.
/-- Lemma 14.31.9: if the underlying simplicial-set map of a morphism of simplicial abelian groups
is a simplicial homotopy equivalence, then the induced map on normalized Moore complexes is a
quasi-isomorphism. -/
theorem normalizedMooreComplex_map_quasiIso_of_homotopyEquivalence
    (hf : IsHomotopyEquivalence (Functor.whiskerRight f (forget AddCommGrpCat))) :
    QuasiIso ((normalizedMooreComplex AddCommGrpCat).map f) := by
  rcases hf with ⟨e, he⟩
  let eFree :
      CategoryTheory.SimplicialObject.HomotopyEquiv
        ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
        ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free) :=
    { hom := Functor.whiskerRight e.hom AddCommGrpCat.free
      inv := Functor.whiskerRight e.inv AddCommGrpCat.free
      homotopyHomInvId := by
        simpa using Homotopic.whiskerRight e.homotopyHomInvId AddCommGrpCat.free
      homotopyInvHomId := by
        simpa using Homotopic.whiskerRight e.homotopyInvHomId AddCommGrpCat.free }
  have hfree :
      QuasiIso
        ((normalizedMooreComplex AddCommGrpCat).map
          (Functor.whiskerRight e.hom AddCommGrpCat.free)) := by
    rcases eFree.normalizedMooreComplex_map_isHomotopyEquivalence with ⟨h, hh⟩
    simpa [hh, eFree] using (show QuasiIso h.hom from inferInstance)
  -- Compare the quasi-isomorphism on the free simplicial abelian groups with the canonical
  -- counit maps `ℤ[X] ⟶ X` and `ℤ[Y] ⟶ Y`.
  clear he hfree eFree
  sorry

end CategoryTheory.SimplicialObject
