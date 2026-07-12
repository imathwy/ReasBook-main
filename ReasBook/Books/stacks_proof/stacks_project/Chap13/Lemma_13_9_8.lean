import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Lemma_13_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

/- Domain-style sampling for Lemma 13.9.8:
- primary domain: homological algebra of cochain complexes, mapping cocones, homotopies, and
  boundedness conditions on cochain complexes;
- inspected owner declarations:
  `CochainComplex.mappingCocone`,
  `HomotopyEquiv`,
  `CategoryTheory.IsSplitEpi`,
  `CochainComplex.splitMonoFactorizationProjectionHomotopyEquiv`,
  `CochainComplex.minus`,
  `CochainComplex.bounded`;
- best owner abstraction: the source-facing middle object is the canonical biproduct
  `K ⊞ mappingCocone (𝟙 L)`, while the reusable retract data should be organized around the
  canonical owner `HomotopyEquiv (K ⊞ mappingCocone (𝟙 L)) K`, and split-epimorphicity and
  boundedness should reuse the canonical owners `IsSplitEpi`, `CochainComplex.minus`, and
  `CochainComplex.bounded` instead of a conjunction-heavy existential package;
- layer: `source-facing` for the factorization statement, with `HomotopyEquiv`, `IsSplitEpi`,
  `CochainComplex.minus`, and `CochainComplex.bounded` providing the `core/canonical` owners;
- primitive data: the canonical middle complex `K ⊞ mappingCocone (𝟙 L)` and the canonical map
  `biprod.desc α (mappingCocone.fst (𝟙 L)) : K ⊞ mappingCocone (𝟙 L) ⟶ L`;
- derived API: the homotopy equivalence from the middle object to `K`, the termwise
  split-epimorphicity of `biprod.desc α (mappingCocone.fst (𝟙 L))`, the factorization identity
  `biprod.inl ≫ biprod.desc α (mappingCocone.fst (𝟙 L)) = α`, and boundedness inherited from the
  cocone summand and the biproduct.
-/

/-- The projection `K^• ⊞ C(1_{L^•[-1]}) ⟶ K^•` is a homotopy equivalence, with inverse the left
biproduct inclusion. -/
noncomputable def splitEpiFactorizationProjectionHomotopyEquiv (K L : CochainComplex C ℤ) :
    HomotopyEquiv (K ⊞ mappingCocone (𝟙 L)) K :=
  let p : K ⊞ mappingCocone (𝟙 L) ⟶ K := biprod.fst
  let i : K ⟶ K ⊞ mappingCocone (𝟙 L) := biprod.inl
  let q : K ⊞ mappingCocone (𝟙 L) ⟶ mappingCocone (𝟙 L) := biprod.snd
  let j : mappingCocone (𝟙 L) ⟶ K ⊞ mappingCocone (𝟙 L) := biprod.inr
  { hom := p
    inv := i
    homotopyHomInvId := by
      let h₀ : Homotopy (𝟙 (mappingCocone (𝟙 L))) 0 := by
        let hCone :
            Homotopy
              (𝟙 (mappingCone (𝟙 L)))
              (0 : mappingCone (𝟙 L) ⟶ mappingCone (𝟙 L)) :=
          mappingCone.homotopyToZeroOfId L
        simpa [mappingCocone] using hCone.shift (-1)
      let h₁ : Homotopy (q ≫ j) 0 := by
        simpa using (h₀.compRight j).compLeft q
      let h₂ : Homotopy (p ≫ i + q ≫ j) (p ≫ i) := by
        simpa using Homotopy.add (Homotopy.refl (p ≫ i)) h₁
      exact h₂.symm.trans (Homotopy.ofEq (by simp [p, i, q, j]))
    homotopyInvHomId := by
      simpa [p, i] using Homotopy.refl (𝟙 K : K ⟶ K) }

/-- Each component of the canonical factorization map
`K^• ⊞ C(1_{L^•[-1]}) ⟶ L^•` is a split epimorphism. -/
theorem splitEpiFactorizationDesc_f_isSplitEpi (α : K ⟶ L) (n : ℤ) :
    IsSplitEpi ((biprod.desc α (mappingCocone.fst (𝟙 L))).f n) := by
  refine IsSplitEpi.mk' ⟨(mappingCocone.inl (𝟙 L)).v n n (add_zero n) ≫
      (biprod.inr : mappingCocone (𝟙 L) ⟶ K ⊞ mappingCocone (𝟙 L)).f n, ?_⟩
  simp

@[simp] theorem splitEpiFactorizationInl_comp_desc (α : K ⟶ L) :
    (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
        biprod.desc α (mappingCocone.fst (𝟙 L)) = α := by
  simp

@[simp] theorem splitEpiFactorizationInl_comp_fst :
    (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
        (biprod.fst : K ⊞ mappingCocone (𝟙 L) ⟶ K) = 𝟙 K := by
  simp

-- Proof sketch: take `\tilde K^• = K^• ⊞ mappingCocone (𝟙 L)`, where `mappingCocone (𝟙 L)` is the
-- shifted cone `C(1_{L^•[-1]})`. Let `i` be the left biproduct inclusion, `s` the left biproduct
-- projection, and let `\tilde α` be the biproduct descendent of `α` and
-- `mappingCocone.fst (𝟙 L)`. Degreewise split epimorphy is witnessed by the right biproduct
-- inclusion composed with `mappingCocone.inl (𝟙 L)`, and the cocone summand is contractible
-- because `mappingCone (𝟙 L)` is contractible, so `s ≫ i` is homotopic to the identity.
/-- Lemma 13.9.8: every morphism `α : K^• ⟶ L^•` factors through the canonical complex
`K^• ⊞ C(1_{L^•[-1]})` by a termwise split epimorphism, and the projection to `K^•` has a section
whose composite with that section is homotopic to the identity. -/
@[stacks 0642]
theorem splitEpi_factorization_through_biproduct_mappingCocone_id
    (α : K ⟶ L) :
    ∃ _ : Homotopy
        ((biprod.fst : K ⊞ mappingCocone (𝟙 L) ⟶ K) ≫
          (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)))
        (𝟙 (K ⊞ mappingCocone (𝟙 L))),
      (∀ n : ℤ, IsSplitEpi ((biprod.desc α (mappingCocone.fst (𝟙 L))).f n)) ∧
        (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
            biprod.desc α (mappingCocone.fst (𝟙 L)) = α ∧
        (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
            (biprod.fst : K ⊞ mappingCocone (𝟙 L) ⟶ K) = 𝟙 K := by
  refine ⟨(splitEpiFactorizationProjectionHomotopyEquiv K L).homotopyHomInvId, ?_⟩
  refine ⟨splitEpiFactorizationDesc_f_isSplitEpi α, ?_, ?_⟩
  · exact splitEpiFactorizationInl_comp_desc α
  · exact splitEpiFactorizationInl_comp_fst

lemma mappingCocone_id_plus (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (mappingCocone (𝟙 L)) := by
  have hCone : CochainComplex.plus C (mappingCone (𝟙 L)) := mappingCone_id_plus hL
  simpa [mappingCocone] using (CochainComplex.plus C).le_shift (-1) (mappingCone (𝟙 L)) hCone

lemma mappingCocone_id_boundedAbove (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (mappingCocone (𝟙 L)) := by
  have hCone : CochainComplex.minus C (mappingCone (𝟙 L)) := mappingCone_id_boundedAbove hL
  simpa [mappingCocone] using (CochainComplex.minus C).le_shift (-1) (mappingCone (𝟙 L)) hCone

-- Proof sketch: if `K` and `L` are bounded below, then `mappingCone (𝟙 L)` is bounded below, so
-- its shift `mappingCocone (𝟙 L)` is still bounded below. Binary biproducts of bounded-below
-- cochain complexes remain bounded below.
/-- The canonical split-epimorphic factorization object is bounded below whenever both source and
target complexes are bounded below. -/
theorem splitEpiFactorization_plus
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (K ⊞ mappingCocone (𝟙 L)) := by
  simpa using
    (CochainComplex.plus C).prop_of_isColimit_binaryCofan
      (BinaryBiproduct.isColimit K (mappingCocone (𝟙 L))) hK (mappingCocone_id_plus hL)

-- Proof sketch: choose upper bounds for `K` and `L`. The mapping cone of the identity on `L` is
-- bounded above, hence so is the shifted cocone `mappingCocone (𝟙 L)`, and binary biproducts
-- preserve bounded-above cochain complexes.
/-- The canonical split-epimorphic factorization object is bounded above whenever both source and
target complexes are bounded above. -/
theorem splitEpiFactorization_boundedAbove
    (hK : CochainComplex.minus C K) (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (K ⊞ mappingCocone (𝟙 L)) := by
  simpa using
    (CochainComplex.minus C).prop_of_isLimit_binaryFan
      (BinaryBiproduct.isLimit K (mappingCocone (𝟙 L))) hK (mappingCocone_id_boundedAbove hL)

-- Proof sketch: combine the bounded-below and bounded-above statements for the canonical
-- split-epimorphic factorization object.
/-- The canonical split-epimorphic factorization object is bounded whenever both source and target
complexes are bounded. -/
theorem splitEpiFactorization_bounded
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (K ⊞ mappingCocone (𝟙 L)) := by
  rcases (CochainComplex.bounded_iff C K).1 hK with ⟨hKplus, hKminus⟩
  rcases (CochainComplex.bounded_iff C L).1 hL with ⟨hLplus, hLminus⟩
  exact (CochainComplex.bounded_iff C (K ⊞ mappingCocone (𝟙 L))).2
    ⟨splitEpiFactorization_plus hKplus hLplus,
      splitEpiFactorization_boundedAbove hKminus hLminus⟩

end CochainComplex
