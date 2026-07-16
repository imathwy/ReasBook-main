import Mathlib
import StacksProject_2024.stacks_project.Chap14.Lemma_14_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open HomologicalComplex
open scoped DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.23.9:
- primary domain: the Dold-Kan splitting of the alternating face map complex into the normalized
  Moore complex and the degenerate summand;
- sampled same-kind owner declarations:
  `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
  `decomposition`,
  `QInftyToDegenerateComplex`,
  `cokernelBiprodInlIso`;
- best owner abstraction: the canonical owner for the quotient of `K(U)` by `N(U)` is the
  degenerate complex `D[U]`, with the source-facing cokernel identified via the decomposition
  `K(U) ≅ N(U) ⊞ D(U)`;
- primitive data: the Dold-Kan owners `inclusionOfMooreComplexMap U`, `decomposition U`,
  `QInftyToDegenerateComplex U`, and `degenerateComplexι U`;
- derived API: the homotopy-triviality and acyclicity of `D[U]`, and the source-facing acyclicity
  of the cokernel of `N(U) ⟶ K(U)`.

Source/core/bridge triage:
- `source-facing`: the textbook quasi-isomorphism and cokernel-acyclicity statements for
  `inclusionOfMooreComplexMap U`;
- `core/canonical`: the Dold-Kan homotopy equivalence and the source-facing owner `D[U]`;
- `bridge/view`: the decomposition `K(U) ≅ N(U) ⊞ D(U)` together with `cokernelBiprodInlIso`.
-/

private theorem inclusionOfMooreComplexMap_comp_decomposition_hom (V : SimplicialObject A) :
    inclusionOfMooreComplexMap V ≫ (decomposition V).hom = biprod.inl := by
  apply (cancel_mono (decomposition V).inv).1
  have h₁ :
      (inclusionOfMooreComplexMap V ≫ (decomposition V).hom) ≫ (decomposition V).inv =
        inclusionOfMooreComplexMap V := by
    simpa [Category.assoc] using
      show inclusionOfMooreComplexMap V ≫
          ((decomposition V).hom ≫ (decomposition V).inv) =
        inclusionOfMooreComplexMap V ≫ 𝟙 _ from
        congrArg (fun t ↦ inclusionOfMooreComplexMap V ≫ t)
          (decomposition V).hom_inv_id
  have h₂ : biprod.inl ≫ (decomposition V).inv = inclusionOfMooreComplexMap V := by
    simp [decomposition]
  exact h₁.trans h₂.symm

private theorem qInftyToDegenerateComplex_comp_degenerateComplexι
    (V : SimplicialObject A) :
    QInftyToDegenerateComplex V ≫ degenerateComplexι V = QInfty := by
  let K' : ChainComplex A ℕ := (alternatingFaceMapComplex A).obj V
  have hpq :
      ((PInftyToNormalizedMooreComplex V ≫ inclusionOfMooreComplexMap V : K' ⟶ K')) +
        ((QInftyToDegenerateComplex V ≫ degenerateComplexι V : K' ⟶ K')) =
      𝟙 K' := by
    simpa [K', decomposition, Category.assoc, biprod.lift_desc] using
      (decomposition V).hom_inv_id
  change
      ((PInftyToNormalizedMooreComplex V ≫ inclusionOfMooreComplexMap V : K[V] ⟶ K[V]) +
        (QInftyToDegenerateComplex V ≫ degenerateComplexι V : K[V] ⟶ K[V]) =
      𝟙 K[V]) at hpq
  have hcomp :
      PInftyToNormalizedMooreComplex V ≫ inclusionOfMooreComplexMap V =
        (PInfty : K[V] ⟶ K[V]) :=
    PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap V
  have hpq' :
      (PInfty : K[V] ⟶ K[V]) + (QInftyToDegenerateComplex V ≫ degenerateComplexι V) =
      𝟙 K[V] := by
    rw [← hcomp]
    exact hpq
  have hpQ : (PInfty : K[V] ⟶ K[V]) + QInfty = 𝟙 K[V] :=
    PInfty_add_QInfty
  exact add_left_cancel (hpq'.trans hpQ.symm)

private theorem qInfty_eq_qInftyToDegenerateComplex_comp_degenerateComplexι
    (V : SimplicialObject A) :
    (QInfty : K[V] ⟶ K[V]) =
      QInftyToDegenerateComplex V ≫ degenerateComplexι V :=
  (qInftyToDegenerateComplex_comp_degenerateComplexι V).symm

private theorem degenerateComplexι_comp_qInftyToDegenerateComplex (V : SimplicialObject A) :
    degenerateComplexι V ≫ QInftyToDegenerateComplex V = 𝟙 D[V] := by
  simpa [decomposition, Category.assoc] using
    congrArg (fun k ↦ biprod.inr ≫ k ≫ biprod.snd) (Iso.inv_hom_id (decomposition V))

private theorem degenerateComplex_id_homotopic_zero (V : SimplicialObject A) :
    Nonempty (Homotopy (𝟙 D[V]) (0 : D[V] ⟶ D[V])) := by
  let hQ : Homotopy (QInfty : K[V] ⟶ K[V]) 0 :=
    Homotopy.equivSubZero.toFun (homotopyPInftyToId V).symm
  -- Transport the null-homotopy of `Q∞` across the retract data for the degenerate summand.
  refine ⟨?_⟩
  simpa [Category.assoc, qInfty_eq_qInftyToDegenerateComplex_comp_degenerateComplexι,
    degenerateComplexι_comp_qInftyToDegenerateComplex] using
    (hQ.compRight (QInftyToDegenerateComplex V)).compLeft (degenerateComplexι V)

/-- The degenerate summand `D(U)` in the Dold-Kan decomposition is acyclic. -/
theorem degenerateComplex_acyclic (V : SimplicialObject A) :
    D[V].Acyclic := by
  classical
  let h : Homotopy (𝟙 D[V]) (0 : D[V] ⟶ D[V]) :=
    Classical.choice (degenerateComplex_id_homotopic_zero V)
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  -- The identity map vanishes on homology because it is homotopic to zero.
  simpa using h.homologyMap_eq n

end AlgebraicTopology.DoldKan

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

-- Proof sketch: this is the forward map of the canonical Dold-Kan homotopy equivalence between
-- the normalized Moore complex and the alternating face map complex.
/-- Lemma 14.23.9: for a simplicial object `V` in an abelian category, the canonical morphism of
chain complexes `N(V) ⟶ s(V)` given by `inclusionOfMooreComplexMap V` is a quasi-isomorphism. -/
theorem inclusionOfMooreComplexMap_quasiIso (V : SimplicialObject A) :
    QuasiIso (inclusionOfMooreComplexMap V) := by
  let e :
      HomotopyEquiv
        ((normalizedMooreComplex A).obj V)
        ((alternatingFaceMapComplex A).obj V) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  simpa [e] using (show QuasiIso e.hom from inferInstance)

-- Proof sketch: `K(V) ≅ N(V) ⊞ D(V)` identifies `inclusionOfMooreComplexMap V` with
-- `biprod.inl`, so its cokernel is canonically `D(V)`. The degenerate complex is acyclic by the
-- owner theorem `AlgebraicTopology.DoldKan.degenerateComplex_acyclic`.
/-- The cokernel of the canonical inclusion `N(V) ⟶ s(V)` is acyclic. -/
theorem cokernel_inclusionOfMooreComplexMap_acyclic (V : SimplicialObject A) :
    (cokernel (inclusionOfMooreComplexMap V)).Acyclic := by
  let α : N[V] ⟶ K[V] := inclusionOfMooreComplexMap V
  let e₀ : cokernel (inclusionOfMooreComplexMap V) ≅
      cokernel (biprod.inl : N[V] ⟶ N[V] ⊞ D[V]) :=
    cokernel.mapIso α
      (biprod.inl : N[V] ⟶ N[V] ⊞ D[V])
      (Iso.refl _)
      (decomposition V)
      (by simpa [α] using inclusionOfMooreComplexMap_comp_decomposition_hom V)
  let e : cokernel (inclusionOfMooreComplexMap V) ≅ D[V] :=
    e₀ ≪≫ cokernelBiprodInlIso
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso
    ((degenerateComplex_acyclic V n).isZero_homology)
    (show (cokernel (inclusionOfMooreComplexMap V)).homology n ≅ D[V].homology n from
      (homologyFunctor A (ComplexShape.down ℕ) n).mapIso e)

end CategoryTheory
