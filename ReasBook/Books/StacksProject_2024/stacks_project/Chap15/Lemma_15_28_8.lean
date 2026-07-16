import Mathlib.LinearAlgebra.Pi
import StacksProject_2024.stacks_project.Chap15.Definition_15_28_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_28_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_28_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory HomologicalComplex Module
open scoped KoszulComplex

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
- primary domain: family-level Koszul complexes and their comparison with the canonical
  homotopy cofiber of scalar multiplication;
- sampled owner declarations: `koszulComplex`, `KoszulComplex.map`,
  `koszulComplex_coprod_scalar_iso_homotopyCofiber`, `Fin.finSuccEquivLast`,
  `LinearEquiv.piOptionEquivProd`, `LinearEquiv.prodComm`;
- best owner abstraction: the core/canonical owner remains the linear-form Koszul complex
  `koszulComplex` together with the canonical cone object `homotopyCofiber`;
- primitive data: the tuple `f : Fin (r + 1) → R`, split into its truncated family
  `Fin.init f` and last coefficient `f (Fin.last r)`;
- derived API: the private transport from the canonical `Option`-indexed Pi equivalence to the
  coproduct linear form, and the public family-level bridge
  `koszulComplex_iso_homotopyCofiber_truncate_last`;
- layer triage: this file is entirely `bridge/view`; the local linearization of
  the last-coordinate split stays private because it only repackages the canonical owners above
  and carries no extra source-level mathematics.
-/ 

private def finSnocLinearEquiv (r : ℕ) :
    ((Fin r → R) × R) ≃ₗ[R] (Fin (r + 1) → R) :=
  { toFun := fun x ↦ Fin.snoc x.1 x.2
    invFun := fun x ↦ (Fin.init x, x (Fin.last r))
    map_add' := by
      intro x y
      ext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · simp
    map_smul' := by
      intro a x
      ext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · simp
    left_inv := by
      intro x
      ext i <;> simp
    right_inv := by
      intro x
      ext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · simp [Fin.init_def] }

@[simp] private theorem finSnocLinearEquiv_apply {r : ℕ} (x : (Fin r → R) × R) :
    finSnocLinearEquiv r x = Fin.snoc x.1 x.2 :=
  rfl

@[simp] private theorem finSnocLinearEquiv_symm_apply {r : ℕ} (x : Fin (r + 1) → R) :
    (finSnocLinearEquiv r).symm x = (Fin.init x, x (Fin.last r)) :=
  rfl

private theorem koszulLinearForm_snoc_comp_symm {r : ℕ}
    (fs : Fin r → R) (a : R) :
    (koszulCoprodScalarLinearMap (koszulLinearForm fs) a).comp
        (finSnocLinearEquiv r).symm.toLinearMap =
      koszulLinearForm (Fin.snoc fs a) := by
  apply LinearMap.ext
  intro x
  simp [LinearMap.comp_apply, finSnocLinearEquiv_symm_apply,
    koszulLinearForm, piEquiv_apply_apply, Fin.sum_univ_castSucc, Fin.init_def]

private theorem koszulLinearForm_snoc_comp {r : ℕ}
    (fs : Fin r → R) (a : R) :
    (koszulLinearForm (Fin.snoc fs a)).comp (finSnocLinearEquiv r).toLinearMap =
      koszulCoprodScalarLinearMap (koszulLinearForm fs) a := by
  apply LinearMap.ext
  intro x
  simp [LinearMap.comp_apply, finSnocLinearEquiv_apply, koszulCoprodScalarLinearMap,
    koszulLinearForm, piEquiv_apply_apply, Fin.sum_univ_castSucc]

/-- Helper for Lemma 15.28.8: on exterior-power generators, applying
`finSnocLinearEquiv r` after its inverse is the identity. -/
private theorem exteriorPower_map_finSnoc_right_inverse {r n : ℕ}
    (m : Fin n → Fin (r + 1) → R) :
    ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).toLinearMap) n
        (ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).symm.toLinearMap) n
          (ModuleCat.exteriorPower.mk m)) =
      ModuleCat.exteriorPower.mk m := by
  -- Rewrite both maps on generators and collapse the pointwise inverse pair.
  rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
  congr 1
  funext i
  exact (finSnocLinearEquiv r).right_inv (m i)

/-- Helper for Lemma 15.28.8: on exterior-power generators, applying the inverse of
`finSnocLinearEquiv r` after `finSnocLinearEquiv r` is the identity. -/
private theorem exteriorPower_map_finSnoc_left_inverse {r n : ℕ}
    (m : Fin n → ((Fin r → R) × R)) :
    ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).symm.toLinearMap) n
        (ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).toLinearMap) n
          (ModuleCat.exteriorPower.mk m)) =
      ModuleCat.exteriorPower.mk m := by
  -- Rewrite both maps on generators and collapse the pointwise inverse pair.
  rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
  congr 1
  funext i
  exact (finSnocLinearEquiv r).left_inv (m i)

private def koszulComplex_snoc_iso_coprodScalar {r : ℕ}
    (fs : Fin r → R) (a : R) :
    K^•(Fin.snoc fs a) ≅
      koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a) where
  hom := KoszulComplex.map (finSnocLinearEquiv r).symm.toLinearMap
    (koszulLinearForm_snoc_comp_symm fs a)
  inv := KoszulComplex.map (finSnocLinearEquiv r).toLinearMap
    (koszulLinearForm_snoc_comp fs a)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- Check the degreewise composite on exterior-power generators.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).toLinearMap) n
          (ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).symm.toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    simpa using exteriorPower_map_finSnoc_right_inverse (R := R) (r := r) (n := n) m
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- Check the reverse degreewise composite on exterior-power generators.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).symm.toLinearMap) n
          (ModuleCat.exteriorPower.map (ModuleCat.ofHom (finSnocLinearEquiv r).toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    simpa using exteriorPower_map_finSnoc_left_inverse (R := R) (r := r) (n := n) m

-- Proof sketch: apply `koszulComplex_coprod_scalar_iso_homotopyCofiber` to the linear
-- form attached to the truncated family `Fin.init f` and the last coefficient
-- `f (Fin.last r)`, then transport the linear-map Koszul complex of
-- `koszulCoprodScalarLinearMap` back to the family-level complex through the canonical
-- `Fin.snoc` linear equivalence.

/-- Lemma 15.28.8: for a finite family `f : Fin (r + 1) → R`, the Koszul complex on `f` is
canonically isomorphic to the cone of multiplication by the last entry on the Koszul complex of
the truncated family, written in mathlib as the homotopy cofiber of the canonical scalar
endomorphism `f (Fin.last r) • 𝟙`. -/
def koszulComplex_iso_homotopyCofiber_truncate_last
    {r : ℕ} (f : Fin (r + 1) → R) :
    K^•(f) ≅
      homotopyCofiber
        ((f (Fin.last r)) • 𝟙 (K^•(Fin.init f))) := by
  simpa using
    koszulComplex_snoc_iso_coprodScalar (Fin.init f) (f (Fin.last r)) ≪≫
      koszulComplex_coprod_scalar_iso_homotopyCofiber
        (koszulLinearForm (Fin.init f)) (f (Fin.last r))
