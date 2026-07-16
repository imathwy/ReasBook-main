import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w x y z

noncomputable section

section

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat R)}

section Helpers

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
variable {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
variable {M₃ : Type x} [AddCommGroup M₃] [Module R M₃]
variable {M₄ : Type y} [AddCommGroup M₄] [Module R M₄]
variable {F : Type z} [AddCommGroup F] [Module R F]

/-- Helper for Lemma 15.3.2: the trivial finite free summand `Fin 0 → R` does not change a
module. -/
theorem prod_fin_zero_linearEquiv_nonempty :
    Nonempty (M ≃ₗ[R] (M × (Fin 0 → R))) := by
  -- Use the canonical inclusion and prove it is bijective because the `Fin 0` factor is
  -- subsingleton.
  refine ⟨LinearEquiv.ofBijective (LinearMap.inl R M (Fin 0 → R)) ?_⟩
  constructor
  · intro x y hxy
    exact congrArg (fun z : M × (Fin 0 → R) => z.1) hxy
  · intro x
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i

/-- Helper for Lemma 15.3.2: two finite free coordinate blocks combine into one block indexed by
`Fin (m + n)`. -/
theorem fin_append_linearEquiv_nonempty (m n : ℕ) :
    Nonempty (((Fin m → R) × (Fin n → R)) ≃ₗ[R] (Fin (m + n) → R)) := by
  -- Rewrite the product of arrow modules as arrows on the sum index, then identify that sum index
  -- with `Fin (m + n)`.
  let e₁ : ((Fin (m + n)) → R) ≃ₗ[R] ((Fin m ⊕ Fin n) → R) :=
    LinearEquiv.funCongrLeft (R := R) (M := R) (finSumFinEquiv (m := m) (n := n))
  let e₂ : ((Fin m ⊕ Fin n) → R) ≃ₗ[R] ((Fin m → R) × (Fin n → R)) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) R R
  exact ⟨(e₁.trans e₂).symm⟩

/-- Helper for Lemma 15.3.2: regroup four product factors into paired blocks. -/
theorem prod_four_linearEquiv_nonempty :
    Nonempty (((M₁ × M₂) × (M₃ × M₄)) ≃ₗ[R] ((M₁ × M₃) × (M₂ × M₄))) := by
  -- Reassociate to expose the middle pair, commute those factors, and reassociate back.
  let e₁ :
      ((M₁ × M₂) × (M₃ × M₄)) ≃ₗ[R] (M₁ × (M₂ × (M₃ × M₄))) :=
    LinearEquiv.prodAssoc R M₁ M₂ (M₃ × M₄)
  let e₂ :
      (M₁ × (M₂ × (M₃ × M₄))) ≃ₗ[R] (M₁ × ((M₂ × M₃) × M₄)) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R M₁)
      (LinearEquiv.prodAssoc R M₂ M₃ M₄).symm
  let e₃ :
      (M₁ × ((M₂ × M₃) × M₄)) ≃ₗ[R] (M₁ × ((M₃ × M₂) × M₄)) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R M₁)
      (LinearEquiv.prodCongr (LinearEquiv.prodComm R M₂ M₃) (LinearEquiv.refl R M₄))
  let e₄ :
      (M₁ × ((M₃ × M₂) × M₄)) ≃ₗ[R] (M₁ × (M₃ × (M₂ × M₄))) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R M₁)
      (LinearEquiv.prodAssoc R M₃ M₂ M₄)
  let e₅ :
      (M₁ × (M₃ × (M₂ × M₄))) ≃ₗ[R] ((M₁ × M₃) × (M₂ × M₄)) :=
    (LinearEquiv.prodAssoc R M₁ M₃ (M₂ × M₄)).symm
  exact ⟨e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))⟩

/-- Helper for Lemma 15.3.2: a finite-rank stabilization witness already gives stable freeness. -/
theorem stablyFree_of_fin_stabilization
    (h :
      ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (Fin n → R))) :
    Module.StablyFree R M := by
  rcases h with ⟨m, n, ⟨e⟩⟩
  rcases prod_fin_zero_linearEquiv_nonempty (R := R) (M := ULift.{v} (Fin n → R)) with ⟨e₀⟩
  refine ⟨?_⟩
  -- Package the free target inside `ULift` so its universe matches the stable-freeness owner.
  refine ⟨ULift.{v} (Fin n → R), inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨m, 0, ?_⟩
  refine ⟨e.trans (ULift.moduleEquiv.symm.trans e₀)⟩

/-- Helper for Lemma 15.3.2: a stably free module is projective because it is a retract of a
projective stabilization. -/
theorem stablyFree_projective [Module.StablyFree R M] :
    Module.Projective R M := by
  rcases Module.StablyFree.exists_free (R := R) (M := M) with
    ⟨F, _instAddCommGroupF, _instModuleF, _instFreeF, hstab⟩
  rcases hstab with ⟨m, n, ⟨e⟩⟩
  -- Transport projectivity from the free stabilized target back to `M × R^m`.
  letI : Module.Projective R (F × (Fin n → R)) := by infer_instance
  letI : Module.Projective R (M × (Fin m → R)) := Module.Projective.of_equiv' e.symm
  -- Then `M` is the split direct summand cut out by the first projection.
  exact Module.Projective.of_split
    (LinearMap.inl R M (Fin m → R))
    (LinearMap.fst R M (Fin m → R))
    (by
      ext x
      rfl)

/-- Helper for Lemma 15.3.2: a short exact sequence with projective right term identifies the
middle module with the product of the outer two modules. -/
theorem shortExact_middle_linearEquiv_prod_nonempty (hS : S.ShortExact)
    [Module.Projective R S.X₃] :
    Nonempty (S.X₂ ≃ₗ[R] (S.X₁ × S.X₃)) := by
  -- Convert the canonical categorical splitting to the module-level product description.
  exact ⟨((hS.splittingOfProjective).isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv⟩

/-- Helper for Lemma 15.3.2: a finite free module is linearly equivalent to a finite coordinate
module `Fin n → R`. -/
theorem finite_free_linearEquiv_fin [Module.Free R F] [Module.Finite R F] :
    ∃ n : ℕ, Nonempty (F ≃ₗ[R] (Fin n → R)) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI : Subsingleton R := hR
    letI : Subsingleton F := Module.subsingleton R F
    refine ⟨0, ⟨LinearEquiv.ofSubsingleton F (Fin 0 → R)⟩⟩
  · letI : Nontrivial R := hR
    -- Choose a basis and replace its finite index type by `Fin n`.
    let b : Module.Basis (Module.Free.ChooseBasisIndex R F) R F := Module.Free.chooseBasis R F
    letI : Finite (Module.Free.ChooseBasisIndex R F) := Module.Finite.finite_basis b
    let e :
        Module.Free.ChooseBasisIndex R F ≃ Fin (Fintype.card (Module.Free.ChooseBasisIndex R F)) :=
      Fintype.equivFin (Module.Free.ChooseBasisIndex R F)
    refine ⟨Fintype.card (Module.Free.ChooseBasisIndex R F), ?_⟩
    refine ⟨b.equivFun.trans (LinearEquiv.funCongrLeft (R := R) (M := R) e).symm⟩

/-- Helper for Lemma 15.3.2: a finite stably free module admits a stabilization by a finite free
coordinate block. -/
theorem finite_stablyFree_exists_fin_stabilization
    [Module.Finite R M] [Module.StablyFree R M] :
    ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (Fin n → R)) := by
  rcases Module.StablyFree.exists_free (R := R) (M := M) with
    ⟨F, _instAddCommGroupF, _instModuleF, _instFreeF, hstab⟩
  rcases hstab with ⟨m, k, ⟨e⟩⟩
  -- First show the chosen free witness is finite by projecting from a finite stabilized module.
  letI : Module.Finite R (M × (Fin m → R)) := by infer_instance
  letI : Module.Finite R (F × (Fin k → R)) := Module.Finite.equiv e
  letI : Module.Finite R F :=
    Module.Finite.of_surjective
      (LinearMap.fst R F (Fin k → R))
      (by
        intro x
        exact ⟨(x, 0), rfl⟩)
  rcases finite_free_linearEquiv_fin (R := R) (F := F) with ⟨n, ⟨eF⟩⟩
  rcases fin_append_linearEquiv_nonempty (R := R) n k with ⟨eAppend⟩
  -- Replace the free witness by a finite coordinate module and collapse the two free blocks.
  refine ⟨m, n + k, ?_⟩
  refine ⟨e.trans ((LinearEquiv.prodCongr eF (LinearEquiv.refl R (Fin k → R))).trans eAppend)⟩

/-- Helper for Lemma 15.3.2: finite-rank stabilization witnesses transport across linear
equivalences. -/
theorem fin_stabilization_of_equiv (e : M ≃ₗ[R] N)
    (h :
      ∃ m n : ℕ, Nonempty ((N × (Fin m → R)) ≃ₗ[R] (Fin n → R))) :
    ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (Fin n → R)) := by
  rcases h with ⟨m, n, ⟨w⟩⟩
  -- Reuse the same stabilization rank and move the witness through `e`.
  refine ⟨m, n, ⟨(LinearEquiv.prodCongr e (LinearEquiv.refl R (Fin m → R))).trans w⟩⟩

/-- Helper for Lemma 15.3.2: stabilization witnesses for two modules combine to one for their
product. -/
theorem fin_stabilization_prod
    (hM :
      ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (Fin n → R)))
    (hN :
      ∃ m n : ℕ, Nonempty ((N × (Fin m → R)) ≃ₗ[R] (Fin n → R))) :
    ∃ m n : ℕ, Nonempty (((M × N) × (Fin m → R)) ≃ₗ[R] (Fin n → R)) := by
  rcases hM with ⟨m₁, n₁, ⟨e₁⟩⟩
  rcases hN with ⟨m₂, n₂, ⟨e₂⟩⟩
  rcases fin_append_linearEquiv_nonempty (R := R) m₁ m₂ with ⟨eLeftBlock⟩
  rcases prod_four_linearEquiv_nonempty (R := R)
    (M₁ := M) (M₂ := N) (M₃ := (Fin m₁ → R)) (M₄ := (Fin m₂ → R)) with ⟨eMid⟩
  rcases fin_append_linearEquiv_nonempty (R := R) n₁ n₂ with ⟨eRight⟩
  -- Expand the combined free block, pair each module with its own stabilization, then collapse the
  -- two finite free targets back to one coordinate block.
  let eLeft :
      ((M × N) × (Fin (m₁ + m₂) → R)) ≃ₗ[R]
        ((M × N) × ((Fin m₁ → R) × (Fin m₂ → R))) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R (M × N))
      eLeftBlock.symm
  refine ⟨m₁ + m₂, n₁ + n₂, ?_⟩
  refine ⟨eLeft.trans (eMid.trans ((LinearEquiv.prodCongr e₁ e₂).trans eRight))⟩

/-- Helper for Lemma 15.3.2: if `M` and `M × N` both admit finite-rank stabilization witnesses,
then `N` does as well. -/
theorem fin_stabilization_right_of_prod
    (hM :
      ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (Fin n → R)))
    (hMN :
      ∃ m n : ℕ, Nonempty (((M × N) × (Fin m → R)) ≃ₗ[R] (Fin n → R))) :
    ∃ m n : ℕ, Nonempty ((N × (Fin m → R)) ≃ₗ[R] (Fin n → R)) := by
  rcases hM with ⟨m₁, n₁, ⟨e₁⟩⟩
  rcases hMN with ⟨m₂, n₂, ⟨e₂⟩⟩
  rcases fin_append_linearEquiv_nonempty (R := R) m₂ n₁ with ⟨eLeftBlock⟩
  rcases prod_four_linearEquiv_nonempty (R := R)
    (M₁ := N) (M₂ := (Fin m₂ → R)) (M₃ := M) (M₄ := (Fin m₁ → R)) with ⟨eSwap⟩
  rcases fin_append_linearEquiv_nonempty (R := R) n₂ m₁ with ⟨eRight⟩
  -- Expand the left stabilization by `R^{n₁}`, rewrite that block using the witness for `M`, and
  -- then reorganize factors so the witness for `M × N` can be applied.
  let eLeft :
      (N × (Fin (m₂ + n₁) → R)) ≃ₗ[R]
        (N × ((Fin m₂ → R) × (Fin n₁ → R))) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R N)
      eLeftBlock.symm
  let eAssoc :
      (N × ((Fin m₂ → R) × (Fin n₁ → R))) ≃ₗ[R]
        ((N × (Fin m₂ → R)) × (Fin n₁ → R)) :=
    (LinearEquiv.prodAssoc R N (Fin m₂ → R) (Fin n₁ → R)).symm
  let eLift :
      ((N × (Fin m₂ → R)) × (Fin n₁ → R)) ≃ₗ[R]
        ((N × (Fin m₂ → R)) × (M × (Fin m₁ → R))) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R (N × (Fin m₂ → R)))
      e₁.symm
  let eComm :
      ((N × M) × ((Fin m₂ → R) × (Fin m₁ → R))) ≃ₗ[R]
        ((M × N) × ((Fin m₂ → R) × (Fin m₁ → R))) :=
    LinearEquiv.prodCongr
      (LinearEquiv.prodComm R N M)
      (LinearEquiv.refl R ((Fin m₂ → R) × (Fin m₁ → R)))
  let ePack :
      ((M × N) × ((Fin m₂ → R) × (Fin m₁ → R))) ≃ₗ[R]
        (((M × N) × (Fin m₂ → R)) × (Fin m₁ → R)) :=
    (LinearEquiv.prodAssoc R (M × N) (Fin m₂ → R) (Fin m₁ → R)).symm
  let eApply :
      (((M × N) × (Fin m₂ → R)) × (Fin m₁ → R)) ≃ₗ[R]
        ((Fin n₂ → R) × (Fin m₁ → R)) :=
    LinearEquiv.prodCongr e₂ (LinearEquiv.refl R (Fin m₁ → R))
  refine ⟨m₂ + n₁, n₂ + m₁, ?_⟩
  refine ⟨eLeft.trans (eAssoc.trans (eLift.trans (eSwap.trans (eComm.trans (ePack.trans
    (eApply.trans eRight))))))⟩

end Helpers

/- Domain-style sampling:
* primary domain: short exact sequences of `R`-modules, projective splittings, and stable
  freeness;
* sampled owner declarations:
  `ShortComplex.ShortExact.splittingOfProjective`,
  `ModuleCat.free_shortExact`,
  `Module.Projective.of_free`,
  `Module.StablyFree`;
* best owner abstraction: the ambient owner is the short exact complex `S : ShortComplex
  (ModuleCat R)` with `hS : S.ShortExact`;
* primitive vs. derived:
  the primitive end-term data are the canonical owners `Module.Finite` and `Module.StablyFree`,
  while "finite stably free" is only their conjunction and should remain derived API rather than a
  separate wrapper; projectivity of a stably free end term is supporting bridge data rather than
  primitive public input for the closure lemmas that only use stable freeness.

Source/core/bridge triage:
* `source-facing`: the three closure statements from Stacks Lemma 15.3.2;
* `core/canonical`: `hS.splittingOfProjective` and the owner properties `Module.Finite` /
  `Module.StablyFree`;
* `bridge/view`: the identification of the middle term with a split product coming from the
  canonical splitting. -/

-- Proof sketch: use the canonical splitting `hS.splittingOfProjective`, so `S.X₂` identifies with
-- `S.X₁ × S.X₃`. Stabilize the two end terms by finite free summands, use that products preserve
-- finite/free modules, and apply `ModuleCat.free_shortExact` to obtain a finite free stabilization
-- of `S.X₂`.
/-- Lemma 15.3.2 (1): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P'` and `P''` are finite stably free, then `P` is finite stably free. -/
@[stacks 0BC4]
theorem finiteStablyFree_X₂_of_shortExact (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₂ ∧ Module.StablyFree R S.X₂ := by
  -- Split the short exact sequence using projectivity of the right term coming from stable
  -- freeness.
  letI : Module.Projective R S.X₃ := stablyFree_projective (R := R) (M := S.X₃)
  rcases shortExact_middle_linearEquiv_prod_nonempty (R := R) (S := S) hS with ⟨e⟩
  constructor
  · -- Transport finite generation from the split product back to the middle term.
    exact Module.Finite.equiv e.symm
  · -- Convert both end terms to explicit finite-rank stabilizations and combine them on the split
    -- product.
    have hX₁ :
        ∃ m n : ℕ, Nonempty ((S.X₁ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      finite_stablyFree_exists_fin_stabilization (R := R) (M := S.X₁)
    have hX₃ :
        ∃ m n : ℕ, Nonempty ((S.X₃ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      finite_stablyFree_exists_fin_stabilization (R := R) (M := S.X₃)
    have hProd :
        ∃ m n : ℕ, Nonempty ((((S.X₁ × S.X₃) × (Fin m → R))) ≃ₗ[R] (Fin n → R)) :=
      fin_stabilization_prod (R := R) (M := S.X₁) (N := S.X₃) hX₁ hX₃
    have hX₂ :
        ∃ m n : ℕ, Nonempty ((S.X₂ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      fin_stabilization_of_equiv (R := R) (M := S.X₂) (N := S.X₁ × S.X₃) e hProd
    exact stablyFree_of_fin_stabilization (R := R) (M := S.X₂) hX₂

-- Proof sketch: via `hS.splittingOfProjective`, the canonical decomposition
-- `S.X₂ ≃ₗ[R] S.X₁ × S.X₃` exhibits `S.X₃` as a direct summand of `S.X₂`; transport finite stable
-- freeness across that split-product description.
/-- Lemma 15.3.2 (2): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P'` and `P` are finite stably free, then `P''` is finite stably free. -/
@[stacks 0BC4]
theorem finiteStablyFree_X₃_of_shortExact (hS : S.ShortExact)
    [Module.Projective R S.X₃]
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂] :
    Module.Finite R S.X₃ ∧ Module.StablyFree R S.X₃ := by
  rcases shortExact_middle_linearEquiv_prod_nonempty (R := R) (S := S) hS with ⟨e⟩
  constructor
  · -- The right map in a short exact sequence is surjective.
    exact Module.Finite.of_surjective S.g.hom (ShortComplex.ShortExact.moduleCat_surjective_g hS)
  · -- Move the middle-term stabilization to the split product and cancel the known left factor.
    have hX₁ :
        ∃ m n : ℕ, Nonempty ((S.X₁ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      finite_stablyFree_exists_fin_stabilization (R := R) (M := S.X₁)
    have hX₂ :
        ∃ m n : ℕ, Nonempty ((S.X₂ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      finite_stablyFree_exists_fin_stabilization (R := R) (M := S.X₂)
    have hProd :
        ∃ m n : ℕ, Nonempty ((((S.X₁ × S.X₃) × (Fin m → R))) ≃ₗ[R] (Fin n → R)) :=
      fin_stabilization_of_equiv (R := R) (M := S.X₁ × S.X₃) (N := S.X₂) e.symm hX₂
    have hX₃ :
        ∃ m n : ℕ, Nonempty ((S.X₃ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      fin_stabilization_right_of_prod (R := R) (M := S.X₁) (N := S.X₃) hX₁ hProd
    exact stablyFree_of_fin_stabilization (R := R) (M := S.X₃) hX₃

-- Proof sketch: use the same canonical splitting of `hS`; under
-- `S.X₂ ≃ₗ[R] S.X₁ × S.X₃`, the module `S.X₁` is the complementary direct summand to `S.X₃`, so
-- finite stable freeness descends from the split-product description.
/-- Lemma 15.3.2 (3): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P` and `P''` are finite stably free, then `P'` is finite stably free. -/
@[stacks 0BC4]
theorem finiteStablyFree_X₁_of_shortExact (hS : S.ShortExact)
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₁ ∧ Module.StablyFree R S.X₁ := by
  letI : Module.Projective R S.X₃ := stablyFree_projective (R := R) (M := S.X₃)
  rcases shortExact_middle_linearEquiv_prod_nonempty (R := R) (S := S) hS with ⟨e⟩
  constructor
  · -- Project to the first factor of the split product to obtain a surjection from `S.X₂` onto
    -- `S.X₁`.
    let π : S.X₂ →ₗ[R] S.X₁ := (LinearMap.fst R S.X₁ S.X₃).comp e.toLinearMap
    exact Module.Finite.of_surjective π
      (by
        intro x
        refine ⟨e.symm (x, 0), ?_⟩
        simp [π])
  · -- Commute the product so that the same right-cancellation argument recovers the left factor.
    have hX₃ :
        ∃ m n : ℕ, Nonempty ((S.X₃ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      finite_stablyFree_exists_fin_stabilization (R := R) (M := S.X₃)
    have hX₂ :
        ∃ m n : ℕ, Nonempty ((S.X₂ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      finite_stablyFree_exists_fin_stabilization (R := R) (M := S.X₂)
    have hProd :
        ∃ m n : ℕ, Nonempty ((((S.X₃ × S.X₁) × (Fin m → R))) ≃ₗ[R] (Fin n → R)) := by
      have hSplit :
          ∃ m n : ℕ, Nonempty ((((S.X₁ × S.X₃) × (Fin m → R))) ≃ₗ[R] (Fin n → R)) :=
        fin_stabilization_of_equiv (R := R) (M := S.X₁ × S.X₃) (N := S.X₂) e.symm hX₂
      refine fin_stabilization_of_equiv
        (R := R)
        (M := S.X₃ × S.X₁)
        (N := S.X₁ × S.X₃)
        (LinearEquiv.prodComm R S.X₃ S.X₁)
        hSplit
    have hX₁ :
        ∃ m n : ℕ, Nonempty ((S.X₁ × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      fin_stabilization_right_of_prod (R := R) (M := S.X₃) (N := S.X₁) hX₃ hProd
    exact stablyFree_of_fin_stabilization (R := R) (M := S.X₁) hX₁

end CategoryTheory.ShortComplex

end
