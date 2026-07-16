import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import stacks_proof.stacks_project.Chap10.Lemma_10_72_5
import stacks_proof.stacks_project.Chap10.Lemma_10_74_1
import stacks_proof.stacks_project.Chap10.Proposition_10_102_9
import stacks_proof.stacks_project.Chap10.Remark_10_102_10.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Lean Meta Elab Tactic Term
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open RingTheory
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

/-- Helper for Remark 10.102.10: access the generated private lemmas imported from
`Lemma_10_102_2`. -/
private def lemma_10_102_2_private_name (decl : String) : Name :=
  Name.str (Name.str (Name.num `_private.stacks_project.Chap10.Lemma_10_102_2 0)
    "FiniteFreeComplex") decl

syntax (name := exactPrivate1022) "exact_private_1022 " str : tactic

elab_rules : tactic
  | `(tactic| exact_private_1022 $s:str) => do
      let goal ← getMainGoal
      let target ← goal.getType
      let c ← mkConstWithFreshMVarLevels (lemma_10_102_2_private_name s.getString)
      let cTy ← inferType c
      let (xs, _, _) ← forallMetaTelescopeReducing cTy
      let e := mkAppN c xs
      let eTy ← inferType e
      unless (← isDefEq eTy target) do
        throwError "private Lemma 10.102.2 bridge has type{indentExpr eTy}\nbut the current goal is{indentExpr target}"
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      goal.assign e
      replaceMainGoal []

namespace FiniteFreeComplex

/-- Helper for Remark 10.102.10: under the explicit product model of a biproduct, `biprod.map`
becomes the product linear map. -/
private lemma biprod_map_comp_biprodIsoProd_hom
    {M₁ M₂ N₁ N₂ : ModuleCat R} (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) :
    biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom =
      (ModuleCat.biprodIsoProd M₁ M₂).hom ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
  -- Proof comment: compare both candidate maps on the two source biproduct summands, where the
  -- explicit product model reduces everything to the obvious coordinate formulas.
  refine biprod.hom_ext' _ _ ?_ ?_
  · calc
      biprod.inl ≫ biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom =
          f ≫ biprod.inl ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom := by
            simp [Category.assoc]
      _ = f ≫ ModuleCat.ofHom (LinearMap.inl R N₁ N₂) := by
            rw [biprodIsoProd_inl_hom (R := R) N₁ N₂]
      _ = ModuleCat.ofHom (LinearMap.inl R M₁ M₂) ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            simp [LinearMap.prodMap_apply]
      _ = biprod.inl ≫ (ModuleCat.biprodIsoProd M₁ M₂).hom ≫
            ModuleCat.ofHom (f.hom.prodMap g.hom) := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            have hprod :=
              congrArg (fun z : M₁ × M₂ ↦ (f.hom.prodMap g.hom) z)
                (biprodIsoProd_hom_inl_apply (R := R) M₁ M₂ x)
            simpa [LinearMap.prodMap_apply] using hprod.symm
  · calc
      biprod.inr ≫ biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom =
          g ≫ biprod.inr ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom := by
            simp [Category.assoc]
      _ = g ≫ ModuleCat.ofHom (LinearMap.inr R N₁ N₂) := by
            rw [biprodIsoProd_inr_hom (R := R) N₁ N₂]
      _ = ModuleCat.ofHom (LinearMap.inr R M₁ M₂) ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro y
            simp [LinearMap.prodMap_apply]
      _ = biprod.inr ≫ (ModuleCat.biprodIsoProd M₁ M₂).hom ≫
            ModuleCat.ofHom (f.hom.prodMap g.hom) := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro y
            have hprod :=
              congrArg (fun z : M₁ × M₂ ↦ (f.hom.prodMap g.hom) z)
                (biprodIsoProd_hom_inr_apply (R := R) M₁ M₂ y)
            simpa [LinearMap.prodMap_apply] using hprod.symm

/-- Helper for Chap10 Remark 10 102 10: under the product model of source and target biproducts,
`biprod.map f g` applies as the product linear map. -/
private lemma biprod_map_biprodIsoProd_apply
    {M₁ M₂ N₁ N₂ : ModuleCat R} (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
    (x : M₁ × M₂) :
    ((ModuleCat.biprodIsoProd N₁ N₂).hom.hom)
      ((ModuleCat.Hom.hom (biprod.map f g))
        ((ModuleCat.biprodIsoProd M₁ M₂).inv.hom x)) =
      (f.hom.prodMap g.hom) x := by
  -- Proof comment: apply the categorical comparison to the inverse image of the product
  -- coordinate, then cancel the product-model isomorphism.
  have hcat :=
    biprod_map_comp_biprodIsoProd_hom (R := R) (M₁ := M₁) (M₂ := M₂)
      (N₁ := N₁) (N₂ := N₂) f g
  have happ :=
    congrArg
      (fun h : biprod M₁ M₂ ⟶ ModuleCat.of R (N₁ × N₂) ↦
        (ModuleCat.Hom.hom h) ((ModuleCat.biprodIsoProd M₁ M₂).inv.hom x))
      hcat
  simpa [LinearMap.comp_apply, LinearMap.prodMap_apply] using happ

/-- Helper for Remark 10.102.10: after the objectwise biproduct comparison, the differential of a
binary biproduct complex is the explicit biproduct map of the two summand differentials. -/
private lemma biprodXIso_differential_hom
    {K L : ChainComplex (ModuleCat R) ℕ} (j : ℕ) :
    ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom =
      (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
        biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
  -- Proof comment: compare the two candidate differentials after projecting to the two explicit
  -- degree-`j` summands, where the chain-map commutation squares supply the needed rewrites.
  apply biprod.hom_ext
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫ biprod.fst =
          ((biprod K L).d (j + 1) j) ≫ (biprod.fst : biprod K L ⟶ K).f j := by
            rw [biprodXIso_hom_comp_fst (R := R) K L j]
      _ = (biprod.fst : biprod K L ⟶ K).f (j + 1) ≫ K.d (j + 1) j := by
            simpa [Category.assoc] using
              ((biprod.fst : biprod K L ⟶ K).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫ biprod.fst ≫ K.d (j + 1) j := by
            simpa [Category.assoc] using
              congrArg (fun m ↦ m ≫ K.d (j + 1) j)
                (biprodXIso_hom_comp_fst (R := R) K L (j + 1)).symm
      _ =
          (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
            biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.fst := by
            simp [Category.assoc]
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫ biprod.snd =
          ((biprod K L).d (j + 1) j) ≫ (biprod.snd : biprod K L ⟶ L).f j := by
            rw [biprodXIso_hom_comp_snd (R := R) K L j]
      _ = (biprod.snd : biprod K L ⟶ L).f (j + 1) ≫ L.d (j + 1) j := by
            simpa [Category.assoc] using
              ((biprod.snd : biprod K L ⟶ L).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫ biprod.snd ≫ L.d (j + 1) j := by
            simpa [Category.assoc] using
              congrArg (fun m ↦ m ≫ L.d (j + 1) j)
                (biprodXIso_hom_comp_snd (R := R) K L (j + 1)).symm
      _ =
          (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
            biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.snd := by
            simp [Category.assoc]

/-- Helper for Chap10 Remark 10 102 10: conjugating a differential by a chain-complex
isomorphism gives the corresponding differential of the target complex. -/
private lemma chainIso_inv_d_hom
    {K L : ChainComplex (ModuleCat R) ℕ} (eiso : K ≅ L) (j : ℕ) :
    eiso.inv.f (j + 1) ≫ K.d (j + 1) j ≫ eiso.hom.f j = L.d (j + 1) j := by
  -- Proof comment: commute the inverse chain map across the row differential, then cancel its
  -- component against the forward component in degree `j`.
  have hcomm := eiso.inv.comm (j + 1) j
  have hid : eiso.inv.f j ≫ eiso.hom.f j = 𝟙 (L.X j) := by
    have hcomponent : (eiso.inv ≫ eiso.hom).f j = (𝟙 L : L ⟶ L).f j := by
      exact congrArg (fun f : L ⟶ L ↦ f.f j) eiso.inv_hom_id
    exact hcomponent
  calc
    eiso.inv.f (j + 1) ≫ K.d (j + 1) j ≫ eiso.hom.f j =
        L.d (j + 1) j ≫ eiso.inv.f j ≫ eiso.hom.f j := by
          simpa [Category.assoc] using congrArg (fun m ↦ m ≫ eiso.hom.f j) hcomm
    _ = L.d (j + 1) j := by
          simpa [Category.assoc, hid]

/-- Helper for Remark 10.102.10: the forward and inverse maps of a chain-complex isomorphism
compose to the identity on each displayed component of the target complex. -/
private lemma componentHom_comp_componentInv
    {K L : ChainComplex (ModuleCat R) ℕ} (eiso : K ≅ L) (j : ℕ) :
    (eiso.hom.f j).hom.comp (eiso.inv.f j).hom = LinearMap.id := by
  let L' := L
  have hcat : eiso.inv.f j ≫ eiso.hom.f j = 𝟙 _ := by
    -- Proof comment: read the inverse-after-forward identity at degree `j`.
    have hcomponent : (eiso.inv ≫ eiso.hom).f j = (𝟙 L' : L' ⟶ L').f j := by
      exact congrArg (fun f : L' ⟶ L' ↦ f.f j) eiso.inv_hom_id
    exact hcomponent
  -- Proof comment: pass from the categorical component equality to the underlying linear maps.
  exact congrArg ModuleCat.Hom.hom hcat

/-- Helper for Remark 10.102.10: the inverse and forward maps of a chain-complex isomorphism
compose to the identity on each displayed component of the source complex. -/
private lemma componentInv_comp_componentHom
    {K L : ChainComplex (ModuleCat R) ℕ} (eiso : K ≅ L) (j : ℕ) :
    (eiso.inv.f j).hom.comp (eiso.hom.f j).hom = LinearMap.id := by
  let K' := K
  have hcat : eiso.hom.f j ≫ eiso.inv.f j = 𝟙 _ := by
    -- Proof comment: read the forward-after-inverse identity at degree `j`.
    have hcomponent : (eiso.hom ≫ eiso.inv).f j = (𝟙 K' : K' ⟶ K').f j := by
      exact congrArg (fun f : K' ⟶ K' ↦ f.f j) eiso.hom_inv_id
    exact hcomponent
  -- Proof comment: pass from the categorical component equality to the underlying linear maps.
  exact congrArg ModuleCat.Hom.hom hcat

/-- Helper for Remark 10.102.10: a chain-complex isomorphism gives a linear equivalence in each
degree, with the inverse identities cached for later split-row coordinate maps. -/
private noncomputable def chainIsoComponentLinearEquiv
    {K L : ChainComplex (ModuleCat R) ℕ} (eiso : K ≅ L) (j : ℕ) :
    K.X j ≃ₗ[R] L.X j :=
  LinearEquiv.ofLinear (eiso.hom.f j).hom (eiso.inv.f j).hom
    (componentHom_comp_componentInv (R := R) eiso j)
    (componentInv_comp_componentHom (R := R) eiso j)

/-- Helper for Remark 10.102.10: the standard free module on `Fin (a + b)` is linearly equivalent
to the product of the standard free modules on `Fin a` and `Fin b`. -/
private noncomputable def standard_module_sum_linearEquiv (a b : ℕ) :
    ((Fin a → R) × (Fin b → R)) ≃ₗ[R] (Fin (a + b) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).symm.trans <|
    (LinearEquiv.piCongrLeft R (fun _ : Fin a ⊕ Fin b ↦ R) finSumFinEquiv.symm).symm

/-- Helper for Chap10 Remark 10 102 10: the standard sum equivalence restricts to the left
coordinate on the left finite block. -/
private lemma standard_module_sum_linearEquiv_apply_castAdd (a b : ℕ)
    (x : (Fin a → R) × (Fin b → R)) (i : Fin a) :
    standard_module_sum_linearEquiv (R := R) a b x (Fin.castAdd b i) = x.1 i := by
  -- Proof comment: unfold the finite-sum reindexing and evaluate on the left summand.
  rcases x with ⟨x₁, x₂⟩
  simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_symm_apply_castAdd,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]

/-- Helper for Chap10 Remark 10 102 10: the standard sum equivalence restricts to the right
coordinate on the right finite block. -/
private lemma standard_module_sum_linearEquiv_apply_natAdd (a b : ℕ)
    (x : (Fin a → R) × (Fin b → R)) (i : Fin b) :
    standard_module_sum_linearEquiv (R := R) a b x (Fin.natAdd a i) = x.2 i := by
  -- Proof comment: unfold the finite-sum reindexing and evaluate on the right summand.
  rcases x with ⟨x₁, x₂⟩
  simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_symm_apply_natAdd,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

/-- Helper for Chap10 Remark 10 102 10: a left-block basis vector splits as the corresponding
left product basis vector. -/
private lemma standard_module_sum_linearEquiv_symm_single_castAdd (a b : ℕ) (i : Fin a) :
    (standard_module_sum_linearEquiv (R := R) a b).symm (Pi.single (Fin.castAdd b i) 1) =
      (Pi.single i 1, 0) := by
  -- Proof comment: compare the two product coordinates after reassembling by the standard sum
  -- equivalence.
  ext j
  · by_cases hji : j = i
    · subst hji
      simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
        Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_apply_left]
    · have hne : Fin.castAdd b j ≠ Fin.castAdd b i := by
        intro h
        exact hji ((Fin.castAdd_injective a b) h)
      simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
        Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_apply_left, hne, hji]
  · have hne : Fin.natAdd a j ≠ Fin.castAdd b i := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
      omega
    simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
      Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_apply_right, hne]

/-- Helper for Chap10 Remark 10 102 10: a right-block basis vector splits as the corresponding
right product basis vector. -/
private lemma standard_module_sum_linearEquiv_symm_single_natAdd (a b : ℕ) (i : Fin b) :
    (standard_module_sum_linearEquiv (R := R) a b).symm (Pi.single (Fin.natAdd a i) 1) =
      (0, Pi.single i 1) := by
  -- Proof comment: compare the two product coordinates after reassembling by the standard sum
  -- equivalence.
  ext j
  · have hne : Fin.castAdd b j ≠ Fin.natAdd a i := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
      omega
    simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
      Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_apply_left, hne]
  · by_cases hji : j = i
    · subst hji
      simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
        Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_apply_right]
    · have hne : Fin.natAdd a j ≠ Fin.natAdd a i := by
        intro h
        exact hji ((Fin.natAdd_injective b a) h)
      simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
        Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_apply_right, hne, hji]

/-- Helper for Remark 10.102.10: every term of the identity disk is the standard finite free
module with the displayed identity-disk rank. -/
private lemma identityDiskComplex_X_eq_rank (i : Fin e) (j : ℕ) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).X j =
      ModuleCat.of R (Fin (FiniteFreeComplex.identityDiskRank i j) → R) := by
  -- Proof comment: this records the definitional object formula once for downstream transports.
  rfl

/-- Helper for Remark 10.102.10: the identity-disk term in degree `j` is identified with its
standard finite-coordinate module. -/
private noncomputable def identityDiskTermEquiv (i : Fin e) (j : ℕ) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).X j ≃ₗ[R]
      (Fin (FiniteFreeComplex.identityDiskRank i j) → R) :=
  (eqToIso (identityDiskComplex_X_eq_rank (R := R) i j)).toLinearEquiv

/-- Helper for Remark 10.102.10: the source term of row `k` in a split model, transported to
the product of the reduced-complex source term and the identity-disk source term. -/
private noncomputable def splitRowSourceEquiv
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i))
    (k : Fin e) :
    (Fin (D.rank k.succ) → R) ≃ₗ[R]
      ((Fin (D'.rank k.succ) → R) ×
        (Fin (FiniteFreeComplex.identityDiskRank i (k.1 + 1)) → R)) :=
  (((D.termIso k.succ).toLinearEquiv.symm.trans
      (chainIsoComponentLinearEquiv (R := R) eiso (k.1 + 1))).trans
    (HomologicalComplex.biprodXIso D'.toChainComplex
      (FiniteFreeComplex.identityDiskComplex (R := R) i) (k.1 + 1)).toLinearEquiv).trans
    ((ModuleCat.biprodIsoProd (D'.toChainComplex.X (k.1 + 1))
      ((FiniteFreeComplex.identityDiskComplex (R := R) i).X (k.1 + 1))).toLinearEquiv.trans
      (LinearEquiv.prodCongr (D'.termIso k.succ).toLinearEquiv
        (identityDiskTermEquiv (R := R) i (k.1 + 1))))

/-- Helper for Remark 10.102.10: the target term of row `k` in a split model, transported to
the product of the reduced-complex target term and the identity-disk target term. -/
private noncomputable def splitRowTargetEquiv
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i))
    (k : Fin e) :
    (Fin (D.rank k.castSucc) → R) ≃ₗ[R]
      ((Fin (D'.rank k.castSucc) → R) ×
        (Fin (FiniteFreeComplex.identityDiskRank i k.1) → R)) :=
  (((D.termIso k.castSucc).toLinearEquiv.symm.trans
      (chainIsoComponentLinearEquiv (R := R) eiso k.1)).trans
    (HomologicalComplex.biprodXIso D'.toChainComplex
      (FiniteFreeComplex.identityDiskComplex (R := R) i) k.1).toLinearEquiv).trans
    ((ModuleCat.biprodIsoProd (D'.toChainComplex.X k.1)
      ((FiniteFreeComplex.identityDiskComplex (R := R) i).X k.1)).toLinearEquiv.trans
      (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
        (identityDiskTermEquiv (R := R) i k.1)))

/-- Helper for Remark 10.102.10: the row differential of the identity disk written in the
finite-coordinate terms used by the split-row normal form. -/
private noncomputable def identityDiskRowInCoordinates (i : Fin e) (k : Fin e) :
    (Fin (FiniteFreeComplex.identityDiskRank i (k.1 + 1)) → R) →ₗ[R]
      (Fin (FiniteFreeComplex.identityDiskRank i k.1) → R) :=
  (identityDiskTermEquiv (R := R) i k.1).toLinearMap.comp
    (((FiniteFreeComplex.identityDiskComplex (R := R) i).d (k.1 + 1) k.1).hom.comp
      (identityDiskTermEquiv (R := R) i (k.1 + 1)).symm.toLinearMap)

/-- Helper for Remark 10.102.10: away from its supported degree, the identity-disk row is the
zero finite-coordinate map. -/
private lemma identityDiskRowInCoordinates_eq_zero_of_ne (i : Fin e) {k : Fin e}
    (hk : k.1 ≠ i.1) :
    identityDiskRowInCoordinates (R := R) i k = 0 := by
  -- Proof comment: the imported off-support chain differential becomes zero after the named
  -- source and target coordinate identifications.
  unfold identityDiskRowInCoordinates
  rw [FiniteFreeComplex.identityDiskComplex_d_eq_zero_of_ne (R := R) (i := i) hk]
  ext x j
  simp

/-- Helper for Chap10 Remark 10 102 10: the two supported terms of `identityDiskComplex i`
are the same rank-one module. -/
private lemma identityDiskComplex_supported_terms_eq (i : Fin e) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).X (i.1 + 1) =
      (FiniteFreeComplex.identityDiskComplex (R := R) i).X i.1 := by
  -- Proof comment: both object formulas reduce to `ModuleCat.of R (Fin 1 → R)`.
  rw [identityDiskComplex_X_eq_succ (R := R) (e := e) i,
    identityDiskComplex_X_eq_castSucc (R := R) (e := e) i]

/-- Helper for Remark 10.102.10: in degree `i`, the displayed differential row of
`identityDiskComplex i` is the identity on the supported rank-one summand. -/
private lemma identityDiskComplex_d_eq_id (i : Fin e) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 =
      eqToHom (identityDiskComplex_supported_terms_eq (R := R) i) := by
  -- Proof comment: cancel the source transport in the imported supported-row computation, then
  -- compose the two object identifications into the displayed `eqToHom`.
  have hrow := identityDiskComplex_eqToHom_symm_comp_d (R := R) (e := e) i
  calc
    (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 =
        eqToHom (identityDiskComplex_X_eq_succ (R := R) (e := e) i) ≫
          eqToHom (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm := by
          rw [← hrow]
          simp [Category.assoc]
    _ = eqToHom (identityDiskComplex_supported_terms_eq (R := R) i) := by
          simp [CategoryTheory.eqToHom_trans]

/-- Helper for Chap10 Remark 10 102 10: the supported identity-disk source and target finite
coordinate modules are identified through the named supported object equality. -/
private noncomputable def identityDiskSupportedEquiv (i : Fin e) :
    (Fin (FiniteFreeComplex.identityDiskRank i (i.1 + 1)) → R) ≃ₗ[R]
      (Fin (FiniteFreeComplex.identityDiskRank i i.1) → R) :=
  (((identityDiskTermEquiv (R := R) i (i.1 + 1)).symm.trans
    (eqToIso (identityDiskComplex_supported_terms_eq (R := R) i)).toLinearEquiv).trans
    (identityDiskTermEquiv (R := R) i i.1))

/-- Helper for Remark 10.102.10: on its supported degree, the identity-disk row is the rank-one
identity map in finite coordinates. -/
private lemma identityDiskRowInCoordinates_eq_id (i : Fin e) :
    identityDiskRowInCoordinates (R := R) i i =
      (identityDiskSupportedEquiv (R := R) i).toLinearMap := by
  -- Proof comment: the supported chain differential is the displayed `eqToHom`; after the two
  -- coordinate identifications, this is exactly the canonical rank-one coordinate transport.
  unfold identityDiskRowInCoordinates
  rw [identityDiskComplex_d_eq_id (R := R) (i := i)]
  rfl

/-- Helper for Remark 10.102.10: coordinate conjugation preserves whether the rank-minor ideal is
the unit ideal. -/
private lemma rankMinorIdeal_eq_top_iff_of_linearEquiv_conj {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    I(eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) = ⊤ ↔ I(φ) = ⊤ := by
  rw [rankMinorIdeal_eq_of_linearEquiv_conj (R := R) (φ := φ) eSource eTarget]

/-- Helper for Remark 10.102.10: coordinate conjugation also preserves the unit rank-minor ideal
predicate when invariant basis number identifies differently written finite coordinate sizes. -/
private lemma rankMinorIdeal_eq_top_iff_of_linearEquiv_conj' [Nontrivial R] {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R)) :
    I(eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) = ⊤ ↔ I(φ) = ⊤ := by
  -- Proof comment: delegate the matrix comparison to the theorem-local conjugation API and only
  -- rewrite the resulting equality of ideals into the top-ideal predicate needed below.
  rw [rankMinorIdeal_eq_of_linearEquiv_conj' (R := R) (φ := φ) eSource eTarget]

/-- Helper for Chap10 Remark 10 102 10: the product of two finite-coordinate rows, reindexed as
a row between the corresponding summed finite free modules. -/
private noncomputable def prodMapInStandardCoordinates {m n p q : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (ψ : (Fin p → R) →ₗ[R] (Fin q → R)) :
    (Fin (m + p) → R) →ₗ[R] (Fin (n + q) → R) :=
  (standard_module_sum_linearEquiv (R := R) n q).toLinearMap.comp
    ((φ.prodMap ψ).comp (standard_module_sum_linearEquiv (R := R) m p).symm.toLinearMap)

/-- Helper for Chap10 Remark 10 102 10: reindexing rows and columns by equivalences does not
change a fixed-size determinantal ideal. -/
private lemma matrix_minorIdeal_reindex_eq
    {ι ι' κ κ' : Type*} (r : ℕ) (A : Matrix ι κ R) (e₁ : ι ≃ ι') (e₂ : κ ≃ κ') :
    Matrix.minorIdeal r (Matrix.reindex e₁ e₂ A) = Matrix.minorIdeal r A := by
  -- Proof comment: each selected minor of the reindexed matrix is the corresponding selected
  -- minor of the original matrix, and conversely after using the inverse reindexing.
  refine le_antisymm ?_ ?_
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨f₁, f₂⟩, rfl⟩
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using
      Matrix.det_submatrix_mem_minorIdeal r A
        (f₁.trans e₁.symm.toEmbedding) (f₂.trans e₂.symm.toEmbedding)
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨f₁, f₂⟩, rfl⟩
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using
      Matrix.det_submatrix_mem_minorIdeal r (Matrix.reindex e₁ e₂ A)
        (f₁.trans e₁.toEmbedding) (f₂.trans e₂.toEmbedding)

/-- Helper for Chap10 Remark 10 102 10: in the finite-sum coordinate order, a product row has
the expected block-diagonal matrix. -/
private lemma toMatrix_prodMapInStandardCoordinates {m n p q : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (ψ : (Fin p → R) →ₗ[R] (Fin q → R)) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + q)))
          (prodMapInStandardCoordinates (R := R) φ ψ)) =
      Matrix.fromBlocks
        (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ)
        0 0
        (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin q)) ψ) := by
  -- Proof comment: the chosen sum coordinate equivalence sends left and right summands to the
  -- matching product coordinates, so every block entry reduces to the defining product map.
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [Matrix.reindex_apply, prodMapInStandardCoordinates,
            LinearMap.toMatrix_apply, LinearMap.prodMap_apply,
            standard_module_sum_linearEquiv_apply_castAdd,
            standard_module_sum_linearEquiv_symm_single_castAdd,
            finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      | inr j =>
          simp [Matrix.reindex_apply, prodMapInStandardCoordinates,
            LinearMap.toMatrix_apply, LinearMap.prodMap_apply,
            standard_module_sum_linearEquiv_apply_castAdd,
            standard_module_sum_linearEquiv_symm_single_natAdd,
            finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  | inr i =>
      cases j with
      | inl j =>
          simp [Matrix.reindex_apply, prodMapInStandardCoordinates,
            LinearMap.toMatrix_apply, LinearMap.prodMap_apply,
            standard_module_sum_linearEquiv_apply_natAdd,
            standard_module_sum_linearEquiv_symm_single_castAdd,
            finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      | inr j =>
          simp [Matrix.reindex_apply, prodMapInStandardCoordinates,
            LinearMap.toMatrix_apply, LinearMap.prodMap_apply,
            standard_module_sum_linearEquiv_apply_natAdd,
            standard_module_sum_linearEquiv_symm_single_natAdd,
            finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]

/-- Helper for Chap10 Remark 10 102 10: if a predicate is false above `a`, increasing the
`Nat.findGreatest` search bound past `a` does not change the result. -/
private lemma findGreatest_eq_of_false_above {P : ℕ → Prop} [DecidablePred P]
    {a b : ℕ} (hab : a ≤ b) (hfalse : ∀ ⦃r : ℕ⦄, a < r → ¬ P r) :
    Nat.findGreatest P b = Nat.findGreatest P a := by
  induction b with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst ha
      rfl
  | succ b ih =>
      by_cases hba : a = b + 1
      · subst hba
        rfl
      · have hab' : a ≤ b := by omega
        rw [Nat.findGreatest_of_not]
        · exact ih hab'
        · exact hfalse (by omega)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: exterior powers above the source or target rank of a
finite-coordinate map vanish. -/
private lemma exteriorPower_map_eq_zero_of_min_lt [Nontrivial R]
    {m n r : ℕ} (h : min m n < r) (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorPower.map r φ = 0 := by
  -- Proof comment: if the exterior degree exceeds the source or target rank, the corresponding
  -- exterior power has finrank zero, so the map is forced to be zero.
  have hmn : m < r ∨ n < r := by omega
  rcases hmn with hm' | hn'
  ·
    have hfin : Module.finrank R (⋀[R]^r (Fin m → R)) = 0 := by
      rw [exteriorPower.finrank_eq]
      simpa using Nat.choose_eq_zero_of_lt hm'
    haveI : Subsingleton (⋀[R]^r (Fin m → R)) :=
      (Module.finrank_eq_zero_iff_of_free R (⋀[R]^r (Fin m → R))).mp hfin
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    simp
  ·
    have hfin : Module.finrank R (⋀[R]^r (Fin n → R)) = 0 := by
      rw [exteriorPower.finrank_eq]
      simpa using Nat.choose_eq_zero_of_lt hn'
    haveI : Subsingleton (⋀[R]^r (Fin n → R)) :=
      (Module.finrank_eq_zero_iff_of_free R (⋀[R]^r (Fin n → R))).mp hfin
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: the zeroth exterior-power map of a finite-coordinate
linear map is nonzero over a nontrivial base ring. -/
private lemma exteriorPower_map_zero_ne_zero [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorPower.map 0 φ ≠ 0 := by
  -- Proof comment: naturality of `zeroEquiv` identifies the zeroth exterior-power map with the
  -- identity map on `R`.
  intro hzero
  have hnat := exteriorPower.zeroEquiv_naturality (R := R) φ
  have hval :=
    LinearMap.congr_fun hnat
      (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → (Fin m → R)))
  rw [hzero] at hval
  simp [exteriorPower.zeroEquiv_ιMulti] at hval

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: the exterior-power map in the exterior rank degree is
nonzero. -/
private lemma exteriorPower_map_exteriorRank_ne_zero [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorPower.map (LinearMap.exteriorRank φ) φ ≠ 0 := by
  -- Proof comment: the defining `findGreatest` has the nonzero degree `0` available.
  letI : DecidablePred (fun r ↦ exteriorPower.map r φ ≠ 0) := Classical.decPred _
  unfold LinearMap.exteriorRank
  exact Nat.findGreatest_spec (P := fun r ↦ exteriorPower.map r φ ≠ 0)
    (m := 0) (n := min m n) (zero_le _) (exteriorPower_map_zero_ne_zero (R := R) φ)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: if the map on `r`th exterior powers is zero, then all
`r × r` minors of the coordinate matrix vanish. -/
private lemma matrix_minorIdeal_eq_bot_of_exteriorPower_map_eq_zero {m n r : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hmap : exteriorPower.map r φ = 0) :
    Matrix.minorIdeal r
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) = ⊥ := by
  -- Proof comment: apply arbitrary exterior dual coordinate functionals to the zero map; the
  -- resulting values are exactly the selected determinants, up to transpose.
  rw [Matrix.minorIdeal, Ideal.span_eq_bot]
  intro x hx
  rcases hx with ⟨⟨e₁, e₂⟩, rfl⟩
  let f : Fin r → Module.Dual R (Fin n → R) :=
    fun j ↦ (Pi.basisFun R (Fin n)).coord (e₁ j)
  let v : Fin r → (Fin m → R) := fun i ↦ Pi.basisFun R (Fin m) (e₂ i)
  have h :=
    congrArg
      (fun g : (⋀[R]^r (Fin m → R)) →ₗ[R] (⋀[R]^r (Fin n → R)) ↦
        exteriorPower.pairingDual R (Fin n → R) r (exteriorPower.ιMulti R r f)
          (g (exteriorPower.ιMulti R r v)))
      hmap
  have hdet :
      (Matrix.of fun i j : Fin r ↦
        (Pi.basisFun R (Fin n)).coord (e₁ j)
          (φ (Pi.basisFun R (Fin m) (e₂ i)))).det = 0 := by
    simpa [f, v, exteriorPower.map_apply_ιMulti] using h
  have htranspose :
      (Matrix.of fun i j : Fin r ↦
        (Pi.basisFun R (Fin n)).coord (e₁ j)
          (φ (Pi.basisFun R (Fin m) (e₂ i)))) =
        ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix
          e₁ e₂).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  change
    ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix
      e₁ e₂).det = 0
  rw [← Matrix.det_transpose, ← htranspose]
  exact hdet

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: if all `r × r` minors vanish, then the `r`th
exterior-power map is zero. -/
private lemma exteriorPower_map_eq_zero_of_matrix_minorIdeal_eq_bot {m n r : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hminor : Matrix.minorIdeal r
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) = ⊥) :
    exteriorPower.map r φ = 0 := by
  -- Proof comment: evaluate the image of every source exterior basis vector against every target
  -- exterior basis coordinate; each coordinate is one of the vanishing minors.
  classical
  let bM := (Pi.basisFun R (Fin m)).exteriorPower r
  let bN := (Pi.basisFun R (Fin n)).exteriorPower r
  apply bM.ext
  intro s
  apply bN.repr.injective
  ext t
  let e₁ : Fin r ↪ Fin n := (Set.powersetCard.ofFinEmbEquiv.symm t).toEmbedding
  let e₂ : Fin r ↪ Fin m := (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding
  have hdet_mem :
      ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix
        e₁ e₂).det ∈
        Matrix.minorIdeal r
          (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) :=
    Matrix.det_submatrix_mem_minorIdeal r
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) e₁ e₂
  have hdet_zero :
      ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix
        e₁ e₂).det = 0 := by
    have hbot :
        ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix
          e₁ e₂).det ∈ (⊥ : Ideal R) := by
      simpa [hminor] using hdet_mem
    simpa using hbot
  have hcoord :
      bN.repr (exteriorPower.map r φ (bM s)) t =
        ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix
          e₁ e₂).det := by
    have hbM_apply : bM s = exteriorPower.ιMulti_family R r (Pi.basisFun R (Fin m)) s := by
      simp [bM, exteriorPower.basis_apply]
    rw [hbM_apply]
    rw [exteriorPower.map_apply_ιMulti_family]
    have hbN_repr :
      bN.repr (exteriorPower.ιMulti_family R r (φ ∘ Pi.basisFun R (Fin m)) s) t =
        exteriorPower.ιMultiDual R r (Pi.basisFun R (Fin n)) t
          (exteriorPower.ιMulti_family R r (φ ∘ Pi.basisFun R (Fin m)) s) := by
      simp [bN, exteriorPower.basis_repr_apply]
    rw [hbN_repr]
    simp only [exteriorPower.ιMulti_family]
    rw [exteriorPower.ιMultiDual_apply_ιMulti]
    rw [← Matrix.det_transpose]
    congr 1
    ext i j
    simp [e₁, e₂, LinearMap.toMatrix_apply]
  rw [hcoord, hdet_zero]
  have hzrepr : bN.repr (0 : ⋀[R]^r (Fin n → R)) = 0 := map_zero bN.repr
  have hzero_apply :
      (0 : (⋀[R]^r (Fin m → R)) →ₗ[R] (⋀[R]^r (Fin n → R))) (bM s) = 0 := rfl
  rw [hzero_apply, hzrepr]
  rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: minors strictly above the exterior rank vanish. -/
private lemma matrix_minorIdeal_eq_bot_of_exteriorRank_lt [Nontrivial R]
    {m n r : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hr : LinearMap.exteriorRank φ < r) :
    Matrix.minorIdeal r
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) = ⊥ := by
  -- Proof comment: above the defining greatest nonzero exterior degree, the exterior-power map
  -- is zero, hence so are all minors.
  apply matrix_minorIdeal_eq_bot_of_exteriorPower_map_eq_zero (R := R) φ
  by_cases hrle : r ≤ min m n
  · by_contra hnonzero
    have hle : r ≤ LinearMap.exteriorRank φ := by
      letI : DecidablePred (fun r ↦ exteriorPower.map r φ ≠ 0) := Classical.decPred _
      unfold LinearMap.exteriorRank
      exact Nat.le_findGreatest hrle hnonzero
    omega
  · exact exteriorPower_map_eq_zero_of_min_lt (R := R) (Nat.lt_of_not_ge hrle) φ

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: the minor ideal in the exterior-rank degree is nonzero. -/
private lemma matrix_minorIdeal_exteriorRank_ne_bot [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Matrix.minorIdeal (LinearMap.exteriorRank φ)
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) ≠ ⊥ := by
  -- Proof comment: if those minors vanished, the exterior-rank exterior-power map would vanish.
  intro hbot
  have hmap :=
    exteriorPower_map_eq_zero_of_matrix_minorIdeal_eq_bot (R := R) φ hbot
  exact (exteriorPower_map_exteriorRank_ne_zero (R := R) φ) hmap

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: if the selected minor size exceeds the row count, the
minor ideal is zero. -/
private lemma matrix_minorIdeal_eq_bot_of_row_lt {ι κ : Type*} [Fintype ι]
    {r : ℕ} (h : Fintype.card ι < r) (A : Matrix ι κ R) :
    Matrix.minorIdeal r A = ⊥ := by
  -- Proof comment: an `r`-row minor would require an embedding `Fin r ↪ ι`, contradicting the
  -- cardinality inequality.
  rw [Matrix.minorIdeal, Ideal.span_eq_bot]
  intro x hx
  rcases hx with ⟨⟨e₁, _e₂⟩, rfl⟩
  exfalso
  have hle : r ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_embedding e₁
  omega

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: the full-size minor ideal of a finite-coordinate linear
equivalence is the unit ideal. -/
private lemma matrix_minorIdeal_linearEquiv_full_eq_top [Nontrivial R] {p : ℕ}
    (e : (Fin p → R) ≃ₗ[R] (Fin p → R)) :
    Matrix.minorIdeal p
      (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap) = ⊤ := by
  -- Proof comment: the full determinant of an invertible coordinate matrix is a unit.
  let A := LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap
  have heUnit : IsUnit (e.toLinearMap : Module.End R (Fin p → R)) := by
    refine ⟨⟨e.toLinearMap, e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
    · ext x
      simp
    · ext x
      simp
  have hmatUnit : IsUnit A := by
    simpa [A] using
      (LinearMap.isUnit_toMatrix_iff (v₁ := Pi.basisFun R (Fin p))).2 heUnit
  have hdetUnit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hmatUnit
  refine Ideal.eq_top_of_isUnit_mem _ ?_ hdetUnit
  change A.det ∈ Matrix.minorIdeal p A
  exact Matrix.det_submatrix_mem_minorIdeal p A
    (Function.Embedding.refl _) (Function.Embedding.refl _)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Remark 10 102 10: at the shifted exterior-rank degree, the block diagonal
matrix with a linear-equivalence block has the same minor ideal as the first block. -/
private lemma matrix_minorIdeal_fromBlocks_linearEquiv_at_exteriorRank_eq [Nontrivial R]
    {m n p : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (e : (Fin p → R) ≃ₗ[R] (Fin p → R)) :
    Matrix.minorIdeal (LinearMap.exteriorRank φ + p)
      (Matrix.fromBlocks
        (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ)
        0 0
        (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap)) =
      Matrix.minorIdeal (LinearMap.exteriorRank φ)
        (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) := by
  -- Proof comment: in the block-minor expansion, all antidiagonal terms vanish except the one
  -- taking exterior-rank minors from `φ` and full-size minors from the equivalence block.
  rw [Matrix.minorIdeal_fromBlocks]
  rw [Finset.sum_eq_single (LinearMap.exteriorRank φ, p)]
  · rw [matrix_minorIdeal_linearEquiv_full_eq_top (R := R) e]
    simp
  · intro b hb hbne
    have hsum := Finset.mem_antidiagonal.mp hb
    by_cases hbp : b.2 ≤ p
    · have hb2lt : b.2 < p := by
        by_contra hnot
        have hb2 : b.2 = p := le_antisymm hbp (Nat.le_of_not_gt hnot)
        have hb1 : b.1 = LinearMap.exteriorRank φ := by omega
        exact hbne (Prod.ext hb1 hb2)
      have hb1gt : LinearMap.exteriorRank φ < b.1 := by omega
      rw [matrix_minorIdeal_eq_bot_of_exteriorRank_lt (R := R) φ hb1gt]
      simp
    · have hplt : p < b.2 := Nat.lt_of_not_ge hbp
      have hcard : Fintype.card (Fin p) < b.2 := by
        simpa using hplt
      rw [matrix_minorIdeal_eq_bot_of_row_lt (R := R)
        hcard (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap)]
      simp
  · intro hnot
    have hmem_pair :
        (LinearMap.exteriorRank φ, p) ∈ Finset.antidiagonal (LinearMap.exteriorRank φ + p) :=
      Finset.mem_antidiagonal.mpr rfl
    exact (hnot hmem_pair).elim

/-- Helper for Chap10 Remark 10 102 10: positive minors of the zero matrix generate the zero
ideal. -/
private lemma matrix_minorIdeal_zero_eq_bot_of_pos
    {ι κ : Type*} {r : ℕ} (hr : 0 < r) :
    Matrix.minorIdeal r (0 : Matrix ι κ R) = ⊥ := by
  -- Proof comment: every positive-size selected minor of the zero matrix has determinant zero.
  refine le_antisymm ?_ bot_le
  refine Ideal.span_le.2 ?_
  rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
  change (0 : Matrix (Fin r) (Fin r) R).det ∈ (⊥ : Ideal R)
  rw [Matrix.det_zero (show Nonempty (Fin r) from ⟨⟨0, hr⟩⟩)]
  simp

/-- Helper for Chap10 Remark 10 102 10: zero-size minors of any matrix generate the unit ideal. -/
private lemma matrix_minorIdeal_zero_size_eq_top {ι κ : Type*} (A : Matrix ι κ R) :
    Matrix.minorIdeal 0 A = ⊤ := by
  -- Proof comment: the unique `0 × 0` minor has determinant `1`.
  rw [Matrix.minorIdeal, Ideal.eq_top_iff_one]
  refine Ideal.subset_span ?_
  let e₁ : Fin 0 ↪ ι := ⟨Fin.elim0, fun x ↦ Fin.elim0 x⟩
  let e₂ : Fin 0 ↪ κ := ⟨Fin.elim0, fun x ↦ Fin.elim0 x⟩
  refine ⟨⟨e₁, e₂⟩, ?_⟩
  simp

/-- Helper for Chap10 Remark 10 102 10: the block formula for a zero second diagonal block
reduces to the first block at a fixed minor size. -/
private lemma matrix_minorIdeal_fromBlocks_zero_right_eq
    {ι κ ι' κ' : Type*} (r : ℕ) (A : Matrix ι κ R) :
    (Finset.antidiagonal r).sum
        (fun x : ℕ × ℕ ↦ Matrix.minorIdeal x.1 A *
          Matrix.minorIdeal x.2 (0 : Matrix ι' κ' R)) =
      Matrix.minorIdeal r A := by
  -- Proof comment: in the antidiagonal sum all terms with positive second component vanish, and
  -- the unique term with second component zero is `I_r(A) * ⊤`.
  rw [Finset.sum_eq_single (r, 0)]
  · simp [matrix_minorIdeal_zero_size_eq_top]
  · intro b hb hbne
    have hsum := Finset.mem_antidiagonal.mp hb
    have hbpos : 0 < b.2 := by
      by_contra h
      have hb2 : b.2 = 0 := Nat.eq_zero_of_not_pos h
      have hb1 : b.1 = r := by omega
      exact hbne (Prod.ext hb1 hb2)
    simp [matrix_minorIdeal_zero_eq_bot_of_pos (R := R) hbpos]
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr (by simp))).elim

/-- Helper for Chap10 Remark 10 102 10: a zero product summand does not change the exterior rank
of the row in standard summed coordinates. -/
private lemma exteriorRank_prodMapInStandardCoordinates_zero_eq [Nontrivial R]
    {m n p q : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    LinearMap.exteriorRank
        (prodMapInStandardCoordinates (R := R) φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))) =
      LinearMap.exteriorRank φ := by
  classical
  let F : (Fin (m + p) → R) →ₗ[R] (Fin (n + q) → R) :=
    prodMapInStandardCoordinates (R := R) φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))
  have hF_factor :
      F =
        (standard_module_sum_linearEquiv (R := R) n q).toLinearMap.comp
          ((LinearMap.inl R (Fin n → R) (Fin q → R)).comp
            (φ.comp
              ((LinearMap.fst R (Fin m → R) (Fin p → R)).comp
                (standard_module_sum_linearEquiv (R := R) m p).symm.toLinearMap))) := by
    -- Proof comment: the product with a zero second component factors through the first target
    -- summand.
    ext x j
    dsimp [F]
    by_cases hj : j.1 < n
    · let j₀ : Fin n := Fin.castLT j hj
      have hj_eq : j = Fin.castAdd q j₀ := by
        apply Fin.ext
        rfl
      rw [hj_eq]
      simp [prodMapInStandardCoordinates, LinearMap.prodMap_apply,
        standard_module_sum_linearEquiv_apply_castAdd]
    · have hn_le : n ≤ j.1 := Nat.le_of_not_gt hj
      let j₀ : Fin q := ⟨j.1 - n, by omega⟩
      have hj_eq : j = Fin.natAdd n j₀ := by
        apply Fin.ext
        simp [j₀]
        omega
      rw [hj_eq]
      simp [prodMapInStandardCoordinates, LinearMap.prodMap_apply,
        standard_module_sum_linearEquiv_apply_natAdd]
  have hφ_recover :
      φ =
        (LinearMap.fst R (Fin n → R) (Fin q → R)).comp
          ((standard_module_sum_linearEquiv (R := R) n q).symm.toLinearMap.comp
            (F.comp
              ((standard_module_sum_linearEquiv (R := R) m p).toLinearMap.comp
                (LinearMap.inl R (Fin m → R) (Fin p → R))))) := by
    -- Proof comment: include in the first source summand, apply the product row, then project
    -- back from the first target summand.
    ext x i
    dsimp [F]
    simp [prodMapInStandardCoordinates, LinearMap.prodMap_apply]
  have hpred :
      (fun r ↦ exteriorPower.map r F ≠ 0) =
        fun r ↦ exteriorPower.map r φ ≠ 0 := by
    funext r
    apply propext
    constructor
    · intro hF hφ
      apply hF
      rw [hF_factor]
      simp [exteriorPower.map_comp, hφ]
    · intro hφ hFzero
      apply hφ
      rw [hφ_recover]
      simp [exteriorPower.map_comp, hFzero]
  unfold LinearMap.exteriorRank
  rw [hpred]
  exact @findGreatest_eq_of_false_above (fun r ↦ exteriorPower.map r φ ≠ 0)
    (Classical.decPred _) (min m n) (min (m + p) (n + q)) (by omega)
    (fun {r} h hnonzero ↦ hnonzero (exteriorPower_map_eq_zero_of_min_lt (R := R) h φ))

/-- Helper for Chap10 Remark 10 102 10: adding a zero product row in standard summed
coordinates does not change whether the rank-minor ideal is the unit ideal. -/
private lemma rankMinorIdeal_prodMapInStandardCoordinates_zero_eq_top_iff [Nontrivial R]
    {m n p q : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    I(prodMapInStandardCoordinates (R := R) φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))) = ⊤ ↔
      I(φ) = ⊤ := by
  -- Proof comment: in the finite-sum coordinates, the zero factor contributes only the harmless
  -- zero block, and `simp` normalizes the corresponding rank-minor predicate.
  classical
  rw [LinearMap.rankMinorIdeal, exteriorRank_prodMapInStandardCoordinates_zero_eq]
  rw [← matrix_minorIdeal_reindex_eq (R := R) (r := LinearMap.exteriorRank φ)
    (A := LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + q)))
      (prodMapInStandardCoordinates (R := R) φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))))
    (e₁ := finSumFinEquiv.symm) (e₂ := finSumFinEquiv.symm)]
  rw [toMatrix_prodMapInStandardCoordinates]
  rw [Matrix.minorIdeal_fromBlocks]
  have hzeroMatrix :
      LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin q))
        (0 : (Fin p → R) →ₗ[R] (Fin q → R)) = 0 := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [hzeroMatrix]
  rw [matrix_minorIdeal_fromBlocks_zero_right_eq]
  simp [LinearMap.rankMinorIdeal]

/-- Helper for Chap10 Remark 10 102 10: adding a product row which is a linear equivalence in
standard summed coordinates does not change whether the rank-minor ideal is the unit ideal. -/
private lemma rankMinorIdeal_prodMapInStandardCoordinates_linearEquiv_eq_top_iff [Nontrivial R]
    {m n p q : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (e : (Fin p → R) ≃ₗ[R] (Fin q → R)) :
    I(prodMapInStandardCoordinates (R := R) φ e.toLinearMap) = ⊤ ↔ I(φ) = ⊤ := by
  -- Proof comment: invariant basis number makes the equivalence block square; the block-minor
  -- computation then identifies the shifted rank-minor ideal with the original one.
  classical
  have hpq : p = q := InvariantBasisNumber.eq_of_fin_equiv e
  cases hpq
  let F : (Fin (m + p) → R) →ₗ[R] (Fin (n + p) → R) :=
    prodMapInStandardCoordinates (R := R) φ e.toLinearMap
  let A : Matrix (Fin n) (Fin m) R :=
    LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ
  have hminor_eq_at :
      Matrix.minorIdeal (LinearMap.exteriorRank φ + p)
          (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F) =
        Matrix.minorIdeal (LinearMap.exteriorRank φ) A := by
    rw [← matrix_minorIdeal_reindex_eq (R := R) (r := LinearMap.exteriorRank φ + p)
      (A := LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F)
      (e₁ := finSumFinEquiv.symm) (e₂ := finSumFinEquiv.symm)]
    rw [toMatrix_prodMapInStandardCoordinates]
    exact matrix_minorIdeal_fromBlocks_linearEquiv_at_exteriorRank_eq (R := R) φ e
  have hminor_bot_of_gt :
      ∀ {r : ℕ}, LinearMap.exteriorRank φ + p < r →
        Matrix.minorIdeal r
          (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F) =
          ⊥ := by
    intro r hr
    rw [← matrix_minorIdeal_reindex_eq (R := R) (r := r)
      (A := LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F)
      (e₁ := finSumFinEquiv.symm) (e₂ := finSumFinEquiv.symm)]
    rw [toMatrix_prodMapInStandardCoordinates]
    rw [Matrix.minorIdeal_fromBlocks]
    apply Finset.sum_eq_zero
    intro b hb
    have hsum := Finset.mem_antidiagonal.mp hb
    by_cases hb1 : LinearMap.exteriorRank φ < b.1
    · rw [matrix_minorIdeal_eq_bot_of_exteriorRank_lt (R := R) φ hb1]
      simp
    · have hb1le : b.1 ≤ LinearMap.exteriorRank φ := Nat.le_of_not_gt hb1
      have hplt : p < b.2 := by omega
      have hcard : Fintype.card (Fin p) < b.2 := by
        simpa using hplt
      rw [matrix_minorIdeal_eq_bot_of_row_lt (R := R)
        hcard (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap)]
      simp
  have hFnonzero :
      exteriorPower.map (LinearMap.exteriorRank φ + p) F ≠ 0 := by
    intro hzero
    have hbot :=
      matrix_minorIdeal_eq_bot_of_exteriorPower_map_eq_zero (R := R) F hzero
    rw [hminor_eq_at] at hbot
    exact (matrix_minorIdeal_exteriorRank_ne_bot (R := R) φ) hbot
  have hRank : LinearMap.exteriorRank F = LinearMap.exteriorRank φ + p := by
    have hbound : LinearMap.exteriorRank φ + p ≤ min (m + p) (n + p) := by
      have hmin := LinearMap.exteriorRank_le_min φ
      omega
    have hlower : LinearMap.exteriorRank φ + p ≤ LinearMap.exteriorRank F := by
      letI : DecidablePred (fun r ↦ exteriorPower.map r F ≠ 0) := Classical.decPred _
      unfold LinearMap.exteriorRank
      exact Nat.le_findGreatest hbound hFnonzero
    have hupper : LinearMap.exteriorRank F ≤ LinearMap.exteriorRank φ + p := by
      by_contra hnot
      have hgt : LinearMap.exteriorRank φ + p < LinearMap.exteriorRank F :=
        Nat.lt_of_not_ge hnot
      have hbot := hminor_bot_of_gt hgt
      have hzero :=
        exteriorPower_map_eq_zero_of_matrix_minorIdeal_eq_bot (R := R) F hbot
      exact (exteriorPower_map_exteriorRank_ne_zero (R := R) F) hzero
    exact le_antisymm hupper hlower
  have hIdeal : I(F) = I(φ) := by
    rw [LinearMap.rankMinorIdeal, LinearMap.rankMinorIdeal, hRank]
    exact hminor_eq_at
  change I(F) = ⊤ ↔ I(φ) = ⊤
  rw [hIdeal]

/-- Helper for Chap10 Remark 10 102 10: conjugating a displayed row differential back through
the chosen finite-free term coordinates recovers the owner chain differential. -/
private lemma termIso_hom_comp_diffAt_comp_termIso_inv
    (C : _root_.FiniteFreeComplex R e) (i : Fin e) :
    (C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i) ≫
        (C.termIso i.castSucc).inv =
      C.toChainComplex.d (i.1 + 1) i.1 := by
  -- Proof comment: expand the displayed differential once, then cancel the source and target
  -- coordinate isomorphisms in the ambient chain-complex category.
  dsimp [FiniteFreeComplex.diffAt, FiniteFreeComplex.differential,
    FiniteFreeComplex.termIsoAt]
  change (C.termIso i.succ).hom ≫
      ((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
        (C.termIso i.castSucc).hom) ≫
      (C.termIso i.castSucc).inv =
    C.toChainComplex.d (i.1 + 1) i.1
  simp [Category.assoc]

/-- Helper for Chap10 Remark 10 102 10: conjugating a row of a chain complex through an
isomorphism to a biproduct and then through `biprodXIso` gives the biproduct row map. -/
private lemma chainIsoBiprodXItoRow_eq_biprodMap
    {M K L : ChainComplex (ModuleCat R) ℕ}
    (eiso : M ≅ biprod K L) (j : ℕ) :
    (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
        eiso.inv.f (j + 1) ≫ M.d (j + 1) j ≫ eiso.hom.f j ≫
        (HomologicalComplex.biprodXIso K L j).hom =
      biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
  -- Proof comment: first move the row across the chain isomorphism, then cancel the source
  -- `biprodXIso` against the biproduct differential normal form.
  calc
    (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
        eiso.inv.f (j + 1) ≫ M.d (j + 1) j ≫ eiso.hom.f j ≫
        (HomologicalComplex.biprodXIso K L j).hom =
      (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
        ((biprod K L).d (j + 1) j ≫
          (HomologicalComplex.biprodXIso K L j).hom) := by
        simpa [Category.assoc] using congrArg
          (fun f ↦ (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫ f ≫
            (HomologicalComplex.biprodXIso K L j).hom)
          (chainIso_inv_d_hom (R := R) eiso j)
    _ =
      (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
        ((HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j)) := by
        rw [biprodXIso_differential_hom (R := R) (K := K) (L := L) j]
    _ = biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
        simp [Category.assoc]

/-- Helper for Chap10 Remark 10 102 10: before reindexing product coordinates as a summed
finite free module, the split-model row is the product of the two summand rows. -/
private lemma splitRow_conj_eq_prodMap
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i))
    (k : Fin e) :
    (splitRowTargetEquiv (R := R) (D := D) (D' := D') (i := i) eiso k).toLinearMap.comp
      ((D.diffAt k).comp
        (splitRowSourceEquiv (R := R) (D := D) (D' := D') (i := i) eiso k).symm.toLinearMap) =
    (D'.diffAt k).prodMap (identityDiskRowInCoordinates (R := R) i k) := by
  -- Proof comment: the source and target row equivalences are built from the chain isomorphism,
  -- the biproduct comparison, and the term-coordinate isomorphisms; comparing the two product
  -- projections reduces the row to the chain-map identity for `eiso`.
  apply LinearMap.ext
  intro x
  let xb :
      ↑(biprod (D'.toChainComplex.X (k.1 + 1))
        ((FiniteFreeComplex.identityDiskComplex (R := R) i).X (k.1 + 1))) :=
    ((ModuleCat.biprodIsoProd (D'.toChainComplex.X (k.1 + 1))
      ((FiniteFreeComplex.identityDiskComplex (R := R) i).X (k.1 + 1))).inv.hom)
      (((LinearEquiv.prodCongr (D'.termIso k.succ).toLinearEquiv
        (identityDiskTermEquiv (R := R) i (k.1 + 1))).symm) x)
  have hrowx :=
    congrArg
        (fun f :
          biprod (D'.toChainComplex.X (k.1 + 1))
              ((FiniteFreeComplex.identityDiskComplex (R := R) i).X (k.1 + 1)) ⟶
            biprod (D'.toChainComplex.X k.1)
              ((FiniteFreeComplex.identityDiskComplex (R := R) i).X k.1) ↦
        (((ModuleCat.biprodIsoProd (D'.toChainComplex.X k.1)
          ((FiniteFreeComplex.identityDiskComplex (R := R) i).X k.1)).hom.hom)
          (f.hom xb)))
      (chainIsoBiprodXItoRow_eq_biprodMap (R := R) (eiso := eiso) k.1)
  have hpair :=
    congrArg
      (fun y ↦
        (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
          (identityDiskTermEquiv (R := R) i k.1)) y)
      hrowx
  rw [← termIso_hom_comp_diffAt_comp_termIso_inv (R := R) (C := D) k] at hpair
  have hprod :
      (fun y ↦
        (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
          (identityDiskTermEquiv (R := R) i k.1)) y)
      ((fun f ↦
          ((ModuleCat.biprodIsoProd (D'.toChainComplex.X k.1)
            ((FiniteFreeComplex.identityDiskComplex (R := R) i).X k.1)).hom.hom)
            ((ModuleCat.Hom.hom f) xb))
        (biprod.map (D'.toChainComplex.d (k.1 + 1) k.1)
          ((FiniteFreeComplex.identityDiskComplex (R := R) i).d (k.1 + 1) k.1))) =
        ((D'.diffAt k).prodMap (identityDiskRowInCoordinates (R := R) i k)) x := by
    -- Proof comment: the right-hand biproduct row is the product of the two row maps after the
    -- source and target biproducts are identified with products.
    have hmap :=
      biprod_map_biprodIsoProd_apply (R := R)
        (D'.toChainComplex.d (k.1 + 1) k.1)
        ((FiniteFreeComplex.identityDiskComplex (R := R) i).d (k.1 + 1) k.1)
        (((LinearEquiv.prodCongr (D'.termIso k.succ).toLinearEquiv
          (identityDiskTermEquiv (R := R) i (k.1 + 1))).symm) x)
    exact congrArg
      (fun y ↦
        (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
          (identityDiskTermEquiv (R := R) i k.1)) y)
      hmap
  rw [hprod] at hpair
  exact hpair

/-- Helper for Chap10 Remark 10 102 10: the split-model row of `D` is the product row of the
reduced complex and the identity disk after passing to summed finite coordinates. -/
private lemma splitRow_conj_eq_prodMapInStandardCoordinates
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i))
    (k : Fin e) :
    (standard_module_sum_linearEquiv (R := R) (D'.rank k.castSucc)
        (FiniteFreeComplex.identityDiskRank i k.1)).toLinearMap.comp
      ((splitRowTargetEquiv (R := R) (D := D) (D' := D') (i := i) eiso k).toLinearMap.comp
        ((D.diffAt k).comp
          ((splitRowSourceEquiv (R := R) (D := D) (D' := D') (i := i) eiso k).symm.toLinearMap.comp
            (standard_module_sum_linearEquiv (R := R) (D'.rank k.succ)
              (FiniteFreeComplex.identityDiskRank i (k.1 + 1))).symm.toLinearMap))) =
    prodMapInStandardCoordinates (R := R) (D'.diffAt k)
      (identityDiskRowInCoordinates (R := R) i k) := by
  -- Proof comment: after the product-level split row is known, the summed-coordinate statement is
  -- just pre- and postcomposition by the fixed finite-sum coordinate equivalences.
  apply LinearMap.ext
  intro x
  have h :=
    congrArg
      (fun f ↦
        (standard_module_sum_linearEquiv (R := R) (D'.rank k.castSucc)
          (FiniteFreeComplex.identityDiskRank i k.1)).toLinearMap.comp
          (f.comp (standard_module_sum_linearEquiv (R := R) (D'.rank k.succ)
            (FiniteFreeComplex.identityDiskRank i (k.1 + 1))).symm.toLinearMap))
      (splitRow_conj_eq_prodMap (R := R) (D := D) (D' := D') (i := i) eiso k)
  exact LinearMap.congr_fun h x

/-- Chap10 Remark 10 102 10: after rewriting the split model
`D.toChainComplex ≅ biprod D'.toChainComplex (identityDiskComplex i)` rowwise, the predicate
`I(D.diffAt k) = ⊤` agrees with `I(D'.diffAt k) = ⊤` in every degree. -/
-- TODO: conjugate `D.diffAt k` through `eiso`, normalize the split row with
-- `biprodXIso_differential_hom` and `biprod_map_comp_biprodIsoProd_hom`, then finish the four
-- degree cases using the zero-target, identity-block, zero-source, and off-support block
-- invariance lemmas for `rankMinorIdeal = ⊤`.
private lemma split_model_row_rankMinorIdeal_eq_top_iff
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (_hsplit : D'.rank = FiniteFreeComplex.splitRank D.rank i)
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    ∀ k : Fin e, I(D.diffAt k) = ⊤ ↔ I(D'.diffAt k) = ⊤ := by
  by_cases hsubR : Subsingleton R
  · letI : Subsingleton R := hsubR
    intro k
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      exact Subsingleton.elim _ _
  · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hsubR
    intro k
    let sourceEquiv :
        (Fin (D'.rank k.succ + FiniteFreeComplex.identityDiskRank i (k.1 + 1)) → R) ≃ₗ[R]
          (Fin (D.rank k.succ) → R) :=
      (standard_module_sum_linearEquiv (R := R) (D'.rank k.succ)
        (FiniteFreeComplex.identityDiskRank i (k.1 + 1))).symm.trans
        (splitRowSourceEquiv (R := R) (D := D) (D' := D') (i := i) eiso k).symm
    let targetEquiv :
        (Fin (D.rank k.castSucc) → R) ≃ₗ[R]
          (Fin (D'.rank k.castSucc + FiniteFreeComplex.identityDiskRank i k.1) → R) :=
      (splitRowTargetEquiv (R := R) (D := D) (D' := D') (i := i) eiso k).trans
        (standard_module_sum_linearEquiv (R := R) (D'.rank k.castSucc)
          (FiniteFreeComplex.identityDiskRank i k.1))
    have htransport :
        I(prodMapInStandardCoordinates (R := R) (D'.diffAt k)
            (identityDiskRowInCoordinates (R := R) i k)) = ⊤ ↔
          I(D.diffAt k) = ⊤ := by
      have hconj :=
        rankMinorIdeal_eq_top_iff_of_linearEquiv_conj' (R := R) (φ := D.diffAt k)
          sourceEquiv targetEquiv
      rw [← splitRow_conj_eq_prodMapInStandardCoordinates (R := R) (D := D) (D' := D')
        (i := i) eiso k]
      simpa [sourceEquiv, targetEquiv, LinearMap.comp_assoc] using hconj
    -- Proof comment: after transport, it remains only to remove the identity-disk row from the
    -- product row in finite coordinates.
    have hproduct :
        I(prodMapInStandardCoordinates (R := R) (D'.diffAt k)
            (identityDiskRowInCoordinates (R := R) i k)) = ⊤ ↔
          I(D'.diffAt k) = ⊤ := by
      by_cases hk : k = i
      · subst k
        rw [identityDiskRowInCoordinates_eq_id]
        exact rankMinorIdeal_prodMapInStandardCoordinates_linearEquiv_eq_top_iff
          (R := R) (D'.diffAt i) (identityDiskSupportedEquiv (R := R) i)
      · have hkval : k.1 ≠ i.1 := fun h ↦ hk (Fin.ext h)
        rw [identityDiskRowInCoordinates_eq_zero_of_ne (R := R) (i := i) (k := k) hkval]
        exact rankMinorIdeal_prodMapInStandardCoordinates_zero_eq_top_iff
          (R := R) (D'.diffAt k)
    exact htransport.symm.trans hproduct

/-- Helper for Remark 10.102.10: once the unit-entry split has been normalized degreewise, the
threshold witness on the reduced complex transports back to the original complex. -/
private lemma hasThreshold_of_unit_entry_split
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (hsplit : D'.rank = FiniteFreeComplex.splitRank D.rank i)
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i))
    (hthreshold' : HasThreshold (R := R) D') :
    HasThreshold (R := R) D := by
  -- Route correction: the split transport is reduced to the single rowwise comparison lemma
  -- above, after which the threshold witness is pushed back verbatim.
  exact hasThreshold_of_rankMinorIdeal_eq_top_iff (R := R) (C := D') (D := D)
    (fun k ↦ (split_model_row_rankMinorIdeal_eq_top_iff (R := R) (D := D) (D' := D') (i := i)
      hsplit eiso k).symm)
    hthreshold'

/- Domain triage:
* primary domain: Buchsbaum-Eisenbud exactness criteria for bounded finite free complexes over a
  Noetherian local ring, with the threshold behavior of the rank-minor ideals `I(C.diffAt i)`;
* sampled owner declarations of the same kind:
  `FiniteFreeComplex.ExactInPositiveDegrees`,
  `FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_criterion`,
  `FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion`, and
  `Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth`;
* best owner abstraction: `ExactInPositiveDegrees` is the source-facing owner hypothesis, while
  `Ideal.depth` is the core/canonical owner controlling when a proper rank-minor ideal can no
  longer support the required regular sequences;
* layer: this remark remains `source-facing`, because the threshold conclusion is additional
  mathematical content, not just a restatement of the depth owner.

Primitive data are only the bounded finite free complex `C`, its displayed differentials
`C.diffAt i`, and the exactness owner `C.ExactInPositiveDegrees`. The depth inequalities for the
ideals `I(C.diffAt i)` are derived bridge API coming from Proposition `10.102.9`.
-/

-- Proof sketch: apply Proposition `10.102.9` to convert exactness into the Buchsbaum--Eisenbud
-- criterion. If some `I(C.diffAt j)` is not the unit ideal for arbitrarily large `j`, the
-- criterion gives arbitrarily long regular sequences contained in a proper ideal of the Noetherian
-- local ring, which is impossible. Conversely, once `I(C.diffAt j) = ⊤`, the tail complex ending
-- in `C.diffAt j = 0` forces every later minor ideal to be the unit ideal as in the remark.
/-- Consequence of Chap10 Remark 10 102 10: if the equivalent conditions of Proposition `10.102.9` hold for a bounded
finite free complex, then there is a threshold `j` such that the rank-minor ideal `I(C.diffAt i)`
is the unit ideal exactly for the differentials with index `i ≥ j`. -/
@[stacks 0GLM]
theorem rankMinorIdeal_eq_top_iff_ge_threshold
    (C : _root_.FiniteFreeComplex R e)
    (hExact : C.ExactInPositiveDegrees) :
    ∃ j : Fin (e + 1),
      ∀ i : Fin e,
        I(C.diffAt i) = ⊤ ↔ j ≤ i.castSucc := by
  classical
  by_cases hsubR : Subsingleton R
  · letI : Subsingleton R := hsubR
    refine ⟨0, ?_⟩
    intro i
    have hzero : C.diffAt i = 0 := Subsingleton.elim _ _
    constructor
    · intro _
      exact Fin.zero_le _
    · intro _
      rw [hzero]
      exact rankMinorIdeal_zero_eq_top (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)
  · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hsubR
    -- Route correction: thread exactness through the induction predicate so the reduced complex
    -- in the unit-entry branch remains inside the induction hypothesis.
    let P : ℕ → Prop := fun n ↦
      ∀ D : _root_.FiniteFreeComplex R e,
        positiveRankSum (R := R) D = n → D.ExactInPositiveDegrees → HasThreshold (R := R) D
    have hP : ∀ n : ℕ, P n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro D hsum hExactD
          by_cases hunit :
              ∃ i : Fin e, ∃ a : Fin (D.rank i.succ), ∃ b : Fin (D.rank i.castSucc),
                IsUnit (D.diffEntry i a b)
          · obtain ⟨i, a, b, hu⟩ := hunit
            obtain ⟨D', hsplit, ⟨eiso⟩⟩ :=
              FiniteFreeComplex.exists_iso_biprod_identityDisk_of_isUnit_diffEntry
                (C := D) (i := i) ⟨a, b, hu⟩
            have hlt :
                positiveRankSum (R := R) D' < positiveRankSum (R := R) D :=
              positiveRankSum_splitRank_lt_of_unit_entry (R := R) (C := D) (C' := D')
                (i := i) ⟨a, b, hu⟩ hsplit
            have hlt' : positiveRankSum (R := R) D' < n := by
              simpa [hsum] using hlt
            have hExactD' : D'.ExactInPositiveDegrees :=
              exactInPositiveDegrees_of_biprod_identityDisk (R := R) (C := D) (C' := D')
                (i := i) eiso hExactD
            have hthreshold' : HasThreshold (R := R) D' :=
              ih _ hlt' D' rfl hExactD'
            -- Proof comment: after shrinking to the reduced complex, only the split-transport
            -- step remains; its degreewise comparison is now isolated in one helper.
            exact hasThreshold_of_unit_entry_split (R := R) (D := D) (D' := D') (i := i)
              hsplit eiso hthreshold'
          · have hmax :
                ∀ i : Fin e, ∀ a : Fin (D.rank i.succ), ∀ b : Fin (D.rank i.castSucc),
                  D.diffEntry i a b ∈ IsLocalRing.maximalIdeal R := by
              intro i a b
              exact diffEntry_mem_maximal_of_no_unit (R := R) (C := D) hunit i a b
            let s : Finset (Fin e) := Finset.univ.filter fun i ↦ D.diffAt i = 0
            by_cases hs : s.Nonempty
            · let j0 : Fin e := s.min' hs
              refine ⟨j0.castSucc, ?_⟩
              intro k
              have htop_zero :
                  I(D.diffAt k) = ⊤ ↔ D.diffAt k = 0 :=
                rankMinorIdeal_eq_top_iff_eq_zero_of_entries_mem_maximal (R := R) (C := D)
                  (i := k) (hmax k)
              constructor
              · intro hk0
                have hkZero : D.diffAt k = 0 := htop_zero.mp hk0
                have hk_mem : k ∈ s := by
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
                  simpa [FiniteFreeComplex.diffAt, FiniteFreeComplex.differential] using hkZero
                exact Finset.min'_le s k hk_mem
              · intro hjk
                have hj0_mem : j0 ∈ s := Finset.min'_mem s hs
                have hj0_zero : D.diffAt j0 = 0 := by
                  simpa [s] using (Finset.mem_filter.mp hj0_mem).2
                exact htop_zero.mpr <|
                  diffAt_eq_zero_propagates_tail_zero_of_entries_mem_maximal (R := R)
                    (C := D) hExactD hmax hj0_zero hjk
            · refine ⟨Fin.last e, ?_⟩
              intro k
              have htop_zero :
                  I(D.diffAt k) = ⊤ ↔ D.diffAt k = 0 :=
                rankMinorIdeal_eq_top_iff_eq_zero_of_entries_mem_maximal (R := R) (C := D)
                  (i := k) (hmax k)
              constructor
              · intro hk0
                have hkZero : D.diffAt k = 0 := htop_zero.mp hk0
                have hk_mem : k ∈ s := by
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
                  simpa [FiniteFreeComplex.diffAt, FiniteFreeComplex.differential] using hkZero
                exact (hs ⟨k, hk_mem⟩).elim
              · intro hlast
                exfalso
                have hklt : k.castSucc.1 < (Fin.last e : Fin (e + 1)).1 := by
                  simpa using k.isLt
                exact (not_le_of_gt hklt) hlast
    simpa [HasThreshold] using hP (positiveRankSum (R := R) C) C rfl hExact

end FiniteFreeComplex

end
