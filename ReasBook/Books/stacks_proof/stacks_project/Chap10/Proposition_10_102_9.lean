import StacksProject_2024.Chap10.Lemma_10_72_2
import StacksProject_2024.Chap10.Lemma_10_102_2
import StacksProject_2024.Chap10.Definition_10_102_5
import StacksProject_2024.Chap10.Proposition_10_102_9.Index
import StacksProject_2024.Chap10.Situation_10_102_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open RingTheory Set

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

/- Domain triage:
* primary domain: Buchsbaum-Eisenbud acyclicity criteria in local commutative algebra, where the
  minor ideals are controlled by regular sequences and equivalently by depth;
* sampled owner declarations of the same kind: `Ideal.depth`,
  `Ideal.depth_eq_sSup_lengths_of_isWeaklyRegular`,
  `Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth`, and `moduleDepth`;
* best owner abstraction: `Ideal.depth` is the core/canonical owner for the ideal-theoretic lower
  bound, while Proposition `10.102.9` itself is `source-facing` and should keep the textbook
  regular-sequence clause as its main public statement;
* layer: the depth inequality is only the `bridge/view` reformulation of the source-facing
  Buchsbaum-Eisenbud criterion.
* primitive vs derived split: the primitive data are the complex, its differentials, and the
  rank-minor ideals `I(C.diffAt i)`; the owner depth inequalities are derived bridge API for those
  source-facing regular-sequence conditions.
-/

namespace FiniteFreeComplex

/-- A bounded finite free complex is exact in the positive degrees `e, …, 1` when its underlying
chain complex is exact at every degree `1, …, e`. -/
def ExactInPositiveDegrees (C : _root_.FiniteFreeComplex R e) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j

/-- Source-facing ideal clause in Proposition `10.102.9`: `I` contains a regular sequence of the
prescribed length. -/
inductive ContainsRegularSequenceOfLength (I : Ideal R) (n : ℕ) : Prop where
  | mk (rs : List R) (isRegular : RingTheory.Sequence.IsRegular R rs)
      (subset : Ideal.ofList rs ≤ I) (length_eq : rs.length = n) :
      ContainsRegularSequenceOfLength I n

/-- Helper for Chap10 Proposition 10 102 9: the source-facing regular-sequence clause is exactly
the owner depth inequality from Lemma `10.72.2`. -/
private theorem criterionClause_iff_le_depth (I : Ideal R) (n : ℕ) :
    (I = ⊤ ∨ ContainsRegularSequenceOfLength I n) ↔
      (n : WithTop ℕ) ≤ I.depth R := by
  constructor
  · intro h
    rcases h with htop | hseq
    · -- Proof comment: the source clause reduces directly to the owner theorem in the unit-ideal
      -- branch.
      exact
        (Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth I n).mp
          (Or.inl htop)
    · rcases hseq with ⟨rs, hreg, hsubset, hlen⟩
      -- Proof comment: unwrap the source-facing packaging and pass the resulting sequence to the
      -- owner depth characterization.
      exact
        (Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth I n).mp
          (Or.inr ⟨rs, hreg, hsubset, hlen⟩)
  · intro h
    rcases
        (Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth I n).mpr h with
      htop | hseq
    · -- Proof comment: the unit-ideal branch is already in the source-facing shape.
      exact Or.inl htop
    · rcases hseq with ⟨rs, hreg, hsubset, hlen⟩
      -- Proof comment: repack the owner-side regular sequence witness into the local wrapper used
      -- by Proposition `10.102.9`.
      exact Or.inr <| ContainsRegularSequenceOfLength.mk rs hreg hsubset hlen

/-- Helper for Chap10 Proposition 10 102 9: the total rank of the positive-degree terms of a
bounded finite free complex. -/
private def positiveRankSum (C : _root_.FiniteFreeComplex R e) : ℕ :=
  ∑ j : Fin e, C.rank j.succ

/-- Helper for Chap10 Proposition 10 102 9: the owner-facing Buchsbaum-Eisenbud depth criterion
attached to a bounded finite free complex. -/
private def SatisfiesRankMinorIdealDepthCriterion
    (C : _root_.FiniteFreeComplex R e) : Prop :=
  ∀ i : Fin e,
    (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
      (i.1 + 1 : WithTop ℕ) ≤ (I(C.diffAt i)).depth R

/-- Helper for Chap10 Proposition 10 102 9: splitting off an `identityDiskComplex` along a unit
entry strictly decreases the total positive-degree rank. -/
private lemma positiveRankSum_splitRank_lt_of_unit_entry
    (C C' : _root_.FiniteFreeComplex R e) (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
        IsUnit (C.diffEntry i a b))
    (hsplit : C'.rank = FiniteFreeComplex.splitRank C.rank i) :
    positiveRankSum C' < positiveRankSum C := by
  obtain ⟨a, b, _⟩ := hunit
  have hi_pos : 0 < C.rank i.succ := by
    -- Proof comment: the chosen row index witnesses that the source rank in degree `i + 1` is
    -- positive.
    exact lt_of_le_of_lt (Nat.zero_le a.1) a.2
  -- Proof comment: the split rank agrees away from degree `i + 1`, and drops by one there.
  refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [hsplit, FiniteFreeComplex.splitRank]
    by_cases hji : j = i
    · subst hji
      simp
    · by_cases hcast : j.succ = i.castSucc
      · simp [hji, hcast]
      · simp [hji, hcast]
  · have hpred : C.rank i.succ - 1 < C.rank i.succ := by
      -- Proof comment: the split removes exactly one basis vector from degree `i + 1`.
      simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hi_pos)
    simpa [hsplit, FiniteFreeComplex.splitRank] using hpred

/-- Helper for Chap10 Proposition 10 102 9: if no differential entry is a unit, then every
displayed matrix entry lies in the maximal ideal. -/
private lemma diffEntry_mem_maximal_of_no_unit
    (C : _root_.FiniteFreeComplex R e)
    (hnoUnit :
      ¬ ∃ i : Fin e, ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
          IsUnit (C.diffEntry i a b))
    (i : Fin e) (a : Fin (C.rank i.succ)) (b : Fin (C.rank i.castSucc)) :
    C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R := by
  -- Proof comment: over a local ring, being outside the maximal ideal is equivalent to being a
  -- unit, so the no-unit hypothesis forces every displayed entry into the maximal ideal.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  exact hnoUnit ⟨i, a, b, hunit⟩

/-- Helper for Chap10 Proposition 10 102 9: a zero map followed by an injective map is exact. -/
private lemma functionExact_zero_of_injective
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] P) (hf : Function.Injective f) :
    Function.Exact (0 : M →ₗ[R] N) f := by
  intro x
  constructor
  · intro hx
    have hx0 : x = 0 := hf (by simpa using hx)
    refine ⟨0, ?_⟩
    simpa [hx0]
  · rintro ⟨y, rfl⟩
    simp

/-- Helper for Chap10 Proposition 10 102 9: a surjective map followed by zero is exact. -/
private lemma functionExact_surjective_zero
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Exact f (0 : N →ₗ[R] P) := by
  intro x
  constructor
  · intro _
    exact hf x
  · rintro ⟨y, rfl⟩
    simp

/-- Helper for Chap10 Proposition 10 102 9: if the middle term is zero, the row is exact. -/
private lemma functionExact_of_subsingleton_middle
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Subsingleton N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    Function.Exact f g := by
  intro x
  constructor
  · intro _
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  · rintro ⟨y, rfl⟩
    have hy0 : f y = 0 := Subsingleton.elim _ _
    simpa [hy0]

/-- Helper for Chap10 Proposition 10 102 9: products of exact rows remain exact. -/
private lemma functionExact_prodMap
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (f₁ : M₁ →ₗ[R] M₂) (g₁ : M₂ →ₗ[R] M₃)
    (f₂ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃)
    (hf : Function.Exact f₁ g₁) (hg : Function.Exact f₂ g₂) :
    Function.Exact (f₁.prodMap f₂) (g₁.prodMap g₂) := by
  intro x
  constructor
  · intro hx
    -- Proof comment: exactness of each component row supplies the two preimages.
    have hx₁ : g₁ x.1 = 0 := by
      simpa [LinearMap.prodMap_apply] using congrArg Prod.fst hx
    have hx₂ : g₂ x.2 = 0 := by
      simpa [LinearMap.prodMap_apply] using congrArg Prod.snd hx
    obtain ⟨y₁, hy₁⟩ := (hf x.1).1 hx₁
    obtain ⟨y₂, hy₂⟩ := (hg x.2).1 hx₂
    refine ⟨(y₁, y₂), ?_⟩
    ext
    · simp [LinearMap.prodMap_apply, hy₁]
    · simp [LinearMap.prodMap_apply, hy₂]
  · rintro ⟨y, rfl⟩
    -- Proof comment: composition vanishes componentwise because each source row is exact.
    have hf_zero : g₁.comp f₁ = 0 := hf.linearMap_comp_eq_zero
    have hg_zero : g₂.comp f₂ = 0 := hg.linearMap_comp_eq_zero
    ext
    · simpa [LinearMap.comp_apply] using LinearMap.congr_fun hf_zero y.1
    · simpa [LinearMap.comp_apply] using LinearMap.congr_fun hg_zero y.2

/-- Helper for Chap10 Proposition 10 102 9: objectwise biproduct comparison turns the differential
of a biproduct complex into the biproduct map of the two summand differentials. -/
private lemma biprodXIso_differential_hom_local
    {K L : ChainComplex (ModuleCat R) ℕ} (j : ℕ) :
    ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom =
      (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
        biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
  -- Proof comment: compare the two differentials after projecting to each explicit summand.
  apply biprod.hom_ext
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.fst =
        ((biprod K L).d (j + 1) j) ≫ (biprod.fst : biprod K L ⟶ K).f j := by
          rw [HomologicalComplex.biprodXIso_hom_fst]
      _ = (biprod.fst : biprod K L ⟶ K).f (j + 1) ≫ K.d (j + 1) j := by
          simpa [Category.assoc] using
            ((biprod.fst : biprod K L ⟶ K).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫ biprod.fst ≫ K.d (j + 1) j := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ m ≫ K.d (j + 1) j)
              (HomologicalComplex.biprodXIso_hom_fst K L (j + 1)).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.fst := by
          simp
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.snd =
        ((biprod K L).d (j + 1) j) ≫ (biprod.snd : biprod K L ⟶ L).f j := by
          rw [HomologicalComplex.biprodXIso_hom_snd]
      _ = (biprod.snd : biprod K L ⟶ L).f (j + 1) ≫ L.d (j + 1) j := by
          simpa [Category.assoc] using
            ((biprod.snd : biprod K L ⟶ L).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫ biprod.snd ≫ L.d (j + 1) j := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ m ≫ L.d (j + 1) j)
              (HomologicalComplex.biprodXIso_hom_snd K L (j + 1)).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.snd := by
          simp

/-- Helper for Chap10 Proposition 10 102 9: conjugating a differential by a chain-complex
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

/-- Helper for Chap10 Proposition 10 102 9: after the objectwise biproduct comparison, the
categorical biproduct map becomes the explicit product row. -/
private lemma biprod_map_comp_biprodIsoProd_hom
    {M₁ M₂ N₁ N₂ : ModuleCat R} (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) :
    biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom =
      (ModuleCat.biprodIsoProd M₁ M₂).hom ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
  -- Proof comment: check after the two ordinary product projections.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · have hleft := congrArg (fun k : M₁ ⊞ M₂ ⟶ N₁ ↦ k.hom x)
      (by
        calc
          biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom ≫
              ModuleCat.ofHom (LinearMap.fst R N₁ N₂) =
            biprod.map f g ≫ biprod.fst := by
              rw [biprodIsoProd_hom_comp_fst]
          _ = biprod.fst ≫ f := by
              rw [biprod.map_fst])
    have hright := congrArg (fun k : M₁ ⊞ M₂ ⟶ M₁ ↦ k.hom x)
      (biprodIsoProd_hom_comp_fst M₁ M₂)
    simpa [LinearMap.prodMap_apply] using hleft.trans (congrArg f.hom hright).symm
  · have hleft := congrArg (fun k : M₁ ⊞ M₂ ⟶ N₂ ↦ k.hom x)
      (by
        calc
          biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom ≫
              ModuleCat.ofHom (LinearMap.snd R N₁ N₂) =
            biprod.map f g ≫ biprod.snd := by
              rw [biprodIsoProd_hom_comp_snd]
          _ = biprod.snd ≫ g := by
              rw [biprod.map_snd])
    have hright := congrArg (fun k : M₁ ⊞ M₂ ⟶ M₂ ↦ k.hom x)
      (biprodIsoProd_hom_comp_snd M₁ M₂)
    simpa [LinearMap.prodMap_apply] using hleft.trans (congrArg g.hom hright).symm

/-- Helper for Chap10 Proposition 10 102 9: under the product model of source and target
biproducts, `biprod.map f g` applies as the product linear map. -/
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
    biprod_map_comp_biprodIsoProd_hom f g
  have happ :=
    congrArg
      (fun h : biprod M₁ M₂ ⟶ ModuleCat.of R (N₁ × N₂) ↦
        (ModuleCat.Hom.hom h) ((ModuleCat.biprodIsoProd M₁ M₂).inv.hom x))
      hcat
  simpa [LinearMap.comp_apply, LinearMap.prodMap_apply] using happ

/-- Helper for Chap10 Proposition 10 102 9: exactness of two module rows remains exact after
forming the categorical biproduct row. -/
private lemma functionExact_biprodMap
    {A₁ A₂ A₃ B₁ B₂ B₃ : ModuleCat R}
    (f₁ : A₁ ⟶ A₂) (g₁ : A₂ ⟶ A₃)
    (f₂ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃)
    (hf : Function.Exact f₁.hom g₁.hom) (hg : Function.Exact f₂.hom g₂.hom) :
    Function.Exact (biprod.map f₁ f₂).hom (biprod.map g₁ g₂).hom := by
  have hprod : Function.Exact (f₁.hom.prodMap f₂.hom) (g₁.hom.prodMap g₂.hom) :=
    functionExact_prodMap f₁.hom g₁.hom f₂.hom g₂.hom hf hg
  -- Proof comment: transport exactness through the explicit product model of each biproduct
  -- object.
  have h₁₂ :
      (f₁.hom.prodMap f₂.hom).comp (ModuleCat.biprodIsoProd A₁ B₁).toLinearEquiv.toLinearMap =
        (ModuleCat.biprodIsoProd A₂ B₂).toLinearEquiv.toLinearMap.comp (biprod.map f₁ f₂).hom := by
    ext x
    · have h := congrArg (fun k : A₁ ⊞ B₁ ⟶ ModuleCat.of R (A₂ × B₂) ↦ k.hom x)
        (biprod_map_comp_biprodIsoProd_hom f₁ f₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.fst h
    · have h := congrArg (fun k : A₁ ⊞ B₁ ⟶ ModuleCat.of R (A₂ × B₂) ↦ k.hom x)
        (biprod_map_comp_biprodIsoProd_hom f₁ f₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.snd h
  have h₂₃ :
      (g₁.hom.prodMap g₂.hom).comp (ModuleCat.biprodIsoProd A₂ B₂).toLinearEquiv.toLinearMap =
        (ModuleCat.biprodIsoProd A₃ B₃).toLinearEquiv.toLinearMap.comp (biprod.map g₁ g₂).hom := by
    ext x
    · have h := congrArg (fun k : A₂ ⊞ B₂ ⟶ ModuleCat.of R (A₃ × B₃) ↦ k.hom x)
        (biprod_map_comp_biprodIsoProd_hom g₁ g₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.fst h
    · have h := congrArg (fun k : A₂ ⊞ B₂ ⟶ ModuleCat.of R (A₃ × B₃) ↦ k.hom x)
        (biprod_map_comp_biprodIsoProd_hom g₁ g₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.snd h
  exact (Function.Exact.iff_of_ladder_linearEquiv h₁₂ h₂₃).1 hprod

/-- Helper for Chap10 Proposition 10 102 9: the two supported terms of the identity disk are the
same rank-one free module. -/
private lemma exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  have hsucc : k + 1 + 1 = k + 2 := by
    omega
  have hpred : k + 1 - 1 = k := by
    omega
  -- Proof comment: rewrite the exactness window to the explicit short complex in degrees
  -- `k + 2 → k + 1 → k`, then use the module-category exactness bridge.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  simpa [HomologicalComplex.sc'] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc' (k + 2) (k + 1) k))

/-- Helper for Chap10 Proposition 10 102 9: the two supported terms of the identity disk are the
same rank-one free module. -/
private abbrev identityDisk (i : Fin e) : ChainComplex (ModuleCat R) ℕ :=
  @FiniteFreeComplex.identityDiskComplex R (by infer_instance) e i

/-- Helper for Chap10 Proposition 10 102 9: the two supported terms of the identity disk are the
same rank-one free module. -/
private lemma identityDiskComplex_supported_terms_eq (i : Fin e) :
    ((identityDisk i : ChainComplex (ModuleCat R) ℕ)).X (i.1 + 1) =
      ((identityDisk i : ChainComplex (ModuleCat R) ℕ)).X i.1 := by
  -- Proof comment: both supported objects are the same rank-one standard free module.
  rw [FiniteFreeComplex.identityDiskComplex_X_eq_succ (R := R) (e := e) i,
    FiniteFreeComplex.identityDiskComplex_X_eq_castSucc (R := R) (e := e) i]

/-- Helper for Chap10 Proposition 10 102 9: on its supported degree, the identity-disk
differential is the identity after the canonical term identification. -/
private lemma identityDiskComplex_d_eq_id (i : Fin e) :
    ((identityDisk i : ChainComplex (ModuleCat R) ℕ)).d (i.1 + 1) i.1 =
      eqToHom (identityDiskComplex_supported_terms_eq i) := by
  -- Proof comment: cancel the source transport in the imported supported-row formula, then
  -- compose the two supported object identifications into a single `eqToHom`.
  have hrow :=
    FiniteFreeComplex.identityDiskComplex_eqToHom_symm_comp_d (R := R) (e := e) i
  calc
    ((identityDisk i : ChainComplex (ModuleCat R) ℕ)).d (i.1 + 1) i.1 =
        eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_succ (R := R) (e := e) i) ≫
          eqToHom (FiniteFreeComplex.identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm := by
          rw [← hrow]
          simp [Category.assoc]
    _ = eqToHom (identityDiskComplex_supported_terms_eq i) := by
          simp [CategoryTheory.eqToHom_trans]

/-- Helper for Chap10 Proposition 10 102 9: every positive row of the identity-disk complex is
exact. -/
private lemma exactAt_identityDiskComplex
    {i : Fin e} {j : ℕ}
    (hj : 1 ≤ j) :
    ((identityDisk i : ChainComplex (ModuleCat R) ℕ)).ExactAt j := by
  rw [exactAt_iff_function_exact (K := identityDisk i) hj]
  by_cases hji : j = i.1
  · subst hji
    have hzero : i.1 - 1 ≠ i.1 := by
      omega
    rw [identityDiskComplex_d_eq_id (R := R) (e := e) i]
    rw [FiniteFreeComplex.identityDiskComplex_d_eq_zero_of_ne (R := R) (i := i) hzero]
    -- Proof comment: at the supported target degree, the incoming differential is an
    -- isomorphism and the outgoing differential vanishes.
    refine functionExact_surjective_zero _ ?_
    intro x
    refine ⟨(eqToHom (identityDiskComplex_supported_terms_eq (R := R) (e := e) i).symm).hom x, ?_⟩
    simp
  · by_cases hjSucc : j = i.1 + 1
    · subst hjSucc
      have hzero : i.1 + 1 ≠ i.1 := by
        omega
      rw [FiniteFreeComplex.identityDiskComplex_d_eq_zero_of_ne (R := R) (i := i) hzero]
      rw [show i.1 + 1 - 1 = i.1 by omega]
      rw [identityDiskComplex_d_eq_id (R := R) (e := e) i]
      -- Proof comment: one degree above the support, the outgoing differential is an
      -- isomorphism and the incoming one is zero.
      refine functionExact_zero_of_injective _ ?_
      intro x y hxy
      have hxy' := congrArg (fun z ↦
        (eqToHom (identityDiskComplex_supported_terms_eq (R := R) (e := e) i).symm).hom z) hxy
      simpa using hxy'
    · have hzero :
          IsZero (((identityDisk i : ChainComplex (ModuleCat R) ℕ)).X j) :=
        FiniteFreeComplex.identityDiskComplex_X_isZero_of_ne_support (R := R) (i := i)
          hjSucc hji
      letI : Subsingleton (((identityDisk i : ChainComplex (ModuleCat R) ℕ)).X j) :=
        ModuleCat.subsingleton_of_isZero hzero
      -- Proof comment: away from the two supported degrees, the middle object is zero.
      exact functionExact_of_subsingleton_middle _ _

/-- Helper for Chap10 Proposition 10 102 9: exact positive-degree rows on two complexes assemble
to exact rows on their biproduct. -/
private lemma exactAt_biprod_of_exactAt
    {K L : ChainComplex (ModuleCat R) ℕ} {j : ℕ}
    (hj : 1 ≤ j) (hK : K.ExactAt j) (hL : L.ExactAt j) :
    (biprod K L).ExactAt j := by
  rw [exactAt_iff_function_exact (biprod K L) hj]
  have hK' := (exactAt_iff_function_exact K hj).mp hK
  have hL' := (exactAt_iff_function_exact L hj).mp hL
  have hprod :
      Function.Exact
        (biprod.map (K.d (j + 1) j) (L.d (j + 1) j)).hom
        (biprod.map (K.d j (j - 1)) (L.d j (j - 1))).hom := by
    -- Proof comment: exactness is already known on each summand row, so the explicit biproduct
    -- row is exact componentwise.
    exact functionExact_biprodMap
      (K.d (j + 1) j) (K.d j (j - 1)) (L.d (j + 1) j) (L.d j (j - 1)) hK' hL'
  have h₁₂ :
      (biprod.map (K.d (j + 1) j) (L.d (j + 1) j)).hom.comp
          (HomologicalComplex.biprodXIso K L (j + 1)).toLinearEquiv.toLinearMap =
        (HomologicalComplex.biprodXIso K L j).toLinearEquiv.toLinearMap.comp
          ((biprod K L).d (j + 1) j).hom := by
    -- Proof comment: the objectwise biproduct comparison identifies the displayed differential on
    -- `biprod K L` with the componentwise biproduct map.
    simpa using congrArg (fun k ↦ k.hom)
      (@biprodXIso_differential_hom_local _ _ _ _ K L j).symm
  have h₂₃ :
      (biprod.map (K.d j (j - 1)) (L.d j (j - 1))).hom.comp
          (HomologicalComplex.biprodXIso K L j).toLinearEquiv.toLinearMap =
        (HomologicalComplex.biprodXIso K L (j - 1)).toLinearEquiv.toLinearMap.comp
          ((biprod K L).d j (j - 1)).hom := by
    -- Proof comment: apply the same displayed-differential comparison one degree lower.
    have hpred : j = j - 1 + 1 := by
      omega
    rw [hpred]
    exact congrArg (fun k ↦ k.hom)
      (@biprodXIso_differential_hom_local _ _ _ _ K L (j - 1)).symm
  -- Proof comment: transport exactness back from the explicit componentwise biproduct row to the
  -- actual differential row of `biprod K L`.
  exact (Function.Exact.iff_of_ladder_linearEquiv h₁₂ h₂₃).1 hprod

/-- Helper for Chap10 Proposition 10 102 9: exactness of a biproduct row implies exactness of the
first summand row. -/
private lemma exactAt_fst_of_biprod_exactAt
    {K L : ChainComplex (ModuleCat R) ℕ} {j : ℕ}
    (hj : 1 ≤ j)
    (h : (biprod K L).ExactAt j) :
    K.ExactAt j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  rw [hmid] at h ⊢
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      (biprod K L) (k + 2) (k + 1) k (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      K (k + 2) (k + 1) k (by simp) (by simp)]
  intro A x₂ hx₂
  -- Proof comment: insert the cycle into the left biproduct summand so the exactness witness on
  -- the product row produces a preimage.
  have hx₂' :
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k = 0 := by
    have hcomm := (biprod.inl : K ⟶ biprod K L).comm (k + 1) k
    calc
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k =
          x₂ ≫ (K.d (k + 1) k ≫ (biprod.inl : K ⟶ biprod K L).f k) := by
            simpa [Category.assoc] using congrArg (fun m ↦ x₂ ≫ m) hcomm
      _ = (x₂ ≫ K.d (k + 1) k) ≫ (biprod.inl : K ⟶ biprod K L).f k := by
            simp [Category.assoc]
      _ = 0 := by
            simp [hx₂]
  obtain ⟨A', π, hπ, y₁, hy₁⟩ := h (x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1)) hx₂'
  refine ⟨A', π, hπ, y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2), ?_⟩
  -- Proof comment: project the produced boundary back to the first summand.
  calc
    π ≫ x₂ = π ≫ x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simp [Category.assoc]
    _ = y₁ ≫ (biprod K L).d (k + 2) (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simpa [Category.assoc] using congrArg
            (fun m ↦ m ≫ (biprod.fst : biprod K L ⟶ K).f (k + 1)) hy₁
    _ = y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2) ≫ K.d (k + 2) (k + 1) := by
          have hcomm := (biprod.fst : biprod K L ⟶ K).comm (k + 2) (k + 1)
          simpa [Category.assoc] using congrArg (fun m ↦ y₁ ≫ m) hcomm.symm
    _ = (y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2)) ≫ K.d (k + 2) (k + 1) := by
          simp [Category.assoc]

/-- Helper for Chap10 Proposition 10 102 9: the adjacent left row index in the alternating-rank
recurrence. -/
private abbrev adjacentLeftIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1, by omega⟩

/-- Helper for Chap10 Proposition 10 102 9: the adjacent right row index in the alternating-rank
recurrence. -/
private abbrev adjacentRightIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1 + 1, by omega⟩

/-- Helper for Chap10 Proposition 10 102 9: the middle degree between two adjacent displayed
rows. -/
private abbrev adjacentMiddleIndex (i : Fin (e - 1)) : Fin (e + 1) :=
  ⟨i.1 + 1, by omega⟩

/-- Helper for Chap10 Proposition 10 102 9: an alternating sum and its tail recover the head
term. -/
private theorem alternatingSum_cons_add_tail_eq_head (a : ℤ) :
    ∀ l : List ℤ, List.alternatingSum (a :: l) + List.alternatingSum l = a
  | [] => by
      -- Proof comment: with empty tail the alternating sum is just the head term.
      simp [List.alternatingSum]
  | [b] => by
      -- Proof comment: with a singleton tail the two displayed terms cancel directly.
      simp [List.alternatingSum]
  | b :: c :: t => by
      -- Proof comment: peel off the first cancelling pair and recurse on the shorter tail.
      have ih : List.alternatingSum (c :: t) + List.alternatingSum t = c :=
        alternatingSum_cons_add_tail_eq_head c t
      simp [List.alternatingSum] at ih ⊢
      linarith

/-- Helper for Chap10 Proposition 10 102 9: consecutive alternating tails add back up to the
intermediate rank. -/
private theorem adjacent_alternatingRank_add_eq_rank (C : _root_.FiniteFreeComplex R e)
    (i : Fin (e - 1)) :
    C.alternatingRank (adjacentLeftIndex i) + C.alternatingRank (adjacentRightIndex i) =
      C.rank (adjacentMiddleIndex i) := by
  let tail : List ℤ :=
    List.ofFn fun k : Fin (e - (i.1 + 1)) ↦
      (C.rank ⟨i.1 + 2 + k.1, by omega⟩ : ℤ)
  have hleft_length : e - i.1 = (e - (i.1 + 1)) + 1 := by
    omega
  have hleft_list :
      List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
        (C.rank (adjacentMiddleIndex i) : ℤ) :: tail := by
    -- Proof comment: split the left alternating tail into its first term and the remaining tail.
    have hsucc_eq :
        List.ofFn
            (fun k : Fin ((e - (i.1 + 1)) + 1) ↦
              (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
          (C.rank (adjacentMiddleIndex i) : ℤ) ::
            List.ofFn
              (fun k : Fin (e - (i.1 + 1)) ↦
                (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) := by
      rw [List.ofFn_succ]
      simp [adjacentMiddleIndex]
    have htail_eq :
        List.ofFn
            (fun k : Fin (e - (i.1 + 1)) ↦
              (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) = tail := by
      apply congrArg List.ofFn
      funext k
      simp [Nat.add_left_comm, Nat.add_comm]
    calc
      List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
          List.ofFn
            (fun k : Fin ((e - (i.1 + 1)) + 1) ↦
              (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) := by
            simpa [hleft_length]
      _ = (C.rank (adjacentMiddleIndex i) : ℤ) ::
            List.ofFn
              (fun k : Fin (e - (i.1 + 1)) ↦
                (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) := hsucc_eq
      _ = (C.rank (adjacentMiddleIndex i) : ℤ) :: tail := by
            rw [htail_eq]
  have hleft :
      C.alternatingRank (adjacentLeftIndex i) =
        List.alternatingSum ((C.rank (adjacentMiddleIndex i) : ℤ) :: tail) := by
    -- Proof comment: rewrite the left alternating tail through the explicit head-tail identity.
    change
      List.alternatingSum
          (List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ))) =
        List.alternatingSum ((C.rank (adjacentMiddleIndex i) : ℤ) :: tail)
    simpa using congrArg List.alternatingSum hleft_list
  have hright :
      C.alternatingRank (adjacentRightIndex i) =
        List.alternatingSum tail := by
    -- Proof comment: the right alternating tail is definitionally the tail list introduced above.
    change
      List.alternatingSum
          (List.ofFn (fun k : Fin (e - (i.1 + 1)) ↦
            (C.rank ⟨i.1 + 2 + k.1, by omega⟩ : ℤ))) =
        List.alternatingSum tail
    rfl
  -- Proof comment: apply the elementary alternating-sum identity to the head-tail decomposition.
  rw [hleft, hright]
  simpa [tail] using
    alternatingSum_cons_add_tail_eq_head (C.rank (adjacentMiddleIndex i) : ℤ) tail

/-- Helper for Chap10 Proposition 10 102 9: at the top displayed row, the alternating rank is
the top displayed rank. -/
private theorem alternatingRank_last_eq_rank_top
    (C : FiniteFreeComplex R (e + 1)) :
    C.alternatingRank (Fin.last e) = C.rank ⟨e + 1, by omega⟩ := by
  -- Proof comment: at the last displayed row, the alternating tail has only the top rank term.
  unfold _root_.FiniteFreeComplex.alternatingRank
  simp
  congr

/-- Helper for Chap10 Proposition 10 102 9: an integer-valued row profile is determined by the
adjacent alternating-rank recurrence together with its top boundary value. -/
private theorem alternatingRank_eq_of_intProfile_recurrence
    (C : FiniteFreeComplex R e)
    (r : Fin e → ℤ)
    (hrec : ∀ j : Fin (e - 1),
      r (adjacentLeftIndex j) + r (adjacentRightIndex j) =
        C.rank (adjacentMiddleIndex j))
    (htop : ∀ h : 0 < e, r ⟨e - 1, by omega⟩ = C.rank ⟨e, by omega⟩)
    (i : Fin e) :
    r i = C.alternatingRank i := by
  cases e with
  | zero =>
      exact Fin.elim0 i
  | succ e =>
      -- Proof comment: descend from the top row; both profiles satisfy the same adjacent
      -- recurrence, so equality propagates one degree at a time.
      induction i using Fin.reverseInduction with
      | last =>
          calc
            r (Fin.last e) = C.rank ⟨e + 1, by omega⟩ := htop (Nat.succ_pos _)
            _ = C.alternatingRank (Fin.last e) := by
                  symm
                  exact alternatingRank_last_eq_rank_top (C := C)
      | cast j ih =>
          have hr :
              r (Fin.castSucc j) + r j.succ = C.rank (adjacentMiddleIndex j) :=
            hrec j
          have halt :
              C.alternatingRank (Fin.castSucc j) + C.alternatingRank j.succ =
                C.rank (adjacentMiddleIndex j) :=
            adjacent_alternatingRank_add_eq_rank (C := C) j
          linarith

/-- Helper for Chap10 Proposition 10 102 9: splitting off an identity-disk summand changes the
alternating rank only at the pivot row. -/
private theorem alternatingRank_splitRank_eq
    {C C' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (hsuccPos : 0 < C.rank i.succ)
    (hcastPos : 0 < C.rank i.castSucc)
    (hsplit : C'.rank = FiniteFreeComplex.splitRank C.rank i) :
    ∀ k : Fin e, C.alternatingRank k = C'.alternatingRank k + if k = i then 1 else 0 := by
  let r : Fin e → ℤ := fun k ↦ C'.alternatingRank k + if k = i then 1 else 0
  have hrec :
      ∀ j : Fin (e - 1),
        r (adjacentLeftIndex j) + r (adjacentRightIndex j) =
          C.rank (adjacentMiddleIndex j) := by
    intro j
    have hbase := adjacent_alternatingRank_add_eq_rank (C := C') j
    by_cases hleft : adjacentLeftIndex j = i
    · have hright : adjacentRightIndex j ≠ i := by
        intro hright
        have hstep : (adjacentLeftIndex j).1 + 1 = (adjacentRightIndex j).1 := by
          simp [adjacentLeftIndex, adjacentRightIndex]
        rw [hleft, hright] at hstep
        omega
      have hmid : adjacentMiddleIndex j = i.succ := by
        apply Fin.ext
        have hval : (adjacentLeftIndex j).1 = i.1 := congrArg Fin.val hleft
        omega
      calc
        r (adjacentLeftIndex j) + r (adjacentRightIndex j) =
            (C'.alternatingRank (adjacentLeftIndex j) +
              C'.alternatingRank (adjacentRightIndex j)) + 1 := by
              simp [r, hleft, hright, add_assoc, add_left_comm, add_comm]
        _ = C'.rank (adjacentMiddleIndex j) + 1 := by
              linarith
        _ = C.rank (adjacentMiddleIndex j) := by
              rw [hmid, hsplit]
              simp [FiniteFreeComplex.splitRank]
              omega
    · by_cases hright : adjacentRightIndex j = i
      · have hmid : adjacentMiddleIndex j = i.castSucc := by
          apply Fin.ext
          have hval : (adjacentRightIndex j).1 = i.1 := by
            simpa using congrArg Fin.val hright
          omega
        calc
          r (adjacentLeftIndex j) + r (adjacentRightIndex j) =
              (C'.alternatingRank (adjacentLeftIndex j) +
                C'.alternatingRank (adjacentRightIndex j)) + 1 := by
                simp [r, hleft, hright, add_assoc, add_left_comm, add_comm]
          _ = C'.rank (adjacentMiddleIndex j) + 1 := by
                linarith
          _ = C.rank (adjacentMiddleIndex j) := by
                rw [hmid, hsplit]
                simp [FiniteFreeComplex.splitRank]
                omega
      · have hmidSucc : adjacentMiddleIndex j ≠ i.succ := by
          intro hmid
          apply hleft
          apply Fin.ext
          have hval : (adjacentMiddleIndex j).1 = i.succ.1 := congrArg Fin.val hmid
          omega
        have hmidCast : adjacentMiddleIndex j ≠ i.castSucc := by
          intro hmid
          apply hright
          apply Fin.ext
          have hval : (adjacentMiddleIndex j).1 = i.castSucc.1 := congrArg Fin.val hmid
          omega
        calc
          r (adjacentLeftIndex j) + r (adjacentRightIndex j) =
              C'.alternatingRank (adjacentLeftIndex j) +
                C'.alternatingRank (adjacentRightIndex j) := by
                simp [r, hleft, hright]
          _ = C'.rank (adjacentMiddleIndex j) := hbase
          _ = C.rank (adjacentMiddleIndex j) := by
                rw [hsplit,
                  FiniteFreeComplex.splitRank_eq_of_ne_adjacent (n := C.rank) (i := i)
                    hmidSucc hmidCast]
  have htop :
      ∀ h : 0 < e, r ⟨e - 1, by omega⟩ = C.rank ⟨e, by omega⟩ := by
    intro he
    by_cases htopi : (⟨e - 1, by omega⟩ : Fin e) = i
    · have hmid : (⟨e, by omega⟩ : Fin (e + 1)) = i.succ := by
        apply Fin.ext
        have hval : ((⟨e - 1, by omega⟩ : Fin e).1) = i.1 := congrArg Fin.val htopi
        omega
      calc
        r ⟨e - 1, by omega⟩ = C'.alternatingRank ⟨e - 1, by omega⟩ + 1 := by
          simp [r, htopi]
        _ = C'.rank ⟨e, by omega⟩ + 1 := by
          simpa using alternatingRank_last_eq_rank_top (C := C')
        _ = C.rank ⟨e, by omega⟩ := by
          rw [hmid, hsplit]
          simp [FiniteFreeComplex.splitRank]
          omega
    · have hmidSucc : (⟨e, by omega⟩ : Fin (e + 1)) ≠ i.succ := by
        intro hmid
        apply htopi
        apply Fin.ext
        have hval : ((⟨e, by omega⟩ : Fin (e + 1)).1) = i.succ.1 := congrArg Fin.val hmid
        omega
      have hmidCast : (⟨e, by omega⟩ : Fin (e + 1)) ≠ i.castSucc := by
        intro hmid
        have hval : ((⟨e, by omega⟩ : Fin (e + 1)).1) = i.castSucc.1 := congrArg Fin.val hmid
        omega
      calc
        r ⟨e - 1, by omega⟩ = C'.alternatingRank ⟨e - 1, by omega⟩ := by
          simp [r, htopi]
        _ = C'.rank ⟨e, by omega⟩ := by
          simpa using alternatingRank_last_eq_rank_top (C := C')
        _ = C.rank ⟨e, by omega⟩ := by
          rw [hsplit,
            FiniteFreeComplex.splitRank_eq_of_ne_adjacent (n := C.rank) (i := i)
              hmidSucc hmidCast]
  intro k
  -- Proof comment: the shifted alternating-tail profile satisfies the same recurrence and top
  -- boundary value as `C.alternatingRank`, so the two profiles agree in every degree.
  have hk :=
    alternatingRank_eq_of_intProfile_recurrence (C := C) r hrec htop k
  simpa [r] using hk.symm

/-- Helper for Chap10 Proposition 10 102 9: the forward and inverse components of a chain-complex
isomorphism cancel on each displayed term. -/
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

/-- Helper for Chap10 Proposition 10 102 9: the inverse and forward components of a chain-complex
isomorphism cancel on each displayed term. -/
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

/-- Helper for Chap10 Proposition 10 102 9: a chain-complex isomorphism induces a linear
equivalence on every displayed degree. -/
private noncomputable def chainIsoComponentLinearEquiv
    {K L : ChainComplex (ModuleCat R) ℕ} (eiso : K ≅ L) (j : ℕ) :
    K.X j ≃ₗ[R] L.X j :=
  LinearEquiv.ofLinear (eiso.hom.f j).hom (eiso.inv.f j).hom
    (componentHom_comp_componentInv eiso j)
    (componentInv_comp_componentHom eiso j)

/-- Helper for Chap10 Proposition 10 102 9: the standard free module on `Fin (a + b)` is linearly
equivalent to the product of the standard free modules on `Fin a` and `Fin b`. -/
private noncomputable def standard_module_sum_linearEquiv (a b : ℕ) :
    ((Fin a → R) × (Fin b → R)) ≃ₗ[R] (Fin (a + b) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).symm.trans <|
    (LinearEquiv.piCongrLeft R (fun _ : Fin a ⊕ Fin b ↦ R) finSumFinEquiv.symm).symm

private noncomputable abbrev standardModuleSumEquiv (a b : ℕ) :
    ((Fin a → R) × (Fin b → R)) ≃ₗ[R] (Fin (a + b) → R) :=
  standard_module_sum_linearEquiv a b

/-- Helper for Chap10 Proposition 10 102 9: the summed-coordinate equivalence restricts to the
left finite block. -/
private lemma standard_module_sum_linearEquiv_apply_castAdd (a b : ℕ)
    (x : (Fin a → R) × (Fin b → R)) (i : Fin a) :
    standardModuleSumEquiv a b x (Fin.castAdd b i) = x.1 i := by
  -- Proof comment: unfold the finite-sum reindexing and evaluate on the left summand.
  rcases x with ⟨x₁, x₂⟩
  simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_symm_apply_castAdd,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]

/-- Helper for Chap10 Proposition 10 102 9: the summed-coordinate equivalence restricts to the
right finite block. -/
private lemma standard_module_sum_linearEquiv_apply_natAdd (a b : ℕ)
    (x : (Fin a → R) × (Fin b → R)) (i : Fin b) :
    standardModuleSumEquiv a b x (Fin.natAdd a i) = x.2 i := by
  -- Proof comment: unfold the finite-sum reindexing and evaluate on the right summand.
  rcases x with ⟨x₁, x₂⟩
  simp [standard_module_sum_linearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft, Equiv.piCongrLeft', finSumFinEquiv_symm_apply_natAdd,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

/-- Helper for Chap10 Proposition 10 102 9: a left-block basis vector becomes the corresponding
left product basis vector under the summed-coordinate splitting. -/
private lemma standard_module_sum_linearEquiv_symm_single_castAdd (a b : ℕ) (i : Fin a) :
    (standardModuleSumEquiv a b).symm (Pi.single (Fin.castAdd b i) (1 : R)) =
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

/-- Helper for Chap10 Proposition 10 102 9: a right-block basis vector becomes the corresponding
right product basis vector under the summed-coordinate splitting. -/
private lemma standard_module_sum_linearEquiv_symm_single_natAdd (a b : ℕ) (i : Fin b) :
    (standardModuleSumEquiv a b).symm (Pi.single (Fin.natAdd a i) (1 : R)) =
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

/-- Helper for Chap10 Proposition 10 102 9: the product of two finite-coordinate rows, reindexed
as a row between the corresponding summed finite free modules. -/
private noncomputable def prodMapInStandardCoordinates {m n p q : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (ψ : (Fin p → R) →ₗ[R] (Fin q → R)) :
    (Fin (m + p) → R) →ₗ[R] (Fin (n + q) → R) :=
  (standardModuleSumEquiv n q).toLinearMap.comp
    ((φ.prodMap ψ).comp (standardModuleSumEquiv m p).symm.toLinearMap)

/-- Helper for Chap10 Proposition 10 102 9: reindexing rows and columns by equivalences does not
change a fixed-size determinantal ideal. -/
private lemma matrix_minorIdeal_reindex_eq
    {ι ι' κ κ' : Type*} (r : ℕ) (A : Matrix ι κ R) (e₁ : ι ≃ ι') (e₂ : κ ≃ κ') :
    Matrix.minorIdeal r (Matrix.reindex e₁ e₂ A) = Matrix.minorIdeal r A := by
  -- Proof comment: each selected minor of the reindexed matrix is exactly the corresponding minor
  -- of the original matrix after precomposing with the inverse embeddings, and conversely.
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

/-- Helper for Chap10 Proposition 10 102 9: in the finite-sum coordinate order, a product row has
the expected block-diagonal matrix. -/
private lemma toMatrix_prodMapInStandardCoordinates {m n p q : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (ψ : (Fin p → R) →ₗ[R] (Fin q → R)) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + q)))
          (prodMapInStandardCoordinates φ ψ)) =
      Matrix.fromBlocks
        (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ)
        0 0
        (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin q)) ψ) := by
  -- Proof comment: the chosen sum-coordinate equivalence sends left and right finite blocks to
  -- the two product factors, so each block entry reduces to the defining product map.
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

/-- Helper for Chap10 Proposition 10 102 9: if a predicate is false above `a`, increasing the
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

/-- Helper for Chap10 Proposition 10 102 9: exterior powers above the source or target rank of a
finite-coordinate map vanish. -/
private lemma exteriorPower_map_eq_zero_of_min_lt [Nontrivial R]
    {m n r : ℕ} (h : min m n < r) (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorPower.map r φ = 0 := by
  -- Proof comment: once the exterior degree exceeds either source or target rank, the relevant
  -- exterior power has finrank zero, so the induced map is forced to vanish.
  have hmn : m < r ∨ n < r := by omega
  rcases hmn with hm' | hn'
  · have hfin : Module.finrank R (⋀[R]^r (Fin m → R)) = 0 := by
      rw [exteriorPower.finrank_eq]
      simpa using Nat.choose_eq_zero_of_lt hm'
    haveI : Subsingleton (⋀[R]^r (Fin m → R)) :=
      (Module.finrank_eq_zero_iff_of_free R (⋀[R]^r (Fin m → R))).mp hfin
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    simp
  · have hfin : Module.finrank R (⋀[R]^r (Fin n → R)) = 0 := by
      rw [exteriorPower.finrank_eq]
      simpa using Nat.choose_eq_zero_of_lt hn'
    haveI : Subsingleton (⋀[R]^r (Fin n → R)) :=
      (Module.finrank_eq_zero_iff_of_free R (⋀[R]^r (Fin n → R))).mp hfin
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

/-- Helper for Chap10 Proposition 10 102 9: the zeroth exterior-power map of a finite-coordinate
linear map is nonzero over a nontrivial base ring. -/
private lemma exteriorPower_map_zero_ne_zero [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorPower.map 0 φ ≠ 0 := by
  -- Proof comment: naturality of `zeroEquiv` identifies the zeroth exterior-power map with the
  -- identity map on `R`.
  intro hzero
  have hnat := exteriorPower.zeroEquiv_naturality φ
  have hval :=
    LinearMap.congr_fun hnat
      (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → (Fin m → R)))
  rw [hzero] at hval
  simp [exteriorPower.zeroEquiv_ιMulti] at hval

/-- Helper for Chap10 Proposition 10 102 9: the exterior-power map in the exterior-rank degree is
nonzero. -/
private lemma exteriorPower_map_exteriorRank_ne_zero [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    exteriorPower.map (LinearMap.exteriorRank φ) φ ≠ 0 := by
  -- Proof comment: degree `0` is always available to the `findGreatest` defining exterior rank.
  letI : DecidablePred (fun r ↦ exteriorPower.map r φ ≠ 0) := Classical.decPred _
  unfold LinearMap.exteriorRank
  let P : ℕ → Prop := fun r ↦ exteriorPower.map r φ ≠ 0
  change P (Nat.findGreatest P (min m n))
  exact Nat.findGreatest_spec (show 0 ≤ min m n by simp) (by simpa [P] using exteriorPower_map_zero_ne_zero φ)

/-- Helper for Chap10 Proposition 10 102 9: if the map on `r`th exterior powers is zero, then all
`r × r` minors of the coordinate matrix vanish. -/
private lemma matrix_minorIdeal_eq_bot_of_exteriorPower_map_eq_zero {m n r : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hmap : exteriorPower.map r φ = 0) :
    Matrix.minorIdeal r
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) = ⊥ := by
  -- Proof comment: evaluating arbitrary exterior dual coordinate functionals on the zero map
  -- produces exactly the selected determinants of the coordinate matrix.
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

/-- Helper for Chap10 Proposition 10 102 9: if all `r × r` minors vanish, then the `r`th
exterior-power map is zero. -/
private lemma exteriorPower_map_eq_zero_of_matrix_minorIdeal_eq_bot {m n r : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hminor : Matrix.minorIdeal r
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) = ⊥) :
    exteriorPower.map r φ = 0 := by
  -- Proof comment: each coordinate of the image of an exterior basis vector is a selected minor
  -- of the coordinate matrix, hence vanishes under the minor-ideal hypothesis.
  classical
  let bM := (Pi.basisFun R (Fin m)).exteriorPower r
  let bN := (Pi.basisFun R (Fin n)).exteriorPower r
  apply bM.ext
  intro s
  apply bN.repr.injective
  ext t
  let e₁ : Fin r ↪ Fin n := (powersetCard.ofFinEmbEquiv.symm t).toEmbedding
  let e₂ : Fin r ↪ Fin m := (powersetCard.ofFinEmbEquiv.symm s).toEmbedding
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

/-- Helper for Chap10 Proposition 10 102 9: minors strictly above the exterior rank vanish. -/
private lemma matrix_minorIdeal_eq_bot_of_exteriorRank_lt [Nontrivial R]
    {m n r : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hr : LinearMap.exteriorRank φ < r) :
    Matrix.minorIdeal r
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) = ⊥ := by
  -- Proof comment: above the defining greatest nonzero exterior degree, the exterior-power map
  -- is zero, so every minor of that size vanishes.
  apply matrix_minorIdeal_eq_bot_of_exteriorPower_map_eq_zero φ
  by_cases hrle : r ≤ min m n
  · by_contra hnonzero
    have hle : r ≤ LinearMap.exteriorRank φ := by
      letI : DecidablePred (fun r ↦ exteriorPower.map r φ ≠ 0) := Classical.decPred _
      unfold LinearMap.exteriorRank
      exact Nat.le_findGreatest hrle hnonzero
    omega
  · exact exteriorPower_map_eq_zero_of_min_lt (Nat.lt_of_not_ge hrle) φ

/-- Helper for Chap10 Proposition 10 102 9: the minor ideal in the exterior-rank degree is
nonzero. -/
private lemma matrix_minorIdeal_exteriorRank_ne_bot [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Matrix.minorIdeal (LinearMap.exteriorRank φ)
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ) ≠ ⊥ := by
  -- Proof comment: if those minors vanished, the exterior-power map in exterior-rank degree would
  -- vanish too, contradicting the defining nonzero witness.
  intro hbot
  have hmap := exteriorPower_map_eq_zero_of_matrix_minorIdeal_eq_bot φ hbot
  exact (exteriorPower_map_exteriorRank_ne_zero φ) hmap

/-- Helper for Chap10 Proposition 10 102 9: if the selected minor size exceeds the row count, the
minor ideal is zero. -/
private lemma matrix_minorIdeal_eq_bot_of_row_lt {ι κ : Type*} [Fintype ι]
    {r : ℕ} (h : Fintype.card ι < r) (A : Matrix ι κ R) :
    Matrix.minorIdeal r A = ⊥ := by
  -- Proof comment: an `r`-row minor would require an embedding `Fin r ↪ ι`, contradicting the
  -- cardinality bound.
  rw [Matrix.minorIdeal, Ideal.span_eq_bot]
  intro x hx
  rcases hx with ⟨⟨e₁, _e₂⟩, rfl⟩
  exfalso
  have hle : r ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_embedding e₁
  omega

/-- Helper for Chap10 Proposition 10 102 9: the full-size minor ideal of a finite-coordinate
linear equivalence is the unit ideal. -/
private lemma matrix_minorIdeal_linearEquiv_full_eq_top [Nontrivial R] {p : ℕ}
    (e : (Fin p → R) ≃ₗ[R] (Fin p → R)) :
    Matrix.minorIdeal p
      (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap) = ⊤ := by
  -- Proof comment: the full determinant of an invertible coordinate matrix is a unit, hence it
  -- generates the unit ideal among size-`p` minors.
  let A := LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap
  have heUnit : IsUnit (e.toLinearMap : Module.End R (Fin p → R)) := by
    refine ⟨⟨e.toLinearMap, e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
    · ext x
      simp
    · ext x
      simp
  have hmatUnit : IsUnit A := by
    simpa [A] using
      (LinearMap.isUnit_toMatrix_iff (Pi.basisFun R (Fin p))).2 heUnit
  have hdetUnit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hmatUnit
  refine Ideal.eq_top_of_isUnit_mem _ ?_ hdetUnit
  change A.det ∈ Matrix.minorIdeal p A
  exact Matrix.det_submatrix_mem_minorIdeal p A
    (Function.Embedding.refl _) (Function.Embedding.refl _)

/-- Helper for Chap10 Proposition 10 102 9: at the shifted exterior-rank degree, the block
diagonal matrix with a linear-equivalence block has the same minor ideal as the first block. -/
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
  -- Proof comment: in the block-minor expansion, every antidiagonal term vanishes except the one
  -- taking an exterior-rank minor from `φ` and the full determinant from the equivalence block.
  rw [Matrix.minorIdeal_fromBlocks]
  rw [Finset.sum_eq_single (LinearMap.exteriorRank φ, p)]
  · rw [matrix_minorIdeal_linearEquiv_full_eq_top e]
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
      rw [matrix_minorIdeal_eq_bot_of_exteriorRank_lt φ hb1gt]
      simp
    · have hplt : p < b.2 := Nat.lt_of_not_ge hbp
      have hcard : Fintype.card (Fin p) < b.2 := by
        simpa using hplt
      rw [matrix_minorIdeal_eq_bot_of_row_lt
        hcard (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap)]
      simp
  · intro hnot
    have hmem_pair :
        (LinearMap.exteriorRank φ, p) ∈ Finset.antidiagonal (LinearMap.exteriorRank φ + p) :=
      Finset.mem_antidiagonal.mpr rfl
    exact (hnot hmem_pair).elim

/-- Helper for Chap10 Proposition 10 102 9: positive minors of the zero matrix generate the zero
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

/-- Helper for Chap10 Proposition 10 102 9: zero-size minors of any matrix generate the unit
ideal. -/
private lemma matrix_minorIdeal_zero_size_eq_top {ι κ : Type*} (A : Matrix ι κ R) :
    Matrix.minorIdeal 0 A = ⊤ := by
  -- Proof comment: the unique `0 × 0` minor has determinant `1`.
  rw [Matrix.minorIdeal, Ideal.eq_top_iff_one]
  refine Ideal.subset_span ?_
  let e₁ : Fin 0 ↪ ι := ⟨Fin.elim0, fun x ↦ Fin.elim0 x⟩
  let e₂ : Fin 0 ↪ κ := ⟨Fin.elim0, fun x ↦ Fin.elim0 x⟩
  refine ⟨⟨e₁, e₂⟩, ?_⟩
  simp

/-- Helper for Chap10 Proposition 10 102 9: the block formula for a zero second diagonal block
reduces to the first block at a fixed minor size. -/
private lemma matrix_minorIdeal_fromBlocks_zero_right_eq
    {ι κ ι' κ' : Type*} (r : ℕ) (A : Matrix ι κ R) :
    (Finset.antidiagonal r).sum
        (fun x : ℕ × ℕ ↦ Matrix.minorIdeal x.1 A *
          Matrix.minorIdeal x.2 (0 : Matrix ι' κ' R)) =
      Matrix.minorIdeal r A := by
  -- Proof comment: all antidiagonal terms with positive second component vanish, and the unique
  -- term with second component zero is `I_r(A) * ⊤`.
  rw [Finset.sum_eq_single (r, 0)]
  · simp [matrix_minorIdeal_zero_size_eq_top]
  · intro b hb hbne
    have hsum := Finset.mem_antidiagonal.mp hb
    have hbpos : 0 < b.2 := by
      by_contra h
      have hb2 : b.2 = 0 := Nat.eq_zero_of_not_pos h
      have hb1 : b.1 = r := by omega
      exact hbne (Prod.ext hb1 hb2)
    simp [matrix_minorIdeal_zero_eq_bot_of_pos hbpos]
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr (by simp))).elim

/-- Helper for Chap10 Proposition 10 102 9: a zero product summand does not change the exterior
rank of the row in standard summed coordinates. -/
private lemma exteriorRank_prodMapInStandardCoordinates_zero_eq [Nontrivial R]
    {m n p q : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    LinearMap.exteriorRank
        (prodMapInStandardCoordinates φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))) =
      LinearMap.exteriorRank φ := by
  classical
  let F : (Fin (m + p) → R) →ₗ[R] (Fin (n + q) → R) :=
    prodMapInStandardCoordinates φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))
  have hF_factor :
      F =
        (standardModuleSumEquiv n q).toLinearMap.comp
          ((LinearMap.inl R (Fin n → R) (Fin q → R)).comp
            (φ.comp
              ((LinearMap.fst R (Fin m → R) (Fin p → R)).comp
                (standardModuleSumEquiv m p).symm.toLinearMap))) := by
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
    · let j₀ : Fin q := ⟨j.1 - n, by omega⟩
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
          ((standardModuleSumEquiv n q).symm.toLinearMap.comp
            (F.comp
              ((standardModuleSumEquiv m p).toLinearMap.comp
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
    (fun {r} h hnonzero ↦ hnonzero (exteriorPower_map_eq_zero_of_min_lt h φ))

/-- Helper for Chap10 Proposition 10 102 9: adding a zero product summand preserves both the
exterior rank and the rank-minor ideal in standard summed coordinates. -/
private lemma prodMapInStandardCoordinates_zero_profile [Nontrivial R]
    {m n p q : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    LinearMap.exteriorRank
        (prodMapInStandardCoordinates φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))) =
        LinearMap.exteriorRank φ ∧
      I(prodMapInStandardCoordinates φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))) =
        I(φ) := by
  refine ⟨exteriorRank_prodMapInStandardCoordinates_zero_eq φ, ?_⟩
  -- Proof comment: after fixing the exterior rank, the block-diagonal minor computation shows
  -- that the zero block contributes no new minors of the relevant size.
  rw [LinearMap.rankMinorIdeal, exteriorRank_prodMapInStandardCoordinates_zero_eq]
  rw [← matrix_minorIdeal_reindex_eq (LinearMap.exteriorRank φ)
    (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + q)))
      (prodMapInStandardCoordinates φ (0 : (Fin p → R) →ₗ[R] (Fin q → R))))
    finSumFinEquiv.symm finSumFinEquiv.symm]
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

/-- Helper for Chap10 Proposition 10 102 9: adding a linearly equivalent second summand in
standard summed coordinates shifts the exterior rank by the size of that block and leaves the
rank-minor ideal unchanged. -/
private lemma prodMapInStandardCoordinates_linearEquiv_profile [Nontrivial R]
    {m n p q : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (e : (Fin p → R) ≃ₗ[R] (Fin q → R)) :
    LinearMap.exteriorRank (prodMapInStandardCoordinates φ e.toLinearMap) =
        LinearMap.exteriorRank φ + p ∧
      I(prodMapInStandardCoordinates φ e.toLinearMap) = I(φ) := by
  classical
  have hpq : p = q := InvariantBasisNumber.eq_of_fin_equiv e
  cases hpq
  let F : (Fin (m + p) → R) →ₗ[R] (Fin (n + p) → R) :=
    prodMapInStandardCoordinates φ e.toLinearMap
  let A : Matrix (Fin n) (Fin m) R :=
    LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ
  have hminor_eq_at :
      Matrix.minorIdeal (LinearMap.exteriorRank φ + p)
          (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F) =
        Matrix.minorIdeal (LinearMap.exteriorRank φ) A := by
    rw [← matrix_minorIdeal_reindex_eq (LinearMap.exteriorRank φ + p)
      (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F)
      finSumFinEquiv.symm finSumFinEquiv.symm]
    rw [toMatrix_prodMapInStandardCoordinates]
    exact matrix_minorIdeal_fromBlocks_linearEquiv_at_exteriorRank_eq φ e
  have hminor_bot_of_gt :
      ∀ {r : ℕ}, LinearMap.exteriorRank φ + p < r →
        Matrix.minorIdeal r
          (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F) =
          ⊥ := by
    intro r hr
    rw [← matrix_minorIdeal_reindex_eq r
      (LinearMap.toMatrix (Pi.basisFun R (Fin (m + p))) (Pi.basisFun R (Fin (n + p))) F)
      finSumFinEquiv.symm finSumFinEquiv.symm]
    rw [toMatrix_prodMapInStandardCoordinates]
    rw [Matrix.minorIdeal_fromBlocks]
    apply Finset.sum_eq_zero
    intro b hb
    have hsum := Finset.mem_antidiagonal.mp hb
    by_cases hb1 : LinearMap.exteriorRank φ < b.1
    · rw [matrix_minorIdeal_eq_bot_of_exteriorRank_lt φ hb1]
      simp
    · have hbp : p < b.2 := by
        have hb1le : b.1 ≤ LinearMap.exteriorRank φ := Nat.le_of_not_gt hb1
        omega
      have hcard : Fintype.card (Fin p) < b.2 := by
        simpa using hbp
      rw [matrix_minorIdeal_eq_bot_of_row_lt
        hcard (LinearMap.toMatrix (Pi.basisFun R (Fin p)) (Pi.basisFun R (Fin p)) e.toLinearMap)]
      simp
  have hFnonzero :
      exteriorPower.map (LinearMap.exteriorRank φ + p) F ≠ 0 := by
    intro hzero
    have hbot := matrix_minorIdeal_eq_bot_of_exteriorPower_map_eq_zero F hzero
    rw [hminor_eq_at] at hbot
    exact (matrix_minorIdeal_exteriorRank_ne_bot φ) hbot
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
      have hzero := exteriorPower_map_eq_zero_of_matrix_minorIdeal_eq_bot F hbot
      exact (exteriorPower_map_exteriorRank_ne_zero F) hzero
    exact le_antisymm hupper hlower
  have hIdeal : I(F) = I(φ) := by
    rw [LinearMap.rankMinorIdeal, LinearMap.rankMinorIdeal, hRank]
    exact hminor_eq_at
  exact ⟨hRank, hIdeal⟩

/-- Helper for Chap10 Proposition 10 102 9: every term of the identity disk is definitionally the
standard finite free module with the corresponding `identityDiskRank`. -/
private lemma identityDiskComplex_X_eq_rank (i : Fin e) (j : ℕ) :
    (identityDisk i).X j =
      ModuleCat.of R (Fin (FiniteFreeComplex.identityDiskRank i j) → R) := by
  -- Proof comment: record the definitional object formula once so later transports stay explicit.
  rfl

/-- Helper for Chap10 Proposition 10 102 9: the identity-disk term in degree `j` is identified
with its standard finite-coordinate module. -/
private noncomputable def identityDiskTermEquiv (i : Fin e) (j : ℕ) :
    (@FiniteFreeComplex.identityDiskComplex R (inferInstance : Ring R) e i).X j ≃ₗ[R]
      (Fin (FiniteFreeComplex.identityDiskRank i j) → R) :=
  (eqToIso (show (@FiniteFreeComplex.identityDiskComplex R (inferInstance : Ring R) e i).X j =
      ModuleCat.of R (Fin (FiniteFreeComplex.identityDiskRank i j) → R) from rfl)).toLinearEquiv

/-- Helper for Chap10 Proposition 10 102 9: the source term of the split row is transported to
the product of the reduced-complex source term and the identity-disk source term. -/
private noncomputable def splitRowSourceEquiv
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (identityDisk i))
    (k : Fin e) :
    (Fin (D.rank k.succ) → R) ≃ₗ[R]
      ((Fin (D'.rank k.succ) → R) ×
        (Fin (FiniteFreeComplex.identityDiskRank i (k.1 + 1)) → R)) :=
  (((D.termIso k.succ).toLinearEquiv.symm.trans
      (chainIsoComponentLinearEquiv eiso (k.1 + 1))).trans
    (HomologicalComplex.biprodXIso D'.toChainComplex
      (identityDisk i) (k.1 + 1)).toLinearEquiv).trans
    ((ModuleCat.biprodIsoProd (D'.toChainComplex.X (k.1 + 1))
      ((identityDisk i).X (k.1 + 1))).toLinearEquiv.trans
      (LinearEquiv.prodCongr (D'.termIso k.succ).toLinearEquiv
        (identityDiskTermEquiv i (k.1 + 1))))

/-- Helper for Chap10 Proposition 10 102 9: the target term of the split row is transported to
the product of the reduced-complex target term and the identity-disk target term. -/
private noncomputable def splitRowTargetEquiv
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (identityDisk i))
    (k : Fin e) :
    (Fin (D.rank k.castSucc) → R) ≃ₗ[R]
      ((Fin (D'.rank k.castSucc) → R) ×
        (Fin (FiniteFreeComplex.identityDiskRank i k.1) → R)) :=
  (((D.termIso k.castSucc).toLinearEquiv.symm.trans
      (chainIsoComponentLinearEquiv eiso k.1)).trans
    (HomologicalComplex.biprodXIso D'.toChainComplex
      (identityDisk i) k.1).toLinearEquiv).trans
    ((ModuleCat.biprodIsoProd (D'.toChainComplex.X k.1)
      ((identityDisk i).X k.1)).toLinearEquiv.trans
      (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
        (identityDiskTermEquiv i k.1)))

/-- Helper for Chap10 Proposition 10 102 9: the identity-disk row written in the finite
coordinates used by the split-row normal form. -/
private noncomputable def identityDiskRowInCoordinates (i : Fin e) (k : Fin e) :
    (Fin (FiniteFreeComplex.identityDiskRank i (k.1 + 1)) → R) →ₗ[R]
      (Fin (FiniteFreeComplex.identityDiskRank i k.1) → R) :=
  (identityDiskTermEquiv i k.1).toLinearMap.comp
    (((identityDisk i).d (k.1 + 1) k.1).hom.comp
      (identityDiskTermEquiv i (k.1 + 1)).symm.toLinearMap)

/-- Helper for Chap10 Proposition 10 102 9: away from its supported degree, the identity-disk row
is the zero finite-coordinate map. -/
private lemma identityDiskRowInCoordinates_eq_zero_of_ne (i : Fin e) {k : Fin e}
    (hk : k.1 ≠ i.1) :
    identityDiskRowInCoordinates i k =
      (0 :
        (Fin (FiniteFreeComplex.identityDiskRank i (k.1 + 1)) → R) →ₗ[R]
          (Fin (FiniteFreeComplex.identityDiskRank i k.1) → R)) := by
  -- Proof comment: the off-support chain differential is already zero before the coordinate
  -- identifications, so the transported row is zero as well.
  unfold identityDiskRowInCoordinates
  rw [@FiniteFreeComplex.identityDiskComplex_d_eq_zero_of_ne R _ e i k.1 hk]
  ext x j
  simp

/-- Helper for Chap10 Proposition 10 102 9: the supported identity-disk source and target
finite-coordinate modules are canonically identified. -/
private noncomputable def identityDiskSupportedEquiv (i : Fin e) :
    (Fin (FiniteFreeComplex.identityDiskRank i (i.1 + 1)) → R) ≃ₗ[R]
      (Fin (FiniteFreeComplex.identityDiskRank i i.1) → R) :=
  (((identityDiskTermEquiv i (i.1 + 1)).symm.trans
    (eqToIso (show (identityDisk i).X (i.1 + 1) = (identityDisk i).X i.1 by
      rw [@FiniteFreeComplex.identityDiskComplex_X_eq_succ R _ e i,
        @FiniteFreeComplex.identityDiskComplex_X_eq_castSucc R _ e i])).toLinearEquiv).trans
    (identityDiskTermEquiv i i.1))

/-- Helper for Chap10 Proposition 10 102 9: on its supported degree, the identity-disk row is the
rank-one identity map in finite coordinates. -/
private lemma identityDiskRowInCoordinates_eq_id (i : Fin e) :
    identityDiskRowInCoordinates i i =
      ((identityDiskSupportedEquiv i).toLinearMap :
        (Fin (FiniteFreeComplex.identityDiskRank i (i.1 + 1)) → R) →ₗ[R]
          (Fin (FiniteFreeComplex.identityDiskRank i i.1) → R)) := by
  -- Proof comment: after identifying the supported row with the named `eqToHom`, the coordinate
  -- conjugation is exactly the canonical supported finite-coordinate equivalence.
  unfold identityDiskRowInCoordinates
  rw [identityDiskComplex_d_eq_id (R := R) (e := e) (i := i)]
  rfl

/-- Helper for Chap10 Proposition 10 102 9: conjugating a displayed row back through the chosen
term coordinates recovers the owner chain differential. -/
private lemma termIso_hom_comp_diffAt_comp_termIso_inv
    (C : _root_.FiniteFreeComplex R e) (i : Fin e) :
    (C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i) ≫
        (C.termIso i.castSucc).inv =
      C.toChainComplex.d (i.1 + 1) i.1 := by
  -- Proof comment: expand the displayed differential once, then cancel the source and target
  -- coordinate isomorphisms in the chain-complex category.
  dsimp [FiniteFreeComplex.diffAt, FiniteFreeComplex.differential, FiniteFreeComplex.termIsoAt]
  change (C.termIso i.succ).hom ≫
      ((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
        (C.termIso i.castSucc).hom) ≫
      (C.termIso i.castSucc).inv =
    C.toChainComplex.d (i.1 + 1) i.1
  simp [Category.assoc]

/-- Helper for Chap10 Proposition 10 102 9: conjugating a row through a chain-complex
isomorphism to a biproduct and then through `biprodXIso` gives the biproduct row map. -/
private lemma chainIsoBiprodXItoRow_eq_biprodMap
    {M K L : ChainComplex (ModuleCat R) ℕ}
    (eiso : M ≅ biprod K L) (j : ℕ) :
    (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
        eiso.inv.f (j + 1) ≫ M.d (j + 1) j ≫ eiso.hom.f j ≫
        (HomologicalComplex.biprodXIso K L j).hom =
      biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
  -- Proof comment: move the row across the chain isomorphism, then normalize the biproduct
  -- differential with the explicit `biprodXIso` comparison.
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
          (chainIso_inv_d_hom eiso j)
    _ =
      (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
        ((HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j)) := by
        rw [@biprodXIso_differential_hom_local _ _ _ _ K L j]
    _ = biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
        simp [Category.assoc]

/-- Helper for Chap10 Proposition 10 102 9: before reindexing product coordinates as a summed
finite free module, the split-model row is the product of the two summand rows. -/
private lemma splitRow_conj_eq_prodMap
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (identityDisk i))
    (k : Fin e) :
    (splitRowTargetEquiv eiso k).toLinearMap.comp
      ((D.diffAt k).comp
        (splitRowSourceEquiv eiso k).symm.toLinearMap) =
    (D'.diffAt k).prodMap (identityDiskRowInCoordinates i k) := by
  -- Proof comment: compare the row after projecting the biproduct source and target to their two
  -- explicit components.
  apply LinearMap.ext
  intro x
  let xb :
      ↑(biprod (D'.toChainComplex.X (k.1 + 1))
        ((identityDisk i).X (k.1 + 1))) :=
    ((ModuleCat.biprodIsoProd (D'.toChainComplex.X (k.1 + 1))
      ((identityDisk i).X (k.1 + 1))).inv.hom)
      (((LinearEquiv.prodCongr (D'.termIso k.succ).toLinearEquiv
        (identityDiskTermEquiv i (k.1 + 1))).symm) x)
  have hrowx :=
    congrArg
        (fun f :
          biprod (D'.toChainComplex.X (k.1 + 1))
              ((identityDisk i).X (k.1 + 1)) ⟶
            biprod (D'.toChainComplex.X k.1)
              ((identityDisk i).X k.1) ↦
        (((ModuleCat.biprodIsoProd (D'.toChainComplex.X k.1)
          ((identityDisk i).X k.1)).hom.hom)
          (f.hom xb)))
      (chainIsoBiprodXItoRow_eq_biprodMap eiso k.1)
  have hpair :=
    congrArg
      (fun y ↦
        (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
          (identityDiskTermEquiv i k.1)) y)
      hrowx
  rw [← termIso_hom_comp_diffAt_comp_termIso_inv D k] at hpair
  have hprod :
      (fun y ↦
        (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
          (identityDiskTermEquiv i k.1)) y)
      ((fun f ↦
          ((ModuleCat.biprodIsoProd (D'.toChainComplex.X k.1)
            ((identityDisk i).X k.1)).hom.hom)
            ((ModuleCat.Hom.hom f) xb))
        (biprod.map (D'.toChainComplex.d (k.1 + 1) k.1)
          ((identityDisk i).d (k.1 + 1) k.1))) =
        ((D'.diffAt k).prodMap (identityDiskRowInCoordinates i k)) x := by
    -- Proof comment: the right-hand biproduct row is exactly the product of the two summand rows
    -- after the biproduct terms are identified with products.
    have hmap :=
      biprod_map_biprodIsoProd_apply
        (D'.toChainComplex.d (k.1 + 1) k.1)
        ((identityDisk i).d (k.1 + 1) k.1)
        (((LinearEquiv.prodCongr (D'.termIso k.succ).toLinearEquiv
          (identityDiskTermEquiv i (k.1 + 1))).symm) x)
    exact congrArg
      (fun y ↦
        (LinearEquiv.prodCongr (D'.termIso k.castSucc).toLinearEquiv
          (identityDiskTermEquiv i k.1)) y)
      hmap
  rw [hprod] at hpair
  exact hpair

/-- Helper for Chap10 Proposition 10 102 9: after passing to summed finite coordinates, the split
row becomes the product row of the reduced complex and the identity disk. -/
private lemma splitRow_conj_eq_prodMapInStandardCoordinates
    {D D' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : D.toChainComplex ≅
      biprod D'.toChainComplex (identityDisk i))
    (k : Fin e) :
    (standardModuleSumEquiv (D'.rank k.castSucc)
        (FiniteFreeComplex.identityDiskRank i k.1)).toLinearMap.comp
      ((splitRowTargetEquiv eiso k).toLinearMap.comp
        ((D.diffAt k).comp
          ((splitRowSourceEquiv eiso k).symm.toLinearMap.comp
            (standardModuleSumEquiv (D'.rank k.succ)
              (FiniteFreeComplex.identityDiskRank i (k.1 + 1))).symm.toLinearMap))) =
    (standardModuleSumEquiv (D'.rank k.castSucc)
      (FiniteFreeComplex.identityDiskRank i k.1)).toLinearMap.comp
      (((D'.diffAt k).prodMap (identityDiskRowInCoordinates i k)).comp
        (standardModuleSumEquiv (D'.rank k.succ)
          (FiniteFreeComplex.identityDiskRank i (k.1 + 1))).symm.toLinearMap) := by
  -- Proof comment: after the product-level split row is known, the summed-coordinate statement is
  -- just post- and precomposition by the fixed finite-sum coordinate equivalences.
  apply LinearMap.ext
  intro x
  have h :=
    congrArg
      (fun f ↦
        (standardModuleSumEquiv (D'.rank k.castSucc)
          (FiniteFreeComplex.identityDiskRank i k.1)).toLinearMap.comp
          (f.comp (standardModuleSumEquiv (D'.rank k.succ)
            (FiniteFreeComplex.identityDiskRank i (k.1 + 1))).symm.toLinearMap))
      (splitRow_conj_eq_prodMap eiso k)
  exact LinearMap.congr_fun h x

/-- Helper for Chap10 Proposition 10 102 9: exactness in positive degrees descends across a split
`identityDiskComplex` summand. -/
private lemma exactInPositiveDegrees_of_biprod_identityDisk
    {C C' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : C.toChainComplex ≅
      biprod C'.toChainComplex (identityDisk i)) :
    C.ExactInPositiveDegrees → C'.ExactInPositiveDegrees := by
  intro hExact j hj hje
  -- Proof comment: transport exactness to the split model and then project away the
  -- `identityDiskComplex` factor.
  have hbiprod :
      (biprod C'.toChainComplex (identityDisk i)).ExactAt j := by
    exact (hExact j hj hje).of_iso eiso
  exact exactAt_fst_of_biprod_exactAt hj hbiprod

/-- Helper for Chap10 Proposition 10 102 9: removing a unit entry should preserve the exactness
criterion after transport to the split summand. -/
private theorem exact_and_depth_criterion_iff_of_unit_entry
    [Nontrivial R]
    {C C' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (hsuccPos : 0 < C.rank i.succ)
    (hcastPos : 0 < C.rank i.castSucc)
    (hsplit : C'.rank = FiniteFreeComplex.splitRank C.rank i)
    (eiso : C.toChainComplex ≅
      biprod C'.toChainComplex (identityDisk i)) :
    (C.ExactInPositiveDegrees ↔ C'.ExactInPositiveDegrees) ∧
      (SatisfiesRankMinorIdealDepthCriterion C ↔
        SatisfiesRankMinorIdealDepthCriterion C') := sorry

/-- Helper for Chap10 Proposition 10 102 9: in the minimal local case where every displayed
matrix entry lies in the maximal ideal, exactness is equivalent to the owner depth criterion. -/
private theorem exactInPositiveDegrees_iff_rankMinorIdeal_depth_criterion_of_entries_mem_maximal
    [Nontrivial R]
    (C : _root_.FiniteFreeComplex R e)
    (hmax :
      ∀ i : Fin e, ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R) :
    C.ExactInPositiveDegrees ↔
      SatisfiesRankMinorIdealDepthCriterion C := sorry

/-- Helper for Chap10 Proposition 10 102 9: the owner-facing depth formulation of the
Buchsbaum-Eisenbud exactness criterion. -/
private theorem exactInPositiveDegrees_iff_rankMinorIdeal_depth_criterion
    [Nontrivial R]
    (C : _root_.FiniteFreeComplex R e) :
    C.ExactInPositiveDegrees ↔
      ∀ i : Fin e,
        (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
          (i.1 + 1 : WithTop ℕ) ≤ (I(C.diffAt i)).depth R := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ D : _root_.FiniteFreeComplex R e,
      positiveRankSum D = n →
        (D.ExactInPositiveDegrees ↔
          SatisfiesRankMinorIdealDepthCriterion D)
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D hsum
        by_cases hunit :
            ∃ i : Fin e, ∃ a : Fin (D.rank i.succ), ∃ b : Fin (D.rank i.castSucc),
              IsUnit (D.diffEntry i a b)
        · obtain ⟨i, a, b, hu⟩ := hunit
          obtain ⟨D', hsplit, ⟨eiso⟩⟩ :=
            FiniteFreeComplex.exists_iso_biprod_identityDisk_of_isUnit_diffEntry D i ⟨a, b, hu⟩
          have hlt :
              positiveRankSum D' < positiveRankSum D :=
            positiveRankSum_splitRank_lt_of_unit_entry D D' i ⟨a, b, hu⟩ hsplit
          have hlt' : positiveRankSum D' < n := by
            simpa [hsum] using hlt
          have hrec :
              D'.ExactInPositiveDegrees ↔
                SatisfiesRankMinorIdealDepthCriterion D' :=
            ih (positiveRankSum D') hlt' D' rfl
          have htransport :=
            exact_and_depth_criterion_iff_of_unit_entry
              (lt_of_le_of_lt (Nat.zero_le a.1) a.2)
              (lt_of_le_of_lt (Nat.zero_le b.1) b.2)
              hsplit eiso
          -- Proof comment: the unit-entry branch reduces to the smaller split-rank complex.
          exact htransport.1.trans (hrec.trans htransport.2.symm)
        · have hmax :
              ∀ i : Fin e, ∀ a : Fin (D.rank i.succ), ∀ b : Fin (D.rank i.castSucc),
                D.diffEntry i a b ∈ IsLocalRing.maximalIdeal R := by
            intro i a b
            exact diffEntry_mem_maximal_of_no_unit D hunit i a b
          -- Proof comment: once every entry lies in the maximal ideal, the source proof enters
          -- the minimal local case handled separately.
          exact exactInPositiveDegrees_iff_rankMinorIdeal_depth_criterion_of_entries_mem_maximal D hmax
  simpa [SatisfiesRankMinorIdealDepthCriterion] using
    hP (positiveRankSum C) C rfl

-- Proof sketch: for the forward implication, localize at the associated primes and apply the
-- depth-zero decomposition lemmas to deduce the alternating rank formulas and that each minor ideal
-- avoids every associated prime; prime avoidance then produces a nonzerodivisor allowing
-- induction on the length of the complex to build the required regular sequences. For the reverse
-- implication, localize at nonmaximal primes to invoke the inductive hypothesis on dimension,
-- deduce that any homology is supported only at the maximal ideal, and then apply the acyclicity
-- lemma using the depth bounds supplied by the regular sequences in the minor ideals.
/-! Source-facing wrapper choice: the final clause is packaged by
`ContainsRegularSequenceOfLength` so the public statement keeps the textbook semantics while
avoiding an oversized conjunction surface. -/
/-- Companion bridge: Proposition `10.102.9` rewritten through the owner depth condition on the
rank-minor ideals. -/
theorem exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion
    [Nontrivial R]
    (C : _root_.FiniteFreeComplex R e) :
    C.ExactInPositiveDegrees ↔
      ∀ i : Fin e,
        (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
          (i.1 + 1 : WithTop ℕ) ≤ (I(C.diffAt i)).depth R := by
  -- Proof comment: the public depth bridge is exactly the owner-facing helper theorem proved by
  -- induction on the total positive-degree rank.
  exact exactInPositiveDegrees_iff_rankMinorIdeal_depth_criterion C

/-- Chap10 Proposition 10 102 9

For a bounded finite free complex over a local Noetherian ring, exactness in degrees `e, …, 1`
is equivalent to the Buchsbaum-Eisenbud criterion that each differential has the expected
alternating rank and its rank-minor ideal is either the unit ideal or contains a regular sequence
of the corresponding length. -/
@[stacks 00N1]
theorem exactInPositiveDegrees_iff_buchsbaumEisenbud_criterion
    [Nontrivial R]
    (C : _root_.FiniteFreeComplex R e) :
    C.ExactInPositiveDegrees ↔
      ∀ i : Fin e,
        (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
          (I(C.diffAt i) = ⊤ ∨
            ContainsRegularSequenceOfLength (I(C.diffAt i)) (i.1 + 1)) := by
  -- Proof comment: once the owner depth version is available, the public source-facing theorem is
  -- just the pointwise translation supplied by `criterionClause_iff_le_depth`.
  rw [exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion C]
  constructor
  · intro h i
    rcases h i with ⟨hrank, hdepth⟩
    exact ⟨hrank, (criterionClause_iff_le_depth (I(C.diffAt i)) (i.1 + 1)).mpr hdepth⟩
  · intro h i
    rcases h i with ⟨hrank, hcriterion⟩
    exact
      ⟨hrank,
        (criterionClause_iff_le_depth (I(C.diffAt i)) (i.1 + 1)).mp hcriterion⟩

end FiniteFreeComplex

end
