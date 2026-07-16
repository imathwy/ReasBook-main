import stacks_proof.stacks_project.Chap15.Lemma_15_29_1
import stacks_proof.stacks_project.Chap15.Lemma_15_29_5
import stacks_proof.stacks_project.Chap15.Lemma_15_29_6
import stacks_proof.stacks_project.Chap15.Definition_15_30_1
import stacks_proof.stacks_project.Chap15.Lemma_15_28_4
import stacks_proof.stacks_project.Chap15.Lemma_15_30_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory.Limits
open CategoryTheory
open ComplexShape
open scoped KoszulComplex

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 15.31.1: every positive-length finite family decomposes into its prefix and
terminal value via `Fin.snoc`. -/
private theorem family_eq_snoc_last {s : ℕ} (f : Fin (s + 1) → R) :
    Fin.snoc (fun i : Fin s ↦ f i.castSucc) (f (Fin.last s)) = f := by
  -- Split the index into the terminal branch and the prefix branch.
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro i
    simp [Fin.snoc_castSucc]

/-- Helper for Lemma 15.31.1: updating the terminal entry of a positive-length family is the same
as keeping the prefix and changing only the `Fin.snoc` tail. -/
private theorem update_last_eq_snoc_pow {s : ℕ} (f : Fin (s + 1) → R) (n : ℕ) :
    Function.update f (Fin.last s) (f (Fin.last s) ^ (n + 1)) =
      Fin.snoc (fun i : Fin s ↦ f i.castSucc) (f (Fin.last s) ^ (n + 1)) := by
  -- Away from the last index the update is unchanged, and the last index is replaced by the power.
  let fs : Fin s → R := fun i ↦ f i.castSucc
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [Function.update, Fin.snoc_last]
  · intro i
    simp [Function.update, Fin.snoc_castSucc]

/-- Helper for Lemma 15.31.1: permuting a finite Koszul-regular family preserves
Koszul-regularity. -/
private theorem isKoszulRegularSequence_perm {r : ℕ} (e : Equiv.Perm (Fin r))
    {f : Fin r → R} (hKoszul : IsKoszulRegularSequence f) :
    IsKoszulRegularSequence (fun i ↦ f (e i)) := by
  -- Rewrite both predicates as vanishing of positive Koszul homology.
  rw [isKoszulRegularSequence_iff] at hKoszul ⊢
  intro i hi
  letI : Invertible (e.permMatrix R) := {
    invOf := e⁻¹.permMatrix R
    invOf_mul_self := by
      -- The inverse permutation matrix is the two-sided inverse of the permutation matrix.
      change ((e⁻¹).permMatrix R) * (e.permMatrix R) = 1
      rw [← Matrix.permMatrix_mul]
      simp
    mul_invOf_self := by
      -- The same computation gives the right inverse identity.
      change (e.permMatrix R) * ((e⁻¹).permMatrix R) = 1
      rw [← Matrix.permMatrix_mul]
      simp
  }
  let ek :
      K^•(f) ≅ K^•(fun j ↦ f (e j)) := by
    -- The permutation matrix acts on coordinate vectors by precomposition with the permutation.
    simpa [Matrix.toLin'_apply, Matrix.permMatrix_mulVec] using
      (koszul_complex_on_matrix_linear_combination_iso (e.permMatrix R) f)
  -- Transport homology vanishing across the Koszul-complex isomorphism from Lemma `15.28.4`.
  exact (CategoryTheory.Iso.isZero_iff (HomologicalComplex.homologyMapIso ek i)).mp
    (hKoszul i hi)

/-- Helper for Lemma 15.31.1: replacing the last entry of a Koszul-regular family by any positive
power preserves Koszul-regularity. -/
private theorem isKoszulRegularSequence_snoc_pow {s : ℕ} {fs : Fin s → R} {a : R} (n : ℕ)
    (hKoszul : IsKoszulRegularSequence (Fin.snoc fs a)) :
    IsKoszulRegularSequence (Fin.snoc fs (a ^ (n + 1))) := by
  induction n with
  | zero =>
      -- The first positive power is the original family.
      simpa using hKoszul
  | succ n ih =>
      -- Multiply the last entry by one additional copy of `a` and use Lemma `15.30.4`.
      have hmul :
          IsKoszulRegularSequence (Fin.snoc fs (a ^ (n + 1) * a)) :=
        IsKoszulRegularOn.snoc_mul ih hKoszul
      simpa [pow_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmul

/-- Helper for Lemma 15.31.1: swapping the chosen coordinate with the last one turns the
last-coordinate power update back into the original coordinate update. -/
private theorem swap_update_last_eq_update {s : ℕ} (f : Fin (s + 1) → R) (j : Fin (s + 1))
    (n : ℕ) :
    (fun i ↦
      Function.update (fun k ↦ f ((Equiv.swap j (Fin.last s)) k)) (Fin.last s) (f j ^ (n + 1))
        ((Equiv.swap j (Fin.last s)) i)) =
      Function.update f j (f j ^ (n + 1)) := by
  -- Check the updated family coordinatewise, using that the transposition is an involution.
  funext i
  by_cases hij : i = j
  · subst hij
    simp [Function.update]
  · by_cases hlast : i = Fin.last s
    · subst hlast
      have hjlast : j ≠ Fin.last s := by
        simpa [eq_comm] using hij
      simp [Function.update, hij, hjlast]
    · have hswap : Equiv.swap j (Fin.last s) i = i :=
        Equiv.swap_apply_of_ne_of_ne hij hlast
      simp [Function.update, hij, hlast, hswap]

/-- Helper for Lemma 15.31.1: replacing any chosen entry of a Koszul-regular family by a positive
power preserves Koszul-regularity. -/
private theorem isKoszulRegularSequence_update_pow {r : ℕ} (f : Fin r → R) (j : Fin r) (n : ℕ)
    (hKoszul : IsKoszulRegularSequence f) :
    IsKoszulRegularSequence (Function.update f j (f j ^ (n + 1))) := by
  cases r with
  | zero =>
      exact Fin.elim0 j
  | succ s =>
      let e : Equiv.Perm (Fin (s + 1)) := Equiv.swap j (Fin.last s)
      let g : Fin (s + 1) → R := fun i ↦ f (e i)
      have hperm : IsKoszulRegularSequence g := by
        -- Move the chosen coordinate to the terminal position.
        simpa [g] using isKoszulRegularSequence_perm e hKoszul
      have hsnoc : IsKoszulRegularSequence
          (Fin.snoc (fun i : Fin s ↦ g i.castSucc) (g (Fin.last s))) := by
        -- Re-express the permuted family in `Fin.snoc` form to use the source-proof power step.
        simpa [family_eq_snoc_last g] using hperm
      have hpow :
          IsKoszulRegularSequence
            (Fin.snoc (fun i : Fin s ↦ g i.castSucc) (g (Fin.last s) ^ (n + 1))) := by
        -- Apply the last-coordinate power lemma to the permuted family.
        exact isKoszulRegularSequence_snoc_pow n hsnoc
      have hupdate_last :
          IsKoszulRegularSequence
            (Function.update g (Fin.last s) (g (Fin.last s) ^ (n + 1))) := by
        -- Rewrite the last-coordinate update back into `Function.update`.
        simpa [update_last_eq_snoc_pow g n] using hpow
      have hback :
          IsKoszulRegularSequence
            (fun i ↦
              Function.update g (Fin.last s) (g (Fin.last s) ^ (n + 1)) (e i)) := by
        -- Undo the permutation to return to the original coordinate order.
        simpa [g] using isKoszulRegularSequence_perm e hupdate_last
      -- The transposed update is exactly the original single-coordinate power update.
      simpa [g, e, swap_update_last_eq_update f j n] using hback

/-- Helper for Lemma 15.31.1: replacing every entry of a Koszul-regular family by the same
positive power preserves Koszul-regularity. -/
private theorem isKoszulRegularSequence_pow_family {r : ℕ} (f : Fin r → R) (n : ℕ)
    (hKoszul : IsKoszulRegularSequence f) :
    IsKoszulRegularSequence (fun j ↦ f j ^ (n + 1)) := by
  -- Follow the source proof: update one coordinate at a time by a positive power.
  let s : Finset (Fin r) := Finset.univ
  let g : Finset (Fin r) → (Fin r → R)
    | t => fun j ↦ if j ∈ t then f j ^ (n + 1) else f j
  have hg_empty : g ∅ = f := by
    -- Initially no coordinate has been powered.
    funext j
    simp [g]
  have hg_step :
      ∀ {t : Finset (Fin r)} {j : Fin r}, j ∉ t →
        g (insert j t) = Function.update (g t) j (f j ^ (n + 1)) := by
    intro t j hj
    -- Inserting `j` powers exactly one new coordinate.
    funext k
    by_cases hkj : k = j
    · subst hkj
      simp [g]
    · by_cases hk : k ∈ t
      · simp [g, hk, hkj, Finset.mem_insert, hk]
      · simp [g, hk, hkj, Finset.mem_insert, hk]
  have hg_all : g s = fun j ↦ f j ^ (n + 1) := by
    -- At the end every coordinate belongs to `Finset.univ`.
    funext j
    simp [g, s]
  have hstep :
      ∀ t : Finset (Fin r), IsKoszulRegularSequence (g t) := by
    intro t
    refine Finset.induction_on t ?base ?step
    · -- Start from the original family.
      simpa [hg_empty] using hKoszul
    · intro j t hjt ht
      -- Power one additional coordinate and use the single-coordinate update lemma.
      rw [hg_step (t := t) (j := j) hjt]
      have hgj : g t j = f j := by
        simp [g, hjt]
      simpa [hgj] using isKoszulRegularSequence_update_pow (g t) j n ht
  -- Evaluate the induction at the full set of coordinates.
  simpa [hg_all] using hstep s

/-- Helper for Lemma 15.31.1: the `n`th powered Koszul stage in the cohomological grading used by
Lemma `15.29.6`. -/
private abbrev powered_koszul_cochain_stage {r : ℕ} (f : Fin r → R) (n : ℕ) :
    CochainComplex (ModuleCat R) ℕ :=
  (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).restriction embeddingUpNat)

/-- Helper for Lemma 15.31.1: after extending the powered Koszul complex to the cohomological
grading, the degree `-1` term is zero because it comes from exterior degree `r + 1`. -/
private theorem powered_koszul_extend_neg_one_is_zero {r : ℕ} (f : Fin r → R) (n : ℕ) :
    IsZero (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).X (-1 : ℤ)) := by
  have hterm : IsZero ((K^•[n](f)).X (r + 1)) := by
    change IsZero ((ModuleCat.of R (Fin r → R)).exteriorPower (r + 1))
    rw [ModuleCat.isZero_iff_subsingleton]
    let B :
        Module.Basis (Set.powersetCard (Fin r) (r + 1)) R
          ↥(⋀[R]^(r + 1) (Fin r → R)) :=
      Module.Basis.exteriorPower (r + 1) (Pi.basisFun R (Fin r))
    have hempty : IsEmpty (Set.powersetCard (Fin r) (r + 1)) := by
      refine ⟨fun s ↦ ?_⟩
      have hs : ((s : Finset (Fin r)).card) = r + 1 := by
        simpa using s.2
      have hsle : ((s : Finset (Fin r)).card) ≤ r := by
        simpa using Finset.card_le_univ (s := (s : Finset (Fin r)))
      omega
    -- Proof comment: the exterior-power basis is indexed by `(r + 1)`-element subsets of
    -- `Fin r`, but that index type is empty, so every vector has zero coordinates.
    refine ⟨fun x y ↦ ?_⟩
    apply B.repr.injective
    have hx : B.repr x = 0 := Subsingleton.elim _ _
    have hy : B.repr y = 0 := Subsingleton.elim _ _
    exact hx.trans hy.symm
  let e :
      (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).X (-1 : ℤ)) ≅
        ((K^•[n](f)).X (r + 1)) :=
    (K^•[n](f)).extendXIso (embeddingUpIntLE (r : ℤ)) (by
      dsimp [ComplexShape.embeddingUpIntLE]
      omega)
  -- Proof comment: `extendXIso` identifies cohomological degree `-1` with chain degree `r + 1`.
  exact (CategoryTheory.Iso.isZero_iff e).mpr hterm

/-- Helper for Lemma 15.31.1: in the full reindexed powered Koszul short complex around degree
`0`, the map into cycles vanishes because its source object is zero. -/
private theorem powered_koszul_full_sc_zero_to_cycles_eq_zero {r : ℕ} (f : Fin r → R) (n : ℕ) :
    ((((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).sc' (-1) 0 1).toCycles) = 0 := by
  let S := (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).sc' (-1) 0 1)
  let hzero := powered_koszul_extend_neg_one_is_zero (f := f) n
  -- Proof comment: any morphism out of the zero predecessor term is zero.
  simpa [S] using hzero.eq_of_src S.toCycles 0

/-- Helper for Lemma 15.31.1: in the full reindexed powered Koszul complex, degree-`0` cycles
already compute degree-`0` homology because the predecessor term is zero. -/
private noncomputable def powered_koszul_full_cycles_to_homology_iso_zero
    {r : ℕ} (f : Fin r → R) (n : ℕ) :
    (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).cycles (0 : ℤ)) ≅
      (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).homology (0 : ℤ)) := by
  let K := ((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ)))
  let S : CategoryTheory.ShortComplex (ModuleCat R) := K.sc' (-1) 0 1
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  let inv : S.homology ⟶ S.cycles :=
    S.descHomology (𝟙 _) (by
      -- Proof comment: the predecessor differential vanishes, so the identity on cycles
      -- descends to homology.
      simpa [S, K] using powered_koszul_full_sc_zero_to_cycles_eq_zero (f := f) n)
  have hπinv : S.homologyπ ≫ inv = 𝟙 S.cycles := by
    -- Proof comment: this is the defining computation rule for `descHomology`.
    exact
      ShortComplex.π_descHomology (S := S) (k := 𝟙 _)
        (hk := by
          simpa [S, K] using powered_koszul_full_sc_zero_to_cycles_eq_zero (f := f) n)
  let eShort : S.cycles ≅ S.homology :=
    { hom := S.homologyπ
      inv := inv
      hom_inv_id := hπinv
      inv_hom_id := by
        -- Proof comment: `homologyπ` is epi, so the left inverse is automatically a right inverse.
        apply (cancel_epi S.homologyπ).1
        calc
          S.homologyπ ≫ (inv ≫ S.homologyπ) = (S.homologyπ ≫ inv) ≫ S.homologyπ := by
            simp [Category.assoc]
          _ = 𝟙 S.cycles ≫ S.homologyπ := by
            rw [hπinv]
          _ = S.homologyπ := by
            simp
          _ = S.homologyπ ≫ 𝟙 S.homology := by
            simp }
  -- Proof comment: move between ambient cycles/homology and the owner short complex once.
  exact
    (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK) ≪≫
      eShort ≪≫
      (K.homologyIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Lemma 15.31.1: restricting the reindexed powered Koszul stage to nonnegative
degrees does not change the degree-`0` cycles. -/
private noncomputable def powered_koszul_stage_cycles_iso_zero {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    (powered_koszul_cochain_stage f n).cycles 0 ≅
      (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).cycles (0 : ℤ)) := by
  let K := ((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ)))
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let Sr : CategoryTheory.ShortComplex (ModuleCat R) := Kr.sc' 0 0 1
  let Sf : CategoryTheory.ShortComplex (ModuleCat R) := K.sc' (-1) 0 1
  let e0 : Kr.X 0 ≅ K.X (0 : ℤ) :=
    K.restrictionXIso ComplexShape.embeddingUpNat rfl
  let e1 : Kr.X 1 ≅ K.X (1 : ℤ) :=
    K.restrictionXIso ComplexShape.embeddingUpNat rfl
  have hprevKr : (ComplexShape.up ℕ).prev 0 = 0 := by
    simp [CochainComplex.prev]
  have hnextKr : (ComplexShape.up ℕ).next 0 = 1 := by
    simpa using (CochainComplex.next ℕ 0)
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  have hd :
      Kr.d 0 1 ≫ e1.hom = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
    -- Proof comment: expand the restricted differential once so both cycle objects are kernels
    -- of the same full outgoing differential.
    rw [HomologicalComplex.restriction_d_eq
      (K := K) (e := ComplexShape.embeddingUpNat) (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    calc
      ((e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ e1.inv) ≫ e1.hom) =
          e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ (e1.inv ≫ e1.hom) := by
            simp [Category.assoc]
      _ = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
            simp
  -- Proof comment: compare both cycle objects on the kernel surface before passing to homology.
  exact
    (Kr.cyclesIsoSc' 0 0 1 hprevKr hnextKr) ≪≫
      Sr.cyclesIsoKernel ≪≫
      CategoryTheory.Limits.kernel.mapIso (Kr.d 0 1) (K.d (0 : ℤ) (1 : ℤ)) e0 e1 hd ≪≫
      Sf.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Lemma 15.31.1: the degree-`0` homology of the restricted powered Koszul stage is
the top Koszul homology of the powered family. -/
private noncomputable def powered_koszul_stage_homology_zero_iso {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    (powered_koszul_cochain_stage f n).homology 0 ≅
      (K^•[n](f)).homology r := by
  let K := ((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ)))
  -- Proof comment: compare the restricted degree-`0` homology with restricted cycles, then with
  -- full cycles, then with full degree-`0` homology, and finally undo the cohomological reindexing.
  exact
    (CochainComplex.isoHomologyπ₀ (powered_koszul_cochain_stage f n)).symm ≪≫
      powered_koszul_stage_cycles_iso_zero (f := f) n ≪≫
      powered_koszul_full_cycles_to_homology_iso_zero (f := f) n ≪≫
      ((K^•[n](f)).extendHomologyIso (embeddingUpIntLE (r : ℤ)) (by
        dsimp [ComplexShape.embeddingUpIntLE]
        omega))

/-- Helper for Lemma 15.31.1: stagewise vanishing of degree-`i` homology in a sequential diagram
of `ℕ`-graded cochain complexes implies vanishing of the degree-`i` homology of the colimit. -/
private theorem colimit_homology_isZero_of_exact_sequential_nat
    (S : CategoryTheory.Functor ℕ (CochainComplex (ModuleCat R) ℕ)) (i : ℕ)
    (hS : ∀ n : ℕ, IsZero ((S.obj n).homology i)) :
    IsZero ((colimit S).homology i) := by
  -- TODO: turn the stagewise zero homology hypothesis into exactness of the degree-`i` short
  -- complexes in the functor category, pass exactness through the sequential colimit in
  -- `ModuleCat R`, and identify the resulting colimit short complex with `(colimit S).sc i`.
  sorry

/-- Helper for Lemma 15.31.1: in positive degree, the restricted powered Koszul stage computes
the complementary powered Koszul homology. -/
private noncomputable def powered_koszul_stage_homology_iso_of_pos {r : ℕ}
    (f : Fin r → R) (n i : ℕ) (hi : 0 < i) (hir : i ≤ r) :
    (powered_koszul_cochain_stage f n).homology i ≅
      (K^•[n](f)).homology (r - i) := by
  let K := ((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ)))
  cases i with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 hi)
  | succ j =>
      have hres :
          (K.restriction ComplexShape.embeddingUpNat).homology (j + 1) ≅
            K.homology ((j + 1 : ℕ) : ℤ) := by
        -- In successor degree, the standard restriction homology comparison applies directly.
        simpa using
          (HomologicalComplex.restrictionHomologyIso
            K ComplexShape.embeddingUpNat j (j + 1) (j + 2)
            (by simp) (by simp)
            (by simp : ComplexShape.embeddingUpNat.f j = ((j : ℕ) : ℤ))
            (by simp : ComplexShape.embeddingUpNat.f (j + 1) = ((j + 1 : ℕ) : ℤ))
            (by norm_num : ComplexShape.embeddingUpNat.f (j + 2) = ((j + 2 : ℕ) : ℤ))
            (by simp)
            (by
              calc
                (ComplexShape.up ℤ).next (((j + 1 : ℕ) : ℤ)) = (((j + 1 : ℕ) : ℤ) + 1) := by
                  simpa using (CochainComplex.next ℤ (((j + 1 : ℕ) : ℤ)))
                _ = ((j + 2 : ℕ) : ℤ) := by omega))
      -- Undo the cohomological reindexing `p ↦ r - p`.
      exact hres ≪≫
        ((K^•[n](f)).extendHomologyIso (embeddingUpIntLE (r : ℤ)) (by
          dsimp [ComplexShape.embeddingUpIntLE]
          omega))

/-- Helper for Lemma 15.31.1: in every positive lower degree, the powered Koszul stage has zero
homology because the complementary powered Koszul homology is positive and the powered family is
still Koszul-regular. -/
private theorem powered_koszul_stage_homology_is_zero_of_succ_lt {r : ℕ}
    (f : Fin r → R) (hKoszul : IsKoszulRegularSequence f) (n i : ℕ) (hi : i.succ < r) :
    IsZero ((powered_koszul_cochain_stage f n).homology i.succ) := by
  have hpow_family :
      IsKoszulRegularSequence (fun j ↦ f j ^ (n + 1)) :=
    isKoszulRegularSequence_pow_family f n hKoszul
  rw [isKoszulRegularSequence_iff] at hpow_family
  have hpos : 0 < i.succ := Nat.succ_pos _
  have hir : i.succ ≤ r := Nat.le_of_lt hi
  have hcomp_pos : 1 ≤ r - i.succ := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hi)
  -- Positive stage degree `i + 1` identifies with complementary positive Koszul homology.
  exact (CategoryTheory.Iso.isZero_iff
    (powered_koszul_stage_homology_iso_of_pos (f := f) n i.succ hpos hir)).mpr
      (hpow_family (r - i.succ) hcomp_pos)

/-- Helper for Lemma 15.31.1: the source proof reduces the degrees `i < r` to the powered Koszul
stages from Lemma `15.29.6`, and this helper isolates the remaining lower-degree transport. -/
private theorem extendedAlternatingCechComplex_homology_isZero_of_lt_of_isKoszulRegularSequence
    {r : ℕ} (f : Fin r → R) (hKoszul : IsKoszulRegularSequence f) {i : ℕ} (hi : i < r) :
    IsZero ((extendedAlternatingCechComplex f R).homology i) := by
  -- TODO: split the degree `i` into the boundary case `i = 0` and the successor case `i = j + 1`,
  -- use `powered_koszul_stage_homology_zero_iso` for the boundary branch and
  -- `powered_koszul_stage_homology_is_zero_of_succ_lt` for the positive branch, then pass the
  -- resulting stagewise vanishing through `colimit_homology_isZero_of_exact_sequential_nat` and
  -- finally transport across `extendedAlternatingCechComplex_iso_colimit_koszulPowerCochainSystem`.
  sorry

-- Proof sketch: by Lemma 15.30.4 and induction, replacing any entry of a Koszul-regular sequence
-- by a positive power preserves Koszul-regularity, and Lemma 15.28.4 lets us permute the sequence.
-- Hence each powered family `(fun i ↦ f i ^ (n + 1))` is still Koszul-regular, so its Koszul
-- complex has vanishing positive homology. Lemma 15.29.6 identifies the extended alternating Čech
-- complex with the colimit of these Koszul complexes, from which the only possible nonvanishing
-- cohomology degree is the top degree `r`.
/-- Lemma 15.31.1: if `f : Fin r → R` is a Koszul-regular sequence, then the extended alternating
Čech complex attached to `f` has vanishing cohomology in every degree `i ≠ r`. -/
@[stacks 0G6L]
theorem extendedAlternatingCechComplex_homology_isZero_of_isKoszulRegularSequence {r : ℕ}
    (f : Fin r → R) (hKoszul : IsKoszulRegularSequence f) (i : ℕ) (hi : i ≠ r) :
    IsZero ((extendedAlternatingCechComplex f R).homology i) := by
  -- Split off the upper-degree vanishing, which is already public from Lemma `15.29.5`.
  rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
  · -- The remaining lower-degree source argument is isolated in the helper above.
    exact extendedAlternatingCechComplex_homology_isZero_of_lt_of_isKoszulRegularSequence
      f hKoszul hlt
  · -- Above the top degree, the extended alternating Čech complex vanishes independently of
    -- regularity, so the source proof only needs the lower-degree powered-Koszul transport.
    simpa using
      (extendedAlternatingCechCohomology_isZero_of_gt
        (R := R) (M := R) (f := f) (q := i) hgt)

end RingTheory.Sequence
