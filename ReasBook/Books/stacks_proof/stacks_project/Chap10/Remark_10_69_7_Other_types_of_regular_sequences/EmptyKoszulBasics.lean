import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_28_11
import StacksProject_2024.Chap15.Definition_15_30_1

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Chap10 Remark 10 69 7 Other types of regular sequences: `koszulComplexOn f`
is the family-level Koszul complex `K^•(f)` attached to the tuple linear form
`koszulLinearForm f`. -/
noncomputable abbrev koszulComplexOn {r : ℕ} (f : Fin r → R) :
    ChainComplex (ModuleCat R) ℕ :=
  koszulComplex (koszulLinearForm f)

/-- Helper for Chap10 Remark 10 69 7 Other types of regular sequences: the degree-`n` object of
`koszulComplexOn f` is the `n`th exterior power of the finite free module on the index set. -/
theorem koszulComplexOn_X {r : ℕ} (f : Fin r → R) (n : ℕ) :
    (koszulComplexOn f).X n = (ModuleCat.of R (Fin r → R)).exteriorPower n :=
  rfl

/-- Helper for Chap10 Remark 10 69 7 Other types of regular sequences: the finite-family linear
form is the canonical `koszulLinearForm`. -/
noncomputable abbrev koszulFamilyLinearMap {r : ℕ} (f : Fin r → R) :
    (Fin r → R) →ₗ[R] R :=
  koszulLinearForm f

/-- Helper for Chap10 Remark 10 69 7 Other types of regular sequences: the finite-family Koszul
linear form evaluates the basis vector at the corresponding entry of the family. -/
theorem koszulFamilyLinearMap_basis {r : ℕ} (f : Fin r → R) (i : Fin r) :
    koszulFamilyLinearMap f (Pi.basisFun R (Fin r) i) = f i := by
  simp [koszulFamilyLinearMap, koszulLinearForm, Module.piEquiv_apply_apply, Pi.single_apply]

/-- Helper for Chap10 Remark 10 69 7 Other types of regular sequences: coercing the restricted
Koszul differential back to the ambient exterior algebra gives contraction by the defining
linear form. -/
@[simp] theorem koszulDifferentialLinearMap_apply
    {E : Type u} [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (n : ℕ)
    (x : ⋀[R]^(n + 1) E) :
    (koszulDifferentialLinearMap φ n x : ExteriorAlgebra R E) =
      CliffordAlgebra.contractLeft φ x :=
  rfl

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the finite-family owner
criterion for `rs.get` is exactly vanishing of the positive homology of its Koszul complex. -/
theorem isKoszulRegularSequence_get_iff {rs : List R} :
    IsKoszulRegularSequence rs.get ↔
      ∀ i : ℕ, 1 ≤ i → CategoryTheory.Limits.IsZero ((koszulComplexOn rs.get).homology i) := by
  -- This is just the Chapter 15 owner characterization specialized to the list family `rs.get`.
  simpa using (isKoszulRegularSequence_iff (f := rs.get))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the positive-cardinality subsets
of `Fin 0` do not exist. -/
theorem powersetCard_fin_zero_isEmpty {n : ℕ} (hn : 1 ≤ n) :
    IsEmpty (Set.powersetCard (Fin 0) n) := by
  classical
  -- Any candidate subset of `Fin 0` is empty, so its cardinality cannot be positive.
  refine ⟨fun s => ?_⟩
  have : False := by
    have hs : (s.1 : Finset (Fin 0)) = ∅ := Finset.eq_empty_of_isEmpty _
    have hzero : n = 0 := by
      simpa [hs] using s.2.symm
    exact Nat.ne_of_lt hn hzero.symm
  exact this.elim

/-- Helper for Remark 10.69.7 (Other types of regular sequences): every positive exterior power of
the zero free module on `Fin 0` is a zero object. -/
theorem fin_zero_exteriorPower_isZero {n : ℕ} (hn : 1 ≤ n) :
    IsZero ((ModuleCat.of R (Fin 0 → R)).exteriorPower n) := by
  classical
  let b : Module.Basis (Fin 0) R (Fin 0 → R) := Pi.basisFun R (Fin 0)
  haveI : IsEmpty (Set.powersetCard (Fin 0) n) := powersetCard_fin_zero_isEmpty (n := n) hn
  haveI : Subsingleton ↑(((ModuleCat.of R (Fin 0 → R)).exteriorPower n)) := by
    -- Identify the exterior power with functions on the empty basis index set.
    change Subsingleton (⋀[R]^n (Fin 0 → R))
    exact Equiv.subsingleton ((b.exteriorPower n).equivFun).toEquiv
  exact ModuleCat.isZero_of_subsingleton ((ModuleCat.of R (Fin 0 → R)).exteriorPower n)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): subsets of `Fin 1` have
cardinality at most `1`, so no subset has cardinality at least `2`. -/
theorem powersetCard_fin_one_isEmpty {n : ℕ} (hn : 2 ≤ n) :
    IsEmpty (Set.powersetCard (Fin 1) n) := by
  classical
  refine ⟨fun s => ?_⟩
  have hs_le : ((s.1 : Finset (Fin 1)).card) ≤ 1 := by
    simpa using Finset.card_le_univ (s := (s.1 : Finset (Fin 1)))
  have hs_card : ((s.1 : Finset (Fin 1)).card) = n := by
    simpa using s.2
  have : False := by
    omega
  exact this.elim

/-- Helper for Remark 10.69.7 (Other types of regular sequences): every exterior power of the
rank-one free module in degree at least `2` is zero. -/
theorem fin_one_exteriorPower_isZero {n : ℕ} (hn : 2 ≤ n) :
    IsZero ((ModuleCat.of R (Fin 1 → R)).exteriorPower n) := by
  classical
  let b : Module.Basis (Fin 1) R (Fin 1 → R) := Pi.basisFun R (Fin 1)
  haveI : IsEmpty (Set.powersetCard (Fin 1) n) := powersetCard_fin_one_isEmpty (n := n) hn
  haveI : Subsingleton ↑(((ModuleCat.of R (Fin 1 → R)).exteriorPower n)) := by
    -- Identify the exterior power with functions on the empty basis index set.
    change Subsingleton (⋀[R]^n (Fin 1 → R))
    exact Equiv.subsingleton ((b.exteriorPower n).equivFun).toEquiv
  exact ModuleCat.isZero_of_subsingleton ((ModuleCat.of R (Fin 1 → R)).exteriorPower n)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the singleton Koszul complex
has no terms above degree `1`. -/
theorem koszulComplexOn_singleton_X_isZero_of_two_le {A : Type u} [CommRing A] {r : A} {n : ℕ}
    (hn : 2 ≤ n) :
    IsZero ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).X n) := by
  -- The source route isolates the singleton head case by observing that all higher exterior powers
  -- of the rank-one free module already vanish.
  simpa [koszulComplexOn_X] using fin_one_exteriorPower_isZero (R := A) hn

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the source-facing family carried
by the singleton list `[r]` is the canonical `Fin.cons` family. -/
theorem singleton_list_get_eq_fin_cons {A : Type u} [CommRing A] {r : A} :
    ([r] : List A).get = (Fin.cons r (Fin.elim0 : Fin 0 → A)) := by
  -- Both sides have exactly one value, namely `r` at the unique index of `Fin 1`.
  ext i
  fin_cases i
  rfl

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the empty sequence is
Koszul-regular. -/
theorem isKoszulRegularSequence_nil :
    IsKoszulRegularSequence (R := R) (Fin.elim0 : Fin 0 → R) := by
  rw [isKoszulRegularSequence_iff]
  intro i hi
  -- In positive degree, the empty Koszul complex has zero middle object.
  have hXi : IsZero ((koszulComplexOn (R := R) (Fin.elim0 : Fin 0 → R)).X i) := by
    simpa [koszulComplexOn_X] using fin_zero_exteriorPower_isZero (R := R) hi
  have hsc : IsZero (((koszulComplexOn (R := R) (Fin.elim0 : Fin 0 → R)).sc i).X₂) := by
    simpa using hXi
  -- The associated homology therefore vanishes in every positive degree.
  simpa [HomologicalComplex.homology] using
    (ShortComplex.isZero_homology_of_isZero_X₂
      ((koszulComplexOn (R := R) (Fin.elim0 : Fin 0 → R)).sc i) hsc)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the empty Koszul complex is the
degree-zero single complex on the base ring. -/
noncomputable def empty_koszulComplexOn_iso_single₀ {A : Type u} [CommRing A] :
    koszulComplexOn (R := A) (Fin.elim0 : Fin 0 → A) ≅
      (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) := by
  let C := koszulComplexOn (R := A) (Fin.elim0 : Fin 0 → A)
  let X0 : ModuleCat A := ModuleCat.of A A
  let hposZero : ∀ n : ℕ, IsZero (C.X (n + 1)) := by
    intro n
    -- Positive degrees of the empty Koszul complex are the positive exterior powers of `A^0`.
    simpa [C, koszulComplexOn_X] using
      fin_zero_exteriorPower_isZero (R := A) (n := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let toSingle : C ⟶ (ChainComplex.single₀ (ModuleCat A)).obj X0 :=
    (ChainComplex.toSingle₀Equiv C X0).symm
      ⟨(ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom, by
        -- The degree-`1` source already vanishes, so the augmentation compatibility is automatic.
        exact (hposZero 0).eq_of_src _ _⟩
  let fromSingle : (ChainComplex.single₀ (ModuleCat A)).obj X0 ⟶ C :=
    (ChainComplex.fromSingle₀Equiv C X0).symm
      ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv)
  refine { hom := toSingle, inv := fromSingle, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply HomologicalComplex.hom_ext
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- In degree `0`, the two maps reduce to the inverse equivalence on exterior power `0`.
      change toSingle.f 0 ≫ fromSingle.f 0 = 𝟙 _
      simpa [toSingle, fromSingle] using
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom_inv_id
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      -- In positive degrees, the empty Koszul complex is already zero.
      exact (hposZero n).eq_of_src _ _
  · apply HomologicalComplex.hom_ext
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- In degree `0`, the single complex and the empty Koszul complex identify through `iso₀`.
      change fromSingle.f 0 ≫ toSingle.f 0 = 𝟙 _
      simpa [toSingle, fromSingle] using
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv_hom_id
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      have hsingle :
          IsZero (((ChainComplex.single₀ (ModuleCat A)).obj X0).X (n + 1)) := by
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 X0 (n + 1) (by simp)
      -- Positive degrees of the target `single₀` complex are zero as well.
      exact hsingle.eq_of_src _ _

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the empty sequence is
Koszul-regular on any coefficient module. -/
theorem isKoszulRegularOn_nil {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] :
    IsKoszulRegularOn M (Fin.elim0 : Fin 0 → A) := by
  intro i hi
  let K :=
    ((tensorLeft (ModuleCat.of A M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplexOn (R := A) (Fin.elim0 : Fin 0 → A))
  have hXi : IsZero (K.X i) := by
    -- Positive degrees of the empty family Koszul complex are zero, and tensoring preserves zero
    -- objects.
    have hZ : IsZero ((ModuleCat.of A (Fin 0 → A)).exteriorPower i) :=
      fin_zero_exteriorPower_isZero (R := A) hi
    simpa [K, koszulComplexOn, koszulLinearForm] using
      ((tensorLeft (ModuleCat.of A M)).map_isZero hZ)
  have hExact : K.ExactAt i := by
    apply ShortComplex.exact_of_isZero_X₂
    exact hXi
  simpa [IsKoszulRegularOn, K, koszulComplexOn] using hExact.isZero_homology

end RingTheory.Sequence
