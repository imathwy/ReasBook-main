import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_27_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_27_9
import StacksProject_2024.stacks_project.Chap13.Lemma_13_21_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_21_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_27_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7
import StacksProject_2024.stacks_project.Chap15.Definition_15_70_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_16.SpectralComparison
import StacksProject_2024.stacks_project.Chap15.Lemma_15_70_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "DMod" => DerivedCategory Mod
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "Hb" => boundedDerivedHomologyFunctor Mod
local notation "single₀" => DerivedCategory.singleFunctor Mod (0 : ℤ)
local notation "singleCpx₀" => CochainComplex.singleFunctor Mod (0 : ℤ)

/-
Domain-style sampling for Lemma 15.70.5:
- primary domain: finite injective dimension in `D(R)`, together with bounded derived objects and
  bounded cochain-complex presentations;
- sampled owner declarations:
  `HasFiniteInjectiveDimension`,
  `injectiveDimension`,
  `DbMod`,
  `boundedDerivedHomologyFunctor`,
  `DerivedCategory.homologyFunctor`,
  `t.bounded`,
  `Compᵇ(Mod)`;
- best owner abstraction: the source-facing statements stay about finite injective dimension,
  while boundedness in `D(R)` should be stated directly on the chapter owner
  `DbMod`, and the representative-level bounded-complex hypothesis should reuse the
  chapter owner `Compᵇ(Mod)` rather than a raw cochain complex together with separate
  support-bound witnesses;
  finite injective dimension for modules is already canonically owned by `injectiveDimension`,
  and the bounded-derived cohomology objects should be read through the chapter owner
  `boundedDerivedHomologyFunctor`, so the hypotheses below should use
  `injectiveDimension _ ≠ ⊤` directly on `((Hb i).obj K)`;
- primitive vs. derived:
  primitive data are the bounded derived object `K : DbMod` in part `(1)`, read through the
  chapter owner `Hb i`,
  the bounded representative complex `K' : Compᵇ(Mod)` in part `(2)`, and the module-level
  finite-injective-dimension hypotheses on cohomology objects or terms;
  derived API is the resulting `HasFiniteInjectiveDimension` conclusion, stated in part `(2)`
  directly for the represented object `Q.obj K'.obj`;
- source/core/bridge triage:
  `source-facing`: the two finite-injective-dimension theorems below;
  `core/canonical`: `HasFiniteInjectiveDimension`, `injectiveDimension`,
    `DbMod`, `Hb`,
    `DerivedCategory.homologyFunctor`, `t.bounded`, and
    `Compᵇ(Mod)`;
  `bridge/view`: passage from a chosen representative `K'` to an arbitrary isomorphic derived
  object, which is not kept in the main public theorem statement.
-/

-- Proof sketch: apply the Ext spectral sequence of Lemma `13.21.3` to the functor
-- `Hom_R(N, -)` and use the boundedness of `K` together with the finite injective-dimension
-- bounds on the cohomology objects `H^i(K)` to deduce eventual vanishing of
-- `Ext^n_R(N, K)` for every module `N`; then conclude from the criterion of Lemma `15.70.2`.
/-- Helper for Lemma 15.70.5: finitely many bounded-derived cohomology modules with finite
injective dimension admit one common natural-number bound on an interval `[c, d]`. -/
lemma exists_common_injective_dimension_bound_on_bounded_support
    (K : DbMod) (c d : ℤ)
    (hH : ∀ i : ℤ, injectiveDimension ((Hb i).obj K) ≠ ⊤) :
    ∃ m : ℕ,
      ∀ i : ℤ, c ≤ i → i ≤ d → injectiveDimension ((Hb i).obj K) ≤ m := by
  classical
  let bound : ℤ → ℕ := fun i ↦
    Classical.choose ((injectiveDimension_ne_top_iff ((Hb i).obj K)).1 (hH i))
  let m : ℕ := (Finset.Icc c d).sup bound
  refine ⟨m, ?_⟩
  intro i hci hid
  have hi_mem : i ∈ Finset.Icc c d := by
    simp [Finset.mem_Icc, hci, hid]
  have hle_bound : injectiveDimension ((Hb i).obj K) ≤ bound i := by
    -- Convert the chosen `HasInjectiveDimensionLE` witness into an explicit owner inequality.
    exact
      (injectiveDimension_le_iff ((Hb i).obj K) (bound i)).2
        (Classical.choose_spec
          ((injectiveDimension_ne_top_iff ((Hb i).obj K)).1 (hH i)))
  have hsup : (bound i : WithBot ℕ∞) ≤ m := by
    exact_mod_cast Finset.le_sup hi_mem
  -- Take the maximum over the finite interval `[c, d]`.
  exact le_trans hle_bound hsup

/-- Helper for Lemma 15.70.5: the derived image of a bounded cochain complex defines an object of
`D^b(R)`. -/
lemma q_obj_mem_t_bounded_of_bounded_complex
    (K : Compᵇ(Mod)) :
    (t.bounded : ObjectProperty (DerivedCategory Mod)) (Q.obj K.obj) := by
  rcases (CochainComplex.bounded_iff Mod K.obj).1 K.property with ⟨hplus, hminus⟩
  change (∃ n, (Q.obj K.obj).IsGE n) ∧ ∃ n, (Q.obj K.obj).IsLE n
  constructor
  · rcases (CochainComplex.plus_iff Mod K.obj).1 hplus with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- The bounded-below side is exactly `IsGE` for the chosen representative.
    rw [DerivedCategory.isGE_Q_obj_iff]
    letI : K.obj.IsStrictlyGE n := hn
    infer_instance
  · rcases (CochainComplex.minus_iff Mod K.obj).1 hminus with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- The bounded-above side is exactly `IsLE` for the chosen representative.
    rw [DerivedCategory.isLE_Q_obj_iff]
    letI : K.obj.IsStrictlyLE n := hn
    infer_instance

/-- Helper for Lemma 15.70.5: a bounded cochain complex determines the corresponding bounded
derived object. -/
noncomputable abbrev boundedDerivedObject_of_bounded_complex
    (K : Compᵇ(Mod)) :
    DbMod :=
  ⟨Q.obj K.obj, q_obj_mem_t_bounded_of_bounded_complex K⟩

/-- Helper for Lemma 15.70.5: the bounded-derived homology of the object represented by a bounded
complex is the ordinary homology of that complex. -/
noncomputable def bounded_complex_homology_iso
    (K : Compᵇ(Mod)) (i : ℤ) :
    ((Hb i).obj (boundedDerivedObject_of_bounded_complex K)) ≅ K.obj.homology i :=
  by
    -- This is the standard comparison between `H^i(Q(K.obj))` and the homology of `K.obj`.
    change ((DerivedCategory.homologyFunctor Mod i).obj (Q.obj K.obj)) ≅ K.obj.homology i
    exact (DerivedCategory.homologyFunctorFactors Mod i).app K.obj

/-- Helper for Lemma 15.70.5: finite injective dimension is invariant under isomorphism in
`D(R)`. -/
lemma hasFiniteInjectiveDimension_of_iso {K L : DerivedCategory Mod} (e : K ≅ L) :
    HasFiniteInjectiveDimension K ↔ HasFiniteInjectiveDimension L := by
  constructor
  · rintro ⟨a, b, I, hGE, hLE, hInj, ⟨eI⟩⟩
    refine ⟨a, b, I, hGE, hLE, hInj, ?_⟩
    -- Replace the represented object along the chosen isomorphism in the derived category.
    exact ⟨e.symm ≪≫ eI⟩
  · rintro ⟨a, b, I, hGE, hLE, hInj, ⟨eI⟩⟩
    refine ⟨a, b, I, hGE, hLE, hInj, ?_⟩
    -- The converse transport uses the original isomorphism `e`.
    exact ⟨e ≪≫ eI⟩

/-- Helper for Lemma 15.70.5: injective amplitude in a fixed interval is invariant under
isomorphism in `D(R)`. -/
lemma hasInjectiveAmplitudeIn_of_iso {K L : DerivedCategory Mod} {a b : ℤ} (e : K ≅ L) :
    HasInjectiveAmplitudeIn K a b ↔ HasInjectiveAmplitudeIn L a b := by
  constructor
  · rintro ⟨I, hGE, hLE, hInj, ⟨eI⟩⟩
    refine ⟨I, hGE, hLE, hInj, ?_⟩
    -- Transport the chosen injective representative across the given derived isomorphism.
    exact ⟨e.symm ≪≫ eI⟩
  · rintro ⟨I, hGE, hLE, hInj, ⟨eI⟩⟩
    refine ⟨I, hGE, hLE, hInj, ?_⟩
    -- The converse direction uses the original isomorphism.
    exact ⟨e ≪≫ eI⟩

/-- Helper for Lemma 15.70.5: enlarging the interval preserves injective amplitude. -/
lemma hasInjectiveAmplitudeIn_mono {K : DerivedCategory Mod} {a b a' b' : ℤ}
    (hK : HasInjectiveAmplitudeIn K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    HasInjectiveAmplitudeIn K a' b' := by
  rcases hK with ⟨I, hGE, hLE, hInj, hIso⟩
  refine ⟨I, ?_, ?_, hInj, hIso⟩
  · -- Lowering the left endpoint preserves strict bounded-below support.
    rw [CochainComplex.isStrictlyGE_iff] at hGE ⊢
    intro i hi
    exact hGE i (lt_of_lt_of_le hi ha)
  · -- Raising the right endpoint preserves strict bounded-above support.
    rw [CochainComplex.isStrictlyLE_iff] at hLE ⊢
    intro i hi
    exact hLE i (lt_of_le_of_lt hb hi)

/-- Helper for Lemma 15.70.5: a degree-zero module object with injective dimension bounded by
`m` has injective amplitude in `[0, m]`. -/
lemma single_zero_hasInjectiveAmplitudeIn_of_module_le
    (M : ModuleCat.{u} R) (m : ℕ) (hM : injectiveDimension M ≤ m) :
    HasInjectiveAmplitudeIn ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M) 0 m := by
  -- Route correction: the truncation induction needs a fixed interval witness, so we prove the
  -- stronger amplitude statement directly instead of first packaging only existential finiteness.
  refine ((injectiveAmplitudeIn_ext_vanishing_tfae
    ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M) 0 m).out 1 0).mp ?_
  intro (N : ModuleCat.{u} R) i hi e
  by_cases hi_neg : i < 0
  · -- Negative Ext groups from degree-zero module objects vanish.
    exact
      (single_shiftedHom_subsingleton_of_lt_zero
        (𝒜 := ModuleCat.{u} R) (B := N) (A := M) i hi_neg).elim e 0
  · have hi_nonneg : 0 ≤ i := le_of_not_gt hi_neg
    have hm_lt_i : (m : ℤ) < i := by
      by_contra hm_ge_i
      apply hi
      constructor
      · exact hi_nonneg
      · omega
    letI : HasInjectiveDimensionLT M (m + 1) :=
      (injectiveDimension_le_iff M m).1 hM
    have hmi : m + 1 ≤ Int.toNat i := by
      omega
    have hi_cast : ((Int.toNat i : ℕ) : ℤ) = i := by
      exact Int.toNat_of_nonneg hi_nonneg
    let e' : CategoryTheory.Abelian.Ext N M (Int.toNat i) :=
      (CategoryTheory.Abelian.Ext.homEquiv
        (C := ModuleCat.{u} R) (X := N) (Y := M) (n := Int.toNat i)).symm
          (by simpa [hi_cast] using e)
    have he' : e' = 0 :=
      CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT e' (m + 1) hmi
    have hext :
        (CategoryTheory.Abelian.Ext.homEquiv
          (C := ModuleCat.{u} R) (X := N) (Y := M) (n := Int.toNat i)) e' = 0 := by
      simpa using
        congrArg
          (CategoryTheory.Abelian.Ext.homEquiv
            (C := ModuleCat.{u} R) (X := N) (Y := M) (n := Int.toNat i))
          he'
    simpa [e', hi_cast] using hext

/-- Helper for Lemma 15.70.5: the canonical `shiftIso` identifies the degree-`i` single object,
after shifting by `i`, with the degree-zero single object. -/
noncomputable def singleFunctor_shifted_single0_iso_canonical
    (M : ModuleCat.{u} R) (i : ℤ) :
    (((DerivedCategory.singleFunctor Mod i).obj M)⟦i⟧) ≅
      ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M) :=
  ((DerivedCategory.singleFunctors Mod).shiftIso i 0 i (by simp)).app M

/-- Helper for Lemma 15.70.5: a degree-`i` single object with module injective dimension at most
`m` has injective amplitude in any larger interval containing `[i, i + m]`. -/
lemma singleFunctor_hasInjectiveAmplitudeIn_common_interval_of_module_le
    (M : ModuleCat.{u} R) (i c d : ℤ) (m : ℕ)
    (hM : injectiveDimension M ≤ m) (hci : c ≤ i) (hid : i ≤ d) :
    HasInjectiveAmplitudeIn ((DerivedCategory.singleFunctor Mod i).obj M) c (d + m) := by
  have h₀ : HasInjectiveAmplitudeIn ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M) 0 m :=
    single_zero_hasInjectiveAmplitudeIn_of_module_le M m hM
  rcases h₀ with ⟨I, hGE, hLE, hInj, ⟨eI⟩⟩
  letI : I.IsStrictlyGE 0 := hGE
  letI : I.IsStrictlyLE m := hLE
  have hShiftGE : (I⟦-i⟧).IsStrictlyGE i := by
    -- Shifting the representing injective complex by `-i` moves its support to start at `i`.
    simpa using I.isStrictlyGE_shift 0 (-i) i (by omega)
  have hShiftLE : (I⟦-i⟧).IsStrictlyLE (i + m) := by
    -- The same shift moves the upper endpoint from `m` to `i + m`.
    simpa [add_comm, add_left_comm, add_assoc] using
      I.isStrictlyLE_shift m (-i) (m + i) (by omega)
  have hShiftInj : ∀ j : ℤ, Injective ((I⟦-i⟧).X j) := by
    intro j
    -- Each shifted term is canonically isomorphic to an original injective term.
    exact
      Injective.of_iso
        (I.shiftFunctorObjXIso (-i) j (j - i) (by omega)).symm
        (hInj (j - i))
  have hShiftedSingle0 :
      HasInjectiveAmplitudeIn (((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M)⟦-i⟧) i (i + m) := by
    refine ⟨I⟦-i⟧, hShiftGE, hShiftLE, hShiftInj, ?_⟩
    refine ⟨((shiftFunctor (DerivedCategory Mod) (-i)).mapIso eI) ≪≫
      ((DerivedCategory.Q.commShiftIso (-i)).app I).symm⟩
  let eSingle :
      ((DerivedCategory.singleFunctor Mod i).obj M) ≅
        (((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M)⟦-i⟧) := by
    -- The canonical single-object shift comparison removes the degree `i`.
    exact
      (shiftShiftNeg ((DerivedCategory.singleFunctor Mod i).obj M) i).symm ≪≫
        (shiftFunctor (DerivedCategory Mod) (-i)).mapIso
          (singleFunctor_shifted_single0_iso_canonical (M := M) i)
  have hBase :
      HasInjectiveAmplitudeIn ((DerivedCategory.singleFunctor Mod i).obj M) i (i + m) :=
    (hasInjectiveAmplitudeIn_of_iso eSingle).2 hShiftedSingle0
  -- Enlarge `[i, i + m]` to the common interval `[c, d + m]` used in the truncation step.
  exact hasInjectiveAmplitudeIn_mono hBase hci (by omega)

/-- Helper for Lemma 15.70.5: a degree-zero module object with finite module-level injective
dimension has finite injective dimension in `D(R)`. -/
lemma single_zero_hasFiniteInjectiveDimension_of_module
    (M : ModuleCat.{u} R) (hM : injectiveDimension M ≠ ⊤) :
    HasFiniteInjectiveDimension ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M) := by
  rcases (injectiveDimension_ne_top_iff M).1 hM with ⟨m, hm⟩
  refine ⟨0, m, ?_⟩
  -- Reuse the fixed-interval degree-zero bridge proved just above.
  exact single_zero_hasInjectiveAmplitudeIn_of_module_le M m
    ((injectiveDimension_le_iff M m).2 hm)

/-- Helper for Lemma 15.70.5: shifting an injective-amplitude representative shifts the
cohomological interval by the same amount. -/
theorem hasInjectiveAmplitudeIn_shift_iff_local
    (K : DMod) (n a b : ℤ) :
    HasInjectiveAmplitudeIn (K⟦n⟧) a b ↔ HasInjectiveAmplitudeIn K (a + n) (b + n) := by
  constructor
  · rintro ⟨I, hGE, hLE, hInj, ⟨eI⟩⟩
    have hShiftGE : (I⟦-n⟧).IsStrictlyGE (a + n) := by
      -- Shifting the representative by `-n` moves the lower support endpoint to `a + n`.
      simpa [add_assoc, add_left_comm, add_comm] using
        I.isStrictlyGE_shift a (-n) (a + n) (by omega)
    have hShiftLE : (I⟦-n⟧).IsStrictlyLE (b + n) := by
      -- The upper endpoint moves by the same amount.
      simpa [add_assoc, add_left_comm, add_comm] using
        I.isStrictlyLE_shift b (-n) (b + n) (by omega)
    have hShiftInj : ∀ j : ℤ, Injective ((I⟦-n⟧).X j) := by
      intro j
      -- Each shifted term is canonically isomorphic to an original injective term.
      exact
        Injective.of_iso
          (I.shiftFunctorObjXIso (-n) j (j - n) (by omega)).symm
          (hInj (j - n))
    refine ⟨I⟦-n⟧, hShiftGE, hShiftLE, hShiftInj, ?_⟩
    -- Shift the given derived isomorphism back by `-n` and compare with `Q.commShiftIso`.
    exact
      ⟨(shiftShiftNeg K n).symm ≪≫
        (shiftFunctor DMod (-n)).mapIso eI ≪≫
          ((DerivedCategory.Q.commShiftIso (-n)).app I).symm⟩
  · rintro ⟨I, hGE, hLE, hInj, ⟨eI⟩⟩
    have hShiftGE : (I⟦n⟧).IsStrictlyGE a := by
      -- Shifting the representative by `n` moves the lower endpoint back to `a`.
      simpa [add_assoc, add_left_comm, add_comm] using
        I.isStrictlyGE_shift (a + n) n a (by omega)
    have hShiftLE : (I⟦n⟧).IsStrictlyLE b := by
      -- The upper endpoint also shifts back by `n`.
      simpa [add_assoc, add_left_comm, add_comm] using
        I.isStrictlyLE_shift (b + n) n b (by omega)
    have hShiftInj : ∀ j : ℤ, Injective ((I⟦n⟧).X j) := by
      intro j
      -- Shift preserves injectivity termwise via the standard objectwise comparison.
      exact
        Injective.of_iso
          (I.shiftFunctorObjXIso n j (j + n) (by omega)).symm
          (hInj (j + n))
    refine ⟨I⟦n⟧, hShiftGE, hShiftLE, hShiftInj, ?_⟩
    -- Shift the representing isomorphism forward by `n` and undo the `Q`-shift comparison.
    exact
      ⟨(shiftFunctor DMod n).mapIso eI ≪≫
        ((DerivedCategory.Q.commShiftIso n).app I).symm⟩

/-- Helper for Lemma 15.70.5: the lower truncation projection induces an isomorphism on degree-`n`
cohomology. -/
lemma isIso_homologyMap_truncGEπ_local
    (K : DMod) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) :=
  isIso_homologyMap_truncGEπ (A := Mod) K n

/-- Helper for Lemma 15.70.5: the upper truncation map induces an isomorphism on the last
remaining cohomology group. -/
lemma isIso_homologyMap_truncLTι_local
    (K : DMod) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) :=
  isIso_homologyMap_truncLTι (A := Mod) K n₀ n₁ h

/-- Helper for Lemma 15.70.5: an object concentrated in degree `n` is canonically the single
object on its degree-`n` cohomology. -/
noncomputable def singleFunctor_iso_of_isGE_of_isLE_local
    (X : DMod) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor Mod n).obj ((H n).obj X) :=
  singleFunctorIso_of_isGE_of_isLE (A := Mod) X n

/-- Helper for Lemma 15.70.5: the successive lower-truncation quotient has the same degree-`a`
cohomology as the original derived object. -/
noncomputable def truncGE_step_homologyIso_local
    (K : DMod) (a : ℤ) :
    (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅ (H a).obj K := by
  let eι :
      (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅
        (H a).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _ ((H a).map ((t.truncLTι (a + 1)).app ((t.truncGE a).obj K)))
      (isIso_homologyMap_truncLTι_local ((t.truncGE a).obj K) a (a + 1) (by omega))
  let eπ : (H a).obj K ≅ (H a).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _ ((H a).map ((t.truncGEπ a).app K))
      (isIso_homologyMap_truncGEπ_local K a)
  -- Compare first with the `τ≥a` piece and then with the original object.
  exact eι ≪≫ eπ.symm

/-- Helper for Lemma 15.70.5: the bottom truncation piece is the shifted cohomology object in
degree `a`. -/
noncomputable def truncGE_step_termIso_local
    (K : DMod) (a : ℤ) :
    ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅ shiftedCohomology Mod K a := by
  have hLE : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE a := by
    simpa using
      (inferInstance : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE ((a + 1) - 1))
  -- The bottom piece is supported only in degree `a`, so it is the shifted cohomology object.
  exact
    singleFunctor_iso_of_isGE_of_isLE_local
      ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) a ≪≫
      (DerivedCategory.singleFunctor Mod a).mapIso (truncGE_step_homologyIso_local K a)

/-- Helper for Lemma 15.70.5: the source-facing lower-step triangle. -/
noncomputable def truncGE_step_homologyTriangle_local
    (K : DMod) (a : ℤ) :
    Triangle DMod :=
  Triangle.mk
    ((truncGE_step_termIso_local K a).inv ≫
      (t.truncLTι (a + 1)).app ((t.truncGE a).obj K))
    ((t.natTransTruncGEOfLE a (a + 1) (le_add_of_nonneg_right zero_le_one)).app K)
    (((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) ≫
      (t.truncGEδLT (a + 1)).app ((t.truncGE a).obj K) ≫
      ((truncGE_step_termIso_local K a).hom)⟦1⟧')

/-- Helper for Lemma 15.70.5: the lower-step triangle is distinguished. -/
theorem truncGE_step_homology_triangle_local
    (K : DMod) (a : ℤ) :
    truncGE_step_homologyTriangle_local K a ∈ distTriang DMod := by
  let e₃ :
      (t.truncGE (a + 1)).obj K ≅ (t.truncGE (a + 1)).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _ ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K))
      (t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) K)
  let e :
      truncGE_step_homologyTriangle_local K a ≅
        (t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K) := by
    refine Triangle.isoMk _ _ (truncGE_step_termIso_local K a).symm
      (Iso.refl _) e₃ ?_ ?_ ?_
    · simp [truncGE_step_homologyTriangle_local]
    · haveI : ((t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K)).obj₃.IsGE a := by
        dsimp
        exact t.isGE_of_ge _ a (a + 1) (by omega)
      exact t.from_truncGE_obj_ext (by
        simpa [truncGE_step_homologyTriangle_local, e₃, Category.assoc,
          t.π_natTransTruncGEOfLE_app] using
          (NatTrans.naturality (t.truncGEπ (a + 1)) ((t.truncGEπ a).app K)).symm)
    · have he₃ : e₃.hom = (t.truncGE (a + 1)).map ((t.truncGEπ a).app K) := by
        -- Route correction: `asIso` needs the truncation comparison registered as an isomorphism.
        letI : IsIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) :=
          t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) K
        change (asIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K))).hom =
          (t.truncGE (a + 1)).map ((t.truncGEπ a).app K)
        simp
      simp [truncGE_step_homologyTriangle_local, he₃, Category.assoc]
  -- This is exactly the owner truncation triangle rewritten so the first term is `H^a(K)[a]`.
  exact
    isomorphic_distinguished _
      (t.triangleLTGE_distinguished (a + 1) ((t.truncGE a).obj K)) _ e

/-- Helper for Lemma 15.70.5: in degrees above the cutoff, lower truncation preserves homology. -/
noncomputable def homology_truncGE_iso
    (K : DMod) (c i : ℤ) (hci : c ≤ i) :
    (H i).obj ((t.truncGE c).obj K) ≅ (H i).obj K := by
  let f : K ⟶ (t.truncGE c).obj K := (t.truncGEπ c).app K
  let Y : DMod := (t.truncGE c).obj K
  let eK :
      (H i).obj K ≅ (H i).obj ((t.truncGE i).obj K) :=
    @asIso _ _ _ _ ((H i).map ((t.truncGEπ i).app K))
      (isIso_homologyMap_truncGEπ_local K i)
  let eY :
      (H i).obj Y ≅ (H i).obj ((t.truncGE i).obj Y) :=
    @asIso _ _ _ _ ((H i).map ((t.truncGEπ i).app Y))
      (isIso_homologyMap_truncGEπ_local Y i)
  have hf :
      (H i).map f ≫ eY.hom = eK.hom ≫ (H i).map ((t.truncGE i).map f) := by
    change
      (H i).map f ≫ (H i).map ((t.truncGEπ i).app Y) =
        (H i).map ((t.truncGEπ i).app K) ≫ (H i).map ((t.truncGE i).map f)
    simpa [Functor.map_comp, f, Y] using
      congrArg ((H i).map) (NatTrans.naturality (t.truncGEπ i) f)
  have hmiddle : IsIso ((H i).map ((t.truncGE i).map f)) := by
    haveI : IsIso ((t.truncGE i).map f) := t.isIso_truncGE_map_truncGEπ_app i c hci K
    exact Functor.map_isIso (H i) ((t.truncGE i).map f)
  have hcomp : IsIso ((H i).map f ≫ eY.hom) := by
    rw [hf]
    letI : IsIso ((H i).map ((t.truncGE i).map f)) := hmiddle
    change IsIso (eK.hom ≫ (H i).map ((t.truncGE i).map f))
    infer_instance
  letI : IsIso ((H i).map f ≫ eY.hom) := hcomp
  haveI : IsIso ((H i).map f) := IsIso.of_isIso_comp_right ((H i).map f) eY.hom
  -- The desired comparison goes from the truncation back to the original object.
  exact (asIso ((H i).map f)).symm

/-- Helper for Lemma 15.70.5: in degrees above the cutoff, lower truncation preserves the
intrinsic shifted cohomology object. -/
noncomputable def shiftedCohomology_truncGE_iso
    (K : DMod) (c i : ℤ) (hci : c ≤ i) :
    shiftedCohomology Mod ((t.truncGE c).obj K) i ≅ shiftedCohomology Mod K i :=
  (DerivedCategory.singleFunctor Mod i).mapIso (homology_truncGE_iso K c i hci)

/-- Helper for Lemma 15.70.5: moving from the tail interval
`[c + 1, c + 1 + n]` to the full support interval `[c, c + (n + 1)]`
is equivalent to remembering that the index is not `c`. -/
lemma mem_Icc_succ_iff (c j : ℤ) (n : ℕ) :
    j ∈ Set.Icc (c + 1) (c + 1 + n) ↔
      j ∈ Set.Icc c (c + (n + 1)) ∧ j ≠ c := by
  constructor
  · intro hj
    rcases hj with ⟨hleft, hright⟩
    constructor
    · constructor
      · omega
      · simpa [add_assoc, add_left_comm, add_comm] using hright
    · omega
  · rintro ⟨hj, hne⟩
    rcases hj with ⟨hleft, hright⟩
    constructor
    · have hlt : c < j := lt_of_le_of_ne hleft (by simpa [eq_comm] using hne)
      omega
    · simpa [add_assoc, add_left_comm, add_comm] using hright

/-- Helper for Lemma 15.70.5: finitely many terms of a bounded cochain complex with finite
injective dimension admit one common natural-number bound on an interval `[c, d]`. -/
lemma exists_common_injective_dimension_bound_on_terms_of_bounded_complex
    (K : Compᵇ(Mod)) (c d : ℤ)
    (hterm : ∀ i : ℤ, injectiveDimension (K.obj.X i) ≠ ⊤) :
    ∃ m : ℕ,
      ∀ i : ℤ, c ≤ i → i ≤ d → injectiveDimension (K.obj.X i) ≤ m := by
  classical
  let bound : ℤ → ℕ := fun i ↦
    Classical.choose ((injectiveDimension_ne_top_iff (K.obj.X i)).1 (hterm i))
  let m : ℕ := (Finset.Icc c d).sup bound
  refine ⟨m, ?_⟩
  intro i hci hid
  have hi_mem : i ∈ Finset.Icc c d := by
    simp [Finset.mem_Icc, hci, hid]
  have hle_bound : injectiveDimension (K.obj.X i) ≤ bound i := by
    -- Convert the chosen `HasInjectiveDimensionLE` witness into an explicit owner inequality.
    exact
      (injectiveDimension_le_iff (K.obj.X i) (bound i)).2
        (Classical.choose_spec
          ((injectiveDimension_ne_top_iff (K.obj.X i)).1 (hterm i)))
  have hsup : (bound i : WithBot ℕ∞) ≤ m := by
    exact_mod_cast Finset.le_sup hi_mem
  -- Take the maximum over the finite interval `[c, d]`.
  exact le_trans hle_bound hsup

/-- Helper for Lemma 15.70.5: transporting morphisms along source and target isomorphisms is
additive on Hom groups. -/
private theorem iso_hom_congr_add_equiv_map_add_local
    {X Y X₁ Y₁ : Mod} (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- `Iso.homCongr` is composition with the isomorphism legs, so additivity is bilinearity.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.70.5: source and target isomorphisms induce an additive equivalence on
Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv_local
    {X Y X₁ Y₁ : Mod} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := iso_hom_congr_add_equiv_map_add_local α β }

/-- Helper for Lemma 15.70.5: every additive group is canonically additively equivalent to its
universe lift. -/
private noncomputable def add_equiv_ulift_local (A : AddCommGrpCat.{u}) :
    A ≃+ AddCommGrpCat.of (ULift.{u} A) where
  toEquiv :=
    { toFun := fun a ↦ ⟨a⟩
      invFun := fun a ↦ a.down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  map_add' := by
    intro a b
    rfl

/-- Helper for Lemma 15.70.5: an additive equivalence yields an isomorphism after packaging the
codomain as an object of `AddCommGrpCat`. -/
private noncomputable def ulift_add_equiv_to_iso_local
    {A : AddCommGrpCat.{u}} {B : Type u} [AddCommGroup B] (e : A ≃+ B) :
    A ≅ AddCommGrpCat.of B :=
  AddEquiv.toAddCommGrpIso e

/-- Helper for Lemma 15.70.5: componentwise additive equivalences of short complexes induce an
additive equivalence on homology. -/
private noncomputable def shortComplex_homology_add_equiv_of_componentwise_add_equiv_local
    {S : ShortComplex AddCommGrpCat.{u}}
    {T : ShortComplex AddCommGrpCat.{max u u}}
    (e₁ : S.X₁ ≃+ T.X₁)
    (e₂ : S.X₂ ≃+ T.X₂)
    (e₃ : S.X₃ ≃+ T.X₃)
    (comm₁₂ :
      (ulift_add_equiv_to_iso_local e₁).hom ≫ T.f =
        (S.map AddCommGrpCat.uliftFunctor.{u, u}).f ≫
          (ulift_add_equiv_to_iso_local e₂).hom)
    (comm₂₃ :
      (ulift_add_equiv_to_iso_local e₂).hom ≫ T.g =
        (S.map AddCommGrpCat.uliftFunctor.{u, u}).g ≫
          (ulift_add_equiv_to_iso_local e₃).hom) :
    S.homology ≃+ T.homology := by
  let F := AddCommGrpCat.uliftFunctor.{u, u}
  let e : S.map F ≅ T :=
    ShortComplex.isoMk
      (ulift_add_equiv_to_iso_local e₁)
      (ulift_add_equiv_to_iso_local e₂)
      (ulift_add_equiv_to_iso_local e₃)
      comm₁₂ comm₂₃
  let eh : F.obj S.homology ≅ T.homology :=
    (S.mapHomologyIso F).symm ≪≫ ShortComplex.homologyMapIso e
  -- First identify `S.homology` with its lift, then transport across the lifted short complex.
  exact (add_equiv_ulift_local S.homology).trans eh.addCommGroupIsoToAddEquiv

/-- Helper for Lemma 15.70.5: in degree `n`, the mapped degree-zero Ext cocomplex agrees
additively with the restriction of the full Hom complex. -/
private noncomputable def mapped_ext_zero_component_bridge_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ) :
    ((((Abelian.extFunctorObj N 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).X n) ≃+
      (((CochainComplex.HomComplex
          ((singleCpx₀).obj N)
          I.cochainComplex).restriction ComplexShape.embeddingUpNat).X n) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  let eKr :
      K.X (((n : ℕ) : ℤ)) ≅
        (K.restriction ComplexShape.embeddingUpNat).X n :=
    (K.restrictionXIso ComplexShape.embeddingUpNat
      (by simp : ComplexShape.embeddingUpNat.f n = ((n : ℕ) : ℤ))).symm
  let eExt :
      Abelian.Ext N (I.cocomplex.X n) 0 ≃+
        (N ⟶ I.cocomplex.X n) :=
    Abelian.Ext.addEquiv₀
  let eHom :
      (N ⟶ I.cocomplex.X n) ≃+
        (((CochainComplex.HomComplex
            ((singleCpx₀).obj N)
            I.cochainComplex).restriction ComplexShape.embeddingUpNat).X n) :=
    (iso_hom_congr_add_equiv_local
        (Iso.refl _)
        (I.cochainComplexXIso (((n : ℕ) : ℤ)) n
          (by simp : n = ((n : ℕ) : ℤ))).symm).trans
      ((CochainComplex.HomComplex.Cochain.fromSingleEquiv
          (K := I.cochainComplex)
          (X := N)
          (p := 0) (q := ((n : ℕ) : ℤ)) (n := ((n : ℕ) : ℤ))
          (by simp)).symm.trans
        (eKr.addCommGroupIsoToAddEquiv))
  exact
    { toEquiv := eExt.toEquiv.trans eHom.toEquiv
      map_add' := by
        intro x y
        calc
          eHom (eExt (x + y)) = eHom (eExt x + eExt y) := by
            congr 1
            exact eExt.map_add x y
          _ = eHom (eExt x) + eHom (eExt y) := by
            exact eHom.map_add (eExt x) (eExt y) }

/-- Helper for Lemma 15.70.5: after forgetting the final restriction transport, the degreewise
`Ext^0 = Hom` comparison sends `Ext.mk₀ g` to the corresponding single-supported cochain. -/
private theorem mapped_ext_zero_component_to_full_hom_apply_mk₀_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ)
    (g : N ⟶ I.cocomplex.X n) :
    (((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom
        (mapped_ext_zero_component_bridge_local N M I n (Abelian.Ext.mk₀ g))) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) (by simp) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  let e :
      K.X (ComplexShape.embeddingUpNat.f n) ≃+
        (N ⟶ I.cochainComplex.X (n : ℤ)) :=
    CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (K := I.cochainComplex)
      (X := N)
      (p := 0) (q := (n : ℤ)) (n := (n : ℤ))
      (by simp)
  -- Apply the single-supported cochain equivalence so every factor simplifies.
  apply e.injective
  have hmk : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g := by
    -- `Ext.addEquiv₀` is inverse to the degree-zero constructor `Ext.mk₀`.
    apply Abelian.Ext.homEquiv₀.symm.injective
    simpa using (Abelian.Ext.mk₀_addEquiv₀_apply (Abelian.Ext.mk₀ g))
  calc
    e
        (((K.restrictionXIso ComplexShape.embeddingUpNat rfl).hom
          (mapped_ext_zero_component_bridge_local N M I n (Abelian.Ext.mk₀ g)))) =
      (iso_hom_congr_add_equiv_local (Iso.refl N)
          ((I.cochainComplexXIso (n : ℤ) n rfl).symm))
        (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g)) := by
          simpa [Function.comp, e, mapped_ext_zero_component_bridge_local,
            iso_hom_congr_add_equiv_local, HomologicalComplex.restrictionXIso, K] using
            (AddEquiv.apply_symm_apply e
              ((iso_hom_congr_add_equiv_local (Iso.refl N)
                ((I.cochainComplexXIso (n : ℤ) n rfl).symm))
                (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g))))
    _ = g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv := by
          rw [hmk]
          simp [iso_hom_congr_add_equiv_local]
    _ = e
          (CochainComplex.HomComplex.Cochain.fromSingleMk
            (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) (by simp)) := by
          symm
          simpa [e] using
            (AddEquiv.apply_symm_apply e
              (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv))

/-- Helper for Lemma 15.70.5: on the mapped degree-zero Ext cocomplex, the successor
differential sends `Ext.mk₀ g` to the class induced by postcomposition with the cocomplex
differential. -/
private theorem mapped_ext_zero_cocomplex_d_apply_mk₀_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ)
    (g : N ⟶ I.cocomplex.X n) :
    (((((Abelian.extFunctorObj N 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
      (Abelian.Ext.mk₀ g)) =
        Abelian.Ext.mk₀ (g ≫ I.cocomplex.d n (n + 1)) := by
  have hmk₀_apply {Y : Mod} (h : N ⟶ Y) :
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ h) = h := by
    -- `Ext.addEquiv₀` is inverse to the degree-zero constructor `Ext.mk₀`.
    apply Abelian.Ext.homEquiv₀.symm.injective
    simp [Abelian.Ext.homEquiv₀_symm_apply]
  -- Compute the mapped cocomplex differential by the owner map on `Ext^0`.
  apply Abelian.Ext.addEquiv₀.injective
  calc
    Abelian.Ext.addEquiv₀
        (((((Abelian.extFunctorObj N 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
          (Abelian.Ext.mk₀ g)) =
      Abelian.Ext.addEquiv₀
        (((Abelian.extFunctorObj N 0).map
            (I.cocomplex.d n (n + 1)))
          (Abelian.Ext.mk₀ g)) := by
          rfl
    _ = Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) ≫ I.cocomplex.d n (n + 1) := by
          exact ext_zero_addEquiv₀_map (I.cocomplex.d n (n + 1)) (Abelian.Ext.mk₀ g)
    _ = g ≫ I.cocomplex.d n (n + 1) := by
          rw [hmk₀_apply g]
    _ = Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (g ≫ I.cocomplex.d n (n + 1))) := by
          rw [hmk₀_apply (g ≫ I.cocomplex.d n (n + 1))]

/-- Helper for Lemma 15.70.5: after transporting the degree-zero `Ext` generator into the full
Hom complex, the full differential is computed by the usual single-supported-cochain formula. -/
private theorem mapped_ext_zero_full_hom_d_apply_mk₀_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ)
    (g : N ⟶ I.cocomplex.X n) :
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).d (n : ℤ) ((n + 1 : ℕ) : ℤ))
        ((((CochainComplex.HomComplex
            ((singleCpx₀).obj N)
            I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom
          (mapped_ext_zero_component_bridge_local N M I n (Abelian.Ext.mk₀ g)))) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        (((g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) ≫
            I.cochainComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ)))
        (by simp) := by
  -- First normalize the transported Ext class to the corresponding single-supported cochain.
  rw [mapped_ext_zero_component_to_full_hom_apply_mk₀_local N M I n g]
  -- Then the full Hom-complex differential is exactly `δ_fromSingleMk`.
  simpa [Category.assoc] using
    (CochainComplex.HomComplex.Cochain.δ_fromSingleMk
      (K := I.cochainComplex)
      (X := N)
      (p := 0)
      (f := g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv)
      (n := (n : ℤ))
      (h := by simp)
      (((n + 1 : ℕ) : ℤ))
      (((n + 1 : ℕ) : ℤ))
      (by simp))

/-- Helper for Lemma 15.70.5: after whiskering with the successor `restrictionXIso`, the mapped
`Ext^0` differential agrees with the restricted Hom differential on the generator `Ext.mk₀ g`.
-/
private theorem mapped_ext_zero_component_d_comm_apply_mk₀_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ)
    (g : N ⟶ I.cocomplex.X n) :
    (((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom
        ((((CochainComplex.HomComplex
            ((singleCpx₀).obj N)
            I.cochainComplex).restriction ComplexShape.embeddingUpNat).d n (n + 1))
          (mapped_ext_zero_component_bridge_local N M I n (Abelian.Ext.mk₀ g)))) =
      (((CochainComplex.HomComplex
          ((singleCpx₀).obj N)
          I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom
        (mapped_ext_zero_component_bridge_local N M I (n + 1)
          (((((Abelian.extFunctorObj N 0).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
            (Abelian.Ext.mk₀ g)))) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  -- Expand the restricted differential once so both sides lie in the same full Hom complex.
  rw [HomologicalComplex.restriction_d_eq
    (K := K) (e := ComplexShape.embeddingUpNat) (i' := (n : ℤ))
    (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
  simp only [ComplexShape.embeddingUpNat_f, Int.natCast_add, Int.cast_ofNat_Int,
    CochainComplex.HomComplex_X, HomologicalComplex.restriction_X,
    Functor.mapHomologicalComplex_obj_X, Abelian.extFunctorObj_obj_coe,
    Functor.mapHomologicalComplex_obj_d, Abelian.extFunctorObj_map]
  trans CochainComplex.HomComplex.Cochain.fromSingleMk
      (((g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) ≫
          I.cochainComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ)))
      (by simp)
  · simpa [K] using mapped_ext_zero_full_hom_d_apply_mk₀_local N M I n g
  trans CochainComplex.HomComplex.Cochain.fromSingleMk
      ((g ≫ I.cocomplex.d n (n + 1)) ≫
        (I.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
      (by simp)
  · rw [I.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
    simp [Category.assoc]
  change
    CochainComplex.HomComplex.Cochain.fromSingleMk
        ((g ≫ I.cocomplex.d n (n + 1)) ≫
          (I.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
        (show (0 : ℤ) + ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) by simp) =
      (((CochainComplex.HomComplex
          ((singleCpx₀).obj N)
          I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom
        (mapped_ext_zero_component_bridge_local N M I (n + 1)
          (((((Abelian.extFunctorObj N 0).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
            (Abelian.Ext.mk₀ g))))
  rw [mapped_ext_zero_cocomplex_d_apply_mk₀_local N M I n g]
  simpa [K, Category.assoc] using
    (mapped_ext_zero_component_to_full_hom_apply_mk₀_local
      N M I (n + 1) (g ≫ I.cocomplex.d n (n + 1))).symm

/-- Helper for Lemma 15.70.5: the degreewise `Ext^0 = Hom` comparison intertwines successor
differentials of the mapped Ext cocomplex and the restricted Hom complex. -/
private theorem mapped_ext_zero_component_d_comm_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ)
    (x : ((((Abelian.extFunctorObj N 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).X n)) :
    mapped_ext_zero_component_bridge_local N M I (n + 1)
        (((((Abelian.extFunctorObj N 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1)) x) =
      ((((CochainComplex.HomComplex
          ((singleCpx₀).obj N)
          I.cochainComplex).restriction ComplexShape.embeddingUpNat).d n (n + 1))
        (mapped_ext_zero_component_bridge_local N M I n x)) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  let erestriction :
      K.X (ComplexShape.embeddingUpNat.f (n + 1)) ≃+
        (K.restriction ComplexShape.embeddingUpNat).X (n + 1) :=
    let eRestriction := (K.restrictionXIso ComplexShape.embeddingUpNat rfl).symm
    { toEquiv :=
        { toFun := eRestriction.hom
          invFun := eRestriction.inv
          left_inv := by
            intro y
            exact ConcreteCategory.congr_hom eRestriction.hom_inv_id y
          right_inv := by
            intro y
            exact ConcreteCategory.congr_hom eRestriction.inv_hom_id y }
      map_add' := by
        intro x y
        exact (ConcreteCategory.hom eRestriction.hom).map_add x y }
  -- Verify the differential on `Ext.mk₀` generators and cancel the restriction transport.
  apply erestriction.injective
  obtain ⟨g, hg⟩ := Abelian.Ext.homEquiv₀.symm.surjective x
  have hg' : Abelian.Ext.mk₀ g = x := by
    simpa [Abelian.Ext.homEquiv₀_symm_apply] using hg
  rw [← hg']
  symm
  simpa [K] using mapped_ext_zero_component_d_comm_apply_mk₀_local N M I n g

/-- Helper for Lemma 15.70.5: the differential compatibility above can be packaged as a morphism
equality after converting additive equivalences into isomorphisms. -/
private theorem mapped_ext_zero_component_d_comm_hom_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ) :
    (ulift_add_equiv_to_iso_local (mapped_ext_zero_component_bridge_local N M I n)).hom ≫
        ((CochainComplex.HomComplex
            ((singleCpx₀).obj N)
            I.cochainComplex).restriction ComplexShape.embeddingUpNat).d n (n + 1) =
      ((AddCommGrpCat.uliftFunctor.{u, u}).map
          ((((Abelian.extFunctorObj N 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))) ≫
        (ulift_add_equiv_to_iso_local
          (mapped_ext_zero_component_bridge_local N M I (n + 1))).hom := by
  ext x
  rcases x with ⟨x⟩
  -- Evaluate both morphisms on the underlying Ext-class and use the pointwise bridge.
  simpa using (mapped_ext_zero_component_d_comm_local N M I n x).symm

/-- Helper for Lemma 15.70.5: the degree-`0` source map of the mapped `Ext^0` short complex is
zero. -/
private theorem mapped_ext_zero_sc_zero_f_eq_zero_local
    (N M : Mod) (I : InjectiveResolution M) :
    ((((Abelian.extFunctorObj N 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).sc' 0 0 1).f = 0 := by
  let E :=
    (((Abelian.extFunctorObj N 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
  -- At degree `0`, the predecessor is still `0`, so the source map is `d 0 0 = 0`.
  change E.d 0 0 = 0
  simpa [E, CochainComplex.prev] using
    (E.shape 0 0 (show ¬ (ComplexShape.up ℕ).Rel 0 0 from Nat.succ_ne_zero 0))

/-- Helper for Lemma 15.70.5: in positive degrees, restricting the full Hom complex along
`embeddingUpNat` does not change homology. -/
private noncomputable def restricted_hom_complex_homology_iso_nat_succ_local
    (N M : Mod) (I : InjectiveResolution M) (n : ℕ) :
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology (n + 1) ≅
      (CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).homology (((n + 1 : ℕ) : ℤ)) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  -- In successor degree, the standard restriction homology comparison applies directly.
  simpa [K] using
    (HomologicalComplex.restrictionHomologyIso
      K ComplexShape.embeddingUpNat n (n + 1) (n + 2)
      (by simp) (by simp)
      (by simp : ComplexShape.embeddingUpNat.f n = (n : ℤ))
      (by simp : ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ))
      (by norm_num : ComplexShape.embeddingUpNat.f (n + 2) = ((n + 2 : ℕ) : ℤ))
      (by simp)
      (by
        calc
          (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = (((n + 1 : ℕ) : ℤ) + 1) := by
            simpa using (CochainComplex.next ℤ (((n + 1 : ℕ) : ℤ)))
          _ = ((n + 2 : ℕ) : ℤ) := by omega))

/-- Helper for Lemma 15.70.5: the degree-`0` source map of the restricted Hom short complex is
zero. -/
private theorem restricted_hom_complex_sc_zero_f_eq_zero_local
    (N M : Mod) (I : InjectiveResolution M) :
    (((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).sc' 0 0 1).f = 0 := by
  let K :=
    (CochainComplex.HomComplex
      ((singleCpx₀).obj N)
      I.cochainComplex).restriction ComplexShape.embeddingUpNat
  -- At degree `0`, the restricted predecessor is still `0`, so the source map is `d 0 0 = 0`.
  change K.d 0 0 = 0
  simpa [K, CochainComplex.prev] using
    (K.shape 0 0 (show ¬ (ComplexShape.up ℕ).Rel 0 0 from Nat.succ_ne_zero 0))

/-- Helper for Lemma 15.70.5: the degree-`0` boundary map into cycles for the restricted Hom
short complex vanishes. -/
private theorem restricted_hom_complex_sc_zero_toCycles_eq_zero_local
    (N M : Mod) (I : InjectiveResolution M) :
    (((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).sc' 0 0 1).toCycles = 0 := by
  let S :=
    (((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).sc' 0 0 1)
  -- Cancel the mono inclusion of cycles and reduce to the normalized source map.
  apply (cancel_mono S.iCycles).1
  rw [ShortComplex.toCycles_i, restricted_hom_complex_sc_zero_f_eq_zero_local N M I]
  symm
  exact
    (CategoryTheory.Limits.zero_comp :
      (0 : S.X₁ ⟶ S.cycles) ≫ S.iCycles = (0 : S.X₁ ⟶ S.X₂))

/-- Helper for Lemma 15.70.5: the degree `-1` term of the full Hom complex vanishes because the
injective-resolution cochain complex is zero in negative degrees. -/
private theorem full_hom_complex_neg_one_isZero_local
    (N M : Mod) (I : InjectiveResolution M) :
    IsZero
      ((CochainComplex.HomComplex
          ((singleCpx₀).obj N)
          I.cochainComplex).X (-1)) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  let e :
      K.X (-1) ≃+ (N ⟶ I.cochainComplex.X (-1)) :=
    CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (K := I.cochainComplex)
      (X := N)
      (p := 0) (q := (-1 : ℤ)) (n := (-1 : ℤ))
      (by simp)
  let hneg : IsZero (I.cochainComplex.X (-1)) :=
    CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by omega)
  have hsub_hom : Subsingleton (N ⟶ I.cochainComplex.X (-1)) := by
    refine ⟨fun f g ↦ ?_⟩
    exact hneg.eq_of_tgt f g
  have hsub : Subsingleton (K.X (-1)) := by
    refine ⟨fun x y ↦ e.injective ?_⟩
    exact Subsingleton.elim _ _
  letI : Subsingleton (K.X (-1)) := hsub
  -- A subsingleton abelian group object is zero.
  exact AddCommGrpCat.isZero_of_subsingleton (K.X (-1))

/-- Helper for Lemma 15.70.5: the degree-`0` predecessor differential of the full `ℤ`-indexed
Hom short complex vanishes because its source object is zero. -/
private theorem full_hom_complex_sc_zero_f_eq_zero_local
    (N M : Mod) (I : InjectiveResolution M) :
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).sc' (-1) 0 1).f = 0 := by
  let S :=
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).sc' (-1) 0 1)
  let hzero := full_hom_complex_neg_one_isZero_local N M I
  -- The left term is zero, so every map out of it vanishes.
  exact hzero.eq_of_src S.f 0

/-- Helper for Lemma 15.70.5: the degree-`0` boundary map into cycles for the full `ℤ`-indexed
Hom short complex vanishes because its source object is zero. -/
private theorem full_hom_complex_sc_zero_toCycles_eq_zero_local
    (N M : Mod) (I : InjectiveResolution M) :
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).sc' (-1) 0 1).toCycles = 0 := by
  let S :=
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).sc' (-1) 0 1)
  let hzero := full_hom_complex_neg_one_isZero_local N M I
  -- Any morphism out of the zero source object is zero.
  exact hzero.eq_of_src S.toCycles 0

/-- Helper for Lemma 15.70.5: after identifying both degree-`0` cycle objects with kernels of the
same outgoing differential, restricting the full Hom complex to nonnegative degrees does not
change the degree-`0` cycles. -/
private noncomputable def restricted_hom_complex_cycles_iso_nat_zero_local
    (N M : Mod) (I : InjectiveResolution M) :
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).cycles 0 ≅
      (CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).cycles (0 : ℤ) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let Sr : ShortComplex AddCommGrpCat := Kr.sc' 0 0 1
  let Sf : ShortComplex AddCommGrpCat := K.sc' (-1) 0 1
  let e0 : Kr.X 0 ≅ K.X (0 : ℤ) := K.restrictionXIso ComplexShape.embeddingUpNat rfl
  let e1 : Kr.X 1 ≅ K.X (1 : ℤ) := K.restrictionXIso ComplexShape.embeddingUpNat rfl
  have hprevKr : (ComplexShape.up ℕ).prev 0 = 0 := by
    simp
  have hnextKr : (ComplexShape.up ℕ).next 0 = 1 := by
    simpa using (CochainComplex.next ℕ 0)
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  have hd :
      Kr.d 0 1 ≫ e1.hom = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
    -- Expanding the restricted differential shows that both cycle objects are kernels
    -- of the same outgoing differential in the full Hom complex.
    rw [HomologicalComplex.restriction_d_eq
      (K := K) (e := ComplexShape.embeddingUpNat) (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    calc
      ((e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ e1.inv) ≫ e1.hom) =
          e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ (e1.inv ≫ e1.hom) := by
            simp [Category.assoc]
      _ = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
            simp
  exact
    (Kr.cyclesIsoSc' 0 0 1 hprevKr hnextKr) ≪≫
      Sr.cyclesIsoKernel ≪≫
      kernel.mapIso (Kr.d 0 1) (K.d (0 : ℤ) (1 : ℤ)) e0 e1 hd ≪≫
      Sf.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Lemma 15.70.5: restricting the full Hom complex to nonnegative degrees does not
change degree-`0` homology. -/
private noncomputable def restricted_hom_complex_homology_iso_nat_zero_local
    (N M : Mod) (I : InjectiveResolution M) :
    ((CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology 0 ≅
      (CochainComplex.HomComplex
        ((singleCpx₀).obj N)
        I.cochainComplex).homology (0 : ℤ) := by
  let K := CochainComplex.HomComplex ((singleCpx₀).obj N) I.cochainComplex
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let hCycles := restricted_hom_complex_cycles_iso_nat_zero_local N M I
  let eπr : Kr.homology 0 ≅ Kr.cycles 0 := (CochainComplex.isoHomologyπ₀ Kr).symm
  have hzero_prev : K.d (-1) 0 = 0 := by
    exact (full_hom_complex_neg_one_isZero_local N M I).eq_of_src _ _
  let eπf : K.cycles (0 : ℤ) ≅ K.homology (0 : ℤ) :=
    K.isoHomologyπ (-1) 0 (by simp) hzero_prev
  -- Compare homology with cycles on the restricted and full complexes, then use the cycle bridge.
  exact eπr ≪≫ hCycles ≪≫ eπf

/-- Helper for Lemma 15.70.5: homology of the mapped degree-zero Ext cocomplex identifies with
homology of the restricted full Hom complex. -/
private noncomputable def mapped_ext_zero_homology_add_equiv_restricted_hom_local
    (N M : Mod) (I : InjectiveResolution M) (p : ℕ) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
      (((Abelian.extFunctorObj N 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex)) ≃+
      ((CochainComplex.HomComplex
          ((singleCpx₀).obj N)
          I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology p := by
  let E :=
    (((Abelian.extFunctorObj N 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
  let Kr :=
    (CochainComplex.HomComplex
      ((singleCpx₀).obj N)
      I.cochainComplex).restriction ComplexShape.embeddingUpNat
  cases p with
  | zero =>
      let S : ShortComplex AddCommGrpCat := E.sc' 0 0 1
      let T : ShortComplex AddCommGrpCat := Kr.sc' 0 0 1
      have hprev : (ComplexShape.up ℕ).prev 0 = 0 := by
        simp
      have hnext : (ComplexShape.up ℕ).next 0 = 1 := by
        simpa using (CochainComplex.next ℕ 0)
      have hcomm₁₂ :
          (ulift_add_equiv_to_iso_local
              (mapped_ext_zero_component_bridge_local N M I 0)).hom ≫ T.f =
            (S.map AddCommGrpCat.uliftFunctor.{u, u}).f ≫
              (ulift_add_equiv_to_iso_local
                (mapped_ext_zero_component_bridge_local N M I 0)).hom := by
        -- At degree `0`, both incoming differentials vanish.
        rw [mapped_ext_zero_sc_zero_f_eq_zero_local N M I,
          restricted_hom_complex_sc_zero_f_eq_zero_local N M I]
        simp
      have hcomm₂₃ :
          (ulift_add_equiv_to_iso_local
              (mapped_ext_zero_component_bridge_local N M I 0)).hom ≫ T.g =
            (S.map AddCommGrpCat.uliftFunctor.{u, u}).g ≫
              (ulift_add_equiv_to_iso_local
                (mapped_ext_zero_component_bridge_local N M I 1)).hom := by
        -- The outgoing differential is the successor differential `d 0 1`.
        simpa [S, T] using mapped_ext_zero_component_d_comm_hom_local N M I 0
      let eShort : S.homology ≃+ T.homology :=
        shortComplex_homology_add_equiv_of_componentwise_add_equiv_local
          (mapped_ext_zero_component_bridge_local N M I 0)
          (mapped_ext_zero_component_bridge_local N M I 0)
          (mapped_ext_zero_component_bridge_local N M I 1)
          hcomm₁₂ hcomm₂₃
      exact
        (E.homologyIsoSc' 0 0 1 hprev hnext).addCommGroupIsoToAddEquiv.trans <|
          eShort.trans <|
            ((Kr.homologyIsoSc' 0 0 1 hprev hnext).symm.addCommGroupIsoToAddEquiv)
  | succ n =>
      let S : ShortComplex AddCommGrpCat := E.sc' n (n + 1) (n + 2)
      let T : ShortComplex AddCommGrpCat := Kr.sc' n (n + 1) (n + 2)
      have hprev : (ComplexShape.up ℕ).prev (n + 1) = n := by
        simp
      have hnext : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by
        simpa using (CochainComplex.next ℕ (n + 1))
      have hcomm₁₂ :
          (ulift_add_equiv_to_iso_local
              (mapped_ext_zero_component_bridge_local N M I n)).hom ≫ T.f =
            (S.map AddCommGrpCat.uliftFunctor.{u, u}).f ≫
              (ulift_add_equiv_to_iso_local
                (mapped_ext_zero_component_bridge_local N M I (n + 1))).hom := by
        -- The incoming differential is the successor differential `d n (n + 1)`.
        simpa [S, T] using mapped_ext_zero_component_d_comm_hom_local N M I n
      have hcomm₂₃ :
          (ulift_add_equiv_to_iso_local
              (mapped_ext_zero_component_bridge_local N M I (n + 1))).hom ≫ T.g =
            (S.map AddCommGrpCat.uliftFunctor.{u, u}).g ≫
              (ulift_add_equiv_to_iso_local
                (mapped_ext_zero_component_bridge_local N M I (n + 2))).hom := by
        -- The outgoing differential is the next successor differential.
        simpa [S, T] using mapped_ext_zero_component_d_comm_hom_local N M I (n + 1)
      let eShort : S.homology ≃+ T.homology :=
        shortComplex_homology_add_equiv_of_componentwise_add_equiv_local
          (mapped_ext_zero_component_bridge_local N M I n)
          (mapped_ext_zero_component_bridge_local N M I (n + 1))
          (mapped_ext_zero_component_bridge_local N M I (n + 2))
          hcomm₁₂ hcomm₂₃
      exact
        (E.homologyIsoSc' n (n + 1) (n + 2) hprev hnext).addCommGroupIsoToAddEquiv.trans <|
          eShort.trans <|
            ((Kr.homologyIsoSc' n (n + 1) (n + 2) hprev hnext).symm.addCommGroupIsoToAddEquiv)

/-- Helper for Lemma 15.70.5: for a chosen injective resolution, the homology of the mapped
degree-zero Ext cocomplex identifies with the module Ext group in degree `p`. -/
private noncomputable def mapped_ext_zero_cocomplex_homology_equiv_abelian_ext_local
    (N M : Mod) (I : InjectiveResolution M) (p : ℕ) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
      (((Abelian.extFunctorObj N 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex)) ≃+
      CategoryTheory.Abelian.Ext N M p := by
  -- Route correction: compute mapped `Ext^0` homology by comparing it degreewise with the full
  -- `ℤ`-indexed Hom complex used by `InjectiveResolution.extAddEquivCohomologyClass`.
  cases p with
  | zero =>
      exact
        (mapped_ext_zero_homology_add_equiv_restricted_hom_local N M I 0).trans <|
          (restricted_hom_complex_homology_iso_nat_zero_local N M I).addCommGroupIsoToAddEquiv.trans <|
            (I.extAddEquivCohomologyClass.trans
              (CochainComplex.HomComplex.homologyAddEquiv
                ((singleCpx₀).obj N)
                I.cochainComplex 0).symm).symm
  | succ n =>
      exact
        (mapped_ext_zero_homology_add_equiv_restricted_hom_local N M I (n + 1)).trans <|
          (restricted_hom_complex_homology_iso_nat_succ_local N M I n).addCommGroupIsoToAddEquiv.trans <|
            (I.extAddEquivCohomologyClass.trans
              (CochainComplex.HomComplex.homologyAddEquiv
                ((singleCpx₀).obj N)
                I.cochainComplex (n + 1)).symm).symm

/-- Helper for Lemma 15.70.5: objectwise, the `p`-th right derived functor of
`Ext^0_R(N,-)` agrees with the usual module `Ext^p_R(N,-)`. -/
private noncomputable def rightDerived_ext_zero_obj_iso_abelian_ext_local
    (N M : Mod) (p : ℕ) :
    ((((Abelian.extFunctorObj N 0).rightDerived p).obj M) ≅
      AddCommGrpCat.of (CategoryTheory.Abelian.Ext N M p)) := by
  let I : InjectiveResolution M := injectiveResolution M
  -- Compute the derived value on the chosen injective resolution, then apply the objectwise
  -- Ext-computation equivalence.
  exact
    (I.isoRightDerivedObj (Abelian.extFunctorObj N 0) p) ≪≫
      (mapped_ext_zero_cocomplex_homology_equiv_abelian_ext_local N M I p).toAddCommGrpIso

/-- Helper for Lemma 15.70.5: if the target module is zero, then the derived value
`R^p Ext^0_R(N,-)` vanishes on that module. -/
private theorem rightDerived_ext_zero_obj_isZero_of_isZero_local
    (N M : Mod) (p : ℕ) (hM : IsZero M) :
    IsZero ((((Abelian.extFunctorObj N 0).rightDerived p).obj M)) := by
  have hzeroExt :
      IsZero (AddCommGrpCat.of (CategoryTheory.Abelian.Ext N M p)) := by
    simpa [Abelian.extFunctorObj_obj_coe] using
      (Abelian.extFunctorObj N p).map_isZero hM
  exact (rightDerived_ext_zero_obj_iso_abelian_ext_local N M p).isZero_iff.mpr hzeroExt

/-- Helper for Lemma 15.70.5: if the target module has injective dimension at most `m`, then the
derived value `R^p Ext^0_R(N,-)` vanishes for every degree `p > m`. -/
private theorem rightDerived_ext_zero_obj_isZero_of_injectiveDimension_le_out_of_range_local
    (N M : Mod) (m p : ℕ) (hM : injectiveDimension M ≤ m) (hp : m < p) :
    IsZero ((((Abelian.extFunctorObj N 0).rightDerived p).obj M)) := by
  letI : HasInjectiveDimensionLT M (m + 1) :=
    (injectiveDimension_le_iff M m).1 hM
  have hzeroExt : IsZero (AddCommGrpCat.of (CategoryTheory.Abelian.Ext N M p)) := by
    letI : Subsingleton (CategoryTheory.Abelian.Ext N M p) := by
      refine ⟨fun x y ↦ ?_⟩
      have hx : x = 0 :=
        CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT x (m + 1) (by omega)
      have hy : y = 0 :=
        CategoryTheory.Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT y (m + 1) (by omega)
      rw [hx, hy]
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact (rightDerived_ext_zero_obj_iso_abelian_ext_local N M p).isZero_iff.mpr hzeroExt

/-- Helper for Lemma 15.70.5: after applying `Ext^0_R(N,-)` to a Cartan-Eilenberg resolution,
the resulting double complex still has finite antidiagonal support. -/
private theorem mapped_ext_zero_cartan_eilenberg_has_finite_antidiagonal_support_local
    (N : Mod) (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K) :
    let T :=
      (((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj CE.doubleComplex.obj
    doubleComplexHasFiniteAntidiagonalSupport T := by
  let T :=
    (((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj CE.doubleComplex.obj
  obtain ⟨a, ha⟩ :=
    (CochainComplex.plus_iff (C := CochainComplex Mod ℤ) CE.doubleComplex.obj).mp
      CE.doubleComplex.property
  intro n
  -- Proof comment: any nonzero term on the antidiagonal `p + q = n` must satisfy the horizontal
  -- lower bound `a ≤ p` and the vertical lower bound `0 ≤ q = n - p`.
  refine (Set.finite_Icc a n).subset ?_
  intro p hp
  constructor
  · by_contra hpa
    have hp_lt : p < a := lt_of_not_ge hpa
    have hzeroColumn : IsZero (CE.doubleComplex.obj.X p) := by
      let _ : CE.doubleComplex.obj.IsStrictlyGE a := ha
      exact CE.doubleComplex.obj.isZero_of_isGE a p hp_lt
    have hzeroSource : IsZero ((CE.doubleComplex.obj.X p).X (n - p)) :=
      (HomologicalComplex.eval Mod (ComplexShape.up ℤ) (n - p)).map_isZero hzeroColumn
    have hzeroTarget : IsZero ((T.X p).X (n - p)) := by
      simpa [T, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
        (Abelian.extFunctorObj N 0).map_isZero hzeroSource
    exact hp hzeroTarget
  · by_contra hpn
    have hn_lt : n < p := lt_of_not_ge hpn
    have hzeroSource : IsZero ((CE.doubleComplex.obj.X p).X (n - p)) := by
      let _ : CochainComplex.IsStrictlyGE (CE.doubleComplex.obj.X p) 0 :=
        CE.vertical_isStrictlyGE p
      exact (CE.doubleComplex.obj.X p).isZero_of_isGE 0 (n - p) (by omega)
    have hzeroTarget : IsZero ((T.X p).X (n - p)) := by
      simpa [T, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
        (Abelian.extFunctorObj N 0).map_isZero hzeroSource
    exact hp hzeroTarget

/-- Helper for Lemma 15.70.5: if the target module is zero, then every derived `Ext` group from
`N[0]` into that target vanishes. -/
private theorem ext_single_zero_target_isZero_local
    (N M : Mod) (i : ℤ) (hM : IsZero M) :
    IsZero (AddCommGrpCat.of (Ext^i((single₀).obj N, (single₀).obj M))) := by
  have hsingle : IsZero ((single₀).obj M) :=
    (DerivedCategory.singleFunctor Mod (0 : ℤ)).map_isZero hM
  have hshift : IsZero (((single₀).obj M)⟦i⟧) :=
    (shiftFunctor DMod i).map_isZero hsingle
  -- Every morphism into a zero target shift agrees, so the `Ext` group is subsingleton.
  letI : Subsingleton (Ext^i((single₀).obj N, (single₀).obj M)) :=
    ⟨fun f g ↦ hshift.eq_of_tgt f g⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.70.5: if a target module has injective dimension at most `m`, then
`Ext^i(N[0], M[0])` vanishes outside the interval `[0, m]`. -/
private theorem ext_single_zero_target_module_isZero_of_injectiveDimension_le_local
    (N M : Mod) (m : ℕ) (i : ℤ)
    (hM : injectiveDimension M ≤ m) (hi : i ∉ Set.Icc (0 : ℤ) m) :
    IsZero (AddCommGrpCat.of (Ext^i((single₀).obj N, (single₀).obj M))) := by
  have hAmp :
      HasInjectiveAmplitudeIn ((single₀).obj M) 0 m :=
    single_zero_hasInjectiveAmplitudeIn_of_module_le M m hM
  have hvan :
      ∀ (N' : ModuleCat R) (j : ℤ), j ∉ Set.Icc (0 : ℤ) m →
        ∀ e : Ext^j((single₀).obj N', (single₀).obj M), e = 0 :=
    ((injectiveAmplitudeIn_ext_vanishing_tfae ((single₀).obj M) 0 m).out 0 1).mp hAmp
  -- Convert the source-facing vanishing criterion into a zero object of `AddCommGrpCat`.
  letI : Subsingleton (Ext^i((single₀).obj N, (single₀).obj M)) :=
    ⟨fun x y ↦ by rw [hvan N i hi x, hvan N i hi y]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.70.5: in negative vertical degrees, applying `Ext^0_R(N,-)` to any
Cartan-Eilenberg column gives zero homology. -/
private theorem mapped_cartan_eilenberg_column_homology_isZero_of_neg_local
    (N : Mod) (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K)
    (p q : ℤ) (hq : q < 0) :
    IsZero
      ((((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CE.doubleComplex.obj.X p)).homology q) := by
  let C :=
    (((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CE.doubleComplex.obj.X p))
  have hzeroSource : IsZero ((CE.doubleComplex.obj.X p).X q) := by
    let _ : CochainComplex.IsStrictlyGE (CE.doubleComplex.obj.X p) 0 :=
      CE.vertical_isStrictlyGE p
    exact (CE.doubleComplex.obj.X p).isZero_of_isGE 0 q hq
  have hzeroTarget : IsZero (C.X q) := by
    simpa [C, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (Abelian.extFunctorObj N 0).map_isZero hzeroSource
  -- The middle object of the short complex computing `H^q(C)` is zero, so the homology vanishes.
  simpa [C] using
    (ShortComplex.isZero_homology_of_isZero_X₂ (S := C.sc q) (by simpa using hzeroTarget))

/-- Helper for Lemma 15.70.5: the Chapter 13 abutment object attached to `L` when applying the
bounded-below total right derived functor of `Ext^0_R(N,-)` and then taking degree-`i`
homology. -/
private abbrev boundedBelow_rightDerived_abutment_obj_local
    (N : Mod) (L : CochainComplex.Plus Mod) (i : ℤ) : AddCommGrpCat :=
  ((ObjectProperty.ι (DerivedCategory.TStructure.t.plus : ObjectProperty (D AddCommGrpCat)) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat i).obj
    ((Functor.totalRightDerived
        (mapBoundedBelowHomotopyCategoryToDerivedBelow (Abelian.extFunctorObj N 0))
        (mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 Mod))
        (boundedBelowHomotopyQuasiIso Mod)).obj
      ((HomotopyCategory.Plus.quotient Mod ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 Mod)).obj L)))

/-- Helper for Lemma 15.70.5: after choosing the canonical injective resolution of `L.obj`, the
Chapter 13 abutment identifies with the degree-`i` homology of the Hom complex from `N[0]` into
that injective model. -/
private noncomputable def boundedBelow_rightDerived_abutment_iso_homology_hom_complex_local
    (N : Mod) (L : CochainComplex.Plus Mod) (i : ℤ) :
    boundedBelow_rightDerived_abutment_obj_local N L i ≅
      AddCommGrpCat.of
        ((CochainComplex.HomComplex ((singleCpx₀).obj N)
          (((injectiveResolution L.obj : InjectiveResolution L.obj) : CochainComplex Mod ℤ)))
          .homology i) := by
  -- Route correction: keep the source-faithful spectral-sequence route, but isolate the remaining
  -- owner-level transport from the total-right-derived abutment to the concrete injective model.
  let Ires : InjectiveResolution L.obj := injectiveResolution L.obj
  let Iplus : CochainComplex.InjectivePlus Mod := Ires
  let X : K⁺(Mod) := (HomotopyCategory.Plus.quotient Mod).obj L
  let Y : K⁺(Mod) := (HomotopyCategory.Plus.quotient Mod).obj Iplus
  let Fplus := mapBoundedBelowHomotopyCategoryToDerivedBelow (Abelian.extFunctorObj N 0)
  let Qplus := mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 Mod)
  let RF := Functor.totalRightDerived Fplus Qplus (boundedBelowHomotopyQuasiIso Mod)
  have hIresQis :
      boundedBelowHomotopyQuasiIso Mod
        ((HomotopyCategory.Plus.quotient Mod).map Ires.ι) := by
    -- The injective-resolution augmentation is a quasi-isomorphism already in the ambient
    -- homotopy category, hence also after restricting to the bounded-below subcategory.
    change
      HomotopyCategory.quasiIso Mod (ComplexShape.up ℤ)
        ((HomotopyCategory.plus Mod).ι.map
          ((HomotopyCategory.Plus.quotient Mod).map Ires.ι))
    simpa using
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (C := Mod) (c := ComplexShape.up ℤ) Ires.ι).2
        (by infer_instance : QuasiIso Ires.ι)
  have hRFmap :
      IsIso (RF.map (Qplus.map ((HomotopyCategory.Plus.quotient Mod).map Ires.ι))) := by
    exact
      Functor.totalRightDerived_map_isIso_of_mem
        (S := boundedBelowHomotopyQuasiIso Mod)
        (F := Fplus)
        ((HomotopyCategory.Plus.quotient Mod).map Ires.ι)
        hIresQis
  have hComputeY :
      Fplus.ComputesRightDerivedAt (boundedBelowHomotopyQuasiIso Mod) Y := by
    -- The canonical injective replacement is a bounded-below injective complex, so it computes
    -- the bounded-below right derived functor directly.
    simpa [Fplus, Y, Iplus] using
      (boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := Fplus) (I := Iplus))
  have hUnitY :
      IsIso
        (((Functor.totalRightDerivedUnit
            Fplus
            Qplus
            (boundedBelowHomotopyQuasiIso Mod)).app Y)) := by
    exact
      (Functor.computesRightDerivedAt_iff
        (F := Fplus) (S := boundedBelowHomotopyQuasiIso Mod) (X := Y)).1
        hComputeY
  let eTransport :
      RF.obj (Qplus.obj X) ≅ RF.obj (Qplus.obj Y) :=
    asIso (RF.map (Qplus.map ((HomotopyCategory.Plus.quotient Mod).map Ires.ι)))
  let eCompute :
      RF.obj (Qplus.obj Y) ≅ Fplus.obj Y :=
    (asIso
      (((Functor.totalRightDerivedUnit
          Fplus
          Qplus
          (boundedBelowHomotopyQuasiIso Mod)).app Y))).symm
  let ePlus :
      (ObjectProperty.ι (DerivedCategory.TStructure.t.plus : ObjectProperty (D AddCommGrpCat))).obj
          (Fplus.obj Y) ≅
        (mapHomotopyCategoryToDerived (𝒜 := Mod) (Abelian.extFunctorObj N 0)).obj
          ((ObjectProperty.ι (HomotopyCategory.plus Mod)).obj Y) :=
    (mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso
      (F := Abelian.extFunctorObj N 0)).app Y
  let eHomology :
      ((DerivedCategory.homologyFunctor AddCommGrpCat i).obj
          ((mapHomotopyCategoryToDerived (𝒜 := Mod) (Abelian.extFunctorObj N 0)).obj
            ((ObjectProperty.ι (HomotopyCategory.plus Mod)).obj Y))) ≅
        AddCommGrpCat.of
          ((CochainComplex.HomComplex ((singleCpx₀).obj N)
            (((injectiveResolution L.obj : InjectiveResolution L.obj) :
              CochainComplex Mod ℤ))).homology i) := by
    -- The homotopy-category representative is exactly the mapped injective complex, whose
    -- degreewise description is the full Hom complex from `N[0]`.
    simpa [Y, Iplus, Ires, mapHomotopyCategoryToDerived,
      Functor.mapHomotopyCategory_obj, Functor.mapHomologicalComplex_obj_X,
      Functor.mapHomologicalComplex_obj_d, Abelian.extFunctorObj_obj_coe,
      Abelian.extFunctorObj_map] using
      (((DerivedCategory.homologyFunctorFactorsh AddCommGrpCat i).app
        (((Abelian.extFunctorObj N 0).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((ObjectProperty.ι (HomotopyCategory.plus Mod)).obj Y))).symm)
  -- Transport the abutment along the injective resolution, compute the derived functor on the
  -- injective model, then read off the homology of the resulting mapped Hom complex.
  exact
    (DerivedCategory.homologyFunctor AddCommGrpCat i).mapIso
        ((ObjectProperty.ι
          (DerivedCategory.TStructure.t.plus : ObjectProperty (D AddCommGrpCat))).mapIso
          eTransport) ≪≫
      (DerivedCategory.homologyFunctor AddCommGrpCat i).mapIso
        ((ObjectProperty.ι
          (DerivedCategory.TStructure.t.plus : ObjectProperty (D AddCommGrpCat))).mapIso
          eCompute) ≪≫
      (DerivedCategory.homologyFunctor AddCommGrpCat i).mapIso ePlus ≪≫
      eHomology

/-- Helper for Lemma 15.70.5: the Hom-complex homology of the canonical injective model of
`L.obj` computes the user-facing derived `Ext` group. -/
private noncomputable def homology_hom_complex_iso_ext_local
    (N : Mod) (L : CochainComplex.Plus Mod) (i : ℤ) :
    AddCommGrpCat.of
      ((CochainComplex.HomComplex ((singleCpx₀).obj N)
        (((injectiveResolution L.obj : InjectiveResolution L.obj) : CochainComplex Mod ℤ)))
        .homology i) ≅
      AddCommGrpCat.of (Ext^i((single₀).obj N, Q.obj L.obj)) := by
  let Ires : InjectiveResolution L.obj := injectiveResolution L.obj
  let Iplus : CochainComplex.InjectivePlus Mod := Ires
  let eHomology :
      AddCommGrpCat.of
          ((CochainComplex.HomComplex ((singleCpx₀).obj N)
            ((Iplus : CochainComplex Mod ℤ))).homology i) ≅
        AddCommGrpCat.of
          (Ext^i((single₀).obj N, DerivedCategory.Q.obj (Iplus : CochainComplex Mod ℤ))) :=
    (single_source_homology_add_equiv_ext_of_bounded_below_injective
      (R := R) Iplus N i).toAddCommGrpIso
  let eTarget : DerivedCategory.Q.obj (Iplus : CochainComplex Mod ℤ) ≅ Q.obj L.obj :=
    asIso (DerivedCategory.Q.map Ires.ι)
  let eExt :
      Ext^i((single₀).obj N, DerivedCategory.Q.obj (Iplus : CochainComplex Mod ℤ)) ≃+
        Ext^i((single₀).obj N, Q.obj L.obj) :=
    { toEquiv := (Iso.refl _).homCongr ((shiftFunctor DMod i).mapIso eTarget)
      map_add' := by
        intro f g
        simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp] }
  -- First compute Ext against the injective model, then transport along the quasi-isomorphism
  -- from that model back to `L.obj`.
  exact eHomology ≪≫ ulift_add_equiv_to_iso_local eExt

/-- Helper for Lemma 15.70.5: both spectral-sequence arguments reduce to transporting the
Chapter 13 abutment for `Ext^0_R(N,-)` to the user-facing group
`Ext^i((single₀).obj N, Q.obj L.obj)`. -/
private theorem ext_zero_of_boundedBelow_rightDerived_abutment_isZero_local
    (N : Mod) (L : CochainComplex.Plus Mod) (i : ℤ)
    (hab : IsZero (boundedBelow_rightDerived_abutment_obj_local N L i))
    (e : Ext^i((single₀).obj N, Q.obj L.obj)) :
    e = 0 := by
  -- Route correction: the remaining owner-level gap is now isolated once, instead of being
  -- duplicated in the two spectral-sequence endgames below.
  let eAbutment :=
    boundedBelow_rightDerived_abutment_iso_homology_hom_complex_local N L i
  let eExt := homology_hom_complex_iso_ext_local N L i
  have hzeroExt :
      IsZero (AddCommGrpCat.of (Ext^i((single₀).obj N, Q.obj L.obj))) := by
    -- Transport the zero-object hypothesis across the concrete Hom-complex model and then to Ext.
    exact (eAbutment ≪≫ eExt).isZero_iff.mp hab
  letI : Subsingleton (Ext^i((single₀).obj N, Q.obj L.obj)) :=
    AddCommGrpCat.subsingleton_of_isZero hzeroExt
  -- Once the target Ext group is a zero object, every class is equal to `0`.
  exact Subsingleton.elim _ _

/-- Helper for Lemma 15.70.5: for the second filtration, the fixed-`q` associated `E₁` slice is
the textbook second page-one complex. -/
private noncomputable def associated_pageOneComplex_iso_of_secondDoubleComplex_local
    (K : HomologicalComplex₂ AddCommGrpCat (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence AddCommGrpCat 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (q : ℤ) :
    CategoryTheory.Lemma_15_65_16.associatedPageOneComplex E q ≅
      secondDoubleComplexPageOneComplex K q :=
  -- Proof comment: the theorem-local spectral-comparison API rewrites the fixed-`q` `E₁` slice
  -- degreewise, and the `d₁` squares are exactly the second-filtration page-one differential
  -- commutativities.
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ by
      simpa
        [CategoryTheory.Lemma_15_65_16.associatedPageOneComplex, secondDoubleComplexPageOne_def]
        using (FilteredComplex.pageOneIso (secondDoubleComplexFilteredComplex K) E p q))
    (fun p p' hpp' ↦ by
      have hp : p + 1 = p' := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpp'
      subst hp
      -- The fixed-`q` `E₁` differential is the ambient `d₁` map at bidegree `(p,q)`.
      simpa [CategoryTheory.Lemma_15_65_16.associatedPageOneComplex] using
        (FilteredComplex.pageOne_d_commSq
          (secondDoubleComplexFilteredComplex K) E p q))

/-- Helper for Lemma 15.70.5: the fixed-`q` second `E₁` complex of the mapped Cartan-Eilenberg
double complex is the mapped chosen resolution of `H^q(K)`. -/
private noncomputable theorem image_resolution_component_iso_to_row_image_ext_zero_local
    (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K) (p q : ℤ) :
    (((CE.imageResolution (q - 1)).cochainComplex).X p) ≅
      image (((CE.doubleComplex.obj.flip.X p).d (q - 1) q)) := by
  -- Proof comment: `CE.imageIso (q - 1)` identifies the image resolution with the whole rowwise
  -- image complex, and evaluation at horizontal degree `p` extracts the desired term.
  simpa using
    (HomologicalComplex.eval Mod (ComplexShape.up ℤ) p).mapIso
      (CE.imageIso (q - 1))

/-- Helper for Lemma 15.70.5: evaluating the chosen cycles resolution at horizontal degree `p`
recovers the cycles of the fixed row in degree `q`. -/
private noncomputable theorem cycles_resolution_component_iso_to_row_cycles_ext_zero_local
    (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K) (p q : ℤ) :
    (((CE.cyclesResolution q).cochainComplex).X p) ≅
      ((CE.doubleComplex.obj.flip.X p).cycles q) := by
  -- Proof comment: `CE.cyclesIso q` is already the rowwise cycles comparison, so evaluation gives
  -- the fixed horizontal component directly.
  simpa using
    (HomologicalComplex.eval Mod (ComplexShape.up ℤ) p).mapIso
      (CE.cyclesIso q)

/-- Helper for Lemma 15.70.5: evaluating the chosen horizontal-homology resolution at horizontal
degree `p` recovers the homology of the fixed row in degree `q`. -/
private noncomputable theorem homology_resolution_component_iso_to_row_homology_ext_zero_local
    (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K) (p q : ℤ) :
    (((CE.homologyResolution q).cochainComplex).X p) ≅
      ((CE.doubleComplex.obj.flip.X p).homology q) := by
  -- Proof comment: `CE.homologyIso q` identifies the chosen homology resolution with the rowwise
  -- homology complex, and evaluation at `p` extracts the component used on the second `E₁` page.
  simpa using
    (HomologicalComplex.eval Mod (ComplexShape.up ℤ) p).mapIso
      (CE.homologyIso q)

/-- Helper for Lemma 15.70.5: after applying `Ext^0_R(N,-)`, the degree-`p` term of the chosen
homology resolution agrees with `Ext^0_R(N,-)` applied to the row homology in degree `q`. -/
private noncomputable theorem mapped_homology_resolution_component_iso_to_mapped_row_homology_ext_zero_local
    (N : Mod) (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K) (p q : ℤ) :
    ((((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CE.homologyResolution q).cochainComplex)).X p) ≅
      (Abelian.extFunctorObj N 0).obj ((CE.doubleComplex.obj.flip.X p).homology q) := by
  -- Proof comment: first transport the degree-`p` term of the chosen homology resolution to the
  -- actual row homology, then apply `Ext^0_R(N,-)` to that comparison.
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (Abelian.extFunctorObj N 0).mapIso
      (homology_resolution_component_iso_to_row_homology_ext_zero_local
        (K := K) (CE := CE) p q)

/-- Helper for Lemma 15.70.5: the fixed-`q` second `E₁` complex of the mapped Cartan-Eilenberg
double complex is the mapped chosen resolution of `H^q(K)`. -/
private noncomputable theorem second_page_one_complex_iso_to_mapped_homology_resolution_ext_zero_local
    (N : Mod) (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K) (q : ℤ) :
    secondDoubleComplexPageOneComplex
        ((((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          CE.doubleComplex.obj)
        q ≅
      ((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CE.homologyResolution q).cochainComplex) := by
  -- Proof comment: this is the remaining owner-level bridge from the second `E₁` row complex to
  -- the mapped homology-resolution complex.
  -- TODO: assemble the componentwise row-homology comparisons using the degreewise split short
  -- exact sequences coming from the Cartan-Eilenberg rows, then check the `d₁` compatibility via
  -- `secondDoubleComplexPageOneDifferential_def`.
  sorry

/-- Helper for Lemma 15.70.5: the mapped homology-resolution complex has zero homology in every
negative degree. -/
private theorem mapped_homology_resolution_homology_isZero_of_neg_local
    (N : Mod) (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K)
    (p q : ℤ) (hp : p < 0) :
    IsZero
      ((((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CE.homologyResolution q).cochainComplex)).homology p) := by
  let C :=
    ((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CE.homologyResolution q).cochainComplex)
  have hzeroSource : IsZero (((CE.homologyResolution q).cochainComplex).X p) := by
    let _ : CochainComplex.IsStrictlyGE ((CE.homologyResolution q).cochainComplex) 0 := inferInstance
    exact ((CE.homologyResolution q).cochainComplex).isZero_of_isGE 0 p hp
  have hzeroTarget : IsZero (C.X p) := by
    simpa [C, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (Abelian.extFunctorObj N 0).map_isZero hzeroSource
  -- Proof comment: a cochain complex with zero middle term at degree `p` has zero `p`-th
  -- homology.
  simpa [C] using
    (ShortComplex.isZero_homology_of_isZero_X₂ (S := C.sc p) (by simpa using hzeroTarget))

/-- Helper for Lemma 15.70.5: negative first indices already vanish on the second `E₂` page once
the fixed-`q` `E₁` slice is rewritten as the mapped homology-resolution complex. -/
private theorem second_page_two_negative_column_isZero_local
    (N : Mod) (K : CochainComplex.Plus Mod) (CE : CartanEilenbergResolution K)
    (E : CohomologicalSpectralSequence AddCommGrpCat 0)
    (hAssoc :
      IsAssociatedToFilteredComplex
        (secondDoubleComplexFilteredComplex
          ((((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            CE.doubleComplex.obj))
        E)
    (p q : ℤ) (hp : p < 0) :
    IsZero ((E.page 2).X (p, q)) := by
  let T :=
    (((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj CE.doubleComplex.obj
  let C :=
    ((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CE.homologyResolution q).cochainComplex)
  letI : IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex T) E := by
    simpa [T] using hAssoc
  let eAssoc :
      CategoryTheory.Lemma_15_65_16.associatedPageOneComplex E q ≅
        secondDoubleComplexPageOneComplex T q :=
    associated_pageOneComplex_iso_of_secondDoubleComplex_local (K := T) (E := E) q
  let ePageOne :
      secondDoubleComplexPageOneComplex T q ≅ C :=
    second_page_one_complex_iso_to_mapped_homology_resolution_ext_zero_local N K CE q
  rcases
      CategoryTheory.Lemma_15_65_16.associated_pageTwo_iso_of_pageOne_complex_iso_local
        (E := E) (p := p) (q := q) (C := C) (eAssoc ≪≫ ePageOne) with
    ⟨ePageTwo⟩
  -- Proof comment: after the page-two comparison, negative columns vanish because the mapped
  -- homology-resolution complex is supported in degrees `≥ 0`.
  exact (ePageTwo.isZero_iff).mpr
    (mapped_homology_resolution_homology_isZero_of_neg_local N K CE p q hp)

/-- Helper for Lemma 15.70.5: bounded support together with a common module injective-dimension
bound on the cohomology objects forces vanishing of `Ext` outside `[c, d + m]`. -/
lemma ext_isZero_outside_interval_of_bounded_homology_injective_bound_local
    (K : DbMod) (c d : ℤ) (m : ℕ)
    (hGE : K.obj.IsGE c) (hLE : K.obj.IsLE d)
    (hH :
      ∀ q : ℤ, c ≤ q → q ≤ d →
        injectiveDimension ((Hb q).obj K) ≤ m) :
    ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc c (d + m) →
      ∀ e : Ext^i((single₀).obj N, K.obj), e = 0 := by
  intro N i hi e
  -- Route correction: the truncation/Postnikov route drifted from the source. The intended proof
  -- uses Lemma `13.21.3` for `Hom_R(N,-)` and reads eventual `Ext`-vanishing from the second
  -- spectral sequence.
  classical
  let Kplus : CochainComplex.Plus Mod :=
    ⟨DerivedCategory.Q.objPreimage K.obj, by
      -- Proof comment: the bounded-below hypothesis on `K` transports to its fixed preimage.
      rw [CochainComplex.isGE_iff]
      intro n hn
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      have hzeroK : IsZero ((H n).obj K.obj) := isZero_of_isGE K.obj c n hn
      exact (objPreimage_homology_iso K.obj n).isZero_iff.mp hzeroK⟩
  obtain ⟨CE⟩ := exists_cartanEilenbergResolution (K := Kplus)
  let T :=
    (((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj CE.doubleComplex.obj
  let FI₂ := secondDoubleComplexFilteredComplex T
  have hfin : doubleComplexHasFiniteAntidiagonalSupport T := by
    simpa [T] using
      mapped_ext_zero_cartan_eilenberg_has_finite_antidiagonal_support_local
        (N := N) (K := Kplus) (CE := CE)
  let s : Finset (ℤ × ℤ) := (Finset.Icc (0 : ℤ) m).product (Finset.Icc c d)
  have hiSupport : i ∉ s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2) := by
    intro hiSupport
    rcases Finset.mem_image.mp hiSupport with ⟨pq, hpq, hsum⟩
    rcases Finset.mem_product.mp hpq with ⟨hp, hq⟩
    have hp' : pq.1 ∈ Set.Icc (0 : ℤ) m := by simpa using hp
    have hq' : pq.2 ∈ Set.Icc c d := by simpa using hq
    have hi' : i = pq.1 + pq.2 := by simpa using hsum.symm
    have hmem : i ∈ Set.Icc c (d + m) := by
      constructor <;> omega
    exact hi hmem
  obtain ⟨firstSpectralSequence, secondSpectralSequence, hAssoc₁, hAssoc₂, firstPageOneIso,
      secondPageTwoIso, targetIso, hBounded₁, hCoh₁, hConv₁, hBounded₂, hCoh₂, hConv₂⟩ :=
    exists_cartanEilenberg_rightDerived_spectralSequences
      (F := Abelian.extFunctorObj N 0) (K := Kplus) (CE := CE)
  letI : IsAssociatedToFilteredComplex FI₂ secondSpectralSequence := by
    simpa [FI₂, T] using hAssoc₂
  have hs :
      ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s →
        IsZero ((secondSpectralSequence.page 2).X (pq.1, pq.2)) := by
    intro pq hpq
    by_cases hpneg : pq.1 < 0
    · -- Negative columns are handled by the all-integer page-two comparison from the fixed-`q`
      -- `E₁` slice to the mapped homology-resolution complex.
      exact
        second_page_two_negative_column_isZero_local
          N Kplus CE secondSpectralSequence hAssoc₂ pq.1 pq.2 hpneg
    · have hpnonneg : 0 ≤ pq.1 := le_of_not_gt hpneg
      obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hpnonneg
      by_cases hqIn : pq.2 ∈ Set.Icc c d
      · have hpOut : (p : ℤ) ∉ Set.Icc (0 : ℤ) m := by
          intro hpIn
          exact hpq <| Finset.mem_product.mpr ⟨by simpa using hpIn, by simpa using hqIn⟩
        have hpgt : m < p := by
          omega
        have hpageZeroHb :
            IsZero
              ((((Abelian.extFunctorObj N 0).rightDerived p).obj
                ((Hb pq.2).obj K))) :=
          rightDerived_ext_zero_obj_isZero_of_injectiveDimension_le_out_of_range_local
            N ((Hb pq.2).obj K) m p (hH pq.2 hqIn.1 hqIn.2) hpgt
        have hpageZero :
            IsZero
              ((((Abelian.extFunctorObj N 0).rightDerived p).obj
                (Kplus.obj.homology pq.2))) := by
          simpa using
            (((Abelian.extFunctorObj N 0).rightDerived p).mapIso
              (objPreimage_homology_iso K.obj pq.2)).isZero_iff.mp hpageZeroHb
        exact hpageZero.of_iso (secondPageTwoIso p pq.2).symm
      · have hzeroHomology : IsZero (Kplus.obj.homology pq.2) := by
          by_cases hqLow : pq.2 < c
          · have hzeroK : IsZero ((H pq.2).obj K.obj) := isZero_of_isGE K.obj c pq.2 hqLow
            exact (objPreimage_homology_iso K.obj pq.2).isZero_iff.mp hzeroK
          · have hqHigh : d < pq.2 := by
              by_contra hqHigh
              exact hqIn ⟨le_of_not_gt hqLow, le_of_not_gt hqHigh⟩
            have hzeroK : IsZero ((H pq.2).obj K.obj) := isZero_of_isLE K.obj d pq.2 hqHigh
            exact (objPreimage_homology_iso K.obj pq.2).isZero_iff.mp hzeroK
        have hpageZero :
            IsZero
              ((((Abelian.extFunctorObj N 0).rightDerived p).obj
                (Kplus.obj.homology pq.2))) :=
          rightDerived_ext_zero_obj_isZero_of_isZero_local N (Kplus.obj.homology pq.2) p
            hzeroHomology
        exact hpageZero.of_iso (secondPageTwoIso p pq.2).symm
  have hcohom :
      IsZero (FI₂.underlying.homology i) :=
    cohomology_isZero_of_not_mem_totalDegree_image_support
      FI₂ secondSpectralSequence
      (secondDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport T hfin)
      (by decide : (0 : ℤ) ≤ 2) s hs hiSupport
  have hab :
      IsZero
        (((ObjectProperty.ι (DerivedCategory.TStructure.t.plus : ObjectProperty (D AddCommGrpCat)) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat i).obj
          ((Functor.totalRightDerived
              (mapBoundedBelowHomotopyCategoryToDerivedBelow (Abelian.extFunctorObj N 0))
              (mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 Mod))
              (boundedBelowHomotopyQuasiIso Mod)).obj
            ((HomotopyCategory.Plus.quotient Mod ⋙
                mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 Mod)).obj Kplus)))) := by
    exact (targetIso i).isZero_iff.mp hcohom
  exact ext_zero_of_boundedBelow_rightDerived_abutment_isZero_local N Kplus i hab e

/-- Helper for Lemma 15.70.5: on the explicit `ModuleCat R` surface, Ext-vanishing outside an
interval packages directly as injective amplitude in that interval. -/
lemma injectiveAmplitudeIn_ext_vanishing_tfae_module_surface_local
    (K : DMod) (a b : ℤ)
    (hExt :
      ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc a b →
        ∀ e : Ext^i((single₀).obj N, K), e = 0) :
    HasInjectiveAmplitudeIn K a b := by
  -- This is exactly the module-surface implication `(2) → (1)` from Lemma `15.70.2`.
  exact ((injectiveAmplitudeIn_ext_vanishing_tfae K a b).out 1 0).mp hExt

/-- Helper for Lemma 15.70.5: bounded support together with a common module injective-dimension
bound on the terms of a bounded complex forces vanishing of `Ext` outside `[c, d + m]` for the
represented derived object. -/
lemma ext_isZero_outside_interval_of_bounded_termwise_injective_bound_local
    (K' : Compᵇ(Mod)) (c d : ℤ) (m : ℕ)
    (hGE : K'.obj.IsStrictlyGE c) (hLE : K'.obj.IsStrictlyLE d)
    (hterm :
      ∀ p : ℤ, c ≤ p → p ≤ d →
        injectiveDimension (K'.obj.X p) ≤ m) :
    ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc c (d + m) →
      ∀ e : Ext^i((single₀).obj N, Q.obj K'.obj), e = 0 := by
  intro N i hi e
  -- Route correction: part `(2)` should also follow the source spectral-sequence argument rather
  -- than the discarded truncation induction. Here the first Cartan-Eilenberg spectral sequence is
  -- the correct owner-level bridge.
  classical
  let Kplus : CochainComplex.Plus Mod :=
    ⟨K'.obj, (CochainComplex.plus_iff Mod K'.obj).2 ⟨c, hGE⟩⟩
  obtain ⟨CE⟩ := exists_cartanEilenbergResolution (K := Kplus)
  let T :=
    (((Abelian.extFunctorObj N 0).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj CE.doubleComplex.obj
  let FI₁ := firstDoubleComplexFilteredComplex T
  have hfin : doubleComplexHasFiniteAntidiagonalSupport T := by
    simpa [T] using
      mapped_ext_zero_cartan_eilenberg_has_finite_antidiagonal_support_local
        (N := N) (K := Kplus) (CE := CE)
  let s : Finset (ℤ × ℤ) := (Finset.Icc c d).product (Finset.Icc (0 : ℤ) m)
  have hiSupport : i ∉ s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2) := by
    intro hiSupport
    rcases Finset.mem_image.mp hiSupport with ⟨pq, hpq, hsum⟩
    rcases Finset.mem_product.mp hpq with ⟨hp, hq⟩
    have hp' : pq.1 ∈ Set.Icc c d := by simpa using hp
    have hq' : pq.2 ∈ Set.Icc (0 : ℤ) m := by simpa using hq
    have hi' : i = pq.1 + pq.2 := by simpa using hsum.symm
    have hmem : i ∈ Set.Icc c (d + m) := by
      constructor <;> omega
    exact hi hmem
  obtain ⟨firstSpectralSequence, secondSpectralSequence, hAssoc₁, hAssoc₂, firstPageOneIso,
      secondPageTwoIso, targetIso, hBounded₁, hCoh₁, hConv₁, hBounded₂, hCoh₂, hConv₂⟩ :=
    exists_cartanEilenberg_rightDerived_spectralSequences
      (F := Abelian.extFunctorObj N 0) (K := Kplus) (CE := CE)
  letI : IsAssociatedToFilteredComplex FI₁ firstSpectralSequence := by
    simpa [FI₁, T] using hAssoc₁
  have hs :
      ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s →
        IsZero ((firstSpectralSequence.page 1).X (pq.1, pq.2)) := by
    intro pq hpq
    by_cases hqneg : pq.2 < 0
    · have hcolumn :
          IsZero (firstDoubleComplexPageOne T pq.1 pq.2) := by
        simpa [firstDoubleComplexPageOne_def, T] using
          mapped_cartan_eilenberg_column_homology_isZero_of_neg_local
            (N := N) (K := Kplus) (CE := CE) pq.1 pq.2 hqneg
      exact hcolumn.of_iso
        (FilteredComplex.pageOneIso FI₁ firstSpectralSequence pq.1 pq.2).symm
    · have hqnonneg : 0 ≤ pq.2 := le_of_not_gt hqneg
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hqnonneg
      by_cases hpIn : pq.1 ∈ Set.Icc c d
      · have hqOut : (q : ℤ) ∉ Set.Icc (0 : ℤ) m := by
          intro hqIn
          exact hpq <| Finset.mem_product.mpr ⟨by simpa using hpIn, by simpa using hqIn⟩
        have hqgt : m < q := by
          omega
        have hpageZero :
            IsZero (((Abelian.extFunctorObj N 0).rightDerived q).obj (K'.obj.X pq.1)) :=
          rightDerived_ext_zero_obj_isZero_of_injectiveDimension_le_out_of_range_local
            N (K'.obj.X pq.1) m q (hterm pq.1 hpIn.1 hpIn.2) hqgt
        exact hpageZero.of_iso (firstPageOneIso pq.1 q).symm
      · have hzeroTerm : IsZero (K'.obj.X pq.1) := by
          by_cases hpLow : pq.1 < c
          · exact K'.obj.isZero_of_isStrictlyGE c pq.1 hpLow
          · have hpHigh : d < pq.1 := by
              by_contra hpHigh
              exact hpIn ⟨le_of_not_gt hpLow, le_of_not_gt hpHigh⟩
            exact K'.obj.isZero_of_isStrictlyLE d pq.1 hpHigh
        have hpageZero :
            IsZero (((Abelian.extFunctorObj N 0).rightDerived q).obj (K'.obj.X pq.1)) :=
          rightDerived_ext_zero_obj_isZero_of_isZero_local N (K'.obj.X pq.1) q hzeroTerm
        exact hpageZero.of_iso (firstPageOneIso pq.1 q).symm
  have hcohom :
      IsZero (FI₁.underlying.homology i) :=
    cohomology_isZero_of_not_mem_totalDegree_image_support
      FI₁ firstSpectralSequence
      (firstDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport T hfin)
      (by decide : (0 : ℤ) ≤ 1) s hs hiSupport
  have hab :
      IsZero
        (((ObjectProperty.ι (DerivedCategory.TStructure.t.plus : ObjectProperty (D AddCommGrpCat)) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat i).obj
          ((Functor.totalRightDerived
              (mapBoundedBelowHomotopyCategoryToDerivedBelow (Abelian.extFunctorObj N 0))
              (mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 Mod))
              (boundedBelowHomotopyQuasiIso Mod)).obj
            ((HomotopyCategory.Plus.quotient Mod ⋙
                mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 Mod)).obj Kplus)))) := by
    exact (targetIso i).isZero_iff.mp hcohom
  exact ext_zero_of_boundedBelow_rightDerived_abutment_isZero_local N Kplus i hab e

/-- Lemma 15.70.5 (1): if `K` lies in the bounded derived category `D^b(R)` and each cohomology
module `H^i(K)` has finite injective dimension, then `K` has finite injective dimension. -/
theorem hasFiniteInjectiveDimension_of_bounded_of_homology_finiteInjectiveDimension
    (K : DbMod)
    (hH : ∀ i : ℤ,
      injectiveDimension ((Hb i).obj K) ≠ ⊤) :
    HasFiniteInjectiveDimension K.obj := by
  rcases (derivedCategory_t_bounded_iff K.obj).1 K.property with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  let c' : ℤ := min c d
  have hGE : K.obj.IsGE c' := by
    -- Move the lower bound to `min c d` so the support interval is nonempty on the left.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hc i (lt_of_lt_of_le hi (min_le_left _ _))
  have hLEd : K.obj.IsLE d := by
    -- Keep the original upper support bound from the boundedness witness.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hd i hi
  rcases exists_common_injective_dimension_bound_on_bounded_support K c' d hH with ⟨m, hm⟩
  have hExt :
      ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc c' (d + m) →
        ∀ e : Ext^i((single₀).obj N, K.obj), e = 0 :=
    ext_isZero_outside_interval_of_bounded_homology_injective_bound_local
      K c' d m hGE hLEd hm
  have hAmp : HasInjectiveAmplitudeIn K.obj c' (d + m) := by
    -- Once Ext vanishes outside the interval, the local wrapper packages the amplitude directly.
    exact injectiveAmplitudeIn_ext_vanishing_tfae_module_surface_local K.obj c' (d + m) hExt
  -- The explicit interval `[c', d + m]` gives finite injective dimension.
  exact (hasFiniteInjectiveDimension_iff K.obj).2 ⟨c', d + m, hAmp⟩

-- Proof sketch: for each term `K'ⁱ`, choose a finite injective resolution and splice these
-- resolutions into a bounded double complex representing `DerivedCategory.Q.obj K'`. The total
-- complex is again bounded with injective terms, so it gives a finite injective-amplitude
-- representative of `DerivedCategory.Q.obj K'`.
/-- Lemma 15.70.5 (2): if a bounded cochain complex `K'` has termwise finite injective dimension,
then the represented derived object `Q.obj K'.obj` has finite injective
dimension. The boundedness datum is carried by the chapter owner `Compᵇ(Mod)`. -/
theorem hasFiniteInjectiveDimension_of_bounded_of_termwise_finiteInjectiveDimension
    (K' : Compᵇ(Mod))
    (hterm : ∀ i : ℤ, injectiveDimension (K'.obj.X i) ≠ ⊤) :
    HasFiniteInjectiveDimension (Q.obj K'.obj) := by
  rcases (CochainComplex.bounded_iff Mod K'.obj).1 K'.property with ⟨hplus, hminus⟩
  rcases (CochainComplex.plus_iff Mod K'.obj).1 hplus with ⟨c, hGE⟩
  rcases (CochainComplex.minus_iff Mod K'.obj).1 hminus with ⟨d, hLE⟩
  rcases
      exists_common_injective_dimension_bound_on_terms_of_bounded_complex K' c d hterm with
    ⟨m, hm⟩
  have hExt :
      ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc c (d + m) →
        ∀ e : Ext^i((single₀).obj N, Q.obj K'.obj), e = 0 :=
    ext_isZero_outside_interval_of_bounded_termwise_injective_bound_local
      K' c d m hGE hLE hm
  have hAmp : HasInjectiveAmplitudeIn (Q.obj K'.obj) c (d + m) := by
    -- Apply the same explicit-surface packaging step to the represented derived object.
    exact
      injectiveAmplitudeIn_ext_vanishing_tfae_module_surface_local (Q.obj K'.obj) c (d + m) hExt
  -- The explicit interval `[c, d + m]` gives finite injective dimension.
  exact (hasFiniteInjectiveDimension_iff (Q.obj K'.obj)).2 ⟨c, d + m, hAmp⟩

end

end CategoryTheory
