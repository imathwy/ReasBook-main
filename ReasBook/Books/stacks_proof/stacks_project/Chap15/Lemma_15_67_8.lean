import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_67_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory Mod
local notation "single₀" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/- Domain-style sampling for Lemma 15.67.8:
- primary domain: tor-amplitude in `D(R)` for objects represented by bounded cochain complexes of
  `R`-modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`,
  `Compᵇ(Mod)`;
- best owner abstraction: `HasTorAmplitudeIn` is the tor-amplitude owner, while the presenting
  bounded cochain complex should use the chapter owner `Compᵇ(Mod)` rather than an
  unbundled complex plus a separate boundedness witness;
- primitive vs. derived:
  primitive data are the bounded complex `K : Compᵇ(Mod)`, with underlying cochain
  complex `K.obj`, and the termwise tor-amplitude hypotheses on the shifted single-term objects
  `((single₀).obj (K.obj.X i))⟦i⟧`;
  derived API is the finite-tor-dimension statement, which packages the interval choice after the
  main tor-amplitude theorem rather than introducing a second owner;
- source/core/bridge triage:
  `source-facing`: `hasTorAmplitudeIn_of_bounded_of_termwise_hasTorAmplitudeIn`;
  `core/canonical`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`, and
    `Compᵇ(Mod)`;
  `bridge/view`: the forgetful passage from the bounded cochain complex `K` to its underlying
  cochain complex `K.obj`, then to the shifted degree-zero terms `((single₀).obj (K.obj.X i))⟦i⟧`,
  and finally to the derived object `Q.obj K.obj`.

This keeps the textbook theorem source-facing, but moves its boundedness input to the canonical
chapter owner category and its termwise hypothesis to the intrinsic shifted derived objects rather
than the coordinate-level interval formula `a - i, b - i`.
-/

-- Proof sketch: argue by induction on the length of the bounded complex using stupid
-- truncations. The induction step writes the image of `K` in `D(R)` in a distinguished triangle
-- whose left vertex is a shift of a single term `K.obj.X i`, so Lemma `15.67.5` propagates the
-- shifted tor-amplitude bounds from the terms to the whole complex.
/-- Helper for Lemma 15.67.8: tor-amplitude in a fixed interval is invariant under isomorphism in
`D(R)`. -/
lemma hasTorAmplitudeIn_of_iso {K L : DMod} {a b : ℤ} (e : K ≅ L) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeIn L a b := by
  constructor
  · intro h M i hi
    -- Transport the vanishing statement along the tensor image of the isomorphism.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor Mod i).mapIso
          ((derivedTensorProduct ((single₀).obj M)).mapIso e.symm))
  · intro h M i hi
    -- The inverse implication uses the inverse tensor comparison.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor Mod i).mapIso
          ((derivedTensorProduct ((single₀).obj M)).mapIso e))

/-- Helper for Lemma 15.67.8: enlarging the interval preserves tor-amplitude. -/
lemma hasTorAmplitudeIn_mono {K : DMod} {a b a' b' : ℤ}
    (hK : HasTorAmplitudeIn K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeIn K a' b' := by
  intro M i hi
  -- Any degree outside the larger interval is already outside the smaller interval.
  exact hK M i <| by
    intro hi'
    exact hi ⟨le_trans ha hi'.1, le_trans hi'.2 hb⟩

/-- Helper for Lemma 15.67.8: finite tor dimension is invariant under isomorphism. -/
lemma hasFiniteTorDimension_of_iso {K L : DMod} (e : K ≅ L) :
    HasFiniteTorDimension K ↔ HasFiniteTorDimension L := by
  constructor
  · rintro ⟨a, b, hK⟩
    exact ⟨a, b, (hasTorAmplitudeIn_of_iso e).1 hK⟩
  · rintro ⟨a, b, hL⟩
    exact ⟨a, b, (hasTorAmplitudeIn_of_iso e).2 hL⟩

/-- Helper for Lemma 15.67.8: the canonical `shiftIso` identifies the degree-`c` single object,
after shifting by `c`, with the degree-zero single object. -/
noncomputable def singleFunctor_shifted_single0_iso_canonical (M : Mod) (c : ℤ) :
    (((DerivedCategory.singleFunctor Mod c).obj M)⟦c⟧) ≅ (single₀).obj M :=
  ((DerivedCategory.singleFunctors Mod).shiftIso c 0 c (by simp)).app M

/-- Helper for Lemma 15.67.8: the degree-`c` single object has tor-amplitude in `[a, b]` exactly
when the degree-zero single object has tor-amplitude in `[a - c, b - c]`. -/
lemma singleFunctor_hasTorAmplitudeIn_iff_single0
    (M : Mod) (c a b : ℤ) :
    HasTorAmplitudeIn ((DerivedCategory.singleFunctor Mod c).obj M) a b ↔
      HasTorAmplitudeIn ((single₀).obj M) (a - c) (b - c) := by
  let e :
      (((DerivedCategory.singleFunctor Mod c).obj M)⟦c⟧) ≅ (single₀).obj M :=
    singleFunctor_shifted_single0_iso_canonical (R := R) M c
  constructor
  · intro h
    -- Shift to degree `0`, then transport across the canonical single-object comparison.
    have hShift :
        HasTorAmplitudeIn (((DerivedCategory.singleFunctor Mod c).obj M)⟦c⟧) (a - c) (b - c) := by
      exact
        (hasTorAmplitudeIn_shift_iff
          (R := R) ((DerivedCategory.singleFunctor Mod c).obj M) c (a - c) (b - c)).2 <| by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    exact (hasTorAmplitudeIn_of_iso (R := R) e).1 hShift
  · intro h
    have hShift :
        HasTorAmplitudeIn (((DerivedCategory.singleFunctor Mod c).obj M)⟦c⟧) (a - c) (b - c) := by
      -- Transport the interval statement back to the shifted degree-`c` single object.
      exact (hasTorAmplitudeIn_of_iso (R := R) e).2 h
    -- Undo the shift to recover the original degree-`c` single object.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hasTorAmplitudeIn_shift_iff
        (R := R) ((DerivedCategory.singleFunctor Mod c).obj M) c (a - c) (b - c)).1 hShift

/-- Helper for Lemma 15.67.8: the canonical single-degree representative matches the negatively
shifted degree-zero single object on the same module term. -/
lemma singleFunctor_hasTorAmplitudeIn_iff_shifted_single0_neg
    (M : Mod) (c a b : ℤ) :
    HasTorAmplitudeIn ((DerivedCategory.singleFunctor Mod c).obj M) a b ↔
      HasTorAmplitudeIn (((single₀).obj M)⟦-c⟧) a b := by
  constructor
  · intro h
    have hBase :
        HasTorAmplitudeIn ((single₀).obj M) (a - c) (b - c) :=
      (singleFunctor_hasTorAmplitudeIn_iff_single0 (R := R) M c a b).1 h
    -- Route correction: the canonical API bridges `singleFunctor c` to the shift by `-c`, not to
    -- the shift by `c` that appears in the current theorem statement.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hasTorAmplitudeIn_shift_iff (R := R) ((single₀).obj M) (-c) a b).2 hBase
  · intro h
    have hBase :
        HasTorAmplitudeIn ((single₀).obj M) (a - c) (b - c) := by
      -- First shift the degree-zero single object back to the unshifted interval.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hasTorAmplitudeIn_shift_iff (R := R) ((single₀).obj M) (-c) a b).1 h
    exact (singleFunctor_hasTorAmplitudeIn_iff_single0 (R := R) M c a b).2 hBase

/-- Helper for Lemma 15.67.8: a representative concentrated in degree `c` has the same
tor-amplitude as the negatively shifted degree-zero single object on its surviving term. -/
lemma representative_hasTorAmplitudeIn_iff_shifted_single0_neg_of_strict_bounds
    (L : CochainComplex Mod ℤ) (c a b : ℤ) [L.IsStrictlyGE c] [L.IsStrictlyLE c] :
    HasTorAmplitudeIn (Q.obj L) a b ↔
      HasTorAmplitudeIn (((single₀).obj (L.X c))⟦-c⟧) a b := by
  let eSingle :
      Q.obj L ≅ (DerivedCategory.singleFunctor Mod c).obj (L.X c) :=
    representative_single_iso_of_strict_bounds (A := Mod) L c
  -- Compare the representative to the canonical degree-`c` single object, then rewrite that
  -- single object in the shift convention that `singleFunctors.shiftIso` actually supplies.
  exact
    (hasTorAmplitudeIn_of_iso (R := R) eSingle).trans
      (singleFunctor_hasTorAmplitudeIn_iff_shifted_single0_neg (R := R) (L.X c) c a b)

/-- Helper for Lemma 15.67.8: the zero object has tor-amplitude in every interval. -/
lemma hasTorAmplitudeIn_of_isZero {K : DMod} (hK : IsZero K) (a b : ℤ) :
    HasTorAmplitudeIn K a b := by
  intro M i hi
  letI : (derivedTensorProduct ((single₀).obj M)).CommShift ℤ :=
    derivedTensorProduct_commShift ((single₀).obj M)
  letI : (derivedTensorProduct ((single₀).obj M)).IsTriangulated :=
    derivedTensorProduct_isTriangulated ((single₀).obj M)
  letI : (derivedTensorProduct ((single₀).obj M)).Additive := inferInstance
  letI : (derivedTensorProduct ((single₀).obj M)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  -- Tensor and homology preserve zero objects, so every test homology group vanishes.
  exact
    (DerivedCategory.homologyFunctor Mod i).map_isZero <|
      (derivedTensorProduct ((single₀).obj M)).map_isZero hK

/-- Helper for Lemma 15.67.8: after shifting back the shorter brutal stage, the termwise
tor-amplitude hypothesis on `L` restricts to the tail interval `[a + 1, b]`. -/
lemma shifted_brutal_stage_shift_back_termwise_hasTorAmplitudeIn
    {L : CochainComplex Mod ℤ} {a b c d : ℤ} {n : ℕ}
    (hn : Int.toNat (d - c) = n + 1)
    (hterm :
      ∀ i : Set.Icc c d,
        HasTorAmplitudeIn (((single₀).obj (L.X i.1))⟦i.1⟧) a b) :
    ∀ i : Set.Icc (c + 1) d,
      HasTorAmplitudeIn
        (((single₀).obj (((shifted_brutal_left_stage (A := Mod) (L⟦d⟧) n)⟦-d⟧).X i.1))⟦i.1⟧)
          a b := by
  have hcd : c ≤ d := by
    by_contra hcd
    have hnonpos : d - c ≤ 0 := by
      omega
    rw [Int.toNat_of_nonpos hnonpos] at hn
    omega
  have hwidth : d - c = ((n + 1 : ℕ) : ℤ) := by
    rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hcd)]
    exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
  have hc1 : c + 1 = d - (n : ℤ) := by
    omega
  intro i
  have hi_stage : -((n : ℕ) : ℤ) ≤ i.1 - d := by
    simpa [hc1] using i.2.1
  have hi_nonneg : 0 ≤ i.1 - d + (n : ℤ) := by
    omega
  have hShiftObj : i.1 + -d = i.1 - d := by
    omega
  have hShiftTerm : i.1 = i.1 - d + d := by
    omega
  let eShift :
      (((shifted_brutal_left_stage (A := Mod) (L⟦d⟧) n)⟦-d⟧).X i.1) ≅
        (shifted_brutal_left_stage (A := Mod) (L⟦d⟧) n).X (i.1 - d) :=
    (shifted_brutal_left_stage (A := Mod) (L⟦d⟧) n).shiftFunctorObjXIso (-d) i.1 (i.1 - d)
      hShiftObj
  let eStage :
      (shifted_brutal_left_stage (A := Mod) (L⟦d⟧) n).X (i.1 - d) ≅
        (L⟦d⟧).X (i.1 - d) :=
    (L⟦d⟧).stupidTruncXIso (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) (by
      refine Eq.symm ?_
      dsimp [ComplexShape.embeddingUpIntGE]
      rw [Int.toNat_of_nonneg hi_nonneg]
      omega)
  let eTerm :
      (L⟦d⟧).X (i.1 - d) ≅ L.X i.1 :=
    L.shiftFunctorObjXIso d (i.1 - d) i.1 hShiftTerm
  let eModule :
      (((shifted_brutal_left_stage (A := Mod) (L⟦d⟧) n)⟦-d⟧).X i.1) ≅ L.X i.1 :=
    eShift ≪≫ eStage ≪≫ eTerm
  let eSingle :
      (((single₀).obj (((shifted_brutal_left_stage (A := Mod) (L⟦d⟧) n)⟦-d⟧).X i.1))⟦i.1⟧) ≅
        (((single₀).obj (L.X i.1))⟦i.1⟧) :=
    (shiftFunctor DMod i.1).mapIso ((single₀).mapIso eModule)
  have hci : c ≤ i.1 := by
    omega
  have hOrig : HasTorAmplitudeIn (((single₀).obj (L.X i.1))⟦i.1⟧) a b :=
    hterm ⟨i.1, ⟨hci, i.2.2⟩⟩
  -- The shifted-back brutal stage has the same degree-`i` term as `L`, so tor-amplitude
  -- transports along the induced shifted single-object isomorphism.
  exact (hasTorAmplitudeIn_of_iso eSingle).2 hOrig

/-- Helper for Lemma 15.67.8: a strictly bounded representative with the stated termwise
tor-amplitude bounds has total tor-amplitude in the same interval. -/
theorem hasTorAmplitudeIn_of_strict_bounds_of_termwise_hasTorAmplitudeIn
    (a b : ℤ) :
    ∀ n : ℕ, ∀ {c d : ℤ} (L : CochainComplex Mod ℤ),
      Int.toNat (d - c) = n →
      L.IsStrictlyGE c →
      L.IsStrictlyLE d →
      (∀ i : Set.Icc c d, HasTorAmplitudeIn (((single₀).obj (L.X i.1))⟦i.1⟧) a b) →
      HasTorAmplitudeIn (Q.obj L) a b := by
  intro n
  induction n with
  | zero =>
      intro c d L hn hGE hLE hterm
      by_cases hcd : c ≤ d
      · have hdc : d ≤ c := by
          have hsub : d - c = 0 := by
            calc
              d - c = (Int.toNat (d - c) : ℤ) := by
                symm
                exact Int.toNat_of_nonneg (sub_nonneg.mpr hcd)
              _ = 0 := by
                simpa using congrArg (fun m : ℕ ↦ (m : ℤ)) hn
          omega
        have hdc_eq : d = c := by
          omega
        subst d
        have hcc : c ∈ Set.Icc c c := by
          simp
        have hsingleNeg : HasTorAmplitudeIn (((single₀).obj (L.X c))⟦-c⟧) a b := by
          have hsinglePos : HasTorAmplitudeIn (((single₀).obj (L.X c))⟦c⟧) a b :=
            hterm ⟨c, hcc⟩
          -- TODO: the theorem hypothesis supplies the shift by `c`, but the canonical
          -- `singleFunctors.shiftIso` bridge for a representative concentrated in degree `c`
          -- lands in the shift by `-c`. A source-faithful repair needs the exact sign
          -- reconciliation between these two conventions before the width-`0` branch can close.
          sorry
        -- In width `0`, the representative is a single degree, so the remaining issue is exactly
        -- the sign convention relating the theorem hypothesis to the canonical single-object API.
        exact
          (representative_hasTorAmplitudeIn_iff_shifted_single0_neg_of_strict_bounds
            (R := R) L c a b).2 hsingleNeg
      · have hlt : d < c := by
          omega
        letI : L.IsStrictlyLE d := hLE
        letI : L.IsStrictlyGE c := hGE
        letI : (Q.obj L).IsLE d := by
          rw [DerivedCategory.isLE_Q_obj_iff]
          infer_instance
        letI : (Q.obj L).IsGE c := by
          rw [DerivedCategory.isGE_Q_obj_iff]
          infer_instance
        -- If the support interval is empty, the derived object is zero and hence has every
        -- tor-amplitude.
        exact hasTorAmplitudeIn_of_isZero (R := R) (t.isZero (Q.obj L) d c hlt) a b
  | succ n ih =>
      intro c d L hn hGE hLE hterm
      have hcd : c ≤ d := by
        by_contra hcd
        have hnonpos : d - c ≤ 0 := by
          omega
        have hzero : Int.toNat (d - c) = 0 := by
          rw [Int.toNat_of_nonpos hnonpos]
        omega
      have hwidth : d - c = ((n + 1 : ℕ) : ℤ) := by
        rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hcd)]
        exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
      have hc1 : c + 1 = d - (n : ℤ) := by
        omega
      have hn' : Int.toNat (d - (c + 1)) = n := by
        rw [show d - (c + 1) = (n : ℤ) by omega]
        simp
      let K : CochainComplex Mod ℤ := L⟦d⟧
      let L1 : CochainComplex Mod ℤ := (shifted_brutal_left_stage (A := Mod) K n)⟦-d⟧
      have hKGE : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := by
        simpa [K] using
          shifted_representative_isStrictlyGE_left_endpoint (A := Mod) (L := L) (a := c)
            (b := d) (n := n) hn hGE
      have hKLE : K.IsStrictlyLE 0 := by
        simpa [K] using
          shifted_representative_isStrictlyLE_zero (A := Mod) (L := L) (b := d) hLE
      have hL1GE : L1.IsStrictlyGE (c + 1) := by
        letI : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := hKGE
        letI : (shifted_brutal_left_stage (A := Mod) K n).IsStrictlyGE (-((n : ℕ) : ℤ)) :=
          inferInstance
        have hShiftGE : -d + (c + 1) = -((n : ℕ) : ℤ) := by
          omega
        simpa [L1, hc1] using
          CochainComplex.isStrictlyGE_shift
            (K := shifted_brutal_left_stage (A := Mod) K n)
            (-((n : ℕ) : ℤ)) (-d) (c + 1) hShiftGE
      have hL1LE : L1.IsStrictlyLE d := by
        letI : K.IsStrictlyLE 0 := hKLE
        letI : (shifted_brutal_left_stage (A := Mod) K n).IsStrictlyLE 0 := inferInstance
        have hShiftLE : -d + d = 0 := by
          omega
        simpa [L1] using
          CochainComplex.isStrictlyLE_shift
            (K := shifted_brutal_left_stage (A := Mod) K n)
            0 (-d) d hShiftLE
      have hL1Terms :
          ∀ i : Set.Icc (c + 1) d,
            HasTorAmplitudeIn (((single₀).obj (L1.X i.1))⟦i.1⟧) a b := by
        -- The shifted-back smaller brutal stage inherits the tail termwise hypothesis.
        simpa [L1] using
          shifted_brutal_stage_shift_back_termwise_hasTorAmplitudeIn
            (R := R) (L := L) (a := a) (b := b) (c := c) (d := d) (n := n) hn hterm
      have hIH : HasTorAmplitudeIn (Q.obj L1) a b := by
        -- Apply the induction hypothesis to the shorter interval `[c + 1, d]`.
        exact ih (c := c + 1) (d := d) L1 hn' hL1GE hL1LE hL1Terms
      let S :=
        (shifted_brutal_left_stage_short_complex_sign_corrected (A := Mod) K n).map
          (shiftFunctor (CochainComplex Mod ℤ) (-d))
      have hS : S.ShortExact := by
        -- The brutal-stage short exact sequence remains short exact after shifting back.
        exact
          (shifted_brutal_left_stage_short_exact_sign_corrected (A := Mod) K n).map_of_exact
            (shiftFunctor (CochainComplex Mod ℤ) (-d))
      let T : Triangle DMod :=
        Triangle.mk (Q.map S.f) (Q.map S.g) (DerivedCategory.triangleOfSESδ hS)
      have hT : T ∈ distTriang DMod := by
        simpa [T] using DerivedCategory.triangleOfSES_distinguished hS
      have h₁ : HasTorAmplitudeIn T.obj₁ a b := by
        simpa [T, S, L1] using hIH
      have hcc : c ∈ Set.Icc c d := by
        exact ⟨le_rfl, hcd⟩
      have hsingleNeg : HasTorAmplitudeIn (((single₀).obj (L.X c))⟦-c⟧) a b := by
        have hsinglePos : HasTorAmplitudeIn (((single₀).obj (L.X c))⟦c⟧) a b :=
          hterm ⟨c, hcc⟩
        -- TODO: the successor step needs the same sign reconciliation as the width-`0` case:
        -- `shifted_brutal_single_shift_back_iso` produces the canonical degree-`c` single object,
        -- and the proven bridge above rewrites that object to `((single₀).obj (L.X c))⟦-c⟧`.
        -- The current hypothesis still arrives as the shift by `c`.
        sorry
      have h₃ : HasTorAmplitudeIn T.obj₃ a b := by
        let eQuot :
            Q.obj S.X₃ ≅ (DerivedCategory.singleFunctor Mod c).obj (L.X c) := by
          dsimp [S, K, shifted_brutal_left_stage_short_complex_sign_corrected]
          exact
            shifted_brutal_single_shift_back_iso (A := Mod) (L := L) (a := c) (b := d) (n := n) hn
        have hQuot :
            HasTorAmplitudeIn ((DerivedCategory.singleFunctor Mod c).obj (L.X c)) a b := by
          exact
            (singleFunctor_hasTorAmplitudeIn_iff_shifted_single0_neg (R := R) (L.X c) c a b).2
              hsingleNeg
        -- The quotient term is the leftmost single degree from the original complex; only the
        -- sign convention relating the theorem hypothesis to that canonical single object remains.
        exact (hasTorAmplitudeIn_of_iso (R := R) eQuot).2 hQuot
      have h₂ : HasTorAmplitudeIn T.obj₂ a b := by
        -- Lemma 15.67.5 propagates the common interval through the distinguished triangle.
        exact hasTorAmplitudeIn_obj₂_of_distinguishedTriangle (R := R) T hT h₁ h₃
      let eMid :
          Q.obj S.X₂ ≅ Q.obj L := by
        let eStage : S.X₂ ≅ L := by
          dsimp [S, L1, K, shifted_brutal_left_stage_short_complex_sign_corrected]
          exact
            ((shiftFunctor (CochainComplex Mod ℤ) (-d)).mapIso
              (shifted_brutal_full_stage_iso_of_isStrictlyGE (A := Mod) K n)).trans
              (shiftShiftNeg L d)
        exact Q.mapIso eStage
      -- Replace the middle brutal stage by the original representative.
      exact (hasTorAmplitudeIn_of_iso eMid).1 h₂

/-- Helper for Lemma 15.67.8: finitely many shifted single terms on a finite integer interval
admit one common tor-amplitude interval. -/
theorem exists_common_torAmplitude_interval_of_termwise_hasFiniteTorDimension_on_Icc :
    ∀ n : ℕ, ∀ {c d : ℤ} (L : CochainComplex Mod ℤ),
      Int.toNat (d - c) = n →
      (∀ i : Set.Icc c d,
        HasFiniteTorDimension (((single₀).obj (L.X i.1))⟦i.1⟧)) →
      ∃ a b : ℤ,
        ∀ i : Set.Icc c d,
          HasTorAmplitudeIn (((single₀).obj (L.X i.1))⟦i.1⟧) a b := by
  intro n
  induction n with
  | zero =>
      intro c d L hn hterm
      by_cases hcd : c ≤ d
      · have hdc : d ≤ c := by
          have hsub : d - c = 0 := by
            calc
              d - c = (Int.toNat (d - c) : ℤ) := by
                symm
                exact Int.toNat_of_nonneg (sub_nonneg.mpr hcd)
              _ = 0 := by
                simpa using congrArg (fun m : ℕ ↦ (m : ℤ)) hn
          omega
        have hdc_eq : d = c := by
          omega
        subst d
        have hcc : c ∈ Set.Icc c c := by
          simp
        rcases hterm ⟨c, hcc⟩ with ⟨a, b, hab⟩
        refine ⟨a, b, ?_⟩
        intro i
        have hic : i.1 = c := by
          exact le_antisymm i.2.2 i.2.1
        -- On a singleton interval, reuse the unique chosen tor-amplitude witness.
        simpa [hic] using hab
      · have hlt : d < c := by
          omega
        refine ⟨0, 0, ?_⟩
        intro i
        -- If the interval is empty, there is nothing to check.
        exfalso
        exact (not_le_of_gt hlt) (le_trans i.2.1 i.2.2)
  | succ n ih =>
      intro c d L hn hterm
      have hcd : c ≤ d := by
        by_contra hcd
        have hnonpos : d - c ≤ 0 := by
          omega
        have hzero : Int.toNat (d - c) = 0 := by
          rw [Int.toNat_of_nonpos hnonpos]
        omega
      have hc1 : c + 1 = d - (n : ℤ) := by
        have hwidth : d - c = ((n + 1 : ℕ) : ℤ) := by
          rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hcd)]
          exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
        omega
      have hn' : Int.toNat (d - (c + 1)) = n := by
        rw [show d - (c + 1) = (n : ℤ) by omega]
        simp
      have hcc : c ∈ Set.Icc c d := by
        exact ⟨le_rfl, hcd⟩
      rcases hterm ⟨c, hcc⟩ with ⟨a₀, b₀, h₀⟩
      have hTail :
          ∀ i : Set.Icc (c + 1) d,
            HasFiniteTorDimension (((single₀).obj (L.X i.1))⟦i.1⟧) := by
        intro i
        have hc_step : c ≤ c + 1 := by
          omega
        have hci : c ≤ i.1 := by
          exact le_trans hc_step i.2.1
        exact hterm ⟨i.1, ⟨hci, i.2.2⟩⟩
      rcases ih (c := c + 1) (d := d) L hn' hTail with ⟨a₁, b₁, hTailAmp⟩
      refine ⟨min a₀ a₁, max b₀ b₁, ?_⟩
      intro i
      by_cases hic : i.1 = c
      · -- Enlarge the interval chosen for the head term.
        simpa [hic] using hasTorAmplitudeIn_mono h₀ (min_le_left _ _) (le_max_left _ _)
      · have hiTail : i.1 ∈ Set.Icc (c + 1) d := by
          have hltc : c < i.1 := by
            exact lt_of_le_of_ne i.2.1 (Ne.symm hic)
          have hleft : c + 1 ≤ i.1 := by
            omega
          constructor
          · exact hleft
          · exact i.2.2
        -- Enlarge the interval chosen for the tail block.
        exact hasTorAmplitudeIn_mono (hTailAmp ⟨i.1, hiTail⟩) (min_le_right _ _) (le_max_right _ _)

/-- Helper for Lemma 15.67.8: finitely many shifted single terms with finite tor dimension admit
one common tor-amplitude interval. -/
theorem exists_common_torAmplitude_interval_of_strict_bounds_of_termwise_hasFiniteTorDimension
    (L : CochainComplex Mod ℤ) {c d : ℤ}
    (hGE : L.IsStrictlyGE c) (hLE : L.IsStrictlyLE d)
    (hterm :
      ∀ i : Set.Icc c d,
        HasFiniteTorDimension (((single₀).obj (L.X i.1))⟦i.1⟧)) :
    ∃ a b : ℤ,
      ∀ i : Set.Icc c d,
        HasTorAmplitudeIn (((single₀).obj (L.X i.1))⟦i.1⟧) a b := by
  -- The support bounds are irrelevant here; only the finiteness of the interval `[c, d]` matters.
  exact
    exists_common_torAmplitude_interval_of_termwise_hasFiniteTorDimension_on_Icc
      (R := R) (n := Int.toNat (d - c)) L rfl hterm

/-- Lemma 15.67.8 (1): if a bounded cochain complex of `R`-modules has each term `K^i`
tor-amplitude in `[a - i, b - i]`, equivalently if the shifted single-term object
`K^i[i] = ((single₀).obj (K.obj.X i))⟦i⟧` has tor-amplitude in `[a, b]`, then the associated
object of `D(R)` has tor-amplitude in `[a, b]`. -/
@[stacks 066H]
theorem hasTorAmplitudeIn_of_bounded_of_termwise_hasTorAmplitudeIn
    (a b : ℤ)
    (K : Compᵇ(Mod))
    (hterm :
      ∀ i : ℤ,
        HasTorAmplitudeIn (((single₀).obj (K.obj.X i))⟦i⟧) a b) :
    HasTorAmplitudeIn (Q.obj K.obj) a b := by
  rcases (CochainComplex.bounded_iff Mod K.obj).1 K.property with ⟨hplus, hminus⟩
  rcases (CochainComplex.plus_iff Mod K.obj).1 hplus with ⟨c, hGE⟩
  rcases (CochainComplex.minus_iff Mod K.obj).1 hminus with ⟨d, hLE⟩
  -- Apply the strict-bounds induction to the bounded representative `K.obj`.
  exact
    hasTorAmplitudeIn_of_strict_bounds_of_termwise_hasTorAmplitudeIn
      (a := a) (b := b) (n := Int.toNat (d - c)) K.obj rfl hGE hLE
      (fun i ↦ hterm i.1)

-- Proof sketch: for each nonzero term `K.obj.X i`, choose a finite tor-amplitude interval;
-- boundedness of `K` leaves only finitely many relevant indices, so these intervals admit common
-- endpoints `a ≤ b`. Transport those bounds to the shifted objects `K^i[i]` via
-- `hasTorAmplitudeIn_shift_iff`, apply the first part with the common interval `[a, b]`, and then
-- package the result via `HasTorAmplitudeIn.hasFiniteTorDimension`.
/-- Lemma 15.67.8 (2): a bounded cochain complex of `R`-modules whose terms all have finite tor
dimension has finite tor dimension in `D(R)`. -/
@[stacks 066H]
theorem hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension
    (K : Compᵇ(Mod))
    (hterm : ∀ i : ℤ, ModuleHasFiniteTorDimension (K.obj.X i)) :
    HasFiniteTorDimension (Q.obj K.obj) := by
  rcases (CochainComplex.bounded_iff Mod K.obj).1 K.property with ⟨hplus, hminus⟩
  rcases (CochainComplex.plus_iff Mod K.obj).1 hplus with ⟨c, hGE⟩
  rcases (CochainComplex.minus_iff Mod K.obj).1 hminus with ⟨d, hLE⟩
  have hShifted :
      ∀ i : Set.Icc c d,
        HasFiniteTorDimension (((single₀).obj (K.obj.X i.1))⟦i.1⟧) := by
    intro i
    -- Shift the module-level finite tor dimension witness from degree `0` to degree `i`.
    exact
      (hasFiniteTorDimension_shift_iff (R := R) ((single₀).obj (K.obj.X i.1)) i.1).2
        (hterm i.1)
  rcases
      exists_common_torAmplitude_interval_of_strict_bounds_of_termwise_hasFiniteTorDimension
        (R := R) K.obj hGE hLE hShifted with
    ⟨a, b, hAmp⟩
  have hK : HasTorAmplitudeIn (Q.obj K.obj) a b := by
    -- Apply the main induction with the common interval chosen on the finite support range.
    exact
      hasTorAmplitudeIn_of_strict_bounds_of_termwise_hasTorAmplitudeIn
        (R := R) a b (n := Int.toNat (d - c)) K.obj rfl hGE hLE hAmp
  exact hK.hasFiniteTorDimension

end

end CategoryTheory
