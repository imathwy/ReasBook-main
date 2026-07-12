import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_27_9
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_67_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open DerivedCategory
open DerivedCategory.TStructure
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "Hb" => boundedDerivedHomologyFunctor Mod

/- Domain-style sampling for Lemma 15.67.9:
- primary domain: tor-amplitude and finite tor dimension in the bounded derived category `D^b(R)`,
  read through the canonical bounded-derived cohomology functors;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`,
  `Dᵇ(ModuleCat R)`,
  `boundedDerivedHomologyFunctor`,
  `shiftedCohomology`,
  `hasTorAmplitudeIn_shift_iff`;
- best owner abstraction: the tor-amplitude owner is `HasTorAmplitudeIn K a b`, boundedness is
  carried canonically by `K : DbMod`; the cohomology modules of such a bounded object should
  be read through the chapter owner `Hb i : Dᵇ(ModuleCat R) ⥤ ModuleCat R`, and finite tor
  dimension for those modules should use the module-level owner
  `ModuleHasFiniteTorDimension` instead of re-expanding it through the degree-zero embedding; the
  intrinsic shifted cohomology object attached to `H^i(K)` should be read through the chapter owner
  `shiftedCohomology Mod K.obj i` rather than through a local
  `M[0][i]` spelling; the only bridge-level input needed on the public surface is the companion
  shift theorem `hasTorAmplitudeIn_shift_iff`, which lets the hypotheses be read on the intrinsic
  shifted cohomology objects
  `shiftedCohomology Mod K.obj i`, rather than as raw `singleFunctor` packaging or as a second
  coordinate-level interval API;
- primitive vs. derived:
  primitive data are the bounded derived object `K` and the termwise tor-amplitude hypotheses on
  its intrinsic shifted bounded-derived cohomology objects `shiftedCohomology Mod K.obj i`;
  derived API is the finite-tor-dimension consequence, obtained by packaging interval existence;
- source/core/bridge triage:
  `source-facing`: the two textbook bounded-derived theorems below;
  `core/canonical`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`, `Dᵇ(ModuleCat R)`, `Hb`, and `shiftedCohomology`;
  `bridge/view`: the boundedness owner on `K`, the degree-zero embedding `M ↦ M[0]`, and the
    shift-transport bridge `hasTorAmplitudeIn_shift_iff`.

This file therefore keeps the source-facing bounded-derived statements, while reusing the chapter
owners `boundedDerivedHomologyFunctor`, `shiftedCohomology`,
`ModuleHasFiniteTorDimension`, and the Chapter 13 bounded-object/cohomology bridge instead of
spelling a parallel representative API here.
-/

local notation "DMod" => DerivedCategory Mod
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "single₀" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/-- Helper for Lemma 15.67.9: after tensoring with a degree-zero module, shifting the derived
complex by `n` shifts homology degrees by the same amount. -/
noncomputable def homology_tensor_single_shift_iso_local
    (K : DMod) (M : Mod) (i n : ℤ) :
    (H i).obj ((K⟦n⟧) ⊗[R]^L ((single₀).obj M)) ≅
      (H (i + n)).obj (K ⊗[R]^L ((single₀).obj M)) :=
  homology_tensor_single_shift_iso (R := R) K M i n

/-- Helper for Lemma 15.67.9: shifting translates tor-amplitude by the same integer. -/
theorem hasTorAmplitudeIn_shift_iff_local (K : DMod) (n a b : ℤ) :
    HasTorAmplitudeIn (K⟦n⟧) a b ↔ HasTorAmplitudeIn K (a + n) (b + n) :=
  hasTorAmplitudeIn_shift_iff (R := R) K n a b

/-- Helper for Lemma 15.67.9: in a distinguished triangle, tor-amplitude on the first shifted by
one and on the second object implies the same tor-amplitude on the third object. -/
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle_local
    {a b : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b :=
  hasTorAmplitudeIn_obj₃_of_distinguishedTriangle (R := R) T hT h₁ h₂

/-- Helper for Lemma 15.67.9: in a distinguished triangle, tor-amplitude on the first and third
objects implies the same tor-amplitude on the middle object. -/
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle_local
    {a b : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b :=
  hasTorAmplitudeIn_obj₂_of_distinguishedTriangle (R := R) T hT h₁ h₃

/-- Helper for Lemma 15.67.9: the lower truncation projection induces an isomorphism on degree-`n`
cohomology. -/
lemma isIso_homologyMap_truncGEπ_local
    (K : DMod) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) :=
  isIso_homologyMap_truncGEπ (A := Mod) K n

/-- Helper for Lemma 15.67.9: the upper truncation map induces an isomorphism on the last
remaining cohomology group. -/
lemma isIso_homologyMap_truncLTι_local
    (K : DMod) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) :=
  isIso_homologyMap_truncLTι (A := Mod) K n₀ n₁ h

/-- Helper for Lemma 15.67.9: an object concentrated in degree `n` is canonically the single
object on its degree-`n` cohomology. -/
noncomputable def singleFunctor_iso_of_isGE_of_isLE_local
    (X : DMod) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor Mod n).obj ((H n).obj X) :=
  singleFunctorIso_of_isGE_of_isLE (A := Mod) X n

/-- Helper for Lemma 15.67.9: the successive lower-truncation quotient has the same degree-`a`
cohomology as the original derived object. -/
noncomputable def truncGE_step_homologyIso_local
    (K : DMod) (a : ℤ) :
    (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅ (H a).obj K := by
  let eι :
      (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅
        (H a).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _ ((H a).map ((t.truncLTι (a + 1)).app ((t.truncGE a).obj K)))
      (isIso_homologyMap_truncLTι_local (R := R) ((t.truncGE a).obj K) a (a + 1) (by omega))
  let eπ : (H a).obj K ≅ (H a).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _ ((H a).map ((t.truncGEπ a).app K))
      (isIso_homologyMap_truncGEπ_local (R := R) K a)
  exact eι ≪≫ eπ.symm

/-- Helper for Lemma 15.67.9: the bottom truncation piece is the shifted cohomology object in
degree `a`. -/
noncomputable def truncGE_step_termIso_local
    (K : DMod) (a : ℤ) :
    ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅ shiftedCohomology Mod K a := by
  have hLE : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE a := by
    simpa using
      (inferInstance : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE ((a + 1) - 1))
  exact
    singleFunctor_iso_of_isGE_of_isLE_local (R := R)
      ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) a ≪≫
      (DerivedCategory.singleFunctor Mod a).mapIso (truncGE_step_homologyIso_local (R := R) K a)

/-- Helper for Lemma 15.67.9: the source-facing lower-step triangle. -/
noncomputable def truncGE_step_homologyTriangle_local
    (K : DMod) (a : ℤ) :
    Triangle DMod :=
  Triangle.mk
    ((truncGE_step_termIso_local (R := R) K a).inv ≫
      (t.truncLTι (a + 1)).app ((t.truncGE a).obj K))
    ((t.natTransTruncGEOfLE a (a + 1) (le_add_of_nonneg_right zero_le_one)).app K)
    (((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) ≫
      (t.truncGEδLT (a + 1)).app ((t.truncGE a).obj K) ≫
      ((truncGE_step_termIso_local (R := R) K a).hom)⟦1⟧')

/-- Helper for Lemma 15.67.9: the lower-step triangle is distinguished. -/
theorem truncGE_step_homology_triangle_local
    (K : DMod) (a : ℤ) :
    truncGE_step_homologyTriangle_local (R := R) K a ∈ distTriang DMod := by
  let e₃ :
      (t.truncGE (a + 1)).obj K ≅ (t.truncGE (a + 1)).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _ ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K))
      (t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) K)
  let e :
      truncGE_step_homologyTriangle_local (R := R) K a ≅
        (t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K) := by
    refine Triangle.isoMk _ _ (truncGE_step_termIso_local (R := R) K a).symm
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
        -- Route correction: `asIso` needs the truncation map marked as an isomorphism locally.
        letI : IsIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) :=
          t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) K
        change (asIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K))).hom =
          (t.truncGE (a + 1)).map ((t.truncGEπ a).app K)
        simp
      simp [truncGE_step_homologyTriangle_local, he₃, Category.assoc]
  exact
    isomorphic_distinguished _
      (t.triangleLTGE_distinguished (a + 1) ((t.truncGE a).obj K)) _ e

/-- Helper for Lemma 15.67.9: tor-amplitude is invariant under isomorphism in `D(R)`. -/
lemma hasTorAmplitudeIn_of_iso {K L : DerivedCategory Mod} {a b : ℤ} (e : K ≅ L) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeIn L a b := by
  constructor
  · intro h M i hi
    -- Apply the tor-amplitude hypothesis before transporting along the tensor image of the iso.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor Mod i).mapIso
          ((derivedTensorProduct ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M)).mapIso
            e.symm))
  · intro h M i hi
    -- The converse direction uses the inverse isomorphism.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor Mod i).mapIso
          ((derivedTensorProduct ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M)).mapIso e))

/-- Helper for Lemma 15.67.9: enlarging the interval preserves tor-amplitude. -/
lemma hasTorAmplitudeIn_mono {K : DerivedCategory Mod} {a b a' b' : ℤ}
    (hK : HasTorAmplitudeIn K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeIn K a' b' := by
  intro M i hi
  -- Any degree outside the larger interval is also outside the smaller interval.
  exact hK M i <| by
    intro hi'
    exact hi ⟨le_trans ha hi'.1, le_trans hi'.2 hb⟩

/-- Helper for Lemma 15.67.9: finite tor dimension is invariant under isomorphism. -/
lemma hasFiniteTorDimension_of_iso {K L : DerivedCategory Mod} (e : K ≅ L) :
    HasFiniteTorDimension K ↔ HasFiniteTorDimension L := by
  constructor
  · rintro ⟨a, b, hK⟩
    exact ⟨a, b, (hasTorAmplitudeIn_of_iso (R := R) e).1 hK⟩
  · rintro ⟨a, b, hL⟩
    exact ⟨a, b, (hasTorAmplitudeIn_of_iso (R := R) e).2 hL⟩

/-- Helper for Lemma 15.67.9: shifting a single object in degree `i` back to degree `0`
translates tor-amplitude by `i`. -/
lemma singleFunctor_hasTorAmplitudeIn_iff (M : Mod) (i A B : ℤ) :
    HasTorAmplitudeIn ((DerivedCategory.singleFunctor Mod i).obj M) A B ↔
      HasTorAmplitudeIn ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M) (A - i) (B - i) := by
  let e :
      (((DerivedCategory.singleFunctor Mod i).obj M)⟦i⟧) ≅
        ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj M) :=
    (((DerivedCategory.singleFunctors Mod).shiftIso i 0 i (by simp)).app M)
  constructor
  · intro h
    -- First rewrite the interval by the shift, then identify the shifted single object with `M[0]`.
    have hshift :
        HasTorAmplitudeIn (((DerivedCategory.singleFunctor Mod i).obj M)⟦i⟧) (A - i) (B - i) := by
      exact
        (hasTorAmplitudeIn_shift_iff_local (R := R) ((DerivedCategory.singleFunctor Mod i).obj M) i
          (A - i) (B - i)).2 <| by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              using h
    exact (hasTorAmplitudeIn_of_iso (R := R) e).1 hshift
  · intro h
    -- Reverse the same transport to recover the original single object in degree `i`.
    have hshift :
        HasTorAmplitudeIn (((DerivedCategory.singleFunctor Mod i).obj M)⟦i⟧) (A - i) (B - i) := by
      exact (hasTorAmplitudeIn_of_iso (R := R) e).2 h
    exact
      by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (hasTorAmplitudeIn_shift_iff_local (R := R) ((DerivedCategory.singleFunctor Mod i).obj M)
            i (A - i) (B - i)).1 hshift

/-- Helper for Lemma 15.67.9: in degrees above the cutoff, lower truncation preserves homology. -/
noncomputable def homology_truncGE_iso
    (K : DerivedCategory Mod) (c i : ℤ) (hci : c ≤ i) :
    (DerivedCategory.homologyFunctor Mod i).obj ((t.truncGE c).obj K) ≅
      (DerivedCategory.homologyFunctor Mod i).obj K := by
  let f : K ⟶ (t.truncGE c).obj K := (t.truncGEπ c).app K
  let Y : DMod := (t.truncGE c).obj K
  let eK :
      (H i).obj K ≅ (H i).obj ((t.truncGE i).obj K) :=
    @asIso _ _ _ _ ((H i).map ((t.truncGEπ i).app K))
      (isIso_homologyMap_truncGEπ_local (R := R) K i)
  let eY :
      (H i).obj Y ≅ (H i).obj ((t.truncGE i).obj Y) :=
    @asIso _ _ _ _ ((H i).map ((t.truncGEπ i).app Y))
      (isIso_homologyMap_truncGEπ_local (R := R) Y i)
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

/-- Helper for Lemma 15.67.9: in degrees above the cutoff, lower truncation preserves the
intrinsic shifted cohomology object. -/
noncomputable def shiftedCohomology_truncGE_iso
    (K : DerivedCategory Mod) (c i : ℤ) (hci : c ≤ i) :
    shiftedCohomology Mod ((t.truncGE c).obj K) i ≅ shiftedCohomology Mod K i :=
  (DerivedCategory.singleFunctor Mod i).mapIso (homology_truncGE_iso (R := R) K c i hci)

/-- Helper for Lemma 15.67.9: moving from the tail interval
`[c + 1, c + 1 + n]` to the full support interval `[c, c + (n + 1)]`
is equivalent to remembering that the index is not `c`. -/
lemma mem_Icc_succ_iff (c j : ℤ) (n : ℕ) :
    j ∈ Set.Icc (c + 1) (c + 1 + n) ↔ j ∈ Set.Icc c (c + (n + 1)) ∧ j ≠ c := by
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

/-- Helper for Lemma 15.67.9: bounded support together with a common tor-amplitude bound on each
shifted cohomology object forces the whole derived object to have that tor-amplitude. -/
theorem hasTorAmplitudeIn_of_isGE_isLE_of_shiftedCohomology
    (a b c : ℤ) (n : ℕ) (K : DerivedCategory Mod)
    (hGE : K.IsGE c) (hLE : K.IsLE (c + n))
    (hH : ∀ i : Set.Icc c (c + n), HasTorAmplitudeIn (shiftedCohomology Mod K i.1) a b) :
    HasTorAmplitudeIn K a b := by
  induction n generalizing c K with
  | zero =>
      letI : K.IsGE c := hGE
      letI : K.IsLE c := by simpa using hLE
      let e : K ≅ shiftedCohomology Mod K c := by
        simpa [shiftedCohomology] using
          singleFunctor_iso_of_isGE_of_isLE_local (R := R) K c
      have hC : HasTorAmplitudeIn (shiftedCohomology Mod K c) a b := by
        exact hH ⟨c, by simp⟩
      -- In the one-degree case, `K` is exactly its unique shifted cohomology object.
      exact (hasTorAmplitudeIn_of_iso (R := R) e).2 hC
  | succ n ih =>
      letI : K.IsGE c := hGE
      letI : K.IsLE (c + n + 1) := by
        convert hLE using 1
        omega
      let T := truncGE_step_homologyTriangle_local (R := R) K c
      have hT : T ∈ distTriang (DerivedCategory Mod) := by
        simpa [T] using truncGE_step_homology_triangle_local (R := R) K c
      have h₁ : HasTorAmplitudeIn T.obj₁ a b := by
        -- The first vertex is the lowest shifted cohomology object.
        simpa [T, truncGE_step_homologyTriangle_local, shiftedCohomology]
          using hH ⟨c, by
            constructor
            · omega
            · omega⟩
      have hGEtail : ((t.truncGE (c + 1)).obj K).IsGE (c + 1) := by
        infer_instance
      have hLEtail : ((t.truncGE (c + 1)).obj K).IsLE (c + 1 + n) := by
        convert (inferInstance : ((t.truncGE (c + 1)).obj K).IsLE (c + n + 1)) using 1
        omega
      have hHtail :
          ∀ i : Set.Icc (c + 1) (c + 1 + n),
            HasTorAmplitudeIn
              (shiftedCohomology Mod ((t.truncGE (c + 1)).obj K) i.1) a b := by
        intro i
        have hi_step : i.1 ∈ Set.Icc c (c + (n + 1)) := (mem_Icc_succ_iff c i.1 n).1 i.2 |>.1
        have hOrig : HasTorAmplitudeIn (shiftedCohomology Mod K i.1) a b := by
          exact hH ⟨i.1, by simpa [add_assoc, add_left_comm, add_comm] using hi_step⟩
        -- Above `c + 1`, the tail truncation has the same shifted cohomology as `K`.
        exact
          (hasTorAmplitudeIn_of_iso (R := R)
            (shiftedCohomology_truncGE_iso (R := R) K (c + 1) i.1 i.2.1)).2 hOrig
      have h₃ : HasTorAmplitudeIn T.obj₃ a b := by
        -- The induction hypothesis applies to the tail truncation.
        exact ih (c + 1) ((t.truncGE (c + 1)).obj K) hGEtail hLEtail hHtail
      have h₂ : HasTorAmplitudeIn T.obj₂ a b := by
        -- Lemma 15.67.5 propagates the common interval through the step triangle.
        exact hasTorAmplitudeIn_obj₂_of_distinguishedTriangle_local (R := R) T hT h₁ h₃
      have hπ : IsIso ((t.truncGEπ c).app K) :=
        (t.isGE_iff_isIso_truncGEπ_app c K).1 hGE
      -- Finally identify `τ_{≥ c} K` with `K` itself.
      exact (hasTorAmplitudeIn_of_iso (R := R) (asIso ((t.truncGEπ c).app K))).2 h₂

/-- Helper for Lemma 15.67.9: finite tor dimension of a cohomology module yields finite tor
dimension of the corresponding intrinsic shifted cohomology object. -/
lemma shiftedCohomology_hasFiniteTorDimension_of_module
    (K : DerivedCategory Mod) (i : ℤ)
    (h : ModuleHasFiniteTorDimension ((DerivedCategory.homologyFunctor Mod i).obj K)) :
    HasFiniteTorDimension (shiftedCohomology Mod K i) := by
  rcases h with ⟨a, b, hM⟩
  refine ⟨a + i, b + i, ?_⟩
  -- Convert the module interval on `H^i(K)[0]` to the intrinsic shifted cohomology object.
  simpa [shiftedCohomology, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using (singleFunctor_hasTorAmplitudeIn_iff (R := R)
      ((DerivedCategory.homologyFunctor Mod i).obj K) i (a + i) (b + i)).2
        (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hM)

/-- Helper for Lemma 15.67.9: finitely many shifted cohomology objects with finite tor dimension
admit one common tor-amplitude interval. -/
theorem exists_common_torAmplitude_interval_of_isGE_isLE_of_shiftedCohomology_hasFiniteTorDimension
    (c : ℤ) (n : ℕ) (K : DerivedCategory Mod)
    (hGE : K.IsGE c) (hLE : K.IsLE (c + n))
    (hH : ∀ i : Set.Icc c (c + n), HasFiniteTorDimension (shiftedCohomology Mod K i.1)) :
    ∃ a b : ℤ, ∀ i : Set.Icc c (c + n), HasTorAmplitudeIn (shiftedCohomology Mod K i.1) a b := by
  induction n generalizing c K with
  | zero =>
      rcases hH ⟨c, by simp⟩ with ⟨a, b, hC⟩
      refine ⟨a, b, ?_⟩
      intro i
      have hi_le : i.1 ≤ c := by simpa using i.2.2
      have hi : i.1 = c := le_antisymm hi_le i.2.1
      simpa [hi] using hC
  | succ n ih =>
      letI : K.IsGE c := hGE
      letI : K.IsLE (c + n + 1) := by
        convert hLE using 1
        omega
      rcases hH ⟨c, by
          constructor
          · omega
          · omega⟩ with ⟨a₀, b₀, h₀⟩
      have hGEtail : ((t.truncGE (c + 1)).obj K).IsGE (c + 1) := by
        infer_instance
      have hLEtail : ((t.truncGE (c + 1)).obj K).IsLE (c + 1 + n) := by
        convert (inferInstance : ((t.truncGE (c + 1)).obj K).IsLE (c + n + 1)) using 1
        omega
      have hHtail :
          ∀ i : Set.Icc (c + 1) (c + 1 + n),
            HasFiniteTorDimension (shiftedCohomology Mod ((t.truncGE (c + 1)).obj K) i.1) := by
        intro i
        have hi_step : i.1 ∈ Set.Icc c (c + (n + 1)) := (mem_Icc_succ_iff c i.1 n).1 i.2 |>.1
        have hOrig : HasFiniteTorDimension (shiftedCohomology Mod K i.1) := by
          exact hH ⟨i.1, by simpa [add_assoc, add_left_comm, add_comm] using hi_step⟩
        -- Transport finite tor dimension along the truncation comparison iso.
        exact
          (hasFiniteTorDimension_of_iso (R := R)
            (shiftedCohomology_truncGE_iso (R := R) K (c + 1) i.1 i.2.1)).2 hOrig
      rcases ih (c + 1) ((t.truncGE (c + 1)).obj K) hGEtail hLEtail hHtail with
        ⟨a₁, b₁, hTail⟩
      refine ⟨min a₀ a₁, max b₀ b₁, ?_⟩
      intro i
      by_cases hic : i.1 = c
      ·
        -- Enlarge the interval chosen for the bottom cohomology object.
        simpa [hic] using hasTorAmplitudeIn_mono h₀ (min_le_left _ _) (le_max_left _ _)
      · have hiTail : i.1 ∈ Set.Icc (c + 1) (c + 1 + n) := by
          exact (mem_Icc_succ_iff c i.1 n).2 ⟨by simpa [add_assoc, add_left_comm, add_comm] using i.2, hic⟩
        -- Enlarge the common interval produced for the tail truncation.
        have hTailOrig : HasTorAmplitudeIn (shiftedCohomology Mod K i.1) a₁ b₁ := by
          exact
            (hasTorAmplitudeIn_of_iso (R := R)
              (shiftedCohomology_truncGE_iso (R := R) K (c + 1) i.1 hiTail.1)).1
              (hTail ⟨i.1, hiTail⟩)
        exact hasTorAmplitudeIn_mono hTailOrig (min_le_right _ _) (le_max_right _ _)

/-- Lemma 15.67.9: if `K` is a bounded derived object of `R`-modules and each cohomology module
`H^i(K)`, placed in cohomological degree `i`, has tor-amplitude in `[a, b]`, then `K` has
tor-amplitude in `[a, b]`. The canonical owner for that shifted cohomology object is
`shiftedCohomology Mod K.obj i`. -/
theorem hasTorAmplitudeIn_of_bounded_of_homology_hasTorAmplitudeIn
    (a b : ℤ) (K : DbMod)
    (hH : ∀ i : ℤ, HasTorAmplitudeIn (shiftedCohomology Mod K.obj i) a b) :
    HasTorAmplitudeIn K.obj a b := by
  rcases (derivedCategory_t_bounded_iff K.obj).1 K.property with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  let c' : ℤ := min c d
  have hGE : K.obj.IsGE c' := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hc i (lt_of_lt_of_le hi (min_le_left _ _))
  have hLEd : K.obj.IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hd i hi
  have hnonneg : 0 ≤ d - c' := by
    dsimp [c']
    omega
  have hcd : c' + Int.toNat (d - c') = d := by
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have hLE : K.obj.IsLE (c' + Int.toNat (d - c')) := by
    rw [hcd]
    exact hLEd
  have hH' :
      ∀ i : Set.Icc c' (c' + Int.toNat (d - c')),
        HasTorAmplitudeIn (shiftedCohomology Mod K.obj i.1) a b := by
    intro i
    simpa [hcd] using hH i.1
  -- Reduce the bounded object to its finite cohomological support interval.
  exact
    hasTorAmplitudeIn_of_isGE_isLE_of_shiftedCohomology (R := R) a b c'
      (Int.toNat (d - c')) K.obj hGE hLE hH'

-- Proof sketch: boundedness leaves only finitely many possibly nonzero cohomology modules, so the
-- finite tor-dimension intervals for the degree-zero cohomology modules admit common endpoints;
-- transport those intervals to the intrinsic shifted cohomology objects
-- `shiftedCohomology Mod K.obj i` by `hasTorAmplitudeIn_shift_iff`, then apply the first theorem.
/-- If every cohomology module of a bounded derived object has finite tor dimension, then the
bounded derived object itself has finite tor dimension. -/
theorem hasFiniteTorDimension_of_bounded_of_homology_hasFiniteTorDimension
    (K : DbMod)
    (hH : ∀ i : ℤ, ModuleHasFiniteTorDimension ((Hb i).obj K)) :
    HasFiniteTorDimension K.obj := by
  rcases (derivedCategory_t_bounded_iff K.obj).1 K.property with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  let c' : ℤ := min c d
  have hGE : K.obj.IsGE c' := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hc i (lt_of_lt_of_le hi (min_le_left _ _))
  have hLEd : K.obj.IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hd i hi
  have hnonneg : 0 ≤ d - c' := by
    dsimp [c']
    omega
  have hcd : c' + Int.toNat (d - c') = d := by
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have hLE : K.obj.IsLE (c' + Int.toNat (d - c')) := by
    rw [hcd]
    exact hLEd
  have hShifted :
      ∀ i : Set.Icc c' (c' + Int.toNat (d - c')),
        HasFiniteTorDimension (shiftedCohomology Mod K.obj i.1) := by
    intro i
    exact shiftedCohomology_hasFiniteTorDimension_of_module (R := R) K.obj i.1 (hH i.1)
  rcases
      exists_common_torAmplitude_interval_of_isGE_isLE_of_shiftedCohomology_hasFiniteTorDimension
        (R := R) c' (Int.toNat (d - c')) K.obj hGE hLE hShifted with
    ⟨a, b, hAmp⟩
  -- Apply the first part with the common interval obtained on the finite support interval.
  exact ⟨a, b,
    hasTorAmplitudeIn_of_isGE_isLE_of_shiftedCohomology (R := R) a b c'
      (Int.toNat (d - c')) K.obj hGE hLE hAmp⟩

end

end CategoryTheory
