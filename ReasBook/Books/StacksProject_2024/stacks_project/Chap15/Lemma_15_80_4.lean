import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.stacks_project.Chap10.Lemma_10_110_8
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_80_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_77_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: perfect objects in `D(R)` over a regular ring of finite Krull dimension, and
  splitting of the canonical truncation triangle along a cohomology gap;
- sampled owner declarations:
  `IsRegularRing`,
  `ringKrullDim`,
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- best owner abstraction: the ring-side core owner is `[IsRegularRing R]`, and the finite
  Krull-dimension clause should stay as the direct bridge datum `ringKrullDim R = d`; this item is
  the `source-facing`
  perfect-complex specialization of the split-triangle owner
  `exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`
  applied to the canonical truncation triangle; the compatibility data should stay in the
  owner theorem's native pair of equations rather than a repackaged local predicate;
- primitive data: `d`, the owner instance `[IsRegularRing R]`, the bridge datum
  `hdim : ringKrullDim R = d`, the perfectness of `K`, and the cohomology-gap hypothesis;
- derived API: the compatible biproduct decomposition of `K` into the lower and upper truncations.

Source/core/bridge triage:
- `source-facing`: the specific truncation-gap splitting statement below;
- `core/canonical`: `[IsRegularRing R]` for the ring-side hypothesis and the split-triangle
  owner from Lemma `15.77.1`;
- `bridge/view`: the regular-ring/perfect specialization supplying the projective-amplitude input
  needed by that owner.
-/

-- Proof sketch: apply the canonical owner
-- `exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`
-- to the truncation triangle
-- `τ_{\le k - d + 1} K ⟶ K ⟶ τ_{\ge k + 1} K ⟶ τ_{\le k - d + 1} K⟦1⟧`.
-- The upper truncation has projective amplitude starting in degree `k + 1` because `K` is
-- perfect over the regular ring `R`; the equality `ringKrullDim R = d` is a separate bridge
-- datum, and Lemma `15.80.3` gives the required vanishing of maps
-- into the shifted lower truncation from the stated cohomology gap.
/-- Helper for Lemma 15.80.4: the lower truncation projection induces an isomorphism on the
top surviving cohomology group. -/
private theorem isIso_homologyMap_truncGEπ_local
    (K : DMod) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle DMod := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang DMod := by
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  -- The left term contributes no degree-`n` cohomology, so exactness forces the middle map.
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n).map T.mor₂))

/-- Helper for Lemma 15.80.4: the upper truncation inclusion induces an isomorphism on the last
remaining cohomology group. -/
private theorem isIso_homologyMap_truncLTι_local
    (K : DMod) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) := by
  subst h
  let T : Triangle DMod := (t.triangleLTGE (n₀ + 1)).obj K
  have hT : T ∈ distTriang DMod := by
    simpa [T] using t.triangleLTGE_distinguished (n₀ + 1) K
  have h₃ : T.obj₃.IsGE (n₀ + 1) := by
    dsimp [T]
    infer_instance
  -- The right term contributes no degree-`n₀` cohomology, so exactness forces the first map.
  have hmor₂_zero : (H n₀).map T.mor₂ = 0 := by
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) n₀ (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (n₀ - 1) n₀ (by omega) = 0 := by
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) (n₀ - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H n₀).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n₀).2 hmor₂_zero
  letI : Mono ((H n₀).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (n₀ - 1) n₀ (by omega)).2 hδ_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n₀).map T.mor₁))

/-- Helper for Lemma 15.80.4: an object concentrated in a single degree is canonically the
single object on its cohomology in that degree. -/
private noncomputable def singleFunctor_iso_of_isGE_of_isLE_local
    (X : DMod) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor Mod n).obj ((H n).obj X) := by
  classical
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (DerivedCategory.singleFunctor Mod n).obj Y :=
    Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso Mod n).app Y
  -- Replace the chosen concentrated model by the canonical one indexed by `H^n(X)`.
  exact e ≪≫ (DerivedCategory.singleFunctor Mod n).mapIso eH.symm

/-- Helper for Lemma 15.80.4: the one-step lower truncation piece has the same degree-`a`
cohomology as the original object. -/
private noncomputable def truncGE_step_homologyIso_local
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
  -- Compare first with the `τ_{\ge a}` piece and then with the original object.
  exact eι ≪≫ eπ.symm

/-- Helper for Lemma 15.80.4: the one-step lower truncation piece is the single object on
`H^a(K)`. -/
private noncomputable def truncGE_step_termIso_local
    (K : DMod) (a : ℤ) :
    ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅
      (DerivedCategory.singleFunctor Mod a).obj ((H a).obj K) := by
  have hLE : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE a := by
    simpa using
      (inferInstance : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE ((a + 1) - 1))
  -- The truncation piece is supported in the single degree `a`, so the concentrated comparison
  -- applies and then the cohomology term is identified with `H^a(K)`.
  exact
    singleFunctor_iso_of_isGE_of_isLE_local (R := R)
      ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) a ≪≫
      (DerivedCategory.singleFunctor Mod a).mapIso (truncGE_step_homologyIso_local (R := R) K a)

/-- Helper for Lemma 15.80.4: the source-facing one-step lower truncation triangle. -/
private noncomputable def truncGE_step_homologyTriangle_local
    (K : DMod) (a : ℤ) :
    Triangle DMod :=
  Triangle.mk
    ((truncGE_step_termIso_local (R := R) K a).inv ≫
      (t.truncLTι (a + 1)).app ((t.truncGE a).obj K))
    ((t.natTransTruncGEOfLE a (a + 1) (le_add_of_nonneg_right zero_le_one)).app K)
    (((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) ≫
      (t.truncGEδLT (a + 1)).app ((t.truncGE a).obj K) ≫
      ((truncGE_step_termIso_local (R := R) K a).hom)⟦1⟧')

/-- Helper for Lemma 15.80.4: the one-step lower truncation triangle is distinguished. -/
private theorem truncGE_step_homology_triangle_local
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
        letI : IsIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) :=
          t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) K
        change (asIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K))).hom =
          (t.truncGE (a + 1)).map ((t.truncGEπ a).app K)
        simp
      simp [truncGE_step_homologyTriangle_local, he₃, Category.assoc]
  -- This is exactly the owner truncation triangle rewritten so the first term is `H^a(K)[-a]`.
  exact
    isomorphic_distinguished _
      (t.triangleLTGE_distinguished (a + 1) ((t.truncGE a).obj K)) _ e

/-- Helper for Lemma 15.80.4: the single object on a zero module is zero in `D(R)`. -/
private theorem singleFunctor_obj_isZero_of_isZero
    (n : ℤ) {M : ModuleCat R} (hM : IsZero M) :
    IsZero ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) := by
  -- Apply the owner functor to the zero module comparison.
  simpa using Functor.map_isZero (DerivedCategory.singleFunctor (ModuleCat R) n) hM

/-- Helper for Lemma 15.80.4: if the left summand is zero, then the projection
`X ⊞ Y ⟶ Y` is an isomorphism. -/
private theorem biprod_snd_isIso_of_isZero_left
    {X Y : DMod} [HasBinaryBiproduct X Y] (hX : IsZero X) :
    IsIso (biprod.snd : X ⊞ Y ⟶ Y) := by
  letI : IsZero X := hX
  have hfst_zero : (biprod.fst : X ⊞ Y ⟶ X) = 0 := by
    exact hX.eq_of_tgt _ _
  -- Use `biprod.inr` as the inverse and collapse the vanished left summand.
  refine ⟨⟨biprod.inr, ?_, ?_⟩⟩
  · apply biprod.hom_ext
    · simpa [Category.assoc, hfst_zero]
    · simp [Category.assoc]
  · simp

/-- Helper for Lemma 15.80.4: vanishing of `H^n(K)` makes the adjacent comparison
`τ_{\ge n} K ⟶ τ_{\ge n + 1} K` an isomorphism. -/
private theorem truncGE_step_comparison_isIso_of_homology_isZero
    (K : DMod) (n : ℤ) (hzero : IsZero ((H n).obj K)) :
    IsIso ((t.natTransTruncGEOfLE n (n + 1) (by omega)).app K) := by
  -- The successive-truncation triangle has cone the single object on `H^n(K)`.
  -- When this homology group vanishes, the comparison morphism is forced to be an isomorphism.
  let T := truncGE_step_homologyTriangle_local (R := R) K n
  have hT : T ∈ distTriang DMod := by
    simpa [T] using truncGE_step_homology_triangle_local (R := R) K n
  have h₁ : IsZero T.obj₁ := by
    -- The first vertex is the single object on `H^n(K)`, so it vanishes with `H^n(K)`.
    simpa [T, truncGE_step_homologyTriangle_local] using
      singleFunctor_obj_isZero_of_isZero (R := R) n hzero
  have hzero₃ : T.mor₃ = 0 := by
    -- The connecting morphism lands in a shift of the zero first vertex.
    let hshift : IsZero (T.obj₁⟦(1 : ℤ)⟧) := Functor.map_isZero _ h₁
    exact hshift.eq_of_tgt T.mor₃ 0
  obtain ⟨e, _, he₂⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hzero₃
  have hsplit : IsIso (biprod.snd : T.obj₁ ⊞ T.obj₃ ⟶ T.obj₃) :=
    biprod_snd_isIso_of_isZero_left h₁
  have hmor₂ : IsIso T.mor₂ := by
    -- The split triangle identifies `T.mor₂` with a composition of isomorphisms.
    rw [he₂]
    infer_instance
  simpa [T, truncGE_step_homologyTriangle_local] using hmor₂

/-- Helper for Lemma 15.80.4: the wide upper-truncation comparison factors through the final
successor step. -/
private theorem natTransTruncGEOfLE_succ_factor_app
    (K : DMod) {a b : ℤ} (hab : a ≤ b) :
    ((t.natTransTruncGEOfLE a (b + 1) (by omega)).app K) =
      ((t.natTransTruncGEOfLE a b hab).app K) ≫
        ((t.natTransTruncGEOfLE b (b + 1) (by omega)).app K) := by
  -- The owner transitivity theorem already records the desired factorization.
  exact
    (NatTrans.congr_app (t.natTransTruncGEOfLE_trans a b (b + 1) hab (by omega)) K).symm

/-- Helper for Lemma 15.80.4: a perfect object has bounded-above upper truncations. -/
private theorem perfect_truncGE_isLE_witness
    (K : DMod) (c : ℤ) (hperfect : K.IsPerfect) :
    ∃ b : ℤ, ((t.truncGE c).obj K).IsLE b := by
  rcases hperfect with ⟨L, e, hL⟩
  rcases hL.bounded with ⟨_, b, _, hLb⟩
  -- A bounded finite-projective representative gives a cohomological upper bound on `K`.
  letI : (DerivedCategory.Q.obj L).IsLE b := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    infer_instance
  letI : K.IsLE b := t.isLE_of_iso e.symm b
  exact ⟨b, inferInstance⟩

/-- Helper for Lemma 15.80.4: a whole cohomology gap upgrades `τ_{\ge a} K ⟶ τ_{\ge b} K`
to an isomorphism. -/
private theorem truncGE_comparison_isIso_of_homology_vanishing_interval
    (K : DMod) {a b : ℤ} (hab : a ≤ b)
    (hvanish : ∀ i : ℤ, a ≤ i → i < b → IsZero ((H i).obj K)) :
    IsIso ((t.natTransTruncGEOfLE a b hab).app K) := by
  -- Move from `τ_{\ge a}` to `τ_{\ge b}` one degree at a time, and use the previous step lemma
  -- at each vanished cohomology group in the interval `[a, b)`.
  induction b, hab using Int.le_induction with
  | base =>
      -- The comparison from `a` to itself is the identity.
      rw [NatTrans.congr_app (t.natTransTruncGEOfLE_refl a) K]
      infer_instance
  | succ b hb ih =>
      have hstep :
          IsIso ((t.natTransTruncGEOfLE b (b + 1)
            (le_add_of_nonneg_right zero_le_one)).app K) := by
        -- The adjacent step is an isomorphism because `H^b(K)` is zero.
        exact truncGE_step_comparison_isIso_of_homology_isZero (R := R) K b
          (hvanish b hb (by omega))
      have hprev :
          IsIso ((t.natTransTruncGEOfLE a b hb).app K) := by
        -- Restrict the vanishing hypothesis from `[a, b + 1)` to `[a, b)`.
        exact ih (fun i hi₁ hi₂ ↦ hvanish i hi₁ (lt_trans hi₂ (by omega)))
      -- Factor the wide comparison through the previous endpoint and compose the two isomorphisms.
      rw [natTransTruncGEOfLE_succ_factor_app (R := R) K hb]
      letI := hprev
      letI := hstep
      let e₁ :
          (t.truncGE a).obj K ≅ (t.truncGE b).obj K :=
        asIso ((t.natTransTruncGEOfLE a b hb).app K)
      let e₂ :
          (t.truncGE b).obj K ≅ (t.truncGE (b + 1)).obj K :=
        asIso ((t.natTransTruncGEOfLE b (b + 1)
          (le_add_of_nonneg_right zero_le_one)).app K)
      -- Repackage the two stepwise comparisons as isomorphisms and compose them.
      simpa [e₁, e₂] using (inferInstance : IsIso ((e₁ ≪≫ e₂).hom))

/-- Helper for Lemma 15.80.4: the connecting morphism in the adjacent truncation triangle
vanishes once the right-hand truncation is identified with `τ_{\ge k + 1} K`. -/
private theorem truncation_gap_connecting_morphism_eq_zero
    (d : ℕ) (hdim : ringKrullDim R = d) (K : DMod) (k : ℤ)
    (hperfect : K.IsPerfect)
    (hvanish : ∀ i : ℤ, k - d + 2 ≤ i → i ≤ k → IsZero ((H i).obj K)) :
    let T := (t.triangleLEGE (k - d + 1) (k - d + 2) (by omega)).obj K
    T.mor₃ = 0 := by
  -- Replace the third vertex `τ_{\ge k - d + 2} K` by `τ_{\ge k + 1} K` using the gap
  -- comparison, then apply Lemma `15.80.3` to the resulting map into
  -- `τ_{\le k - d + 1} K⟦1⟧`.
  -- TODO: the source-faithful transport argument needs the interval comparison
  -- `τ_{≥ k-d+2} K ≅ τ_{≥ k+1} K`, which requires the arithmetic hypothesis `k - d + 2 ≤ k + 1`,
  -- i.e. `1 ≤ d`. The current theorem statement omits that hypothesis, and the `d = 0` case is
  -- mathematically false (for instance for a field and a nonzero single-term perfect complex).
  sorry

/-- Lemma 15.80.4: over a regular ring `R` of Krull dimension `d`, a perfect
object `K` of `D(R)` whose cohomology vanishes in degrees `k - d + 2, \ldots, k` admits a direct
sum decomposition
`K ≅ τ_{\le k - d + 1} K ⊞ τ_{\ge k + 1} K`
compatible with the canonical truncation maps. -/
theorem exists_truncation_gap_biprod_of_isPerfect_of_homology_vanishing
    (d : ℕ) (hdim : ringKrullDim R = d) (K : DMod) (k : ℤ)
    (hperfect : K.IsPerfect)
    (hvanish : ∀ i : ℤ, k - d + 2 ≤ i → i ≤ k → IsZero ((H i).obj K)) :
    ∃ e : K ≅ (t.truncLE (k - d + 1)).obj K ⊞ (t.truncGE (k + 1)).obj K,
      ((t.truncLEι (k - d + 1)).app K) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd = ((t.truncGEπ (k + 1)).app K) := by
  -- Route correction: the source-faithful proof still goes through the adjacent truncation
  -- triangle at `k - d + 1`, then uses the cohomology gap to identify
  -- `τ_{\ge k - d + 2} K ≅ τ_{\ge k + 1} K`, applies Lemma `15.80.3` to kill the connecting
  -- morphism, and finally splits the triangle via
  -- `exists_iso_binaryBiproduct_of_distTriang`.
  -- TODO: once the missing `1 ≤ d` hypothesis is restored, combine the previous lemma with the
  -- canonical split theorem for the adjacent truncation triangle and transport the right summand
  -- along `t.π_natTransTruncGEOfLE_app`.
  sorry

end
