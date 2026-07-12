import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.Chap13.Remark_13_12_4
import StacksProject_2024.Chap13.Lemma_13_35_7
import Mathlib.Tactic.StacksAttribute

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

noncomputable section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/- Domain-style sampling for Lemma 13.12.5:
- primary domain: truncation factorization in the canonical `t`-structure on `D(\mathcal A)`,
  with stepwise vanishing measured by the derived-category homology functors;
- sampled owner declarations:
  `DerivedCategory.IsLE`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isLE_iff`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.Q`,
  `TStructure.liftTruncLE`,
  `TStructure.descTruncGE`,
  `t.truncLEι`,
  `t.truncGEπ`;
- best owner abstraction: the source-facing data remain the actual chain of cochain-complex maps
  from Stacks 08Q2, while the boundedness and truncation conclusions live in the canonical
  `t`-structure owners on `D(\mathcal A)` after applying `DerivedCategory.Q`;
- primitive data: the composable-arrow diagram
  `S : ComposableArrows (CochainComplex 𝒜 ℤ) n` and the vanishing of the degree `-j` or `j`
  homology-functor maps for the induced derived-category arrows `DerivedCategory.Q.map
  ((S.arrow j hj).hom)`;
- derived API: existence of a factorization of `DerivedCategory.Q.map S.hom` through the
  canonical truncation maps
  `τ_{\le -n}(Q(Kₙ^•)) ⟶ Q(Kₙ^•)` and `Q(Kₙ^•) ⟶ τ_{\ge n}(Q(Kₙ^•))`;
- source/core/bridge triage:
  `source-facing`: the two factorization theorems below;
  `core/canonical`: the owners `DerivedCategory.IsLE` / `IsGE`, the homology functors `H i`,
    the localization functor `DerivedCategory.Q`, and the truncation morphisms `t.truncLEι`,
    `t.truncGEπ`;
  `bridge/view`: `DerivedCategory.isLE_iff` / `isGE_iff`, translating the textbook cohomology
    vanishing conditions into those owner predicates.

Accordingly, this file keeps the two source-facing factorization theorems on actual
cochain-complex chains from the source and uses private derived-category helper lemmas only for
the internal truncation-factorization API.
-/

/-- Helper for Lemma 13.12.5: an object of the derived category concentrated in degree `n` is a
single object on its degree-`n` homology. -/
private noncomputable def singleFunctor_iso_of_isGE_of_isLE
    (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor 𝒜 n).obj ((H n).obj X) :=
  singleFunctorIso_of_isGE_of_isLE X n

/-- Helper for Lemma 13.12.5: the degree-`n` homology map induced by the lower truncation
projection `K ⟶ τ_{\ge n} K` is an isomorphism. -/
private theorem homology_map_truncGEπ_isIso
    (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  simpa using isIso_homologyMap_truncGEπ K n

/-- Helper for Lemma 13.12.5: the degree-`n₀` homology map induced by the upper truncation
inclusion `τ_{< n₁} K ⟶ K` is an isomorphism when `n₁ = n₀ + 1`. -/
private theorem homology_map_truncLTι_isIso
    (K : DerivedCategory 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) := by
  simpa using isIso_homologyMap_truncLTι K n₀ n₁ h

/-- Helper for Lemma 13.12.5: the top homology of the successive upper truncation agrees with the
corresponding homology of the original object. -/
private noncomputable def truncLE_step_homology_iso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (H (a + 1)).obj K :=
  _root_.truncLE_step_homologyIso K a

/-- Helper for Lemma 13.12.5: the successive upper-truncation quotient is the single object on the
top homology term. -/
private noncomputable def truncLE_step_term_iso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (singleFunctor 𝒜 (a + 1)).obj ((H (a + 1)).obj K) :=
  _root_.truncLE_step_termIso K a

/-- Helper for Lemma 13.12.5: the successive upper truncations of `K` and the top homology term
form a distinguished triangle. -/
private theorem truncLE_step_homology_triangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    Triangle.mk
        ((t.natTransTruncLTOfLE (a + 1) (a + 2) (by omega)).app K)
        (((Functor.whiskerLeft (t.truncLT (a + 2)) (t.truncGEπ (a + 1))).app K) ≫
          (truncLE_step_term_iso K a).hom)
        ((truncLE_step_term_iso K a).inv ≫ (t.truncGELTδLT (a + 1) (a + 2)).app K)
      ∈ distTriang (DerivedCategory 𝒜) := by
  -- Route correction: reuse the canonical step triangle from Remark 13.12.4 instead of
  -- rebuilding the same distinguished-triangle API locally.
  simpa [truncLE_step_term_iso] using _root_.truncLE_step_homology_triangle K a

/-- Helper for Lemma 13.12.5: a morphism between single-degree objects is zero once its
degree-`a` homology map is zero. -/
private theorem single_map_eq_zero_of_homologyMap_eq_zero
    {A B : 𝒜} {a : ℤ} (q : (singleFunctor 𝒜 a).obj A ⟶ (singleFunctor 𝒜 a).obj B)
    (hq : (H a).map q = 0) :
    q = 0 := by
  let hFF : (singleFunctor 𝒜 a).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (singleFunctor 𝒜 a)
  let u : A ⟶ B := hFF.preimage q
  have huq : (singleFunctor 𝒜 a).map u = q := by
    simpa [u] using hFF.map_preimage q
  -- Proof comment: naturality of `singleFunctorCompHomologyFunctorIso` transports the vanishing
  -- of `H^a(q)` back to the underlying morphism `u : A ⟶ B`.
  have hu : ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ u = 0 := by
    simpa [Functor.comp_map, huq, hq] using
      (NatTrans.naturality (singleFunctorCompHomologyFunctorIso 𝒜 a).hom u).symm
  have hu' :
      ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ u =
        ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ 0 := by
    calc
      ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ u = 0 := hu
      _ = ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ 0 := by
        symm
        rw [Limits.comp_zero]
  have hu_zero : u = 0 := by
    exact (cancel_epi ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom).1 hu'
  rw [← huq, hu_zero]
  simp

/-- Helper for Lemma 13.12.5: a morphism from an object `≤ a` into one concentrated in degree
`a` is zero once its degree-`a` homology map vanishes. -/
private theorem hom_to_concentrated_eq_zero_of_isLE_homologyMap_eq_zero
    {X Z : DerivedCategory 𝒜} {a : ℤ}
    (hX : X.IsLE a) [Z.IsGE a] [Z.IsLE a]
    (g : X ⟶ Z)
    (hg : (H a).map g = 0) :
    g = 0 := by
  let desc : (t.truncGE a).obj X ⟶ Z := t.descTruncGE g a
  have hdesc : (t.truncGEπ a).app X ≫ desc = g := by
    simpa [desc] using t.π_descTruncGE (f := g) a
  have hdesc_homology : (H a).map desc = 0 := by
    haveI : IsIso ((H a).map ((t.truncGEπ a).app X)) := homology_map_truncGEπ_isIso X a
    apply (cancel_epi ((H a).map ((t.truncGEπ a).app X))).1
    simpa [Functor.map_comp, hdesc, hg] using
      congrArg (fun k ↦ (H a).map k) hdesc
  letI : ((t.truncGE a).obj X).IsLE a := by
    letI : X.IsLE a := hX
    infer_instance
  let eX := singleFunctor_iso_of_isGE_of_isLE ((t.truncGE a).obj X) a
  let eZ := singleFunctor_iso_of_isGE_of_isLE Z a
  let q :
      (singleFunctor 𝒜 a).obj ((H a).obj ((t.truncGE a).obj X)) ⟶
        (singleFunctor 𝒜 a).obj ((H a).obj Z) :=
    eX.inv ≫ desc ≫ eZ.hom
  have hq_homology : (H a).map q = 0 := by
    simp [q, Functor.map_comp, hdesc_homology]
  have hq_zero : q = 0 := by
    exact single_map_eq_zero_of_homologyMap_eq_zero q hq_homology
  have hdesc_zero : desc = 0 := by
    have hcomp : eX.inv ≫ desc ≫ eZ.hom = 0 := by
      simpa [q] using hq_zero
    have hcomp' : eX.inv ≫ desc = 0 := by
      apply (cancel_mono eZ.hom).1
      simpa [Category.assoc] using hcomp
    exact (cancel_epi eX.inv).1 (by simpa [Category.assoc] using hcomp')
  rw [← hdesc, hdesc_zero]
  simp

/-- Helper for Lemma 13.12.5: if `X` is bounded above in degree `a`, then a morphism
`X ⟶ A₀[a]` is zero once its degree-`a` homology map is zero. -/
private theorem hom_to_single_eq_zero_of_isLE_homologyMap_eq_zero
    {X : DerivedCategory 𝒜} {A₀ : 𝒜} {a : ℤ}
    (hX : X.IsLE a)
    (g : X ⟶ (singleFunctor 𝒜 a).obj A₀)
    (hg : (H a).map g = 0) :
    g = 0 := by
  exact hom_to_concentrated_eq_zero_of_isLE_homologyMap_eq_zero hX g hg

/-- Helper for Lemma 13.12.5: a morphism `f : X ⟶ Y` from an object `≤ a` factors through
`τ_{< a} Y` once its degree-`a` homology map vanishes. -/
private theorem exists_factor_through_prev_truncLT_of_isLE_and_homologyMap_eq_zero
    {X Y : DerivedCategory 𝒜} {a : ℤ}
    (f : X ⟶ Y)
    (hX : X.IsLE a)
    (hf : (H a).map f = 0) :
    ∃ φ : X ⟶ (t.truncLT a).obj Y,
      φ ≫ (t.truncLTι a).app Y = f := by
  letI : X.IsLE a := hX
  let fLT : X ⟶ (t.truncLT (a + 1)).obj Y := t.liftTruncLT f a (a + 1) rfl
  let T := (t.triangleLTLTGELT a (a + 1) (by omega)).obj Y
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTLTGELT_distinguished a (a + 1) (by omega) Y
  have hfLT : fLT ≫ (t.truncLTι (a + 1)).app Y = f := by
    simpa [fLT] using t.liftTruncLT_ι (f := f) a (a + 1) rfl
  have hfLT_homology : (H a).map fLT = 0 := by
    letI : IsIso ((H a).map ((t.truncLTι (a + 1)).app Y)) :=
      homology_map_truncLTι_isIso (K := Y) (n₀ := a) (n₁ := a + 1) rfl
    exact (cancel_mono ((H a).map ((t.truncLTι (a + 1)).app Y))).1 (by
      simpa [Functor.map_comp, hf] using congrArg (fun k ↦ (H a).map k) hfLT)
  haveI : T.obj₃.IsGE a := by
    dsimp [T]
    infer_instance
  haveI : T.obj₃.IsLE a := by
    dsimp [T]
    infer_instance
  haveI : IsIso ((H a).map T.mor₂) := by
    dsimp [T]
    simpa using homology_map_truncGEπ_isIso (K := (t.truncLT (a + 1)).obj Y) (n := a)
  have hzero : fLT ≫ T.mor₂ = 0 := by
    have hzero_homology : (H a).map (fLT ≫ T.mor₂) = 0 := by
      simpa [Functor.map_comp, hfLT_homology]
    exact hom_to_concentrated_eq_zero_of_isLE_homologyMap_eq_zero hX (fLT ≫ T.mor₂) hzero_homology
  obtain ⟨φ, hφ⟩ := Triangle.coyoneda_exact₂ (T := T) hT fLT hzero
  refine ⟨φ, ?_⟩
  have hφcomp :
      φ ≫ T.mor₁ ≫ (t.truncLTι (a + 1)).app Y = fLT ≫ (t.truncLTι (a + 1)).app Y := by
    rw [hφ]
    exact (Category.assoc φ T.mor₁ ((t.truncLTι (a + 1)).app Y)).symm
  calc
    φ ≫ (t.truncLTι a).app Y = φ ≫ T.mor₁ ≫ (t.truncLTι (a + 1)).app Y := by
      simpa [T, Category.assoc] using
        (congrArg (fun k ↦ φ ≫ k) (t.natTransTruncLTOfLE_ι_app a (a + 1) (by omega) Y)).symm
    _ = fLT ≫ (t.truncLTι (a + 1)).app Y := hφcomp
    _ = f := hfLT

/-- Helper for Lemma 13.12.5: a morphism `f : X ⟶ Y` from an object `≤ a` factors through
`τ_{\le a - 1} Y` once its degree-`a` homology map vanishes. -/
private theorem exists_factor_through_prev_truncLE_of_isLE_and_homologyMap_eq_zero
    {X Y : DerivedCategory 𝒜} {a : ℤ}
    (f : X ⟶ Y)
    (hX : X.IsLE a)
    (hf : (H a).map f = 0) :
    ∃ φ : X ⟶ (t.truncLE (a - 1)).obj Y,
      φ ≫ (t.truncLEι (a - 1)).app Y = f := by
  letI : X.IsLE a := hX
  obtain ⟨φ, hφ⟩ :=
    exists_factor_through_prev_truncLT_of_isLE_and_homologyMap_eq_zero
      (f := f) (X := X) (Y := Y) (a := a) hX hf
  refine ⟨φ ≫ (t.truncLEIsoTruncLT (a - 1) a (by omega)).inv.app Y, ?_⟩
  calc
    (φ ≫ (t.truncLEIsoTruncLT (a - 1) a (by omega)).inv.app Y) ≫ (t.truncLEι (a - 1)).app Y =
        φ ≫ (t.truncLTι a).app Y := by
          rw [Category.assoc, t.truncLEIsoTruncLT_inv_ι_app]
    _ = f := hφ

/-- Helper for Lemma 13.12.5: the upper factorization statement in the derived category is proved
by induction on the length of the composable-arrow diagram. -/
private theorem exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero_aux
    {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.left.IsLE 0)
    (hstep : ∀ j (hj : j < n), (H (-(j : ℤ))).map (S.arrow j hj).hom = 0) :
    ∃ φ : S.left ⟶ (t.truncLE (-(n : ℤ))).obj S.right,
      φ ≫ (t.truncLEι (-(n : ℤ))).app S.right = S.hom := by
  induction n with
  | zero =>
      let e : (t.truncLE 0).obj S.right ≅ S.right :=
        @asIso _ _ _ _ ((t.truncLEι 0).app S.right)
          ((t.isLE_iff_isIso_truncLEι_app 0 S.right).1 h₀)
      refine ⟨e.inv, ?_⟩
      -- In the zero-step case the total composite is the identity, so the inverse truncation map
      -- already gives the required factorization.
      simpa [ComposableArrows.hom, ComposableArrows.left, ComposableArrows.right,
        ComposableArrows.obj', e] using e.inv_hom_id
  | succ n ih =>
      have htail :
          ∀ j (hj : j < n), (H (-(j : ℤ))).map (S.δlast.arrow j hj).hom = 0 := by
        intro j hj
        -- The tail chain keeps the same first `n` step maps as the original chain.
        simpa [ComposableArrows.arrow, ComposableArrows.δlast] using hstep j (by omega)
      obtain ⟨φtail, hφtail⟩ :=
        ih S.δlast h₀ htail
      let f :
          (t.truncLE (-(n : ℤ))).obj S.δlast.right ⟶ S.right :=
        (t.truncLEι (-(n : ℤ))).app S.δlast.right ≫ (S.arrow n (by omega)).hom
      have hf : (H (-(n : ℤ))).map f = 0 := by
        -- The last step map already vanishes on degree `-n` homology, and `f` is obtained by
        -- precomposing that step with the truncation inclusion.
        dsimp [f]
        rw [Functor.map_comp]
        calc
          (H (-(n : ℤ))).map ((t.truncLEι (-(n : ℤ))).app S.δlast.right) ≫
              (H (-(n : ℤ))).map (S.arrow n (by omega)).hom =
              (H (-(n : ℤ))).map ((t.truncLEι (-(n : ℤ))).app S.δlast.right) ≫ 0 := by
                exact congrArg
                  (fun k ↦ (H (-(n : ℤ))).map ((t.truncLEι (-(n : ℤ))).app S.δlast.right) ≫ k)
                  (hstep n (by omega))
          _ = 0 := by
                simpa using
                  (show
                    (H (-(n : ℤ))).map ((t.truncLEι (-(n : ℤ))).app S.δlast.right) ≫ (0 : _)
                      = 0 from CategoryTheory.Limits.comp_zero)
      obtain ⟨φstep, hφstep⟩ :=
        exists_factor_through_prev_truncLE_of_isLE_and_homologyMap_eq_zero
          (f := f) (X := (t.truncLE (-(n : ℤ))).obj S.δlast.right) (Y := S.right)
          (a := -(n : ℤ)) inferInstance hf
      rw [show -((n + 1 : ℕ) : ℤ) = (-(n : ℤ)) - 1 by omega]
      let φ : S.left ⟶ (t.truncLE (-(n : ℤ) - 1)).obj S.right := φtail ≫ φstep
      refine ⟨φ, ?_⟩
      -- First factor through the penultimate truncation stage, then apply the one-step case to
      -- the last arrow. The chain decomposition `S.hom = S.δlast.hom ≫ S.arrow n` supplies the
      -- final comparison.
      dsimp [φ]
      have hmain₁ :
          (φtail ≫ φstep) ≫ (t.truncLEι (-(n : ℤ) - 1)).app S.right = φtail ≫ f := by
        rw [Category.assoc]
        simpa [Category.assoc] using congrArg (fun k ↦ φtail ≫ k) hφstep
      have hmain₂ :
          φtail ≫ f = (φtail ≫ (t.truncLEι (-(n : ℤ))).app S.δlast.right) ≫
            (S.arrow n (by omega)).hom := by
        dsimp [f]
        exact
          (Category.assoc φtail ((t.truncLEι (-(n : ℤ))).app S.δlast.right)
            ((S.arrow n (by omega)).hom)).symm
      have hmain₃ :
          (φtail ≫ (t.truncLEι (-(n : ℤ))).app S.δlast.right) ≫ (S.arrow n (by omega)).hom =
            S.δlast.hom ≫ (S.arrow n (by omega)).hom := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ (S.arrow n (by omega)).hom) hφtail
      have hmain₄ : S.δlast.hom ≫ (S.arrow n (by omega)).hom = S.hom := by
        simpa [ComposableArrows.arrow, ComposableArrows.δlast, ComposableArrows.hom,
          Category.assoc] using
          (S.map'_comp 0 n (n + 1)).symm
      exact hmain₁.trans (hmain₂.trans (hmain₃.trans hmain₄))

-- Proof sketch for Lemma 13.12.5 (1): argue by induction on the length of the composable-arrow
-- diagram. The case
-- `n = 1` comes from the distinguished truncation triangle of Remark 13.12.4 and the vanishing
-- of the induced map on degree-`0` homology; the induction step factors first through
-- `τ_{\le -(n-1)}` of the penultimate complex and then applies the case `n = 1` to the induced
-- map between successive truncations after passing the chain to `D(\mathcal A)` via
-- `DerivedCategory.Q`.
/-- Lemma 13.12.5 (1): if `K₀^• ⟶ ⋯ ⟶ Kₙ^•` is a chain of cochain-complex maps whose source
`K₀^•` is `≤ 0` in `D(\mathcal A)` (equivalently, has no positive cohomology) and whose map
`H^{-j}(K_j^•) ⟶ H^{-j}(K_{j+1}^•)` vanishes at each step, then the induced composite in
`D(\mathcal A)` factors through the canonical truncation map
`τ_{\le -n}(Q(Kₙ^•)) ⟶ Q(Kₙ^•)`. -/
@[stacks 08Q2]
theorem exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (CochainComplex 𝒜 ℤ) n)
    (h₀ : (DerivedCategory.Q.obj S.left).IsLE 0)
    (hstep : ∀ j (hj : j < n),
      (H (-(j : ℤ))).map (DerivedCategory.Q.map ((S.arrow j hj).hom)) = 0) :
    ∃ φ :
      DerivedCategory.Q.obj S.left ⟶ (t.truncLE (-(n : ℤ))).obj (DerivedCategory.Q.obj S.right),
      φ ≫ (t.truncLEι (-(n : ℤ))).app (DerivedCategory.Q.obj S.right) =
        DerivedCategory.Q.map S.hom := by
  let SQ : ComposableArrows (DerivedCategory 𝒜) n := S ⋙ DerivedCategory.Q
  have hstepQ :
      ∀ j (hj : j < n), (H (-(j : ℤ))).map (SQ.arrow j hj).hom = 0 := by
    intro j hj
    simpa [SQ, ComposableArrows.arrow, Functor.comp_map] using hstep j hj
  obtain ⟨φ, hφ⟩ :=
    exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero_aux (S := SQ) (by simpa [SQ] using h₀) hstepQ
  refine ⟨φ, ?_⟩
  simpa [SQ, Functor.comp_obj, Functor.comp_map, ComposableArrows.hom] using hφ

/-- Helper for Lemma 13.12.5: a morphism from a single-degree object into an object of `D^{\ge a}`
is zero once its degree-`a` homology map is zero. -/
private theorem single_to_hom_eq_zero_of_isGE_homologyMap_eq_zero
    {Y : DerivedCategory 𝒜} {A₀ : 𝒜} {a : ℤ}
    (hY : Y.IsGE a)
    (g : (singleFunctor 𝒜 a).obj A₀ ⟶ Y)
    (hg : (H a).map g = 0) :
    g = 0 := by
  letI : Y.IsGE a := hY
  let lift : (singleFunctor 𝒜 a).obj A₀ ⟶ (t.truncLT (a + 1)).obj Y :=
    t.liftTruncLT g a (a + 1) rfl
  have hlift : lift ≫ (t.truncLTι (a + 1)).app Y = g := by
    simpa [lift] using t.liftTruncLT_ι (f := g) a (a + 1) rfl
  haveI : IsIso ((H a).map ((t.truncLTι (a + 1)).app Y)) :=
    homology_map_truncLTι_isIso Y a (a + 1) rfl
  -- Proof comment: transport the homology vanishing to the lift into `τ_{< a + 1} Y`.
  have hlift_homology : (H a).map lift = 0 := by
    apply (cancel_mono ((H a).map ((t.truncLTι (a + 1)).app Y))).1
    simpa [Functor.map_comp, hlift, hg] using
      congrArg (fun k ↦ (H a).map k) hlift
  have htruncGE : ((t.truncLT (a + 1)).obj Y).IsGE a := by
    infer_instance
  let e := singleFunctor_iso_of_isGE_of_isLE ((t.truncLT (a + 1)).obj Y) a
  let q :
      (singleFunctor 𝒜 a).obj A₀ ⟶
        (singleFunctor 𝒜 a).obj ((H a).obj ((t.truncLT (a + 1)).obj Y)) :=
    lift ≫ e.hom
  have hq_homology : (H a).map q = 0 := by
    simp [q, Functor.map_comp, hlift_homology]
  have hq_zero : q = 0 :=
    single_map_eq_zero_of_homologyMap_eq_zero q hq_homology
  have hlift_zero : lift = 0 := by
    calc
      lift = q ≫ e.inv := by simp [q, Category.assoc]
      _ = 0 := by simp [hq_zero]
  rw [← hlift, hlift_zero]
  simp

/-- Helper for Lemma 13.12.5: a morphism into an object `≥ a` factors through
`X ⟶ τ_{\ge a + 1} X` once its degree-`a` homology map vanishes. -/
private theorem exists_factor_through_next_truncGE_of_isGE_and_homologyMap_eq_zero
    {X Y : DerivedCategory 𝒜} {a : ℤ}
    (f : X ⟶ Y)
    (hY : Y.IsGE a)
    (hf : (H a).map f = 0) :
    ∃ φ : (t.truncGE (a + 1)).obj X ⟶ Y,
      (t.truncGEπ (a + 1)).app X ≫ φ = f := by
  letI : Y.IsGE a := hY
  let desc : (t.truncGE a).obj X ⟶ Y := t.descTruncGE f a
  have hdesc : (t.truncGEπ a).app X ≫ desc = f := by
    simpa [desc] using t.π_descTruncGE (f := f) a
  haveI : IsIso ((H a).map ((t.truncGEπ a).app X)) :=
    homology_map_truncGEπ_isIso X a
  -- Proof comment: the descended map from `τ_{\ge a} X` still has zero degree-`a` homology.
  have hdesc_homology : (H a).map desc = 0 := by
    apply (cancel_epi ((H a).map ((t.truncGEπ a).app X))).1
    simpa [Functor.map_comp, hdesc, hf] using
      congrArg (fun k ↦ (H a).map k) hdesc
  let T : Triangle (DerivedCategory 𝒜) :=
    Triangle.mk
      (((_root_.truncGE_step_termIso X a).inv) ≫
        (t.truncLTι (a + 1)).app ((t.truncGE a).obj X))
      ((t.natTransTruncGEOfLE a (a + 1) (le_add_of_nonneg_right zero_le_one)).app X)
      (((t.truncGE (a + 1)).map ((t.truncGEπ a).app X)) ≫
        (t.truncGEδLT (a + 1)).app ((t.truncGE a).obj X) ≫
          ((_root_.truncGE_step_termIso X a).hom)⟦1⟧')
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T, _root_.truncGE_step_homologyTriangle] using
      _root_.truncGE_step_homology_triangle X a
  let g : (singleFunctor 𝒜 a).obj ((H a).obj X) ⟶ Y := T.mor₁ ≫ desc
  have hg_homology : (H a).map g = 0 := by
    -- Proof comment: after expanding the lower-step triangle, `H^a(g)` ends with `H^a(desc)=0`.
    dsimp [g]
    simpa [T, Functor.map_comp, hdesc_homology]
  have hg_zero : g = 0 := by
    exact single_to_hom_eq_zero_of_isGE_homologyMap_eq_zero hY g hg_homology
  have hg_zero' : T.mor₁ ≫ desc = 0 := by simpa [g] using hg_zero
  -- Proof comment: exactness of the lower-step distinguished triangle now factors `desc`
  -- through `τ_{\ge a + 1} X`.
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₂ T hT desc hg_zero'
  refine ⟨φ, ?_⟩
  calc
    (t.truncGEπ (a + 1)).app X ≫ φ =
        (t.truncGEπ a).app X ≫ T.mor₂ ≫ φ := by
          simpa [T, Category.assoc] using
            (congrArg (fun k ↦ k ≫ φ)
              (t.π_natTransTruncGEOfLE_app a (a + 1) (le_add_of_nonneg_right zero_le_one) X)).symm
    _ = (t.truncGEπ a).app X ≫ desc := by
          simpa [Category.assoc] using congrArg (fun k ↦ (t.truncGEπ a).app X ≫ k) hφ.symm
    _ = f := hdesc

/-- Helper for Lemma 13.12.5: the lower factorization statement in the derived category is proved
by induction on the initial segment of the composable-arrow diagram. -/
private theorem exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero_aux
    {a : ℤ} {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.right.IsGE a)
    (hstep : ∀ j (hj : j < n),
      (H (a + ((n - (j + 1) : ℕ) : ℤ))).map (S.arrow j hj).hom = 0) :
    ∃ φ : (t.truncGE (a + (n : ℤ))).obj S.left ⟶ S.right,
      (t.truncGEπ (a + (n : ℤ))).app S.left ≫ φ = S.hom := by
  induction n with
  | zero =>
      have hleft : S.left.IsGE a := by
        simpa [ComposableArrows.left, ComposableArrows.right, ComposableArrows.obj'] using h₀
      letI : S.left.IsGE a := hleft
      have hπ : IsIso ((t.truncGEπ a).app S.left) := by
        infer_instance
      rw [show a + ((0 : ℕ) : ℤ) = a by omega]
      let φ : (t.truncGE a).obj S.left ⟶ S.right :=
        @inv _ _ _ _ ((t.truncGEπ a).app S.left) hπ
      refine ⟨φ, ?_⟩
      dsimp [φ]
      simpa [ComposableArrows.hom, ComposableArrows.left, ComposableArrows.right,
        ComposableArrows.obj'] using IsIso.hom_inv_id ((t.truncGEπ a).app S.left)
  | succ n ih =>
      have htail :
          ∀ j (hj : j < n),
            (H (a + ((n - (j + 1) : ℕ) : ℤ))).map (((S.δ₀).arrow j hj).hom) = 0 := by
        intro j hj
        have hstep' :
            (H (a + ((n - (j + 1) : ℕ) : ℤ))).map (S.arrow (j + 1) (by omega)).hom = 0 := by
          have hindex :
              ((n + 1 - (j + 1 + 1) : ℕ) : ℤ) = ((n - (j + 1) : ℕ) : ℤ) := by
            omega
          have hnext :
              (H (a + ((n + 1 - (j + 1 + 1) : ℕ) : ℤ))).map
                  (S.arrow (j + 1) (by omega)).hom = 0 :=
            hstep (j + 1) (by omega)
          rw [hindex] at hnext
          exact hnext
        simpa [ComposableArrows.arrow, ComposableArrows.δ₀] using hstep'
      obtain ⟨ψ, hψ⟩ := ih S.δ₀ (by simpa [ComposableArrows.δ₀] using h₀) htail
      let u : S.left ⟶ (t.truncGE (a + (n : ℤ))).obj S.δ₀.left :=
        (S.arrow 0 (by omega)).hom ≫ (t.truncGEπ (a + (n : ℤ))).app S.δ₀.left
      have hY : ((t.truncGE (a + (n : ℤ))).obj S.δ₀.left).IsGE (a + (n : ℤ)) := by
        infer_instance
      have hu : (H (a + (n : ℤ))).map u = 0 := by
        -- Proof comment: the head arrow already vanishes on `H^{a+n}`, and the truncation
        -- projection only postcomposes it.
        dsimp [u]
        rw [Functor.map_comp]
        calc
          (H (a + (n : ℤ))).map (S.arrow 0 (by omega)).hom ≫
              (H (a + (n : ℤ))).map ((t.truncGEπ (a + (n : ℤ))).app S.δ₀.left) =
              0 ≫ (H (a + (n : ℤ))).map ((t.truncGEπ (a + (n : ℤ))).app S.δ₀.left) := by
                exact congrArg
                  (fun k ↦ k ≫ (H (a + (n : ℤ))).map ((t.truncGEπ (a + (n : ℤ))).app S.δ₀.left))
                  (hstep 0 (by omega))
          _ = 0 := by
                simpa using
                  (show
                    (0 : _) ≫ (H (a + (n : ℤ))).map ((t.truncGEπ (a + (n : ℤ))).app S.δ₀.left)
                      = 0 from CategoryTheory.Limits.zero_comp)
      obtain ⟨θ, hθ⟩ :=
        exists_factor_through_next_truncGE_of_isGE_and_homologyMap_eq_zero u hY hu
      rw [show a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 by omega]
      let φ : (t.truncGE (a + (n : ℤ) + 1)).obj S.left ⟶ S.right := θ ≫ ψ
      have hmain₂ :
          u ≫ ψ = (S.arrow 0 (by omega)).hom ≫ S.δ₀.hom := by
        dsimp [u]
        simpa [Category.assoc] using
          congrArg (fun k ↦ (S.arrow 0 (by omega)).hom ≫ k) hψ
      have hmain₃ : (S.arrow 0 (by omega)).hom ≫ S.δ₀.hom = S.hom := by
        simpa [ComposableArrows.hom, ComposableArrows.arrow, ComposableArrows.δ₀,
          ComposableArrows.left, ComposableArrows.right, ComposableArrows.obj',
          Category.assoc] using (S.map'_comp 0 1 (n + 1 : ℕ)).symm
      have hmain :
          (t.truncGEπ (a + (n : ℤ) + 1)).app S.left ≫ φ = S.hom := by
        dsimp [φ]
        have hmain₁ :
            (t.truncGEπ (a + (n : ℤ) + 1)).app S.left ≫ θ ≫ ψ = u ≫ ψ := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ ψ) hθ
        exact hmain₁.trans (hmain₂.trans hmain₃)
      exact ⟨φ, hmain⟩

-- Proof sketch for Lemma 13.12.5 (2): keep the source-faithful chain of actual cochain-complex
-- maps, pass it to `D(\mathcal A)` through `DerivedCategory.Q`, and then obtain the required
-- factorization of the induced derived morphism.
/-- Lemma 13.12.5 (2): if `Kₙ^• ⟶ Kₙ₋₁^• ⟶ ⋯ ⟶ K₀^•` is a chain of cochain-complex maps whose
target `K₀^•` is `≥ 0` in `D(\mathcal A)` (equivalently, has no negative cohomology) and whose
map `H^j(K_{j + 1}^•) ⟶ H^j(K_j^•)` vanishes at each step, then the induced composite in
`D(\mathcal A)` factors through the canonical map
`Q(Kₙ^•) ⟶ τ_{\ge n}(Q(Kₙ^•))`. In the forward `ComposableArrows` parameter `S`, this source
condition is recorded on `S.arrow j` in degree `n - (j + 1)`. -/
@[stacks 08Q2]
theorem exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (CochainComplex 𝒜 ℤ) n)
    (h₀ : (DerivedCategory.Q.obj S.right).IsGE 0)
    (hstep : ∀ j (hj : j < n),
      (H ((n - (j + 1) : ℕ) : ℤ)).map (DerivedCategory.Q.map ((S.arrow j hj).hom)) = 0) :
    ∃ φ : (t.truncGE (n : ℤ)).obj (DerivedCategory.Q.obj S.left) ⟶ DerivedCategory.Q.obj S.right,
      (t.truncGEπ (n : ℤ)).app (DerivedCategory.Q.obj S.left) ≫ φ =
        DerivedCategory.Q.map S.hom := by
  let SQ : ComposableArrows (DerivedCategory 𝒜) n := S ⋙ DerivedCategory.Q
  have hstepQ :
      ∀ j (hj : j < n),
        (H (0 + ((n - (j + 1) : ℕ) : ℤ))).map ((SQ.arrow j hj).hom) = 0 := by
    intro j hj
    have hstepQ' :
        (H ((n - (j + 1) : ℕ) : ℤ)).map ((SQ.arrow j hj).hom) = 0 := by
      simpa [SQ, ComposableArrows.arrow, Functor.comp_map] using hstep j hj
    rw [show (0 : ℤ) + ((n - (j + 1) : ℕ) : ℤ) = ((n - (j + 1) : ℕ) : ℤ) by omega]
    exact hstepQ'
  rw [show (n : ℤ) = 0 + (n : ℤ) by omega]
  simpa [SQ, Functor.comp_obj, Functor.comp_map, ComposableArrows.hom,
    ComposableArrows.left, ComposableArrows.right, ComposableArrows.obj'] using
    (exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero_aux
      (a := 0) (S := SQ) (by simpa [SQ] using h₀) hstepQ)

end

end CategoryTheory
