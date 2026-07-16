import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.stacks_project.Chap13.Remark_13_12_4

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
  `TStructure.liftTruncLE`,
  `TStructure.descTruncGE`,
  `t.truncLEι`,
  `t.truncGEπ`;
- best owner abstraction: the source-facing data are already a chain in `DerivedCategory 𝒜`,
  whose endpoint boundedness belongs to the canonical owners `S.left.IsLE 0` and
  `S.right.IsGE 0`; the degreewise vanishing of the induced homology maps remains explicit
  primitive data, but now at the same owner layer;
- primitive data: the composable-arrow diagram `S : ComposableArrows (DerivedCategory 𝒜) n` and
  the vanishing of the degree `-j` or `j` homology-functor maps for its successive arrows
  `S.arrow j`;
- derived API: existence of a factorization through the canonical truncation maps
  `τ_{\le -n}(S.right) ⟶ S.right` and `S.left ⟶ τ_{\ge n}(S.left)`;
- source/core/bridge triage:
  `source-facing`: the two factorization theorems below;
  `core/canonical`: the owners `DerivedCategory.IsLE` / `IsGE`, the homology functors `H i`,
    and the truncation morphisms `t.truncLEι`, `t.truncGEπ`;
  `bridge/view`: `DerivedCategory.isLE_iff` / `isGE_iff`, translating the textbook cohomology
    vanishing conditions into those owner predicates.

Accordingly, this file keeps the two source-facing factorization theorems, upgrades only the
public surface from chosen cochain-complex representatives to the intrinsic derived-category
objects and deletes the redundant complex-level wrapper surface.
-/

/-- Helper for Lemma 13.12.5: an object of the derived category concentrated in degree `n` is a
single object on its degree-`n` homology. -/
private noncomputable def singleFunctor_iso_of_isGE_of_isLE
    (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor 𝒜 n).obj ((H n).obj X) := by
  classical
  -- Use the canonical single-degree model provided by the derived-category `t`-structure.
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (singleFunctor 𝒜 n).obj Y := Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso 𝒜 n).app Y
  exact e ≪≫ (singleFunctor 𝒜 n).mapIso eH.symm

/-- Helper for Lemma 13.12.5: the degree-`n` homology map induced by the lower truncation
projection `K ⟶ τ_{\ge n} K` is an isomorphism. -/
private theorem homology_map_truncGEπ_isIso
    (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    -- The lower truncation discards all degree-`n` homology from the first term.
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    -- The connecting morphism also lands in a vanishing degree for the same reason.
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using isIso_of_mono_of_epi ((H n).map T.mor₂)

/-- Helper for Lemma 13.12.5: the degree-`n₀` homology map induced by the upper truncation
inclusion `τ_{< n₁} K ⟶ K` is an isomorphism when `n₁ = n₀ + 1`. -/
private theorem homology_map_truncLTι_isIso
    (K : DerivedCategory 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) := by
  subst h
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE (n₀ + 1)).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished (n₀ + 1) K
  have h₃ : T.obj₃.IsGE (n₀ + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H n₀).map T.mor₂ = 0 := by
    -- The upper truncation quotient has no degree-`n₀` homology.
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) n₀ (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (n₀ - 1) n₀ (by omega) = 0 := by
    -- The connecting morphism starts in the same vanishing range.
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) (n₀ - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H n₀).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n₀).2 hmor₂_zero
  letI : Mono ((H n₀).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (n₀ - 1) n₀ (by omega)).2 hδ_zero
  simpa [T] using isIso_of_mono_of_epi ((H n₀).map T.mor₁)

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
  simpa [truncLE_step_term_iso] using _root_.truncLE_step_homology_triangle (K := K) (a := a)

/-- Helper for Lemma 13.12.5: a morphism between single-degree objects is zero once its
degree-`a` homology map is zero. -/
private theorem single_map_eq_zero_of_homologyMap_eq_zero
    {A B : 𝒜} {a : ℤ} (q : (singleFunctor 𝒜 a).obj A ⟶ (singleFunctor 𝒜 a).obj B)
    (hq : (H a).map q = 0) :
    q = 0 := by
  let η := singleFunctorCompHomologyFunctorIso 𝒜 a
  let q₀ : A ⟶ B := (singleFunctor 𝒜 a).preimage q
  have hη :
      η.app A ≫ q₀ = 0 := by
    -- Apply the canonical owner identification `H^a(A[a]) ≅ A` to transport the vanishing of
    -- the degree-`a` homology map back to the underlying map `A ⟶ B`.
    have hnat := NatIso.naturality_1 η q₀
    rw [(singleFunctor 𝒜 a).map_preimage q] at hnat
    simpa [q₀, hq, Category.assoc] using hnat.symm
  have hq₀ : q₀ = 0 := by
    exact (cancel_epi (η.app A)).1 hη
  -- Faithfulness of `singleFunctor` turns the vanishing of the underlying map into `q = 0`.
  rw [← (singleFunctor 𝒜 a).map_preimage q, hq₀]
  simp

/-- Helper for Lemma 13.12.5: in the upper-step triangle, the middle morphism induces an
isomorphism on the top surviving homology. -/
private theorem homology_map_truncLE_step_mor₂_isIso
    (X : DerivedCategory 𝒜) (a : ℤ) :
    IsIso ((H a).map (_root_.truncLE_step_homologyTriangle X (a - 1)).mor₂) := by
  -- The upper-step middle map is the truncation projection followed by an isomorphism of
  -- concentrated degree-`a` objects, so its degree-`a` homology map is an isomorphism.
  dsimp [_root_.truncLE_step_homologyTriangle]
  letI :
      IsIso ((H a).map ((Functor.whiskerLeft (t.truncLT (a + 1)) (t.truncGEπ a)).app X)) := by
    simpa using homology_map_truncGEπ_isIso (K := (t.truncLT (a + 1)).obj X) (n := a)
  letI : IsIso ((_root_.truncLE_step_termIso X (a - 1)).hom) := by
    infer_instance
  letI : IsIso ((H a).map ((_root_.truncLE_step_termIso X (a - 1)).hom)) := by
    infer_instance
  simpa [Functor.map_comp] using
    (inferInstance :
      IsIso
        ((H a).map ((Functor.whiskerLeft (t.truncLT (a + 1)) (t.truncGEπ a)).app X) ≫
          (H a).map ((_root_.truncLE_step_termIso X (a - 1)).hom)))

/-- Helper for Lemma 13.12.5: if `X` is bounded above in degree `a`, then a morphism
`X ⟶ A₀[a]` is zero once its degree-`a` homology map is zero. -/
private theorem hom_to_single_eq_zero_of_isLE_homologyMap_eq_zero
    {X : DerivedCategory 𝒜} {A₀ : 𝒜} {a : ℤ}
    (hX : X.IsLE a)
    (g : X ⟶ (singleFunctor 𝒜 a).obj A₀)
    (hg : (H a).map g = 0) :
    g = 0 := by
  let T := _root_.truncLE_step_homologyTriangle X (a - 1)
  letI : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using _root_.truncLE_step_homology_triangle (K := X) (a := a - 1)
  let f : T.obj₂ ⟶ (singleFunctor 𝒜 a).obj A₀ := (t.truncLTι (a + 1)).app X ≫ g
  have hmor₁_zero : T.mor₁ ≫ f = 0 := by
    have hLE : T.obj₁.IsLE (a - 1) := by
      dsimp [T, _root_.truncLE_step_homologyTriangle]
      infer_instance
    -- The first truncation piece lives strictly below degree `a`, so it has no maps into `A₀[a]`.
    simpa [f, T, Category.assoc] using
      (TStructure.t.zero_of_isLE_of_isGE (T.mor₁ ≫ f) (a - 1) a (by omega) hLE
        (inferInstance : ((singleFunctor 𝒜 a).obj A₀).IsGE a))
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₂
    (T := T) (inferInstance : Triangle.IsCoSpecial T) 0 ((singleFunctor 𝒜 a).obj A₀)
    (f := f) hmor₁_zero
  haveI : IsIso ((H a).map T.mor₂) := by
    simpa [T] using homology_map_truncLE_step_mor₂_isIso (X := X) (a := a)
  have hf_homology : (H a).map f = 0 := by
    -- The upper truncation inclusion is an isomorphism on degree `a` homology, and `g` has
    -- zero degree `a` homology map by hypothesis.
    change (H a).map ((t.truncLTι (a + 1)).app X) ≫ (H a).map g = 0
    simpa [Functor.map_comp, Category.assoc, hg]
  have hψ_homology : (H a).map ψ = 0 := by
    have hcomp : (H a).map T.mor₂ ≫ (H a).map ψ = 0 := by
      simpa [Functor.map_comp, hψ, hf_homology, Category.assoc]
    exact (cancel_epi ((H a).map T.mor₂)).1 hcomp
  have hψ_zero : ψ = 0 :=
    single_map_eq_zero_of_homologyMap_eq_zero ψ hψ_homology
  have hf_zero : f = 0 := by
    simpa [hψ, hψ_zero]
  have hι : IsIso ((t.truncLTι (a + 1)).app X) :=
    (t.isLE_iff_isIso_truncLTι_app a (a + 1) (by omega) X).1 hX
  exact (cancel_epi ((t.truncLTι (a + 1)).app X)).1 (by simpa [f] using hf_zero)

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
  let fLT : X ⟶ (t.truncLT (a + 1)).obj Y := t.liftTruncLT f a (a + 1) rfl
  let T := _root_.truncLE_step_homologyTriangle Y (a - 1)
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using _root_.truncLE_step_homology_triangle (K := Y) (a := a - 1)
  have hfLT_homology : (H a).map fLT = 0 := by
    -- The lifted map has the same degree-`a` homology map because `τ_{< a + 1} Y ⟶ Y`
    -- is an isomorphism on degree `a`.
    letI : IsIso ((H a).map ((t.truncLTι (a + 1)).app Y)) :=
      homology_map_truncLTι_isIso (K := Y) (n₀ := a) (n₁ := a + 1) rfl
    have hfac :
        (H a).map fLT ≫ (H a).map ((t.truncLTι (a + 1)).app Y) =
          (H a).map f := by
      simpa [fLT, Functor.map_comp] using
        congrArg (fun k ↦ (H a).map k) (t.liftTruncLT_ι f a (a + 1) rfl)
    apply (cancel_mono ((H a).map ((t.truncLTι (a + 1)).app Y))).1
    simpa [hf] using hfac
  let fSingle : X ⟶ (singleFunctor 𝒜 a).obj ((H a).obj Y) := fLT ≫ T.mor₂
  have hfSingle_zero : fSingle = 0 := by
    -- Route correction: after lifting to `τ_{< a + 1} Y`, kill the map to the single-degree
    -- term by the upper-bounded bridge lemma instead of chasing transports in the triangle.
    refine hom_to_single_eq_zero_of_isLE_homologyMap_eq_zero hX fSingle ?_
    change (H a).map fLT ≫ (H a).map T.mor₂ = 0
    simpa [fSingle, Functor.map_comp, hfLT_homology]
  obtain ⟨φ, hφ⟩ := Triangle.coyoneda_exact₂ (T := T) hT fLT (by
    -- The upper-step triangle now forces the lifted map to factor through the preceding
    -- truncation stage.
    simpa [fSingle] using hfSingle_zero)
  refine ⟨φ, ?_⟩
  -- Compose the factorization with the canonical inclusion `τ_{< a + 1} Y ⟶ Y` to recover `f`.
  calc
    φ ≫ (t.truncLEι (a - 1)).app Y =
        φ ≫ T.mor₁ ≫ (t.truncLTι (a + 1)).app Y := by
          simpa [T, _root_.truncLE_step_homologyTriangle, Category.assoc]
    _ = fLT ≫ (t.truncLTι (a + 1)).app Y := by rw [← hφ]
    _ = f := by
          simpa [fLT] using t.liftTruncLT_ι f a (a + 1) rfl

-- Proof sketch: argue by induction on the length of the composable-arrow diagram. The case
-- `n = 1` comes from the distinguished truncation triangle of Remark 13.12.4 and the vanishing
-- of the induced map on degree-`0` homology; the induction step factors first through
-- `τ_{\le -(n-1)}` of the penultimate complex and then applies the case `n = 1` to the induced
-- map between successive truncations.
/-- Lemma 13.12.5: if `K₀ ⟶ ⋯ ⟶ Kₙ` is a chain in `D(\mathcal A)` whose source is `≤ 0`
(equivalently, has no positive cohomology) and whose degree-`-j` homology-functor maps vanish at
each step, then the total composite factors through the canonical truncation map
`τ_{\le -n}(Kₙ) ⟶ Kₙ`. -/
theorem exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.left.IsLE 0)
    (hstep : ∀ j (hj : j < n), (H (-(j : ℤ))).map (S.arrow j hj).hom = 0) :
    ∃ φ : S.left ⟶ (t.truncLE (-(n : ℤ))).obj S.right,
      φ ≫ (t.truncLEι (-(n : ℤ))).app S.right = S.hom := by
  induction n generalizing S with
  | zero =>
      have hι : IsIso ((t.truncLEι 0).app S.right) :=
        (t.isLE_iff_isIso_truncLEι_app 0 S.right).1 h₀
      let e : (t.truncLE 0).obj S.right ≅ S.right :=
        asIso ((t.truncLEι 0).app S.right)
      refine ⟨e.inv, ?_⟩
      -- In the zero-step case the total composite is the identity, so the inverse truncation map
      -- already gives the required factorization.
      simpa [ComposableArrows.hom, e] using e.inv_hom_id
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
        -- The degree `-n` homology of the truncation inclusion is an isomorphism, so the
        -- stepwise vanishing for the last arrow transports to the induced map from `τ_{\le -n}`.
        letI :
            IsIso ((H (-(n : ℤ))).map ((t.truncLEι (-(n : ℤ))).app S.δlast.right)) := by
          simpa using
            homology_map_truncLTι_isIso
              (K := S.δlast.right) (n₀ := -(n : ℤ)) (n₁ := -(n : ℤ) + 1) rfl
        apply (cancel_mono ((H (-(n : ℤ))).map ((t.truncLEι (-(n : ℤ))).app S.δlast.right))).1
        simpa [f, Functor.map_comp, Category.assoc] using hstep n (by omega)
      obtain ⟨φstep, hφstep⟩ :=
        exists_factor_through_prev_truncLE_of_isLE_and_homologyMap_eq_zero
          (f := f) (X := (t.truncLE (-(n : ℤ))).obj S.δlast.right) (Y := S.right)
          (a := -(n : ℤ)) inferInstance hf
      have hindex : (-(n : ℤ)) - 1 = -((n + 1 : ℕ) : ℤ) := by
        omega
      refine ⟨φtail ≫ φstep, ?_⟩
      -- First factor through the penultimate truncation stage, then apply the one-step case to
      -- the last arrow. The chain decomposition `S.hom = S.δlast.hom ≫ S.arrow n` supplies the
      -- final comparison.
      calc
        (φtail ≫ φstep) ≫ (t.truncLEι (-((n + 1 : ℕ) : ℤ))).app S.right =
            φtail ≫ f := by
              simpa [hindex, Category.assoc] using congrArg (fun k ↦ φtail ≫ k) hφstep
        _ = φtail ≫ f := by
              rfl
        _ = (φtail ≫ (t.truncLEι (-(n : ℤ))).app S.δlast.right) ≫ (S.arrow n (by omega)).hom := by
              simp [f, Category.assoc]
        _ = S.δlast.hom ≫ (S.arrow n (by omega)).hom := by
              rw [hφtail]
        _ = S.hom := by
              simpa [ComposableArrows.arrow, ComposableArrows.δlast, ComposableArrows.hom] using
                (S.map'_comp 0 n (n + 1))

-- Proof sketch: apply the previous induction argument to the dual truncation triangles. The base
-- case `n = 1` uses the distinguished triangle for `τ_{\ge 1}`, and the induction step factors
-- successively through `τ_{\ge j}` because each degree-`j` homology map is zero.
/-- Dual form of Lemma 13.12.5: if `K₀ ⟶ ⋯ ⟶ Kₙ` is a chain in `D(\mathcal A)` whose target is
`≥ 0` (equivalently, has no negative cohomology) and whose degree-`j` homology-functor maps
vanish at each step, then the total composite factors through the canonical map
`K₀ ⟶ τ_{\ge n}(K₀)`. -/
theorem exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.right.IsGE 0)
    (hstep : ∀ j (hj : j < n), (H (j : ℤ)).map (S.arrow j hj).hom = 0) :
    ∃ φ : (t.truncGE (n : ℤ)).obj S.left ⟶ S.right,
      (t.truncGEπ (n : ℤ)).app S.left ≫ φ = S.hom := by
  -- TODO: prove the dual one-step factorization through `τ_{\ge a+1}` using
  -- `_root_.truncGE_step_homologyTriangle`, then iterate it along the textbook truncation stages
  -- `τ_{\ge j}(K_j)` to match the reverse-indexed argument without introducing ad hoc suffix APIs.
  sorry

end CategoryTheory
