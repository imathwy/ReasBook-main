import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_4
import StacksProject_2024.stacks_project.Chap13.Remark_13_35_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory
open DerivedCategory.TStructure
open CategoryTheory.Pretriangulated

universe w v u

noncomputable section

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/- Domain-style sampling for Lemma 13.35.7:
- primary domain: interval-generated object properties in the derived category of an abelian
  category, together with the canonical boundedness owners on `DerivedCategory A` and
  `CochainComplex A ℤ`;
- sampled owner declarations:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`,
  `CategoryTheory.ObjectProperty.additiveClosure`,
  `CategoryTheory.ObjectProperty.shiftInterval`,
  `CategoryTheory.ObjectProperty.additiveExtensionStage`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: keep the source-facing interval stage of `D(A)` while expressing it
  directly through the Chapter 13 owners `shiftInterval` and `additiveExtensionStage`; the
  boundedness hypotheses use the canonical owners `K.IsGE a` / `K.IsLE b`, and a chosen cochain
  representative uses the canonical support owners `L.IsStrictlyGE a` / `L.IsStrictlyLE b`;
- primitive-vs-derived split:
  primitive data are the interval family
  `(E.map (singleFunctor A 0))[a, b]`, the Chapter 13 owner
  `additiveExtensionStage
    ((E.map (singleFunctor A 0))[a, b]) (Nat.succPNat (Int.toNat (b - a)))`,
  the canonical boundedness owners on `K`, and a chosen cochain-complex representative of `K`
  with canonical support bounds;
  derived API is the four membership lemmas below.

Source/core/bridge triage:
- `source-facing`: the four membership lemmas;
- `core/canonical`: `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `CochainComplex.IsStrictlyGE`, `CochainComplex.IsStrictlyLE`, `shiftInterval`,
  `additiveClosure`, `retractClosure`, and `additiveExtensionStage`;
- `bridge/view`: none beyond the direct source-facing use of the Chapter 13 owner
  `additiveExtensionStage
    ((E.map (singleFunctor A 0))[a, b]) (Nat.succPNat (Int.toNat (b - a)))`
  for `smd(add(\mathcal E[a,b])^{\star (b-a+1)})`.
-/

variable (E : ObjectProperty A) (K : DerivedCategory A) (a b : ℤ)

local notation "H" => homologyFunctor A
local notation "single₀" => singleFunctor A (0 : ℤ)
local notation "intervalStage" =>
  additiveExtensionStage
    ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a)))

/-- Helper for Lemma 13.35.7: enlarging the upper bound of a shift interval enlarges the
corresponding object property. -/
lemma shiftInterval_mono_upper
    (P : ObjectProperty (DerivedCategory A)) (a b c : ℤ) (hbc : b ≤ c) :
    P[a, b] ≤ P[a, c] := by
  -- Reuse the same witnessing shift in the larger interval.
  intro X hX
  rw [prop_shiftInterval_iff] at hX ⊢
  rcases hX with ⟨n, hn, hX⟩
  exact ⟨n, ⟨hn.1, hn.2.trans hbc⟩, hX⟩

/-- Helper for Lemma 13.35.7: lowering the left endpoint of a shift interval enlarges the
corresponding object property. -/
lemma shiftInterval_mono_lower
    (P : ObjectProperty (DerivedCategory A)) (a b c : ℤ) (hca : c ≤ a) :
    P[a, b] ≤ P[c, b] := by
  -- Reuse the same witnessing shift in the larger interval.
  intro X hX
  rw [prop_shiftInterval_iff] at hX ⊢
  rcases hX with ⟨n, hn, hX⟩
  exact ⟨n, ⟨hca.trans hn.1, hn.2⟩, hX⟩

/-- Helper for Lemma 13.35.7: an object bounded both below and above in a single degree is a
single shifted object on its degree-`n` cohomology. -/
noncomputable def singleFunctorIso_of_isGE_of_isLE
    (X : DerivedCategory A) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor A n).obj ((H n).obj X) := by
  classical
  -- Use the canonical single-degree model supplied by the derived-category `t`-structure.
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (singleFunctor A n).obj Y := Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso A n).app Y
  exact e ≪≫ (singleFunctor A n).mapIso eH.symm

/-- Helper for Lemma 13.35.7: the map on degree-`n₀` cohomology induced by the upper truncation
inclusion `τ_{< n₁} K ⟶ K` is an isomorphism when `n₁ = n₀ + 1`. -/
lemma isIso_homologyMap_truncLTι
    (K : DerivedCategory A) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) := by
  subst h
  let T : Triangle (DerivedCategory A) := (t.triangleLTGE (n₀ + 1)).obj K
  have hT : T ∈ distTriang (DerivedCategory A) := by
    simpa [T] using t.triangleLTGE_distinguished (n₀ + 1) K
  have h₃ : T.obj₃.IsGE (n₀ + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H n₀).map T.mor₂ = 0 := by
    -- The third truncation piece has no cohomology below degree `n₀ + 1`.
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) n₀ (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (n₀ - 1) n₀ (by omega) = 0 := by
    -- The connecting morphism also lands in zero for the same degree reason.
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) (n₀ - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H n₀).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n₀).2 hmor₂_zero
  letI : Mono ((H n₀).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (n₀ - 1) n₀ (by omega)).2 hδ_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n₀).map T.mor₁))

/-- Helper for Lemma 13.35.7: the map on degree-`n` cohomology induced by the lower truncation
projection `K ⟶ τ_{≥ n} K` is an isomorphism. -/
lemma isIso_homologyMap_truncGEπ
    (K : DerivedCategory A) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle (DerivedCategory A) := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang (DerivedCategory A) := by
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n).map T.mor₂))

/-- Helper for Lemma 13.35.7: the top cohomology of the successive upper truncation agrees with
the corresponding cohomology of the original derived object. -/
private noncomputable def truncLE_step_homologyIso
    (K : DerivedCategory A) (a : ℤ) :
    (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (H (a + 1)).obj K := by
  -- Compare first with the `truncGE` piece and then with the original object.
  let eπ :
      (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅
        (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) := by
    exact @asIso _ _ _ _
      ((H (a + 1)).map ((t.truncGEπ (a + 1)).app ((t.truncLT (a + 2)).obj K)))
      (isIso_homologyMap_truncGEπ (A := A) ((t.truncLT (a + 2)).obj K) (a + 1))
  let eι : (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅ (H (a + 1)).obj K :=
    by
      exact @asIso _ _ _ _
        ((H (a + 1)).map ((t.truncLTι (a + 2)).app K))
        (isIso_homologyMap_truncLTι (A := A) K (a + 1) (a + 2) (by omega))
  exact eπ.symm ≪≫ eι

/-- Helper for Lemma 13.35.7: the successive upper-truncation quotient is the single object on the
top cohomology term. -/
private noncomputable def truncLE_step_termIso
    (K : DerivedCategory A) (a : ℤ) :
    ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (singleFunctor A (a + 1)).obj ((H (a + 1)).obj K) := by
  have h : (a + 2) - 1 = a + 1 := by
    omega
  have hLE :
      ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE (a + 1) := by
    simpa [h] using
      (inferInstance :
        ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE ((a + 2) - 1))
  let e :
      ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
        (singleFunctor A (a + 1)).obj
          ((H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K))) :=
    singleFunctorIso_of_isGE_of_isLE (A := A)
      ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) (a + 1)
  exact e ≪≫ (singleFunctor A (a + 1)).mapIso (truncLE_step_homologyIso (A := A) K a)

/-- Helper for Lemma 13.35.7: the successive upper truncations fit into the distinguished triangle
whose third term is the top cohomology object in degree `a + 1`. -/
private noncomputable def truncLE_step_homologyTriangle
    (K : DerivedCategory A) (a : ℤ) :
    Triangle (DerivedCategory A) :=
  Triangle.mk
    ((t.natTransTruncLTOfLE (a + 1) (a + 2) (by omega)).app K)
    (((Functor.whiskerLeft (t.truncLT (a + 2)) (t.truncGEπ (a + 1))).app K) ≫
      (truncLE_step_termIso (A := A) K a).hom)
    ((truncLE_step_termIso (A := A) K a).inv ≫ (t.truncGELTδLT (a + 1) (a + 2)).app K)

/-- Helper for Lemma 13.35.7: the source-facing upper-step triangle is isomorphic to the owner
truncation triangle. -/
private noncomputable def truncLE_step_homologyTriangleIso
    (K : DerivedCategory A) (a : ℤ) :
    truncLE_step_homologyTriangle (A := A) K a ≅
      (t.triangleLTLTGELT (a + 1) (a + 2) (by omega)).obj K := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (truncLE_step_termIso (A := A) K a).symm ?_ ?_ ?_
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]

/-- Helper for Lemma 13.35.7: the successive upper truncations of `K` and the top cohomology term
form a distinguished triangle. -/
private theorem truncLE_step_homology_triangle
    (K : DerivedCategory A) (a : ℤ) :
    truncLE_step_homologyTriangle (A := A) K a ∈ distTriang (DerivedCategory A) :=
  isomorphic_distinguished _
    (t.triangleLTLTGELT_distinguished (a + 1) (a + 2) (by omega) K) _
    (truncLE_step_homologyTriangleIso (A := A) K a)

/-- Helper for Lemma 13.35.7: every object of `E` belongs to its additive closure and then to its
retract closure. -/
lemma mem_additiveClosure_retractClosure_of_mem {X : A} (hX : E X) :
    E.additiveClosure.retractClosure X := by
  -- First enter the additive closure, then the outer retract closure.
  exact E.additiveClosure.le_retractClosure _ <|
    (E.le_colimitsClosure fun n : ℕ ↦ Discrete (Fin n)) _ hX

/-- Helper for Lemma 13.35.7: a single object in degree `i ∈ [a, b]` belongs to the interval
generated by the degree-`0` single functor. -/
lemma single_map_le_shiftInterval
    (i : Set.Icc a b) :
    E.map (singleFunctor A i.1) ≤ (E.map single₀)[a, b] := by
  -- The object `singleFunctor A i.1` is the shift-by-`i` of `singleFunctor A 0`.
  intro Y hY
  rw [prop_shiftInterval_iff]
  rcases hY with ⟨X, hX, ⟨e⟩⟩
  refine ⟨i.1, i.2, ?_⟩
  refine ⟨(singleFunctor A i.1).obj X, ?_, ⟨e.symm⟩⟩
  change (E.map single₀) (((singleFunctor A i.1).obj X)⟦i.1⟧)
  have hsingle₀ : (E.map single₀) ((singleFunctor A 0).obj X) :=
    E.prop_map_obj (singleFunctor A 0) hX
  -- Shift compatibility identifies `singleFunctor A i` shifted by `i` with `singleFunctor A 0`.
  exact (E.map single₀).prop_of_iso (((singleFunctors A).shiftIso i.1 0 i.1 (by simp)).symm.app X)
    hsingle₀

/-- Helper for Lemma 13.35.7: if `X` already lies in `smd(add(E))`, then the single object
`X[-i]` lies in stage `1` of the interval generator. -/
lemma single_mem_stage_one_of_mem_additiveClosure_retractClosure
    (i : Set.Icc a b) {X : A}
    (hX : E.additiveClosure.retractClosure X) :
    additiveExtensionStage ((E.map single₀)[a, b]) 1 ((singleFunctor A i.1).obj X) := by
  have hmap₁ :
      (E.additiveClosure.retractClosure).map (singleFunctor A i.1) ((singleFunctor A i.1).obj X) :=
    (E.additiveClosure.retractClosure).prop_map_obj _ hX
  have hmap₂ :
      (((E.map (singleFunctor A i.1)).additiveClosure).retractClosure)
        ((singleFunctor A i.1).obj X) := by
    have hle :
        (E.additiveClosure.retractClosure).map (singleFunctor A i.1) ≤
          ((E.map (singleFunctor A i.1)).additiveClosure).retractClosure := by
      refine (map_retractClosure_le (F := singleFunctor A i.1) E.additiveClosure).trans ?_
      exact monotone_retractClosure (map_additiveClosure_le (F := singleFunctor A i.1) E)
    exact hle _ hmap₁
  have hmono :
      additiveExtensionStage (E.map (singleFunctor A i.1)) 1 ≤
        additiveExtensionStage ((E.map single₀)[a, b]) 1 := by
    -- Stage `1` is monotone with respect to the generating object property.
    exact additiveExtensionStage_monotone (single_map_le_shiftInterval (E := E) (a := a) (b := b) i) 1
  -- Rewrite stage `1` as the retract closure of the additive closure.
  simpa [CategoryTheory.ObjectProperty.additiveExtensionStage] using hmono _ hmap₂

/-- Helper for Lemma 13.35.7: when the cohomology of `K` is concentrated in `[a, a + n]`, the
upper truncation `τ_{< a + n + 1}K` already belongs to the corresponding interval stage. -/
lemma truncLT_mem_additiveExtensionStage_of_homology_mem_additiveClosure
    (hGE : K.IsGE a) :
    ∀ n : ℕ,
      (∀ i : Set.Icc a (a + n),
        E.additiveClosure.retractClosure ((H i.1).obj K)) →
      additiveExtensionStage ((E.map single₀)[a, a + n]) (Nat.succPNat n)
        ((t.truncLT (a + n + 1)).obj K) := by
  intro n
  induction n with
  | zero =>
      intro hE
      have hGE' : ((t.truncLT (a + 1)).obj K).IsGE a := by
        infer_instance
      have hLE' : ((t.truncLT (a + 1)).obj K).IsLE a := by
        simpa using (inferInstance : ((t.truncLT (a + 1)).obj K).IsLE ((a + 1) - 1))
      have hH :
          (H a).obj ((t.truncLT (a + 1)).obj K) ≅ (H a).obj K := by
        exact @asIso _ _ _ _
          ((H a).map ((t.truncLTι (a + 1)).app K))
          (isIso_homologyMap_truncLTι (A := A) K a (a + 1) (by omega))
      let e :
          ((t.truncLT (a + 1)).obj K) ≅ (singleFunctor A a).obj ((H a).obj K) :=
        singleFunctorIso_of_isGE_of_isLE (A := A) ((t.truncLT (a + 1)).obj K) a ≪≫
          (singleFunctor A a).mapIso hH
      have hsingle :
          additiveExtensionStage ((E.map single₀)[a, a]) 1
            ((singleFunctor A a).obj ((H a).obj K)) := by
        -- In the base case only the degree-`a` cohomology survives.
        exact single_mem_stage_one_of_mem_additiveClosure_retractClosure
          (E := E) (a := a) (b := a) ⟨a, by simp⟩ (hE ⟨a, by simp⟩)
      simpa using
        (additiveExtensionStage ((E.map single₀)[a, a]) 1).prop_of_iso e.symm hsingle
  | succ n ih =>
      intro hE
      have hIH :
          additiveExtensionStage ((E.map single₀)[a, a + n]) (Nat.succPNat n)
            ((t.truncLT (a + n + 1)).obj K) := by
        -- Restrict the cohomology-membership hypothesis to the smaller interval.
        refine ih ?_
        intro i
        exact hE ⟨i.1, ⟨i.2.1, le_trans i.2.2 (by omega)⟩⟩
      have hIH' :
          additiveExtensionStage ((E.map single₀)[a, a + n + 1]) (Nat.succPNat n)
            ((t.truncLT (a + n + 1)).obj K) := by
        -- Enlarge the interval generator from `[a, a + n]` to `[a, a + n + 1]`.
        exact additiveExtensionStage_monotone
          (shiftInterval_mono_upper (P := E.map single₀) a (a + n) (a + n + 1) (by omega))
          (Nat.succPNat n) _ hIH
      have htop :
          additiveExtensionStage ((E.map single₀)[a, a + n + 1]) 1
            ((singleFunctor A (a + n + 1)).obj ((H (a + n + 1)).obj K)) := by
        -- The new top cohomology term contributes the extra extension step.
        exact single_mem_stage_one_of_mem_additiveClosure_retractClosure
          (E := E) (a := a) (b := a + n + 1)
          ⟨a + n + 1, ⟨by omega, by simp⟩⟩
          (hE ⟨a + n + 1, ⟨by omega, by simp⟩⟩)
      rw [show Nat.succPNat (n + 1) = Nat.succPNat n + 1 by rfl]
      rw [additiveExtensionStage_add]
      let P :=
        additiveExtensionStage ((E.map single₀)[a, a + n + 1]) (Nat.succPNat n)
      let Q :=
        additiveExtensionStage ((E.map single₀)[a, a + n + 1]) 1
      let T := truncLE_step_homologyTriangle (A := A) K (a + n)
      have hExt :
          ObjectProperty.extensionProduct P Q T.obj₂ := by
        rw [extensionProduct_iff]
        -- The truncation step triangle realizes the next object as an extension of the previous
        -- truncation by the top cohomology object.
        refine ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃,
          truncLE_step_homology_triangle (A := A) K (a + n), ?_, ?_⟩
        · simpa [P, T, truncLE_step_homologyTriangle, Nat.cast_add, add_assoc] using hIH'
        · simpa [Q, T, truncLE_step_homologyTriangle, Nat.cast_add, add_assoc] using htop
      have hExt' :
          ObjectProperty.extensionProduct
            (((E.map single₀)[a, a + (n + 1)]).additiveExtensionStage (Nat.succPNat n))
            (((E.map single₀)[a, a + (n + 1)]).additiveExtensionStage 1)
            ((t.truncLT (a + (n + 1) + 1)).obj K) := by
        simpa [P, Q, T, truncLE_step_homologyTriangle, Nat.cast_add, add_assoc] using hExt
      exact le_retractClosure _ _ hExt'

/-- Helper for Lemma 13.35.7: clause `(2)` proved on the cohomology-side, before clause `(1)` is
recovered by the inclusion `E ⊆ smd(add(E))`. -/
lemma mem_additiveExtensionStage_of_homology_mem_additiveClosure_core
    (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hE : ∀ i : Set.Icc a b,
      E.additiveClosure.retractClosure ((H i.1).obj K)) :
    additiveExtensionStage
      ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a))) K := by
  by_cases hba : b < a
  · -- If the support interval is empty, the bounded object is zero.
    exact ObjectProperty.prop_of_isZero
      (P := additiveExtensionStage
        ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a))))
      (t.isZero K b a hba)
  · have hab : a ≤ b := by omega
    let n : ℕ := Int.toNat (b - a)
    have hb : b = a + (n : ℤ) := by
      dsimp [n]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
      omega
    have htrunc :
        additiveExtensionStage ((E.map single₀)[a, a + n]) (Nat.succPNat n)
          ((t.truncLT (a + n + 1)).obj K) := by
      exact truncLT_mem_additiveExtensionStage_of_homology_mem_additiveClosure
        (E := E) (K := K) (a := a) hGE n (by simpa [hb] using hE)
    have hLE' : K.IsLE (a + n) := by
      simpa [hb] using hLE
    let e : (t.truncLT (a + n + 1)).obj K ≅ K := by
      exact @asIso _ _ _ _
        ((t.truncLTι (a + n + 1)).app K)
        ((t.isLE_iff_isIso_truncLTι_app (a + n) (a + n + 1) (by omega) K).1 hLE')
    -- Replace `τ_{≤ b}K` by `K` using the bounded-above hypothesis.
    simpa [hb, Int.toNat_of_nonneg (sub_nonneg.mpr hab)] using
      (additiveExtensionStage ((E.map single₀)[a, a + n]) (Nat.succPNat n)).prop_of_iso e htrunc

-- Proof sketch: induct on the length `b - a`, using the truncation triangle for the top
-- cohomology object and Lemma `13.35.4` to add one more extension step; the base case is a single
-- shifted cohomology object in degree `a`.
/-- Lemma 13.35.7 (1): if the cohomology of `K` is supported on `[a, b]` and every cohomology
object `H^i(K)` for `i ∈ [a, b]` belongs to `E`, then `K` lies in the textbook stage
`smd(add(\mathcal E[a,b])^{\star (b - a + 1)})`, encoded here by the Chapter 13 owner
`additiveExtensionStage
  ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a)))`. -/
theorem mem_additiveExtensionStage_of_homology_mem
    (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hE : ∀ i : Set.Icc a b, E ((H i.1).obj K)) :
    intervalStage K := by
  -- Reduce clause `(1)` to clause `(2)` by passing from `E` to `smd(add(E))`.
  refine mem_additiveExtensionStage_of_homology_mem_additiveClosure_core
    (E := E) (K := K) (a := a) (b := b) hGE hLE ?_
  intro i
  exact mem_additiveClosure_retractClosure_of_mem (E := E) (hE i)

-- Proof sketch: apply clause `(1)` to the retract closure of the additive closure of `E` inside
-- `A`, then use that the derived-category interval stage generated by `E` already contains the
-- shifted objects coming from `smd(add(E))`.
/-- Lemma 13.35.7 (2): if the cohomology of `K` is supported on `[a, b]` and every cohomology
object `H^i(K)` for `i ∈ [a, b]` belongs to `smd(add(\mathcal E))`, encoded here by
`E.additiveClosure.retractClosure`, then `K` still lies in
`smd(add(\mathcal E[a,b])^{\star (b - a + 1)})`, encoded here by the Chapter 13 owner
`additiveExtensionStage
  ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a)))`. -/
theorem mem_additiveExtensionStage_of_homology_mem_additiveClosure
    (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hE : ∀ i : Set.Icc a b,
      E.additiveClosure.retractClosure ((H i.1).obj K)) :
    intervalStage K := by
  exact mem_additiveExtensionStage_of_homology_mem_additiveClosure_core
    (E := E) (K := K) (a := a) (b := b) hGE hLE hE

/-- Helper for Lemma 13.35.7: a representative complex supported in a single degree becomes the
corresponding single object in the derived category. -/
noncomputable abbrev representative_single_iso_of_strict_bounds
    (L : CochainComplex A ℤ) (n : ℤ) [L.IsStrictlyGE n] [L.IsStrictlyLE n] :
    Q.obj L ≅ (singleFunctor A n).obj (L.X n) :=
  let M : A := Classical.choose (CochainComplex.exists_iso_single (K := L) n)
  let e : L ≅ (HomologicalComplex.single A (ComplexShape.up ℤ) n).obj M :=
    Classical.choice (Classical.choose_spec (CochainComplex.exists_iso_single (K := L) n))
  let eX : L.X n ≅ M :=
    (HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapIso e ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M
  Q.mapIso e ≪≫ (singleFunctor A n).mapIso eX.symm

-- Clause `(4)` is proved below by induction on the width of a bounded representative.
-- The earlier top-truncation attempt is kept only as historical context; the remaining blocker is
-- now the shift-to-left-brutal-filtration pivot recorded in the successor case.
/-- Helper for Lemma 13.35.7: restricting the representative-term hypothesis from `[a, b]` to
`[a + 1, b]` keeps every term in the same retract closure. -/
lemma restrict_termwise_mem_Icc_succ_left
    {L : CochainComplex A ℤ}
    (hE : ∀ i : Set.Icc a b, E.additiveClosure.retractClosure (L.X i)) :
    ∀ i : Set.Icc (a + 1) b, E.additiveClosure.retractClosure (L.X i) := by
  -- Forgetting the first index of the interval keeps the ambient termwise membership hypothesis.
  intro i
  have hai : a ≤ i.1 := by
    exact le_trans (by omega) i.2.1
  exact hE ⟨i.1, ⟨hai, i.2.2⟩⟩

/-- Helper for Lemma 13.35.7: shifting a representative by its upper support bound turns the
strict upper bound into degree `0`. -/
lemma shifted_representative_isStrictlyLE_zero
    {L : CochainComplex A ℤ} {b : ℤ}
    (hLE : L.IsStrictlyLE b) :
    (L⟦b⟧).IsStrictlyLE 0 := by
  letI : L.IsStrictlyLE b := hLE
  -- Shifting by `b` moves the top nonzero degree `b` to `0`.
  simpa using CochainComplex.isStrictlyLE_shift (K := L) b b 0 (by omega)

/-- Helper for Lemma 13.35.7: if `Int.toNat (b - a) = n + 1`, then shifting by `b` moves the
left endpoint `a` of the support interval to `-((n + 1) : ℤ)`. -/
lemma shifted_representative_isStrictlyGE_left_endpoint
    {L : CochainComplex A ℤ} {a b : ℤ} {n : ℕ}
    (hn : Int.toNat (b - a) = n + 1)
    (hGE : L.IsStrictlyGE a) :
    (L⟦b⟧).IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := by
  have hab : a ≤ b := by
    by_contra hab
    have hnonpos : b - a ≤ 0 := by omega
    rw [Int.toNat_of_nonpos hnonpos] at hn
    omega
  have hwidth : b - a = ((n + 1 : ℕ) : ℤ) := by
    rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
  have hshift : b + (-((n + 1 : ℕ) : ℤ)) = a := by
    omega
  letI : L.IsStrictlyGE a := hGE
  -- The width identity converts the lower support bound into the new leftmost degree.
  simpa using
    CochainComplex.isStrictlyGE_shift (K := L) a b (-((n + 1 : ℕ) : ℤ)) hshift

/-- Helper for Lemma 13.35.7: if the shifted representative has no terms below
`-((n + 1) : ℤ)`, then the identity on the restricted stage extends back to the whole
complex. -/
lemma shifted_brutal_full_stage_hasLift
    (K : CochainComplex A ℤ) (n : ℕ)
    [K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ))] :
    (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))).HasLift
      (𝟙 (K.restriction (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))))) := by
  intro j hj i' hij
  have hj0 :
      j = 0 := by
    simpa using
      (ComplexShape.boundaryGE_embeddingUpIntGE_iff (-((n + 1 : ℕ) : ℤ)) j).1 hj
  subst hj0
  have hij' : i' + 1 = -((n + 1 : ℕ) : ℤ) := by
    simpa [ComplexShape.embeddingUpIntGE] using hij
  have hi : i' < -((n + 1 : ℕ) : ℤ) := by
    omega
  -- The unique boundary differential starts in a zero term, so the lift condition is automatic.
  simpa [ComplexShape.embeddingUpIntGE] using
    (K.isZero_of_isStrictlyGE (-((n + 1 : ℕ) : ℤ)) i' hi).eq_of_src
      (K.d i' ((ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))).f 0))
      0

/-- Helper for Lemma 13.35.7: once the shifted representative is supported in
`[-((n + 1) : ℤ), 0]`, the full brutal left stage is isomorphic to the original complex. -/
noncomputable def shifted_brutal_full_stage_iso_of_isStrictlyGE
    (K : CochainComplex A ℤ) (n : ℕ)
    [K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ))] :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))) ≅ K := by
  let e : ComplexShape.Embedding (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))
  let π : K ⟶ K.stupidTrunc e :=
    e.liftExtend (𝟙 (K.restriction e))
      (shifted_brutal_full_stage_hasLift (A := A) K n)
  letI : ∀ i : ℤ, IsIso (π.f i) := by
    intro i
    by_cases hi : ∃ j : ℕ, e.f j = i
    · rcases hi with ⟨j, hj⟩
      -- On the retained degrees, the comparison is the identity on the restricted complex.
      have hId : IsIso ((𝟙 (K.restriction e) : K.restriction e ⟶ K.restriction e).f j) := by
        simpa using (inferInstance : IsIso (𝟙 ((K.restriction e).X j)))
      simpa [π] using
        ((ComplexShape.Embedding.isIso_liftExtend_f_iff
          (e := e) (φ := 𝟙 (K.restriction e))
          (hφ := shifted_brutal_full_stage_hasLift (A := A) K n)
          (i := j) (i' := i) hj)).2 hId
    · have hnot : ∀ j : ℕ, e.f j ≠ i := by
        intro j hj
        exact hi ⟨j, hj⟩
      have hi_lt : i < -((n + 1 : ℕ) : ℤ) := by
        simpa [e] using
          (ComplexShape.notMem_range_embeddingUpIntGE_iff (p := -((n + 1 : ℕ) : ℤ)) i).1 hnot
      have hK : IsZero (K.X i) :=
        K.isZero_of_isStrictlyGE (-((n + 1 : ℕ) : ℤ)) i hi_lt
      have hStage : IsZero ((K.stupidTrunc e).X i) := by
        simpa [HomologicalComplex.stupidTrunc] using (K.restriction e).isZero_extend_X e i hnot
      -- Outside the retained range, both source and target terms are zero.
      exact IsZero.isIso hK hStage (π.f i)
  letI : IsIso π := HomologicalComplex.Hom.isIso_of_components π
  -- Reorient the comparison so the brutal stage is the source-facing object.
  exact (asIso π).symm

/-- Helper for Lemma 13.35.7: the `n`th lower brutal stage of a cochain complex supported on the
left is the stupid truncation that keeps degrees `≥ -n`. -/
abbrev shifted_brutal_left_stage
    (K : CochainComplex A ℤ) (n : ℕ) :
    CochainComplex A ℤ :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ)))

/-- Helper for Lemma 13.35.7: the new leftmost quotient term in the sign-correct brutal
filtration is the single complex in degree `-((n + 1) : ℤ)`. -/
abbrev shifted_brutal_left_stage_single
    (K : CochainComplex A ℤ) (n : ℕ) :
    CochainComplex A ℤ :=
  (CochainComplex.singleFunctor A (-((n + 1 : ℕ) : ℤ))).obj (K.X (-((n + 1 : ℕ) : ℤ)))

/-- Helper for Lemma 13.35.7: on every retained degree of the `n`th lower brutal stage, the
stage term identifies with the original term of `K`. -/
noncomputable def shifted_brutal_left_stage_x_iso
    (K : CochainComplex A ℤ) (n : ℕ) {i : ℤ} (hi : -((n : ℕ) : ℤ) ≤ i) :
    (shifted_brutal_left_stage (A := A) K n).X i ≅ K.X i := by
  let j : ℕ := Int.toNat (i + (n : ℤ))
  have hj : (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))).f j = i := by
    dsimp [j, ComplexShape.embeddingUpIntGE]
    rw [Int.toNat_of_nonneg]
    · omega
    · omega
  -- The degree belongs to the truncation range, so the stage is canonically the original term.
  exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) hj

/-- Helper for Lemma 13.35.7: after identifying the retained degrees with the corresponding terms
of `K`, the differential of the lower brutal stage is the original differential of `K`. -/
lemma shifted_brutal_left_stage_d_via_x_iso
    (K : CochainComplex A ℤ) (n : ℕ) {i j : ℤ}
    (hi : -((n : ℕ) : ℤ) ≤ i) (hj : -((n : ℕ) : ℤ) ≤ j) :
    (shifted_brutal_left_stage_x_iso (A := A) K n hi).inv ≫
      (shifted_brutal_left_stage (A := A) K n).d i j ≫
      (shifted_brutal_left_stage_x_iso (A := A) K n hj).hom =
        K.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))
  let i₀ : ℕ := Int.toNat (i + (n : ℤ))
  let j₀ : ℕ := Int.toNat (j + (n : ℤ))
  have hi₀ : e.f i₀ = i := by
    dsimp [e, i₀, ComplexShape.embeddingUpIntGE]
    rw [Int.toNat_of_nonneg]
    · omega
    · omega
  have hj₀ : e.f j₀ = j := by
    dsimp [e, j₀, ComplexShape.embeddingUpIntGE]
    rw [Int.toNat_of_nonneg]
    · omega
    · omega
  -- First peel off the `extend` isomorphisms, then peel off the `restriction` isomorphisms.
  change (shifted_brutal_left_stage_x_iso (A := A) K n hi).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (shifted_brutal_left_stage_x_iso (A := A) K n hj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [shifted_brutal_left_stage, shifted_brutal_left_stage_x_iso,
    HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.restrictionXIso, e, i₀, j₀, hi₀, hj₀]

/-- Helper for Lemma 13.35.7: the canonical inclusion between consecutive lower brutal stages. -/
noncomputable def shifted_brutal_left_stage_step_sign_corrected
    (K : CochainComplex A ℤ) (n : ℕ) :
    shifted_brutal_left_stage (A := A) K n ⟶ shifted_brutal_left_stage (A := A) K (n + 1) :=
  { f := fun i ↦
      if hi : -((n : ℕ) : ℤ) ≤ i then
        let hi' : -(((n + 1 : ℕ)) : ℤ) ≤ i := by
          omega
        (shifted_brutal_left_stage_x_iso (A := A) K n hi).hom ≫
          (shifted_brutal_left_stage_x_iso (A := A) K (n + 1) hi').inv
      else
        0
    comm' := by
      intro i j hij
      have hij' : i + 1 = j := by
        simpa using hij
      by_cases hi : -((n : ℕ) : ℤ) ≤ i
      · have hj : -((n : ℕ) : ℤ) ≤ j := by
          omega
        have hi' : -(((n + 1 : ℕ)) : ℤ) ≤ i := by
          omega
        have hj' : -(((n + 1 : ℕ)) : ℤ) ≤ j := by
          omega
        -- On shared degrees, both stage differentials identify with the differential of `K`.
        apply (cancel_mono (shifted_brutal_left_stage_x_iso (A := A) K (n + 1) hj').hom).1
        apply (cancel_epi (shifted_brutal_left_stage_x_iso (A := A) K n hi).inv).1
        rw [dif_pos hi, dif_pos hj]
        repeat rw [Category.assoc]
        rw [Iso.inv_hom_id_assoc]
        rw [shifted_brutal_left_stage_d_via_x_iso (A := A) (K := K) (n + 1) hi' hj']
        simpa [Category.assoc] using
          (shifted_brutal_left_stage_d_via_x_iso (A := A) (K := K) n hi hj).symm
      · by_cases hj : -((n : ℕ) : ℤ) ≤ j
        · have hi_lt : i < -((n : ℕ) : ℤ) := by
            omega
          have hzero :
              IsZero ((shifted_brutal_left_stage (A := A) K n).X i) := by
            exact
              (shifted_brutal_left_stage (A := A) K n).isZero_of_isStrictlyGE
                (-((n : ℕ) : ℤ)) i hi_lt
          -- Below the previous cutoff, the source term is zero, so the square is trivial.
          rw [dif_neg hi, zero_comp, dif_pos hj]
          exact hzero.eq_of_src _ _
        · -- Strictly below the shared range, both components of the step map are zero.
          rw [dif_neg hi, dif_neg hj, zero_comp, comp_zero] }

/-- Helper for Lemma 13.35.7: below the old cutoff, the consecutive-stage inclusion is zero in
degree `i`. -/
lemma shifted_brutal_left_stage_step_component_eq_zero
    (K : CochainComplex A ℤ) (n : ℕ) {i : ℤ} (hi : i < -((n : ℕ) : ℤ)) :
    (shifted_brutal_left_stage_step_sign_corrected (A := A) K n).f i = 0 := by
  -- The old stage has no degree-`i` term, so the inclusion vanishes there.
  simpa [shifted_brutal_left_stage_step_sign_corrected, not_le_of_gt hi]

/-- Helper for Lemma 13.35.7: on any degree shared by two consecutive lower brutal stages, the
stage inclusion is the identity after both terms are identified with `K.X i`. -/
lemma shifted_brutal_left_stage_step_component_eq_iso
    (K : CochainComplex A ℤ) (n : ℕ) {i : ℤ} (hi : -((n : ℕ) : ℤ) ≤ i) :
    (shifted_brutal_left_stage_step_sign_corrected (A := A) K n).f i =
      (shifted_brutal_left_stage_x_iso (A := A) K n hi).hom ≫
        (shifted_brutal_left_stage_x_iso (A := A) K (n + 1) (by omega)).inv := by
  -- On shared degrees, the inclusion is transported from the identity on `K.X i`.
  simpa [shifted_brutal_left_stage_step_sign_corrected, hi]

/-- Helper for Lemma 13.35.7: the projection from the next lower brutal stage to its new
leftmost single term. -/
noncomputable def shifted_brutal_left_stage_to_single_sign_corrected
    (K : CochainComplex A ℤ) (n : ℕ) :
    shifted_brutal_left_stage (A := A) K (n + 1) ⟶ shifted_brutal_left_stage_single (A := A) K n :=
  HomologicalComplex.mkHomToSingle
    ((shifted_brutal_left_stage_x_iso (A := A) K (n + 1)
      (i := -((n + 1 : ℕ) : ℤ)) (by simp)).hom)
    (fun i hi ↦ by
      have hi' : i < -((n + 1 : ℕ) : ℤ) := by
        have : i + 1 = -((n + 1 : ℕ) : ℤ) := by
          simpa using hi
        omega
      have hzero :
          IsZero ((shifted_brutal_left_stage (A := A) K (n + 1)).X i) := by
        exact
          (shifted_brutal_left_stage (A := A) K (n + 1)).isZero_of_isStrictlyGE
            (-((n + 1 : ℕ) : ℤ)) i hi'
      -- The boundary source lies below the new cutoff, so the projection condition is automatic.
      exact hzero.eq_of_src _ _)

/-- Helper for Lemma 13.35.7: away from the new cutoff degree, the quotient projection to the
single complex vanishes. -/
lemma shifted_brutal_left_stage_to_single_component_eq_zero
    (K : CochainComplex A ℤ) (n : ℕ) {i : ℤ}
    (hi : i ≠ -((n + 1 : ℕ) : ℤ)) :
    (shifted_brutal_left_stage_to_single_sign_corrected (A := A) K n).f i = 0 := by
  -- The single target is supported only at its distinguished degree.
  dsimp [shifted_brutal_left_stage_to_single_sign_corrected, HomologicalComplex.mkHomToSingle]
  split_ifs with h
  · exact (False.elim <| hi h)
  · rfl

/-- Helper for Lemma 13.35.7: at the new cutoff degree, the quotient projection is the canonical
identification with `K.X (-(n + 1))`, followed by the self-iso of the single complex. -/
lemma shifted_brutal_left_stage_to_single_component_eq_cutoff
    (K : CochainComplex A ℤ) (n : ℕ) :
    (shifted_brutal_left_stage_to_single_sign_corrected (A := A) K n).f (-((n + 1 : ℕ) : ℤ)) =
      (shifted_brutal_left_stage_x_iso (A := A) K (n + 1)
        (i := -((n + 1 : ℕ) : ℤ)) (by simp)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
          (K.X (-((n + 1 : ℕ) : ℤ)))).inv := by
  -- Evaluate the `mkHomToSingle` constructor at its distinguished degree.
  simp [shifted_brutal_left_stage_to_single_sign_corrected]

/-- Helper for Lemma 13.35.7: the consecutive-stage inclusion followed by the quotient projection
vanishes. -/
lemma shifted_brutal_left_stage_step_comp_to_single_sign_corrected
    (K : CochainComplex A ℤ) (n : ℕ) :
    shifted_brutal_left_stage_step_sign_corrected (A := A) K n ≫
      shifted_brutal_left_stage_to_single_sign_corrected (A := A) K n = 0 := by
  ext i
  by_cases hi : i = -((n + 1 : ℕ) : ℤ)
  · subst hi
    -- At the new cutoff, the old stage has no term, so the first component is zero.
    rw [HomologicalComplex.comp_f,
      shifted_brutal_left_stage_step_component_eq_zero (A := A) (K := K) (n := n)
        (i := -((n + 1 : ℕ) : ℤ)) (by omega),
      zero_comp]
    rfl
  · -- Away from the new cutoff, the projection to the single complex vanishes.
    rw [HomologicalComplex.comp_f,
      shifted_brutal_left_stage_to_single_component_eq_zero (A := A) (K := K) (n := n)
        (i := i) hi,
      comp_zero]
    rfl

/-- Helper for Lemma 13.35.7: the sign-correct consecutive-stage short complex for the lower
brutal filtration of `K`. -/
noncomputable def shifted_brutal_left_stage_short_complex_sign_corrected
    (K : CochainComplex A ℤ) (n : ℕ) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    (shifted_brutal_left_stage_step_sign_corrected (A := A) K n)
    (shifted_brutal_left_stage_to_single_sign_corrected (A := A) K n)
    (shifted_brutal_left_stage_step_comp_to_single_sign_corrected (A := A) K n)

/-- Helper for Lemma 13.35.7: evaluating the sign-correct stage short complex in any degree
produces one of the canonical split shapes `0 ⟶ 0 ⟶ 0`, `0 ⟶ K.X i ⟶ K.X i`, or
`K.X i ⟶ K.X i ⟶ 0`. -/
private noncomputable def shifted_brutal_left_stage_degreewise_splitting
    (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ) :
    ((shifted_brutal_left_stage_short_complex_sign_corrected (A := A) K n).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting := by
  let S : ShortComplex A :=
    (shifted_brutal_left_stage_short_complex_sign_corrected (A := A) K n).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
  by_cases hi_lt : i < -((n + 1 : ℕ) : ℤ)
  · change S.Splitting
    have hX₁ : IsZero S.X₁ := by
      dsimp [S]
      exact
        (shifted_brutal_left_stage (A := A) K n).isZero_of_isStrictlyGE
          (-((n : ℕ) : ℤ)) i (by omega)
    have hX₂ : IsZero S.X₂ := by
      dsimp [S]
      exact
        (shifted_brutal_left_stage (A := A) K (n + 1)).isZero_of_isStrictlyGE
          (-((n + 1 : ℕ) : ℤ)) i hi_lt
    have hX₃ : IsZero S.X₃ := by
      dsimp [S, shifted_brutal_left_stage_single]
      exact
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
          (K.X (-((n + 1 : ℕ) : ℤ))) i (by omega)
    have hg : IsIso S.g := by
      dsimp [S, shifted_brutal_left_stage_short_complex_sign_corrected]
      rw [shifted_brutal_left_stage_to_single_component_eq_zero (A := A) (K := K) (n := n)
        (i := i) (by omega)]
      exact hX₂.isIso hX₃ 0
    -- Strictly below the new cutoff, everything is zero.
    exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
  · by_cases hi_eq : i = -((n + 1 : ℕ) : ℤ)
    · subst hi_eq
      change S.Splitting
      have hX₁ : IsZero S.X₁ := by
        dsimp [S]
        exact
          (shifted_brutal_left_stage (A := A) K n).isZero_of_isStrictlyGE
            (-((n : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
      have hg : IsIso S.g := by
        dsimp [S, shifted_brutal_left_stage_short_complex_sign_corrected]
        have hcut :
            (shifted_brutal_left_stage_to_single_sign_corrected (A := A) K n).f
                (-((n + 1 : ℕ) : ℤ)) =
              (shifted_brutal_left_stage_x_iso (A := A) K (n + 1)
                (i := -((n + 1 : ℕ) : ℤ)) (by simp)).hom ≫
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
                  (K.X (-((n + 1 : ℕ) : ℤ)))).inv := by
          exact shifted_brutal_left_stage_to_single_component_eq_cutoff
            (A := A) (K := K) (n := n)
        have hnorm : (-(↑n + 1) : ℤ) = -((n + 1 : ℕ) : ℤ) := by
          norm_num
        rw [hnorm, hcut]
        haveI :
            IsIso
              ((shifted_brutal_left_stage_x_iso (A := A) K (n + 1)
                (i := -((n + 1 : ℕ) : ℤ)) (by simp)).hom) := by
          infer_instance
        exact IsIso.comp_isIso
      -- At the new cutoff, the short complex is `0 ⟶ K.X i ⟶ K.X i`.
      exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
    · change S.Splitting
      have hi_ge : -((n : ℕ) : ℤ) ≤ i := by
        omega
      have hX₃ : IsZero S.X₃ := by
        dsimp [S, shifted_brutal_left_stage_single]
        exact
          HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
            (K.X (-((n + 1 : ℕ) : ℤ))) i hi_eq
      have hf : IsIso S.f := by
        dsimp [S, shifted_brutal_left_stage_short_complex_sign_corrected]
        rw [shifted_brutal_left_stage_step_component_eq_iso (A := A) (K := K) (n := n)
          (i := i) hi_ge]
        infer_instance
      -- Above the new cutoff, the quotient term vanishes and the inclusion is an isomorphism.
      exact ShortComplex.Splitting.ofIsIsoOfIsZero S hf hX₃

/-- Helper for Lemma 13.35.7: the sign-correct consecutive-stage short complex is short exact. -/
lemma shifted_brutal_left_stage_short_exact_sign_corrected
    (K : CochainComplex A ℤ) (n : ℕ) :
    (shifted_brutal_left_stage_short_complex_sign_corrected (A := A) K n).ShortExact := by
  -- Evaluate degreewise and use the canonical splittings in the three cutoff regimes.
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i ↦
      (shifted_brutal_left_stage_degreewise_splitting (A := A) K n i).shortExact)

/-- Helper for Lemma 13.35.7: after shifting back by `-b`, the new quotient term of the brutal
stage sequence identifies with the single object in degree `a`. -/
noncomputable def shifted_brutal_single_shift_back_iso
    {L : CochainComplex A ℤ} {a b : ℤ} {n : ℕ}
    (hn : Int.toNat (b - a) = n + 1) :
    Q.obj ((shifted_brutal_left_stage_single (A := A) (L⟦b⟧) n)⟦-b⟧) ≅
      (singleFunctor A a).obj (L.X a) := by
  have hab : a ≤ b := by
    by_contra hab
    have hnonpos : b - a ≤ 0 := by omega
    rw [Int.toNat_of_nonpos hnonpos] at hn
    omega
  have hwidth : b - a = ((n + 1 : ℕ) : ℤ) := by
    rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
  have ha : a = b - ((n + 1 : ℕ) : ℤ) := by omega
  let eShift :
      ((shifted_brutal_left_stage_single (A := A) (L⟦b⟧) n)⟦-b⟧) ≅
        (CochainComplex.singleFunctor A a).obj ((L⟦b⟧).X (-((n + 1 : ℕ) : ℤ))) :=
    ((CochainComplex.singleFunctors A).shiftIso (-b) a (-((n + 1 : ℕ) : ℤ)) (by
      omega)).app ((L⟦b⟧).X (-((n + 1 : ℕ) : ℤ)))
  let eTerm :
      ((L⟦b⟧).X (-((n + 1 : ℕ) : ℤ))) ≅ L.X a :=
    L.shiftFunctorObjXIso b (-((n + 1 : ℕ) : ℤ)) a (by
      omega)
  -- First rewrite the shifted single complex on the chain level, then pass to the quotient.
  exact Q.mapIso (eShift ≪≫ (CochainComplex.singleFunctor A a).mapIso eTerm)

/-- Helper for Lemma 13.35.7: shifting back the smaller brutal stage transports the intervalwise
term hypothesis from `L` on `[a, b]` to the shortened interval `[a + 1, b]`. -/
lemma shifted_brutal_stage_shift_back_termwise_mem_sign_corrected
    {L : CochainComplex A ℤ} {a b : ℤ} {n : ℕ}
    (hn : Int.toNat (b - a) = n + 1)
    (hE : ∀ i : Set.Icc a b, E.additiveClosure.retractClosure (L.X i)) :
    ∀ i : Set.Icc (a + 1) b,
      E.additiveClosure.retractClosure
        (((shifted_brutal_left_stage (A := A) (L⟦b⟧) n)⟦-b⟧).X i.1) := by
  have hab : a ≤ b := by
    by_contra hab
    have hnonpos : b - a ≤ 0 := by omega
    rw [Int.toNat_of_nonpos hnonpos] at hn
    omega
  have hwidth : b - a = ((n + 1 : ℕ) : ℤ) := by
    rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
  have ha1 : a + 1 = b - (n : ℤ) := by
    omega
  intro i
  have hi_stage : -((n : ℕ) : ℤ) ≤ i.1 - b := by
    simpa [ha1] using i.2.1
  have hi_nonneg : 0 ≤ i.1 - b + (n : ℤ) := by
    omega
  let eShift :
      (((shifted_brutal_left_stage (A := A) (L⟦b⟧) n)⟦-b⟧).X i.1) ≅
        (shifted_brutal_left_stage (A := A) (L⟦b⟧) n).X (i.1 - b) :=
    (shifted_brutal_left_stage (A := A) (L⟦b⟧) n).shiftFunctorObjXIso (-b) i.1 (i.1 - b) (by
      omega)
  let eStage :
      (shifted_brutal_left_stage (A := A) (L⟦b⟧) n).X (i.1 - b) ≅
        (L⟦b⟧).X (i.1 - b) :=
    (L⟦b⟧).stupidTruncXIso (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) (by
      refine Eq.symm ?_
      dsimp [ComplexShape.embeddingUpIntGE]
      rw [Int.toNat_of_nonneg hi_nonneg]
      omega)
  let eTerm :
      (L⟦b⟧).X (i.1 - b) ≅ L.X i.1 :=
    L.shiftFunctorObjXIso b (i.1 - b) i.1 (by omega)
  -- The shifted-back smaller stage has the same degree-`i` term as `L`, so the ambient
  -- retract-closure hypothesis transports across these canonical isomorphisms.
  exact ((E.additiveClosure.retractClosure).prop_of_iso
    (eTerm.symm ≪≫ eStage.symm ≪≫ eShift.symm)
    (hE ⟨i.1, ⟨le_trans (by omega) i.2.1, i.2.2⟩⟩))

lemma mem_additiveExtensionStage_of_representative_mem_additiveClosure_core :
    ∀ n : ℕ, ∀ {a b : ℤ} (L : CochainComplex A ℤ),
      Int.toNat (b - a) = n →
      L.IsStrictlyGE a →
      L.IsStrictlyLE b →
      (∀ i : Set.Icc a b, E.additiveClosure.retractClosure (L.X i)) →
      additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a))) (Q.obj L) := by
  intro n
  induction n with
  | zero =>
      intro a b L hn hGE hLE hE
      by_cases hab : a ≤ b
      · have hba : b ≤ a := by
          have hsub : b - a = 0 := by
            calc
              b - a = (Int.toNat (b - a) : ℤ) := by
                symm
                exact Int.toNat_of_nonneg (sub_nonneg.mpr hab)
              _ = 0 := by simpa using congrArg (fun m : ℕ ↦ (m : ℤ)) hn
          omega
        have hb_eq : b = a := by omega
        subst b
        -- In width `0`, the representative is concentrated in degree `a`, so it is a single
        -- object in the derived category.
        let e : Q.obj L ≅ (singleFunctor A a).obj (L.X a) :=
          representative_single_iso_of_strict_bounds (A := A) L a
        have hsingle :
            additiveExtensionStage ((E.map single₀)[a, a]) 1
              ((singleFunctor A a).obj (L.X a)) := by
          -- The unique surviving term already lies in stage `1`.
          exact single_mem_stage_one_of_mem_additiveClosure_retractClosure
            (E := E) (a := a) (b := a) ⟨a, by simp⟩ (hE ⟨a, by simp⟩)
        simpa using
          (additiveExtensionStage ((E.map single₀)[a, a]) 1).prop_of_iso e.symm hsingle
      · have hlt : b < a := by omega
        letI : L.IsStrictlyLE b := hLE
        letI : L.IsStrictlyGE a := hGE
        letI : (Q.obj L).IsLE b := by
          rw [DerivedCategory.isLE_Q_obj_iff]
          infer_instance
        letI : (Q.obj L).IsGE a := by
          rw [DerivedCategory.isGE_Q_obj_iff]
          infer_instance
        -- If `b < a`, the representative is zero, hence belongs to every interval stage.
        exact ObjectProperty.prop_of_isZero
          (P := additiveExtensionStage
            ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a))))
          (t.isZero (Q.obj L) b a hlt)
  | succ n ih =>
      intro a b L hn hGE hLE hE
      have hab : a ≤ b := by
        by_contra hab
        have hnonpos : b - a ≤ 0 := by omega
        have : Int.toNat (b - a) = 0 := by
          rw [Int.toNat_of_nonpos hnonpos]
        omega
      have hwidth : b - a = ((n + 1 : ℕ) : ℤ) := by
        rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
        exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
      have ha : a = b - ((n + 1 : ℕ) : ℤ) := by
        omega
      have ha1 : a + 1 = b - (n : ℤ) := by
        omega
      have hn' : Int.toNat (b - (a + 1)) = n := by
        rw [show b - (a + 1) = (n : ℤ) by omega]
        simp
      let K : CochainComplex A ℤ := L⟦b⟧
      let L1 : CochainComplex A ℤ := (shifted_brutal_left_stage (A := A) K n)⟦-b⟧
      have hKGE : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := by
        simpa [K] using
          shifted_representative_isStrictlyGE_left_endpoint (A := A) (L := L) (a := a)
            (b := b) (n := n) hn hGE
      have hKLE : K.IsStrictlyLE 0 := by
        simpa [K] using
          shifted_representative_isStrictlyLE_zero (A := A) (L := L) (b := b) hLE
      have hL1GE : L1.IsStrictlyGE (a + 1) := by
        letI : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := hKGE
        letI : (shifted_brutal_left_stage (A := A) K n).IsStrictlyGE (-((n : ℕ) : ℤ)) :=
          inferInstance
        simpa [L1, ha1] using
          CochainComplex.isStrictlyGE_shift
            (K := shifted_brutal_left_stage (A := A) K n)
            (-((n : ℕ) : ℤ)) (-b) (a + 1) (by
              omega)
      have hL1LE : L1.IsStrictlyLE b := by
        letI : K.IsStrictlyLE 0 := hKLE
        letI : (shifted_brutal_left_stage (A := A) K n).IsStrictlyLE 0 := inferInstance
        simpa [L1] using
          CochainComplex.isStrictlyLE_shift
            (K := shifted_brutal_left_stage (A := A) K n)
            0 (-b) b (by
              omega)
      have hL1Terms :
          ∀ i : Set.Icc (a + 1) b,
            E.additiveClosure.retractClosure (L1.X i.1) := by
        -- The shifted-back smaller brutal stage agrees termwise with `L` on `[a + 1, b]`.
        simpa [L1] using
          shifted_brutal_stage_shift_back_termwise_mem_sign_corrected
            (A := A) (E := E) (L := L) (a := a) (b := b) (n := n) hn hE
      have hIH :
          additiveExtensionStage ((E.map single₀)[a + 1, b]) (Nat.succPNat n) (Q.obj L1) := by
        -- The induction hypothesis applies to the smaller interval `[a + 1, b]`.
        simpa [hn'] using ih (a := a + 1) (b := b) L1 hn' hL1GE hL1LE hL1Terms
      have hIH' :
          additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat n) (Q.obj L1) := by
        -- Enlarge the left endpoint from `[a + 1, b]` to `[a, b]`.
        exact additiveExtensionStage_monotone
          (shiftInterval_mono_lower (P := E.map single₀) (a + 1) b a (by omega))
          (Nat.succPNat n) _ hIH
      have hsingle :
          additiveExtensionStage ((E.map single₀)[a, b]) 1
            ((singleFunctor A a).obj (L.X a)) := by
        -- The leftmost term of the shortened interval contributes the new stage-`1` factor.
        exact single_mem_stage_one_of_mem_additiveClosure_retractClosure
          (E := E) (a := a) (b := b) ⟨a, ⟨le_rfl, hab⟩⟩ (hE ⟨a, ⟨le_rfl, hab⟩⟩)
      let S :=
        (shifted_brutal_left_stage_short_complex_sign_corrected (A := A) K n).map
          (shiftFunctor (CochainComplex A ℤ) (-b))
      have hS :
          S.ShortExact := by
        -- The remaining chain-level input is the short exactness of the sign-correct brutal
        -- stage sequence, transported by the shift functor.
        exact
          (shifted_brutal_left_stage_short_exact_sign_corrected (A := A) K n).map_of_exact
            (shiftFunctor (CochainComplex A ℤ) (-b))
      let eMid :
          Q.obj S.X₂ ≅ Q.obj L := by
        let eStage :
            S.X₂ ≅ L := by
          dsimp [S, L1, K, shifted_brutal_left_stage_short_complex_sign_corrected]
          exact
            ((shiftFunctor (CochainComplex A ℤ) (-b)).mapIso
              (shifted_brutal_full_stage_iso_of_isStrictlyGE (A := A) K n)).trans
              (shiftShiftNeg L b)
        exact Q.mapIso eStage
      have hquot :
          additiveExtensionStage ((E.map single₀)[a, b]) 1 (Q.obj S.X₃) := by
        let eQuot :
            Q.obj S.X₃ ≅ (singleFunctor A a).obj (L.X a) := by
          dsimp [S, K, shifted_brutal_left_stage_short_complex_sign_corrected]
          exact shifted_brutal_single_shift_back_iso
            (A := A) (L := L) (a := a) (b := b) (n := n) hn
        exact
          (additiveExtensionStage ((E.map single₀)[a, b]) 1).prop_of_iso eQuot.symm hsingle
      have hExt :
          ObjectProperty.extensionProduct
            (additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat n))
            (additiveExtensionStage ((E.map single₀)[a, b]) 1)
            (Q.obj S.X₂) := by
        rw [extensionProduct_iff]
        -- The shifted short exact sequence yields the required distinguished triangle.
        exact ⟨Q.obj S.X₁, Q.obj S.X₃, Q.map S.f, Q.map S.g, DerivedCategory.triangleOfSESδ hS,
          DerivedCategory.triangleOfSES_distinguished hS, by simpa [S, L1] using hIH', hquot⟩
      have hMid :
          additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat (n + 1)) (Q.obj S.X₂) := by
        rw [show Nat.succPNat (n + 1) = Nat.succPNat n + 1 by rfl]
        rw [additiveExtensionStage_add]
        exact le_retractClosure _ _ hExt
      -- Replace the middle brutal stage by the original representative using the full-stage iso.
      have hFinal :
          additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat (n + 1)) (Q.obj L) := by
        exact
        (additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat (n + 1))).prop_of_iso
          eMid hMid
      simpa [hn] using hFinal

-- Proof sketch: represent `K` by a bounded cochain complex `L`, filter `L` by stupid
-- truncations, and identify the successive quotients with shifts of the terms `L.X i`; then apply
-- Lemma `13.35.4` to iterate the extension construction.
/-- Lemma 13.35.7 (3): if `K` is represented by a cochain complex supported on `[a, b]` whose
terms in degrees `i ∈ [a, b]` belong to `E`, then `K` lies in
`smd(add(\mathcal E[a,b])^{\star (b - a + 1)})`, encoded here by the Chapter 13 owner
`additiveExtensionStage
  ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a)))`. -/
theorem mem_additiveExtensionStage_of_exists_representative_mem
    (hK :
      ∃ (L : CochainComplex A ℤ) (e : Q.obj L ≅ K),
        L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧ ∀ i : Set.Icc a b, E (L.X i)) :
    intervalStage K := by
  rcases hK with ⟨L, e, hGE, hLE, hE⟩
  have hL :
      additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a))) (Q.obj L) := by
    exact mem_additiveExtensionStage_of_representative_mem_additiveClosure_core
      (E := E) (a := a) (n := Int.toNat (b - a)) (b := b) L rfl hGE hLE
      (fun i ↦ mem_additiveClosure_retractClosure_of_mem (E := E) (hE i))
  exact (intervalStage).prop_of_iso e hL

-- Proof sketch: argue as in clause `(3)`, replacing the termwise hypothesis `L.X i ∈ E` by
-- membership in `smd(add(E))`; each graded piece already lies in the additive closure generated by
-- the shifts of `E`, so the same truncation induction applies.
/-- Lemma 13.35.7 (4): if `K` is represented by a cochain complex supported on `[a, b]` whose
terms in degrees `i ∈ [a, b]` belong to `smd(add(\mathcal E))`, encoded here by
`E.additiveClosure.retractClosure`, then `K` lies in
`smd(add(\mathcal E[a,b])^{\star (b - a + 1)})`, encoded here by the Chapter 13 owner
`additiveExtensionStage
  ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a)))`. -/
theorem mem_additiveExtensionStage_of_exists_representative_mem_additiveClosure
    (hK :
      ∃ (L : CochainComplex A ℤ) (e : Q.obj L ≅ K),
        L.IsStrictlyGE a ∧
          L.IsStrictlyLE b ∧
            ∀ i : Set.Icc a b, E.additiveClosure.retractClosure (L.X i)) :
    intervalStage K := by
  rcases hK with ⟨L, e, hGE, hLE, hE⟩
  have hL :
      additiveExtensionStage ((E.map single₀)[a, b]) (Nat.succPNat (Int.toNat (b - a))) (Q.obj L) := by
    exact mem_additiveExtensionStage_of_representative_mem_additiveClosure_core
      (E := E) (a := a) (n := Int.toNat (b - a)) (b := b) L rfl hGE hLE hE
  exact (intervalStage).prop_of_iso e hL

end
