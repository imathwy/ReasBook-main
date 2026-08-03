import BauschkeLean.Chap25.Corollary_25_4
import BauschkeLean.Chap21.Corollary_21_20

open Set
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 25.5 packages five textbook regularity alternatives on
  `A.dom - B.dom` implying maximal monotonicity of `A + B`.
- `core/canonical`: the reusable owner conclusion is `Maximal IsMonotone (A + B)`, routed
  through the stronger source-facing Chapter 25 corollary
  `Maximal.add_of_cone_dom_sub_eq_span`.
- `bridge/view`: the textbook alternatives stay on the corollary surface, while the local bridge
  theorem below isolates their derived `sri` consequence and then upgrades it to the
  `cone = span` hypothesis expected by Corollary 25.4.
Semantic recall: `lean_leansearch` did not return a relevant maximal-monotonicity sum theorem for
this item, so the owner/API choice was verified locally against `Chap06/Proposition_6_19.lean`,
`Chap15/Proposition_15_5.lean`, `Chap21/Proposition_21_12.lean`, and
`Chap25/Theorem_25_2.lean`.

Primitive data: `A`, `B`, `hA`, `hB`, and the five raw source alternatives.
Derived API: the intermediate `sri` regularity on `A.dom - B.dom`, and then maximal
monotonicity of `A + B`.

Branch `(v)` is recorded only by its mathematically operative `sri` content on the public
surface: the extra convexity conjuncts from the textbook wording are redundant once the local
bridge upgrades `0 ∈ sri (A.dom - B.dom)` to the `cone = span` hypothesis used by Corollary
25.4. -/

/-- Helper for Corollary 25.5: maximal monotonicity forces the graph to be nonempty. -/
private theorem graphNonemptyOfMaximal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : SetValuedOperator E E} (hT : Maximal IsMonotone T) :
    (gra T).Nonempty := by
  -- Compare `T` with the zero operator; emptiness would contradict maximality at the origin.
  by_contra hT_graph
  let Z : SetValuedOperator E E := fun _ ↦ ({0} : Set E)
  have hZ_mono : Z.IsMonotone := by
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hu hv
    simp [Z] at hu hv
    subst u
    subst v
    simp
  have hTZ : T ≤ Z := by
    intro x u hu
    have hmem : (x, u) ∈ gra T := by
      simpa [SetValuedOperator.mem_graph] using hu
    exact (hT_graph ⟨(x, u), hmem⟩).elim
  have hzero_mem : 0 ∈ T 0 := (hT.2 hZ_mono hTZ 0) (by simp [Z])
  have hmem_zero : (0, 0) ∈ gra T := by
    simpa [SetValuedOperator.mem_graph] using hzero_mem
  exact hT_graph ⟨(0, 0), hmem_zero⟩

/-- Helper for Corollary 25.5: the projected Fitzpatrick domain is convex for a maximally
monotone operator. -/
private theorem convexFstImageDomFitzpatrickOfMaximal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : SetValuedOperator E E) (hT : Maximal IsMonotone T) :
    Convex ℝ T.fstImageDomFitzpatrick := by
  have hT_graph : (gra T).Nonempty := graphNonemptyOfMaximal hT
  have hT_mono : T.IsMonotone := Maximal.isMonotone hT
  let FT : E × E → Set.Ioi (⊥ : EReal) :=
    properIoi (F[T])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone T hT_graph hT_mono)
  have hFT : FT ∈ Γ₀(E × E) := by
    -- Package the Fitzpatrick owner through the canonical `Γ₀` interface before projecting.
    simpa [FT] using fitzpatrickFunction_mem_gammaZero T hT_graph hT_mono
  -- The first-coordinate image of a convex effective domain is convex.
  simpa [fstImageDomFitzpatrick, FT, ERealFunction.effectiveDomain, ERealFunction.dom] using
    hFT.2.convex_effectiveDomain.linear_image (ContinuousLinearMap.fst ℝ E E).toLinearMap

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 25.5: first-coordinate projection commutes with Minkowski subtraction. -/
private theorem fstImageSub_eq_sub_fstImage {S T : Set (H × H)} :
    Prod.fst '' (S - T) = (Prod.fst '' S) - (Prod.fst '' T) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases Set.mem_sub.mp hp with ⟨s, hs, t, ht, hst⟩
    refine Set.mem_sub.mpr ⟨s.1, ⟨s, hs, rfl⟩, t.1, ⟨t, ht, rfl⟩, ?_⟩
    simpa using congrArg Prod.fst hst
  · intro hx
    rcases Set.mem_sub.mp hx with ⟨xs, hs, xt, ht, hxt⟩
    rcases hs with ⟨s, hs, rfl⟩
    rcases ht with ⟨t, ht, rfl⟩
    refine ⟨s - t, Set.mem_sub.mpr ⟨s, hs, t, ht, rfl⟩, ?_⟩
    simpa using hxt

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 25.5: a common point of `A` and `interior B` translates an interior
neighborhood of the origin into `A - B`. -/
private theorem zeroMemInterior_sub_of_mem_left_mem_interior_right {A B : Set H} {y : H}
    (hyA : y ∈ A) (hyB : y ∈ interior B) :
    (0 : H) ∈ interior (A - B) := by
  -- Translate a small ball around `y` inside `B` back to a ball around `0` inside `A - B`.
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hyB) with ⟨ε, hε, hball⟩
  have hsubset : Metric.ball (0 : H) ε ⊆ A - B := by
    intro z hz
    refine Set.mem_sub.mpr ?_
    refine ⟨y, hyA, y - z, hball ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, norm_neg] using hz
    · abel
  -- The translated ball certifies that `0` is an interior point of the difference set.
  refine mem_interior_iff_mem_nhds.mpr ?_
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) hε) hsubset

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: an interior neighborhood of the origin already forces
`0 ∈ sri S`. -/
private theorem coneEqUniv_of_zeroMemInterior {S : Set H}
    (h0 : (0 : H) ∈ interior S) :
    cone S = (Set.univ : Set H) := by
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0) with ⟨ε, hε, hball⟩
  ext x
  constructor
  · intro _
    simp
  · intro _
    let r : ℝ := ε / (1 + ‖x‖)
    have hr_pos : 0 < r := by
      dsimp [r]
      positivity
    have hscaled_ball : r • x ∈ Metric.ball (0 : H) ε := by
      have hr_nonneg : 0 ≤ r := hr_pos.le
      have hscaled_lt : ‖r • x‖ < ε := by
        have hfrac_lt_one : ‖x‖ / (1 + ‖x‖) < (1 : ℝ) := by
          have hden_pos : 0 < 1 + ‖x‖ := by positivity
          have hnorm_lt : ‖x‖ < 1 + ‖x‖ := by
            nlinarith [norm_nonneg x]
          exact (div_lt_one hden_pos).2 hnorm_lt
        dsimp [r]
        rw [norm_smul, Real.norm_of_nonneg hr_nonneg]
        calc
          (ε / (1 + ‖x‖)) * ‖x‖ = ε * (‖x‖ / (1 + ‖x‖)) := by ring
          _ < ε * 1 := by
            gcongr
          _ = ε := by ring
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hscaled_lt
    have hscaled_mem : r • x ∈ S := hball hscaled_ball
    have hscaled_cone : r • x ∈ cone S := by
      simpa [Set.cone_def] using (ConvexCone.subset_hull hscaled_mem :
        r • x ∈ (ConvexCone.hull ℝ S : Set H))
    have hx_eq : x = r⁻¹ • (r • x) := by
      calc
        x = (1 : ℝ) • x := by simp
        _ = (r⁻¹ * r) • x := by rw [inv_mul_cancel₀ hr_pos.ne']
        _ = r⁻¹ • (r • x) := by rw [smul_smul]
    exact hx_eq ▸
      ConvexCone.smul_mem (ConvexCone.hull ℝ S) (inv_pos.mpr hr_pos) hscaled_cone

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: once the cone generated by `S` is all of `H`, its linear span is
also all of `H`, so `cone S = span S`. -/
private theorem coneEqSpan_of_coneEqUniv {S : Set H}
    (hcone_univ : cone S = (Set.univ : Set H)) :
    cone S = (Submodule.span ℝ S : Set H) := by
  have hcone_subset_span : cone S ⊆ (Submodule.span ℝ S : Set H) := by
    simpa [Set.cone_def] using
      (ConvexCone.hull_min (C := (Submodule.span ℝ S).toConvexCone)
        (fun x hx ↦ Submodule.subset_span hx))
  have hspan_univ : (Submodule.span ℝ S : Set H) = (Set.univ : Set H) := by
    apply le_antisymm
    · intro x hx
      simp
    · intro x hx
      have hxCone : x ∈ cone S := by simp [hcone_univ]
      exact hcone_subset_span hxCone
  rw [hcone_univ, hspan_univ]

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: if every ray segment from `0` stays in `S` for a short time, then
the cone generated by `S` is all of `H`. -/
private theorem coneEqUniv_of_segmentRegularity {S : Set H}
    (hseg : ∀ x : H, ∃ ε : ℝ, 0 < ε ∧ segment ℝ (0 : H) (ε • x) ⊆ S) :
    cone S = (Set.univ : Set H) := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rcases hseg x with ⟨ε, hε, hεseg⟩
    have hscaled_mem : ε • x ∈ S := hεseg (right_mem_segment ℝ (0 : H) (ε • x))
    have hscaled_cone : ε • x ∈ cone S := by
      simpa [Set.cone_def] using (ConvexCone.subset_hull hscaled_mem :
        ε • x ∈ (ConvexCone.hull ℝ S : Set H))
    have hx_eq : x = ε⁻¹ • (ε • x) := by
      calc
        x = (1 : ℝ) • x := by simp
        _ = (ε⁻¹ * ε) • x := by rw [inv_mul_cancel₀ hε.ne']
        _ = ε⁻¹ • (ε • x) := by rw [smul_smul]
    exact hx_eq ▸
      ConvexCone.smul_mem (ConvexCone.hull ℝ S) (inv_pos.mpr hε) hscaled_cone

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: an interior neighborhood of the origin already forces
`0 ∈ sri S`. -/
private theorem zeroMemSri_of_zeroMemInterior {S : Set H}
    (h0 : (0 : H) ∈ interior S) :
    (0 : H) ∈ sri S := by
  have h0S : (0 : H) ∈ S := interior_subset h0
  have hcone_univ : cone S = (Set.univ : Set H) := coneEqUniv_of_zeroMemInterior h0
  have hclosedSpan_univ :
      ((Submodule.span ℝ S).topologicalClosure : Set H) = (Set.univ : Set H) := by
    apply le_antisymm
    · intro x hx
      simp
    · intro x hx
      have hxCone : x ∈ cone S := by simp [hcone_univ]
      exact cone_subset_topologicalClosure_span S hxCone
  -- At the origin, the translated set is still `S`, so both sides reduce to `univ`.
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨h0S, ?_⟩
  rw [sub_singleton_zero_eq_self]
  rw [hcone_univ, hclosedSpan_univ]

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: if every ray segment from `0` stays in `S` for a short time, then
`0` lies in the strong relative interior of `S`. -/
private theorem zeroMemSri_of_segmentRegularity {S : Set H}
    (hseg : ∀ x : H, ∃ ε : ℝ, 0 < ε ∧ segment ℝ (0 : H) (ε • x) ⊆ S) :
    (0 : H) ∈ sri S := by
  have h0S : (0 : H) ∈ S := by
    rcases hseg 0 with ⟨ε, hε, hεseg⟩
    simpa using hεseg (left_mem_segment ℝ (0 : H) (ε • (0 : H)))
  have hcone_univ : cone S = (Set.univ : Set H) := coneEqUniv_of_segmentRegularity hseg
  have hclosedSpan_univ :
      ((Submodule.span ℝ S).topologicalClosure : Set H) = (Set.univ : Set H) := by
    apply le_antisymm
    · intro x hx
      simp
    · intro x hx
      have hxCone : x ∈ cone S := by simp [hcone_univ]
      exact cone_subset_topologicalClosure_span S hxCone
  -- The segment hypothesis gives `cone S = univ`; then the closed span is also `univ`.
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨h0S, ?_⟩
  rw [sub_singleton_zero_eq_self]
  rw [hcone_univ, hclosedSpan_univ]

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: a strong-relative-interior witness at the origin upgrades to the
source `cone S = span S` criterion. -/
private theorem coneEqSpan_of_zeroMemSri {S : Set H}
    (hsri : (0 : H) ∈ sri S) :
    cone S = (Submodule.span ℝ S : Set H) := by
  have hcone_closedSpan :
      cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
    rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨_, hcone⟩
    simpa [sub_singleton_zero_eq_self] using hcone
  have hcone_subset_span : cone S ⊆ (Submodule.span ℝ S : Set H) := by
    simpa [Set.cone_def] using
      (ConvexCone.hull_min (C := (Submodule.span ℝ S).toConvexCone)
        fun x hx ↦ Submodule.subset_span hx)
  have hclosedSpan_eq_span :
      ((Submodule.span ℝ S).topologicalClosure : Set H) = (Submodule.span ℝ S : Set H) := by
    apply le_antisymm
    · intro x hx
      rw [← hcone_closedSpan] at hx
      exact hcone_subset_span hx
    · exact subset_closure
  rw [hcone_closedSpan, hclosedSpan_eq_span]

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: the five source regularity alternatives all imply
`0 ∈ sri (A.dom - B.dom)`. -/
private theorem zero_mem_sri_dom_sub_of_sumRegularity
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hreg :
      B.dom = (Set.univ : Set H) ∨
        (A.dom ∩ interior B.dom).Nonempty ∨
        (0 : H) ∈ interior (A.dom - B.dom) ∨
        (∀ x : H, ∃ ε : ℝ, 0 < ε ∧ segment ℝ (0 : H) (ε • x) ⊆ A.dom - B.dom) ∨
        (0 : H) ∈ sri (A.dom - B.dom)) :
    (0 : H) ∈ sri (A.dom - B.dom) := by
  -- Route correction: the five textbook branches are only source-facing input data. The real
  -- owner bridge needed downstream is the derived `sri` hypothesis on `A.dom - B.dom`.
  rcases hreg with hBuniv | hreg
  · have hA_dom_nonempty : A.dom.Nonempty := dom_nonempty_of_maximal A hA
    rcases hA_dom_nonempty with ⟨x, hxA⟩
    -- Branch `(i)` immediately produces a point in `A.dom ∩ interior B.dom`.
    have hxInterior : x ∈ interior B.dom := by
      simp [hBuniv]
    exact zeroMemSri_of_zeroMemInterior
      (zeroMemInterior_sub_of_mem_left_mem_interior_right hxA hxInterior)
  rcases hreg with hinter | hreg
  · rcases hinter with ⟨x, hxA, hxInterior⟩
    -- Branch `(ii)` is exactly the translation-to-the-origin interior argument.
    exact zeroMemSri_of_zeroMemInterior
      (zeroMemInterior_sub_of_mem_left_mem_interior_right hxA hxInterior)
  rcases hreg with h0Interior | hreg
  · -- Branch `(iii)` already gives the stronger interior conclusion at the origin.
    exact zeroMemSri_of_zeroMemInterior h0Interior
  rcases hreg with hseg | hsri
  · -- Branch `(iv)` identifies every direction with the cone generated by `A.dom - B.dom`.
    exact zeroMemSri_of_segmentRegularity hseg
  · -- Branch `(v)` is the target `sri` statement itself.
    exact hsri

/-- Helper for Corollary 25.5: a strong-relative-interior witness on `A.dom - B.dom` lifts to the
projected Fitzpatrick-domain difference `A.fstImageDomFitzpatrick - B.fstImageDomFitzpatrick`. -/
private theorem zeroMemSri_fstImageDomFitzpatrickSub_of_zeroMemSriDomSub
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈ sri (A.dom - B.dom)) :
    (0 : H) ∈ sri (A.fstImageDomFitzpatrick - B.fstImageDomFitzpatrick) := by
  have hA_fitz_nonempty : A.fstImageDomFitzpatrick.Nonempty := by
    rcases dom_nonempty_of_maximal A hA with ⟨x, hx⟩
    exact ⟨x, dom_subset_fst_image_dom_fitzpatrick (A := A) hA hx⟩
  have hB_fitz_nonempty : B.fstImageDomFitzpatrick.Nonempty := by
    rcases dom_nonempty_of_maximal B hB with ⟨x, hx⟩
    exact ⟨x, dom_subset_fst_image_dom_fitzpatrick (A := B) hB hx⟩
  have hA_fitz_subset :
      A.fstImageDomFitzpatrick ⊆ closure (convexHull ℝ A.dom) := by
    -- The Chapter 21 bridge first lands in `closure A.dom`, then enlarges to the closed hull.
    intro x hx
    exact closure_mono (subset_convexHull ℝ A.dom)
      (fst_image_dom_fitzpatrick_subset_closure_dom (A := A) hA hx)
  have hB_fitz_subset :
      B.fstImageDomFitzpatrick ⊆ closure (convexHull ℝ B.dom) := by
    -- The same closure control applies to `B`.
    intro x hx
    exact closure_mono (subset_convexHull ℝ B.dom)
      (fst_image_dom_fitzpatrick_subset_closure_dom (A := B) hB hx)
  have hcone :
      cone (A.dom - (ContinuousLinearMap.id ℝ H) '' B.dom) =
        ((Submodule.span ℝ (A.dom - (ContinuousLinearMap.id ℝ H) '' B.dom)).topologicalClosure :
          Set H) := by
    -- At the origin, the defining `sri` cone identity reduces to the source domain difference.
    rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨_, hcone⟩
    simpa [ContinuousLinearMap.id_apply, sub_singleton_zero_eq_self] using hcone
  -- Apply Proposition 6.21 with `L = id` and the domain/Fitzpatrick containments.
  simpa [ContinuousLinearMap.id_apply] using
    (zero_mem_strongRelativeInterior_sub_image_of_subset_closure_convexHull
      (A := B.dom) (B := A.dom)
      (C := B.fstImageDomFitzpatrick) (D := A.fstImageDomFitzpatrick)
      (L := ContinuousLinearMap.id ℝ H)
      hB_fitz_nonempty hA_fitz_nonempty
      (convexFstImageDomFitzpatrickOfMaximal B hB)
      (convexFstImageDomFitzpatrickOfMaximal A hA)
      (dom_subset_fst_image_dom_fitzpatrick (A := B) hB)
      hB_fitz_subset
      (dom_subset_fst_image_dom_fitzpatrick (A := A) hA)
      hA_fitz_subset
      hcone)

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: the projected Fitzpatrick-domain difference is exactly the same
space owner surface `Prod.fst '' (dom (F[A]) - dom (F[B]))`. -/
private theorem zeroMemSri_ownerSurface_of_zeroMemSriFstImageDomFitzpatrickSub
    {A B : SetValuedOperator H H}
    (hsri :
      (0 : H) ∈ sri (A.fstImageDomFitzpatrick - B.fstImageDomFitzpatrick)) :
    (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))) := by
  -- Normalize the projected Fitzpatrick-domain difference to the Chapter 25 owner spelling.
  simpa [fstImageDomFitzpatrick, fstImageSub_eq_sub_fstImage] using hsri

/-- Helper for Corollary 25.5: a strong-relative-interior witness on `A.dom - B.dom` upgrades to
the `cone = span` hypothesis of Corollary 25.4. -/
private theorem maximalAdd_of_zeroMemSriDomSub
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈ sri (A.dom - B.dom)) :
    Maximal IsMonotone (A + B) := by
  have hcone :
      cone (A.dom - B.dom) = (Submodule.span ℝ (A.dom - B.dom) : Set H) :=
    coneEqSpan_of_zeroMemSri hsri
  -- Corollary 25.4 is the already-compiled same-space owner for the `cone = span` surface.
  exact Maximal.add_of_cone_dom_sub_eq_span hA hB hcone

/-- Corollary 25.5: let `A` and `B` be maximally monotone operators from `H → 2^H`. If one of
the five source regularity alternatives holds, namely `dom B = H`, or
`(dom A ∩ interior (dom B)).Nonempty`, or `0 ∈ interior (dom A - dom B)`, or `∀ x, ∃ ε > 0,
segment ℝ (0 : H) (ε • x) ⊆ dom A - dom B`, or `0 ∈ sri (dom A - dom B)`, then `A + B` is
maximally monotone. -/
theorem Maximal.add_of_sumRegularity
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hreg :
      B.dom = (Set.univ : Set H) ∨
        (A.dom ∩ interior B.dom).Nonempty ∨
        (0 : H) ∈ interior (A.dom - B.dom) ∨
        (∀ x : H, ∃ ε : ℝ, 0 < ε ∧ segment ℝ (0 : H) (ε • x) ⊆ A.dom - B.dom) ∨
        (0 : H) ∈ sri (A.dom - B.dom)) :
    Maximal IsMonotone (A + B) := by
  -- First compress the five textbook branches to the single source-side `sri` hypothesis.
  have hsri : (0 : H) ∈ sri (A.dom - B.dom) :=
    zero_mem_sri_dom_sub_of_sumRegularity hA hreg
  -- Then transport that `sri` witness to the projected Fitzpatrick surface and apply Theorem 25.2.
  exact maximalAdd_of_zeroMemSriDomSub hA hB hsri

end

end SetValuedOperator
