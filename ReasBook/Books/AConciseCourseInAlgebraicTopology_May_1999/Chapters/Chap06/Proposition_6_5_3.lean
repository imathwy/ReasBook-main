import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Corollary_6_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Theorem_6_4_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

open CategoryTheory
open scoped ContinuousMap
open scoped unitInterval

universe u

variable {A X Y : Type u}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` is the canonical owner for
-- ordinary homotopy equivalences, while `Under (TopCat.of A)` is the canonical owner for maps
-- under `A`.

/-- Helper for Proposition 6.5.3: the commutative triangle carried by a morphism in
`Under (TopCat.of A)` rewrites to the continuous-map equation `e.toFun.comp i = j`. -/
private theorem homotopyEquivToFun_comp_eq
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom) :
    e.toFun.comp i = j := by
  -- Rewrite the under-category triangle into the corresponding equality of continuous maps.
  have hw : f.right.hom.comp i = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w f)
  simpa [he] using hw

/-- Helper for Proposition 6.5.3: a cofibration adjusts an ordinary map `g₀ : Y ⟶ X` whose
restriction to `A` is homotopic to `i` into an actual morphism under `A`, without changing its
ordinary homotopy class. -/
private theorem existsUnderHom_homotopy_of_isCofibration
    {i : C(A, X)} {j : C(A, Y)}
    (hj : IsCofibration.{u, u, u} j) {g₀ : C(Y, X)}
    (H : (g₀.comp j).Homotopy i) :
    ∃ g :
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
          (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)),
      ∃ G : g₀.Homotopy g.right.hom, ∀ z : I × A, G (z.1, j z.2) = H z := by
  -- Extend the boundary homotopy along `j` and retain the extension formula for later range
  -- calculations.
  obtain ⟨G, F, hF⟩ := hj.exists_homotopy_extension (f₀ := g₀) (g := i) H
  have hGj : G.comp j = i := by
    -- Reading the time-`1` endpoint of the extension recovers the corrected under-triangle.
    ext a
    simpa using hF (1, a)
  refine ⟨Under.homMk (TopCat.ofHom G) ?_, F, hF⟩
  -- Package the corrected endpoint as a morphism in the under category.
  simpa using congrArg TopCat.ofHom hGj

/-- Helper for Proposition 6.5.3: forgetting the detailed extension data from
`existsUnderHom_homotopy_of_isCofibration` recovers the ordinary homotopy class of the corrected
under-map. -/
private theorem existsUnderHom_homotopic_of_isCofibration
    {i : C(A, X)} {j : C(A, Y)}
    (hj : IsCofibration.{u, u, u} j) {g₀ : C(Y, X)}
    (H : (g₀.comp j).Homotopy i) :
    ∃ g :
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
          (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)),
      g₀.Homotopic g.right.hom := by
  -- Discard only the boundary-control witness; the underlying corrected under-map is the same.
  rcases existsUnderHom_homotopy_of_isCofibration hj H with ⟨g, G, _⟩
  exact ⟨g, ⟨G⟩⟩

/-- Helper for Proposition 6.5.3: if `j : A → Y` is a cofibration, then the canonical inclusion
of its image `Set.range j ↪ Y` is also a cofibration. -/
private theorem rangeInclusion_isCofibration_of_isCofibration
    {j : C(A, Y)} (hj : IsCofibration.{u, u, u} j) :
    IsCofibration.{u, u, u} (TopCat.subtypeInclusion (Set.range j)).hom := by
  intro Z _ f₀ g H
  -- Factor `j` through its image so the original HEP applies after precomposition.
  let jRange : C(A, Set.range j) := ⟨Set.rangeFactorization j, j.continuous.rangeFactorization⟩
  rcases hj.exists_homotopy_extension f₀ (g.comp jRange) (H.compContinuousMap jRange) with
    ⟨G, F, hF⟩
  refine ⟨G, F, ?_⟩
  -- Unpack a point of the image as `j a` and reuse the original extension formula.
  intro z
  rcases z with ⟨t, ⟨y, ⟨a, rfl⟩⟩⟩
  simpa [jRange] using hF (t, a)

/-- Helper for Proposition 6.5.3: the endpoint `{1} ⊆ I` is a DR-pair. -/
private theorem oneSingletonIsDRPair : IsDRPair ({1} : Set I) := by
  let control : C(I, I) :=
    { toFun := fun x ↦
        Set.projIcc 0 1 zero_le_one (((1 / 2 : ℝ) * (1 - (x : ℝ))))
      continuous_toFun := by
        exact continuous_projIcc.comp
          (continuous_const.mul (continuous_const.sub continuous_subtype_val)) }
  have hContHomotopyMap :
      Continuous fun p : I × I ↦
        Set.projIcc 0 1 zero_le_one (((p.2 : ℝ) + (1 - (p.2 : ℝ)) * (p.1 : ℝ))) := by
    exact continuous_projIcc.comp <|
      (continuous_subtype_val.comp continuous_snd).add
        ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
          (continuous_subtype_val.comp continuous_fst))
  let retract : C(I, I) := ContinuousMap.const I (1 : I)
  let homotopyMap : C(I × I, I) :=
    { toFun := fun p ↦
        Set.projIcc 0 1 zero_le_one (((p.2 : ℝ) + (1 - (p.2 : ℝ)) * (p.1 : ℝ)))
      continuous_toFun := hContHomotopyMap }
  have hZero : ∀ x : I, homotopyMap (x, 0) = x := by
    -- At time `0`, the affine formula reduces to the identity on `I`.
    intro x
    apply Subtype.ext
    simp [homotopyMap, Set.projIcc_of_mem]
  have hOne : ∀ x : I, homotopyMap (x, 1) = retract x := by
    -- At time `1`, the affine formula reaches the constant endpoint `1`.
    intro x
    apply Subtype.ext
    simp [homotopyMap, retract]
  let homotopy : (ContinuousMap.id I).Homotopy retract :=
    ContinuousMap.Homotopy.ofProdSwap homotopyMap hZero hOne
  have hRel :
      (ContinuousMap.id I).HomotopyRel retract ({1} : Set I) := by
    refine ⟨homotopy, ?_⟩
    -- The affine contraction fixes the endpoint `1` throughout the homotopy.
    intro t x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simp [homotopy, homotopyMap, retract, ContinuousMap.Homotopy.ofProdSwap]
  have hZeroSet : control ⁻¹' ({0} : Set I) = ({1} : Set I) := by
    -- The control map is `(1 - x) / 2`, so it vanishes exactly at `x = 1`.
    ext x
    constructor
    · intro hx
      have hxle : (((1 / 2 : ℝ) * (1 - (x : ℝ)))) ≤ 0 := by
        simpa [control, projIcc_eq_zero] using hx
      have hxReal : (x : ℝ) = 1 := by
        nlinarith [x.2.1, x.2.2, hxle]
      exact Set.mem_singleton_iff.mpr (Subtype.ext hxReal)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp [control]
  have hEndpoint : ∀ x : I, control x < 1 → retract x ∈ ({1} : Set I) := by
    -- The endpoint map is constantly `1`, so the DR target condition is automatic.
    intro x hx
    simp [retract]
  have hControlLtOne : ∀ x : I, control x < 1 := by
    -- The control values lie in `[0, 1 / 2]`, hence are strictly below `1`.
    intro x
    have hmem :
        (((1 / 2 : ℝ) * (1 - (x : ℝ)))) ∈ I := by
      constructor
      · nlinarith [x.2.2]
      · nlinarith [x.2.1]
    have hx : (((1 / 2 : ℝ) * (1 - (x : ℝ)))) < 1 := by
      nlinarith [x.2.1]
    change Set.projIcc 0 1 zero_le_one (((1 / 2 : ℝ) * (1 - (x : ℝ)))) < (1 : I)
    rw [Set.projIcc_of_mem _ hmem]
    simpa using hx
  exact ⟨{
    control := control
    retract := retract
    homotopy := hRel
    zeroSet_eq := hZeroSet
    endpoint_mem := hEndpoint
    control_lt_one := hControlLtOne }⟩

/-- Helper for Proposition 6.5.3: a homotopy relative to `Set.range j` between endomorphisms of
`Y` upgrades to a homotopy under `A` between the corresponding endomorphisms of `Under.mk j`. -/
private theorem homotopicUnder_of_homotopicRelRange
    {j : C(A, Y)}
    {u₀ u₁ :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A))}
    (h : u₀.right.hom.HomotopicRel u₁.right.hom (Set.range j)) :
    HomotopicUnder u₀ u₁ := by
  refine ⟨{ toHomotopy := h.some.toHomotopy, prop' := ?_ }⟩
  intro t
  -- Relative-to-range means every stage fixes the image of `j`, hence each stage is again under
  -- `A`.
  ext a
  have hu₀ : u₀.right.hom.comp j = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w u₀)
  calc
    ((h.some.toHomotopy.curry t).comp j) a = h.some (t, j a) := rfl
    _ = u₀.right.hom (j a) := by
      exact h.some.eq_fst t ⟨a, rfl⟩
    _ = j a := by
      simpa using ContinuousMap.congr_fun hu₀ a

/-- Helper for Proposition 6.5.3: the loop `H.symm.trans H` contracts relative to the boundary
`({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopySymmTransHomotopicRelRefl
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ : C(T, Z)}
    (H : r₀.Homotopy r₁) :
    (H.symm.trans H).toContinuousMap.HomotopicRel
      ((ContinuousMap.Homotopy.refl r₁).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  let loopParam : I × I → I := fun st ↦
    ⟨1 - Path.Homotopy.reflTransSymmAux (σ st.1, st.2), by
      have hmem := Path.Homotopy.reflTransSymmAux_mem_I (σ st.1, st.2)
      constructor
      · linarith [hmem.2]
      · linarith [hmem.1]⟩
  refine ⟨{
      toHomotopy :=
        { toFun := fun sx ↦ H (loopParam (sx.1, sx.2.1), sx.2.2)
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            change H (loopParam (0, t), x) = (H.symm.trans H) (t, x)
            rw [ContinuousMap.Homotopy.trans_apply]
            split_ifs with ht
            · have hParam :
                loopParam (0, t) =
                  σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ := by
                apply Subtype.ext
                have ht' : (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 1 - 2 * (t : ℝ)
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) =
                    1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_pos ht']
              exact congrArg (fun u : I ↦ H (u, x)) hParam
            · have hParam :
                loopParam (0, t) = ⟨2 * t - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
                apply Subtype.ext
                have ht' : ¬ (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 2 * (t : ℝ) - 1
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) =
                    1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_neg ht']
                ring
              exact congrArg (fun u : I ↦ H (u, x)) hParam
          map_one_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            simp [loopParam, Path.Homotopy.reflTransSymmAux] }
      prop' := ?_ }⟩
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]

/-- Helper for Proposition 6.5.3: on `A`, the left-composite ordinary homotopy built from the
corrected inverse is the self-canceling loop `hInverseOnA.symm.trans hInverseOnA`. -/
private theorem leftCompositeRestrictionEq
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    {g :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A))}
    (hg : e.symm.toFun.Homotopy g.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    (hLeftInvOnA :
      (e.left_inv.some.compContinuousMap i).toContinuousMap = hInverseOnA.toContinuousMap)
    (hLift : ∀ z : I × A, hg (z.1, j z.2) = hInverseOnA z) :
    let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.right.hom.comp e.toFun) :=
      ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
    let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).right.hom :=
      FfgRaw.cast rfl (by
        ext x
        rw [he]
        rfl)
    ((Ffg.symm.trans e.left_inv.some).toContinuousMap).comp ((ContinuousMap.id I).prodMap i) =
      (hInverseOnA.symm.trans hInverseOnA).toContinuousMap := by
  let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.right.hom.comp e.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
  let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).right.hom :=
    FfgRaw.cast rfl (by
      ext x
      rw [he]
      rfl)
  have hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  have hFfg :
      Ffg.toContinuousMap.comp ((ContinuousMap.id I).prodMap i) = hInverseOnA.toContinuousMap := by
    -- Restricting the corrected inverse homotopy to `A` recovers the chosen lifted inverse
    -- homotopy.
    ext z
    rcases z with ⟨t, a⟩
    calc
      Ffg (t, i a) = hg (t, e.toFun (i a)) := by
        rfl
      _ = hg (t, j a) := by
        rw [show e.toFun (i a) = j a by
          simpa using ContinuousMap.congr_fun hcomp a]
      _ = hInverseOnA (t, a) := hLift (t, a)
  have hLeftInvOnA_apply :
      ∀ z : I × A, e.left_inv.some (z.1, i z.2) = hInverseOnA z := by
    -- The chosen left-inverse homotopy on `A` is definitionally the one used in the main proof.
    intro z
    exact ContinuousMap.congr_fun hLeftInvOnA z
  -- Compare the restricted left composite pointwise with the normalized self-canceling loop.
  ext z
  rcases z with ⟨t, a⟩
  change (Ffg.symm.trans e.left_inv.some) (t, i a) = (hInverseOnA.symm.trans hInverseOnA) (t, a)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hFfg
        (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
  · simpa using
      hLeftInvOnA_apply
        (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, a)

/-- Helper for Proposition 6.5.3: on `A`, the left-composite ordinary homotopy built from the
corrected inverse is homotopic rel boundary to the constant homotopy at `i`. -/
private theorem leftCompositeRestriction_homotopicRelRefl
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    {g :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A))}
    (hg : e.symm.toFun.Homotopy g.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    (hLeftInvOnA :
      (e.left_inv.some.compContinuousMap i).toContinuousMap = hInverseOnA.toContinuousMap)
    (hLift : ∀ z : I × A, hg (z.1, j z.2) = hInverseOnA z) :
    let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.right.hom.comp e.toFun) :=
      ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
    let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).right.hom :=
      FfgRaw.cast rfl (by
        ext x
        rw [he]
        rfl)
    ((((Ffg.symm.trans e.left_inv.some).toContinuousMap).comp
        ((ContinuousMap.id I).prodMap i))).HomotopicRel
      ((ContinuousMap.Homotopy.refl i).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
  let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.right.hom.comp e.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
  let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).right.hom :=
    FfgRaw.cast rfl (by
      ext x
      rw [he]
      rfl)
  have hRestriction :
      ((Ffg.symm.trans e.left_inv.some).toContinuousMap).comp ((ContinuousMap.id I).prodMap i) =
        (hInverseOnA.symm.trans hInverseOnA).toContinuousMap := by
    -- Normalize the restricted composite once, so the remaining step is the standard loop
    -- contraction.
    simpa [FfgRaw, Ffg] using
      leftCompositeRestrictionEq f e he hg hInverseOnA hLeftInvOnA hLift
  -- After normalization, contract the self-canceling loop relative to the boundary.
  rcases homotopySymmTransHomotopicRelRefl hInverseOnA with ⟨hrel⟩
  exact ⟨hrel.cast hRestriction.symm rfl⟩

/-- Helper for Proposition 6.5.3: an ordinary homotopy between endomorphisms of `Y` that both fix
`Set.range j` should be rectified to a homotopy relative to `Set.range j`. -/
private theorem comp_rangeInclusion_eq_rangeInclusion_of_comp_eq
    {j : C(A, Y)} {u : C(Y, Y)} (hu : u.comp j = j) :
    u.comp (TopCat.subtypeInclusion (Set.range j)).hom =
      (TopCat.subtypeInclusion (Set.range j)).hom := by
  -- Rephrase the endpoint condition on `j` as the pointwise fixedness needed on the image
  -- inclusion.
  ext z
  rcases z with ⟨y, ⟨a, rfl⟩⟩
  simpa using ContinuousMap.congr_fun hu a

/-- Helper for Proposition 6.5.3: a path family on `Y` that is constant on `S` assembles into a
homotopy relative to `S`. -/
private theorem homotopyRelOfConstPathFamily
    {S : Set Y} {u₀ u₁ : C(Y, Y)} {D : C(Y, C(I, Y))}
    (h₀ : (pathSpaceEvalAt 0 Y).comp D = u₀)
    (h₁ : (pathSpaceEvalAt 1 Y).comp D = u₁)
    (hconst : ∀ y ∈ S, D y = ContinuousMap.const I (u₀ y)) :
    u₀.HomotopicRel u₁ S := by
  refine ⟨{ toHomotopy := ContinuousMap.Homotopy.ofPathSpaceMap D h₀ h₁, prop' := ?_ }⟩
  intro t y hy
  -- On the distinguished subset, the path family is constant, so every time slice agrees with
  -- the initial map.
  have hDy : D y t = u₀ y := by
    simpa using ContinuousMap.congr_fun (hconst y hy) t
  simpa [ContinuousMap.Homotopy.ofPathSpaceMap_apply] using hDy

/-- Helper for Proposition 6.5.3: if an ordinary homotopy between endomorphisms of `Y` contracts
to the constant homotopy after restricting along `j`, then the two endomorphisms are homotopic
under `A`. -/
private theorem homotopicUnder_of_restrictedContraction
    {j : C(A, Y)} (hj : IsCofibration.{u, u, u} j)
    {u₀ u₁ :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A))}
    (F : u₀.right.hom.Homotopy u₁.right.hom)
    (hFrel :
      (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)).HomotopicRel
        ((ContinuousMap.Homotopy.refl j).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A))) :
    HomotopicUnder u₀ u₁ := by
  -- Route correction: instead of trying to read `HomotopicUnder` directly from the relative
  -- contraction on `I × A`, first rebracket that contraction into a homotopy of maps
  -- `A → C(I, Y)` and then extend it across `j` in the path-space codomain.
  have hu₀ : u₀.right.hom.comp j = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w u₀)
  have hu₁ : u₁.right.hom.comp j = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w u₁)
  rcases hFrel with ⟨hFrel⟩
  let rawK : C((I × A) × I, Y) :=
    { toFun := fun sat ↦ hFrel.toHomotopy (sat.1.1, (sat.2, sat.1.2))
      continuous_toFun := by
        -- Repackage the restricted contraction by viewing the original `I × (I × A)`
        -- coordinates as `((s, a), t)`.
        have hcoord : Continuous fun sat : (I × A) × I ↦ (sat.1.1, (sat.2, sat.1.2)) := by
          fun_prop
        simpa using hFrel.toHomotopy.continuous.comp hcoord }
  let K :
      (F.toPathSpaceMap.comp j).Homotopy ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) :=
    { toContinuousMap := rawK.curry
      map_zero_left := by
        intro a
        -- At the outer time `0`, the rebracketed path-space homotopy recovers the original path
        -- family `F.toPathSpaceMap.comp j`.
        ext t
        calc
          rawK.curry (0, a) t = hFrel.toHomotopy (0, (t, a)) := rfl
          _ = (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (t, a) := by
            exact hFrel.toHomotopy.apply_zero (t, a)
          _ = (F.toPathSpaceMap.comp j) a t := rfl
      map_one_left := by
        intro a
        -- At the outer time `1`, the same rebracketing gives the constant-path family on `j`.
        ext t
        calc
          rawK.curry (1, a) t = ((ContinuousMap.Homotopy.refl j).toContinuousMap) (t, a) := by
            change
              hFrel.toHomotopy (1, (t, a)) =
                ((ContinuousMap.Homotopy.refl j).toContinuousMap) (t, a)
            exact hFrel.toHomotopy.apply_one (t, a)
          _ = ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) a t := rfl }
  obtain ⟨G, L, hL⟩ := hj.exists_homotopy_extension
    (f₀ := F.toPathSpaceMap) (g := (ContinuousMap.Homotopy.refl j).toPathSpaceMap) K
  have hGj : G.comp j = (ContinuousMap.Homotopy.refl j).toPathSpaceMap := by
    -- The lifted path family ends at the constant-path family on `j`.
    ext a t
    calc
      G (j a) t = L (1, j a) t := by
        simpa using congrArg (fun γ : C(I, Y) => γ t) (L.apply_one (j a)).symm
      _ = K (1, a) t := by
        simpa using ContinuousMap.congr_fun (hL (1, a)) t
      _ = ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) a t := by
        simpa using ContinuousMap.congr_fun (K.apply_one a) t
  let v₀ :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) :=
    Under.homMk (TopCat.ofHom ((pathSpaceEvalAt 0 Y).comp G)) (by
      -- Every initial point of the extended path family is still a map under `A`.
      simpa using congrArg TopCat.ofHom (by
        ext a
        exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGj a) 0))
  let v₁ :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) :=
    Under.homMk (TopCat.ofHom ((pathSpaceEvalAt 1 Y).comp G)) (by
      -- The terminal endpoints of the same family also remain under `A`.
      simpa using congrArg TopCat.ofHom (by
        ext a
        exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGj a) 1))
  let sourceFaceRaw :
      ((pathSpaceEvalAt 0 Y).comp F.toPathSpaceMap).Homotopy ((pathSpaceEvalAt 0 Y).comp G) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl (pathSpaceEvalAt 0 Y)) L
  let sourceFace : u₀.right.hom.Homotopy v₀.right.hom :=
    sourceFaceRaw.cast F.pathSpaceEvalAtZero_comp_toPathSpaceMap rfl
  have hSourceFace : HomotopicUnder u₀ v₀ := by
    refine ⟨{ toHomotopy := sourceFace, prop' := ?_ }⟩
    intro s
    -- The `t = 0` face stays under `A` because the lifted comparison preserves the `0`-endpoint
    -- of each path over the restriction.
    ext a
    change (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp j) a = j a
    have hBoundary0 :
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (0, a) = j a := by
      calc
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (0, a) = F (0, j a) := rfl
        _ = u₀.right.hom (j a) := by
          simpa using F.apply_zero (j a)
        _ = j a := by
          simpa using ContinuousMap.congr_fun hu₀ a
    have hRestricted0 : hFrel.toHomotopy (s, (0, a)) = j a := by
      exact (hFrel.eq_fst s ⟨by simp, by simp⟩).trans hBoundary0
    have hFace0 :
        (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp j) a = hFrel.toHomotopy (s, (0, a)) := by
      calc
        (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp j) a =
            ((pathSpaceEvalAt 0 Y).comp (L.curry s)) (j a) := rfl
        _ = L (s, j a) 0 := rfl
        _ = K (s, a) 0 := by
          simpa using ContinuousMap.congr_fun (hL (s, a)) 0
        _ = hFrel.toHomotopy (s, (0, a)) := rfl
    exact hFace0.trans hRestricted0
  let middleFace : v₀.right.hom.Homotopy v₁.right.hom :=
    ContinuousMap.Homotopy.ofPathSpaceMap G rfl rfl
  have hMiddleFace : HomotopicUnder v₀ v₁ := by
    refine ⟨{ toHomotopy := middleFace, prop' := ?_ }⟩
    intro s
    -- Since `G.comp j` is already the constant-path family on `j`, every intermediate slice of
    -- `middleFace` is a map under `A`.
    ext a
    calc
      ((middleFace.curry s).comp j) a = G (j a) s := rfl
      _ = ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) a s := by
        exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGj a) s
      _ = j a := rfl
  let targetFaceRaw :
      ((pathSpaceEvalAt 1 Y).comp F.toPathSpaceMap).Homotopy ((pathSpaceEvalAt 1 Y).comp G) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl (pathSpaceEvalAt 1 Y)) L
  let targetFace : u₁.right.hom.Homotopy v₁.right.hom :=
    targetFaceRaw.cast ((F.pathSpaceEvalAt_comp_toPathSpaceMap 1).trans F.curry_one) rfl
  have hTargetFace : HomotopicUnder u₁ v₁ := by
    refine ⟨{ toHomotopy := targetFace, prop' := ?_ }⟩
    intro s
    -- The `t = 1` face is handled identically, using the other boundary component of the
    -- restricted contraction.
    ext a
    change (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp j) a = j a
    have hBoundary1 :
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (1, a) = j a := by
      calc
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (1, a) = F (1, j a) := rfl
        _ = u₁.right.hom (j a) := by
          simpa using F.apply_one (j a)
        _ = j a := by
          simpa using ContinuousMap.congr_fun hu₁ a
    have hRestricted1 : hFrel.toHomotopy (s, (1, a)) = j a := by
      exact (hFrel.eq_fst s ⟨by simp, by simp⟩).trans hBoundary1
    have hFace1 :
        (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp j) a = hFrel.toHomotopy (s, (1, a)) := by
      calc
        (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp j) a =
            ((pathSpaceEvalAt 1 Y).comp (L.curry s)) (j a) := rfl
        _ = L (s, j a) 1 := rfl
        _ = K (s, a) 1 := by
          simpa using ContinuousMap.congr_fun (hL (s, a)) 1
        _ = hFrel.toHomotopy (s, (1, a)) := rfl
    exact hFace1.trans hRestricted1
  -- Compose the two endpoint faces with the middle path-space face to obtain the required
  -- homotopy under `A`.
  exact HomotopicUnder.trans hSourceFace <|
    HomotopicUnder.trans hMiddleFace (HomotopicUnder.symm hTargetFace)

/-- Helper for Proposition 6.5.3: homotopies under `A` remain homotopies under `A` after
precomposing by a fixed morphism in `Under (TopCat.of A)`. -/
private theorem homotopicUnder_precompose
    {U V W : Under (TopCat.of A)} {f₀ f₁ : V ⟶ W}
    (h : HomotopicUnder f₀ f₁) (g : U ⟶ V) :
    HomotopicUnder (g ≫ f₀) (g ≫ f₁) := by
  rcases h with ⟨H⟩
  refine ⟨{ toHomotopy :=
      H.toHomotopy.comp (ContinuousMap.Homotopy.refl g.right.hom), prop' := ?_ }⟩
  intro t
  -- Every stage of the original under-homotopy stays under `A`, and precomposition preserves
  -- that triangle.
  ext a
  calc
    (((H.toHomotopy.curry t).comp g.right.hom).comp U.hom.hom) a =
        (H.toHomotopy.curry t) (g.right.hom (U.hom.hom a)) := rfl
    _ = (H.toHomotopy.curry t) (V.hom.hom a) := by
      have hg := congrFun (congrArg ContinuousMap.toFun (congrArg TopCat.Hom.hom (Under.w g))) a
      simpa using congrArg (H.toHomotopy.curry t) hg
    _ = W.hom.hom a := by
      simpa using congrFun (congrArg ContinuousMap.toFun (H.prop t)) a

/-- Helper for Proposition 6.5.3: homotopies under `A` remain homotopies under `A` after
postcomposing by a fixed morphism in `Under (TopCat.of A)`. -/
private theorem homotopicUnder_postcompose
    {U V W : Under (TopCat.of A)} {f₀ f₁ : U ⟶ V}
    (h : HomotopicUnder f₀ f₁) (g : V ⟶ W) :
    HomotopicUnder (f₀ ≫ g) (f₁ ≫ g) := by
  rcases h with ⟨H⟩
  refine ⟨{ toHomotopy :=
      (ContinuousMap.Homotopy.refl g.right.hom).comp H.toHomotopy, prop' := ?_ }⟩
  intro t
  -- Postcomposition preserves the under-triangle because each stage already lands over `V.hom`.
  ext a
  calc
    ((g.right.hom.comp (H.toHomotopy.curry t)).comp U.hom.hom) a =
        g.right.hom ((H.toHomotopy.curry t) (U.hom.hom a)) := rfl
    _ = g.right.hom (V.hom.hom a) := by
      exact congrArg g.right.hom (ContinuousMap.congr_fun (H.prop t) a)
    _ = W.hom.hom a := by
      simpa using congrFun (congrArg ContinuousMap.toFun (congrArg TopCat.Hom.hom (Under.w g))) a

/-- Helper for Proposition 6.5.3: the right-composite ordinary homotopy built from the corrected
inverse restricts to the normalized loop built from the chosen restriction of the inverse. -/
private theorem rightCompositeRestrictionEqNormalized
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    {g :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A))}
    (hg : e.symm.toFun.Homotopy g.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    (hLift : ∀ z : I × A, hg (z.1, j z.2) = hInverseOnA z) :
    let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
    let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
      FgfRaw.cast rfl (by
        ext y
        rw [he]
        rfl)
    let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
    let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
      (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
        (by
          ext a
          rfl)
        hcomp
    ((Fgf.symm.trans e.right_inv.some).toContinuousMap).comp ((ContinuousMap.id I).prodMap j) =
      (rightInverseOnA.symm.trans (e.right_inv.some.compContinuousMap j)).toContinuousMap := by
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
      (by
        ext a
        rfl)
      hcomp
  have hFgf :
      Fgf.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
        rightInverseOnA.toContinuousMap := by
    -- Restricting the corrected right-composite homotopy to `A` recovers the chosen whiskered
    -- inverse homotopy on `A`.
    ext z
    rcases z with ⟨t, a⟩
    calc
      Fgf (t, j a) = e.toFun (hg (t, j a)) := by
        rfl
      _ = e.toFun (hInverseOnA (t, a)) := by
        rw [hLift (t, a)]
      _ = rightInverseOnA (t, a) := by
        rfl
  -- Compare the restricted right composite pointwise with the normalized loop.
  ext z
  rcases z with ⟨t, a⟩
  change (Fgf.symm.trans e.right_inv.some) (t, j a) =
    (rightInverseOnA.symm.trans (e.right_inv.some.compContinuousMap j)) (t, a)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hFgf
        (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
  · rfl

/-- Helper for Proposition 6.5.3: once the normalized restricted right loop is known to contract
relative to the boundary, the raw restricted right composite contracts as well. -/
private theorem rightCompositeRestriction_homotopicRelRefl
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    {g :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A))}
    (hg : e.symm.toFun.Homotopy g.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    (hLift : ∀ z : I × A, hg (z.1, j z.2) = hInverseOnA z)
    (hNormalized :
      let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
      let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
        (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
          (by
            ext a
            rfl)
          hcomp
      ((rightInverseOnA.symm.trans
          (e.right_inv.some.compContinuousMap j)).toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl j).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A))) :
    let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
    let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
      FgfRaw.cast rfl (by
        ext y
        rw [he]
        rfl)
    ((((Fgf.symm.trans e.right_inv.some).toContinuousMap).comp
        ((ContinuousMap.id I).prodMap j))).HomotopicRel
      ((ContinuousMap.Homotopy.refl j).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
      (by
        ext a
        rfl)
      hcomp
  have hRestriction :
      ((Fgf.symm.trans e.right_inv.some).toContinuousMap).comp ((ContinuousMap.id I).prodMap j) =
        (rightInverseOnA.symm.trans (e.right_inv.some.compContinuousMap j)).toContinuousMap := by
    -- Normalize the restricted right composite once, so the remaining step is exactly the
    -- normalized loop contraction.
    simpa [FgfRaw, Fgf, hcomp, rightInverseOnA] using
      rightCompositeRestrictionEqNormalized f e he hg hInverseOnA hLift
  -- Rewrite the raw restricted right loop to the normalized one and use the supplied contraction.
  rcases hNormalized with ⟨hNormalized⟩
  exact ⟨hNormalized.cast hRestriction.symm rfl⟩

/-- Helper for Proposition 6.5.3: the ordinary HEP already gives the controlled restriction data
needed on the right branch, even before the endpoint is rectified to `ContinuousMap.id Y`. -/
private theorem existsControlledRestrictionHomotopy
    {j : C(A, Y)} (hj : IsCofibration.{u, u, u} j)
    {Z : Type u} [TopologicalSpace Z]
    {f₀ : C(Y, Z)} {g : C(A, Z)}
    (H : (f₀.comp j).Homotopy g) :
    ∃ G : C(Y, Z), ∃ F : f₀.Homotopy G,
      F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) = H.toContinuousMap := by
  -- Use the standard HEP extension, but keep the exact restriction equation for later
  -- normalization instead of immediately forgetting it.
  obtain ⟨G, F, hF⟩ := hj.exists_homotopy_extension (f₀ := f₀) (g := g) H
  refine ⟨G, F, ?_⟩
  -- Read the extension formula pointwise on `I × A`.
  ext z
  rcases z with ⟨t, a⟩
  simpa using hF (t, a)

/-- Helper for Proposition 6.5.3: construct a right-inverse homotopy of `e` whose restriction
along `j` is exactly the whiskered inverse homotopy chosen on `A`. -/
private theorem rightInverseWithPrescribedRestriction
    {i : C(A, X)} {j : C(A, Y)}
    (hj : IsCofibration.{u, u, u} j)
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i) :
    let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
    let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
      (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
        (by
          ext a
          rfl)
      hcomp
    ∃ u : C(Y, Y), u.comp j = j ∧
      ∃ R : (e.toFun.comp e.symm.toFun).Homotopy u,
        R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
          rightInverseOnA.toContinuousMap := by
  -- Route correction: the generic path-space lifting statement was too strong. First extract the
  -- correct HEP output, namely a controlled endpoint `u` under `A` together with a homotopy from
  -- `e ∘ e⁻¹` to `u`.
  let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
      (by
        ext a
        rfl)
      hcomp
  obtain ⟨u, R, hR⟩ :=
    existsControlledRestrictionHomotopy hj rightInverseOnA
  have hu : u.comp j = j := by
    -- Evaluate the controlled restriction at time `1` to read off the endpoint condition on `u`.
    ext a
    calc
      u (j a) = R (1, j a) := by
        exact (R.apply_one (j a)).symm
      _ = rightInverseOnA (1, a) := by
        simpa using ContinuousMap.congr_fun hR (1, a)
      _ = j a := by
        simpa using rightInverseOnA.apply_one a
  exact ⟨u, hu, R, hR⟩

/-- Helper for Proposition 6.5.3: the controlled right-inverse homotopy factors through a
path-space map on `Set.range j`, and that range-level path family still ends at the image
inclusion. -/
private theorem rightInversePathSpaceFactorsThroughRange
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    {u : C(Y, Y)} (hu : u.comp j = j)
    {R : (e.toFun.comp e.symm.toFun).Homotopy u}
    (hR :
      let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
      let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
        (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
          (by
            ext a
            rfl)
          hcomp
      R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) = rightInverseOnA.toContinuousMap) :
    let D : C(Set.range j, C(I, Y)) :=
      R.toPathSpaceMap.comp (TopCat.subtypeInclusion (Set.range j)).hom
    let jRange : C(A, Set.range j) := ⟨Set.rangeFactorization j, j.continuous.rangeFactorization⟩
    let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
    let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
      (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
        (by
          ext a
          rfl)
        hcomp
    D.comp jRange = rightInverseOnA.toPathSpaceMap ∧
      (pathSpaceEvalAt 1 Y).comp D = (TopCat.subtypeInclusion (Set.range j)).hom := by
  let D : C(Set.range j, C(I, Y)) :=
    R.toPathSpaceMap.comp (TopCat.subtypeInclusion (Set.range j)).hom
  let jRange : C(A, Set.range j) := ⟨Set.rangeFactorization j, j.continuous.rangeFactorization⟩
  let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
      (by
        ext a
        rfl)
      hcomp
  have hR' :
      R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
        rightInverseOnA.toContinuousMap := by
    -- Rewrite the chosen controlled restriction into the normalized right inverse on `A`.
    simpa [hcomp, rightInverseOnA] using hR
  refine ⟨?_, ?_⟩
  · -- Restricting the range-level path-space family back along `j` recovers the normalized right
    -- inverse path family on `A`.
    ext a t
    exact ContinuousMap.congr_fun hR' (t, a)
  · -- The time-`1` endpoint of the restricted path-space family is the range inclusion, because
    -- the corrected endpoint map `u` fixes the image of `j`.
    ext z
    rcases z with ⟨y, ⟨a, rfl⟩⟩
    change R (1, j a) = j a
    calc
      R (1, j a) = u (j a) := by
        exact R.apply_one (j a)
      _ = j a := by
        simpa using ContinuousMap.congr_fun hu a

/-- Helper for Proposition 6.5.3: once the corrected right branch lands in an endpoint map
`u : Y → Y` under `A`, the remaining comparison with `ContinuousMap.id Y` is the only open
endpoint-rectification step. -/
private theorem rightEndpointRestrictionEqNormalized
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    {u : C(Y, Y)} {R : (e.toFun.comp e.symm.toFun).Homotopy u}
    (hR :
      let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
      let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
        (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
          (by
            ext a
            rfl)
          hcomp
      R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) = rightInverseOnA.toContinuousMap) :
    let H : u.Homotopy (ContinuousMap.id Y) := R.symm.trans e.right_inv.some
    let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
    let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
      (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
        (by
          ext a
          rfl)
        hcomp
    H.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
      (rightInverseOnA.symm.trans (e.right_inv.some.compContinuousMap j)).toContinuousMap := by
  let H : u.Homotopy (ContinuousMap.id Y) := R.symm.trans e.right_inv.some
  let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
      (by
        ext a
        rfl)
      hcomp
  have hR' :
      R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
        rightInverseOnA.toContinuousMap := by
    -- First rewrite the controlled endpoint homotopy to the normalized right inverse on `A`.
    simpa [hcomp, rightInverseOnA] using hR
  -- Compare the restricted endpoint homotopy pointwise with the explicit normalized right loop.
  ext z
  rcases z with ⟨t, a⟩
  change H (t, j a) = (rightInverseOnA.symm.trans (e.right_inv.some.compContinuousMap j)) (t, a)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [H, ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hR'
        (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
  · rfl

/-- Helper for Proposition 6.5.3: an endomorphism under `A` that is ordinarily homotopic to the
identity already admits a two-sided inverse under `A`. -/
private theorem existsUnderInverse_of_homotopyToId
    {j : C(A, Y)} (hj : IsCofibration.{u, u, u} j)
    (u :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (H : u.right.hom.Homotopy (ContinuousMap.id Y)) :
    ∃ h :
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
          (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)),
      HomotopicUnder (h ≫ u) (𝟙 (Under.mk (TopCat.ofHom j) : Under (TopCat.of A))) ∧
        HomotopicUnder (u ≫ h) (𝟙 (Under.mk (TopCat.ofHom j) : Under (TopCat.of A))) := by
  have hu : u.right.hom.comp j = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w u)
  let HOnARaw : (u.right.hom.comp j).Homotopy j := H.compContinuousMap j
  let HOnA : j.Homotopy j := HOnARaw.cast hu rfl
  obtain ⟨h, G, hG⟩ :=
    existsUnderHom_homotopy_of_isCofibration
      (i := j) (j := j) (g₀ := ContinuousMap.id Y) hj HOnA
  have hh : h.right.hom.comp j = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w h)
  have hHOnA : ∀ z : I × A, HOnA z = H (z.1, j z.2) := by
    intro z
    rcases z with ⟨t, a⟩
    rfl
  let leftRawBase :
      ((ContinuousMap.id Y).comp u.right.hom).Homotopy (h.right.hom.comp u.right.hom) :=
    G.comp (ContinuousMap.Homotopy.refl u.right.hom)
  let leftRaw : u.right.hom.Homotopy (u ≫ h).right.hom :=
    leftRawBase.cast rfl rfl
  have hLeftRawRestriction :
      leftRaw.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) = HOnA.toContinuousMap := by
    -- The correction `G` was chosen to agree with `H` on `A`, and `u` already fixes `A`.
    ext z
    rcases z with ⟨t, a⟩
    calc
      leftRaw (t, j a) = G (t, u.right.hom (j a)) := by
        change leftRawBase (t, j a) = G (t, u.right.hom (j a))
        rfl
      _ = G (t, j a) := by
        rw [show u.right.hom (j a) = j a by
          simpa using ContinuousMap.congr_fun hu a]
      _ = HOnA (t, a) := hG (t, a)
  have hLeftRaw_apply : ∀ z : I × A, leftRaw (z.1, j z.2) = HOnA z := by
    intro z
    exact ContinuousMap.congr_fun hLeftRawRestriction z
  have hLeftRestriction :
      ((leftRaw.symm.trans H).toContinuousMap).comp ((ContinuousMap.id I).prodMap j) =
        (HOnA.symm.trans HOnA).toContinuousMap := by
    -- The composite `u ≫ h` differs from `u` by the same boundary path `HOnA`, so their
    -- difference restricts to the standard self-canceling loop.
    ext z
    rcases z with ⟨t, a⟩
    change (leftRaw.symm.trans H) (t, j a) = (HOnA.symm.trans HOnA) (t, a)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · simpa [ContinuousMap.Homotopy.symm] using
        hLeftRaw_apply
          (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
    · simpa using (hHOnA
        (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, a)).symm
  have hLeftRestricted :
      (((leftRaw.symm.trans H).toContinuousMap).comp ((ContinuousMap.id I).prodMap j)).HomotopicRel
        ((ContinuousMap.Homotopy.refl j).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
    -- After normalization, the restriction is the generic self-canceling loop.
    rw [hLeftRestriction]
    exact homotopySymmTransHomotopicRelRefl HOnA
  have hLeft :
      HomotopicUnder (u ≫ h) (𝟙 (Under.mk (TopCat.ofHom j) : Under (TopCat.of A))) := by
    exact homotopicUnder_of_restrictedContraction hj (leftRaw.symm.trans H) hLeftRestricted
  let rightRawBase :
      (u.right.hom.comp h.right.hom).Homotopy ((ContinuousMap.id Y).comp h.right.hom) :=
    H.comp (ContinuousMap.Homotopy.refl h.right.hom)
  let rightRaw : (h ≫ u).right.hom.Homotopy h.right.hom :=
    rightRawBase.cast rfl rfl
  have hRightRawRestriction :
      rightRaw.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) = HOnA.toContinuousMap := by
    -- Postcomposing by `h` keeps the same boundary path because `h` fixes `A` exactly.
    ext z
    rcases z with ⟨t, a⟩
    calc
      rightRaw (t, j a) = H (t, h.right.hom (j a)) := by
        change rightRawBase (t, j a) = H (t, h.right.hom (j a))
        rfl
      _ = H (t, j a) := by
        rw [show h.right.hom (j a) = j a by
          simpa using ContinuousMap.congr_fun hh a]
      _ = HOnA (t, a) := (hHOnA (t, a)).symm
  have hRightRaw_apply : ∀ z : I × A, rightRaw (z.1, j z.2) = HOnA z := by
    intro z
    exact ContinuousMap.congr_fun hRightRawRestriction z
  have hRightRestriction :
      ((rightRaw.trans G.symm).toContinuousMap).comp ((ContinuousMap.id I).prodMap j) =
        (HOnA.trans HOnA.symm).toContinuousMap := by
    -- The composite `h ≫ u` differs from `h` by the same boundary path `HOnA`, so the
    -- resulting restriction is the opposite self-canceling loop.
    ext z
    rcases z with ⟨t, a⟩
    change (rightRaw.trans G.symm) (t, j a) = (HOnA.trans HOnA.symm) (t, a)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · simpa using
        hRightRaw_apply
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
    · simpa [ContinuousMap.Homotopy.symm] using hG
        (σ ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, a)
  have hRightRestricted :
      (((rightRaw.trans G.symm).toContinuousMap).comp ((ContinuousMap.id I).prodMap j)).HomotopicRel
        ((ContinuousMap.Homotopy.refl j).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
    -- Contract the opposite self-canceling loop by applying the generic contraction to `HOnA.symm`.
    rw [hRightRestriction]
    simpa using homotopySymmTransHomotopicRelRefl HOnA.symm
  have hRight :
      HomotopicUnder (h ≫ u) (𝟙 (Under.mk (TopCat.ofHom j) : Under (TopCat.of A))) := by
    exact homotopicUnder_of_restrictedContraction hj (rightRaw.trans G.symm) hRightRestricted
  exact ⟨h, hRight, hLeft⟩

/-- Helper for Proposition 6.5.3: once the right-inverse witness is chosen with the prescribed
restriction on `A`, the restricted right composite becomes the self-canceling loop
`rightInverseOnA.symm.trans rightInverseOnA`. -/
private theorem rightCompositeRestrictionEqSelfCanceling
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    {g :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A))}
    (hg : e.symm.toFun.Homotopy g.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    (hLift : ∀ z : I × A, hg (z.1, j z.2) = hInverseOnA z)
    {u : C(Y, Y)} {R : (e.toFun.comp e.symm.toFun).Homotopy u}
    (hR :
      let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
      let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
        (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
          (by
            ext a
            rfl)
          hcomp
      R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) = rightInverseOnA.toContinuousMap) :
    let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
    let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
      FgfRaw.cast rfl (by
        ext y
        rw [he]
        rfl)
    let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
    let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
      (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
        (by
          ext a
          rfl)
        hcomp
    ((Fgf.symm.trans R).toContinuousMap).comp ((ContinuousMap.id I).prodMap j) =
      (rightInverseOnA.symm.trans rightInverseOnA).toContinuousMap := by
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
      (by
        ext a
        rfl)
      hcomp
  have hFgf :
      Fgf.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
        rightInverseOnA.toContinuousMap := by
    -- Restricting the corrected right-composite homotopy to `A` recovers the chosen whiskered
    -- inverse homotopy on `A`.
    ext z
    rcases z with ⟨t, a⟩
    calc
      Fgf (t, j a) = e.toFun (hg (t, j a)) := by
        rfl
      _ = e.toFun (hInverseOnA (t, a)) := by
        rw [hLift (t, a)]
      _ = rightInverseOnA (t, a) := by
        rfl
  have hR' :
      R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
        rightInverseOnA.toContinuousMap := by
    simpa [hcomp, rightInverseOnA] using hR
  -- Compare the restricted controlled right composite pointwise with the normalized
  -- self-canceling loop.
  ext z
  rcases z with ⟨t, a⟩
  change (Fgf.symm.trans R) (t, j a) = (rightInverseOnA.symm.trans rightInverseOnA) (t, a)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hFgf
        (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
  · simpa using
      ContinuousMap.congr_fun hR'
        (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, a)

/-- Helper for Proposition 6.5.3: the controlled right-composite loop contracts relative to the
boundary once it is rewritten as `rightInverseOnA.symm.trans rightInverseOnA`. -/
private theorem rightCompositeRestriction_homotopicRelReflControlled
    {i : C(A, X)} {j : C(A, Y)}
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom)
    {g :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A))}
    (hg : e.symm.toFun.Homotopy g.right.hom)
    (hInverseOnA : (e.symm.toFun.comp j).Homotopy i)
    (hLift : ∀ z : I × A, hg (z.1, j z.2) = hInverseOnA z)
    {u : C(Y, Y)} {R : (e.toFun.comp e.symm.toFun).Homotopy u}
    (hR :
      let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
      let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
        (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
          (by
            ext a
            rfl)
          hcomp
      R.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) = rightInverseOnA.toContinuousMap) :
    let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
    let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
      FgfRaw.cast rfl (by
        ext y
        rw [he]
        rfl)
    ((((Fgf.symm.trans R).toContinuousMap).comp
        ((ContinuousMap.id I).prodMap j))).HomotopicRel
      ((ContinuousMap.Homotopy.refl j).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  let hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let rightInverseOnA : ((e.toFun.comp e.symm.toFun).comp j).Homotopy j :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hInverseOnA).cast
      (by
        ext a
        rfl)
      hcomp
  have hRestriction :
      ((Fgf.symm.trans R).toContinuousMap).comp ((ContinuousMap.id I).prodMap j) =
        (rightInverseOnA.symm.trans rightInverseOnA).toContinuousMap := by
    -- Normalize the restricted controlled right composite once, so the remaining step is the
    -- standard self-canceling loop contraction.
    simpa [FgfRaw, Fgf, hcomp, rightInverseOnA] using
      rightCompositeRestrictionEqSelfCanceling f e he hg hInverseOnA hLift hR
  -- After normalization, contract the self-canceling loop relative to the boundary.
  rcases homotopySymmTransHomotopicRelRefl rightInverseOnA with ⟨hrel⟩
  exact ⟨hrel.cast hRestriction.symm rfl⟩

/-- Proposition 6.5.3. If `i : A → X` and `j : A → Y` are cofibrations and `f : X → Y` is a map
under `A` that is an ordinary homotopy equivalence, then `f` is a cofiber homotopy equivalence. -/
theorem isCofiberHomotopyEquivalence_of_homotopyEquiv
    {i : C(A, X)} {j : C(A, Y)}
    (hi : IsCofibration.{u, u, u} i) (hj : IsCofibration.{u, u, u} j)
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (e : X ≃ₕ Y) (he : e.toFun = f.right.hom) :
    IsCofiberHomotopyEquivalence f := by
  -- Rewrite the under-category triangle into the continuous-map shape needed by the HEP.
  have hcomp : e.toFun.comp i = j := homotopyEquivToFun_comp_eq f e he
  let hInverseOnA : (e.symm.toFun.comp j).Homotopy i :=
    -- Restrict the ordinary left-inverse homotopy along `i` and rewrite its source endpoint.
    (e.left_inv.some.compContinuousMap i).cast
      (by
        rw [ContinuousMap.comp_assoc, hcomp]
        rfl)
      (by simp)
  have hLeftInvOnA :
      (e.left_inv.some.compContinuousMap i).toContinuousMap = hInverseOnA.toContinuousMap := by
    -- The chosen restricted left-inverse homotopy is definitionally the one used throughout the
    -- proof.
    rfl
  -- Use the cofibration on `j` to correct the ordinary inverse into a genuine morphism under `A`.
  obtain ⟨g, hg, hLift⟩ := existsUnderHom_homotopy_of_isCofibration hj hInverseOnA
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.right.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).right.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  obtain ⟨u, hu, R, hR⟩ := rightInverseWithPrescribedRestriction hj f e he hInverseOnA
  let uUnder :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) :=
    Under.homMk (TopCat.ofHom u) (by simpa using congrArg TopCat.ofHom hu)
  have hRightRestricted :
      ((((Fgf.symm.trans R).toContinuousMap).comp
          ((ContinuousMap.id I).prodMap j))).HomotopicRel
        ((ContinuousMap.Homotopy.refl j).toContinuousMap)
          (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
    -- The controlled right-inverse witness turns the restricted loop into the standard
    -- self-canceling form.
    simpa [FgfRaw, Fgf] using
      rightCompositeRestriction_homotopicRelReflControlled f e he hg hInverseOnA hLift hR
  let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.right.hom.comp e.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
  let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).right.hom :=
    FfgRaw.cast rfl (by
      ext x
      rw [he]
      rfl)
  have hLeftRestricted :
      ((((Ffg.symm.trans e.left_inv.some).toContinuousMap).comp
          ((ContinuousMap.id I).prodMap i))).HomotopicRel
        ((ContinuousMap.Homotopy.refl i).toContinuousMap)
          (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
    -- The left restricted composite contracts after normalization to the self-canceling loop.
    simpa [FfgRaw, Ffg] using
      leftCompositeRestriction_homotopicRelRefl f e he hg hInverseOnA hLeftInvOnA hLift
  refine (isCofiberHomotopyEquivalence_iff).2 ?_
  let HEndpoint : u.Homotopy (ContinuousMap.id Y) := R.symm.trans e.right_inv.some
  obtain ⟨h, hhRight, _hhLeft⟩ := existsUnderInverse_of_homotopyToId hj uUnder HEndpoint
  have hToU : HomotopicUnder (g ≫ f) uUnder := by
    exact homotopicUnder_of_restrictedContraction hj (Fgf.symm.trans R) hRightRestricted
  let g' :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) :=
    h ≫ g
  refine ⟨g', ?_, ?_⟩
  · -- Upgrade the right ordinary homotopy to a homotopy under `A` by rectifying only its
    -- restriction along `j`, then absorb the controlled endpoint `u` into a genuine under
    -- inverse of `u`.
    have hCompToU : HomotopicUnder (g' ≫ f) (h ≫ uUnder) := by
      simpa [g', Category.assoc] using homotopicUnder_precompose hToU h
    exact HomotopicUnder.trans hCompToU hhRight
  · -- The left ordinary homotopy is handled by the analogous restricted contraction on `i`.
    let leftComposite :
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
          (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) :=
      f ≫ g'
    let rawLeft :
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
          (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) :=
      f ≫ g
    have hRawLeft :
        HomotopicUnder rawLeft (𝟙 (Under.mk (TopCat.ofHom i) : Under (TopCat.of A))) := by
      exact homotopicUnder_of_restrictedContraction hi (Ffg.symm.trans e.left_inv.some)
        hLeftRestricted
    have hAbsorb :
        HomotopicUnder (leftComposite ≫ rawLeft) leftComposite := by
      simpa [leftComposite, rawLeft, g', Category.assoc] using
        homotopicUnder_precompose hRawLeft leftComposite
    have hCancel :
        HomotopicUnder (leftComposite ≫ rawLeft) rawLeft := by
      have hToEndpoint :
          HomotopicUnder (leftComposite ≫ rawLeft) (f ≫ h ≫ uUnder ≫ g) := by
        simpa [leftComposite, rawLeft, g', Category.assoc] using
          homotopicUnder_postcompose (homotopicUnder_precompose hToU (f ≫ h)) g
      have hEndpointCancel :
          HomotopicUnder (f ≫ h ≫ uUnder ≫ g) rawLeft := by
        simpa [rawLeft, uUnder, Category.assoc] using
          homotopicUnder_postcompose (homotopicUnder_precompose hhRight f) g
      exact HomotopicUnder.trans hToEndpoint hEndpointCancel
    have hLeftToRaw : HomotopicUnder leftComposite rawLeft := by
      exact HomotopicUnder.trans (HomotopicUnder.symm hAbsorb) hCancel
    exact HomotopicUnder.trans hLeftToRaw hRawLeft

/-- Existence-only restatement of Proposition 6.5.3 for callers that only know that the
underlying map of `f` is an ordinary homotopy equivalence. -/
theorem isCofiberHomotopyEquivalence_of_exists_homotopyEquiv
    {i : C(A, X)} {j : C(A, Y)}
    (hi : IsCofibration.{u, u, u} i) (hj : IsCofibration.{u, u, u} j)
    (f :
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of A)))
    (hf : ∃ e : X ≃ₕ Y, e.toFun = f.right.hom) :
    IsCofiberHomotopyEquivalence f := by
  rcases hf with ⟨e, he⟩
  exact isCofiberHomotopyEquivalence_of_homotopyEquiv hi hj f e he
