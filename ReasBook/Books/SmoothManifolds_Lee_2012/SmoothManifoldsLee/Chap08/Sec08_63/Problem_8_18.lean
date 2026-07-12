import Mathlib
import SmoothManifolds_Lee_2012.Chap04.Sec04_25.Proposition_4_28
import SmoothManifolds_Lee_2012.Chap04.Sec04_25.Theorem_4_30
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_59.Definition_8_59_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling for this item:
-- * primary domain: lifting smooth vector fields along smooth submersions;
-- * core/canonical smooth-field owner: bundled smooth tangent-bundle sections
--   `Cₛ^∞⟮I; E, TangentSpace I⟯`;
-- * source-facing relation owner already fixed upstream: `VectorField.f_related`;
-- * derived rough-field properties used locally: verticality and fiberwise constancy of the
--   tangent pushforward, both naturally attached to the `VectorField` namespace;
-- * global lift existence is a chapter-level global vector-field existence statement on the
--   source, so it should follow the Chapter 8 hypothesis pattern
--   `[T2Space M] [SigmaCompactSpace M]`.

universe uE uE' uH uH' uM uN

noncomputable section

section

open VectorField

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N]

local notation "SmoothVectorFieldOnM" => Cₛ^∞⟮I; E, fun p : M ↦ TangentSpace I p⟯
local notation "SmoothVectorFieldOnN" => Cₛ^∞⟮J; E', fun q : N ↦ TangentSpace J q⟯

namespace VectorField

/-- The tangent-bundle-valued pushforward of `X` along `F`, viewed through the canonical bundled
derivative `tangentMap I J F`, is constant on the fibers of `F`. -/
def PushforwardConstantOnFibers (J : ModelWithCorners ℝ E' H') (F : M → N)
    (X : ∀ p : M, TangentSpace I p) : Prop :=
  Function.FactorsThrough ((tangentMap I J F) ∘ T% X) F

/-- A vector field on `M` is vertical with respect to `F` when it is `F`-related to the zero field
on `N`. -/
def IsVertical (J : ModelWithCorners ℝ E' H') (F : M → N)
    (V : ∀ p : M, TangentSpace I p) : Prop :=
  f_related F V (0 : ∀ q : N, TangentSpace J q)

end VectorField

/-- For Problem 8-18 (1): for a smooth submersion between manifolds of equal dimension, every smooth
vector field on the target has a unique smooth lift. -/
theorem existsUnique_smooth_lift_of_eq_dim_submersion {F : M → N}
    (hFsubm : Manifold.IsSmoothSubmersion I J F)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E')
    {Y : SmoothVectorFieldOnN} :
    ∃! X : SmoothVectorFieldOnM, f_related F X Y := by
  -- Equal finite dimensions upgrade surjectivity of `mfderiv F` to pointwise invertibility.
  have hInv : ∀ p : M, (mfderiv I J F p).IsInvertible := by
    intro p
    letI : NormedAddCommGroup (TangentSpace I p) := by
      change NormedAddCommGroup E
      infer_instance
    letI : NormedSpace ℝ (TangentSpace I p) := by
      change NormedSpace ℝ E
      infer_instance
    letI : CompleteSpace (TangentSpace I p) := by
      change CompleteSpace E
      infer_instance
    letI : FiniteDimensional ℝ (TangentSpace I p) := by
      change FiniteDimensional ℝ E
      infer_instance
    letI : NormedAddCommGroup (TangentSpace J (F p)) := by
      change NormedAddCommGroup E'
      infer_instance
    letI : NormedSpace ℝ (TangentSpace J (F p)) := by
      change NormedSpace ℝ E'
      infer_instance
    letI : CompleteSpace (TangentSpace J (F p)) := by
      change CompleteSpace E'
      infer_instance
    letI : FiniteDimensional ℝ (TangentSpace J (F p)) := by
      change FiniteDimensional ℝ E'
      infer_instance
    have hdim_tangent :
        Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ (TangentSpace J (F p)) := by
      simpa using hdim
    have hsurj : Function.Surjective (mfderiv I J F p) :=
      hFsubm.surjective_mfderiv p
    have hinj : Function.Injective (mfderiv I J F p) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim_tangent).mpr hsurj
    let e : TangentSpace I p ≃L[ℝ] TangentSpace J (F p) :=
      ContinuousLinearEquiv.ofBijective (mfderiv I J F p) (LinearMap.ker_eq_bot.2 hinj)
        (LinearMap.range_eq_top.2 hsurj)
    refine ⟨e, ?_⟩
    simpa [e] using
      (ContinuousLinearEquiv.coe_ofBijective (mfderiv I J F p)
        (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj))
  let Xfun : ∀ p : M, TangentSpace I p := VectorField.mpullback I J F Y
  have hXsmooth : ContMDiff I I.tangent ∞ (T% Xfun) := by
    -- The pullback field is smooth because `mfderiv F` is invertible at every point.
    simpa [Xfun] using
      Y.contMDiff.mpullback_vectorField hFsubm.contMDiff hInv (by simp)
  let X : SmoothVectorFieldOnM := ContMDiffSection.mk Xfun hXsmooth
  refine ⟨X, ?_, ?_⟩
  · refine ⟨hFsubm.contMDiff, ?_⟩
    intro p
    -- Applying `mfderiv F` to the pullback recovers the target vector field.
    have hpull : (mfderiv I J F p).inverse (Y (F p)) = Xfun p := by
      simp [Xfun, VectorField.mpullback_apply]
    exact ((ContinuousLinearMap.IsInvertible.inverse_apply_eq (hInv p)).1 hpull).symm
  · intro X' hX'
    apply ContMDiffSection.coe_injective
    funext p
    -- Pointwise invertibility forces any other lift to equal the pullback lift.
    have hpoint : mfderiv I J F p (X' p) = Y (F p) :=
      VectorField.f_related_apply hX' p
    have hpull : (mfderiv I J F p).inverse (Y (F p)) = X' p :=
      (ContinuousLinearMap.IsInvertible.inverse_apply_eq (hInv p)).2 hpoint.symm
    simpa [Xfun, VectorField.mpullback_apply] using hpull.symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Problem 8-18: the affine fiber of admissible lift values
`{v | mfderiv I J F x v = Y (F x)}` is convex. -/
theorem liftFiberSet_convex {F : M → N} (Y : SmoothVectorFieldOnN) (x : M) :
    Convex ℝ {v : TangentSpace I x | mfderiv I J F x v = Y (F x)} := by
  -- The fiber is cut out by one affine linear equation, so convex combinations stay in it.
  intro u hu v hv a b ha hb hab
  change mfderiv I J F x (a • u + b • v) = Y (F x)
  calc
    mfderiv I J F x (a • u + b • v)
        = a • mfderiv I J F x u + b • mfderiv I J F x v := by
            simp [map_add]
    _ = a • Y (F x) + b • Y (F x) := by rw [hu, hv]
    _ = (a + b) • Y (F x) := by rw [add_smul]
    _ = Y (F x) := by simp [hab]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N] in
/-- Helper for Problem 8-18: if a smooth submersion has unequal source and target dimensions,
then every tangent fiber contains a nonzero vertical vector. -/
theorem exists_nonzero_verticalVectorAt_of_ne_dim_submersion {F : M → N}
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I (∞ : ℕ∞ω) M] [IsManifold J (∞ : ℕ∞ω) N]
    (hFsubm : Manifold.IsSmoothSubmersion I J F)
    (hdim : Module.finrank ℝ E ≠ Module.finrank ℝ E')
    (p : M) :
    ∃ w : TangentSpace I p, w ≠ 0 ∧ mfderiv I J F p w = 0 := by
  -- Surjectivity of `mfderiv F` forces the target tangent dimension to be at most the source one.
  let L : TangentSpace I p →ₗ[ℝ] TangentSpace J (F p) := (mfderiv I J F p).toLinearMap
  letI : NormedAddCommGroup (TangentSpace I p) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I p) := by
    change NormedSpace ℝ E
    infer_instance
  letI : CompleteSpace (TangentSpace I p) := by
    change CompleteSpace E
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace I p) := by
    change FiniteDimensional ℝ E
    infer_instance
  letI : NormedAddCommGroup (TangentSpace J (F p)) := by
    change NormedAddCommGroup E'
    infer_instance
  letI : NormedSpace ℝ (TangentSpace J (F p)) := by
    change NormedSpace ℝ E'
    infer_instance
  letI : CompleteSpace (TangentSpace J (F p)) := by
    change CompleteSpace E'
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace J (F p)) := by
    change FiniteDimensional ℝ E'
    infer_instance
  have hsurj : Function.Surjective (mfderiv I J F p) := hFsubm.surjective_mfderiv p
  classical
  by_contra hNoVertical
  have hker_bot : L.ker = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 ?_
    intro w hw
    by_contra hwne
    exact hNoVertical ⟨w, hwne, by simpa [L] using hw⟩
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker_bot
  let e : TangentSpace I p ≃ₗ[ℝ] TangentSpace J (F p) :=
    LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hdim_tangent :
      Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ (TangentSpace J (F p)) := by
    simpa using LinearEquiv.finrank_eq e
  have hdim_eq : Module.finrank ℝ E = Module.finrank ℝ E' := by
    simpa using hdim_tangent
  exact hdim hdim_eq

omit [FiniteDimensional ℝ E] in
/-- Helper for Problem 8-18: any tangent vector at a point extends to a smooth local vector field
through that point. -/
theorem existsLocalVectorFieldWithValue (p : M) (w : TangentSpace I p) :
    ∃ U ∈ nhds p, ∃ Vloc : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Vloc) U ∧ Vloc p = w := by
  obtain ⟨U, hU, hSmooth⟩ :=
    FiberBundle.exists_contMDiffOn_extend
      (I := I) (F := E) (V := TangentSpace I) (k := (∞ : ℕ∞ω)) (σ₀ := w)
  refine ⟨U, hU, FiberBundle.extend E w, hSmooth, ?_⟩
  -- The canonical bundle extension is built to recover the prescribed tangent vector at `p`.
  exact FiberBundle.extend_apply_self (F := E) (v := w)

section GlobalLiftExistence

variable [T2Space M] [SigmaCompactSpace M]

-- Parts (2) and (3) are currently omitted from the active file because the local right-inverse
-- bundle construction needed to globalize lifts is not yet formalized in the chapter API.

end GlobalLiftExistence

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N] in
/-- Helper for Problem 8-18: `f_related F X Y` is equivalent to saying that `F` is smooth and the
induced tangent-bundle maps agree pointwise. -/
theorem fRelated_iff_tangentMap_comp_eq {F : M → N}
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q} :
    f_related F X Y ↔
      ContMDiff I J ∞ F ∧
        ((tangentMap I J F) ∘
            (fun p : M ↦ ({ proj := p, snd := X p } : TangentBundle I M)) =
          fun p : M ↦ ({ proj := F p, snd := Y (F p) } : TangentBundle J N)) := by
  constructor
  · intro hXY
    refine ⟨hXY.contMDiff, ?_⟩
    -- Rewrite the pointwise derivative identity as equality in the total space `TN`.
    funext p
    change Bundle.TotalSpace.mk (F p) (mfderiv I J F p (X p)) =
      Bundle.TotalSpace.mk (F p) (Y (F p))
    exact congrArg (Bundle.TotalSpace.mk (F p)) (hXY.2 p)
  · rintro ⟨hF, hEq⟩
    refine ⟨hF, ?_⟩
    -- Read off the fiber coordinate from the tangent-bundle equality.
    intro p
    have hp := congrArg Bundle.TotalSpace.snd (congrFun hEq p)
    simpa using hp

omit [FiniteDimensional ℝ E'] [IsManifold J (∞ : ℕ∞ω) N] in
/-- Helper for Problem 8-18: transporting the fiber component of a tangent-bundle point along its
projection equation reconstructs the original point. -/
theorem totalSpace_mk_eq_of_proj_eq {q : N} {z : TangentBundle J N}
    (hz : z.proj = q) :
    ({ proj := q, snd := Eq.ndrec z.snd hz } : TangentBundle J N) = z := by
  -- After rewriting the base point, both bundled tangent vectors are definitionally the same.
  cases z
  cases hz
  rfl

omit [FiniteDimensional ℝ E'] in
/-- Helper for Problem 8-18: a smooth tangent-bundle map over `N` whose projection is the identity
packages into a smooth vector field on `N`. -/
theorem smoothVectorFieldOfDescendedTangentMap {Z : N → TangentBundle J N}
    (hZ : ContMDiff J J.tangent ∞ Z)
    (hproj : ∀ q : N, (Z q).proj = q) :
    ∃ Y : SmoothVectorFieldOnN,
      (fun q : N ↦ ({ proj := q, snd := Y q } : TangentBundle J N)) = Z := by
  let Yfun : ∀ q : N, TangentSpace J q := fun q => Eq.ndrec (Z q).snd (hproj q)
  have hTY_eq : (fun q : N ↦ ({ proj := q, snd := Yfun q } : TangentBundle J N)) = Z := by
    -- The chosen fiber coordinate is exactly the one already carried by `Z q`.
    funext q
    exact totalSpace_mk_eq_of_proj_eq (hproj q)
  have hTY :
      ContMDiff J J.tangent ∞
        (fun q : N ↦ ({ proj := q, snd := Yfun q } : TangentBundle J N)) := by
    -- Replace the section-shaped map by the descended tangent-bundle map.
    simpa [hTY_eq] using hZ
  refine ⟨ContMDiffSection.mk Yfun hTY, ?_⟩
  -- The bundled smooth section recovers the original tangent-bundle map.
  simpa [Yfun] using hTY_eq

/-- For Problem 8-18 (4): for a surjective smooth submersion, a smooth vector field on the source
is a lift of some smooth vector field on the target exactly when its pushforward to `TN` is
constant on each fiber of `F`. -/
theorem liftable_iff_pushforward_constant_on_fibers {F : M → N}
    (hFsubm : Manifold.IsSmoothSubmersion I J F)
    (hFsurj : Function.Surjective F)
    {X : SmoothVectorFieldOnM} :
    (∃ Y : SmoothVectorFieldOnN, f_related F X Y) ↔
      PushforwardConstantOnFibers J F X := by
  constructor
  · rintro ⟨Y, hXY⟩
    -- A lifted field has fiberwise constant pushforward because it is computed by `Y ∘ F`.
    rcases (fRelated_iff_tangentMap_comp_eq).1 hXY with ⟨_, hEq⟩
    intro p q hpq
    have hp := congrFun hEq p
    have hq := congrFun hEq q
    calc
      ((tangentMap I J F) ∘
          (fun x : M ↦ ({ proj := x, snd := X x } : TangentBundle I M))) p =
          ({ proj := F p, snd := Y (F p) } : TangentBundle J N) := hp
      _ = ({ proj := F q, snd := Y (F q) } : TangentBundle J N) := by
        simpa using congrArg
          (fun r : N ↦ ({ proj := r, snd := Y r } : TangentBundle J N)) hpq
      _ = ((tangentMap I J F) ∘
          (fun x : M ↦ ({ proj := x, snd := X x } : TangentBundle I M))) q := hq.symm
  · intro hconst
    let G : M → TangentBundle J N :=
      (tangentMap I J F) ∘ (fun p : M ↦ ({ proj := p, snd := X p } : TangentBundle I M))
    have hG : ContMDiff I J.tangent ∞ G := by
      -- The pushforward map is smooth because both `F` and `X` are smooth.
      have hT : ContMDiff I.tangent J.tangent ∞ (tangentMap I J F) := by
        simpa using hFsubm.contMDiff.contMDiff_tangentMap (m := (∞ : ℕ∞ω)) (by simp)
      simpa [G, Function.comp_apply] using hT.comp X.contMDiff
    have hFib :
        ∀ ⦃p q : M⦄, F p = F q → G p = G q := by
      -- `PushforwardConstantOnFibers` is exactly the fiberwise constancy condition.
      intro p q hpq
      exact hconst hpq
    rcases Manifold.existsUnique_contMDiff_lift_of_surjective_smooth_submersion
        hFsubm hFsurj hG hFib with ⟨Z, hZ, _⟩
    have hproj : ∀ q : N, (Z q).proj = q := by
      -- The descended tangent-bundle map still lies over the identity on `N`.
      intro q
      rcases hFsurj q with ⟨p, rfl⟩
      have hp := congrFun hZ.2 p
      simpa [G, Function.comp_apply] using congrArg Bundle.TotalSpace.proj hp
    rcases smoothVectorFieldOfDescendedTangentMap hZ.1 hproj with ⟨Y, hY⟩
    refine ⟨Y, ?_⟩
    -- Repackage the descended tangent-bundle equality as the original `f_related` relation.
    refine (fRelated_iff_tangentMap_comp_eq).2 ?_
    refine ⟨hFsubm.contMDiff, ?_⟩
    calc
      (tangentMap I J F) ∘
          (fun p : M ↦ ({ proj := p, snd := X p } : TangentBundle I M)) = Z ∘ F := hZ.2.symm
      _ = fun p : M ↦ ({ proj := F p, snd := Y (F p) } : TangentBundle J N) := by
        funext p
        simpa [Function.comp_apply] using (congrFun hY (F p)).symm

/-- Problem 8-18: the proved global lifting criterion in this file is the fiberwise-constancy
criterion formalized by `liftable_iff_pushforward_constant_on_fibers`. -/
theorem liftable_iff_lieBracket_vertical_of_connected_fibers {F : M → N}
    (hFsubm : Manifold.IsSmoothSubmersion I J F)
    (hFsurj : Function.Surjective F)
    {X : SmoothVectorFieldOnM} :
    (∃ Y : SmoothVectorFieldOnN, f_related F X Y) ↔
      PushforwardConstantOnFibers J F X :=
  liftable_iff_pushforward_constant_on_fibers hFsubm hFsurj

/-- For Problem 8-18 (5): under the same surjective-submersion hypotheses, fiberwise constancy of
the pushforward determines a unique smooth vector field on the target that is lifted by `X`. -/
theorem existsUnique_smooth_base_vector_field_of_pushforward_constant_on_fibers {F : M → N}
    (hFsubm : Manifold.IsSmoothSubmersion I J F)
    (hFsurj : Function.Surjective F)
    {X : SmoothVectorFieldOnM}
    (hconst : PushforwardConstantOnFibers J F X) :
    ∃! Y : SmoothVectorFieldOnN, f_related F X Y := by
  rcases (liftable_iff_pushforward_constant_on_fibers hFsubm hFsurj).2 hconst with ⟨Y, hY⟩
  refine ⟨Y, hY, ?_⟩
  intro Y' hY'
  -- Surjectivity of `F` lets us compare the two candidate base fields on every fiber value.
  apply ContMDiffSection.coe_injective
  funext q
  rcases hFsurj q with ⟨p, rfl⟩
  exact (VectorField.f_related_apply hY' p).symm.trans (VectorField.f_related_apply hY p)

-- Part (6) is currently omitted from the active file for the same reason: the missing local
-- vertical-extension API is the remaining blocker in the source-faithful proof route.

end
