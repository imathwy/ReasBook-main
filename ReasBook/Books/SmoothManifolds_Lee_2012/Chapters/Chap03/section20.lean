import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Topology.Maps.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_20 (from Chap03/Sec03_16) -/
universe u v

open Bundle
open scoped Manifold ContDiff

noncomputable section

variable {n : ℕ}
variable {H : Type u} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M]

section GlobalChart

variable (U : TopologicalSpace.Opens H)

/-- Helper for Proposition 3.20: the inclusion `U × ℝ^n ↪ H × ℝ^n` is smooth. -/
lemma prod_subtype_val_contMDiff :
    ContMDiff
      (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞
      (Prod.map (Subtype.val : U → H) (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) := by
  -- Check smoothness componentwise on the product manifold.
  rw [contMDiff_prod_iff]
  constructor
  · -- The first coordinate is the smooth open-subset inclusion composed with the first projection.
    change ContMDiff
      (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      I
      ∞
      (fun x : U × EuclideanSpace ℝ (Fin n) ↦ ((x.1 : U) : H))
    exact (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → H)).comp contMDiff_fst
  · -- The second coordinate is just the ordinary second projection.
    change ContMDiff
      (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ∞
      (fun x : U × EuclideanSpace ℝ (Fin n) ↦ x.2)
    exact contMDiff_snd

/-- Helper for Proposition 3.20: the preferred product chart on `U × ℝ^n` is the ambient
inclusion `U × ℝ^n ↪ H × ℝ^n`. -/
lemma prod_chartAt_eq_prod_subtype_val
    (x : U × EuclideanSpace ℝ (Fin n)) :
    (chartAt (ModelProd H (EuclideanSpace ℝ (Fin n))) x :
      U × EuclideanSpace ℝ (Fin n) → ModelProd H (EuclideanSpace ℝ (Fin n))) =
      Prod.map (Subtype.val : U → H)
        (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  -- The first factor uses the open-subset chart, while the second factor uses the identity chart.
  funext y
  cases y
  rfl

/-- Helper for Proposition 3.20: over an open subset of the model space, the tangent-bundle chart
is the ambient inclusion of `U × ℝ^n` after the canonical identification `TotalSpace.toProd`. -/
lemma tangent_bundle_opens_chartAt
    (p : TangentBundle I U) :
    (chartAt (ModelProd H (EuclideanSpace ℝ (Fin n))) p :
      TangentBundle I U → ModelProd H (EuclideanSpace ℝ (Fin n))) =
      ((Prod.map (Subtype.val : U → H)
          (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) :
        U × EuclideanSpace ℝ (Fin n) → ModelProd H (EuclideanSpace ℝ (Fin n))) ∘
        TotalSpace.toProd U (EuclideanSpace ℝ (Fin n)) := by
  funext q
  have hchart : achart H p.1 = achart H q.1 := by
    ext y <;> simp [TopologicalSpace.Opens.chartAt_eq]
  apply Prod.ext
  · -- All preferred charts on `U` are the inclusion `Subtype.val`, so the base coordinate is `q.1`.
    simpa [Function.comp, TopologicalSpace.Opens.chartAt_eq] using
      (TangentBundle.coe_chartAt_fst (p := q) (q := p))
  · -- With identical base charts, the tangent coordinate change collapses to the identity.
    simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv,
      FiberBundleCore.localTrivAsPartialEquiv, VectorBundleCore.toFiberBundleCore_baseSet,
      tangentBundleCore_baseSet, hchart]
    simp only [mfld_simps]
    exact (tangentBundleCore I U).coordChange_self (achart H q.1) q.1
      (mem_achart_source H q.1) q.2

/-- Helper for Proposition 3.20: over an open subset of the model space, every tangent-bundle
trivialization has full base set. -/
lemma tangent_bundle_opens_trivializationAt_baseSet_univ
    (x : U) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x).baseSet = Set.univ := by
  -- The open-subset chart is global because it is the restriction of the unique model-space chart.
  ext y
  rw [TangentBundle.trivializationAt_baseSet]
  simp [TopologicalSpace.Opens.chartAt_eq]

/-- Helper for Proposition 3.20: over an open subset of the model space, a tangent-bundle
trivialization is defined on all of `TU`. -/
lemma tangent_bundle_opens_trivializationAt_source_univ
    (x : U) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x).source = Set.univ := by
  -- Once the base set is all of `U`, the source is all of the total space.
  rw [(trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x).source_eq,
    tangent_bundle_opens_trivializationAt_baseSet_univ (I := I) (U := U) x]
  simp

/-- Helper for Proposition 3.20: over an open subset of the model space, the tangent-bundle
trivialization lands on all of `U × ℝ^n`. -/
lemma tangent_bundle_opens_trivializationAt_target_univ
    (x : U) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x).target = Set.univ := by
  -- The target of a trivialization is `baseSet × univ`, so the global base chart gives all pairs.
  rw [(trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x).target_eq,
    tangent_bundle_opens_trivializationAt_baseSet_univ (I := I) (U := U) x]
  simp

/-- Helper for Proposition 3.20: over an open subset of the model space, the tangent-bundle
trivialization is exactly the canonical product identification. -/
lemma tangent_bundle_opens_trivializationAt_eq_toProd
    (x : U) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x :
      TangentBundle I U → U × EuclideanSpace ℝ (Fin n)) =
      TotalSpace.toProd U (EuclideanSpace ℝ (Fin n)) := by
  funext p
  let q : TangentBundle I U := ⟨x, 0⟩
  have htriv :
      (chartAt (ModelProd H (EuclideanSpace ℝ (Fin n))) q :
        TangentBundle I U → ModelProd H (EuclideanSpace ℝ (Fin n))) p =
      Prod.map (Subtype.val : U → H)
        (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x) p) := by
    -- Expanding the bundle chart shows it is the trivialization followed by the base inclusion.
    simpa [q, Function.comp, TopologicalSpace.Opens.chartAt_eq, prodChartedSpace_chartAt] using
      congrArg
        (fun e : OpenPartialHomeomorph (TangentBundle I U)
          (ModelProd H (EuclideanSpace ℝ (Fin n))) ↦ e p)
        (FiberBundle.chartedSpace_chartAt
          (F := EuclideanSpace ℝ (Fin n)) (E := TangentSpace I) (HB := H) (x := q))
  have hprod :
      (chartAt (ModelProd H (EuclideanSpace ℝ (Fin n))) q :
        TangentBundle I U → ModelProd H (EuclideanSpace ℝ (Fin n))) p =
      Prod.map (Subtype.val : U → H)
        (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        ((TotalSpace.toProd U (EuclideanSpace ℝ (Fin n))) p) := by
    -- The previous chart computation identifies the same chart with `TotalSpace.toProd`.
    simpa [Function.comp] using
      congrArg
        (fun f : TangentBundle I U → ModelProd H (EuclideanSpace ℝ (Fin n)) ↦ f p)
        (tangent_bundle_opens_chartAt (I := I) U q)
  exact (Subtype.val_injective.prodMap (fun _ _ h ↦ h)) (htriv.symm.trans hprod)

/-- Helper for Proposition 3.20: over an open subset of the model space, the inverse
trivialization is the canonical reconstruction from product coordinates. -/
lemma tangent_bundle_opens_trivializationAt_symm_eq_fromProd
    (x : U) :
    let e : Trivialization (EuclideanSpace ℝ (Fin n))
        (Bundle.TotalSpace.proj : TangentBundle I U → U) :=
      trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x
    ((e.toOpenPartialHomeomorph).symm : U × EuclideanSpace ℝ (Fin n) → TangentBundle I U) =
      fun z ↦ (⟨z.1, z.2⟩ : TangentBundle I U) := by
  let e : Trivialization (EuclideanSpace ℝ (Fin n))
      (Bundle.TotalSpace.proj : TangentBundle I U → U) :=
    trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x
  funext z
  have hz : z ∈ e.target := by
    rw [tangent_bundle_opens_trivializationAt_target_univ (I := I) (U := U) x]
    simp
  -- Apply `TotalSpace.toProd` to both sides, where both points are visibly sent to `z`.
  apply (TotalSpace.toProd U (EuclideanSpace ℝ (Fin n))).injective
  calc
    TotalSpace.toProd U (EuclideanSpace ℝ (Fin n))
        (((e.toOpenPartialHomeomorph).symm) z) =
      e (((e.toOpenPartialHomeomorph).symm) z) := by
        simpa using
          congrArg
            (fun f : TangentBundle I U → U × EuclideanSpace ℝ (Fin n) ↦
              f (((e.toOpenPartialHomeomorph).symm) z))
            (tangent_bundle_opens_trivializationAt_eq_toProd (I := I) (U := U) x).symm
    _ = z := e.apply_symm_apply hz
    _ = TotalSpace.toProd U (EuclideanSpace ℝ (Fin n)) (⟨z.1, z.2⟩ : TangentBundle I U) := by
        rfl

/-- Helper for Proposition 3.20: the canonical identification `TU ≃ U × ℝ^n` is smooth for an
open subset `U` of the model space. -/
lemma tangent_bundle_opens_to_prod_contMDiff :
    ContMDiff I.tangent (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : TangentBundle I U ↦ (p.1, p.2)) := by
  -- Route correction: instead of transporting charts by hand, identify the global trivialization
  -- itself with `TotalSpace.toProd` and invoke the generic smoothness theorem for trivializations.
  classical
  by_cases hU : Nonempty U
  · let x : U := Classical.choice hU
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x
    have hsource : e.source = Set.univ :=
      tangent_bundle_opens_trivializationAt_source_univ (I := I) (U := U) x
    have heq :
        (e : TangentBundle I U → U × EuclideanSpace ℝ (Fin n)) =
          TotalSpace.toProd U (EuclideanSpace ℝ (Fin n)) :=
      tangent_bundle_opens_trivializationAt_eq_toProd (I := I) (U := U) x
    have hcont :
        ContMDiffOn I.tangent (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (e : TangentBundle I U → U × EuclideanSpace ℝ (Fin n)) e.source := by
      simpa [ModelWithCorners.tangent] using
        (e.contMDiffOn :
          ContMDiffOn I.tangent (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ e e.source)
    -- The global chart on `TU` is the bundle trivialization, so smoothness is immediate on `univ`.
    rw [← contMDiffOn_univ]
    simpa [hsource] using
      (hcont.congr fun y hy ↦ by simpa using (congrArg (fun f => f y) heq).symm)
  · letI : IsEmpty U := ⟨fun x => hU ⟨x⟩⟩
    intro p
    exact isEmptyElim p.1

/-- Helper for Proposition 3.20: the inverse identification `(U × ℝ^n) → TU` is smooth. -/
lemma tangent_bundle_opens_to_prod_symm_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I.tangent ∞
      (fun x : U × EuclideanSpace ℝ (Fin n) ↦
        (⟨x.1, x.2⟩ : TangentBundle I U)) := by
  -- Route correction: use the same global trivialization, now through its inverse on the full
  -- target `U × ℝ^n`.
  classical
  by_cases hU : Nonempty U
  · let x : U := Classical.choice hU
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x
    have htarget : e.target = Set.univ :=
      tangent_bundle_opens_trivializationAt_target_univ (I := I) (U := U) x
    have heq :
        (((e.toOpenPartialHomeomorph).symm : U × EuclideanSpace ℝ (Fin n) → TangentBundle I U)) =
          (fun z ↦ (⟨z.1, z.2⟩ : TangentBundle I U)) :=
      by
        simpa [e] using tangent_bundle_opens_trivializationAt_symm_eq_fromProd (I := I) (U := U) x
    have hcont :
        ContMDiffOn (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I.tangent ∞
          (((e.toOpenPartialHomeomorph).symm : U × EuclideanSpace ℝ (Fin n) → TangentBundle I U))
          e.target := by
      simpa [ModelWithCorners.tangent] using
        (e.contMDiffOn_symm :
          ContMDiffOn (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I.tangent ∞
            ((e.toOpenPartialHomeomorph).symm) e.target)
    -- The inverse global chart is smooth on all of `U × ℝ^n` because the trivialization target is
    -- all of `univ`.
    rw [← contMDiffOn_univ]
    simpa [htarget] using
      (hcont.congr fun y hy ↦ by simpa using (congrArg (fun f => f y) heq).symm)
  · letI : IsEmpty U := ⟨fun x => hU ⟨x⟩⟩
    intro x
    exact isEmptyElim x.1

/-- Helper for Proposition 3.20: the forward trivialization lemma, stated with the exact function
type expected by the diffeomorphism structure fields. -/
lemma tangent_bundle_opens_to_prod_contMDiff_field :
    ContMDiff I.tangent (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (show TangentBundle I U → U × EuclideanSpace ℝ (Fin n) from
        TotalSpace.toProd U (EuclideanSpace ℝ (Fin n))) := by
  -- This wrapper only matches the exact field elaboration expected in the diffeomorphism record.
  simpa [TangentBundle, TotalSpace.toProd]
    using tangent_bundle_opens_to_prod_contMDiff (I := I) U

/-- Helper for Proposition 3.20: the inverse trivialization lemma, stated with the exact function
type expected by the diffeomorphism structure fields. -/
lemma tangent_bundle_opens_to_prod_symm_contMDiff_field :
    ContMDiff (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I.tangent ∞
      (show U × EuclideanSpace ℝ (Fin n) → TangentBundle I U from
        (TotalSpace.toProd U (EuclideanSpace ℝ (Fin n))).symm) := by
  -- This wrapper only matches the exact field elaboration expected in the diffeomorphism record.
  simpa [TangentBundle, TotalSpace.toProd]
    using tangent_bundle_opens_to_prod_symm_contMDiff (I := I) U

/-- Proposition 3.20: if a smooth `n`-manifold with or without boundary admits a single global
smooth chart, encoded canonically as a diffeomorphism onto an open subset of the model space, then
its tangent bundle is diffeomorphic to `M × ℝ^n`. -/
def tangentBundle_diffeomorphic_prod_of_global_chart
    (e : M ≃ₘ⟮I, I⟯ U) :
    TangentBundle I M ≃ₘ⟮I.tangent, I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      M × EuclideanSpace ℝ (Fin n) := by
  let hU :
      TangentBundle I U ≃ₘ⟮I.tangent, I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
        U × EuclideanSpace ℝ (Fin n) :=
    { toEquiv := TotalSpace.toProd U (EuclideanSpace ℝ (Fin n))
      -- The open-subset case is the textbook single-chart trivialization of the tangent bundle.
      contMDiff_toFun := tangent_bundle_opens_to_prod_contMDiff_field (I := I) U
      -- The inverse map is the corresponding smooth reconstruction from product coordinates.
      contMDiff_invFun := tangent_bundle_opens_to_prod_symm_contMDiff_field (I := I) U }
  exact
    (tangentMap_diffeomorph e).trans <|
      hU.trans <|
        e.symm.prodCongr <|
          Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin n)) (∞ : ℕ∞ω)

end GlobalChart

/-- The explicit-map version of a global chart: a smooth open embedding whose inverse is smooth on
its open image yields a diffeomorphism onto that open subset. -/
def globalChartDiffeomorph
    {e : M → H} (he : Topology.IsOpenEmbedding e) (hcont : ContMDiff I I ∞ e)
    (hsymm :
      let U : TopologicalSpace.Opens H := ⟨Set.range e, he.isOpen_range⟩
      let eHomeomorph : M ≃ₜ U :=
        (he.isEmbedding.toHomeomorph : M ≃ₜ Set.range e).trans <| Homeomorph.setCongr rfl
      ContMDiff I I ∞ eHomeomorph.symm) :
    let U : TopologicalSpace.Opens H := ⟨Set.range e, he.isOpen_range⟩
    M ≃ₘ⟮I, I⟯ U := by
  let U : TopologicalSpace.Opens H := ⟨Set.range e, he.isOpen_range⟩
  let eHomeomorph : M ≃ₜ U :=
    (he.isEmbedding.toHomeomorph : M ≃ₜ Set.range e).trans <| Homeomorph.setCongr rfl
  refine
    { toEquiv := eHomeomorph.toEquiv
      contMDiff_toFun := by
        have hcomp : Subtype.val ∘ eHomeomorph = e := by
          ext x
          rfl
        refine (ContMDiff.subtypeVal_comp_iff U eHomeomorph).mp ?_
        rw [hcomp]
        exact hcont
      contMDiff_invFun := by
        simpa [U, eHomeomorph] using hsymm }

/-- Proposition 3.20, explicit-map form: a smooth open embedding into the model space whose
inverse is smooth on its image gives the tangent-bundle trivialization `TM ≃ M × ℝ^n`. -/
def tangentBundle_diffeomorphic_prod_of_global_chart_map
    {e : M → H} (he : Topology.IsOpenEmbedding e) (hcont : ContMDiff I I ∞ e)
    (hsymm :
      let U : TopologicalSpace.Opens H := ⟨Set.range e, he.isOpen_range⟩
      let eHomeomorph : M ≃ₜ U :=
        (he.isEmbedding.toHomeomorph : M ≃ₜ Set.range e).trans <| Homeomorph.setCongr rfl
      ContMDiff I I ∞ eHomeomorph.symm) :
    TangentBundle I M ≃ₘ⟮I.tangent, I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      M × EuclideanSpace ℝ (Fin n) :=
  by
    let U : TopologicalSpace.Opens H := ⟨Set.range e, he.isOpen_range⟩
    exact tangentBundle_diffeomorphic_prod_of_global_chart U
      (globalChartDiffeomorph he hcont hsymm)
