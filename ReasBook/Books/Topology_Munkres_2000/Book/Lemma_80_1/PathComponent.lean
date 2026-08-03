module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Lifting

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  [PathConnectedSpace B] [LocallyPathConnectedSpace B]

/-- Helper for Lemma 80.1: varying the base coordinate inside a path-connected
trivialization does not leave the path component of a point. -/
private lemma trivializationSymm_mem_pathComponent {F : Type*} [TopologicalSpace F]
    {p : E → B} (t : Bundle.Trivialization F p) (e₀ z : E) {V : Set B}
    (hV : IsPathConnected V) (hVt : V ⊆ t.baseSet) (hz : z ∈ pathComponent e₀)
    (hpz : p z ∈ V) {y : B} (hy : y ∈ V) :
    t.toOpenPartialHomeomorph.symm (y, (t z).2) ∈ pathComponent e₀ := by
  -- Map a path in the base set through the inverse of the fixed sheet coordinate.
  have hjoined :=
    (hV.joinedIn (p z) hpz y hy).map_continuousOn
      (f := fun x ↦ t.toOpenPartialHomeomorph.symm (x, (t z).2))
      ((t.continuousOn_symm_prodMk_left (v := (t z).2)).mono hVt)
  rw [t.symm_apply_mk_proj (t.mem_source.mpr (hVt hpz))] at hjoined
  -- Its image path joins `z` to the requested point in the same sheet.
  exact hjoined.joined.mem_pathComponent hz

/-- Helper for Lemma 80.1: a path-connected part of a covering trivialization
evenly covers the restriction to a chosen path component. -/
private lemma isEvenlyCovered_restrictPathComponent {F : Type*} [TopologicalSpace F]
    [DiscreteTopology F] {p : E → B} (hp : IsCoveringMap p)
    (t : Bundle.Trivialization F p) (e₀ : E) {b : B} {V : Set B}
    (hVopen : IsOpen V) (hbV : b ∈ V) (hV : IsPathConnected V)
    (hVt : V ⊆ t.baseSet) :
    IsEvenlyCovered (fun x : pathComponent e₀ ↦ p x) b
      ((fun x : pathComponent e₀ ↦ p x) ⁻¹' {b}) := by
  let q : pathComponent e₀ → B := fun x ↦ p x
  let F₀ := {i : F // ∀ y ∈ V,
    t.toOpenPartialHomeomorph.symm (y, i) ∈ pathComponent e₀}
  -- A point over `V` determines the coordinate of its entire local sheet.
  let toFun : q ⁻¹' V → V × F₀ := fun x ↦
    (⟨q x, x.2⟩, ⟨(t x.1.1).2, fun y hy ↦
      trivializationSymm_mem_pathComponent t e₀ x.1.1 hV hVt x.1.2 x.2 hy⟩)
  let invMem (x : V × F₀) :
      p (t.toOpenPartialHomeomorph.symm (x.1.1, x.2.1)) ∈ V :=
    (t.proj_symm_apply' (hVt x.1.2)).symm ▸ x.1.2
  let invFun : V × F₀ → q ⁻¹' V := fun x ↦
    ⟨⟨t.toOpenPartialHomeomorph.symm (x.1.1, x.2.1), x.2.2 x.1.1 x.1.2⟩, invMem x⟩
  -- Both composites reduce through the named inverse laws of the trivialization.
  have leftInv : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact t.symm_apply_mk_proj (t.mem_source.mpr (hVt x.2))
  have rightInv : Function.RightInverse invFun toFun := by
    intro x
    apply Prod.ext
    · apply Subtype.ext
      exact t.proj_symm_apply' (hVt x.1.2)
    · apply Subtype.ext
      exact congrArg Prod.snd (t.apply_symm_apply' (hVt x.1.2))
  -- Continuity of the forward map comes from the original local trivialization.
  have hval : Continuous (fun x : q ⁻¹' V ↦ (x.1.1 : E)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have htapp : Continuous (fun x : q ⁻¹' V ↦ t x.1.1) :=
    t.continuousOn_toFun.comp_continuous hval fun x ↦ t.mem_source.mpr (hVt x.2)
  have continuousToFun : Continuous toFun := by
    exact (Continuous.subtype_mk (hp.continuous.comp hval) _).prodMk
      (Continuous.subtype_mk (continuous_snd.comp htapp) _)
  -- The inverse map is the restriction of the continuous inverse trivialization.
  have hpair : Continuous (fun x : V × F₀ ↦ (x.1.1, x.2.1)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hinv : Continuous (fun x : V × F₀ ↦
      t.toOpenPartialHomeomorph.symm (x.1.1, x.2.1)) :=
    t.continuousOn_invFun.comp_continuous hpair fun x ↦
      t.mem_target.mpr (hVt x.1.2)
  have continuousInvFun : Continuous invFun := by
    exact Continuous.subtype_mk (Continuous.subtype_mk hinv _) _
  let H : q ⁻¹' V ≃ₜ V × F₀ :=
    { toFun := toFun
      invFun := invFun
      left_inv := leftInv
      right_inv := rightInv
      continuous_toFun := continuousToFun
      continuous_invFun := continuousInvFun }
  -- Package the homeomorphism, then convert its discrete coordinate to the canonical fiber.
  have hcovered : IsEvenlyCovered q b F₀ := by
    refine ⟨inferInstance, V, hbV, hVopen, ?_, H, ?_⟩
    · exact hVopen.preimage (hp.continuous.comp continuous_subtype_val)
    · intro x
      rfl
  simpa [q] using hcovered.to_isEvenlyCovered_preimage

/-- The restriction of a covering map to the path component of any point of its
domain is surjective onto a path-connected, locally path-connected base. -/
theorem surjective_restrictPathComponent {p : E → B} (hp : IsCoveringMap p) (e₀ : E) :
    Function.Surjective (fun x : pathComponent e₀ ↦ p x) := by
  intro b
  let γ := PathConnectedSpace.somePath (p e₀) b
  have hγ : γ 0 = p e₀ := by simp [γ]
  let Γ := hp.liftPath γ e₀ hγ
  -- The lifted path keeps its endpoint in the component of the chosen point.
  have hΓ : Γ 1 ∈ pathComponent e₀ := by
    rw [mem_pathComponent_iff]
    exact ⟨⟨Γ, hp.liftPath_zero γ e₀ hγ, rfl⟩⟩
  refine ⟨⟨Γ 1, hΓ⟩, ?_⟩
  -- At the right endpoint, the lifting equation is exactly the desired fiber equation.
  simpa [γ] using congr_fun (hp.liftPath_lifts γ e₀ hγ) 1

/-- A covering map restricts to a covering map on the path component of any point
of its domain when the base is path connected and locally path connected. -/
theorem restrictPathComponent {p : E → B} (hp : IsCoveringMap p) (e₀ : E) :
    IsCoveringMap (fun x : pathComponent e₀ ↦ p x) := by
  intro b
  -- Surjectivity supplies a point in the original fiber, so its canonical trivialization exists.
  obtain ⟨x, hx⟩ := hp.surjective_restrictPathComponent e₀ b
  letI : Nonempty (p ⁻¹' {b}) := ⟨⟨x.1, hx⟩⟩
  letI : DiscreteTopology (p ⁻¹' {b}) := (hp b).1
  let t := (hp b).toTrivialization
  have hbt : b ∈ t.baseSet := (hp b).mem_toTrivialization_baseSet
  -- Shrink the original evenly-covered neighborhood to an open path-connected one.
  obtain ⟨V, ⟨hVopen, hbV, hV⟩, hVt⟩ :=
    (isOpen_isPathConnected_basis b).mem_iff.mp (t.open_baseSet.mem_nhds hbt)
  -- The sheet-coordinate construction now gives the required restricted trivialization.
  exact isEvenlyCovered_restrictPathComponent hp t e₀ hVopen hbV hV hVt

end IsCoveringMap
