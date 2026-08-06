import Mathlib.Logic.Equiv.Fin.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

universe u v w

variable {X : Type u} [TopologicalSpace X]

private instance singletonPathToSetTopologicalSpace (x : X) :
    TopologicalSpace (PathToSet ({x} : Set X) x) :=
  PathToSet.instTopologicalSpace ({x} : Set X) ⟨x, by simp⟩

private theorem singletonPathToSet_endpoint_eq {x : X} (γ : PathToSet ({x} : Set X) x) :
    γ.endpoint.1 = x := by
  rcases γ.endpoint with ⟨y, hy⟩
  simpa using hy

private def singletonPathToLoopSpaceHomeomorph (x : X) :
    PathToSet ({x} : Set X) x ≃ₜ Ω X x where
  toFun γ :=
    Path.mk γ.path.toContinuousMap γ.path.source
      (γ.path.target.trans (singletonPathToSet_endpoint_eq γ))
  invFun γ :=
    { endpoint := ⟨x, by simp⟩
      path := γ }
  left_inv γ := by
    cases γ with
    | mk endpoint path =>
        cases endpoint with
        | mk y hy =>
            cases Set.mem_singleton_iff.mp hy
            rfl
  right_inv γ := rfl
  continuous_toFun := by
    rw [continuous_induced_rng]
    change Continuous fun γ : PathToSet ({x} : Set X) x ↦ γ.path.toContinuousMap
    exact
      (continuous_snd : Continuous fun z : ({x} : Set X) × C(I, X) ↦ z.2).comp
        (continuous_induced_dom : Continuous
          (PathToSet.endpointAndPath ({x} : Set X) ⟨x, by simp⟩))
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous fun γ : Ω X x ↦
      ((⟨x, by simp⟩ : ({x} : Set X)), γ.toContinuousMap)
    exact continuous_const.prodMk
      (continuous_induced_dom : Continuous fun γ : Ω X x ↦ γ.toContinuousMap)

@[simp] private theorem singletonPathToLoopSpaceHomeomorph_apply_refl (x : X) :
    singletonPathToLoopSpaceHomeomorph x (PathToSet.refl ⟨x, by simp⟩) = Path.refl x :=
  rfl

private def oneGenLoopHomeomorph (x : X) : Ω^ (Fin 1) X x ≃ₜ Ω X x where
  toFun p :=
    Path.mk ⟨fun t ↦ p (fun _ ↦ t), by fun_prop⟩
      (p.2 (fun _ ↦ 0) ⟨0, Or.inl rfl⟩)
      (p.2 (fun _ ↦ 1) ⟨0, Or.inr rfl⟩)
  invFun γ :=
    ⟨⟨fun t ↦ γ (t 0), by fun_prop⟩, fun t ht ↦ by
      rcases ht with ⟨i, hi | hi⟩
      · have hi0 : t 0 = 0 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = x := γ.source
      · have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = x := γ.target⟩
  left_inv p := by
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
    ext t
    rfl
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t _ ↦ t, by fun_prop⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t : I^(Fin 1) ↦ t 0, by fun_prop⟩).comp continuous_induced_dom

@[simp] private theorem oneGenLoopHomeomorph_symm_refl (x : X) :
    (oneGenLoopHomeomorph x).symm (Path.refl x) = GenLoop.const := by
  ext t
  rfl

private def genLoopHomeomorph {M : Type v} {Y : Type u} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z) :
    Ω^ M Y y ≃ₜ Ω^ M Z z where
  toFun p :=
    ⟨⟨fun t ↦ h (p t), h.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      simpa [hy] using congrArg h (p.2 t ht)⟩
  invFun p :=
    ⟨⟨fun t ↦ h.symm (p t), (h.symm.continuous).comp p.1.continuous⟩, fun t ht ↦ by
      have hp : p t = z := p.2 t ht
      calc
        h.symm (p t) = h.symm z := by rw [hp]
        _ = y := (h.symm_apply_eq).2 hy.symm⟩
  left_inv p := by
    ext t
    simp
  right_inv p := by
    ext t
    simp
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact (ContinuousMap.continuous_postcomp ⟨h, h.continuous⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_postcomp ⟨h.symm, h.symm.continuous⟩).comp
        continuous_subtype_val

private theorem genLoopHomeomorph_respects {M : Type v} {Y : Type u} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z)
    {p q : Ω^ M Y y} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopHomeomorph h hy p) (genLoopHomeomorph h hy q) := by
  change (genLoopHomeomorph h hy p).1.HomotopicRel (genLoopHomeomorph h hy q).1 (Cube.boundary M)
  simpa [genLoopHomeomorph, GenLoop.Homotopic] using
    ContinuousMap.HomotopicRel.comp_continuousMap hpq ⟨h, h.continuous⟩

private theorem genLoopHomeomorph_symm_respects {M : Type v} {Y : Type u} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z)
    {p q : Ω^ M Z z} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic
      ((genLoopHomeomorph h hy).symm p)
      ((genLoopHomeomorph h hy).symm q) := by
  have hsymm : h.symm z = y := by
    exact (h.symm_apply_eq).2 hy.symm
  simpa [genLoopHomeomorph] using
    genLoopHomeomorph_respects h.symm hsymm hpq

private def homotopyGroupHomeomorphEquiv {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z)
    (n : ℕ) : π_ n Y y ≃ π_ n Z z :=
  let e : Ω^ (Fin n) Y y ≃ₜ Ω^ (Fin n) Z z := genLoopHomeomorph h hy
  { toFun :=
      Quotient.map e (fun _ _ hpq ↦ genLoopHomeomorph_respects h hy hpq)
    invFun :=
      Quotient.map e.symm (fun _ _ hpq ↦ genLoopHomeomorph_symm_respects h hy hpq)
    left_inv := by
      intro p
      refine Quotient.inductionOn p ?_
      intro γ
      change Quotient.mk' (e.symm (e γ)) = Quotient.mk' γ
      congr
      ext t
      simp
    right_inv := by
      intro p
      refine Quotient.inductionOn p ?_
      intro γ
      change Quotient.mk' (e (e.symm γ)) = Quotient.mk' γ
      congr
      ext t
      simp }

private def loopSpaceRepresentativeEquiv (n : ℕ) (x : X) :
    Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ Ω^ (Fin (n + 1)) X x :=
  let e₁ : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
    GenLoop.genLoopGenLoopEquiv x
  let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Observation 9.6.5: generalized-loop homotopies are exactly paths in the
generalized-loop space. -/
private theorem genLoopHomotopic_iff_joined
    {N : Type*} {Y : Type*} [TopologicalSpace Y] {y : Y} {p q : Ω^ N Y y} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    -- Curry the relative homotopy into a path through the generalized-loop space.
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun y hy ↦ (H.prop t y hy).trans (p.property y hy)⟩ :
            Ω^ N Y y),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t y hy
      exact (H.prop t y hy).trans (p.property y hy)
    · ext y
      exact H.apply_zero y
    · ext y
      exact H.apply_one y
  · rintro ⟨γ⟩
    -- Uncurry a path of generalized loops into a homotopy relative to the boundary.
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro a
      change γ 0 a = p a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.source
    · intro a
      change γ 1 a = q a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.target
    · intro t a ha
      exact ((γ t).property a ha).trans (p.property a ha).symm

/-- Helper for Observation 9.6.5: a homeomorphism preserves and reflects the path relation
`Joined`. -/
private theorem joined_iff_homeomorph
    {Y : Type*} {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {a b : Y} :
    Joined (h a) (h b) ↔ Joined a b := by
  constructor
  · rintro ⟨γ⟩
    -- Pull the path back along the inverse homeomorphism.
    simpa using (show Joined (h.symm (h a)) (h.symm (h b)) from ⟨γ.map h.symm.continuous⟩)
  · rintro ⟨γ⟩
    -- Push the path forward along the homeomorphism.
    exact ⟨γ.map h.continuous⟩

/-- Helper for Observation 9.6.5: a homeomorphism between generalized-loop spaces preserves and
reflects the `GenLoop.Homotopic` relation. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Ω^ M Y y ≃ₜ Ω^ N Z z) {p q : Ω^ M Y y} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate homotopies to paths, use the homeomorphism, then translate back.
  rw [genLoopHomotopic_iff_joined, genLoopHomotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Observation 9.6.5: the representative-level equivalence for the loop-space shift
preserves and reflects generalized-loop homotopy. -/
private theorem loopSpaceRepresentativeEquiv_homotopic_iff (n : ℕ) (x : X)
    {p q : Ω^ (Fin n) (Ω X x) (Path.refl x)} :
    GenLoop.Homotopic (loopSpaceRepresentativeEquiv n x p) (loopSpaceRepresentativeEquiv n x q) ↔
      GenLoop.Homotopic p q := by
  let e : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin (n + 1)) X x :=
    let e₁ : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
      genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
    let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
      GenLoop.genLoopGenLoopEquiv x
    let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
      GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    (e₁.trans e₂).trans e₃
  -- Route correction: descend the quotient through the composite homeomorphism via `Joined`.
  change GenLoop.Homotopic (e p) (e q) ↔ GenLoop.Homotopic p q
  exact genLoopHomotopic_iff_of_homeomorph e

private theorem loopSpaceRepresentativeEquiv_respects (n : ℕ) (x : X)
    {p q : Ω^ (Fin n) (Ω X x) (Path.refl x)} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (loopSpaceRepresentativeEquiv n x p) (loopSpaceRepresentativeEquiv n x q) :=
  by
    -- The representative map is relation-preserving because it is a homeomorphism of loop spaces.
    exact (loopSpaceRepresentativeEquiv_homotopic_iff n x).2 hpq

private theorem loopSpaceRepresentativeEquiv_symm_respects (n : ℕ) (x : X)
    {p q : Ω^ (Fin (n + 1)) X x} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic
      ((loopSpaceRepresentativeEquiv n x).symm p)
      ((loopSpaceRepresentativeEquiv n x).symm q) := by
  -- Apply the same relation-compatibility theorem to the inverse representatives.
  have himage :
      GenLoop.Homotopic
        (loopSpaceRepresentativeEquiv n x ((loopSpaceRepresentativeEquiv n x).symm p))
        (loopSpaceRepresentativeEquiv n x ((loopSpaceRepresentativeEquiv n x).symm q)) := by
    simpa using hpq
  exact
    (loopSpaceRepresentativeEquiv_homotopic_iff n x
      (p := (loopSpaceRepresentativeEquiv n x).symm p)
      (q := (loopSpaceRepresentativeEquiv n x).symm q)).1 himage

private def loopSpaceHomotopyGroupEquivPiSucc (n : ℕ) (x : X) :
    π_ n (Ω X x) (Path.refl x) ≃ π_ (n + 1) X x :=
  -- Descend the representative-level equivalence to the quotient using the homotopy iff lemma.
  Quotient.congr (loopSpaceRepresentativeEquiv n x) fun _ _ ↦
    (loopSpaceRepresentativeEquiv_homotopic_iff n x).symm

/-- Observation 9.6.5: after identifying `π_(n + 1) X x` with the positive-degree relative
homotopy group of the singleton pair `π_(n + 1)(X, {x}, x)`, the Chapter 9 owner carries the
source cone/sphere description of `π_(n + 1) X x`. -/
noncomputable def piSuccRelativeHomotopyGroupSingletonEquiv (n : ℕ) (x : X) :
    π_ (n + 1) X x ≃ relativeHomotopyGroup n.succPNat ({x} : Set X) ⟨x, by simp⟩ := by
  change π_ (n + 1) X x ≃
    π_ n (PathToSet ({x} : Set X) x) (PathToSet.refl ⟨x, by simp⟩)
  exact
    (loopSpaceHomotopyGroupEquivPiSucc n x).symm.trans
      (homotopyGroupHomeomorphEquiv
        (singletonPathToLoopSpaceHomeomorph x)
        (singletonPathToLoopSpaceHomeomorph_apply_refl x)
        n).symm
