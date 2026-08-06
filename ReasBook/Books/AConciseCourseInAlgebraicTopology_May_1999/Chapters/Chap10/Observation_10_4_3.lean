import Mathlib.Logic.Equiv.Fin.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open scoped Topology Topology.Homotopy unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: no built-in owner for `n`-connected pairs surfaced in
-- the current environment. The source-facing owners `NConnectedPair` and `IsNEquivalence` match
-- the source directly, so this item is formalized as the bridge between them for the subtype
-- inclusion `A ↪ X`.

noncomputable section

/-- Helper for Observation 10.4.3: generalized-loop homotopies are exactly paths in the
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
          (⟨curriedHomotopy t, fun a ha ↦ (H.prop t a ha).trans (p.property a ha)⟩ :
            Ω^ N Y y),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t a ha
      exact (H.prop t a ha).trans (p.property a ha)
    · ext a
      exact H.apply_zero a
    · ext a
      exact H.apply_one a
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

/-- Helper for Observation 10.4.3: a homeomorphism preserves and reflects the path relation
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

/-- Helper for Observation 10.4.3: a homeomorphism between generalized-loop spaces preserves and
reflects the `GenLoop.Homotopic` relation. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Ω^ M Y y ≃ₜ Ω^ N Z z) {p q : Ω^ M Y y} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate homotopies to paths, use the homeomorphism, then translate back.
  rw [genLoopHomotopic_iff_joined, genLoopHomotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Observation 10.4.3: `Fin 1`-indexed generalized loops are the ordinary loop
space. -/
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

/-- Helper for Observation 10.4.3: the inverse of the `Fin 1` loop-homeomorphism sends the
constant loop to the constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl (x : X) :
    (oneGenLoopHomeomorph x).symm (Path.refl x) = GenLoop.const := by
  ext t
  rfl

/-- Helper for Observation 10.4.3: a homeomorphism of spaces induces a homeomorphism on
generalized-loop spaces. -/
private def genLoopHomeomorph {M : Type*} {Y : Type*} {Z : Type*}
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

/-- Helper for Observation 10.4.3: iterated loops on the loop space identify with the next
ordinary iterated loop space. -/
private def loopSpaceRepresentativeHomeomorph (n : ℕ) (x : X) :
    Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin (n + 1)) X x :=
  let e₁ : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
    GenLoop.genLoopGenLoopEquiv x
  let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Observation 10.4.3: the standard loop-space shift descends to an equivalence on
homotopy groups. -/
private def loopSpaceHomotopyGroupEquivPiSucc (n : ℕ) (x : X) :
    π_ n (Ω X x) (Path.refl x) ≃ π_ (n + 1) X x :=
  Quotient.congr (loopSpaceRepresentativeHomeomorph n x) fun _ _ ↦
    (genLoopHomotopic_iff_of_homeomorph (loopSpaceRepresentativeHomeomorph n x)).symm

/-- Helper for Observation 10.4.3: applying the loop-space shift equivalence sends a class to the
class of the shifted representative. -/
@[simp] private theorem loopSpaceHomotopyGroupEquivPiSucc_apply
    (n : ℕ) (x : X) (γ : Ω^ (Fin n) (Ω X x) (Path.refl x)) :
    loopSpaceHomotopyGroupEquivPiSucc n x ⟦γ⟧ =
      (⟦loopSpaceRepresentativeHomeomorph n x γ⟧ : π_ (n + 1) X x) :=
  rfl

/-- Helper for Observation 10.4.3: the representative-level loop-space shift commutes with the
subtype inclusion. -/
private theorem loopSpaceRepresentativeHomeomorph_subtypeInclusion
    (A : Set X) (x : A) (n : ℕ)
    (γ : Ω^ (Fin n) (Ω A x) (Path.refl x)) :
    loopSpaceRepresentativeHomeomorph n x.1
        (genLoopMap (pairLoopSubspaceInclusionMap A x) γ) =
      genLoopMap (pairSubspaceInclusion A)
        (loopSpaceRepresentativeHomeomorph n x γ) := by
  ext t
  rfl

/-- Helper for Observation 10.4.3: the tail `π₀` model from Theorem 9.2.2 is definitionally the
degree-`1` relative homotopy group. -/
theorem pairRelativePiZeroHomotopyGroup_eq_relativePiOne (A : Set X) (x : A) :
    pairRelativePiZeroHomotopyGroup A x = relativeHomotopyGroup 1 A x :=
  rfl

/-- Helper for Observation 10.4.3: trivial relative `π₁(X, A, x)` makes the tail `π₀` model
subsingleton. -/
theorem pairRelativePiZeroSubsingleton_of_relativePiOneSubsingleton
    (A : Set X) (x : A)
    [Subsingleton (relativeHomotopyGroup 1 A x)] :
    Subsingleton (pairRelativePiZeroHomotopyGroup A x) := by
  -- The two Chapter 9 owners are definitionally the same type in degree `1`.
  simpa [pairRelativePiZeroHomotopyGroup_eq_relativePiOne (A := A) (x := x)] using
    (inferInstance : Subsingleton (relativeHomotopyGroup 1 A x))

/-- Helper for Observation 10.4.3: surjective `π₀(A) → π₀(X)` and trivial relative `π₁(X, A, x)`
force `π₀(A) → π₀(X)` to be injective. -/
theorem zerothHomotopyInclusion_injective_of_surjective_and_relativePiOneSubsingleton
    (A : Set X)
    (h0 : Function.Surjective (zerothHomotopyInclusion A))
    (hrel : ∀ x : A, Subsingleton (relativeHomotopyGroup 1 A x)) :
    Function.Injective (zerothHomotopyInclusion A) := by
  intro a₀ b₀ hab
  rcases h0 (zerothHomotopyInclusion A a₀) with ⟨c, hc⟩
  rcases Quotient.exists_rep c with ⟨x, rfl⟩
  have ha :
      zerothHomotopyInclusion A a₀ = ⟦(x : X)⟧ := by
    -- Rewrite the chosen preimage component by a concrete representative.
    simpa [zerothHomotopyInclusion_mk] using hc.symm
  have hb :
      zerothHomotopyInclusion A b₀ = ⟦(x : X)⟧ := by
    -- The two source components have the same ambient image by assumption.
    exact hab.symm.trans ha
  have hpair : Subsingleton (pairRelativePiZeroHomotopyGroup A x) := by
    -- The tail `π₀` relative term is just `relativeHomotopyGroup 1 A x`.
    let _ : Subsingleton (relativeHomotopyGroup 1 A x) := hrel x
    exact pairRelativePiZeroSubsingleton_of_relativePiOneSubsingleton A x
  rcases (pairHomotopyLongExactSequenceTail_exact_boundary_to_piZero A x a₀).mp ha with ⟨r₀, hr₀⟩
  rcases (pairHomotopyLongExactSequenceTail_exact_boundary_to_piZero A x b₀).mp hb with ⟨r₁, hr₁⟩
  have hr : r₀ = r₁ := Subsingleton.elim _ _
  -- Equal relative classes have equal boundary images in `π₀(A)`.
  simpa [hr₀, hr₁] using congrArg (pairHomotopyBoundaryZeroMap A x) hr

/-- Helper for Observation 10.4.3: injective `π₀(A) → π₀(X)` together with surjective
`π₁(A, x) → π₁(X, x)` collapses the relative `π₁(X, A, x)` term. -/
theorem relativePiOneSubsingleton_of_piZeroInjective_and_loopPiOneSurjective
    (A : Set X)
    (hπ0 : Function.Injective (zerothHomotopyInclusion A))
    (hπ1 : ∀ x : A, Function.Surjective (pairLoopSubspaceInclusionPiZeroMap A x)) :
    ∀ x : A, Subsingleton (relativeHomotopyGroup 1 A x) := by
  intro x
  have hpair : Subsingleton (pairRelativePiZeroHomotopyGroup A x) := by
    refine ⟨fun r s ↦ ?_⟩
    have hrBoundaryAmbient :
        zerothHomotopyInclusion A (pairHomotopyBoundaryZeroMap A x r) = ⟦(x : X)⟧ := by
      -- Every boundary value lands in the ambient component of the basepoint.
      exact
        (pairHomotopyLongExactSequenceTail_exact_boundary_to_piZero A x
          (pairHomotopyBoundaryZeroMap A x r)).mpr ⟨r, rfl⟩
    have hsBoundaryAmbient :
        zerothHomotopyInclusion A (pairHomotopyBoundaryZeroMap A x s) = ⟦(x : X)⟧ := by
      -- The same exactness statement applies to any other relative class.
      exact
        (pairHomotopyLongExactSequenceTail_exact_boundary_to_piZero A x
          (pairHomotopyBoundaryZeroMap A x s)).mpr ⟨s, rfl⟩
    have hrBoundary :
        pairHomotopyBoundaryZeroMap A x r = ⟦x⟧ := by
      -- Injectivity of `π₀(A) → π₀(X)` forces the boundary to be the base component.
      apply hπ0
      simpa [zerothHomotopyInclusion_mk] using hrBoundaryAmbient
    have hsBoundary :
        pairHomotopyBoundaryZeroMap A x s = ⟦x⟧ := by
      -- The same argument works for `s`.
      apply hπ0
      simpa [zerothHomotopyInclusion_mk] using hsBoundaryAmbient
    rcases (pairHomotopyLongExactSequenceTail_exact_ambient_to_relative A x r).mp hrBoundary with
      ⟨gr, hgr⟩
    rcases (pairHomotopyLongExactSequenceTail_exact_ambient_to_relative A x s).mp hsBoundary with
      ⟨gs, hgs⟩
    rcases hπ1 x gr with ⟨ar, har⟩
    rcases hπ1 x gs with ⟨as, has⟩
    have hgrBase :
        pairLoopToRelativePiZeroMap A x gr = pairRelativePiZeroBasepoint A x := by
      -- Exactness identifies the image of the subspace-loop map with the kernel.
      exact
        (pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient A x gr).mpr ⟨ar, har⟩
    have hgsBase :
        pairLoopToRelativePiZeroMap A x gs = pairRelativePiZeroBasepoint A x := by
      -- The second chosen ambient loop lies in the same kernel for the same reason.
      exact
        (pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient A x gs).mpr ⟨as, has⟩
    calc
      r = pairRelativePiZeroBasepoint A x := by simpa [hgr] using hgrBase
      _ = s := by simpa [hgs] using hgsBase.symm
  -- Transport the tail `π₀` model back to the textbook degree-`1` relative group.
  simpa [pairRelativePiZeroHomotopyGroup_eq_relativePiOne (A := A) (x := x)] using hpair

/-- Helper for Observation 10.4.3: the Chapter 10 owner and the pair-LES owner use the same
inclusion-induced map on based homotopy groups. -/
theorem subtypeInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap
    (A : Set X) (x : A) (q : ℕ) :
    ((TopCat.subtypeInclusion A).hom).eStar q x = pairSubspaceInclusionHomotopyGroupMap A x q := by
  -- Both sides are induced by the same continuous inclusion `A ↪ X`.
  funext y
  rfl

/-- Helper for Observation 10.4.3: under the canonical `π₀ ≃ ZerothHomotopy` identifications,
the degree-`0` map induced by `A ↪ X` is `zerothHomotopyInclusion A`. -/
theorem subtypeInclusionPiZero_commutes (A : Set X) (x : A) :
    (HomotopyGroup.pi0EquivZerothHomotopy :
        π_ 0 X x.1 ≃ ZerothHomotopy X).toFun ∘
        ((TopCat.subtypeInclusion A).hom).eStar 0 x =
      zerothHomotopyInclusion A ∘
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A).toFun := by
  -- Both sides send a generalized-loop class to the ambient path component of its endpoint.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Observation 10.4.3: the tail `π₀(Ω-) ≃ π₁(-)` identification carries the loop-space
subtype-inclusion map to the ordinary degree-`1` inclusion map. -/
theorem pairLoopPiZero_commutes_withSubtypeInclusionPiOne
    (A : Set X) (x : A) :
    (loopSpaceHomotopyGroupEquivPiSucc 0 x.1).toFun ∘
        pairLoopSubspaceInclusionPiZeroMap A x =
      pairSubspaceInclusionHomotopyGroupMap A x 1 ∘
        (loopSpaceHomotopyGroupEquivPiSucc 0 x).toFun := by
  -- Compare both induced maps on loop representatives before passing to the quotient.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  simp [pairLoopSubspaceInclusionPiZeroMap,
    pairSubspaceInclusionHomotopyGroupMap,
    loopSpaceRepresentativeHomeomorph_subtypeInclusion]

/-- Helper for Observation 10.4.3: the higher loop-space model from Theorem 9.2.2 agrees with the
ordinary inclusion-induced map after the standard loop-space shift equivalence. -/
theorem pairLoopSubspaceInclusion_commutes_withSubtypeInclusionPiSucc
    (A : Set X) (x : A) (q : ℕ) :
    (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1).toFun ∘
        pairLoopSubspaceInclusionHomotopyGroupMap A x q =
      pairSubspaceInclusionHomotopyGroupMap A x (q + 2) ∘
        (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x).toFun := by
  -- Compare both induced maps on iterated-loop representatives before quotienting.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  simp [pairLoopSubspaceInclusionHomotopyGroupMap,
    pairSubspaceInclusionHomotopyGroupMap,
    loopSpaceRepresentativeHomeomorph_subtypeInclusion]

/-- Helper for Observation 10.4.3: surjectivity in degree `q + 2` and injectivity in degree
`q + 1` force the relative group `π_(q + 2)(X, A, x)` to be trivial. -/
theorem relativeHomotopyGroupSubsingleton_of_inclusionSurjective_inclusionInjective
    (A : Set X) (q : ℕ)
    (hsurj : ∀ x : A, Function.Surjective (pairSubspaceInclusionHomotopyGroupMap A x (q + 2)))
    (hinj : ∀ x : A, Function.Injective (pairSubspaceInclusionHomotopyGroupMap A x (q + 1))) :
    ∀ x : A, Subsingleton (relativeHomotopyGroup (q + 1).succPNat A x) := by
  intro x
  refine ⟨fun r s ↦ ?_⟩
  have hloopSurj :
      Function.Surjective (pairLoopSubspaceInclusionHomotopyGroupMap A x q) := by
    intro g
    let g' := loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1 g
    rcases hsurj x g' with ⟨a', ha'⟩
    refine ⟨(loopSpaceHomotopyGroupEquivPiSucc (q + 1) x).symm a', ?_⟩
    apply (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1).injective
    calc
      loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1
          (pairLoopSubspaceInclusionHomotopyGroupMap A x q
            ((loopSpaceHomotopyGroupEquivPiSucc (q + 1) x).symm a')) =
        pairSubspaceInclusionHomotopyGroupMap A x (q + 2) a' := by
          simpa using
            congrFun
              (pairLoopSubspaceInclusion_commutes_withSubtypeInclusionPiSucc A x q)
              ((loopSpaceHomotopyGroupEquivPiSucc (q + 1) x).symm a')
      _ = g' := ha'
      _ = loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1 g := rfl
  have hr1 : r = 1 := by
    have hboundary :
        pairHomotopyBoundaryMap A x q r = 1 := by
      apply hinj x
      exact (pairHomotopyLongExactSequenceBoundaryToSubspace A x q).apply_apply_eq_one r
    rcases ((pairHomotopyLongExactSequenceAmbientToRelative A x q) r).mp hboundary with ⟨g, hg⟩
    rcases hloopSurj g with ⟨a, ha⟩
    have hbase : pairLoopToRelativeHomotopyGroupMap A x q g = 1 := by
      exact (pairHomotopyLongExactSequenceSubspaceToAmbient A x q g).mpr ⟨a, ha⟩
    simpa [hg] using hbase
  have hs1 : s = 1 := by
    have hboundary :
        pairHomotopyBoundaryMap A x q s = 1 := by
      apply hinj x
      exact (pairHomotopyLongExactSequenceBoundaryToSubspace A x q).apply_apply_eq_one s
    rcases ((pairHomotopyLongExactSequenceAmbientToRelative A x q) s).mp hboundary with ⟨g, hg⟩
    rcases hloopSurj g with ⟨a, ha⟩
    have hbase : pairLoopToRelativeHomotopyGroupMap A x q g = 1 := by
      exact (pairHomotopyLongExactSequenceSubspaceToAmbient A x q g).mpr ⟨a, ha⟩
    simpa [hg] using hbase
  -- Once both elements are equal to the identity, the relative group is subsingleton.
  simpa [hr1, hs1]

/-- Helper for Observation 10.4.3: surjectivity of `zerothHomotopyInclusion A` transports to the
degree-`0` homotopy-group map of the subtype inclusion. -/
private theorem subtypeInclusionPiZeroSurjective_of_zerothHomotopySurjective
    (A : Set X) (x : A) (h0 : Function.Surjective (zerothHomotopyInclusion A)) :
    Function.Surjective (((TopCat.subtypeInclusion A).hom).eStar 0 x) := by
  intro g
  rcases h0
      ((HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X) g) with
    ⟨a₀, ha₀⟩
  rcases (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A).surjective a₀ with
    ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  -- Compare the chosen preimage after transporting both sides through `π₀ ≃ ZerothHomotopy`.
  apply (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X).injective
  calc
    (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X)
        (((TopCat.subtypeInclusion A).hom).eStar 0 x a) =
      zerothHomotopyInclusion A
        ((HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A) a) := by
          simpa using congrFun (subtypeInclusionPiZero_commutes A x) a
    _ =
      (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X) g := ha₀

/-- Helper for Observation 10.4.3: injectivity of the subtype-inclusion map on `π₀` is exactly
injectivity of `zerothHomotopyInclusion A`. -/
private theorem subtypeInclusionPiZeroInjective_iff_zerothHomotopyInclusionInjective
    (A : Set X) (x : A) :
    Function.Injective (((TopCat.subtypeInclusion A).hom).eStar 0 x) ↔
      Function.Injective (zerothHomotopyInclusion A) := by
  constructor
  · intro hπ0 a b hab
    rcases (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A).surjective a with
      ⟨a', rfl⟩
    rcases (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A).surjective b with
      ⟨b', rfl⟩
    -- Pull the `ZerothHomotopy` equality back through the commuting square and use injectivity on
    -- `π₀`.
    exact
      congrArg
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A) <|
        hπ0 <|
          (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X).injective <|
            calc
              (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X)
                  (((TopCat.subtypeInclusion A).hom).eStar 0 x a') =
                zerothHomotopyInclusion A
                  ((HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A) a') := by
                    simpa using congrFun (subtypeInclusionPiZero_commutes A x) a'
              _ =
                zerothHomotopyInclusion A
                  ((HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A) b') := hab
              _ =
                (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X)
                  (((TopCat.subtypeInclusion A).hom).eStar 0 x b') := by
                    simpa using (congrFun (subtypeInclusionPiZero_commutes A x) b').symm
  · intro h0 a b hab
    -- Push the `π₀` equality forward through the same square and use injectivity on
    -- path components.
    apply (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A).injective
    apply h0
    calc
      zerothHomotopyInclusion A
          ((HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A) a) =
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X)
          (((TopCat.subtypeInclusion A).hom).eStar 0 x a) := by
            simpa using (congrFun (subtypeInclusionPiZero_commutes A x) a).symm
      _ =
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x.1 ≃ ZerothHomotopy X)
          (((TopCat.subtypeInclusion A).hom).eStar 0 x b) := by rw [hab]
      _ =
        zerothHomotopyInclusion A
          ((HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A) b) := by
            simpa using congrFun (subtypeInclusionPiZero_commutes A x) b

/-- Helper for Observation 10.4.3: the connectivity data of the pair `(X, A)` yields the
`n`-equivalence data for the subtype inclusion `A ↪ X`. -/
private theorem isNEquivalence_subtypeInclusion_of_nConnectedPair_data
    (A : Set X) (n : ℕ)
    (h0 : Function.Surjective (zerothHomotopyInclusion A))
    (hrel : ∀ {q : ℕ+}, (q : ℕ) ≤ n → ∀ a : A, Subsingleton (relativeHomotopyGroup q A a)) :
    IsNEquivalence n (TopCat.subtypeInclusion A).hom := by
  refine ⟨?_, ?_⟩
  · intro x q hq
    cases q with
    | zero =>
        -- Degree `0` injectivity comes from the tail exact sequence and trivial relative `π₁`.
        have hπ0 :
            Function.Injective (zerothHomotopyInclusion A) :=
          zerothHomotopyInclusion_injective_of_surjective_and_relativePiOneSubsingleton A h0
            (fun a ↦ hrel (q := 1) (Nat.succ_le_of_lt hq) a)
        exact
          (subtypeInclusionPiZeroInjective_iff_zerothHomotopyInclusionInjective A x).2 hπ0
    | succ m =>
        intro a b hab
        have hq' : m + 2 ≤ n := Nat.succ_le_of_lt hq
        have hkernel :
            pairSubspaceInclusionHomotopyGroupMap A x (m + 1) (a * b⁻¹) = 1 := by
          -- Rewrite the inclusion-induced map as the bundled homomorphism on positive homotopy
          -- groups so `map_div` applies directly.
          rw [← subtypeInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap A x (m + 1)]
          change (((TopCat.subtypeInclusion A).hom).eStarMulHom m x) (a * b⁻¹) = 1
          calc
            (((TopCat.subtypeInclusion A).hom).eStarMulHom m x) (a * b⁻¹) =
              (((TopCat.subtypeInclusion A).hom).eStarMulHom m x) a /
                (((TopCat.subtypeInclusion A).hom).eStarMulHom m x) b := by
                  simpa [div_eq_mul_inv] using
                    (((TopCat.subtypeInclusion A).hom).eStarMulHom m x).map_div a b
            _ = 1 := by
              have habe :
                  (((TopCat.subtypeInclusion A).hom).eStarMulHom m x) a =
                    (((TopCat.subtypeInclusion A).hom).eStarMulHom m x) b := by
                simpa using hab
              rw [habe]
              simp
        rcases
            ((pairHomotopyLongExactSequenceBoundaryToSubspace A x m) (a * b⁻¹)).mp hkernel with
          ⟨r, hr⟩
        have hr1 : r = 1 := by
          -- The relative group in degree `m + 2` is trivial by the connectivity hypothesis.
          exact
            @Subsingleton.elim
              (relativeHomotopyGroup (m + 1).succPNat A x)
              (hrel (q := (m + 1).succPNat) hq' x) r 1
        have hdiff : a * b⁻¹ = 1 := by
          simpa [eq_comm, hr1] using hr
        -- A trivial quotient `a * b⁻¹ = 1` forces `a = b`.
        have hmul := congrArg (fun z ↦ z * b) hdiff
        simpa [mul_assoc] using hmul
  · intro x q hq
    cases q with
    | zero =>
        -- Degree `0` surjectivity is the explicit `π₀` hypothesis from `NConnectedPair`.
        exact subtypeInclusionPiZeroSurjective_of_zerothHomotopySurjective A x h0
    | succ m =>
        cases m with
        | zero =>
            intro g
            let gLoop := (loopSpaceHomotopyGroupEquivPiSucc 0 x.1).symm g
            have hpair :
                Subsingleton (pairRelativePiZeroHomotopyGroup A x) := by
              let _ : Subsingleton (relativeHomotopyGroup 1 A x) := hrel (q := 1) hq x
              exact pairRelativePiZeroSubsingleton_of_relativePiOneSubsingleton A x
            have hbase :
                pairLoopToRelativePiZeroMap A x gLoop = pairRelativePiZeroBasepoint A x := by
              exact @Subsingleton.elim (pairRelativePiZeroHomotopyGroup A x) hpair _ _
            rcases (pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient A x gLoop).mp
                hbase with ⟨aLoop, haLoop⟩
            refine ⟨(loopSpaceHomotopyGroupEquivPiSucc 0 x) aLoop, ?_⟩
            -- The degree-`1` map is the loop-space `π₀` inclusion under the standard shift
            -- equivalence.
            have hpairMap :
                pairSubspaceInclusionHomotopyGroupMap A x 1
                    ((loopSpaceHomotopyGroupEquivPiSucc 0 x) aLoop) = g := by
              calc
                pairSubspaceInclusionHomotopyGroupMap A x 1
                    ((loopSpaceHomotopyGroupEquivPiSucc 0 x) aLoop) =
                  (loopSpaceHomotopyGroupEquivPiSucc 0 x.1)
                    (pairLoopSubspaceInclusionPiZeroMap A x aLoop) := by
                      simpa using
                        (congrFun (pairLoopPiZero_commutes_withSubtypeInclusionPiOne A x)
                          aLoop).symm
                _ = (loopSpaceHomotopyGroupEquivPiSucc 0 x.1) gLoop := by rw [haLoop]
                _ = g := by simp [gLoop]
            simpa [subtypeInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap A x 1] using
              hpairMap
        | succ m =>
            intro g
            let gLoop := (loopSpaceHomotopyGroupEquivPiSucc (m + 1) x.1).symm g
            have hbase :
                pairLoopToRelativeHomotopyGroupMap A x m gLoop = 1 := by
              exact
                @Subsingleton.elim
                  (relativeHomotopyGroup (m + 1).succPNat A x)
                  (hrel (q := (m + 1).succPNat) hq x) _ _
            rcases ((pairHomotopyLongExactSequenceSubspaceToAmbient A x m) gLoop).mp hbase with
              ⟨aLoop, haLoop⟩
            refine ⟨(loopSpaceHomotopyGroupEquivPiSucc (m + 1) x) aLoop, ?_⟩
            -- The higher-degree inclusion map is the shifted loop-space map from Theorem 9.2.2.
            have hpairMap :
                pairSubspaceInclusionHomotopyGroupMap A x (m + 2)
                    ((loopSpaceHomotopyGroupEquivPiSucc (m + 1) x) aLoop) = g := by
              calc
                pairSubspaceInclusionHomotopyGroupMap A x (m + 2)
                    ((loopSpaceHomotopyGroupEquivPiSucc (m + 1) x) aLoop) =
                  (loopSpaceHomotopyGroupEquivPiSucc (m + 1) x.1)
                    (pairLoopSubspaceInclusionHomotopyGroupMap A x m aLoop) := by
                      simpa using
                        (congrFun
                          (pairLoopSubspaceInclusion_commutes_withSubtypeInclusionPiSucc A x m)
                          aLoop).symm
                _ = (loopSpaceHomotopyGroupEquivPiSucc (m + 1) x.1) gLoop := by rw [haLoop]
                _ = g := by simp [gLoop]
            simpa
              [subtypeInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap A x (m + 2)]
              using hpairMap

/-- Helper for Observation 10.4.3: `n`-equivalence data for the subtype inclusion forces the
relative homotopy groups of `(X, A)` up through degree `n` to be trivial. -/
private theorem relativeSubsingleton_of_isNEquivalence_subtypeInclusion_data
    (A : Set X) (n : ℕ)
    (hEq : IsNEquivalence n (TopCat.subtypeInclusion A).hom) :
    ∀ a : A, ∀ {q : ℕ+}, (q : ℕ) ≤ n -> Subsingleton (relativeHomotopyGroup q A a) := by
  intro a q hq
  cases hpred : q.natPred with
  | zero =>
      have hq1 : q = 1 := by
        simpa [hpred] using (PNat.succPNat_natPred q).symm
      subst hq1
      have hπ0 :
          Function.Injective (zerothHomotopyInclusion A) := by
        have h0lt : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hq
        exact
          (subtypeInclusionPiZeroInjective_iff_zerothHomotopyInclusionInjective A a).1
            (hEq.injective a (q := 0) h0lt)
      have hπ1 :
          ∀ x : A, Function.Surjective (pairLoopSubspaceInclusionPiZeroMap A x) := by
        intro x
        intro g
        rcases hEq.surjective x (q := 1) hq ((loopSpaceHomotopyGroupEquivPiSucc 0 x.1) g) with
          ⟨b, hb⟩
        refine ⟨(loopSpaceHomotopyGroupEquivPiSucc 0 x).symm b, ?_⟩
        -- Pull the degree-`1` surjectivity back through the loop-space shift equivalence.
        apply (loopSpaceHomotopyGroupEquivPiSucc 0 x.1).injective
        calc
          (loopSpaceHomotopyGroupEquivPiSucc 0 x.1)
              (pairLoopSubspaceInclusionPiZeroMap A x
                ((loopSpaceHomotopyGroupEquivPiSucc 0 x).symm b)) =
            pairSubspaceInclusionHomotopyGroupMap A x 1 b := by
              simpa using
                congrFun (pairLoopPiZero_commutes_withSubtypeInclusionPiOne A x)
                  ((loopSpaceHomotopyGroupEquivPiSucc 0 x).symm b)
          _ = ((TopCat.subtypeInclusion A).hom).eStar 1 x b := by
              rw [← subtypeInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap A x 1]
          _ = (loopSpaceHomotopyGroupEquivPiSucc 0 x.1) g := hb
      -- The special tail exactness clause handles relative `π₁`.
      exact relativePiOneSubsingleton_of_piZeroInjective_and_loopPiOneSurjective A hπ0 hπ1 a
  | succ m =>
      have hqsucc : q = (m + 1).succPNat := by
        simpa [hpred] using (PNat.succPNat_natPred q).symm
      subst hqsucc
      have hsurj :
          ∀ x : A, Function.Surjective (pairSubspaceInclusionHomotopyGroupMap A x (m + 2)) := by
        intro x
        have hsurjIncl :
            Function.Surjective (((TopCat.subtypeInclusion A).hom).eStar (m + 2) x) :=
          hEq.surjective x (q := m + 2) (by simpa using hq)
        simpa [subtypeInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap A x (m + 2)] using
          hsurjIncl
      have hinj :
          ∀ x : A, Function.Injective (pairSubspaceInclusionHomotopyGroupMap A x (m + 1)) := by
        intro x
        have hlt : m + 1 < n :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self (m + 1)) (by simpa using hq)
        have hinjIncl :
            Function.Injective (((TopCat.subtypeInclusion A).hom).eStar (m + 1) x) :=
          hEq.injective x (q := m + 1) hlt
        simpa [subtypeInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap A x (m + 1)] using
          hinjIncl
      -- In degrees `m + 2`, the positive-degree exactness clause gives the desired triviality.
      exact
        relativeHomotopyGroupSubsingleton_of_inclusionSurjective_inclusionInjective A m hsurj
          hinj a

/-- Observation 10.4.3: a pair `(X, A)` is `n`-connected precisely when the canonical inclusion
`A ↪ X`, viewed as `(TopCat.subtypeInclusion A).hom : C(A, X)`, is an `n`-equivalence; with the
local Chapter 9 owner `IsNEquivalence`, this requires the `π₀` surjectivity clause from
Definition 10.4.2 to be stated explicitly. -/
theorem nConnectedPair_iff_isNEquivalence_subtypeInclusion (n : ℕ) (A : Set X) :
    NConnectedPair n A ↔
      Function.Surjective (zerothHomotopyInclusion A) ∧
        IsNEquivalence n (TopCat.subtypeInclusion A).hom :=
  by
    constructor
    · intro hPair
      rcases (nConnectedPair_iff n A).mp hPair with ⟨h0, hrel⟩
      -- Assemble the forward implication from the explicit `π₀` clause and the positive-degree
      -- relative triviality package.
      exact
        ⟨h0,
          isNEquivalence_subtypeInclusion_of_nConnectedPair_data A n h0
            (fun {q} hq a ↦ hrel hq a)⟩
    · rintro ⟨h0, hEq⟩
      -- The reverse implication keeps the same `π₀` surjectivity clause and recovers the positive
      -- relative-group triviality from the `n`-equivalence hypotheses.
      exact
        (nConnectedPair_iff n A).mpr
          ⟨h0, fun {q} hq a ↦
            relativeSubsingleton_of_isNEquivalence_subtypeInclusion_data A n hEq a hq⟩

/-- In an `n`-connected pair `(X, A)`, the canonical inclusion `A ↪ X` is an `n`-equivalence. -/
instance isNEquivalence_subtypeInclusion (n : ℕ) (A : Set X) [h : NConnectedPair n A] :
    IsNEquivalence n (TopCat.subtypeInclusion A).hom :=
  (nConnectedPair_iff_isNEquivalence_subtypeInclusion n A).mp h |>.2

/-- If the canonical inclusion `A ↪ X` is an `n`-equivalence and the induced map
`π₀(A) → π₀(X)` is surjective, then `(X, A)` is `n`-connected. -/
theorem nConnectedPair_of_isNEquivalence_subtypeInclusion
    (n : ℕ) (A : Set X)
    (h0 : Function.Surjective (zerothHomotopyInclusion A))
    [h : IsNEquivalence n (TopCat.subtypeInclusion A).hom] :
    NConnectedPair n A :=
  (nConnectedPair_iff_isNEquivalence_subtypeInclusion n A).mpr ⟨h0, h⟩
