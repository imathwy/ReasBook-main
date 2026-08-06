import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Theorem_1_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_17
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5

open Path.Homotopic.Quotient
open scoped ContinuousMap unitInterval

noncomputable section

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} B]

/-- A continuous self-map of `X` is a homotopy automorphism if it is the forward map of a
self-homotopy equivalence. -/
def IsHomotopyAutomorphism (X : Type u) [TopologicalSpace X] (f : C(X, X)) : Prop :=
  ∃ e : X ≃ₕ X, e.toFun = f

namespace ContinuousMap.HomotopyEquiv

/-- The forward map of a self-homotopy equivalence is a homotopy automorphism. -/
theorem isHomotopyAutomorphism (X : Type u) [TopologicalSpace X] (e : X ≃ₕ X) :
    IsHomotopyAutomorphism X e.toFun :=
  ⟨e, rfl⟩

end ContinuousMap.HomotopyEquiv

/-- `HomotopyAut X` is the subtype of the compactly generated self-mapping space consisting of the
self-homotopy equivalences. -/
abbrev HomotopyAut (X : Type u) [TopologicalSpace X] : Type u :=
  { f : CompactlyGenerated.MapSpace X X // IsHomotopyAutomorphism X (f : C(X, X)) }

notation:max "Aut(" X ")" => HomotopyAut X

instance (X : Type u) [TopologicalSpace X] : CoeFun (Aut(X)) fun _ ↦ X → X :=
  ⟨fun e ↦ e.1⟩

namespace HomotopyAut

variable (X : Type u) [TopologicalSpace X]

/-- The `HomotopyAut X` point determined by a self-homotopy equivalence. -/
def ofHomotopyEquiv (e : X ≃ₕ X) : Aut(X) :=
  ⟨CompactlyGenerated.MapSpace.ofContinuousMap e.toFun, e.isHomotopyAutomorphism X⟩

/-- `ofHomotopyEquiv e` has underlying self-map `e.toFun`. -/
@[simp] theorem coe_ofHomotopyEquiv (e : X ≃ₕ X) :
    ((HomotopyAut.ofHomotopyEquiv X e : Aut(X)) : C(X, X)) = e.toFun :=
  rfl

/-- `ofHomotopyEquiv e` acts by the underlying map of `e`. -/
@[simp] theorem ofHomotopyEquiv_apply (e : X ≃ₕ X) (x : X) :
    HomotopyAut.ofHomotopyEquiv X e x = e x :=
  rfl

/-- A chosen homotopy equivalence whose forward map is the underlying self-map of `e`. -/
noncomputable def toHomotopyEquiv (e : Aut(X)) : X ≃ₕ X :=
  Classical.choose e.2

/-- The chosen homotopy equivalence underlying `e` has the expected forward map. -/
@[simp] theorem toHomotopyEquiv_toContinuousMap (e : Aut(X)) :
    e.toHomotopyEquiv.toFun = (e : C(X, X)) :=
  Classical.choose_spec e.2

end HomotopyAut

/-- A continuous self-map of `X` is a homotopy automorphism exactly when it admits a two-sided
homotopy inverse. -/
theorem isHomotopyAutomorphism_iff_exists_homotopyInverse
    (X : Type u) [TopologicalSpace X] (f : C(X, X)) :
    IsHomotopyAutomorphism X f ↔
      ∃ g : C(X, X), (g.comp f).Homotopic (ContinuousMap.id X) ∧
        (f.comp g).Homotopic (ContinuousMap.id X) := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.invFun, e.left_inv, e.right_inv⟩
  · rintro ⟨g, hg_left, hg_right⟩
    exact
      ⟨{ toFun := f
         invFun := g
         left_inv := hg_left
         right_inv := hg_right }, rfl⟩

/-- The identity self-map of `X` is a homotopy automorphism. -/
theorem isHomotopyAutomorphism_id (X : Type u) [TopologicalSpace X] :
    IsHomotopyAutomorphism X (ContinuousMap.id X) :=
  ⟨ContinuousMap.HomotopyEquiv.refl X, rfl⟩

/-- Composition preserves the property of being a homotopy automorphism. -/
theorem isHomotopyAutomorphism_comp (X : Type u) [TopologicalSpace X] {f g : C(X, X)}
    (hf : IsHomotopyAutomorphism X f) (hg : IsHomotopyAutomorphism X g) :
    IsHomotopyAutomorphism X (f.comp g) := by
  rcases hf with ⟨ef, rfl⟩
  rcases hg with ⟨eg, rfl⟩
  exact ⟨eg.trans ef, rfl⟩

instance homotopyAutMonoid (X : Type u) [TopologicalSpace X] : Monoid (Aut(X)) where
  one := ⟨CompactlyGenerated.MapSpace.ofContinuousMap (ContinuousMap.id X),
    isHomotopyAutomorphism_id X⟩
  mul e₁ e₂ :=
    ⟨CompactlyGenerated.MapSpace.ofContinuousMap
        (ContinuousMap.comp (e₁ : C(X, X)) (e₂ : C(X, X))),
      isHomotopyAutomorphism_comp X e₁.2 e₂.2⟩
  one_mul e := by
    apply Subtype.ext
    apply CompactlyGenerated.MapSpace.ext
    intro x
    rfl
  mul_one e := by
    apply Subtype.ext
    apply CompactlyGenerated.MapSpace.ext
    intro x
    rfl
  mul_assoc e₁ e₂ e₃ := by
    apply Subtype.ext
    apply CompactlyGenerated.MapSpace.ext
    intro x
    rfl

/-- The composition law on `HomotopyAut X` acts by ordinary composition on points. -/
@[simp] theorem homotopyAut_mul_apply (X : Type u) [TopologicalSpace X]
    (e₁ e₂ : Aut(X)) (x : X) :
    (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

/-- A homotopy of ordinary self-maps gives a path in the compactly generated self-mapping space. -/
theorem joinedMapSpaceOfHomotopic (X : Type u) [TopologicalSpace X]
    {f g : C(X, X)} (h : f.Homotopic g) :
    Joined (CompactlyGenerated.MapSpace.ofContinuousMap f)
      (CompactlyGenerated.MapSpace.ofContinuousMap g) := by
  rcases h with ⟨H⟩
  refine ⟨{ toFun := fun t ↦ CompactlyGenerated.MapSpace.ofContinuousMap (H.curry t)
            continuous_toFun := ?_
            source' := ?_
            target' := ?_ }⟩
  · -- View the curried homotopy as a continuous family in the kified mapping space.
    let curried : I → C(X, X) := fun t ↦ H.curry t
    have hcurried : Continuous curried := by
      refine ContinuousMap.continuous_of_continuous_uncurry curried ?_
      simpa [Function.uncurry] using H.continuous
    let upCurried : ULift.{u} I → C(X, X) := fun t ↦ curried t.down
    have hUpCurried : Continuous upCurried := by
      simpa [upCurried] using hcurried.comp continuous_uliftDown
    have hToCompactlyGenerated :
        @Continuous (ULift.{u} I) C(X, X) inferInstance
          (TopologicalSpace.compactlyGenerated C(X, X)) upCurried := by
      simpa [upCurried] using
        (CompactlyGenerated.continuousToCompactlyGeneratedOfCompactProbe
          (CompHaus.of (ULift.{u} I)) ⟨upCurried, hUpCurried⟩)
    have hkifiedUp : Continuous fun t : ULift.{u} I ↦ (Kified.mk (upCurried t) : Kified C(X, X)) :=
      by
        have hCompositeToCompactlyGenerated :
            @Continuous (ULift.{u} I) C(X, X) inferInstance
              (TopologicalSpace.compactlyGenerated C(X, X))
              (Kified.of ∘ fun t : ULift.{u} I ↦ (Kified.mk (upCurried t) : Kified C(X, X))) := by
          simpa [Function.comp] using hToCompactlyGenerated
        simpa [Function.comp, kifiedTopologicalSpace] using
          (continuous_induced_rng.2 hCompositeToCompactlyGenerated :
            Continuous fun t : ULift.{u} I ↦ (Kified.mk (upCurried t) : Kified C(X, X)))
    have hkified : Continuous fun t : I ↦ (Kified.mk (curried t) : Kified C(X, X)) := by
      simpa [upCurried, curried, Function.comp] using hkifiedUp.comp continuous_uliftUp
    simpa [CompactlyGenerated.MapSpace, CompactlyGenerated.MapSpace.ofContinuousMap, curried] using
      hkified
  · -- The left endpoint is the first endpoint map of the homotopy.
    apply CompactlyGenerated.MapSpace.ext
    intro x
    exact H.apply_zero x
  · -- The right endpoint is the second endpoint map of the homotopy.
    apply CompactlyGenerated.MapSpace.ext
    intro x
    exact H.apply_one x

/-- Being a homotopy automorphism is invariant under homotopy of the underlying self-map. -/
theorem isHomotopyAutomorphismOfHomotopic (X : Type u) [TopologicalSpace X] {f g : C(X, X)}
    (hg : IsHomotopyAutomorphism X g) (hfg : f.Homotopic g) :
    IsHomotopyAutomorphism X f := by
  rcases (isHomotopyAutomorphism_iff_exists_homotopyInverse X g).mp hg with
    ⟨k, hk_left, hk_right⟩
  refine (isHomotopyAutomorphism_iff_exists_homotopyInverse X f).mpr ⟨k, ?_, ?_⟩
  · -- Precompose the chosen inverse by the homotopy between `f` and `g`.
    exact
      (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl k) hfg).trans hk_left
  · -- Postcompose the chosen inverse by the homotopy between `f` and `g`.
    exact
      (ContinuousMap.Homotopic.comp hfg (ContinuousMap.Homotopic.refl k)).trans hk_right

section CompactlyGeneratedAut

variable (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace X]

/-- A path in the compactly generated mapping space yields an ordinary homotopy of the
underlying continuous maps. -/
theorem homotopicOfJoinedMapSpace {Y : Type*} [TopologicalSpace Y]
    {f g : CompactlyGenerated.MapSpace X Y} (h : Joined f g) :
    ((f : C(X, Y))).Homotopic (g : C(X, Y)) := by
  rcases h with ⟨p⟩
  have continuousFromUnitIntervalProd :
      Continuous (fun tx : I × X ↦ p tx.1 tx.2) := by
    -- Transpose to `X → C(I, Y)` and use compact probes on the source.
    let F : X → C(I, Y) := fun x ↦
      ⟨fun t ↦ p t x, by
        simpa using
          (continuous_eval_const x).comp ((continuousKifiedForget C(X, Y)).comp p.continuous)⟩
    have hFcont : Continuous F := by
      refine continuous_from_uCompactlyGeneratedSpace F ?_
      intro S k
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      have hforget : Continuous fun t : I ↦ (p t : C(X, Y)) := by
        exact (continuousKifiedForget C(X, Y)).comp p.continuous
      have hr : Continuous fun t : I ↦ (p t : C(X, Y)).comp k := by
        exact (ContinuousMap.continuous_precomp k).comp hforget
      let r : C(I, C(S, Y)) := ⟨fun t ↦ (p t : C(X, Y)).comp k, hr⟩
      have huncurry : Continuous fun ts : I × S ↦ r ts.1 ts.2 :=
        ContinuousMap.continuous_uncurry_of_continuous r
      have hswap : Continuous fun st : S × I ↦ r st.2 st.1 := by
        simpa using huncurry.comp (Homeomorph.prodComm S I).continuous
      simpa [F, Function.uncurry, r] using hswap
    have huncurry : Continuous fun xt : X × I ↦ F xt.1 xt.2 :=
      ContinuousMap.continuous_uncurry_of_continuous ⟨F, hFcont⟩
    simpa [F] using huncurry.comp (Homeomorph.prodComm I X).continuous
  refine
    ⟨{ toContinuousMap := ⟨fun tx ↦ p tx.1 tx.2, continuousFromUnitIntervalProd⟩
       map_zero_left := ?_
       map_one_left := ?_ }⟩
  · -- The left edge is the source endpoint map of the path.
    intro x
    exact congrArg (fun q : CompactlyGenerated.MapSpace X Y ↦ q x) p.source
  · -- The right edge is the target endpoint map of the path.
    intro x
    exact congrArg (fun q : CompactlyGenerated.MapSpace X Y ↦ q x) p.target

/-- A path in the ambient mapping space between two homotopy automorphisms lifts to a path inside
`Aut(X)`. -/
theorem joinedHomotopyAutOfJoinedMapSpace {a b : Aut(X)}
    (h : Joined ((a : Aut(X)) : CompactlyGenerated.MapSpace X X)
      (((b : Aut(X)) : CompactlyGenerated.MapSpace X X))) :
    Joined a b := by
  rcases h with ⟨p⟩
  have hprop :
      ∀ t : I, IsHomotopyAutomorphism X ((p t : CompactlyGenerated.MapSpace X X) : C(X, X)) := by
    intro t
    have hslice :
        Joined (p t : CompactlyGenerated.MapSpace X X)
          (((b : Aut(X)) : CompactlyGenerated.MapSpace X X)) := by
      refine ⟨(p.truncateOfLE t.2.2).cast ?_ ?_⟩
      · exact (p.extend_apply t.2).symm
      · exact (p.extend_one).symm
    exact
      isHomotopyAutomorphismOfHomotopic X b.2 (homotopicOfJoinedMapSpace X hslice)
  refine ⟨{ toFun := fun t ↦ ⟨p t, hprop t⟩
            continuous_toFun := p.continuous.subtype_mk hprop
            source' := ?_
            target' := ?_ }⟩
  · -- The lifted path starts at `a`.
    apply Subtype.ext
    exact p.source
  · -- The lifted path ends at `b`.
    apply Subtype.ext
    exact p.target

/-- Homotopic underlying self-maps of `Aut(X)` determine joined points of `Aut(X)`. -/
private theorem joinedHomotopyAutOfHomotopic {a b : Aut(X)}
    (h : ((a : C(X, X))).Homotopic (b : C(X, X))) :
    Joined a b := by
  have hMaps :
      Joined (((a : Aut(X)) : CompactlyGenerated.MapSpace X X))
        (((b : Aut(X)) : CompactlyGenerated.MapSpace X X)) :=
    joinedMapSpaceOfHomotopic X h
  simpa using joinedHomotopyAutOfJoinedMapSpace X hMaps

/-- Joined points in `Aut(X)` multiply to joined points on path components. -/
private theorem joinedHomotopyAutMul {a b c d : Aut(X)}
    (ha : Joined a b) (hc : Joined c d) : Joined (a * c) (b * d) := by
  have haMaps :
      Joined (((a : Aut(X)) : CompactlyGenerated.MapSpace X X))
        (((b : Aut(X)) : CompactlyGenerated.MapSpace X X)) := by
    exact ⟨ha.somePath.map continuous_subtype_val⟩
  have hcMaps :
      Joined (((c : Aut(X)) : CompactlyGenerated.MapSpace X X))
        (((d : Aut(X)) : CompactlyGenerated.MapSpace X X)) := by
    exact ⟨hc.somePath.map continuous_subtype_val⟩
  have haHom : ((a : C(X, X))).Homotopic (b : C(X, X)) :=
    homotopicOfJoinedMapSpace X haMaps
  have hcHom : ((c : C(X, X))).Homotopic (d : C(X, X)) :=
    homotopicOfJoinedMapSpace X hcMaps
  have hcomp : ((a : C(X, X)).comp (c : C(X, X))).Homotopic ((b : C(X, X)).comp (d : C(X, X))) :=
    ContinuousMap.Homotopic.comp haHom hcHom
  exact joinedHomotopyAutOfHomotopic X hcomp

instance : MulOne (ZerothHomotopy (Aut(X))) where
  one := Quotient.mk'' (1 : Aut(X))
  mul := Quotient.map₂' (· * ·) fun _ _ h₁ _ _ h₂ ↦ joinedHomotopyAutMul X h₁ h₂

end CompactlyGeneratedAut

/-- The homotopy class of the underlying self-map of an element of `Aut(F_b)`. -/
abbrev fiberHomotopyAutClass (p : C(E, B)) (b : B)
    (e : Aut(fiber p b)) : fiberMapHomotopyClasses p b b :=
  Quotient.mk'' ((e : C(fiber p b, fiber p b)))

/-- The explicit path-level fiber translation along a loop `β` as an element of `Aut(F_b)`. -/
noncomputable def fiberTranslationPathHomotopyAut
    (p : C(E, B)) [IsFibration p] {b : B} (β : Path b b) :
    Aut(fiber p b) :=
  HomotopyAut.ofHomotopyEquiv (fiber p b)
    (Classical.choose (exists_homotopyEquiv_fiberTranslationPath p β))

/-- The explicit path-level element of `Aut(F_b)` along `β` represents the canonical
fiber-translation class of `β`. -/
theorem fiberTranslationPathHomotopyAut_class
    (p : C(E, B)) [IsFibration p] {b : B} (β : Path b b) :
    fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p β) =
      fiberTranslationClass p (mk β) := by
  simpa [fiberHomotopyAutClass, fiberTranslationPathHomotopyAut] using
    Classical.choose_spec (exists_homotopyEquiv_fiberTranslationPath p β)

section FiberTranslationLoopClass

variable (p : C(E, B)) [IsFibration p] (b : B) [UCompactlyGeneratedSpace (fiber p b)]

omit [IsFibration p] in
/-- Helper for Corollary 7.6.8: equality of fiber-translation classes yields a path-component join
between the corresponding homotopy automorphisms of `F_b`. -/
private theorem joinedOfFiberHomotopyAutClassEq
    {e₀ e₁ : Aut(fiber p b)}
    (hClass : fiberHomotopyAutClass p b e₀ = fiberHomotopyAutClass p b e₁) :
    Joined e₀ e₁ := by
  -- Extract a homotopy of underlying self-maps from the equality of quotient classes.
  have hHom :
      ((e₀ : C(fiber p b, fiber p b))).Homotopic (e₁ : C(fiber p b, fiber p b)) :=
    Quotient.exact hClass
  -- Turn that homotopy into a path in the ambient mapping space and lift it back to `Aut(F_b)`.
  have hJoinedMaps :
      Joined (CompactlyGenerated.MapSpace.ofContinuousMap (e₀ : C(fiber p b, fiber p b)))
        (CompactlyGenerated.MapSpace.ofContinuousMap (e₁ : C(fiber p b, fiber p b))) :=
    joinedMapSpaceOfHomotopic (fiber p b) hHom
  simpa using joinedHomotopyAutOfJoinedMapSpace (fiber p b) hJoinedMaps

/-- Helper for Corollary 7.6.8: homotopic loops determine joined path-level automorphisms of the
fiber. -/
private theorem fiberTranslationPathHomotopyAut_joined_of_homotopic
    {β₀ β₁ : Path b b} (hβ : β₀.Homotopic β₁) :
    Joined (fiberTranslationPathHomotopyAut p β₀) (fiberTranslationPathHomotopyAut p β₁) := by
  -- Compare both chosen path-level automorphisms with the canonical translation class.
  have hClass :
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p β₀) =
        fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p β₁) := by
    calc
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p β₀) =
          fiberTranslationClass p (mk β₀) :=
        fiberTranslationPathHomotopyAut_class p β₀
      _ = fiberTranslationClass p (mk β₁) :=
        fiberTranslationClass_eq_of_homotopic p hβ
          (isFiberTranslation_fiberTranslationClass p (mk β₀))
          (isFiberTranslation_fiberTranslationClass p (mk β₁))
      _ = fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p β₁) :=
        (fiberTranslationPathHomotopyAut_class p β₁).symm
  -- Convert equality of represented classes into a path-component relation in `Aut(F_b)`.
  exact joinedOfFiberHomotopyAutClassEq p b hClass

/-- Helper for Corollary 7.6.8: the path-level automorphism of the constant loop represents the
unit component class. -/
private theorem fiberTranslationPathHomotopyAut_joined_refl :
    Joined (fiberTranslationPathHomotopyAut p (Path.refl b)) (1 : Aut(fiber p b)) := by
  -- Compare the chosen representative of the constant loop with the identity translation class.
  have hClass :
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p (Path.refl b)) =
        fiberHomotopyAutClass p b (1 : Aut(fiber p b)) := by
    calc
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p (Path.refl b)) =
          fiberTranslationClass p (mk (Path.refl b)) :=
        fiberTranslationPathHomotopyAut_class p (Path.refl b)
      _ = (⟦ContinuousMap.id (fiber p b)⟧ : fiberMapHomotopyClasses p b b) :=
        fiberTranslationClass_mk_refl p
      _ = fiberHomotopyAutClass p b (1 : Aut(fiber p b)) := by
        rfl
  -- Equality of represented classes yields the desired join in `Aut(F_b)`.
  exact joinedOfFiberHomotopyAutClassEq p b hClass

/-- Helper for Corollary 7.6.8: the path-level automorphism of a concatenated loop represents the
product of the corresponding component classes. -/
private theorem fiberTranslationPathHomotopyAut_joined_mul
    (β₁ β₂ : Path b b) :
    Joined (fiberTranslationPathHomotopyAut p (β₂.trans β₁))
      (fiberTranslationPathHomotopyAut p β₁ * fiberTranslationPathHomotopyAut p β₂) := by
  -- First compare each chosen automorphism with the explicit path-level translation map.
  have hClass₁ :
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p β₁) =
        (⟦fiberTranslationMapOfPath p β₁⟧ : fiberMapHomotopyClasses p b b) := by
    rw [fiberTranslationPathHomotopyAut_class, fiberTranslationMapOfPath_class]
  have hClass₂ :
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p β₂) =
        (⟦fiberTranslationMapOfPath p β₂⟧ : fiberMapHomotopyClasses p b b) := by
    rw [fiberTranslationPathHomotopyAut_class, fiberTranslationMapOfPath_class]
  have hHom₁ :
      ((fiberTranslationPathHomotopyAut p β₁ : C(fiber p b, fiber p b))).Homotopic
        (fiberTranslationMapOfPath p β₁) :=
    Quotient.exact hClass₁
  have hHom₂ :
      ((fiberTranslationPathHomotopyAut p β₂ : C(fiber p b, fiber p b))).Homotopic
        (fiberTranslationMapOfPath p β₂) :=
    Quotient.exact hClass₂
  have hProdClass :
      fiberHomotopyAutClass p b
          (fiberTranslationPathHomotopyAut p β₁ * fiberTranslationPathHomotopyAut p β₂) =
        (⟦(fiberTranslationMapOfPath p β₁).comp (fiberTranslationMapOfPath p β₂)⟧ :
          fiberMapHomotopyClasses p b b) := by
    -- Compose the representative homotopies to compare the product with the explicit composite.
    apply Quotient.sound
    simpa [fiberHomotopyAutClass] using ContinuousMap.Homotopic.comp hHom₁ hHom₂
  have hClass :
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p (β₂.trans β₁)) =
        fiberHomotopyAutClass p b
          (fiberTranslationPathHomotopyAut p β₁ * fiberTranslationPathHomotopyAut p β₂) := by
    calc
      fiberHomotopyAutClass p b (fiberTranslationPathHomotopyAut p (β₂.trans β₁)) =
          fiberTranslationClass p (mk (β₂.trans β₁)) :=
        fiberTranslationPathHomotopyAut_class p (β₂.trans β₁)
      _ = (⟦(fiberTranslationMapOfPath p β₁).comp (fiberTranslationMapOfPath p β₂)⟧ :
            fiberMapHomotopyClasses p b b) :=
        fiberTranslationClass_mk_trans p β₂ β₁
      _ = fiberHomotopyAutClass p b
            (fiberTranslationPathHomotopyAut p β₁ * fiberTranslationPathHomotopyAut p β₂) :=
        hProdClass.symm
  -- Pass back from equality of represented classes to `Joined` in `Aut(F_b)`.
  exact joinedOfFiberHomotopyAutClassEq p b hClass

/-- Corollary 7.6.8: loop lifting gives the canonical homomorphism
`π₁(B, b) → π₀(Aut(F_b))`, formalized as
`FundamentalGroup B b →* ZerothHomotopy (Aut(fiber p b))`. -/
noncomputable def fiberTranslationLoopClass :
    FundamentalGroup B b →* ZerothHomotopy (Aut(fiber p b)) where
  toFun :=
    Quotient.lift
      (fun β : Path b b ↦
        (⟦fiberTranslationPathHomotopyAut p β⟧ :
          ZerothHomotopy (Aut(fiber p b))))
      (fun β₀ β₁ hβ ↦ Quotient.sound
        (fiberTranslationPathHomotopyAut_joined_of_homotopic p b hβ))
  map_one' := by
    -- Normalize the identity loop to the constant path and use the unit join lemma.
    have hOne : (1 : FundamentalGroup B b) =
        FundamentalGroup.fromPath (mk (Path.refl b)) :=
      FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk b)
    rw [hOne]
    simpa using
      (Quotient.sound (fiberTranslationPathHomotopyAut_joined_refl p b) :
        (⟦fiberTranslationPathHomotopyAut p (Path.refl b)⟧ :
          ZerothHomotopy (Aut(fiber p b))) = (1 : ZerothHomotopy (Aut(fiber p b))))
  map_mul' := by
    intro γ₁ γ₂
    let loopClass : FundamentalGroup B b → ZerothHomotopy (Aut(fiber p b)) :=
      Quotient.lift
        (fun β : Path b b ↦
          (⟦fiberTranslationPathHomotopyAut p β⟧ :
            ZerothHomotopy (Aut(fiber p b))))
        (fun β₀ β₁ hβ ↦ Quotient.sound
          (fiberTranslationPathHomotopyAut_joined_of_homotopic p b hβ))
    change
      loopClass (FundamentalGroup.fromPath γ₁.toPath * FundamentalGroup.fromPath γ₂.toPath) =
        loopClass (FundamentalGroup.fromPath γ₁.toPath) *
          loopClass (FundamentalGroup.fromPath γ₂.toPath)
    refine Quotient.inductionOn₂ γ₁.toPath γ₂.toPath ?_
    intro β₁ β₂
    -- Reduce multiplication in `π₁(B, b)` to concatenation of represented loops.
    have hMul :
        FundamentalGroup.fromPath ⟦β₁⟧ * FundamentalGroup.fromPath ⟦β₂⟧ =
          FundamentalGroup.fromPath ⟦β₂.trans β₁⟧ := by
      simpa [CategoryTheory.End.mul_def] using
        (FundamentalGroupoid.comp_eq (FundamentalGroupoid.mk b) (FundamentalGroupoid.mk b)
          (FundamentalGroupoid.mk b) (FundamentalGroup.fromPath ⟦β₂⟧)
          (FundamentalGroup.fromPath ⟦β₁⟧))
    rw [hMul]
    simpa using
      (Quotient.sound (fiberTranslationPathHomotopyAut_joined_mul p b β₁ β₂) :
        (⟦fiberTranslationPathHomotopyAut p (β₂.trans β₁)⟧ :
            ZerothHomotopy (Aut(fiber p b))) =
          (⟦fiberTranslationPathHomotopyAut p β₁ * fiberTranslationPathHomotopyAut p β₂⟧ :
            ZerothHomotopy (Aut(fiber p b))))

/-- On a represented loop class, `fiberTranslationLoopClass p b` is given by the explicit
path-level fiber-translation automorphism. -/
theorem fiberTranslationLoopClass_fromPath (β : Path b b) :
    fiberTranslationLoopClass p b (FundamentalGroup.fromPath (mk β)) =
      (⟦fiberTranslationPathHomotopyAut p β⟧ :
        ZerothHomotopy (Aut(fiber p b))) := by
  rfl

/-- Helper for Corollary 7.6.8: `e : Aut(F_b)` represents the loop-translation class of `γ`
when it induces the prescribed `π₀(Aut(F_b))` class and the corresponding homotopy class of
fiber self-maps. -/
structure IsRepresentative (γ : FundamentalGroup B b) (e : Aut(fiber p b)) : Prop where
  loopClass_eq :
    fiberTranslationLoopClass p b γ =
      (⟦e⟧ : ZerothHomotopy (Aut(fiber p b)))
  homotopyClass_eq :
    fiberHomotopyAutClass p b e = fiberTranslationClass p γ.toPath

namespace IsRepresentative

/-- Helper for Corollary 7.6.8: package the two defining equalities of a representing
homotopy automorphism. -/
def ofEq (γ : FundamentalGroup B b) (e : Aut(fiber p b))
    (hLoop :
      fiberTranslationLoopClass p b γ =
        (⟦e⟧ : ZerothHomotopy (Aut(fiber p b))))
    (hClass : fiberHomotopyAutClass p b e = fiberTranslationClass p γ.toPath) :
    IsRepresentative p b γ e where
  loopClass_eq := hLoop
  homotopyClass_eq := hClass

end IsRepresentative

/-- `fiberTranslationLoopClass p b γ` is represented by an element of `Aut(F_b)` whose underlying
self-map realizes the fiber-translation class of `γ`. -/
theorem fiberTranslationLoopClass_spec (γ : FundamentalGroup B b) :
    ∃ e : Aut(fiber p b), IsRepresentative p b γ e := by
  -- Reduce the loop class to a represented loop and use the chosen path-level automorphism.
  change
    ∃ e : Aut(fiber p b), IsRepresentative p b (FundamentalGroup.fromPath γ.toPath) e
  refine Quotient.inductionOn γ.toPath ?_
  intro β
  refine ⟨fiberTranslationPathHomotopyAut p β, ?_⟩
  exact
    IsRepresentative.ofEq p b (FundamentalGroup.fromPath (mk β))
      (fiberTranslationPathHomotopyAut p β)
      (fiberTranslationLoopClass_fromPath p b β)
      (fiberTranslationPathHomotopyAut_class p β)

/-- A loop class in `π₁(B, b)` determines a fiber-translation class represented by an element of
`Aut(F_b)`. -/
theorem exists_fiberTranslationLoopHomotopyAut (γ : FundamentalGroup B b) :
    ∃ e : Aut(fiber p b),
      fiberHomotopyAutClass p b e = fiberTranslationClass p γ.toPath := by
  -- Forget the `π₀ Aut(F_b)` representative equality from the specification theorem.
  rcases fiberTranslationLoopClass_spec p b γ with ⟨e, hRep⟩
  exact ⟨e, hRep.homotopyClass_eq⟩

end FiberTranslationLoopClass

/-- The homotopy-category action from Theorem 7.6.5 is the bridge obtained by forgetting the
source-facing `π₀ Aut(F_b)` class to its represented endomorphism in the homotopy category. -/
noncomputable def fiberHomotopyClassRepresentation
    (p : C(E, B)) [IsFibration p] (b : B) :
    FundamentalGroup B b →* CategoryTheory.End (topCatHomotopyCategoryObj (fiber p b)) :=
  (fiberTranslationHomotopyFunctor p).mapEnd (FundamentalGroupoid.mk b)

/-- `fiberHomotopyClassRepresentation p b` sends `γ` to the homotopy-category morphism
represented by the fiber-translation class of `γ`. -/
theorem fiberHomotopyClassRepresentation_apply
    (p : C(E, B)) [IsFibration p] (b : B) (γ : FundamentalGroup B b) :
    fiberHomotopyClassRepresentation p b γ =
      topCatHomotopyCategoryMapClass (fiberTranslationClass p γ.toPath) := by
  change fiberHomotopyClassRepresentation p b (FundamentalGroup.fromPath γ.toPath) =
      topCatHomotopyCategoryMapClass (fiberTranslationClass p γ.toPath)
  refine Quotient.inductionOn γ.toPath ?_
  intro β
  change (fiberTranslationHomotopyFunctor p).map (FundamentalGroup.fromPath (mk β)) =
      topCatHomotopyCategoryMapClass (fiberTranslationClass p (mk β))
  exact fiberTranslationHomotopyFunctor_map_fromPath p β

/-- The homotopy-category bridge is represented by any `Aut(F_b)` representative of the
source-facing class `fiberTranslationLoopClass p b γ`. -/
theorem fiberHomotopyClassRepresentation_isRepresentedByHomotopyAut
    (p : C(E, B)) [IsFibration p] (b : B) [UCompactlyGeneratedSpace (fiber p b)]
    (γ : FundamentalGroup B b) :
    ∃ e : Aut(fiber p b),
      fiberTranslationLoopClass p b γ =
        (⟦e⟧ : ZerothHomotopy (Aut(fiber p b))) ∧
      fiberHomotopyClassRepresentation p b γ =
        topCatHomotopyCategoryMapClass (fiberHomotopyAutClass p b e) := by
  -- Choose the representative supplied by `fiberTranslationLoopClass_spec`.
  rcases fiberTranslationLoopClass_spec p b γ with ⟨e, hRep⟩
  refine ⟨e, hRep.loopClass_eq, ?_⟩
  -- Rewrite the homotopy-category action through the same represented class.
  calc
    fiberHomotopyClassRepresentation p b γ =
        topCatHomotopyCategoryMapClass (fiberTranslationClass p γ.toPath) :=
      fiberHomotopyClassRepresentation_apply p b γ
    _ = topCatHomotopyCategoryMapClass (fiberHomotopyAutClass p b e) := by
      rw [← hRep.homotopyClass_eq]
