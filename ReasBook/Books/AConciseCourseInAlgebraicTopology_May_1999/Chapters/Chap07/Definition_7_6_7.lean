import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_17
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContinuousMap unitInterval

universe u

-- `HomotopyAut X` is the source-facing subtype of the compactly generated self-mapping space
-- `X ^ X` consisting of the self-homotopy equivalences. This keeps the textbook k-space mapping
-- space owner while preserving the underlying continuous self-maps.

variable (X : Type u) [TopologicalSpace X]

/-- A continuous self-map of `X` is a textbook homotopy automorphism if it admits a two-sided
homotopy inverse. -/
def IsHomotopyAutomorphism (f : C(X, X)) : Prop :=
  ∃ e : X ≃ₕ X, e.toFun = f

namespace ContinuousMap.HomotopyEquiv

/-- The forward map of a self-homotopy equivalence is a homotopy automorphism. -/
theorem isHomotopyAutomorphism (e : X ≃ₕ X) : IsHomotopyAutomorphism X e.toFun :=
  ⟨e, rfl⟩

end ContinuousMap.HomotopyEquiv

/-- `HomotopyAut X` is the textbook `Aut(X)`, namely the subtype of the
compactly generated mapping space `X ^ X` consisting of the self-homotopy equivalences of `X`;
with composition it is a topological monoid, and `π₀ Aut(X)` is a group under composition. -/
abbrev HomotopyAut : Type u :=
  { f : CompactlyGenerated.MapSpace X X // IsHomotopyAutomorphism X (f : C(X, X)) }

notation:max "Aut(" X ")" => HomotopyAut X

instance : CoeFun (Aut(X)) fun _ ↦ X → X := ⟨fun e ↦ e.1⟩

/-- In May's category `U`, multiplication on `M` is continuous for the compactly generated
product topology on `M × M`. -/
class UContinuousMul (M : Type*) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul :
    @Continuous (M × M) M (compactlyGeneratedProductTopology M M) inferInstance
      (fun p : M × M ↦ p.1 * p.2)

namespace HomotopyAut

/-- The `HomotopyAut X` element underlying a self-homotopy equivalence. -/
def ofHomotopyEquiv (e : X ≃ₕ X) : Aut(X) :=
  ⟨CompactlyGenerated.MapSpace.ofContinuousMap e.toFun, e.isHomotopyAutomorphism⟩

/-- `ofHomotopyEquiv e` has underlying self-map `e.toFun`. -/
@[simp] theorem coe_ofHomotopyEquiv (e : X ≃ₕ X) :
    ((HomotopyAut.ofHomotopyEquiv X e : Aut(X)) : C(X, X)) = e.toFun :=
  rfl

/-- `ofHomotopyEquiv e` acts by the underlying self-map of `e`. -/
@[simp] theorem ofHomotopyEquiv_apply (e : X ≃ₕ X) (x : X) :
    HomotopyAut.ofHomotopyEquiv X e x = e x :=
  rfl

end HomotopyAut

/-- A continuous self-map of `X` is a textbook homotopy automorphism exactly when it admits a
two-sided homotopy inverse. -/
theorem isHomotopyAutomorphism_iff_exists_homotopyInverse (f : C(X, X)) :
    IsHomotopyAutomorphism X f ↔
      ∃ g : C(X, X), (g.comp f).Homotopic (ContinuousMap.id X) ∧
        (f.comp g).Homotopic (ContinuousMap.id X) :=
by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.invFun, e.left_inv, e.right_inv⟩
  · rintro ⟨g, hg_left, hg_right⟩
    exact ⟨
      { toFun := f
        invFun := g
        left_inv := hg_left
        right_inv := hg_right },
      rfl
    ⟩

/-- The identity self-map of `X` is a homotopy automorphism. -/
theorem isHomotopyAutomorphism_id : IsHomotopyAutomorphism X (ContinuousMap.id X) :=
  ⟨ContinuousMap.HomotopyEquiv.refl X, rfl⟩

/-- Composition preserves the property of being a homotopy automorphism. -/
theorem isHomotopyAutomorphism_comp {f g : C(X, X)}
    (hf : IsHomotopyAutomorphism X f) (hg : IsHomotopyAutomorphism X g) :
    IsHomotopyAutomorphism X (f.comp g) := by
  rcases hf with ⟨ef, rfl⟩
  rcases hg with ⟨eg, rfl⟩
  exact ⟨eg.trans ef, rfl⟩

/-- Composition makes `HomotopyAut X` into a monoid. -/
instance homotopyAutMonoid : Monoid (Aut(X)) where
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
@[simp] theorem homotopyAut_mul_apply (e₁ e₂ : Aut(X)) (x : X) :
    (e₁ * e₂) x = e₁ (e₂ x) := by
  rfl

/-- The unit of `HomotopyAut X` acts as the identity on points. -/
@[simp] theorem homotopyAut_one_apply (x : X) :
    (1 : Aut(X)) x = x := by
  rfl

namespace HomotopyAut

/-- A chosen homotopy equivalence whose forward map is the underlying self-map of `e`. -/
noncomputable def toHomotopyEquiv (e : Aut(X)) : X ≃ₕ X :=
  Classical.choose e.2

/-- The chosen homotopy equivalence underlying `e` has the expected forward map. -/
@[simp] theorem toHomotopyEquiv_toContinuousMap (e : Aut(X)) :
    e.toHomotopyEquiv.toFun = (e : C(X, X)) :=
  Classical.choose_spec e.2

/-- The chosen homotopy equivalence underlying `e` acts by the underlying self-map of `e`. -/
@[simp] theorem toHomotopyEquiv_apply (e : Aut(X)) (x : X) :
    HomotopyAut.toHomotopyEquiv X e x = e x := by
  rw [toHomotopyEquiv_toContinuousMap]

/-- The chosen inverse map of a homotopy automorphism. -/
noncomputable def invFun (e : Aut(X)) : C(X, X) :=
  e.toHomotopyEquiv.invFun

/-- The chosen inverse map of `e` is a left homotopy inverse of the underlying self-map. -/
theorem invFun_left_inv (e : Aut(X)) :
    (ContinuousMap.comp e.invFun e).Homotopic (ContinuousMap.id X) := by
  simpa [invFun, toHomotopyEquiv_toContinuousMap] using e.toHomotopyEquiv.left_inv

/-- The chosen inverse map of `e` is a right homotopy inverse of the underlying self-map. -/
theorem invFun_right_inv (e : Aut(X)) :
    (ContinuousMap.comp e e.invFun).Homotopic (ContinuousMap.id X) := by
  simpa [invFun, toHomotopyEquiv_toContinuousMap] using e.toHomotopyEquiv.right_inv

/-- The chosen inverse map of `e` is again a homotopy automorphism. -/
theorem isHomotopyAutomorphism_invFun (e : Aut(X)) :
    IsHomotopyAutomorphism X e.invFun :=
  ⟨e.toHomotopyEquiv.symm, rfl⟩

end HomotopyAut

private noncomputable def homotopyAutInv (e : Aut(X)) : Aut(X) :=
  HomotopyAut.ofHomotopyEquiv X e.toHomotopyEquiv.symm

/-- Helper for Definition 7.6.7: a homotopy of ordinary continuous maps gives a path in the
compactly generated mapping space. -/
theorem joinedMapSpaceOfHomotopic {Y : Type*} [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) :
    Joined (CompactlyGenerated.MapSpace.ofContinuousMap f)
      (CompactlyGenerated.MapSpace.ofContinuousMap g) := by
  rcases h with ⟨H⟩
  refine ⟨{ toFun := fun t ↦ CompactlyGenerated.MapSpace.ofContinuousMap (H.curry t)
            continuous_toFun := ?_
            source' := ?_
            target' := ?_ }⟩
  · -- Curry the homotopy and then view the family inside the kified mapping space.
    let curried : I → C(X, Y) := fun t ↦ H.curry t
    have hcurried : Continuous curried := by
      refine ContinuousMap.continuous_of_continuous_uncurry curried ?_
      simpa [Function.uncurry] using H.continuous
    have hkified : Continuous fun t : I ↦ CompactlyGenerated.MapSpace.ofContinuousMap (curried t) :=
      continuousToKifiedOfContinuous hcurried
    simpa [curried] using hkified
  · -- The left endpoint is the first endpoint map of the homotopy.
    apply CompactlyGenerated.MapSpace.ext
    intro x
    exact H.apply_zero x
  · -- The right endpoint is the second endpoint map of the homotopy.
    apply CompactlyGenerated.MapSpace.ext
    intro x
    exact H.apply_one x

/-- Helper for Definition 7.6.7: being a homotopy automorphism is invariant under homotopy of the
underlying self-map. -/
theorem isHomotopyAutomorphismOfHomotopic {f g : C(X, X)}
    (hg : IsHomotopyAutomorphism X g) (hfg : f.Homotopic g) :
    IsHomotopyAutomorphism X f := by
  rcases
      (isHomotopyAutomorphism_iff_exists_homotopyInverse X g).mp hg with
    ⟨k, hk_left, hk_right⟩
  refine
    (isHomotopyAutomorphism_iff_exists_homotopyInverse X f).mpr
      ⟨k, ?_, ?_⟩
  · -- Precompose the given homotopy inverse by the ambient homotopy.
    exact
      (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl k) hfg).trans hk_left
  · -- Postcompose the given homotopy inverse by the ambient homotopy.
    exact
      (ContinuousMap.Homotopic.comp hfg (ContinuousMap.Homotopic.refl k)).trans hk_right

/-- Helper for Definition 7.6.7: chosen inverses of homotopic homotopy automorphisms are again
homotopic. -/
theorem invFunHomotopicOfHomotopic {e₁ e₂ : Aut(X)}
    (h : ((e₁ : C(X, X))).Homotopic (e₂ : C(X, X))) :
    e₁.invFun.Homotopic e₂.invFun := by
  -- First compare `e₂.invFun` with `e₁.invFun ∘ e₂ ∘ e₂.invFun`.
  have hIdToComp : (ContinuousMap.id X).Homotopic (ContinuousMap.comp e₁.invFun e₂) := by
    exact
      (HomotopyAut.invFun_left_inv X e₁).symm.trans
        (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl e₁.invFun) h)
  have hToTriple :
      e₂.invFun.Homotopic
        (ContinuousMap.comp (ContinuousMap.comp e₁.invFun e₂) e₂.invFun) := by
    simpa [ContinuousMap.comp_assoc] using
      ContinuousMap.Homotopic.comp hIdToComp (ContinuousMap.Homotopic.refl e₂.invFun)
  -- Then collapse the trailing `e₂ ∘ e₂.invFun` back to the identity.
  have hCollapse :
      (ContinuousMap.comp (ContinuousMap.comp e₁.invFun e₂) e₂.invFun).Homotopic e₁.invFun := by
    simpa [ContinuousMap.comp_assoc] using
      ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl e₁.invFun)
        (HomotopyAut.invFun_right_inv X e₂)
  exact (hToTriple.trans hCollapse).symm

section CompactlyGenerated

variable [UCompactlyGeneratedSpace X]

/-- Helper for Definition 7.6.7: a path in the compactly generated mapping space yields an
ordinary homotopy of the underlying continuous maps. -/
theorem homotopicOfJoinedMapSpace {Y : Type*} [TopologicalSpace Y]
    {f g : CompactlyGenerated.MapSpace X Y} (h : Joined f g) :
    ((f : C(X, Y))).Homotopic (g : C(X, Y)) := by
  rcases h with ⟨p⟩
  have continuousFromUnitIntervalProd :
      Continuous (fun tx : I × X ↦ p tx.1 tx.2) := by
    -- To prove continuity on `I × X`, first curry in the `X`-variable and then use that `I` is
    -- compact Hausdorff and locally compact.
    let F : X → C(I, Y) := fun x ↦
      ⟨fun t ↦ p t x, by
        simpa using
          (continuous_eval_const x).comp ((continuousKifiedForget C(X, Y)).comp p.continuous)
      ⟩
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
  have hcont : Continuous fun tx : I × X ↦ p tx.1 tx.2 := by
    exact continuousFromUnitIntervalProd
  refine
    ⟨{ toContinuousMap := ⟨fun tx ↦ p tx.1 tx.2, hcont⟩
       map_zero_left := ?_
       map_one_left := ?_ }⟩
  · -- The left edge is the source endpoint map of the path.
    intro x
    exact congrArg (fun q : CompactlyGenerated.MapSpace X Y ↦ q x) p.source
  · -- The right edge is the target endpoint map of the path.
    intro x
    exact congrArg (fun q : CompactlyGenerated.MapSpace X Y ↦ q x) p.target

/-- Helper for Definition 7.6.7: a path in the ambient mapping space between two homotopy
automorphisms lifts to a path inside `Aut(X)`. -/
theorem joinedHomotopyAutOfJoinedMapSpace {a b : Aut(X)}
    (h : Joined ((a : Aut(X)) : CompactlyGenerated.MapSpace X X)
      (((b : Aut(X)) : CompactlyGenerated.MapSpace X X))) :
    Joined a b := by
  rcases h with ⟨p⟩
  have hprop :
      ∀ t : I, IsHomotopyAutomorphism X ((p t : CompactlyGenerated.MapSpace X X) : C(X, X)) := by
    intro t
    -- Join the time slice to the endpoint and transport the automorphism property along that
    -- homotopy.
    have hslice :
        Joined (p t : CompactlyGenerated.MapSpace X X)
          (((b : Aut(X)) : CompactlyGenerated.MapSpace X X)) := by
      refine
        ⟨(p.truncateOfLE t.2.2).cast ?_ ?_⟩
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

/-- Helper for Definition 7.6.7: a compact family of self-maps in `X ^ X` evaluates continuously
on the product `K × X`. -/
theorem mapSpaceFamilyUncurryContinuous {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] (a : C(K, CompactlyGenerated.MapSpace X X)) :
    Continuous fun p : K × X ↦ ((a p.1 : C(X, X)) p.2) := by
  -- Route correction: instead of using `continuous_comp'` on `C(X, X)`, transpose the family so
  -- the compact test space `K` is the locally compact variable in the compact-open API.
  let F : X → C(K, X) := fun x ↦
    ⟨fun k ↦ (a k : C(X, X)) x, by
      simpa using
        (continuous_eval_const x).comp ((continuousKifiedForget C(X, X)).comp a.continuous)⟩
  have hF : Continuous F := by
    -- Check continuity into `C(K, X)` on compact sources, then untranspose back.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro S k
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have hforget : Continuous fun t : K ↦ (a t : C(X, X)) := by
      exact (continuousKifiedForget C(X, X)).comp a.continuous
    have hprecomp : Continuous fun t : K ↦ (a t : C(X, X)).comp k := by
      exact (ContinuousMap.continuous_precomp k).comp hforget
    let r : C(K, C(S, X)) := ⟨fun t ↦ (a t : C(X, X)).comp k, hprecomp⟩
    have huncurry : Continuous fun ts : K × S ↦ r ts.1 ts.2 :=
      ContinuousMap.continuous_uncurry_of_continuous r
    have hswap : Continuous fun st : S × K ↦ r st.2 st.1 := by
      simpa using huncurry.comp (Homeomorph.prodComm S K).continuous
    simpa [F, Function.uncurry, r] using hswap
  -- Uncurry the transposed family and swap the product factors back to `K × X`.
  have huncurry : Continuous fun xk : X × K ↦ F xk.1 xk.2 :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩
  simpa [F] using huncurry.comp (Homeomorph.prodComm K X).continuous

/-- Helper for Definition 7.6.7: compact-source families of self-maps compose continuously in
`X ^ X`. -/
theorem continuousCompMapSpaceOfCompactSource {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [UCompactlyGeneratedSpace.{u} K]
    (h : C(K, CompactlyGenerated.MapSpace X X × CompactlyGenerated.MapSpace X X)) :
    Continuous fun k : K ↦
      CompactlyGenerated.MapSpace.ofContinuousMap
        ((((h k).1 : C(X, X)).comp ((h k).2 : C(X, X)))) := by
  let a : C(K, CompactlyGenerated.MapSpace X X) := ⟨fun k ↦ (h k).1, h.continuous.fst⟩
  let b : C(K, CompactlyGenerated.MapSpace X X) := ⟨fun k ↦ (h k).2, h.continuous.snd⟩
  have huncurry :
      Continuous fun p : K × X ↦ ((a p.1 : C(X, X)) (((b p.1 : C(X, X)) p.2))) := by
    -- Evaluate the outer family after pairing the compact parameter with the inner evaluation.
    have ha : Continuous fun p : K × X ↦ ((a p.1 : C(X, X)) p.2) :=
      mapSpaceFamilyUncurryContinuous X a
    have hb : Continuous fun p : K × X ↦ ((b p.1 : C(X, X)) p.2) :=
      mapSpaceFamilyUncurryContinuous X b
    have hpair : Continuous fun p : K × X ↦ (p.1, ((b p.1 : C(X, X)) p.2)) :=
      continuous_fst.prodMk hb
    simpa using ha.comp hpair
  let compFamily : K → C(X, X) := fun k ↦ ((h k).1 : C(X, X)).comp ((h k).2 : C(X, X))
  have hCompFamily : Continuous compFamily := by
    -- Repackage the continuous uncurried family back into the ordinary compact-open mapping space.
    refine ContinuousMap.continuous_of_continuous_uncurry compFamily ?_
    simpa [compFamily, a, b, Function.uncurry, ContinuousMap.comp_apply] using huncurry
  -- Finally, view the continuous `C(X, X)`-valued family in the kified owner `X ^ X`.
  have hkified :
      Continuous fun k : K ↦ CompactlyGenerated.MapSpace.ofContinuousMap (compFamily k) :=
    continuousToKifiedOfContinuous hCompFamily
  simpa [compFamily] using hkified

/-- Definition 7.6.7: composition on `HomotopyAut X` is continuous for the chapter's compactly
generated product topology on `Aut(X) × Aut(X)`, so `Aut(X)` is a topological monoid in May's
`U`-setting. -/
theorem homotopyAutContinuousMul :
    @Continuous (Aut(X) × Aut(X)) (Aut(X))
      (compactlyGeneratedProductTopology (Aut(X)) (Aut(X))) inferInstance
      (fun p : Aut(X) × Aut(X) ↦ p.1 * p.2) := by
  -- Rewrite the source topology as the k-ification of the ordinary product topology.
  rw [compactlyGeneratedProductTopology_def]
  refine
    @continuous_from_compactlyGenerated
      (Aut(X) × Aut(X)) (Aut(X))
      instTopologicalSpaceProd inferInstance
      (fun p : Aut(X) × Aut(X) ↦ p.1 * p.2) ?_
  intro S g
  let pairFamily : C(S, CompactlyGenerated.MapSpace X X × CompactlyGenerated.MapSpace X X) :=
    ⟨fun s ↦
        ((((g s).1 : Aut(X)) : CompactlyGenerated.MapSpace X X),
          (((g s).2 : Aut(X)) : CompactlyGenerated.MapSpace X X)),
      (continuous_subtype_val.comp g.continuous.fst).prodMk
        (continuous_subtype_val.comp g.continuous.snd)⟩
  have hcomp :
      Continuous fun s : S ↦
        CompactlyGenerated.MapSpace.ofContinuousMap
          ((((pairFamily s).1 : C(X, X)).comp ((pairFamily s).2 : C(X, X)))) :=
    continuousCompMapSpaceOfCompactSource X pairFamily
  -- Lift the ambient composition family back to the homotopy-automorphism subtype.
  have hmul :
      Continuous fun s : S ↦
        (⟨
          CompactlyGenerated.MapSpace.ofContinuousMap
            ((((pairFamily s).1 : C(X, X)).comp ((pairFamily s).2 : C(X, X)))),
          isHomotopyAutomorphism_comp X ((g s).1).2 ((g s).2).2
        ⟩ : Aut(X)) := by
    exact Continuous.subtype_mk hcomp fun s ↦ by
      simpa [pairFamily] using isHomotopyAutomorphism_comp X ((g s).1).2 ((g s).2).2
  -- The explicit subtype lift is definitionally the multiplication family.
  simpa [pairFamily] using hmul

/-- `Aut(X)` carries the source-faithful `U`-topological monoid structure from Definition 7.6.7.
-/
instance homotopyAutUContinuousMul : UContinuousMul (Aut(X)) where
  continuous_mul := homotopyAutContinuousMul X

/-- Helper for Definition 7.6.7: multiplication of path components in `Aut(X)` is induced by
pointwise composition of representative paths in the compactly generated mapping space. -/
private theorem joinedHomotopyAutMul {a b c d : Aut(X)}
    (ha : Joined a b) (hc : Joined c d) : Joined (a * c) (b * d) := by
  rcases ha with ⟨p⟩
  rcases hc with ⟨q⟩
  let pq : C(I, CompactlyGenerated.MapSpace X X × CompactlyGenerated.MapSpace X X) :=
    ⟨fun t ↦ (((p t : Aut(X)) : CompactlyGenerated.MapSpace X X),
        ((q t : Aut(X)) : CompactlyGenerated.MapSpace X X)),
      (continuous_subtype_val.comp p.continuous).prodMk
        (continuous_subtype_val.comp q.continuous)⟩
  have hcomp :
      Continuous fun t : I ↦
        CompactlyGenerated.MapSpace.ofContinuousMap
          ((((pq t).1 : C(X, X)).comp ((pq t).2 : C(X, X)))) :=
    continuousCompMapSpaceOfCompactSource X pq
  have hMaps :
      Joined (((a * c : Aut(X)) : CompactlyGenerated.MapSpace X X))
        (((b * d : Aut(X)) : CompactlyGenerated.MapSpace X X)) := by
    refine
      ⟨{ toFun := fun t ↦
            CompactlyGenerated.MapSpace.ofContinuousMap
              ((((pq t).1 : C(X, X)).comp ((pq t).2 : C(X, X)))),
          continuous_toFun := hcomp,
          source' := ?_,
          target' := ?_ }⟩
    · apply CompactlyGenerated.MapSpace.ext
      intro x
      simp [pq, p.source, q.source]
    · apply CompactlyGenerated.MapSpace.ext
      intro x
      simp [pq, p.target, q.target]
  exact joinedHomotopyAutOfJoinedMapSpace X hMaps

private theorem homotopyAutInv_joined {e₁ e₂ : Aut(X)} (h : Joined e₁ e₂) :
    Joined (homotopyAutInv X e₁) (homotopyAutInv X e₂) := by
  -- Forget the subtype path, invert it up to homotopy, and then lift back into `Aut(X)`.
  have hMaps :
      Joined (((e₁ : Aut(X)) : CompactlyGenerated.MapSpace X X))
        (((e₂ : Aut(X)) : CompactlyGenerated.MapSpace X X)) := by
    rcases h with ⟨p⟩
    exact ⟨p.map continuous_subtype_val⟩
  have hHom : ((e₁ : C(X, X))).Homotopic (e₂ : C(X, X)) :=
    homotopicOfJoinedMapSpace X hMaps
  have hInvHom : e₁.invFun.Homotopic e₂.invFun :=
    invFunHomotopicOfHomotopic X hHom
  have hInvMaps :
      Joined (CompactlyGenerated.MapSpace.ofContinuousMap e₁.invFun)
        (CompactlyGenerated.MapSpace.ofContinuousMap e₂.invFun) :=
    joinedMapSpaceOfHomotopic X hInvHom
  simpa [homotopyAutInv, HomotopyAut.invFun] using
    joinedHomotopyAutOfJoinedMapSpace X hInvMaps

/-- The path-component quotient `π₀ Aut(X)` has the unit induced by the identity
self-homotopy equivalence. -/
instance homotopyAutPi0One : One (ZerothHomotopy (Aut(X))) where
  one := Quotient.mk'' (1 : Aut(X))

/-- Multiplication on `π₀ Aut(X)` is induced from composition on representatives. -/
instance homotopyAutPi0Mul : Mul (ZerothHomotopy (Aut(X))) where
  mul := Quotient.map₂' (· * ·) fun _ _ h₁ _ _ h₂ ↦ joinedHomotopyAutMul X h₁ h₂

/-- Inversion on `π₀ Aut(X)` is induced from chosen inverse representatives. -/
noncomputable instance homotopyAutPi0Inv : Inv (ZerothHomotopy (Aut(X))) where
  inv := Quotient.map' (homotopyAutInv X) fun _ _ h ↦ homotopyAutInv_joined X h

/-- `π₀ Aut(X)` is a group under composition. -/
noncomputable instance homotopyAutPi0Group :
    Group (ZerothHomotopy (Aut(X))) :=
  Group.ofLeftAxioms
    (fun a b c ↦ by
      -- Associativity is inherited directly from the representative-level monoid law.
      refine Quotient.inductionOn₃ a b c ?_
      intro x y z
      rfl)
    (fun a ↦ by
      -- The path-component unit is represented by the monoid unit.
      refine Quotient.inductionOn a ?_
      intro x
      rfl)
    (fun a ↦ by
      -- The chosen inverse is left inverse up to homotopy on representatives.
      refine Quotient.inductionOn a ?_
      intro e
      apply Quotient.sound
      have hInvLeft :
          (ContinuousMap.comp e.invFun e).Homotopic (ContinuousMap.id X) :=
        HomotopyAut.invFun_left_inv X e
      have hJoinedMaps :
          Joined
            (CompactlyGenerated.MapSpace.ofContinuousMap (ContinuousMap.comp e.invFun e))
            (CompactlyGenerated.MapSpace.ofContinuousMap (ContinuousMap.id X)) :=
        joinedMapSpaceOfHomotopic X hInvLeft
      simpa [homotopyAutInv, HomotopyAut.invFun] using
        joinedHomotopyAutOfJoinedMapSpace X hJoinedMaps)

end CompactlyGenerated
