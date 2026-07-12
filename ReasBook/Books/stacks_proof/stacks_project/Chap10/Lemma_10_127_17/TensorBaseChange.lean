import StacksProject_2024.Chap10.Lemma_10_127_14
import StacksProject_2024.Chap10.Lemma_10_127_11_Pre
import Mathlib.Tactic.StacksAttribute

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.127.17: transport a tensor product across an equality of left-factor
algebra structures when the two tensor factors may live in different universes. -/
noncomputable def tensorRingEquivOfAlgEq_mixed
    {R : Type u} {Sj : Type v} {Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (let _ : Algebra R Sj := alg1; Sj ⊗[R] Rk) ≃+* (let _ : Algebra R Sj := alg2; Sj ⊗[R] Rk) := by
  subst halg
  exact RingEquiv.refl _

/-- Helper for Lemma 10.127.17: the reverse mixed-universe tensor bridge is the identity on pure
tensors once the left-factor algebra structures are identified. -/
theorem tensorRingEquivOfAlgEq_mixed_symm_tmul
    {R : Type u} {Sj : Type v} {Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) (x : Sj) (y : Rk) :
    (tensorRingEquivOfAlgEq_mixed (R := R) (Sj := Sj) (Rk := Rk) alg1 alg2 halg).symm
        (let _ : Algebra R Sj := alg2; x ⊗ₜ[R] y) =
      (let _ : Algebra R Sj := alg1; x ⊗ₜ[R] y) := by
  subst halg
  rfl

/-- Helper for Lemma 10.127.17: the reverse mixed-universe tensor bridge as a named ring
homomorphism. -/
noncomputable def tensorRingHomOfAlgEqSymm_mixed
    {R : Type u} {Sj : Type v} {Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (let _ : Algebra R Sj := alg2; Sj ⊗[R] Rk) →+* (let _ : Algebra R Sj := alg1; Sj ⊗[R] Rk) :=
  (tensorRingEquivOfAlgEq_mixed (R := R) (Sj := Sj) (Rk := Rk) alg1 alg2 halg).symm.toRingHom

/-- Helper for Lemma 10.127.17: when the algebra structures already agree, the reverse mixed
tensor bridge is the identity ring homomorphism. -/
theorem tensorRingHomOfAlgEqSymm_mixed_rfl
    {R : Type u} {Sj : Type v} {Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg : Algebra R Sj) :
    tensorRingHomOfAlgEqSymm_mixed (R := R) (Sj := Sj) (Rk := Rk) alg alg rfl = RingHom.id _ := by
  rfl

/-- Helper for Lemma 10.127.17: tensor an explicit algebra map on the left factor and the identity
on the right factor when the two tensor factors live in different universes. -/
noncomputable def tensorMapLeft_mixed
    {R : Type u} {A : Type u} {B : Type u} {C : Type v}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : A →ₐ[R] C) :
    A ⊗[R] B →+* C ⊗[R] B :=
  (Algebra.TensorProduct.map φ (AlgHom.id R B)).toRingHom

/-- Helper for Lemma 10.127.17: the mixed-universe left tensor map sends a pure tensor to the
image on the left and keeps the same right factor. -/
theorem tensorMapLeft_mixed_tmul
    {R : Type u} {A : Type u} {B : Type u} {C : Type v}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : A →ₐ[R] C) (x : A) (y : B) :
    tensorMapLeft_mixed φ (x ⊗ₜ[R] y) = φ x ⊗ₜ[R] y := by
  simp [tensorMapLeft_mixed, Algebra.TensorProduct.map_tmul]

/-- Helper for Lemma 10.127.17: tensoring a surjective left-factor map with the identity on the
right factor remains surjective. -/
theorem tensorMapLeft_mixed_surjective
    {R : Type u} {A : Type u} {B : Type u} {C : Type v}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : A →ₐ[R] C) (hφ : Function.Surjective φ) :
    Function.Surjective (tensorMapLeft_mixed (R := R) (A := A) (B := B) (C := C) φ) := by
  intro z
  -- Proof comment: tensor induction reduces surjectivity to pure tensors, where surjectivity of
  -- `φ` gives a preimage on the left factor.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨0, by simp [tensorMapLeft_mixed]⟩
  · intro x y
    obtain ⟨a, rfl⟩ := hφ x
    refine ⟨a ⊗ₜ[R] y, ?_⟩
    simp [tensorMapLeft_mixed_tmul]
  · intro x y hx hy
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    refine ⟨x' + y', ?_⟩
    simp

/-- Helper for Lemma 10.127.17: bijectivity descends along a surjective precomposition. -/
theorem bijective_of_surjective_of_bijective_comp
    {X Y Z : Type*} (β : X → Y) (f : Y → Z)
    (hβ : Function.Surjective β) (hcomp : Function.Bijective (f ∘ β)) :
    Function.Bijective f := by
  constructor
  · intro y₁ y₂ hy
    -- Proof comment: lift both source points through the surjective comparison map and use
    -- injectivity of the composite.
    obtain ⟨x₁, rfl⟩ := hβ y₁
    obtain ⟨x₂, rfl⟩ := hβ y₂
    exact congrArg β (hcomp.1 hy)
  · intro z
    -- Proof comment: first lift through the bijective composite, then project the lift through
    -- the comparison map.
    obtain ⟨x, hx⟩ := hcomp.2 z
    exact ⟨β x, hx⟩

/-
Domain sampling:
* Primary domain: directed approximation systems for finitely presented commutative ring maps and
  their stagewise base-change transitions.
* Owner declarations inspected in this domain:
  - `DirectedFiniteTypeHomApproximation`
  - `DirectedFiniteTypeHomApproximation.stageBaseChangeMap`
  - `RingHom.FinitePresentation`
* Best owner abstraction: `DirectedFiniteTypeHomApproximation f`.
* Layer triage:
  - `source-facing`: the existence theorem below
  - `core/canonical`: `DirectedFiniteTypeHomApproximation f`
  - `bridge/view`: the canonical stagewise base-change map and the stronger bijectivity condition
    on that map
* Primitive vs. derived:
  - primitive owner data: the directed system of source and target stages, transition maps,
    finite-type hypotheses, and colimit identifications
  - derived API here: the statement that the already canonical map
    `A.stageBaseChangeMap h : Sᵢ ⊗[Rᵢ] Rⱼ →+* Sⱼ` is bijective, hence an isomorphism
-/

namespace DirectedFiniteTypeHomApproximation

variable {f : R →+* S} (A : DirectedFiniteTypeHomApproximation f)

/-- The transition maps in a finite-presentation approximation identify each later target stage
with the canonical base change from an earlier one. -/
def HasBijectiveBaseChangeTransitions : Prop :=
  ∀ {i j : A.Λ} (h : i ≤ j), Function.Bijective (A.stageBaseChangeMap h)

/-- Helper for Lemma 10.127.17: on pure tensors, the finite-type owner base-change map multiplies
the target transition with the later stage map. This is the owner-level formula used to compare
the abstract base-change map with the explicit descended tensor cancellation. -/
theorem stageBaseChangeMap_tmul {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j h)).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.RStage j) (A.SStage j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ xS : A.SStage i,
      ∀ yR : A.RStage j,
        A.stageBaseChangeMap h (xS ⊗ₜ[A.RStage i] yR) = A.SMap i j h xS * A.stageMap j yR := by
  intro _instSi _instRj _instSj _instSjk _instTower xS yR
  -- Proof comment: unfold the owner base-change map and evaluate `productMap` on a pure tensor.
  simp only [DirectedFiniteTypeHomApproximation.stageBaseChangeMap]
  -- Proof comment: the private transition algebra hom is definitionally the target transition.
  change (A.SMap i j h xS) * A.stageMap j yR = (A.SMap i j h xS) * A.stageMap j yR
  rfl

/-- Helper for Lemma 10.127.17: after transporting the source tensor product across an equality of
left-factor algebra structures, the owner base-change map still has the expected pure-tensor
formula. -/
theorem stageBaseChangeMap_tensorBridge_tmul {i j : A.Λ} (h : i ≤ j)
    (algStage : Algebra (A.RStage i) (A.SStage i))
    (hinst : (A.stageMap i).toAlgebra = algStage)
    (xS : A.SStage i) (yR : A.RStage j) :
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
    ((A.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm_mixed (R := A.RStage i) (Sj := A.SStage i)
          (Rk := A.RStage j) ((A.stageMap i).toAlgebra) algStage hinst))
      (let _ : Algebra (A.RStage i) (A.SStage i) := algStage
       xS ⊗ₜ[A.RStage i] yR) =
      A.SMap i j h xS * A.stageMap j yR := by
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
  -- Proof comment: the tensor bridge is the identity on pure tensors, so the owner formula above
  -- applies immediately.
  dsimp [tensorRingHomOfAlgEqSymm_mixed]
  rw [tensorRingEquivOfAlgEq_mixed_symm_tmul]
  exact stageBaseChangeMap_tmul A h xS yR

/-- Helper for Lemma 10.127.17: after tensoring an explicit algebra hom on the left factor and
transporting the source tensor product across an algebra-instance bridge, the owner base-change
map still evaluates on pure tensors by the same multiplicative formula. -/
theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul
    {i j : A.Λ} (h : i ≤ j) {T : Type u} [CommRing T]
    [Algebra (A.RStage i) T]
    (algStage : Algebra (A.RStage i) (A.SStage i))
    (hinst : (A.stageMap i).toAlgebra = algStage)
    (φ : T →ₐ[A.RStage i] A.SStage i) (x : T) (y : A.RStage j) :
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := algStage
    ((A.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm_mixed (R := A.RStage i) (Sj := A.SStage i)
          (Rk := A.RStage j) ((A.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft_mixed (R := A.RStage i) (A := T) (B := A.RStage j)
        (C := A.SStage i) φ (x ⊗ₜ[A.RStage i] y)) =
      A.SMap i j h (φ x) * A.stageMap j y := by
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := algStage
  -- Proof comment: first normalize the explicit left tensor map on a pure tensor and then apply
  -- the bridged owner formula.
  simpa [tensorMapLeft_mixed_tmul] using
    (stageBaseChangeMap_tensorBridge_tmul A h algStage hinst (φ x) y)

/-- Helper for Lemma 10.127.17: rewrite the owner pure-tensor formula against explicit target and
stage maps in the mixed-universe setting. -/
theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul_pointwise_mixed
    {i j : A.Λ} (h : i ≤ j) {T : Type u} [CommRing T]
    [Algebra (A.RStage i) T]
    (algStage : Algebra (A.RStage i) (A.SStage i))
    (hinst : (A.stageMap i).toAlgebra = algStage)
    (φ : T →ₐ[A.RStage i] A.SStage i)
    (targetMapIJ : A.SStage i →+* A.SStage j)
    (stageMapJ : A.RStage j →+* A.SStage j)
    (htarget : ∀ z : A.SStage i, A.SMap i j h z = targetMapIJ z)
    (hstage : ∀ y : A.RStage j, A.stageMap j y = stageMapJ y)
    (x : T) (y : A.RStage j) :
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := algStage
    ((A.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm_mixed (R := A.RStage i) (Sj := A.SStage i)
          (Rk := A.RStage j) ((A.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft_mixed (R := A.RStage i) (A := T) (B := A.RStage j)
        (C := A.SStage i) φ (x ⊗ₜ[A.RStage i] y)) =
      targetMapIJ (φ x) * stageMapJ y := by
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := algStage
  calc
    ((A.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm_mixed (R := A.RStage i) (Sj := A.SStage i)
          (Rk := A.RStage j) ((A.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft_mixed (R := A.RStage i) (A := T) (B := A.RStage j)
        (C := A.SStage i) φ (x ⊗ₜ[A.RStage i] y)) =
        A.SMap i j h (φ x) * A.stageMap j y := by
      exact stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul
        A h algStage hinst φ x y
    _ = targetMapIJ (φ x) * stageMapJ y := by
      rw [htarget (φ x), hstage y]

end DirectedFiniteTypeHomApproximation

/-- Helper for Lemma 10.127.17: surjectivity transports across a conjugation square by source and
target ring equivalences. -/
theorem surjective_of_conjugate_by_ringEquivs
    {S1 S2 T1 T2 : Type*} [CommRing S1] [CommRing S2] [CommRing T1] [CommRing T2]
    (f : S1 →+* T1) (g : S2 →+* T2)
    (eS : S2 ≃+* S1) (eT : T2 ≃+* T1)
    (hconj : f.comp eS.toRingHom = eT.toRingHom.comp g)
    (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro y
  obtain ⟨x, hx⟩ := hg (eT.symm y)
  refine ⟨eS x, ?_⟩
  -- Proof comment: evaluate the conjugation square at the chosen preimage of `eT.symm y`.
  have hpoint := congrArg (fun h : S2 →+* T1 ↦ h x) hconj
  simpa [hx] using hpoint

/-- Helper for Lemma 10.127.17: kernels transport across a conjugation square by source and target
ring equivalences. -/
theorem ker_eq_map_ker_of_conjugate_by_ringEquivs
    {S1 S2 T1 T2 : Type*} [CommRing S1] [CommRing S2] [CommRing T1] [CommRing T2]
    (f : S1 →+* T1) (g : S2 →+* T2)
    (eS : S2 ≃+* S1) (eT : T2 ≃+* T1)
    (hconj : f.comp eS.toRingHom = eT.toRingHom.comp g) :
    RingHom.ker f = Ideal.map eS.toRingHom (RingHom.ker g) := by
  -- Proof comment: pull the kernel of `f` back along the source equivalence, rewrite by the
  -- conjugation square, and then push forward again along the same equivalence.
  rw [← Ideal.map_comap_of_surjective (f := eS.toRingHom) eS.surjective (RingHom.ker f)]
  rw [RingHom.comap_ker, hconj, RingHom.ker_equiv_comp]

/-- Helper for Lemma 10.127.17: two ring homomorphisms out of a tensor product agree as soon as
they agree on all pure tensors. -/
theorem ringHom_eq_of_tmul
    {R : Type u} {A : Type v} {B : Type w} {C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B]
    {φ ψ : A ⊗[R] B →+* C}
    (h : ∀ x : A, ∀ y : B, φ (x ⊗ₜ[R] y) = ψ (x ⊗ₜ[R] y)) :
    φ = ψ := by
  apply RingHom.ext
  intro z
  -- Proof comment: pure tensors generate the tensor product additively, so tensor induction
  -- upgrades the pointwise formula to all elements.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    exact h x y
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 10.127.17: a comparison map between two surjective ring homomorphisms out of
the same source is bijective once the compositions agree and the two source kernels coincide. -/
theorem bijective_of_comp_eq_of_surjective_of_ker_eq
    {T : Type*} {U : Type*} {V : Type*}
    [CommRing T] [CommRing U] [CommRing V]
    {β : T →+* U} {γ : T →+* V} {φ : U →+* V}
    (hcomp : φ.comp β = γ)
    (hβ_surj : Function.Surjective β)
    (hγ_surj : Function.Surjective γ)
    (hker : RingHom.ker β = RingHom.ker γ) :
    Function.Bijective φ := by
  constructor
  · intro u v huv
    rcases hβ_surj u with ⟨tu, rfl⟩
    rcases hβ_surj v with ⟨tv, rfl⟩
    -- Proof comment: compare the two chosen source lifts inside the common source kernel.
    have hγ_eq : γ tu = γ tv := by
      have hcomp_tu := congrArg (fun h : T →+* V ↦ h tu) hcomp
      have hcomp_tv := congrArg (fun h : T →+* V ↦ h tv) hcomp
      calc
        γ tu = φ (β tu) := by simpa [RingHom.comp_apply] using hcomp_tu.symm
        _ = φ (β tv) := huv
        _ = γ tv := by simpa [RingHom.comp_apply] using hcomp_tv
    have hγ_sub : γ (tu - tv) = 0 := by
      rw [map_sub, hγ_eq, sub_self]
    have hβ_sub : β (tu - tv) = 0 := by
      have hmemγ : tu - tv ∈ RingHom.ker γ := by
        exact RingHom.mem_ker.mpr hγ_sub
      have hmemβ : tu - tv ∈ RingHom.ker β := by
        simpa [hker] using hmemγ
      exact RingHom.mem_ker.mp hmemβ
    have hβ_eq : β tu = β tv := by
      exact sub_eq_zero.mp (by simpa [map_sub] using hβ_sub)
    simpa using hβ_eq
  · intro y
    rcases hγ_surj y with ⟨t, rfl⟩
    refine ⟨β t, ?_⟩
    exact congrArg (fun h : T →+* V ↦ h t) hcomp

/-- Helper for Lemma 10.127.17: restricting a ring homomorphism to its image does not change its
kernel. -/
theorem ker_rangeRestrict_eq
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    RingHom.ker φ.rangeRestrict = RingHom.ker φ := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa using h

/-- Helper for Lemma 10.127.17: the kernel of a composition with a range restriction is the comap
of the original kernel along the preceding ring homomorphism. -/
theorem ker_comp_rangeRestrict_eq_comap_ker
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : B →+* C) (e : A →+* B) :
    RingHom.ker (φ.rangeRestrict.comp e) = Ideal.comap e (RingHom.ker φ) := by
  -- Proof comment: first rewrite the kernel of the composition as a comap, then remove the
  -- harmless range restriction from `φ`.
  calc
    RingHom.ker (φ.rangeRestrict.comp e) =
        Ideal.comap e (RingHom.ker φ.rangeRestrict) := by
          symm
          simpa using (RingHom.comap_ker φ.rangeRestrict e)
    _ = Ideal.comap e (RingHom.ker φ) := by
          rw [ker_rangeRestrict_eq]

/-- Helper for Lemma 10.127.17: composing a range restriction with a ring equivalence has kernel
equal to the comap of the original kernel along that equivalence. -/
theorem ker_rangeRestrict_comp_equiv_eq_comap_ker
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : B →+* C) (e : A ≃+* B) :
    RingHom.ker (φ.rangeRestrict.comp e.toRingHom) = Ideal.comap e.toRingHom (RingHom.ker φ) := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · intro hz
    exact congrArg Subtype.val hz
  · intro hz
    exact Subtype.ext hz

/-- Helper for Lemma 10.127.17: once the image-stage transition and later stage map are identified
on underlying elements in `S`, their product agrees with the raw tensor cancellation formula on
pure tensors. -/
theorem range_stage_targetMap_mul_stageMap_eq_sigma_cancel
    {Rj : Type u} {Rk : Type u} {RawJ : Type u} {RawK : Type u}
    [CommRing Rj] [CommRing Rk] [CommRing RawJ] [CommRing RawK]
    [Algebra Rj RawJ] [Algebra Rj Rk] [Algebra Rk RawK]
    {TargetJ : Type*} {TargetK : Type*} [CommRing TargetJ] [CommRing TargetK]
    [Algebra Rj TargetJ]
    (σj : RawJ →+* S) (σk : RawK →+* S)
    (toAmbientK : TargetK →+* S)
    (leftAlgHom : RawJ →ₐ[Rj] TargetJ)
    (targetMapJK : TargetJ →+* TargetK)
    (stageMapK : Rk →+* TargetK)
    (cancel : RawJ ⊗[Rj] Rk ≃+* RawK)
    (rawMapJK : RawJ →+* RawK)
    (hleft_target : ∀ x : RawJ, toAmbientK (targetMapJK (leftAlgHom x)) = σj x)
    (hstage : ∀ r' : Rk, toAmbientK (stageMapK r') = σk (algebraMap Rk RawK r'))
    (hσ_comp : σj = σk.comp rawMapJK)
    (hcancel : ∀ x : RawJ, ∀ r' : Rk,
      cancel (x ⊗ₜ[Rj] r') = rawMapJK x * algebraMap Rk RawK r')
    (x : RawJ) (r' : Rk) :
    toAmbientK (targetMapJK (leftAlgHom x) * stageMapK r') =
      σk (cancel (x ⊗ₜ[Rj] r')) := by
  -- Proof comment: pass the product through the chosen ambient ring map, rewrite each factor by
  -- the stagewise identifications, and then use multiplicativity of `σk`.
  rw [map_mul, hleft_target, hstage, hσ_comp]
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  congr 1
  exact (hcancel x r').symm
