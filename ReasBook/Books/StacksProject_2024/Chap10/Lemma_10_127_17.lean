import stacks_project.Chap10.Lemma_10_127_14
import stacks_project.Chap10.Lemma_10_127_11_Pre

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.127.17: transport a tensor product across an equality of left-factor
algebra structures when the two tensor factors may live in different universes. -/
private noncomputable def tensorRingEquivOfAlgEq_mixed
    {R : Type u} {Sj : Type v} {Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (let _ : Algebra R Sj := alg1; Sj ⊗[R] Rk) ≃+* (let _ : Algebra R Sj := alg2; Sj ⊗[R] Rk) := by
  subst halg
  exact RingEquiv.refl _

/-- Helper for Lemma 10.127.17: the reverse mixed-universe tensor bridge is the identity on pure
tensors once the left-factor algebra structures are identified. -/
private theorem tensorRingEquivOfAlgEq_mixed_symm_tmul
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
private noncomputable def tensorRingHomOfAlgEqSymm_mixed
    {R : Type u} {Sj : Type v} {Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (let _ : Algebra R Sj := alg2; Sj ⊗[R] Rk) →+* (let _ : Algebra R Sj := alg1; Sj ⊗[R] Rk) :=
  (tensorRingEquivOfAlgEq_mixed (R := R) (Sj := Sj) (Rk := Rk) alg1 alg2 halg).symm.toRingHom

/-- Helper for Lemma 10.127.17: when the algebra structures already agree, the reverse mixed
tensor bridge is the identity ring homomorphism. -/
private theorem tensorRingHomOfAlgEqSymm_mixed_rfl
    {R : Type u} {Sj : Type v} {Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg : Algebra R Sj) :
    tensorRingHomOfAlgEqSymm_mixed (R := R) (Sj := Sj) (Rk := Rk) alg alg rfl = RingHom.id _ := by
  rfl

/-- Helper for Lemma 10.127.17: tensor an explicit algebra map on the left factor and the identity
on the right factor when the two tensor factors live in different universes. -/
private noncomputable def tensorMapLeft_mixed
    {R : Type u} {A : Type u} {B : Type u} {C : Type v}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : A →ₐ[R] C) :
    A ⊗[R] B →+* C ⊗[R] B :=
  (Algebra.TensorProduct.map φ (AlgHom.id R B)).toRingHom

/-- Helper for Lemma 10.127.17: the mixed-universe left tensor map sends a pure tensor to the
image on the left and keeps the same right factor. -/
private theorem tensorMapLeft_mixed_tmul
    {R : Type u} {A : Type u} {B : Type u} {C : Type v}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : A →ₐ[R] C) (x : A) (y : B) :
    tensorMapLeft_mixed φ (x ⊗ₜ[R] y) = φ x ⊗ₜ[R] y := by
  simp [tensorMapLeft_mixed, Algebra.TensorProduct.map_tmul]

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
private theorem stageBaseChangeMap_tmul {i j : A.Λ} (h : i ≤ j) :
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
  simp [DirectedFiniteTypeHomApproximation.stageBaseChangeMap,
    Algebra.TensorProduct.productMap_apply_tmul, RingHom.algebraMap_toAlgebra]
  -- Proof comment: the private transition algebra hom is definitionally the target transition.
  change (A.SMap i j h xS) * A.stageMap j yR = (A.SMap i j h xS) * A.stageMap j yR
  rfl

/-- Helper for Lemma 10.127.17: after transporting the source tensor product across an equality of
left-factor algebra structures, the owner base-change map still has the expected pure-tensor
formula. -/
private theorem stageBaseChangeMap_tensorBridge_tmul {i j : A.Λ} (h : i ≤ j)
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
private theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul
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
private theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul_pointwise_mixed
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
private theorem surjective_of_conjugate_by_ringEquivs
    {S₁ S₂ T₁ T₂ : Type*} [CommRing S₁] [CommRing S₂] [CommRing T₁] [CommRing T₂]
    (f : S₁ →+* T₁) (g : S₂ →+* T₂)
    (eS : S₂ ≃+* S₁) (eT : T₂ ≃+* T₁)
    (hconj : f.comp eS.toRingHom = eT.toRingHom.comp g)
    (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro y
  obtain ⟨x, hx⟩ := hg (eT.symm y)
  refine ⟨eS x, ?_⟩
  -- Proof comment: evaluate the conjugation square at the chosen preimage of `eT.symm y`.
  have hpoint := congrArg (fun h : S₂ →+* T₁ ↦ h x) hconj
  simpa [hx] using hpoint

/-- Helper for Lemma 10.127.17: two ring homomorphisms out of a tensor product agree as soon as
they agree on all pure tensors. -/
private theorem ringHom_eq_of_tmul
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
private theorem bijective_of_comp_eq_of_surjective_of_ker_eq
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
private theorem ker_rangeRestrict_eq
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
private theorem ker_comp_rangeRestrict_eq_comap_ker
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
private theorem ker_rangeRestrict_comp_equiv_eq_comap_ker
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
private theorem range_stage_targetMap_mul_stageMap_eq_sigma_cancel
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

/-- Helper for Lemma 10.127.17: a finite-presentation approximation of `f` starts by choosing an
approximation of `id_R` and descending one finitely presented `R`-algebra model of `S` to a
single source stage of that approximation. -/
theorem exists_descended_finitePresentation_stage_model
    (f : R →+* S) (hf : f.FinitePresentation) :
    ∃ (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
      (P₀ : Type u) (_ : CommRing P₀) (_ : Algebra (A₀.RStage i₀) P₀)
      (_ : Algebra.FinitePresentation (A₀.RStage i₀) P₀),
      letI := f.toAlgebra
      letI : Algebra (A₀.RStage i₀) R :=
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource i₀).toAlgebra
      letI : Algebra R (P₀ ⊗[A₀.RStage i₀] R) := Algebra.TensorProduct.rightAlgebra
      Nonempty (P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] S) := by
  classical
  letI := f.toAlgebra
  obtain ⟨A₀⟩ := exists_directedFiniteTypeHomApproximation (RingHom.id R)
  have hSfp : Algebra.FinitePresentation R S := by
    -- Reinterpret the finite-presentation hypothesis on `f` as an algebra-level instance.
    rw [← RingHom.finitePresentation_algebraMap]
    exact hf
  obtain ⟨i₀, P₀, _, _, _, e⟩ :=
    finitelyPresented_algebra_is_baseChange_of_stage
      (RStage := A₀.RStage)
      (map := fun i j h ↦ A₀.RMap i j h)
      (colimitIso := A₀.colimitSource)
      S
  exact ⟨A₀, i₀, P₀, inferInstance, inferInstance, inferInstance, e⟩

/-- Helper for Lemma 10.127.17: the descended raw tensor stage over a tail index is finite type
over the corresponding source stage. -/
private theorem descended_tail_raw_stage_finiteType
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    {P₀ : Type u} [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀] (j : Set.Ici i₀)
    [Algebra (A₀.RStage i₀) (A₀.RStage j.1)] :
    (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)).FiniteType := by
  let baseChangedStage : Type u := A₀.RStage j.1 ⊗[A₀.RStage i₀] P₀
  let baseChangedComm :
      baseChangedStage ≃+* (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) :=
    (Algebra.TensorProduct.comm
      (R := A₀.RStage i₀) (A := A₀.RStage j.1) (B := P₀)).toRingEquiv
  have hbaseChanged_finiteType :
      (algebraMap (A₀.RStage j.1) baseChangedStage).FiniteType := by
    let _ : Algebra.FinitePresentation (A₀.RStage j.1) baseChangedStage := by
      -- Proof comment: base change preserves the descended finite-presentation model.
      exact Algebra.FinitePresentation.baseChange
        (R := A₀.RStage i₀) (A := P₀) (B := A₀.RStage j.1)
    -- Proof comment: finite presentation over the later source stage implies finite type.
    exact RingHom.finiteType_algebraMap.mpr Algebra.FiniteType.of_finitePresentation
  have hbaseChanged_comp :
      baseChangedComm.toRingHom.comp (algebraMap (A₀.RStage j.1) baseChangedStage) =
        algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) := by
    ext x
    rfl
  -- Proof comment: transport the literal base-change finite-type map across tensor commutation.
  rw [← hbaseChanged_comp]
  exact RingHom.FiniteType.comp
    (RingHom.FiniteType.of_surjective _ baseChangedComm.surjective)
    hbaseChanged_finiteType

/-- Helper for Lemma 10.127.17: replacing a raw tensor stage by its image inside `S` preserves the
finite-type stage map from the corresponding source stage. -/
private theorem descended_tail_range_stage_finiteType
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    {P₀ : Type u} [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) [Algebra (A₀.RStage i₀) (A₀.RStage j.1)]
    (σj : (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) →+* S) :
    (((σj).comp (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))).codRestrict
      σj.range (fun x ↦ by
        show ((σj.comp (algebraMap (A₀.RStage j.1)
          (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))) x) ∈ σj.range
        exact ⟨(algebraMap (A₀.RStage j.1)
          (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)) x, rfl⟩)).FiniteType := by
  have hstageMapTail_comp :
      (((σj).comp
          (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))).codRestrict
        σj.range (fun x ↦ by
          show ((σj.comp (algebraMap (A₀.RStage j.1)
            (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))) x) ∈ σj.range
          exact ⟨(algebraMap (A₀.RStage j.1)
            (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)) x, rfl⟩)) =
        ((σj).rangeRestrict).comp
          (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)) := by
    ext x
    rfl
  -- Proof comment: pass from the raw tensor stage to its image via the surjective range map.
  rw [hstageMapTail_comp]
  exact RingHom.FiniteType.comp_surjective
    (descended_tail_raw_stage_finiteType A₀ i₀ (P₀ := P₀) j)
    σj.rangeRestrict_surjective

section FinalTransition

variable {f : R →+* S}
variable (A : DirectedFiniteTypeHomApproximation.{u, v, u} f)
variable {j k : A.Λ} (hjk : j ≤ k)
variable {RawJ : Type u} {RawK : Type u} [CommRing RawJ] [CommRing RawK]
variable [Algebra (A.RStage j) RawJ] [Algebra (A.RStage k) RawK]
variable [Algebra (A.RStage j) (A.RStage k)]

/-- Helper for Lemma 10.127.17: the kernel of the packaged map
`(σk).rangeRestrict.comp cancel.toRingHom` is the comap of `ker σk` along `cancel`. -/
private theorem gamma_ker_eq_comap_cancel_ker_sigma
    (σk : RawK →+* S)
    (cancel : RawJ ⊗[A.RStage j] A.RStage k ≃+* RawK) :
    RingHom.ker ((σk).rangeRestrict.comp cancel.toRingHom) =
      Ideal.comap cancel.toRingHom (RingHom.ker σk) := by
  -- Proof comment: composing with a range restriction does not change the kernel, so only the
  -- comap along `cancel` remains.
  simpa using
    (ker_comp_rangeRestrict_eq_comap_ker (φ := σk) (e := cancel.toRingHom))

/-- Helper for Lemma 10.127.17: restricting a raw stage map to its image does not change the
underlying kernel ideal. -/
private theorem ker_leftAlgHom_eq_ker_sigma_tail
    (σj : RawJ →+* S) :
    RingHom.ker (σj.rangeRestrict : RawJ →+* σj.range) = RingHom.ker σj := by
  -- Proof comment: this is exactly the general kernel invariance for range restrictions.
  simpa using (ker_rangeRestrict_eq σj)

/-- Helper for Lemma 10.127.17: after passing to the ambient ring `S`, the owner base-change map
agrees on pure tensors with the explicit raw tensor cancellation formula at the final tail
transition. -/
private theorem stage_baseChangeMap_comp_beta_eq_gamma_in_ambient_tail
    (σj : RawJ →+* S)
    (σk : RawK →+* S)
    (toAmbientK : A.SStage k →+* S)
    (leftAlgHom :
      let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
      RawJ →ₐ[A.RStage j] A.SStage j)
    (cancel : RawJ ⊗[A.RStage j] A.RStage k ≃+* RawK)
    (rawMapJK : RawJ →+* RawK)
    (hleft_target : ∀ x : RawJ, toAmbientK (A.SMap j k hjk (leftAlgHom x)) = σj x)
    (hstage : ∀ r' : A.RStage k,
      toAmbientK (A.stageMap k r') = σk (algebraMap (A.RStage k) RawK r'))
    (hσ_comp : σj = σk.comp rawMapJK)
    (hcancel : ∀ x : RawJ, ∀ r' : A.RStage k,
      cancel (x ⊗ₜ[A.RStage j] r') = rawMapJK x * algebraMap (A.RStage k) RawK r')
    (x : RawJ) (r' : A.RStage k) :
    toAmbientK
      (((A.stageBaseChangeMap hjk).comp
          (tensorMapLeft_mixed (R := A.RStage j) (A := RawJ) (B := A.RStage k)
            (C := A.SStage j) leftAlgHom))
        (x ⊗ₜ[A.RStage j] r')) =
      σk (cancel (x ⊗ₜ[A.RStage j] r')) := by
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  -- Proof comment: first rewrite the owner base-change map on pure tensors, then identify the
  -- resulting product in `A.SStage k` with the raw tensor cancellation after embedding into `S`.
  have howner :
      ((A.stageBaseChangeMap hjk).comp
          (tensorMapLeft_mixed (R := A.RStage j) (A := RawJ) (B := A.RStage k)
            (C := A.SStage j) leftAlgHom))
        (x ⊗ₜ[A.RStage j] r') =
        A.SMap j k hjk (leftAlgHom x) * A.stageMap k r' := by
    simpa [tensorRingHomOfAlgEqSymm_mixed_rfl] using
      (DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul_pointwise_mixed
        (A := A) (i := j) (j := k) hjk ((A.stageMap j).toAlgebra) rfl leftAlgHom
        (A.SMap j k hjk) (A.stageMap k)
        (by intro z; rfl) (by intro y; rfl) x r')
  calc
    toAmbientK
        (((A.stageBaseChangeMap hjk).comp
            (tensorMapLeft_mixed (R := A.RStage j) (A := RawJ) (B := A.RStage k)
              (C := A.SStage j) leftAlgHom))
          (x ⊗ₜ[A.RStage j] r')) =
        toAmbientK (A.SMap j k hjk (leftAlgHom x) * A.stageMap k r') := by
          rw [howner]
    _ = σk (cancel (x ⊗ₜ[A.RStage j] r')) := by
      exact range_stage_targetMap_mul_stageMap_eq_sigma_cancel
        σj σk toAmbientK leftAlgHom (A.SMap j k hjk) (A.stageMap k)
        cancel rawMapJK hleft_target hstage hσ_comp hcancel x r'

/-- Helper for Lemma 10.127.17: the final transition comparison between the owner base-change map
and the raw tensor cancellation is determined by their agreement after embedding in `S`. -/
private theorem stage_baseChangeMap_comp_beta_eq_gamma
    (σj : RawJ →+* S)
    (σk : RawK →+* S)
    (toAmbientK : A.SStage k →+* S)
    (leftAlgHom :
      let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
      RawJ →ₐ[A.RStage j] A.SStage j)
    (cancel : RawJ ⊗[A.RStage j] A.RStage k ≃+* RawK)
    (rawMapJK : RawJ →+* RawK)
    (gamma : RawJ ⊗[A.RStage j] A.RStage k →+* A.SStage k)
    (hambient_injective : Function.Injective toAmbientK)
    (hleft_target : ∀ x : RawJ, toAmbientK (A.SMap j k hjk (leftAlgHom x)) = σj x)
    (hstage : ∀ r' : A.RStage k,
      toAmbientK (A.stageMap k r') = σk (algebraMap (A.RStage k) RawK r'))
    (hσ_comp : σj = σk.comp rawMapJK)
    (hcancel : ∀ x : RawJ, ∀ r' : A.RStage k,
      cancel (x ⊗ₜ[A.RStage j] r') = rawMapJK x * algebraMap (A.RStage k) RawK r')
    (hgamma : ∀ x : RawJ, ∀ r' : A.RStage k,
      toAmbientK (gamma (x ⊗ₜ[A.RStage j] r')) = σk (cancel (x ⊗ₜ[A.RStage j] r'))) :
    ((A.stageBaseChangeMap hjk).comp
        (tensorMapLeft_mixed (R := A.RStage j) (A := RawJ) (B := A.RStage k)
          (C := A.SStage j) leftAlgHom)) = gamma := by
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  -- Proof comment: pure tensors generate the source tensor product, and the ambient inclusion of
  -- the target stage is injective, so it suffices to compare both maps after embedding in `S`.
  apply ringHom_eq_of_tmul
  intro x r'
  apply hambient_injective
  calc
    toAmbientK
        (((A.stageBaseChangeMap hjk).comp
            (tensorMapLeft_mixed (R := A.RStage j) (A := RawJ) (B := A.RStage k)
              (C := A.SStage j) leftAlgHom))
          (x ⊗ₜ[A.RStage j] r')) =
        σk (cancel (x ⊗ₜ[A.RStage j] r')) := by
          exact stage_baseChangeMap_comp_beta_eq_gamma_in_ambient_tail
            (A := A) hjk σj σk toAmbientK leftAlgHom cancel rawMapJK
            hleft_target hstage hσ_comp hcancel x r'
    _ = toAmbientK (gamma (x ⊗ₜ[A.RStage j] r')) := by
      symm
      exact hgamma x r'

end FinalTransition

-- Proof sketch: the verified prefix above gives the descended stage model `P₀` over one source
-- stage `Rᵢ₀`. The remaining source-faithful step is to replace the raw tensor stages
-- `P₀ ⊗[Rᵢ₀] Rⱼ` by canonical target stages in the universe of `S` and transport the tensor-tail
-- transition isomorphisms through those stage identifications.
/-- Lemma 10.127.17: if `f : R →+* S` is of finite presentation, then `f` is the direct limit of a
directed system of ring maps `R_λ → S_λ` such that each `R_λ` is of finite type over `ℤ`, each
`S_λ` is of finite type over `R_λ`, and for every `λ ≤ μ` the canonical map
`S_λ ⊗[R_λ] R_μ → S_μ` is bijective, hence an isomorphism. -/
theorem exists_directedFinitePresentationHomApproximation (f : R →+* S)
    (hf : f.FinitePresentation) :
    ∃ A : DirectedFiniteTypeHomApproximation.{u, v, u} f, A.HasBijectiveBaseChangeTransitions := by
  classical
  obtain ⟨A₀, i₀, P₀, _instP₀, _instAlgP₀, _instFpP₀, ⟨e⟩⟩ :=
    exists_descended_finitePresentation_stage_model f hf
  letI := f.toAlgebra
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
      A₀.colimitSource i₀).toAlgebra
  have hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀ :=
    rfl
  let tail : Type u := Set.Ici i₀
  letI : Preorder tail := inferInstance
  letI : Nonempty tail := inferInstance
  letI : IsDirectedOrder tail := tail_index_isDirected i₀
  let rawStage : tail → Type u := fun j ↦
    let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1
  let rawMap : ∀ j k : tail, j ≤ k → rawStage j →+* rawStage k := fun j k hjk ↦
    let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
    (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
      { toRingHom := A₀.RMap j.1 k.1 hjk
        commutes' := fun x ↦
          DirectedSystem.map_map (f := fun i j h ↦ A₀.RMap i j h) j.2 hjk x } :
      _ →+* _)
  let σ : (j : tail) → rawStage j →+* S := fun j ↦
    let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A₀.RStage j.1) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.1).toAlgebra
    let _ : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.2
    e.toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
        (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage j.1) R) :
        _ →+* _)
  have hσ_comp :
      ∀ j : tail,
        (σ j).comp (algebraMap (A₀.RStage j.1) (rawStage j)) =
          f.comp
            (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              A₀.colimitSource j.1) := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.1).toAlgebra
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.2
    refine RingHom.ext fun x ↦ ?_
    -- The raw tensor comparison sends the right-factor generator to the image of `x` in `R`.
    have hraw :
        (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
            (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage j.1) R))
          ((algebraMap (A₀.RStage j.1) (rawStage j)) x) =
        algebraMap R (P₀ ⊗[A₀.RStage i₀] R)
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1) x) := by
      rfl
    calc
      (σ j) ((algebraMap (A₀.RStage j.1) (rawStage j)) x)
          = e
              ((Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
                (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage j.1) R))
                ((algebraMap (A₀.RStage j.1) (rawStage j)) x)) := rfl
      _ = e
            (algebraMap R (P₀ ⊗[A₀.RStage i₀] R)
              ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
                A₀.colimitSource j.1) x)) := by rw [hraw]
      _ = algebraMap R S
            ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              A₀.colimitSource j.1) x) := by
            exact e.commutes ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              A₀.colimitSource j.1) x)
      _ = f ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1) x) := rfl
  have hσ_raw_comp :
      ∀ j k : tail, ∀ hjk : j ≤ k, σ j = (σ k).comp (rawMap j k hjk) := by
    intro j k hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.1).toAlgebra
    letI : Algebra (A₀.RStage k.1) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource k.1).toAlgebra
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.2
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage k.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource k.2
    refine RingHom.ext fun x ↦ ?_
    -- Both raw comparisons only depend on the induced image of the right factor in `R`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp only [map_zero]
    · intro x y
      simp only [σ, rawMap, RingHom.comp_apply]
      have hy :
          Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              A₀.colimitSource k.1 ((A₀.RMap j.1 k.1 hjk) y) =
            Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              A₀.colimitSource j.1 y := by
        simp [Ring.DirectLimit.toLimitHom, Ring.DirectLimit.of_f]
      exact (congrArg (fun z ↦ e z)
        (congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r) hy)).symm
    · intro x y hx hy
      simp [map_add, hx, hy]
  have rawMap_id : ∀ j : tail, rawMap j j le_rfl = RingHom.id _ := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- The raw tensor transition over a fixed stage acts as the identity on the right factor.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap, RingHom.id_apply]
      exact congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r)
        (DirectedSystem.map_self (f := fun i j h ↦ A₀.RMap i j h) y)
    · intro x y hx hy
      simp [map_add, hx, hy]
  have rawMap_comp :
      ∀ i j k : tail, ∀ hij : i ≤ j, ∀ hjk : j ≤ k,
        rawMap i k (le_trans hij hjk) = (rawMap j k hjk).comp (rawMap i j hij) := by
    intro i j k hij hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.RMap i₀ i.1 i.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- Composition is inherited from the source directed system because only the right factor moves.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap, RingHom.comp_apply]
      exact congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r)
        (DirectedSystem.map_map (f := fun i j h ↦ A₀.RMap i j h) hij hjk y).symm
    · intro x y hx hy
      simp [map_add, hx, hy]
  letI : DirectedSystem rawStage (fun j k h ↦ rawMap j k h) :=
    { map_self := fun j x ↦ by
        simpa using congrArg (fun g : rawStage j →+* rawStage j ↦ g x) (rawMap_id j)
      map_map := fun {k j i} hij hjk x ↦ by
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : rawStage i →+* rawStage k ↦ g x)
            (rawMap_comp i j k hij hjk)).symm }
  let rangeStage : tail → Type v := fun j ↦ (σ j).range
  have hrange_mono :
      ∀ j k : tail, ∀ hjk : j ≤ k, (σ j).range ≤ (σ k).range := by
    intro j k hjk x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨rawMap j k hjk y, ?_⟩
    simpa [RingHom.comp_apply] using
      (congrArg (fun g : rawStage j →+* S ↦ g y) (hσ_raw_comp j k hjk)).symm
  let targetMap : ∀ j k : tail, j ≤ k → rangeStage j →+* rangeStage k := fun j k hjk ↦
    Subring.inclusion (hrange_mono j k hjk)
  have targetMap_id : ∀ j : tail, targetMap j j le_rfl = RingHom.id _ := by
    intro j
    refine RingHom.ext fun x ↦ ?_
    rfl
  have targetMap_comp :
      ∀ i j k : tail, ∀ hij : i ≤ j, ∀ hjk : j ≤ k,
        targetMap i k (le_trans hij hjk) = (targetMap j k hjk).comp (targetMap i j hij) := by
    intro i j k hij hjk
    refine RingHom.ext fun x ↦ ?_
    rfl
  haveI : DirectedSystem rangeStage (fun j k h ↦ targetMap j k h) :=
    { map_self := fun j x ↦ by
        simpa using congrArg (fun g : rangeStage j →+* rangeStage j ↦ g x) (targetMap_id j)
      map_map := fun {k j i} hij hjk x ↦ by
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : rangeStage i →+* rangeStage k ↦ g x)
            (targetMap_comp i j k hij hjk)).symm }
  let stageMapTail : ∀ j : tail, A₀.RStage j.1 →+* rangeStage j := fun j ↦
    (((σ j).comp (algebraMap (A₀.RStage j.1) (rawStage j))).codRestrict (σ j).range
      fun x ↦ ⟨(algebraMap (A₀.RStage j.1) (rawStage j)) x, rfl⟩)
  have hstageMapTail_apply : ∀ (j : tail) (x : A₀.RStage j.1),
      ((stageMapTail j) x : S) =
        (σ j) ((algebraMap (A₀.RStage j.1) (rawStage j)) x) := by
    intro j x
    rfl
  have hcommTail :
      ∀ {j k : tail} (hjk : j ≤ k),
        (stageMapTail k).comp (A₀.RMap j.1 k.1 hjk) =
          (targetMap j k hjk).comp (stageMapTail j) := by
    intro j k hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    apply Subtype.ext
    -- The image-stage square commutes because `σ` is compatible with the raw tensor transitions.
    change
      (σ k) ((algebraMap (A₀.RStage k.1) (rawStage k)) ((A₀.RMap j.1 k.1 hjk) x)) =
        (σ j) ((algebraMap (A₀.RStage j.1) (rawStage j)) x)
    rw [hσ_raw_comp j k hjk]
    change
      (σ k) ((1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.RMap j.1 k.1 hjk) x)) =
        (σ k) (rawMap j k hjk ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x))
    congr 1
  have hstageMapTail_finiteType :
      ∀ j : tail, (stageMapTail j).FiniteType := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    -- Proof comment: this is exactly the standalone finite-type lemma for image stages.
    simpa [stageMapTail, rawStage] using
      (descended_tail_range_stage_finiteType A₀ i₀ (P₀ := P₀) j (σ j))
  letI : DirectedSystem (fun j : tail ↦ A₀.RStage j.1) (fun j k h ↦ A₀.RMap j.1 k.1 h) :=
    tail_directedSystem A₀.RStage (fun i j h ↦ A₀.RMap i j h) i₀
  let rawToAmbient : (j : tail) → rawStage j →+* (P₀ ⊗[A₀.RStage i₀] R) := fun j ↦
    let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A₀.RStage j.1) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.1).toAlgebra
    let _ : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.2
    (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
      (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage j.1) R) : _ →+* _)
  have hrawToAmbient_comp :
      ∀ j k : tail, ∀ hjk : j ≤ k,
        rawToAmbient j = (rawToAmbient k).comp (rawMap j k hjk) := by
    intro j k hjk
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: cancel the fixed comparison `e` from the already established `σ`-compatibility.
    apply e.injective
    simpa [σ, rawToAmbient, RingHom.comp_assoc, RingHom.comp_apply] using
      congrArg (fun g : rawStage j →+* S => g x) (hσ_raw_comp j k hjk)
  -- Route correction: instead of rebuilding a monolithic inverse for the target colimit, first
  -- show that every tensor already appears on one raw tail stage, then push that cover through `e`
  -- to get a stagewise cover of `S`.
  have tail_source_cover :
      ∀ r : R, ∃ j : tail, ∃ w : A₀.RStage j.1,
        Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource j.1 w = r := by
    intro r
    obtain ⟨i, w, hw⟩ :=
      Ring.DirectLimit.exists_of
        (G := A₀.RStage)
        (f := fun i j h ↦ A₀.RMap i j h)
        (A₀.colimitSource.symm r)
    obtain ⟨k, hik, hi₀k⟩ := exists_ge_ge i i₀
    let j : tail := ⟨k, hi₀k⟩
    refine ⟨j, (A₀.RMap i k hik) w, ?_⟩
    have hw' :
        Ring.DirectLimit.of A₀.RStage (fun i j h ↦ A₀.RMap i j h) k ((A₀.RMap i k hik) w) =
          A₀.colimitSource.symm r := by
      rw [← hw]
      exact Ring.DirectLimit.of_f (f := fun i j h ↦ A₀.RMap i j h) hik w
    have hcolim := congrArg A₀.colimitSource hw'
    simpa [j, Ring.DirectLimit.toLimitHom] using hcolim
  have tail_raw_tensor_cover :
      ∀ z : P₀ ⊗[A₀.RStage i₀] R, ∃ j : tail, ∃ w : rawStage j, rawToAmbient j w = z := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · refine ⟨⟨i₀, le_rfl⟩, 0, ?_⟩
      simp [rawToAmbient]
    · intro p r
      rcases tail_source_cover r with ⟨j, w, hw⟩
      letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
      letI : Algebra (A₀.RStage j.1) R :=
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource j.1).toAlgebra
      letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
        Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource j.2
      refine ⟨j, (p : P₀) ⊗ₜ[A₀.RStage i₀] w, ?_⟩
      rw [show rawToAmbient j ((p : P₀) ⊗ₜ[A₀.RStage i₀] w) =
          (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
            (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage j.1) R))
            (p ⊗ₜ[A₀.RStage i₀] w) from rfl]
      rw [Algebra.TensorProduct.map_tmul]
      simpa using congrArg (fun r' : R ↦ (p : P₀) ⊗ₜ[A₀.RStage i₀] r') hw
    · intro x y hx hy
      rcases hx with ⟨i, x', hx'⟩
      rcases hy with ⟨j, y', hy'⟩
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, rawMap i k hik x' + rawMap j k hjk y', ?_⟩
      have hix :
          rawToAmbient i x' = rawToAmbient k (rawMap i k hik x') := by
        simpa [RingHom.comp_apply] using
          congrArg (fun g : rawStage i →+* (P₀ ⊗[A₀.RStage i₀] R) => g x')
            (hrawToAmbient_comp i k hik)
      have hjy :
          rawToAmbient j y' = rawToAmbient k (rawMap j k hjk y') := by
        simpa [RingHom.comp_apply] using
          congrArg (fun g : rawStage j →+* (P₀ ⊗[A₀.RStage i₀] R) => g y')
            (hrawToAmbient_comp j k hjk)
      rw [map_add]
      rw [← hix, ← hjy, hx', hy']
  have range_stage_cover :
      ∀ s : S, ∃ j : tail, ∃ x : rangeStage j, (x : S) = s := by
    intro s
    rcases tail_raw_tensor_cover (e.symm s) with ⟨j, w, hw⟩
    refine ⟨j, ⟨(σ j) w, ⟨w, rfl⟩⟩, ?_⟩
    change (σ j) w = s
    change e (rawToAmbient j w) = s
    rw [hw]
    exact e.apply_symm_apply s
  let targetStageToAmbient : (j : tail) → rangeStage j →+* S := fun j ↦
    { toFun := fun x ↦ x.1
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let targetColimitToAmbient :
      Ring.DirectLimit rangeStage (fun j k h ↦ targetMap j k h) →+* S :=
    Ring.DirectLimit.lift
      rangeStage
      (fun j k h ↦ targetMap j k h)
      S
      targetStageToAmbient
      (fun j k hjk x ↦ by
        rfl)
  have htargetColimitToAmbient_bijective :
      Function.Bijective targetColimitToAmbient := by
    -- Proof comment: each image-stage inclusion is injective, and `range_stage_cover` supplies
    -- the needed stagewise cover of `S`.
    simpa [targetColimitToAmbient] using
      (Ring.DirectLimit.lift_bijective_of_stagewise_injective_cover
        (A := rangeStage)
        (map := fun j k hjk ↦ targetMap j k hjk)
        (B := S)
        (g := targetStageToAmbient)
        (hg := fun j k hjk x ↦ by
          rfl)
        (hinj := fun _ ↦ Subtype.val_injective)
        (hcover := fun s ↦ by
          rcases range_stage_cover s with ⟨j, x, hx⟩
          exact ⟨j, x, hx⟩))
  let colimitTarget :
      Ring.DirectLimit rangeStage (fun j k h ↦ targetMap j k h) ≃+* S :=
    RingEquiv.ofBijective targetColimitToAmbient htargetColimitToAmbient_bijective
  have htail_colimitSource_of :
      ∀ (j : tail) (x : A₀.RStage j.1),
        (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          i₀ A₀.colimitSource)
          (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
            (fun j k h ↦ A₀.RMap j.1 k.1 h) j x) =
        Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource j.1 x := by
    intro j x
    change
      A₀.colimitSource
          ((tail_directLimit_to_full A₀.RStage (fun i j h ↦ A₀.RMap i j h) i₀)
            (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
              (fun j k h ↦ A₀.RMap j.1 k.1 h) j x)) =
        Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource j.1 x
    rw [tail_directLimit_to_full_of]
    rfl
  have hcolimit_comm_toAmbient :
      targetColimitToAmbient.comp
          (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
        f.comp
          (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            i₀ A₀.colimitSource).toRingHom := by
    -- Proof comment: compare both colimit maps on canonical source-stage generators only.
    apply Ring.DirectLimit.hom_ext
    intro j
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change
      targetColimitToAmbient
          ((Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h))
            (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
              (fun j k h ↦ A₀.RMap j.1 k.1 h) j x)) =
        f
          ((tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            i₀ A₀.colimitSource)
            (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
              (fun j k h ↦ A₀.RMap j.1 k.1 h) j x))
    rw [Ring.DirectLimit.map_apply_of]
    change
      Ring.DirectLimit.lift rangeStage (fun j k h ↦ targetMap j k h) S targetStageToAmbient
          (fun j k hjk x ↦ by
            rfl)
          (Ring.DirectLimit.of rangeStage (fun j k h ↦ targetMap j k h) j (stageMapTail j x)) =
        f
          ((tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            i₀ A₀.colimitSource)
            (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
              (fun j k h ↦ A₀.RMap j.1 k.1 h) j x))
    rw [Ring.DirectLimit.lift_of]
    calc
      ((stageMapTail j x : rangeStage j) : S)
          = (σ j) ((algebraMap (A₀.RStage j.1) (rawStage j)) x) := by
              exact hstageMapTail_apply j x
      _ = f
            ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              A₀.colimitSource j.1) x) := by
            simpa [RingHom.comp_apply] using
              congrArg (fun g : A₀.RStage j.1 →+* S => g x) (hσ_comp j)
      _ = (f.comp
            (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              i₀ A₀.colimitSource).toRingHom)
            (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
              (fun j k h ↦ A₀.RMap j.1 k.1 h) j x) := by
            simpa [RingHom.comp_apply] using
              congrArg f (htail_colimitSource_of j x).symm
  let A : DirectedFiniteTypeHomApproximation f :=
    { Λ := tail
      instPreorder := inferInstance
      instNonempty := inferInstance
      instDirectedOrder := inferInstance
      RStage := fun j ↦ A₀.RStage j.1
      SStage := rangeStage
      instCommRingRStage := fun _ ↦ inferInstance
      instCommRingSStage := fun _ ↦ inferInstance
      RMap := fun j k hjk ↦ A₀.RMap j.1 k.1 hjk
      SMap := targetMap
      instDirectedSystemRStage := inferInstance
      instDirectedSystemSStage := inferInstance
      stageMap := stageMapTail
      comm := fun {j k} hjk ↦ hcommTail hjk
      source_finiteType := fun j ↦ A₀.source_finiteType j.1
      target_finiteType := hstageMapTail_finiteType
      colimitSource := tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        i₀ A₀.colimitSource
      colimitTarget := colimitTarget
      colimit_comm := by
        change
          targetColimitToAmbient.comp
              (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
            f.comp
              (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h)
                i₀ A₀.colimitSource).toRingHom
        exact hcolimit_comm_toAmbient }
  refine ⟨A, ?_⟩
  intro j k hjk
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
  letI : Algebra (A₀.RStage j.1) (rangeStage j) := (stageMapTail j).toAlgebra
  have hcomp :
      (A₀.RMap j.1 k.1 hjk).comp (A₀.RMap i₀ j.1 j.2) = A₀.RMap i₀ k.1 k.2 := by
    ext x
    exact DirectedSystem.map_map (f := fun i j h ↦ A₀.RMap i j h) j.2 hjk x
  let cancel :
      (rawStage j ⊗[A₀.RStage j.1] A₀.RStage k.1) ≃+* rawStage k :=
    rawTensorCancel A₀.RStage (fun i j h ↦ A₀.RMap i j h) P₀ j.2 k.2 hjk hcomp
  let leftAlgHom : rawStage j →ₐ[A₀.RStage j.1] rangeStage j :=
    { toRingHom := (σ j).rangeRestrict
      commutes' := fun x ↦ by
        apply Subtype.ext
        rfl }
  let beta : rawStage j ⊗[A₀.RStage j.1] A₀.RStage k.1 →+* A.stageBaseChange hjk :=
    tensorMapLeft_mixed (R := A₀.RStage j.1) (A := rawStage j) (B := A₀.RStage k.1)
      (C := rangeStage j) leftAlgHom
  let gamma : rawStage j ⊗[A₀.RStage j.1] A₀.RStage k.1 →+* rangeStage k :=
    ((σ k).rangeRestrict).comp cancel.toRingHom
  let includeLeft :
      rawStage j →+* rawStage j ⊗[A₀.RStage j.1] A₀.RStage k.1 :=
    (Algebra.TensorProduct.includeLeft :
      rawStage j →ₐ[A₀.RStage j.1] rawStage j ⊗[A₀.RStage j.1] A₀.RStage k.1).toRingHom
  have hgamma_surj : Function.Surjective gamma := by
    intro y
    rcases (σ k).rangeRestrict_surjective y with ⟨x, rfl⟩
    refine ⟨cancel.symm x, ?_⟩
    simp [gamma, cancel]
  have hleft_surj : Function.Surjective leftAlgHom := by
    intro y
    rcases (σ j).rangeRestrict_surjective y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hbeta_surj : Function.Surjective beta := by
    -- Proof comment: tensoring a surjective left-factor map with the identity stays surjective.
    simpa [beta, tensorMapLeft_mixed] using
      (Algebra.TensorProduct.map_surjective
        (R := A₀.RStage j.1)
        (f := leftAlgHom)
        (g := AlgHom.id (A₀.RStage j.1) (A₀.RStage k.1))
        hleft_surj
        (fun y ↦ ⟨y, rfl⟩))
  have hbeta_ker :
      RingHom.ker beta =
        Ideal.map includeLeft (RingHom.ker leftAlgHom) := by
    -- Proof comment: right exactness computes the kernel after tensoring the surjection
    -- `rawStage j → rangeStage j` with the identity on the later source stage.
    change
      RingHom.ker
          (Algebra.TensorProduct.map leftAlgHom
            (AlgHom.id (A₀.RStage j.1) (A₀.RStage k.1))) =
        Ideal.map includeLeft (RingHom.ker leftAlgHom)
    exact
      (Algebra.TensorProduct.rTensor_ker
        (R := A₀.RStage j.1)
        (C := A₀.RStage k.1)
        (f := leftAlgHom)
        hleft_surj)
  have hstage_comp :
      (A.stageBaseChangeMap hjk).comp beta = gamma := by
    -- Route correction: compare the two maps only after embedding the target stage into `S`, then
    -- recover equality in `rangeStage k` using the injectivity of the ambient inclusion.
    exact stage_baseChangeMap_comp_beta_eq_gamma
      (A := A) hjk (σ j) (σ k) (targetStageToAmbient k) leftAlgHom cancel (rawMap j k hjk)
      gamma Subtype.val_injective
      (by
        intro x
        rfl)
      (by
        intro r'
        simpa [A, stageMapTail] using hstageMapTail_apply k r')
      (hσ_raw_comp j k hjk)
      (by
        intro x r'
        exact rawTensorCancel_tmul_right (RStage := A₀.RStage)
          (map := fun i j h ↦ A₀.RMap i j h) (P₀ := P₀)
          (i₀ := i₀) (j := j.1) (k := k.1) j.2 k.2 hjk hcomp x r')
      (by
        intro x r'
        rfl)
  have hgamma_ker :
      RingHom.ker gamma = RingHom.ker beta := by
    -- Route correction: the remaining kernel step now splits conceptually into two parts:
    -- first normalize `ker gamma` using `gamma_ker_eq_comap_cancel_ker_sigma`, then compare that
    -- comap with `ker beta` by the quotient-level tensor argument.
    have hleft_ker : RingHom.ker leftAlgHom = RingHom.ker (σ j) := by
      -- Proof comment: the image-stage map `leftAlgHom` is just the raw stage map restricted to
      -- its range, so its kernel is literally the kernel of `σ j`.
      simpa [leftAlgHom] using ker_leftAlgHom_eq_ker_sigma_tail (σj := σ j)
    have hcancel_ker :
        Ideal.comap cancel.toRingHom (RingHom.ker (σ k)) =
          Ideal.map includeLeft (RingHom.ker (σ j)) := by
      -- TODO: prove the quotient-level tensor kernel transport by commuting the tensor factors
      -- once, applying `Algebra.TensorProduct.tensorQuotientEquiv` in the right-factor
      -- orientation, and checking the induced map on pure tensors via
      -- `rawTensorCancel_algebraMap` and `rawTensorCancel_tmul_right`.
      sorry
    calc
      RingHom.ker gamma = Ideal.comap cancel.toRingHom (RingHom.ker (σ k)) := by
        exact gamma_ker_eq_comap_cancel_ker_sigma (A := A) hjk (σ k) cancel
      _ = Ideal.map includeLeft (RingHom.ker (σ j)) := hcancel_ker
      _ = RingHom.ker beta := by
        rw [hbeta_ker, hleft_ker]
  exact bijective_of_comp_eq_of_surjective_of_ker_eq
    hstage_comp hbeta_surj hgamma_surj hgamma_ker.symm
