import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.FourierBridge

noncomputable section

open scoped MonoidAlgebra
open Representation

universe u v w x

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

local instance : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 16-16.4-1: if the scalar-extended ambient action is zero, then the
original `K`-linear ambient action is already zero. This is the `f := 0` specialization of the
general base-change descent used later in the projector branch. -/
-- TODO: call the imported descent lemma with the hidden stable-lattice parameter supplied in the
-- elaboration-friendly form, avoiding the current field-notation mismatch.
lemma ambient_action_zero_of_algClosure_action_zero_local
    (u : A[G])
    (hu :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0) :
    ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) = 0 :=
  by
  have hmap :
      MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u =
        MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
          (MonoidAlgebra.mapRingHom G (algebraMap A K) u) := by
    ext g
    simp [MonoidAlgebra.mapRingHom_apply, IsScalarTower.algebraMap_eq A K (AlgebraicClosure K)]
  -- Descend the zero scalar-extension action through faithful base change.
  apply StableLattice.algClosure_baseChange_end_injective_local
  rw [hmap] at hu
  rw [Representation.scalarExtension_asAlgebraHom_mapRingHom (ρ := ρ)] at hu
  simpa using hu

/-- Helper for Proposition 16-16.4-1: if the action homomorphism `R → S` splits on the level of
left `R`-modules and `M` is projective over `S`, then restricting scalars along `R → S` keeps `M`
projective. This packages the formal source step used after the kernel of `A[G] → End_A(P)` is
split. -/
lemma projective_restrictScalars_of_projective_hom
    {R : Type*} [Semiring R]
    {S : Type*} [Semiring S] (σ : R →+* S)
    {M : Type*} [AddCommMonoid M] [Module S M]
    [Module R S] [Module R M] [IsScalarTower R S M]
    (hsmulS : ∀ (r : R) (s : S), (r • s : S) = σ r * s)
    (τ : S →ₗ[R] R)
    (hστ :
      ({ toFun := σ
         map_add' := σ.map_add
         map_smul' := by
           intro r s
           change σ (r * s) = r • σ s
           rw [hsmulS]
           simpa using σ.map_mul r s } : R →ₗ[R] S).comp τ = LinearMap.id)
    [Module.Projective S M] :
    Module.Projective R M := by
  let σlin : R →ₗ[R] S :=
    { toFun := σ
      map_add' := σ.map_add
      map_smul' := by
        intro r s
        change σ (r * s) = r • σ s
        rw [hsmulS]
        simpa using σ.map_mul r s }
  obtain ⟨P, _instAddCommMonoidP, _instModuleP, _instFreeP, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := S) (P := M)).mp inferInstance
  let _ : Module R P := Module.compHom P σ
  let _ : IsScalarTower R S P := by
    refine ⟨?_⟩
    intro r s' x
    -- Rewrite the restricted `R`-action on `S` into multiplication, then reassociate on `P`.
    calc
      (r • s' : S) • x = (σ r * s') • x := by rw [hsmulS]
      _ = (σ r) • (s' • x) := by simpa using (mul_smul (σ r) s' x)
  let ι := Module.Free.ChooseBasisIndex S P
  let b : Module.Basis ι S P := Module.Free.chooseBasis S P
  let _ : Module R (ι →₀ S) := inferInstance
  let toR : (ι →₀ S) →ₗ[R] (ι →₀ R) := Finsupp.mapRange.linearMap τ
  let toS : (ι →₀ R) →ₗ[R] (ι →₀ S) := Finsupp.mapRange.linearMap σlin
  have hsplitFinsupp : toS.comp toR = LinearMap.id := by
    apply LinearMap.ext
    intro f
    ext j
    change σlin (τ (f j)) = f j
    simpa using LinearMap.congr_fun hστ (f j)
  have hprojFinsupp : Module.Projective R (ι →₀ S) := by
    let _ : Module.Projective R (ι →₀ R) := inferInstance
    exact Module.Projective.of_split toR toS hsplitFinsupp
  let eR : P ≃ₗ[R] (ι →₀ S) :=
    { toFun := b.repr
      invFun := b.repr.symm
      left_inv := b.repr.left_inv
      right_inv := b.repr.right_inv
      map_add' := b.repr.map_add
      map_smul' := by
        intro r x
        calc
          b.repr (r • x) = b.repr ((σ r) • x) := by rfl
          _ = (σ r) • b.repr x := by simpa using b.repr.map_smul (σ r) x
          _ = r • b.repr x := by
            ext i
            simpa [Finsupp.smul_apply] using (hsmulS r (b.repr x i)).symm }
  let _ : Module.Projective R (ι →₀ S) := hprojFinsupp
  let _ : Module.Projective R P := by
    -- The free `S`-module splitting ambient is a direct sum of copies of the projective
    -- `R`-module obtained from the split ring action, so it stays projective after restriction.
    exact Module.Projective.of_equiv' eR.symm
  exact Module.Projective.of_split (i.restrictScalars R) (s.restrictScalars R) <| by
    -- The `S`-linear splitting remains a splitting after forgetting scalars.
    ext x
    exact LinearMap.congr_fun hs x

/-- Helper for Proposition 16-16.4-1: once the action map `A[G] → End_A(P)` is surjective and its
kernel is split as a two-sided ideal, LinearRepresentations_Serre_1977's part `(a)` follows formally by restricting scalars
from `End_A(P)` back to `A[G]`. -/
lemma projective_of_action_hom_surjective_and_ker_isCompl
    [Nontrivial L.toSubmodule]
    (hsurj : Function.Surjective L.toRepresentation.asAlgebraHom)
    (hcompl : ∃ I : TwoSidedIdeal A[G],
      IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I) :
    Module.Projective A[G] L.toRepresentation.asModule := by
  let S := Module.End A L.toSubmodule
  let π : A[G] →+* S := L.toRepresentation.asAlgebraHom
  letI : Module A[G] S := Module.compHom S π
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module S L.toSubmodule := by infer_instance
  letI : IsScalarTower A[G] S L.toSubmodule := by
    refine ⟨?_⟩
    intro u f x
    rfl
  let πlin : A[G] →ₗ[A[G]] S :=
    { toFun := π
      map_add' := π.map_add
      map_smul' := by
        intro u v
        change π (u * v) = π u * π v
        simpa using π.map_mul u v }
  let K : TwoSidedIdeal A[G] := TwoSidedIdeal.ker π
  obtain ⟨I, hKI⟩ := hcompl
  change IsCompl K I at hKI
  let eI :
      I ≃ₗ[A[G]] S :=
    LinearEquiv.ofBijective (πlin.comp I.subtype) <| by
      constructor
      · intro x y hxy
        apply Subtype.ext
        have hxy' : π x = π y := by
          simpa [πlin] using hxy
        have hsub :
            ((x : A[G]) - y : A[G]) ∈ K := by
          change π (((x : A[G]) - y : A[G])) = 0
          rw [map_sub, sub_eq_zero]
          exact hxy'
        have hinf :
            ((x : A[G]) - y : A[G]) ∈
              K ⊓ I := by
          exact ⟨hsub, sub_mem x.2 y.2⟩
        have hzero :
            ((x : A[G]) - y : A[G]) = 0 := by
          have : ((x : A[G]) - y : A[G]) ∈ (⊥ : TwoSidedIdeal A[G]) := by
            simpa [hKI.disjoint.eq_bot] using hinf
          simpa using this
        exact sub_eq_zero.mp hzero
      · intro φ
        let u := Function.surjInv hsurj φ
        have hu : π u = φ := Function.surjInv_eq hsurj φ
        have hu_mem :
            u ∈ K ⊔ I := by
          simpa [hKI.sup_eq_top] using (show u ∈ (⊤ : TwoSidedIdeal A[G]) from trivial)
        rcases TwoSidedIdeal.mem_sup.mp hu_mem with ⟨kerElt, hkK, i, hiI, hsum⟩
        refine ⟨⟨i, hiI⟩, ?_⟩
        change π i = φ
        calc
          π i = 0 + π i := by simp
          _ = π kerElt + π i := by rw [(TwoSidedIdeal.mem_ker _).mp hkK]
          _ = π (kerElt + i) := by
            symm
            simpa using π.map_add kerElt i
          _ = φ := by simpa [hsum] using hu
  let σ : S →ₗ[A[G]] A[G] := I.subtype ∘ₗ eI.symm.toLinearMap
  have hsplit : πlin.comp σ = LinearMap.id := by
    apply LinearMap.ext
    intro φ
    -- The complement identifies the endomorphism ring with a direct summand of `A[G]`.
    change eI (eI.symm φ) = φ
    exact eI.apply_symm_apply φ
  have hprojEnd : Module.Projective A[G] S := by
    exact (Module.Projective.iff_split_of_projective (s := πlin) hsurj).2 ⟨σ, hsplit⟩
  have hprojSubmodule : Module.Projective S L.toSubmodule := by
    -- LinearRepresentations_Serre_1977's elementary module-theoretic input is projectivity over the endomorphism ring.
    exact L.toSubmodule_projective_over_endomorphismRing
  letI : Module.Projective A[G] S := hprojEnd
  letI : Module.Projective S L.toSubmodule := hprojSubmodule
  have hprojRestrict :
      Module.Projective A[G] L.toSubmodule := by
    exact
      projective_restrictScalars_of_projective_hom (σ := π) (M := L.toSubmodule)
        (hsmulS := fun u f ↦ rfl) (τ := σ) hsplit
  simpa using hprojRestrict

/-- Helper for Proposition 16-16.4-1: once a central idempotent `e` cuts out exactly the kernel
of the lattice action map by left multiplication, the image ideal `e · A[G]` is a direct
complement to that kernel. This packages the purely ring-theoretic half of LinearRepresentations_Serre_1977's `φ = id`
projector argument so the remaining blocker stays concentrated in the packet descent. -/
lemma isCompl_ker_of_central_idempotent_annihilator
    {e : A[G]}
    (he_center : e ∈ Subalgebra.center A (A[G]))
    (he_idem : IsIdempotentElem e)
    (hker : ∀ u : A[G], L.toRepresentation.asAlgebraHom u = 0 ↔ e * u = 0) :
    ∃ I : TwoSidedIdeal A[G],
      IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
  let I : TwoSidedIdeal A[G] :=
    TwoSidedIdeal.mk'
      {u | ∃ v : A[G], e * v = u}
      (by exact ⟨0, by simp⟩)
      (by
        intro x y hx hy
        rcases hx with ⟨u, rfl⟩
        rcases hy with ⟨v, rfl⟩
        exact ⟨u + v, by rw [mul_add]⟩)
      (by
        intro x hx
        rcases hx with ⟨u, rfl⟩
        exact ⟨-u, by simp⟩)
      (by
        intro x y hy
        rcases hy with ⟨u, rfl⟩
        refine ⟨x * u, ?_⟩
        -- Commute the central projector past the new left factor before reassociating.
        calc
          e * (x * u) = (e * x) * u := by rw [mul_assoc]
          _ = (x * e) * u := by rw [(Subalgebra.mem_center_iff.mp he_center x).symm]
          _ = x * (e * u) := by rw [mul_assoc])
      (by
        intro x y hx
        rcases hx with ⟨u, rfl⟩
        exact ⟨u * y, by rw [mul_assoc]⟩)
  refine ⟨I, ?_⟩
  constructor
  · rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      rw [TwoSidedIdeal.mem_inf] at hx
      rcases hx with ⟨hxker, hxI⟩
      have hxI' : x ∈ ({u : A[G] | ∃ v : A[G], e * v = u} : Set A[G]) := by
        simpa [I] using hxI
      rcases hxI' with ⟨u, rfl⟩
      have hxzero : e * (e * u) = 0 := by
        exact (hker (e * u)).mp ((TwoSidedIdeal.mem_ker _).mp hxker)
      have hzero : e * u = 0 := by
        -- Idempotence identifies points in the image ideal with their `e`-multiple.
        calc
          e * u = (e * e) * u := by rw [he_idem.eq]
          _ = e * (e * u) := by rw [mul_assoc]
          _ = 0 := hxzero
      simpa using hzero
    · exact bot_le
  · rw [codisjoint_iff]
    apply le_antisymm
    · exact le_top
    · intro x hx
      have hker_zero : e * (x - e * x) = 0 := by
        -- Split `x` into its kernel piece and its image-ideal piece using `e^2 = e`.
        calc
          e * (x - e * x) = e * x - e * (e * x) := by rw [mul_sub]
          _ = e * x - (e * e) * x := by rw [mul_assoc]
          _ = e * x - e * x := by rw [he_idem.eq]
          _ = 0 := sub_self _
      refine TwoSidedIdeal.mem_sup.mpr ?_
      refine ⟨x - e * x, ?_, e * x, ⟨x, by simp⟩, by abel⟩
      exact (TwoSidedIdeal.mem_ker _).mpr ((hker (x - e * x)).mpr hker_zero)

/-- Helper for Proposition 16-16.4-1: the class-function description of LinearRepresentations_Serre_1977's special Fourier
element after scalar extension already forces the integral element itself to lie in the center of
`A[G]`. This is the portion of the source projector packet that descends in the current
universe-generic setting without invoking the equal-universe `FDRep` bridge. -/
lemma serre_fourier_id_coeff_isClassFunction
    (hdefect : ρ.HasDefectZero p) :
    letI : Fintype G := Fintype.ofFinite G
    _root_.IsClassFunction fun s : G ↦ L.serre_fourier_element hdefect LinearMap.id s := by
  letI : Fintype G := Fintype.ofFinite G
  refine ⟨?_⟩
  intro a b hab
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, rfl⟩
  have hginv_mul :
      L.toRepresentation g⁻¹ * L.toRepresentation g = LinearMap.id := by
    ext x
    simp
  have htrace_one :
      LinearMap.trace A L.toSubmodule (L.toRepresentation a⁻¹) =
        LinearMap.trace A L.toSubmodule
          (L.toRepresentation a⁻¹ * (L.toRepresentation g⁻¹ * L.toRepresentation g)) := by
    have hmul :
        L.toRepresentation a⁻¹ * (L.toRepresentation g⁻¹ * L.toRepresentation g) =
          L.toRepresentation a⁻¹ := by
      ext x
      simp [hginv_mul]
    exact congrArg (LinearMap.trace A L.toSubmodule) hmul.symm
  -- Route correction: prove centrality directly from the integral coefficient formula, rather
  -- than first transporting to the field-side primitive-idempotent API.
  calc
    L.serre_fourier_element hdefect LinearMap.id a =
        L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule (L.toRepresentation a⁻¹) := by
      simp [StableLattice.serre_fourier_element_apply]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            (L.toRepresentation a⁻¹ * (L.toRepresentation g⁻¹ * L.toRepresentation g)) := by
      rw [htrace_one]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation a⁻¹ * L.toRepresentation g⁻¹) * L.toRepresentation g) := by
      simp [mul_assoc]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation g) *
              (L.toRepresentation a⁻¹ * L.toRepresentation g⁻¹)) := by
      rw [← LinearMap.trace_mul_comm]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule (L.toRepresentation ((g * a * g⁻¹)⁻¹)) := by
      simp [mul_assoc]
    _ = L.serre_fourier_element hdefect LinearMap.id (g * a * g⁻¹) := by
      simp [StableLattice.serre_fourier_element_apply]

/-- Helper for Proposition 16-16.4-1: LinearRepresentations_Serre_1977's special Fourier element for `LinearMap.id` already
has class-function coefficients over `A`, so it is central before any passage to the fraction
field. -/
lemma serre_fourier_id_mem_center
    (hdefect : ρ.HasDefectZero p) :
    let e := L.serre_fourier_element hdefect LinearMap.id
    e ∈ Subalgebra.center A (A[G]) := by
  letI : Fintype G := Fintype.ofFinite G
  let e := L.serre_fourier_element hdefect LinearMap.id
  let f : classFunctionSubmodule A G :=
    ⟨fun s ↦ e s, (mem_classFunctionSubmodule_iff A _).2 <|
      StableLattice.serre_fourier_id_coeff_isClassFunction (L := L) (p := p) hdefect⟩
  have heq : e = Finsupp.equivFunOnFinite.symm (f : G → A) := by
    ext s
    rfl
  -- Route correction: use the integral class-function packet directly, so centrality no longer
  -- depends on the field-side `[Invertible (Nat.card G : K)]` projector API.
  change e ∈ Subalgebra.center A (A[G])
  rw [heq]
  exact mem_center_of_classFunction A f


/-- Helper for Proposition 16-16.4-1: LinearRepresentations_Serre_1977's integral Fourier section is additive in the lifted
endomorphism. This is the coefficientwise linearity of the trace formula. -/
lemma serre_fourier_add_local
    (hdefect : ρ.HasDefectZero p)
    (φ ψ : Module.End A L.toSubmodule) :
    L.serre_fourier_element hdefect (φ + ψ) =
      L.serre_fourier_element hdefect φ + L.serre_fourier_element hdefect ψ := by
  ext s
  -- Compare the explicit coefficients and use additivity of composition and trace.
  calc
    L.serre_fourier_element hdefect (φ + ψ) s =
        L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation s⁻¹).comp (φ + ψ)) := by
          simp [StableLattice.serre_fourier_element_apply]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation s⁻¹).comp φ + (L.toRepresentation s⁻¹).comp ψ) := by
          rw [LinearMap.comp_add]
    _ = L.defect_zero_dim_ratio hdefect *
          (LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp φ) +
            LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp ψ)) := by
          rw [(LinearMap.trace A L.toSubmodule).map_add]
    _ = (L.serre_fourier_element hdefect φ + L.serre_fourier_element hdefect ψ) s := by
          simp [StableLattice.serre_fourier_element_apply, mul_add]

/-- Helper for Proposition 16-16.4-1: LinearRepresentations_Serre_1977's integral Fourier section is `A`-linear in the lifted
endomorphism. This keeps scalar coefficients outside the section while we compute basis monomials
in the group algebra. -/
lemma serre_fourier_smul_local
    (hdefect : ρ.HasDefectZero p)
    (a : A) (φ : Module.End A L.toSubmodule) :
    L.serre_fourier_element hdefect (a • φ) =
      a • L.serre_fourier_element hdefect φ := by
  ext s
  -- Compare the explicit coefficients and move the scalar through composition and trace.
  calc
    L.serre_fourier_element hdefect (a • φ) s =
        L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            ((L.toRepresentation s⁻¹).comp (a • φ)) := by
          simp [StableLattice.serre_fourier_element_apply]
    _ = L.defect_zero_dim_ratio hdefect *
          LinearMap.trace A L.toSubmodule
            (a • ((L.toRepresentation s⁻¹).comp φ)) := by
          rw [LinearMap.comp_smul]
    _ = L.defect_zero_dim_ratio hdefect *
          (a * LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp φ)) := by
          rw [(LinearMap.trace A L.toSubmodule).map_smul]
          simp [smul_eq_mul]
    _ = (a • L.serre_fourier_element hdefect φ) s := by
          simp [StableLattice.serre_fourier_element_apply, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm]

/-- Helper for Proposition 16-16.4-1: LinearRepresentations_Serre_1977's integral Fourier section sends the zero endomorphism
to the zero group-algebra element. -/
lemma serre_fourier_zero_local
    (hdefect : ρ.HasDefectZero p) :
    L.serre_fourier_element hdefect (0 : Module.End A L.toSubmodule) = 0 :=
  by
  ext s
  -- Evaluate the explicit coefficient formula at `s` and simplify the trace of the zero map.
  change L.serre_fourier_element hdefect (0 : Module.End A L.toSubmodule) s = 0
  simp [StableLattice.serre_fourier_element_apply]


end DefectZero

end StableLattice

end section
