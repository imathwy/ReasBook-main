import Serre.Chap16.Proposition_16_16_4_1.FourierBridge

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

/-- Helper for Proposition 16-16.4-1: scalar extension of lattice endomorphisms along the
base-change inclusion `P ↪ E` is injective. This is the descent step from an ambient `K`-linear
identity back to the original `A`-linear endomorphism of the lattice. -/
lemma toSubmodule_endHom_injective :
    Function.Injective
      ((L.toSubmodule_subtype_isBaseChange).endHom :
        Module.End A L.toSubmodule → Module.End K E) := by
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  intro φ ψ hφψ
  ext x
  -- Evaluate the ambient equality on the image of the lattice and then drop back to the subtype.
  have hx := congrArg
    (fun f : Module.End K E ↦ f (((x : L.toSubmodule) : E))) hφψ
  calc
    ↑(φ x) = hf.endHom φ (((x : L.toSubmodule) : E)) := by
      symm
      simpa using hf.endHom_comp_apply φ x
    _ = hf.endHom ψ (((x : L.toSubmodule) : E)) := hx
    _ = ↑(ψ x) := by
      simpa using hf.endHom_comp_apply ψ x

/-- Helper for Proposition 16-16.4-1: once the mapped Fourier element acts on the ambient
representation as the scalar-extended endomorphism `φ`, injectivity of base change descends that
identity to the original lattice action. -/
lemma serre_fourier_action_eq_endHom_of_ambient
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (hambient :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ) :
    L.toRepresentation.asAlgebraHom (L.serre_fourier_element hdefect φ) = φ := by
  -- Compare both lattice endomorphisms after scalar extension to `E`, where the ambient action is
  -- already known to compute coefficientwise.
  apply L.toSubmodule_endHom_injective
  rw [← L.ambient_action_map_eq_endHom (u := L.serre_fourier_element hdefect φ)]
  exact hambient

/-- Helper for Proposition 16-16.4-1: the fraction field of the valuation ring has either
characteristic zero or the same prime characteristic `p` as the residue field. This isolates the
remaining Fourier step into its mixed-characteristic and equal-characteristic branches. -/
lemma charZero_or_charP_fraction_field (_L : StableLattice A ρ)
    [hres : CharP (IsLocalRing.ResidueField A) p] :
    CharZero K ∨ CharP K p := by
  by_cases hchar0 : ringChar K = 0
  · -- If the fraction field has characteristic zero, record that branch explicitly.
    left
    exact (CharP.ringChar_zero_iff_CharZero (R := K)).mp hchar0
  · let q := ringChar K
    have hqprime : Nat.Prime q := by
      rcases CharP.char_is_prime_or_zero K q with hqprime | hqzero
      · exact hqprime
      · exact (hchar0 hqzero).elim
    letI : Fact q.Prime := ⟨hqprime⟩
    letI : CharP K q := ringChar.charP (R := K)
    letI : CharP A q :=
      RingHom.charP (algebraMap A K) (IsFractionRing.injective A K) q
    have hq0 : (q : IsLocalRing.ResidueField A) = 0 := by
      -- Push the characteristic-`q` vanishing from `A` to the residue field quotient.
      change
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q : A) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) 0
      exact congrArg (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
        (CharP.cast_eq_zero (R := A) q)
    letI : CharP (IsLocalRing.ResidueField A) q :=
      ringChar.of_eq
        (CharP.ringChar_of_prime_eq_zero
          (R := IsLocalRing.ResidueField A) hqprime hq0)
    have hpchar : ringChar (IsLocalRing.ResidueField A) = p :=
      @ringChar.eq _ _ p hres
    have hqchar : ringChar (IsLocalRing.ResidueField A) = q :=
      ringChar.eq (R := IsLocalRing.ResidueField A) q
    have hqp : q = p := by
      -- The residue field cannot carry two distinct prime characteristics.
      calc
        q = ringChar (IsLocalRing.ResidueField A) := hqchar.symm
        _ = p := hpchar
    right
    exact hqp ▸ (inferInstance : CharP K q)

omit L ρ in
/-- Helper for Proposition 16-16.4-1: in characteristic zero the group order is nonzero in the
fraction field, so the Chapter `6` Fourier inversion hypotheses provide an inverse to `|G|`. -/
abbrev natCard_invertible_of_charZero_local [CharZero K] :
    Invertible (Nat.card G : K) :=
  by
  -- The characteristic-zero branch can therefore reuse the semisimple Fourier API without any
  -- further denominator bookkeeping.
  exact invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

omit L ρ in
/-- Helper for Proposition 16-16.4-1: after passing to `AlgebraicClosure K`, the same
characteristic-zero argument still makes `|G|` invertible. This is the field-side hypothesis used
by the one-slot inverse-Wedderburn formula. -/
abbrev natCard_invertible_algClosure_of_charZero_local [CharZero K] :
    Invertible (Nat.card G : AlgebraicClosure K) :=
  by
  -- The algebraic closure of a characteristic-zero field is again characteristic zero, so the
  -- nonvanishing of `|G|` persists after scalar extension.
  exact invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

omit L in
/-- Helper for Proposition 16-16.4-1: scalar extension carries the group-algebra action of the
ambient representation to the coefficientwise image in the scalar-extended representation. -/
lemma scalarExtension_asAlgebraHom_mapRingHom_local
    {F : Type*} [Field F] [Algebra K F]
    (u : K[G]) :
    (@Representation.scalarExtension F _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap K F) u) =
      LinearMap.baseChange F (ρ.asAlgebraHom u) := by
  -- Compare the scalar-extended action with base change on group-algebra generators and then
  -- extend linearly across `K[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun v : K[G] =>
      (@Representation.scalarExtension F _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap K F) v) =
        LinearMap.baseChange F (ρ.asAlgebraHom v)) u
    ?_ ?_ ?_
  · intro g
    -- On a group element, scalar extension is definitionally the base-changed action.
    simp [MonoidAlgebra.of, Representation.scalarExtension]
    rfl
  · intro a b ha hb
    -- Both sides are additive in the group-algebra variable.
    simp [ha, hb]
  · intro r a ha
    -- Coefficient scalars commute with both `mapRingHom` and `LinearMap.baseChange`.
    have hmap :
        MonoidAlgebra.mapRingHom G (algebraMap K F) (r • a) =
          (algebraMap K F r) • MonoidAlgebra.mapRingHom G (algebraMap K F) a := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply, Algebra.smul_def]
    rw [hmap, AlgHom.map_smul_of_tower, ha]
    calc
      (algebraMap K F r) • LinearMap.baseChange F (ρ.asAlgebraHom a) =
          LinearMap.baseChange F (r • ρ.asAlgebraHom a) := by
            simpa using (LinearMap.baseChange_smul (S := F) (f := ρ.asAlgebraHom a) r).symm
      _ = LinearMap.baseChange F (ρ.asAlgebraHom (r • a)) := by
            simp

/-- Helper for Proposition 16-16.4-1: if an element of `A[G]` acts trivially on the stable
lattice, then its coefficientwise image in `(AlgebraicClosure K)[G]` acts trivially on the scalar
extension of the ambient representation. -/
lemma algClosure_ambient_action_zero_of_action_zero_local
    (u : A[G]) (hu : L.toRepresentation.asAlgebraHom u = 0) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0 := by
  have hmap :
      MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u =
        MonoidAlgebra.mapRingHom G (algebraMap K (AlgebraicClosure K))
          (MonoidAlgebra.mapRingHom G (algebraMap A K) u) := by
    ext g
    simp [MonoidAlgebra.mapRingHom_apply, IsScalarTower.algebraMap_eq A K (AlgebraicClosure K)]
  -- Rewrite the coefficient map as the two-step scalar extension `A → K → AlgebraicClosure K`,
  -- then push the zero lattice action through the ambient action/base-change bridge.
  rw [hmap, scalarExtension_asAlgebraHom_mapRingHom_local (ρ := ρ)]
  rw [L.ambient_action_map_eq_endHom (u := u), hu]
  simp

/-- Helper for Proposition 16-16.4-1: if the scalar-extended ambient action is zero, then the
original `K`-linear ambient action is already zero. This is the `f := 0` specialization of the
general base-change descent used later in the projector branch. -/
lemma ambient_action_zero_of_algClosure_action_zero_local
    (u : A[G])
    (hu :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0) :
    ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) = 0 := by
  -- Route correction: descend the zero scalar-extension action first, rather than rebuilding
  -- this transport inside every later packet or projector calculation.
  exact
    L.ambient_action_eq_of_algClosure_baseChange_eq_local
      (ρ := ρ) (u := u) (f := 0) (by simpa using hu)

/-- Helper for Proposition 16-16.4-1: the coefficient map from the valuation ring `A` to
`AlgebraicClosure K` is injective. This is the coefficientwise descent step from the algebraic
closure back to the integral group algebra `A[G]`. -/
lemma algebraMap_injective_to_algClosure_local :
    Function.Injective (algebraMap A (AlgebraicClosure K)) := by
  intro a b hab
  -- Factor the map `A → AlgebraicClosure K` through the fraction field `K`, where both stages are
  -- already known to be injective.
  change algebraMap K (AlgebraicClosure K) (algebraMap A K a) =
      algebraMap K (AlgebraicClosure K) (algebraMap A K b) at hab
  exact (IsFractionRing.injective A K)
    ((FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) hab)

/-- Helper for Proposition 16-16.4-1: mapping coefficients from `A[G]` to
`(AlgebraicClosure K)[G]` is injective. Once the algebraic-closure packet argument produces a
vanishing statement upstairs, this lets the proof descend back to `A[G]`. -/
lemma groupAlgebra_mapRingHom_injective_to_algClosure_local :
    Function.Injective
      (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))) := by
  intro a b hab
  ext g
  -- Read the equality of group-algebra elements coefficientwise and descend each coefficient.
  apply
    (StableLattice.algebraMap_injective_to_algClosure_local
      (A := A) (K := K))
  have hg := congrArg (fun z : (AlgebraicClosure K)[G] ↦ z g) hab
  simpa [MonoidAlgebra.mapRingHom_apply] using hg

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
kernel is split as a two-sided ideal, Serre's part `(a)` follows formally by restricting scalars
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
    -- Serre's elementary module-theoretic input is projectivity over the endomorphism ring.
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
complement to that kernel. This packages the purely ring-theoretic half of Serre's `φ = id`
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

/-- Helper for Proposition 16-16.4-1: the class-function description of Serre's special Fourier
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

/-- Helper for Proposition 16-16.4-1: Serre's special Fourier element for `LinearMap.id` already
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

/-- Helper for Proposition 16-16.4-1: base change carries the lattice action of a group element to
the ambient `K`-linear action. -/
lemma endHom_toRepresentation_eq_ambient_action
    (s : G) :
    (L.toSubmodule_subtype_isBaseChange).endHom (L.toRepresentation s) = ρ s := by
  -- Read the group element through the established action/base-change compatibility.
  simpa [Representation.asAlgebraHom_of] using
    (L.ambient_action_map_eq_endHom (u := MonoidAlgebra.of A G s)).symm

/-- Helper for Proposition 16-16.4-1: after mapping coefficients to the fraction field, Serre's
explicit integral Fourier coefficient at `s` already matches the ambient trace expression that the
source proof will compare to the inverse-Wedderburn packet. -/
lemma algebraMap_serre_fourier_element_apply_eq_ambient_trace
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) (s : G) :
    algebraMap A K (L.serre_fourier_element hdefect φ s) =
      ((Module.finrank K ρ.asModule : K) / Nat.card G) *
        LinearMap.trace K E
          (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  have hbaseChange :
      hf.endHom ((L.toRepresentation s⁻¹).comp φ) = ρ s⁻¹ * hf.endHom φ := by
    -- Avoid relying on a multiplicative base-change API: compare both ambient endomorphisms on the
    -- image of the lattice directly.
    apply hf.algHom_ext
    intro x
    calc
      hf.endHom ((L.toRepresentation s⁻¹).comp φ) (((x : L.toSubmodule) : E)) =
          (((L.toRepresentation s⁻¹).comp φ) x : L.toSubmodule) := by
            simpa using hf.endHom_comp_apply ((L.toRepresentation s⁻¹).comp φ) x
      _ = ρ s⁻¹ (((φ x : L.toSubmodule) : E)) := by
            have hact := congrArg
              (fun T : Module.End K E ↦ T (((φ x : L.toSubmodule) : E)))
              (L.endHom_toRepresentation_eq_ambient_action (s := s⁻¹))
            simpa using hact
      _ = ρ s⁻¹ (hf.endHom φ (((x : L.toSubmodule) : E))) := by
            congr 1
            symm
            simpa using hf.endHom_comp_apply φ x
      _ = (ρ s⁻¹ * hf.endHom φ) (((x : L.toSubmodule) : E)) := by
            rfl
  -- This is the verified left-hand coefficient formula needed for the missing one-slot packet
  -- comparison.
  calc
    algebraMap A K (L.serre_fourier_element hdefect φ s) =
        algebraMap A K
          (L.defect_zero_dim_ratio hdefect *
            LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp φ)) := by
              simp [StableLattice.serre_fourier_element_apply]
    _ = ((Module.finrank K ρ.asModule : K) / Nat.card G) *
          LinearMap.trace K E (ρ s⁻¹ * hf.endHom φ) := by
          rw [map_mul, L.algebraMap_defect_zero_dim_ratio (p := p) hdefect,
            L.algebraMap_trace_eq_trace_endHom ((L.toRepresentation s⁻¹).comp φ), hbaseChange]

/-- Helper for Proposition 16-16.4-1: after mapping coefficients all the way to
`AlgebraicClosure K`, Serre's Fourier coefficient formula is still the same ambient trace formula,
now with the endomorphism base-changed to the algebraic closure. This is the exact coefficient
comparison needed for the characteristic-zero one-slot packet route. -/
lemma algebraMap_serre_fourier_element_apply_eq_algClosure_ambient_trace
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) (s : G) :
    algebraMap A (AlgebraicClosure K) (L.serre_fourier_element hdefect φ s) =
      ((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) *
        LinearMap.trace (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E)
          (LinearMap.baseChange (AlgebraicClosure K)
            (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ)) := by
  -- First map the already verified `K`-coefficient formula to the algebraic closure.
  calc
    algebraMap A (AlgebraicClosure K) (L.serre_fourier_element hdefect φ s) =
        algebraMap K (AlgebraicClosure K)
          (((Module.finrank K ρ.asModule : K) / Nat.card G) *
            LinearMap.trace K E
              (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ)) := by
          simpa [IsScalarTower.algebraMap_eq A K (AlgebraicClosure K)] using
            congrArg (algebraMap K (AlgebraicClosure K))
              (L.algebraMap_serre_fourier_element_apply_eq_ambient_trace
                (p := p) hdefect φ s)
    _ = ((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) *
          LinearMap.trace (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E)
            (LinearMap.baseChange (AlgebraicClosure K)
              (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ)) := by
          rw [map_mul]
          congr 1
          · simp [div_eq_mul_inv]
          · simpa using
              (LinearMap.trace_baseChange
                (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ)
                (AlgebraicClosure K))

/-- Helper for Proposition 16-16.4-1: over `K`, the ambient-trace coefficient formula already
characterizes Serre's Fourier element. This packages the source-faithful coefficient comparison
before any later complete-family owner reads off the distinguished simple factor. -/
lemma eq_mapped_serre_fourier_of_ambient_coefficients_local
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (u : K[G])
    (hcoeff :
      ∀ s : G,
        u s =
          ((Module.finrank K ρ.asModule : K) / Nat.card G) *
            LinearMap.trace K E
              (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ)) :
    u =
      MonoidAlgebra.mapRingHom G (algebraMap A K)
        (L.serre_fourier_element hdefect φ) := by
  ext s
  -- Replace the mapped Serre coefficient by the already verified ambient trace formula over `K`.
  rw [MonoidAlgebra.mapRingHom_apply,
    L.algebraMap_serre_fourier_element_apply_eq_ambient_trace
      (p := p) hdefect φ s]
  exact hcoeff s

/-- Helper for Proposition 16-16.4-1: once a candidate element of `(AlgebraicClosure K)[G]` has
the same ambient trace coefficients as Serre's mapped Fourier element, coefficientwise
extensionality identifies the two group-algebra elements. This isolates the last step after the
inverse-Wedderburn coefficient computation. -/
lemma eq_mapped_serre_fourier_of_algClosure_ambient_coefficients
    [Invertible (Nat.card G : K)]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (u : (AlgebraicClosure K)[G])
    (hcoeff :
      ∀ s : G,
        u s =
          ((Module.finrank K ρ.asModule : AlgebraicClosure K) / Nat.card G) *
            LinearMap.trace (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E)
              (LinearMap.baseChange (AlgebraicClosure K)
                (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ))) :
    u =
      MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
        (L.serre_fourier_element hdefect φ) := by
  ext s
  -- Replace the mapped Serre coefficient by the already verified ambient trace formula.
  rw [MonoidAlgebra.mapRingHom_apply,
    L.algebraMap_serre_fourier_element_apply_eq_algClosure_ambient_trace
      (p := p) hdefect φ s]
  exact hcoeff s

/-- Helper for Proposition 16-16.4-1: restricting the group-algebra action to a subrepresentation
is just the ambient action on the underlying vector. This isolates the repeated transport from the
scalar-extended ambient representation to one irreducible constituent. -/
lemma subrepresentation_asAlgebraHom_apply_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    (ρ' : Representation L' G' V') (σ : Subrepresentation ρ')
    (u : L'[G']) (x : σ) :
    (((σ.toRepresentation).asAlgebraHom u) x : V') = ρ'.asAlgebraHom u (x : V') := by
  -- Compare the intrinsic subrepresentation action with the ambient owner action termwise on the
  -- group-algebra basis.
  induction u using MonoidAlgebra.induction_linear with
  | zero =>
      rfl
  | add a b ha hb =>
      simpa [map_add, LinearMap.add_apply] using congrArg₂ HAdd.hAdd ha hb
  | single g a =>
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Proposition 16-16.4-1: if a mapped group-algebra element acts trivially on the
ambient representation, then it also acts trivially on every subrepresentation. This is the
packetwise zero-action bridge used before transporting to complete-family coordinates. -/
lemma subrepresentation_action_zero_of_ambient_zero_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    (ρ' : Representation L' G' V') (σ : Subrepresentation ρ')
    (u : L'[G']) (hu : ρ'.asAlgebraHom u = 0) :
    σ.toRepresentation.asAlgebraHom u = 0 := by
  ext x
  -- Evaluate the ambient vanishing on the underlying vector and then restrict back to the
  -- subrepresentation carrier.
  have hx := congrArg (fun T : Module.End L' V' ↦ T (x : V')) hu
  simpa [subrepresentation_asAlgebraHom_apply_local ρ' σ u x] using hx

/-- Helper for Proposition 16-16.4-1: if a mapped group-algebra element acts as the identity on
the ambient representation, then it acts as the identity on every subrepresentation. This is the
support-side projector bridge used before transporting to complete-family coordinates. -/
lemma subrepresentation_action_id_of_ambient_id_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    (ρ' : Representation L' G' V') (σ : Subrepresentation ρ')
    (u : L'[G']) (hu : ρ'.asAlgebraHom u = LinearMap.id) :
    σ.toRepresentation.asAlgebraHom u = LinearMap.id := by
  ext x
  -- The ambient identity descends coordinatewise to the carrier of the subrepresentation.
  have hx := congrArg (fun T : Module.End L' V' ↦ T (x : V')) hu
  simpa [subrepresentation_asAlgebraHom_apply_local ρ' σ u x] using hx

/-- Helper for Proposition 16-16.4-1: after transporting a constituent to an equivalent
representation, zero ambient action stays zero. This packages the final `Equiv`-conjugation step
needed for packet coordinates. -/
lemma equiv_subrepresentation_action_zero_of_ambient_zero_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    {W' : Type*} [AddCommGroup W'] [Module L' W']
    (ρ' : Representation L' G' V') (σ : Subrepresentation ρ')
    (τ : Representation L' G' W') (e : σ.toRepresentation.Equiv τ)
    (u : L'[G']) (hu : ρ'.asAlgebraHom u = 0) :
    τ.asAlgebraHom u = 0 := by
  -- First restrict the ambient zero action to the chosen constituent, then transport it across
  -- the representation equivalence.
  calc
    τ.asAlgebraHom u = e.toLinearEquiv.conj (σ.toRepresentation.asAlgebraHom u) := by
      symm
      exact Representation.equiv_conj_asAlgebraHom _ _ e u
    _ = 0 := by
      rw [subrepresentation_action_zero_of_ambient_zero_local ρ' σ u hu]
      simp

/-- Helper for Proposition 16-16.4-1: after transporting a constituent to an equivalent
representation, identity ambient action stays the identity. This packages the final support-side
`Equiv`-conjugation step needed for the projector coordinates. -/
lemma equiv_subrepresentation_action_id_of_ambient_id_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    {W' : Type*} [AddCommGroup W'] [Module L' W']
    (ρ' : Representation L' G' V') (σ : Subrepresentation ρ')
    (τ : Representation L' G' W') (e : σ.toRepresentation.Equiv τ)
    (u : L'[G']) (hu : ρ'.asAlgebraHom u = LinearMap.id) :
    τ.asAlgebraHom u = LinearMap.id := by
  -- First restrict the ambient identity to the constituent, then conjugate it across the chosen
  -- equivalence.
  calc
    τ.asAlgebraHom u = e.toLinearEquiv.conj (σ.toRepresentation.asAlgebraHom u) := by
      symm
      exact Representation.equiv_conj_asAlgebraHom _ _ e u
    _ = LinearMap.id := by
      rw [subrepresentation_action_id_of_ambient_id_local ρ' σ u hu]
      simp

/-- Helper for Proposition 16-16.4-1: if an ambient action vanishes, then after transporting each
member of a family of subrepresentations to a chosen equivalent target family, every coordinate
action still vanishes. This packages the repeated packetwise zero-action step used before applying
the injective product projector argument. -/
lemma family_equiv_action_zero_of_ambient_zero_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    {ι : Type*}
    {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module L' (W i)]
    (ρ' : Representation L' G' V')
    (σ : ι → Subrepresentation ρ')
    (τ : ∀ i, Representation L' G' (W i))
    (e : ∀ i, (σ i).toRepresentation.Equiv (τ i))
    (u : L'[G']) (hu : ρ'.asAlgebraHom u = 0) :
    ∀ i, (τ i).asAlgebraHom u = 0 := by
  intro i
  -- Restrict the ambient zero action to the chosen constituent and transport it to the target
  -- family coordinate.
  exact equiv_subrepresentation_action_zero_of_ambient_zero_local ρ' (σ i) (τ i) (e i) u hu

/-- Helper for Proposition 16-16.4-1: if an ambient action is the identity, then after
transporting each member of a family of subrepresentations to a chosen equivalent target family,
every coordinate action is still the identity. This packages the repeated packet-projector step
used to identify the `φ = id` Serre element with the support projector. -/
lemma family_equiv_action_id_of_ambient_id_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    {ι : Type*}
    {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module L' (W i)]
    (ρ' : Representation L' G' V')
    (σ : ι → Subrepresentation ρ')
    (τ : ∀ i, Representation L' G' (W i))
    (e : ∀ i, (σ i).toRepresentation.Equiv (τ i))
    (u : L'[G']) (hu : ρ'.asAlgebraHom u = LinearMap.id) :
    ∀ i, (τ i).asAlgebraHom u = LinearMap.id := by
  intro i
  -- Restrict the ambient identity action to the chosen constituent and transport it to the
  -- target family coordinate.
  exact equiv_subrepresentation_action_id_of_ambient_id_local ρ' (σ i) (τ i) (e i) u hu

/-- Helper for Proposition 16-16.4-1: the scalar extension of the ambient endomorphism induced by
`LinearMap.id` on the stable lattice is the identity on the scalar-extended ambient
representation. This is the normalization needed when the remaining packet argument specializes
Serre's `u_φ` to the projector case `φ = LinearMap.id`. -/
lemma algClosure_baseChange_endHom_id_local :
    LinearMap.baseChange (AlgebraicClosure K)
      ((L.toSubmodule_subtype_isBaseChange).endHom
        (LinearMap.id : Module.End A L.toSubmodule)) = LinearMap.id := by
  have hend :
      (L.toSubmodule_subtype_isBaseChange).endHom
          (LinearMap.id : Module.End A L.toSubmodule) =
        (LinearMap.id : Module.End K E) := by
    -- Identify the lattice identity with the group action of `1`, then reuse the ambient
    -- base-change compatibility for group elements.
    calc
      (L.toSubmodule_subtype_isBaseChange).endHom
          (LinearMap.id : Module.End A L.toSubmodule) =
        (L.toSubmodule_subtype_isBaseChange).endHom (L.toRepresentation 1) := by
          congr 1
          ext x
          simp
      _ = ρ 1 := L.endHom_toRepresentation_eq_ambient_action (s := (1 : G))
      _ = LinearMap.id := by
          ext x
          simp
  -- Base change preserves the identity endomorphism, so the scalar-extended action is also `id`.
  simpa [hend] using
    (LinearMap.baseChange_id (A := AlgebraicClosure K) (M := E))

/-- Helper for Proposition 16-16.4-1: if a mapped group-algebra element acts trivially on
`Representation.scalarExtension ρ`, then every transported constituent in any chosen family also
sees zero action. This packages the scalar-extension specialization of the generic family bridge
used in the remaining packet projector proof. -/
lemma algClosure_family_equiv_action_zero_of_mapped_ambient_zero_local
    {ι : Type*}
    {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module (AlgebraicClosure K) (W i)]
    (σ : ι →
      Subrepresentation
        (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ))
    (τ : ∀ i, Representation (AlgebraicClosure K) G (W i))
    (e : ∀ i, (σ i).toRepresentation.Equiv (τ i))
    (u : A[G])
    (hu :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0) :
    ∀ i,
      (τ i).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0 := by
  -- Specialize the already proved family transport lemma to the scalar-extended ambient
  -- representation and the coefficientwise mapped group-algebra element.
  exact
    family_equiv_action_zero_of_ambient_zero_local
      (ρ' := @Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ)
      σ τ e
      (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) hu

/-- Helper for Proposition 16-16.4-1: if a mapped group-algebra element acts as the identity on
`Representation.scalarExtension ρ`, then every transported constituent in any chosen family also
sees the identity action. This packages the scalar-extension specialization of the generic family
projector bridge used to recognize the `φ = LinearMap.id` Serre element. -/
lemma algClosure_family_equiv_action_id_of_mapped_ambient_id_local
    {ι : Type*}
    {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module (AlgebraicClosure K) (W i)]
    (σ : ι →
      Subrepresentation
        (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ))
    (τ : ∀ i, Representation (AlgebraicClosure K) G (W i))
    (e : ∀ i, (σ i).toRepresentation.Equiv (τ i))
    (u : A[G])
    (hu :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = LinearMap.id) :
    ∀ i,
      (τ i).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = LinearMap.id := by
  -- Specialize the already proved family transport lemma to the scalar-extended ambient
  -- representation and the coefficientwise mapped group-algebra element.
  exact
    family_equiv_action_id_of_ambient_id_local
      (ρ' := @Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ)
      σ τ e
      (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) hu

/-- Helper for Proposition 16-16.4-1: for a complete irreducible family over an algebraically
closed field, the inverse Wedderburn preimage attached to a family of endomorphisms acts on each
coordinate by the prescribed endomorphism. This isolates the final `apply_symm_apply` read-off
used after the coefficient comparison identifies Serre's mapped Fourier element with that
preimage. -/
lemma irreducibleFamilyEndAlgEquiv_symm_coordinate_action_local
    {F : Type*} [Field F] [Algebra A F] [IsScalarTower A K F]
    [IsAlgClosed F] [Invertible (Nat.card G : F)]
    {ι : Type*} [Fintype ι]
    (π : ι → Rep F G)
    [∀ i, FiniteDimensional F (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (f : ∀ i, Module.End F (π i)) (i : ι) :
    (π i).ρ.asAlgebraHom
        ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm f) =
      f i := by
  -- Evaluate the product identity `ρ̃[π] (e.symm f) = f` in the `i`-th coordinate.
  exact congrFun
    ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).apply_symm_apply f) i

/-- Helper for Proposition 16-16.4-1: in characteristic zero, the Chapter `12` packet
decomposition of `Representation.scalarExtension ρ` can be reindexed through a complete
irreducible family over `AlgebraicClosure K`, so each packet support `S i` is exactly the fiber of
one chosen complete-family constituent, and the chosen index map `c` is injective. This is the
theorem-local adapter from the packet owner used in Chapter `12` to the inverse-Wedderburn owner
used in Chapter `6`. -/
lemma charZero_packet_support_complete_family_local
    [CharZero K] :
    ∃ (ι : Type) (_ : Fintype ι)
      (ψ : ι → Rep.{max w v} (AlgebraicClosure K) G)
      (d : ι → ℕ)
      (_ : ∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i))
      (a : ℕ)
      (σ : Fin a →
        Subrepresentation
          (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ))
      (S : ι → Finset (Fin a))
      (κ : Type) (_ : Fintype κ)
      (π : κ → Rep.{max w v} (AlgebraicClosure K) G)
      (_ : ∀ q, FiniteDimensional (AlgebraicClosure K) (π q))
      (hπ_pairwise : PairwiseNonisomorphic π)
      (hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ))
      (c : ι → κ)
      (e : ∀ i, (ψ i).ρ.Equiv (π (c i)).ρ),
      DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) ∧
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).character =
        ∑ j, ((σ j).toRepresentation).character ∧
      (∀ j, ((σ j).toRepresentation).IsIrreducible) ∧
      (∀ i j, j ∈ S i ↔ Nonempty (((σ j).toRepresentation).Equiv (π (c i)).ρ)) ∧
      (∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (d i : AlgebraicClosure K) • (π (c i)).ρ.character) ∧
      Function.Injective c := by
  classical
  obtain ⟨ι, _, ψ, d, hψ_fd, hψ_pairwise, hψ_irr, a, σ, S,
    hinternal, hσchar, hσirr, hS, hfiber⟩ :=
    L.algClosure_packet_block_data (p := p) (ρ := ρ)
  obtain ⟨κ, _, π, hπ_fd, hπ_pairwise, hπ_complete⟩ :=
    Representation.exists_complete_pairwise_nonisomorphic_rep_family
      (k := AlgebraicClosure K) (G := G)
  have hchoose_rep :
      ∀ i, ∃ q, Nonempty (Rep.of (ψ i).ρ ≅ Rep.of (π q).ρ) := by
    intro i
    letI : (ψ i).ρ.IsIrreducible := hψ_irr i
    rcases IsCompleteIrreducibleFamily.exists_iso_of_representation
        (π := fun q ↦ FDRep.of (π q).ρ) hπ_complete (ψ i).ρ inferInstance with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rcases hq with ⟨eFD⟩
    exact
      ⟨(forget₂ (FDRep (AlgebraicClosure K) G) (Rep (AlgebraicClosure K) G)).mapIso eFD⟩
  choose c hc using hchoose_rep
  have hequiv : ∀ i, (ψ i).ρ.Equiv (π (c i)).ρ := by
    intro i
    exact Classical.choice
      (Representation.nonempty_equiv_of_nonempty_iso_of_rep
        (K := AlgebraicClosure K) (G := G) (ψ i).ρ (π (c i)).ρ (hc i))
  refine ⟨ι, inferInstance, ψ, d, hψ_fd, a, σ, S, κ, inferInstance, π, hπ_fd,
    hπ_pairwise, hπ_complete, c, hequiv, ?_⟩
  refine ⟨hinternal, hσchar, hσirr, ?_, ?_, ?_⟩
  · intro i j
    constructor
    · intro hj
      rcases (hS i j).mp hj with ⟨eσψ⟩
      exact ⟨eσψ.trans (hequiv i)⟩
    · intro hj
      rcases hj with ⟨eσπ⟩
      exact (hS i j).mpr ⟨eσπ.trans (hequiv i).symm⟩
  · intro i
    -- Transport the Chapter `12` packet character formula across the chosen equivalence
    -- `ψ i ≃ π (c i)` to match the complete-family indexing.
    calc
      Finset.sum
          (S i)
          (fun j ↦ ((σ j).toRepresentation).character) =
        (d i : AlgebraicClosure K) • (ψ i).ρ.character := hfiber i
      _ = (d i : AlgebraicClosure K) • (π (c i)).ρ.character := by
            congr 1
            simpa using Representation.char_iso (hequiv i)
  · intro i j hij
    -- If two packet indices landed on the same complete-family slot, the chosen equivalences
    -- would make the corresponding packet constituents isomorphic, contradicting pairwise
    -- nonisomorphism of the original packet family.
    subst hij
    by_contra hne
    exact hψ_pairwise hne ⟨Rep.mkIso ((hequiv i).trans (hequiv j).symm)⟩

/-- Helper for Proposition 16-16.4-1: once the packet-to-complete-family indexing map is
injective, every complete-family slot in its image has a unique packet label above it. This is the
exact indexing normalization needed before defining the supported Fourier family on
`Finset.univ.image c`. -/
lemma existsUnique_preimage_of_mem_univ_image_local
    {ι : Type*} [Fintype ι]
    {κ : Type*} [DecidableEq κ]
    {c : ι → κ}
    (hc : Function.Injective c) {q : κ} (hq : q ∈ Finset.univ.image c) :
    ∃! i : ι, c i = q := by
  classical
  -- Read `q` as an actual image point, then use injectivity to force uniqueness of its preimage.
  rcases Finset.mem_image.mp hq with ⟨i, -, rfl⟩
  refine ⟨i, rfl, ?_⟩
  intro j hj
  exact hc hj

/-- Helper for Proposition 16-16.4-1: a family indexed by packet labels extends to the complete
family index set by transporting along the unique preimage on `Finset.univ.image c` and setting
the complementary coordinates to `0`. This isolates the transport bookkeeping needed for the
source-faithful inverse-Wedderburn preimage. -/
noncomputable def family_supported_on_univ_image_local
    {ι : Type*} [Fintype ι]
    {κ : Type*} [DecidableEq κ]
    {V : κ → Type*} [∀ q, Zero (V q)]
    (c : ι → κ) (hc : Function.Injective c)
    (f : ∀ i, V (c i)) :
    ∀ q, V q :=
  fun q =>
    if hq : q ∈ Finset.univ.image c then
      let i := Classical.choose
        (existsUnique_preimage_of_mem_univ_image_local (c := c) hc hq)
      let hi : c i = q :=
        (Classical.choose_spec
          (existsUnique_preimage_of_mem_univ_image_local (c := c) hc hq)).1
      hi ▸ f i
    else
      0

/-- Helper for Proposition 16-16.4-1: on a packet index `c i`, the supported extension recovers
the original family value. This is the normalization used when reading off the distinguished
coordinate after constructing the complete-family preimage. -/
lemma family_supported_on_univ_image_local_apply
    {ι : Type*} [Fintype ι]
    {κ : Type*} [DecidableEq κ]
    {V : κ → Type*} [∀ q, Zero (V q)]
    {c : ι → κ} (hc : Function.Injective c)
    (f : ∀ i, V (c i)) (i : ι) :
    family_supported_on_univ_image_local c hc f (c i) = f i := by
  classical
  have hmem : c i ∈ Finset.univ.image c := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hchoose :
      Classical.choose
          (existsUnique_preimage_of_mem_univ_image_local (c := c) hc hmem) = i := by
    -- Injectivity forces the chosen preimage above `c i` to be the original packet label `i`.
    exact hc (Classical.choose_spec
      (existsUnique_preimage_of_mem_univ_image_local (c := c) hc hmem)).1
  -- Route correction: normalize the transport at `c i` before the main Fourier comparison uses it.
  simpa [family_supported_on_univ_image_local, hmem, hchoose]

/-- Helper for Proposition 16-16.4-1: away from the packet support `Finset.univ.image c`, the
extended family is definitionally zero. This is the off-support normalization used in the same
inverse-Wedderburn comparison. -/
lemma family_supported_on_univ_image_local_apply_of_not_mem
    {ι : Type*} [Fintype ι]
    {κ : Type*} [DecidableEq κ]
    {V : κ → Type*} [∀ q, Zero (V q)]
    {c : ι → κ} (hc : Function.Injective c)
    (f : ∀ i, V (c i)) {q : κ}
    (hq : q ∉ Finset.univ.image c) :
    family_supported_on_univ_image_local c hc f q = 0 := by
  -- Off the image, the definition already uses the zero branch.
  simp [family_supported_on_univ_image_local, hq]

/-- Helper for Proposition 16-16.4-1: when the supported family is constantly the identity on the
packet image, its extension to the complete-family index set is exactly the indicator projector
`q ↦ if q ∈ Finset.univ.image c then id else 0`. This is the normalization consumed by the
remaining `φ = LinearMap.id` packet-projector proofs. -/
lemma family_supported_on_univ_image_local_id
    {F : Type*} [Field F] [Algebra A F] [IsScalarTower A K F]
    {κ : Type*} [DecidableEq κ]
    {ι : Type*} [Fintype ι]
    (π : κ → Rep F G)
    (c : ι → κ) (hc : Function.Injective c) :
    family_supported_on_univ_image_local c hc
        (fun i ↦ (LinearMap.id : Module.End F (π (c i)))) =
      fun q ↦ if q ∈ Finset.univ.image c then (LinearMap.id : Module.End F (π q)) else 0 := by
  classical
  ext q
  by_cases hq : q ∈ Finset.univ.image c
  · -- On the packet image, the supported-family definition transports `LinearMap.id`
    -- along the chosen equality `c i = q`, which is still definitionally `LinearMap.id`.
    simp [family_supported_on_univ_image_local, hq]
  · -- Off the packet image, the definition is already the zero branch.
    simp [family_supported_on_univ_image_local, hq]

/-- Helper for Proposition 16-16.4-1: after applying the inverse-Wedderburn equivalence to the
family supported on `Finset.univ.image c`, the coordinate at `c i` is exactly the original packet
endomorphism `f i`. This is the source-faithful on-support read-off used when the mapped Serre
element is identified with that supported preimage. -/
lemma irreducibleFamilyEndAlgEquiv_symm_supported_family_apply
    {F : Type*} [Field F] [Algebra A F] [IsScalarTower A K F]
    [IsAlgClosed F] [Invertible (Nat.card G : F)]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : κ → Rep F G)
    [∀ q, FiniteDimensional F (π q)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ))
    {ι : Type*} [Fintype ι]
    (c : ι → κ) (hc : Function.Injective c)
    (f : ∀ i, Module.End F (π (c i))) (i : ι) :
    (π (c i)).ρ.asAlgebraHom
        ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
          (family_supported_on_univ_image_local c hc f)) =
      f i := by
  -- First read off the `c i` coordinate of the inverse-Wedderburn preimage, then normalize the
  -- supported family back to the original packet endomorphism.
  rw [irreducibleFamilyEndAlgEquiv_symm_coordinate_action_local
    (π := π) hπ_pairwise hπ_complete
    (f := family_supported_on_univ_image_local c hc f) (i := c i)]
  exact family_supported_on_univ_image_local_apply (hc := hc) f i

/-- Helper for Proposition 16-16.4-1: after applying the inverse-Wedderburn equivalence to the
family supported on `Finset.univ.image c`, every coordinate outside that support acts by `0`.
This is the off-support normalization used by the packet projector argument. -/
lemma irreducibleFamilyEndAlgEquiv_symm_supported_family_apply_of_not_mem
    {F : Type*} [Field F] [Algebra A F] [IsScalarTower A K F]
    [IsAlgClosed F] [Invertible (Nat.card G : F)]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : κ → Rep F G)
    [∀ q, FiniteDimensional F (π q)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ))
    {ι : Type*} [Fintype ι]
    (c : ι → κ) (hc : Function.Injective c)
    (f : ∀ i, Module.End F (π (c i))) {q : κ}
    (hq : q ∉ Finset.univ.image c) :
    (π q).ρ.asAlgebraHom
        ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
          (family_supported_on_univ_image_local c hc f)) =
      0 := by
  -- Read off the `q`-coordinate of the inverse-Wedderburn preimage and use the off-support
  -- branch of the supported family definition.
  rw [irreducibleFamilyEndAlgEquiv_symm_coordinate_action_local
    (π := π) hπ_pairwise hπ_complete
    (f := family_supported_on_univ_image_local c hc f) (i := q)]
  exact family_supported_on_univ_image_local_apply_of_not_mem (hc := hc) f hq

/-- Helper for Proposition 16-16.4-1: the inverse-Wedderburn preimage of the identity family
supported on `Finset.univ.image c` acts on the complete irreducible family exactly as the packet
projector `q ↦ if q ∈ Finset.univ.image c then id else 0`. This is the precise product-side
projector equality needed before applying the injective-coordinate annihilator lemma. -/
lemma irreducibleFamilyEndAlgEquiv_symm_supported_id_family
    {F : Type*} [Field F] [Algebra A F] [IsScalarTower A K F]
    [IsAlgClosed F] [Invertible (Nat.card G : F)]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : κ → Rep F G)
    [∀ q, FiniteDimensional F (π q)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ))
    {ι : Type*} [Fintype ι]
    (c : ι → κ) (hc : Function.Injective c) :
    (fun q ↦
      (π q).ρ.asAlgebraHom
        ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
          (family_supported_on_univ_image_local c hc
            (fun i ↦ (LinearMap.id : Module.End F (π (c i))))))) =
      fun q ↦ if q ∈ Finset.univ.image c then (LinearMap.id : Module.End F (π q)) else 0 := by
  classical
  funext q
  by_cases hq : q ∈ Finset.univ.image c
  · rcases Finset.mem_image.mp hq with ⟨i, -, hiq⟩
    subst hiq
    -- On the packet image, the supported inverse-Wedderburn preimage acts by the chosen identity.
    simpa [hq] using
      irreducibleFamilyEndAlgEquiv_symm_supported_family_apply
        (π := π) hπ_pairwise hπ_complete c hc
        (fun i ↦ (LinearMap.id : Module.End F (π (c i)))) i
  · -- Off the packet image, the supported inverse-Wedderburn preimage acts trivially.
    simpa [hq] using
      irreducibleFamilyEndAlgEquiv_symm_supported_family_apply_of_not_mem
        (π := π) hπ_pairwise hπ_complete c hc
        (fun i ↦ (LinearMap.id : Module.End F (π (c i)))) hq

/-- Helper for Proposition 16-16.4-1: for a complete irreducible family over
`AlgebraicClosure K`, the supported identity family already determines the exact injective product
target and packet projector required by the general annihilator lemma. This isolates the purely
Wedderburn-side data of the characteristic-zero projector argument so the only remaining step is
to identify Serre's mapped element with this supported preimage. -/
lemma irreducibleFamily_supported_id_projector_target_local
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : κ → Rep (AlgebraicClosure K) G)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ))
    {ι : Type*} [Fintype ι]
    (c : ι → κ) (hc : Function.Injective c) :
    Function.Injective (ρ̃[π]) ∧
      (ρ̃[π])
          ((Representation.irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm
            (family_supported_on_univ_image_local c hc
              (fun i ↦ (LinearMap.id : Module.End (AlgebraicClosure K) (π (c i)))))) =
        fun q ↦
          if q ∈ Finset.univ.image c then
            (LinearMap.id : Module.End (AlgebraicClosure K) (π q))
          else
            0 := by
  refine ⟨?_, ?_⟩
  · -- The complete-family product action is the injective target used for coordinatewise
    -- projector calculations.
    exact
      Representation.familyEndAlgHom_injective_of_complete_family
        (π := π) hπ_pairwise hπ_complete
  · -- Read off the supported inverse-Wedderburn preimage coordinatewise; this is exactly the
    -- packet projector normalization needed later.
    ext q
    simpa using congrFun
      (irreducibleFamilyEndAlgEquiv_symm_supported_id_family
        (π := π) hπ_pairwise hπ_complete c hc) q

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the remaining packet
block computation should show that the mapped Serre element acts on the scalar extension by the
base-changed ambient endomorphism attached to `φ`. The target file only uses this already lifted
identity and then descends it back to `K`. -/
lemma equalChar_algClosure_fourier_action_eq_baseChange
    [CharP K p]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) =
      LinearMap.baseChange (AlgebraicClosure K)
        ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  -- TODO: cut out the distinguished packet block in equal characteristic, compute the coordinate
  -- action of the mapped Serre element there, and then reassemble the scalar-extension action as
  -- the transported base change of `φ`. The support-side `φ = LinearMap.id` normalization is
  -- already factored into `algClosure_baseChange_endHom_id_local`.
  sorry

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, once the distinguished
packet-block projector for `φ = LinearMap.id` is identified, the same coordinatewise projector
argument as in characteristic zero yields the forward annihilator statement consumed by the target
file. -/
lemma equalChar_serre_fourier_id_mul_eq_zero_of_algClosure_action_zero
    [CharP K p]
    (hdefect : ρ.HasDefectZero p) (u : A[G])
    (hu :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0) :
    MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
      (L.serre_fourier_element hdefect
        (LinearMap.id : Module.End A L.toSubmodule) * u) = 0 := by
  -- TODO: identify the mapped equal-characteristic Serre projector with the distinguished packet
  -- block projector, use `algClosure_family_equiv_action_zero_of_mapped_ambient_zero_local` and
  -- `algClosure_family_equiv_action_id_of_mapped_ambient_id_local` for the packet coordinates, and
  -- feed that description into
  -- `mapped_serre_fourier_id_mul_eq_zero_of_injective_product_projector`.
  sorry

/-- Helper for Proposition 16-16.4-1: once the source Fourier element produces a genuine
`A[G]`-linear section of the tensor action map, Chapter `14` turns that section into the
averaging endomorphism required for projectivity. -/
lemma exists_averaging_endomorphism_of_tensor_section
    :
    letI : Fintype G := Fintype.ofFinite G
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    ∀ v : L.toSubmodule →ₗ[A[G]] TensorProduct A A[G] L.toSubmodule,
      (groupAlgebra_tensor_action (Λ := A) (G := G) (P := L.toSubmodule)).comp v = LinearMap.id →
      ∃ u : Module.End A L.toSubmodule, u.sumOfConjugates G = LinearMap.id := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  classical
  intro v hv
  let u : Module.End A L.toSubmodule :=
    tensor_left_coeffOne (Λ := A) (G := G) (P := L.toSubmodule).comp (v.restrictScalars A)
  have hvA :
      ((groupAlgebra_tensor_action (Λ := A) (G := G) (P := L.toSubmodule)).restrictScalars A).comp
        (v.restrictScalars A) = LinearMap.id := by
    -- Restrict the equivariant section to the coefficient ring `A`.
    ext x
    simpa using LinearMap.congr_fun hv x
  refine ⟨u, ?_⟩
  -- Route correction: isolate the textbook averaging step from the missing Fourier comparison.
  calc
    u.sumOfConjugates G =
        ((groupAlgebra_tensor_action (Λ := A) (G := G) (P := L.toSubmodule)).restrictScalars A).comp
          (v.restrictScalars A) := by
            symm
            exact tensor_action_comp_equivariant_eq_sumOfConjugates
              (Λ := A) (G := G) (P := L.toSubmodule) v
    _ = LinearMap.id := hvA

/-- Helper for Proposition 16-16.4-1: an averaging endomorphism on the stable lattice gives the
projective splitting criterion from Lemma `14-14.4-1`. -/
lemma projective_of_exists_averaging_endomorphism
    (u : Module.End A L.toSubmodule)
    :
    letI : Fintype G := Fintype.ofFinite G
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    u.sumOfConjugates G = LinearMap.id →
      Module.Projective A[G] L.toRepresentation.asModule := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  intro hu
  have hprojA : Module.Projective A L.toSubmodule := L.toSubmodule_projective
  -- Apply the Chapter `14` averaging criterion on the underlying lattice owner.
  have hproj :
      Module.Projective A[G] L.toSubmodule := by
      exact
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := A) (G := G) (P := L.toSubmodule)).2
        ⟨hprojA, u, hu⟩
  simpa using hproj

end DefectZero

end StableLattice

end
