import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_160_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_106_4
import StacksProject_2024.stacks_project.Chap15.Definition_15_37_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_18_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_38_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_39_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsNoetherianRing B] [IsCompleteLocalRing B]
variable [Algebra (ResidueField A) B]

local notation "κA" => ResidueField A

/-!
Helper API for the source-faithful setup of Lemma 15.40.6.
-/

/-- Helper for Lemma 15.40.6: the relevant local homomorphism is the composite
`A → ResidueField A → B` through the residue field. -/
private noncomputable abbrev residueCompositeToTarget : A →+* B :=
  (algebraMap κA B).comp (residue A)

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- Helper for Lemma 15.40.6: the composite map through the residue field is a local
homomorphism. -/
private theorem residueCompositeToTarget_isLocalHom :
    IsLocalHom (residueCompositeToTarget (A := A) (B := B)) := by
  -- The residue map is local, and local homomorphisms are stable under composition.
  dsimp [residueCompositeToTarget]
  infer_instance

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.40.6: formal smoothness over the residue field makes the target regular
local. -/
private theorem isRegularLocalRing_target_of_formallySmooth_residue
    (hfs : (algebraMap κA B).formally_smooth_for_adic (maximalIdeal B)) :
    IsRegularLocalRing B := by
  -- This is exactly Lemma `15.38.2` applied to the residue-field algebra structure on `B`.
  exact isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic hfs

/-- Helper for Lemma 15.40.6: a universe-aligned wrapper for the `15.39.3` power-series
presentation package. -/
private abbrev HasPowerSeriesPresentation (f : A →+* B) : Prop :=
  ((∃ _ : ringChar A = ringChar (ResidueField A),
        ∃ (σ τ : Type (max u v)) (_ : Finite σ) (_ : Finite τ)
          (K L : Type (max u v)) (_ : Field K) (_ : Field L),
          let P := MvPowerSeries σ K
          let Q := MvPowerSeries τ L
          ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
            let _ : Algebra P Q := rToS.toAlgebra
            Function.Surjective rToA ∧
              Function.Surjective sToB ∧
              sToB.comp rToS = f.comp rToA ∧
              (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
                (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                  IsRegularSystemOfParameters x ∧
                    (∀ i, rToS (x i : P) = (z i : Q)) ∧
                    IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
              rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q))
    ∨
    (∃ (p : ℕ) (_ : Nat.Prime p), CharP (ResidueField A) p ∧
        ∃ (σ τ : Type (max u v)) (_ : Finite σ) (_ : Finite τ)
          (R₀ S₀ : Type (max u v)) (_ : CommRing R₀) (_ : CommRing S₀)
          (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
          let P := MvPowerSeries σ R₀
          let Q := MvPowerSeries τ S₀
          ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
            let _ : Algebra P Q := rToS.toAlgebra
            Function.Surjective rToA ∧
              Function.Surjective sToB ∧
              sToB.comp rToS = f.comp rToA ∧
              (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
                (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                  IsRegularSystemOfParameters x ∧
                    (∀ i, rToS (x i : P) = (z i : Q)) ∧
                    IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
              rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q)))

/-- Helper for Lemma 15.40.6: Noetherianity transports across the canonical `ULift`
ring equivalence. -/
private theorem isNoetherianRing_ulift {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (ULift.{max u v} R) := by
  -- The `ULift` source and target are ring-equivalent, so the Noetherian owner theorem descends.
  exact isNoetherianRing_of_ringEquiv R
    (ULift.ringEquiv.symm : R ≃+* ULift.{max u v} R)

/-- Helper for Lemma 15.40.6: complete-locality transports across the canonical `ULift`
ring equivalence. -/
private theorem isCompleteLocalRing_ulift {R : Type u} [CommRing R] [IsCompleteLocalRing R] :
    IsCompleteLocalRing (ULift.{max u v} R) := by
  let e : R ≃+* ULift.{max u v} R := ULift.ringEquiv.symm
  letI : IsLocalRing (ULift.{max u v} R) := RingEquiv.isLocalRing e
  have hcomplete :
      IsAdicComplete (maximalIdeal (ULift.{max u v} R)) (ULift.{max u v} R) := by
    -- Transport adic completeness across the equivalence and rewrite the maximal ideal.
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact (IsAdicComplete.congr_ringEquiv (I := maximalIdeal R) e).2 inferInstance
  exact { toIsLocalRing := inferInstance, toIsAdicComplete := hcomplete }

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsCompleteLocalRing A] [IsCompleteLocalRing B]
  [Algebra κA B] in
/-- Helper for Lemma 15.40.6: a surjective local homomorphism induces a bijection on residue
fields. -/
private theorem residueField_map_bijective_of_surjective_localHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Nontrivial S]
    (f : R →+* S) (hf_surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  constructor
  · exact RingHom.injective (ResidueField.map f)
  · intro z
    -- Lift a residue-class element through `f`, then rewrite the induced residue-field map.
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, rfl⟩ := hf_surj s
    refine ⟨residue R r, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f r

/-- Helper for Lemma 15.40.6: a bijective ring homomorphism preserves ring characteristic. -/
private theorem ringChar_eq_of_bijective
    {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (hf : Function.Bijective f) :
    ringChar R = ringChar S := by
  apply Nat.dvd_antisymm
  · -- Pull the vanishing of `ringChar S` back through injectivity of `f`.
    have hzeroS : ((ringChar S : ℕ) : S) = 0 :=
      (ringChar.spec S (ringChar S)).2 dvd_rfl
    have hmap : f ((ringChar S : ℕ) : R) = f 0 := by
      simpa using hzeroS
    have hzeroR : ((ringChar S : ℕ) : R) = 0 := hf.1 hmap
    exact (ringChar.spec R (ringChar S)).mp hzeroR
  · -- Map the vanishing of `ringChar R` forward to `S`.
    have hzeroR : ((ringChar R : ℕ) : R) = 0 :=
      (ringChar.spec R (ringChar R)).2 dvd_rfl
    have hzeroS' : f ((ringChar R : ℕ) : R) = 0 := by
      rw [hzeroR]
      simp
    have hmapNat : f ((ringChar R : ℕ) : R) = ((ringChar R : ℕ) : S) := by
      rw [map_natCast]
    have hzeroS : ((ringChar R : ℕ) : S) = 0 := by
      rw [hmapNat] at hzeroS'
      exact hzeroS'
    exact (ringChar.spec S (ringChar R)).mp hzeroS

/-- Helper for Lemma 15.40.6: a bijective ring homomorphism transports `CharP` backwards. -/
private theorem charP_of_bijective
    {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (hf : Function.Bijective f) {p : ℕ} [CharP S p] :
    CharP R p := by
  -- Compare ring characteristics across the bijection and then repackage them as `CharP`.
  apply ringChar.of_eq
  calc
    ringChar R = ringChar S := ringChar_eq_of_bijective f hf
    _ = p := by simpa using (ringChar.eq S p)

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsCompleteLocalRing A] [IsCompleteLocalRing B]
  [Algebra κA B] in
/-- Helper for Lemma 15.40.6: precomposing a formally smooth adic map with a ring equivalence of
discrete source rings preserves adic formal smoothness. -/
private theorem formally_smooth_for_adic_of_domain_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : S →+* T) {J : Ideal T}
    (hf : f.formally_smooth_for_adic J) :
    (f.comp e.toRingHom).formally_smooth_for_adic J := by
  rw [RingHom.formally_smooth_for_adic_iff] at hf ⊢
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  letI : TopologicalSpace T := Ideal.adicTopology J
  refine
    { toContinuous := hf.toContinuous.comp continuous_of_discreteTopology
      lift_condition := ?_ }
  intro B _ _ _ L _ hL g hg g0 hg0 hcomm
  let g0S : S →+* B := g0.comp e.symm.toRingHom
  have hg0S : Continuous g0S := hg0.comp continuous_of_discreteTopology
  have hcommS : (Ideal.Quotient.mk L).comp g0S = g.comp f := by
    -- Move the base square across the inverse equivalence on the discrete source.
    ext s
    simpa [g0S, RingHom.comp_assoc] using DFunLike.congr_fun hcomm (e.symm s)
  -- Solve the lifting problem over `S`, then evaluate it back on the original source `R`.
  obtain ⟨φ, hφcont, hφquot, hφbase⟩ :=
    RingHom.FormallySmoothTopologically.exists_lift hf L hL g hg g0S hg0S hcommS
  refine ⟨φ, hφcont, hφquot, ?_⟩
  ext r
  simpa [g0S, RingHom.comp_assoc] using DFunLike.congr_fun hφbase (e r)

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- Helper for Lemma 15.40.6: a surjective local map `P → A` transports the given formal
smoothness of `κ(A) → B` back to the induced residue-field map `κ(P) → B`. -/
private theorem residue_formallySmooth_of_surjective_local_source
    {P : Type*} [CommRing P] [IsLocalRing P]
    (rToA : P →+* A) (hrToA : Function.Surjective rToA) [IsLocalHom rToA]
    (hfs : (algebraMap κA B).formally_smooth_for_adic (maximalIdeal B)) :
    let eκ : ResidueField P ≃+* κA :=
      RingEquiv.ofBijective (ResidueField.map rToA)
        (residueField_map_bijective_of_surjective_localHom rToA hrToA)
    let _ : Algebra (ResidueField P) B := ((algebraMap κA B).comp eκ.toRingHom).toAlgebra
    (algebraMap (ResidueField P) B).formally_smooth_for_adic (maximalIdeal B) := by
  let eκ : ResidueField P ≃+* κA :=
    RingEquiv.ofBijective (ResidueField.map rToA)
      (residueField_map_bijective_of_surjective_localHom rToA hrToA)
  let _ : Algebra (ResidueField P) B := ((algebraMap κA B).comp eκ.toRingHom).toAlgebra
  -- Transport the source field across the residue-field equivalence induced by `P → A`.
  simpa [eκ] using
    formally_smooth_for_adic_of_domain_ringEquiv
      (J := maximalIdeal B) eκ (algebraMap κA B) hfs

/-- Helper for Lemma 15.40.6: repackage a local homomorphism into the common `ULift`
universe needed to call Lemma `15.39.3`. -/
private noncomputable abbrev uliftLocalHom (f : A →+* B) :
    ULift.{max u v} A →+* ULift.{max u v} B :=
  ((ULift.ringEquiv.symm : B ≃+* ULift.{max u v} B).toRingHom).comp
    (f.comp ((ULift.ringEquiv : ULift.{max u v} A ≃+* A).toRingHom))

omit [IsNoetherianRing A] [IsNoetherianRing B] [Algebra κA B] in
/-- Helper for Lemma 15.40.6: the `ULift` transport of a local homomorphism is still local. -/
private theorem uliftLocalHom_isLocalHom (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (uliftLocalHom (A := A) (B := B) f) := by
  letI : IsLocalRing (ULift.{max u v} A) :=
    (isCompleteLocalRing_ulift (R := A)).toIsLocalRing
  letI : IsLocalRing (ULift.{max u v} B) :=
    (isCompleteLocalRing_ulift (R := B)).toIsLocalRing
  have hdown :
      IsLocalHom ((ULift.ringEquiv : ULift.{max u v} A ≃+* A).toRingHom) := by
    -- The downward `ULift` equivalence is surjective between local rings.
    exact Function.Surjective.isLocalHom _
      (ULift.ringEquiv : ULift.{max u v} A ≃+* A).surjective
  have hup :
      IsLocalHom ((ULift.ringEquiv.symm : B ≃+* ULift.{max u v} B).toRingHom) := by
    -- The upward `ULift` equivalence is likewise a surjective local map.
    exact Function.Surjective.isLocalHom _
      (ULift.ringEquiv.symm : B ≃+* ULift.{max u v} B).surjective
  -- Local homomorphisms are stable under composition with the two `ULift` equivalences.
  dsimp [uliftLocalHom]
  infer_instance

/-- Helper for Lemma 15.40.6: after aligning `A` and `B` into a common universe, the
power-series presentation of Lemma `15.39.3` descends back to the original rings. -/
private theorem hasPowerSeriesPresentation_of_ulift_localHom_completeLocal
    (f : A →+* B) [IsLocalHom f] :
    HasPowerSeriesPresentation (A := A) (B := B) f := by
  -- Unfold the local packaging predicate once so the two source branches can be rebuilt directly.
  unfold HasPowerSeriesPresentation
  letI : IsNoetherianRing (ULift.{max u v} A) := isNoetherianRing_ulift (R := A)
  letI : IsCompleteLocalRing (ULift.{max u v} A) := isCompleteLocalRing_ulift (R := A)
  letI : IsNoetherianRing (ULift.{max u v} B) := isNoetherianRing_ulift (R := B)
  letI : IsCompleteLocalRing (ULift.{max u v} B) := isCompleteLocalRing_ulift (R := B)
  let fκ : A →+* ULift.{max u v} A :=
    (ULift.ringEquiv.symm : A ≃+* ULift.{max u v} A).toRingHom
  letI : IsLocalHom fκ :=
    Function.Surjective.isLocalHom _ (ULift.ringEquiv.symm : A ≃+* ULift.{max u v} A).surjective
  have hκbij : Function.Bijective (ResidueField.map fκ) := by
    -- The residue fields of `A` and `ULift A` are identified by the induced bijective map.
    exact residueField_map_bijective_of_surjective_localHom fκ
      (ULift.ringEquiv.symm : A ≃+* ULift.{max u v} A).surjective
  let fu : ULift.{max u v} A →+* ULift.{max u v} B := uliftLocalHom (A := A) (B := B) f
  letI : IsLocalHom fu := uliftLocalHom_isLocalHom (A := A) (B := B) f
  rcases exists_powerSeries_presentation_of_localHom_completeLocal (f := fu) with
      hfield | hmixed
  · rcases hfield with
      ⟨hchar, σ, τ, hσfinite, hτfinite, K, L, hK, hL, rToA, sToB, rToS, hsurjA,
        hsurjB, hsq, hparam, hflat, hreg⟩
    have hcharA : ringChar A = ringChar κA := by
      -- Compare the ring characteristic of `A` and its lifted residue field through the two
      -- canonical bijections.
      calc
        ringChar A = ringChar (ULift.{max u v} A) := by
          symm
          simpa using ringChar_eq_of_bijective
            ((ULift.ringEquiv : ULift.{max u v} A ≃+* A).toRingHom)
            (ULift.ringEquiv : ULift.{max u v} A ≃+* A).bijective
        _ = ringChar (ResidueField (ULift.{max u v} A)) := hchar
        _ = ringChar κA := by
          symm
          simpa [fκ] using ringChar_eq_of_bijective (ResidueField.map fκ) hκbij
    let rToA' : MvPowerSeries σ K →+* A :=
      ((ULift.ringEquiv : ULift.{max u v} A ≃+* A).toRingHom).comp rToA
    let sToB' : MvPowerSeries τ L →+* B :=
      ((ULift.ringEquiv : ULift.{max u v} B ≃+* B).toRingHom).comp sToB
    left
    refine ⟨hcharA, σ, τ, hσfinite, hτfinite, K, L, hK, hL, ?_⟩
    refine ⟨rToA', sToB', rToS, ?_⟩
    constructor
    · -- Surjectivity descends by lifting the target element into `ULift A` and then projecting.
      intro a
      obtain ⟨x, hx⟩ := hsurjA (ULift.up a)
      refine ⟨x, ?_⟩
      exact congrArg ULift.down hx
    constructor
    · -- The same argument descends surjectivity of the target-side quotient map.
      intro b
      obtain ⟨y, hy⟩ := hsurjB (ULift.up b)
      refine ⟨y, ?_⟩
      exact congrArg ULift.down hy
    constructor
    · -- Evaluate the commutative square on each power series and then descend from `ULift`.
      ext x
      have hsqx : sToB (rToS x) = fu (rToA x) := by
        simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) x)
      have hfu : fu (rToA x) = ULift.up (f (ULift.down (rToA x))) := rfl
      rw [hfu] at hsqx
      exact congrArg ULift.down hsqx
    constructor
    · -- The parameter data and the flat/regular-fiber conclusions live entirely on `P` and `Q`.
      exact hparam
    constructor
    · exact hflat
    · exact hreg
  · rcases hmixed with
      ⟨p, hp, hpChar, σ, τ, hσfinite, hτfinite, R₀, S₀, hR₀, hS₀, hCohenR₀, hCohenS₀,
        rToA, sToB, rToS, hsurjA, hsurjB, hsq, hparam, hflat, hreg⟩
    let _ : CharP (ResidueField (ULift.{max u v} A)) p := hpChar
    have hpCharA : CharP κA p := by
      -- Transport the residue-characteristic class back across the residue-field bijection.
      exact charP_of_bijective (ResidueField.map fκ) hκbij
    let rToA' : MvPowerSeries σ R₀ →+* A :=
      ((ULift.ringEquiv : ULift.{max u v} A ≃+* A).toRingHom).comp rToA
    let sToB' : MvPowerSeries τ S₀ →+* B :=
      ((ULift.ringEquiv : ULift.{max u v} B ≃+* B).toRingHom).comp sToB
    right
    refine ⟨p, hp, hpCharA, σ, τ, hσfinite, hτfinite, R₀, S₀, hR₀, hS₀, hCohenR₀,
      hCohenS₀, ?_⟩
    refine ⟨rToA', sToB', rToS, ?_⟩
    constructor
    · -- Surjectivity again descends by projecting the lifted witness from `ULift A`.
      intro a
      obtain ⟨x, hx⟩ := hsurjA (ULift.up a)
      refine ⟨x, ?_⟩
      exact congrArg ULift.down hx
    constructor
    · -- The target-side surjectivity descends in the same way.
      intro b
      obtain ⟨y, hy⟩ := hsurjB (ULift.up b)
      refine ⟨y, ?_⟩
      exact congrArg ULift.down hy
    constructor
    · -- The mixed-characteristic square also descends pointwise from the `ULift` presentation.
      ext x
      have hsqx : sToB (rToS x) = fu (rToA x) := by
        simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) x)
      have hfu : fu (rToA x) = ULift.up (f (ULift.down (rToA x))) := rfl
      rw [hfu] at hsqx
      exact congrArg ULift.down hsqx
    constructor
    · -- As above, the parameter data and the formal consequences are unchanged by the transport.
      exact hparam
    constructor
    · exact hflat
    · exact hreg

/-- Helper for Lemma 15.40.6: after aligning universes, the composite map
`A → ResidueField A → B` should inherit the presentation package from Lemma `15.39.3`. -/
private theorem exists_powerSeries_presentation_of_residueCompositeToTarget :
    HasPowerSeriesPresentation (A := A) (B := B)
      (residueCompositeToTarget (A := A) (B := B)) := by
  let _ : IsLocalHom (residueCompositeToTarget (A := A) (B := B)) :=
    residueCompositeToTarget_isLocalHom (A := A) (B := B)
  -- Apply the general `ULift` adapter to the composite local map used in the source proof.
  exact hasPowerSeriesPresentation_of_ulift_localHom_completeLocal
    (A := A) (B := B) (residueCompositeToTarget (A := A) (B := B))

/-- Helper for Lemma 15.40.6: a source-faithful presentation branch descends to a surjective map
from the closed fiber to `B`. -/
private theorem closedFiber_to_target_surjective_of_presentation
    {P Q : Type (max u v)} [CommRing P] [CommRing Q] [IsLocalRing P] [IsLocalRing Q]
    (rToA : P →+* A) (sToB : Q →+* B)
    [Algebra P Q] [IsLocalHom rToA]
    (hsToB : Function.Surjective sToB)
    (hsq : sToB.comp (algebraMap P Q) =
      residueCompositeToTarget (A := A) (B := B).comp rToA)
    {d : ℕ}
    (x : Fin d → maximalIdeal P) (z : Fin d → maximalIdeal Q)
    (hx : IsRegularSystemOfParameters x)
    (hmap : ∀ i, algebraMap P Q (x i : P) = (z i : Q)) :
    ∃ gbar : Ideal.Fiber (maximalIdeal P) Q →+* B, Function.Surjective gbar := by
  let J : Ideal Q := Ideal.map (algebraMap P Q) (maximalIdeal P)
  have hmapJ : J = parameterIdeal z := by
    -- Rewrite the image of the source maximal ideal via the chosen parameter family.
    dsimp [J]
    rw [← hx.2]
    simpa using
      parameterIdeal_map_eq_parameterIdeal_of_forall (algebraMap P Q) x z hmap
  have hz_zero : ∀ i, sToB (z i : Q) = 0 := by
    intro i
    have hx_mem : (x i : P) ∈ maximalIdeal P := (x i).2
    have hmap_le : Ideal.map rToA (maximalIdeal P) ≤ maximalIdeal A :=
      IsLocalRing.map_maximalIdeal_le (f := rToA)
    have hr_mem : rToA (x i : P) ∈ maximalIdeal A := by
      exact hmap_le (Ideal.mem_map_of_mem _ hx_mem)
    have hres_zero : residueCompositeToTarget (A := A) (B := B) (rToA (x i : P)) = 0 := by
      change algebraMap κA B (residue A (rToA (x i : P))) = 0
      rw [(IsLocalRing.residue_eq_zero_iff (R := A) (x := rToA (x i : P))).2 hr_mem]
      simp
    have hsq_i :=
      congrArg (fun f : P →+* B ↦ f (x i : P)) hsq
    calc
      sToB (z i : Q) = residueCompositeToTarget (A := A) (B := B) (rToA (x i : P)) := by
        simpa [RingHom.comp_apply, hmap i] using hsq_i
      _ = 0 := hres_zero
  have hJker : J ≤ RingHom.ker sToB := by
    -- The closed-fiber ideal is generated by elements killed in `B`, so `sToB` factors through.
    rw [hmapJ, IsLocalRing.parameterIdeal_eq_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (hz_zero i)
  let gquot : Q ⧸ J →+* B :=
    Ideal.Quotient.lift J sToB fun q hq ↦ RingHom.mem_ker.mp (hJker hq)
  let gbar : Ideal.Fiber (maximalIdeal P) Q →+* B :=
    gquot.comp (closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal P) Q ≃ₐ[P] Q ⧸ J).toRingEquiv.toRingHom
  refine ⟨gbar, ?_⟩
  intro b
  -- Lift `b` through `Q`, then through the closed-fiber quotient equivalence.
  obtain ⟨q, rfl⟩ := hsToB b
  refine ⟨(closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal P) Q ≃ₐ[P] Q ⧸ J).symm (Ideal.Quotient.mk J q), ?_⟩
  simp [gbar, gquot]

/-- Helper for Lemma 15.40.6: the kernel of a surjective map from a regular local closed fiber to
the regular local target is generated by a parameter block. -/
private theorem exists_kernel_parameter_block_on_closedFiber
    {F : Type*} [CommRing F] [IsLocalRing F] [IsRegularLocalRing F]
    (gbar : F →+* B) (hgbar : Function.Surjective gbar)
    [IsRegularLocalRing B] :
    ∃ (c : ℕ) (w : Fin c → maximalIdeal F),
      IsPartOfRegularSystemOfParameters (maximalIdeal F).spanFinrank w ∧
        parameterIdeal w = RingHom.ker gbar := by
  let e : F ⧸ RingHom.ker gbar ≃+* B :=
    RingHom.quotientKerEquivOfSurjective (f := gbar) hgbar
  have hquot : IsRegularLocalRing (F ⧸ RingHom.ker gbar) := by
    -- The quotient by the kernel is the regular local target itself.
    exact IsRegularLocalRing.of_ringEquiv e.symm
  -- Lemma `10.106.4` is exactly the source proof's kernel-killing step on the closed fiber.
  simpa using
    exists_regularSystemOfParameters_with_prefix_span_eq_of_quotient_isRegularLocalRing
      (R := F) (I := RingHom.ker gbar) hquot

/-- Helper for Lemma 15.40.6: the preimage of the closed point under a local homomorphism is the
closed point. -/
private theorem comap_maximalIdeal_eq_of_localHom
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    Ideal.comap f (maximalIdeal S) = maximalIdeal R := by
  apply le_antisymm
  · intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hfx : f x ∈ maximalIdeal S := hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hfx
    intro hxunit
    exact hfx (hxunit.map f)
  · intro x hx
    change f x ∈ maximalIdeal S
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    intro hfxunit
    exact hx (IsLocalHom.map_nonunit (f := f) x hfxunit)

/-- Helper for Lemma 15.40.6: after transporting scalars across a residue-field equivalence, the
tensor `ResidueField A ⊗[ResidueField P] B` collapses back to `B`. -/
private theorem residueFieldTensorTarget_algEquiv
    {P : Type*} [CommRing P] [IsLocalRing P]
    (eκ : ResidueField P ≃+* κA)
    [Algebra (ResidueField P) B]
    (hBalg : algebraMap (ResidueField P) B = (algebraMap κA B).comp eκ.toRingHom) :
    Nonempty <|
    let _ : Algebra (ResidueField P) κA := eκ.toRingHom.toAlgebra
    κA ⊗[ResidueField P] B ≃ₐ[κA] B := by
  let _ : Algebra (ResidueField P) κA := eκ.toRingHom.toAlgebra
  let _ : Algebra κA (ResidueField P) := eκ.symm.toRingHom.toAlgebra
  let _ : IsScalarTower (ResidueField P) κA κA := IsScalarTower.of_algebraMap_eq' rfl
  have htower_forward :
      ∀ x : ResidueField P,
        algebraMap (ResidueField P) B x =
          algebraMap κA B (algebraMap (ResidueField P) κA x) := by
    -- Rewrite the transported `ResidueField P`-algebra structure on `B` through `eκ`.
    intro x
    change algebraMap (ResidueField P) B x = algebraMap κA B (eκ x)
    exact congrArg (fun f : ResidueField P →+* B ↦ f x) hBalg
  let _ : IsScalarTower (ResidueField P) κA B :=
    IsScalarTower.of_algebraMap_eq htower_forward
  have htower_backward :
      ∀ x : κA,
        algebraMap κA B x =
          algebraMap (ResidueField P) B (algebraMap κA (ResidueField P) x) := by
    -- The inverse equivalence expresses the same scalar action in the opposite order.
    intro x
    change algebraMap κA B x = algebraMap (ResidueField P) B (eκ.symm x)
    rw [hBalg]
    simp [RingHom.comp_apply]
  let _ : IsScalarTower κA (ResidueField P) B :=
    IsScalarTower.of_algebraMap_eq htower_backward
  have hκ_backward :
      ∀ x : κA,
        algebraMap κA κA x =
          algebraMap (ResidueField P) κA (algebraMap κA (ResidueField P) x) := by
    -- The same comparison on `κ(A)` itself gives the compatibility needed for tensor collapse.
    intro x
    change x = eκ (eκ.symm x)
    simp
  let _ : IsScalarTower κA (ResidueField P) κA :=
    IsScalarTower.of_algebraMap_eq hκ_backward
  -- With both scalar actions synchronized, the left tensor factor is the unit object.
  exact ⟨by
    simpa using Algebra.TensorProduct.lidOfCompatibleSMul (ResidueField P) κA B⟩

/-- Helper for Lemma 15.40.6: the residue field of the closed point of a local ring is canonically
the ordinary residue field. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.40.6: the closed-point residue field carries the same
`ResidueField R`-algebra structure as the usual residue field. -/
private noncomputable abbrev maximalIdealResidueFieldAlgEquiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃ₐ[ResidueField R] ResidueField R :=
  AlgEquiv.ofRingEquiv (f := maximalIdealResidueFieldEquiv R) fun x ↦ by
    -- Proof comment: the inverse equivalence was defined from the canonical algebra map out of
    -- `ResidueField R`, so it fixes those scalars.
    exact (maximalIdealResidueFieldEquiv R).apply_symm_apply x

/-- Helper for Lemma 15.40.6: the closed points of two local `P`-algebras have the same
contraction to `Spec(P)`. -/
private theorem closedPoint_comap_eq_of_local_maps
    {P : Type*} {Q1 : Type*} [CommRing P] [CommRing Q1]
    [IsLocalRing P] [IsLocalRing Q1] [Algebra P A] [Algebra P Q1]
    [IsLocalHom (algebraMap P A)] [IsLocalHom (algebraMap P Q1)]
    :
    PrimeSpectrum.comap (algebraMap P A)
        ⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩ =
      PrimeSpectrum.comap (algebraMap P Q1)
        ⟨maximalIdeal Q1, (maximalIdeal.isMaximal Q1).isPrime⟩ := by
  let q1 : PrimeSpectrum Q1 := ⟨maximalIdeal Q1, (maximalIdeal.isMaximal Q1).isPrime⟩
  let pA : PrimeSpectrum A := ⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩
  -- Proof comment: both closed points contract to the maximal ideal of the local source `P`.
  apply PrimeSpectrum.ext
  simpa [pA, q1, PrimeSpectrum.comap_asIdeal] using
    (comap_maximalIdeal_eq_of_localHom (R := P) (S := A) (algebraMap P A)).trans
      (comap_maximalIdeal_eq_of_localHom (R := P) (S := Q1) (algebraMap P Q1)).symm

/-- Helper for Lemma 15.40.6: the closed point of a local `P`-algebra contracts to the closed
point of `P`. -/
private theorem closedPoint_comap_eq_source_closedPoint
    {P : Type*} {Q1 : Type*} [CommRing P] [CommRing Q1]
    [IsLocalRing P] [IsLocalRing Q1] [Algebra P Q1]
    [IsLocalHom (algebraMap P Q1)] :
    PrimeSpectrum.comap (algebraMap P Q1)
        ⟨maximalIdeal Q1, (maximalIdeal.isMaximal Q1).isPrime⟩ =
      ⟨maximalIdeal P, (maximalIdeal.isMaximal P).isPrime⟩ := by
  let q1 : PrimeSpectrum Q1 := ⟨maximalIdeal Q1, (maximalIdeal.isMaximal Q1).isPrime⟩
  let p : PrimeSpectrum P := ⟨maximalIdeal P, (maximalIdeal.isMaximal P).isPrime⟩
  -- Proof comment: this is the explicit prime-spectrum form of
  -- `comap_maximalIdeal_eq_of_localHom`.
  apply PrimeSpectrum.ext
  simpa [p, q1, PrimeSpectrum.comap_asIdeal] using
    comap_maximalIdeal_eq_of_localHom (R := P) (S := Q1) (algebraMap P Q1)

/-- Helper for Lemma 15.40.6: tensoring the right factor by an algebra equivalence preserves the
left scalar algebra. -/
private theorem tensor_rightFactor_algEquiv_over_left_scalar
    {k : Type*} {K : Type*} {X : Type*} {Y : Type*}
    [CommRing k] [CommRing K] [CommRing X] [CommRing Y]
    [Algebra k K] [Algebra k X] [Algebra k Y]
    (e : X ≃ₐ[k] Y) :
    Nonempty (K ⊗[k] X ≃ₐ[K] K ⊗[k] Y) := by
  -- Proof comment: keep the left tensor factor fixed and transport only the right factor.
  exact ⟨Algebra.TensorProduct.congr
    (.refl : K ≃ₐ[K] K) e⟩

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsCompleteLocalRing B] in
/-- Helper for Lemma 15.40.6: once the `ResidueField P`-algebra structure on `B` is transported
through the residue-field equivalence induced by a surjective local map `P → A`, the left tensor
factor `(maximalIdeal A).ResidueField` may be replaced by the ordinary residue field `κ(A)`. -/
private theorem maximalIdealResidueField_leftTensor_restrictScalars
    {P : Type*} [CommRing P] [IsLocalRing P] [Algebra P A]
    [IsLocalHom (algebraMap P A)]
    (hrToA : Function.Surjective (algebraMap P A))
    [Algebra (ResidueField P) B]
    (hBalg : algebraMap (ResidueField P) B =
      (algebraMap κA B).comp
        (RingEquiv.ofBijective (ResidueField.map (algebraMap P A))
          (residueField_map_bijective_of_surjective_localHom (algebraMap P A) hrToA)).toRingHom) :
    let eκ : ResidueField P ≃+* κA :=
      RingEquiv.ofBijective (ResidueField.map (algebraMap P A))
        (residueField_map_bijective_of_surjective_localHom (algebraMap P A) hrToA)
    let _ : Algebra (ResidueField P) κA := eκ.toRingHom.toAlgebra
    let _ : Algebra (ResidueField P) (maximalIdeal A).ResidueField :=
      ((algebraMap κA (maximalIdeal A).ResidueField).comp eκ.toRingHom).toAlgebra
    let _ : IsScalarTower (ResidueField P) κA (maximalIdeal A).ResidueField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (ResidueField P) κA B :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        change algebraMap (ResidueField P) B x = algebraMap κA B (eκ x)
        exact congrArg (fun f : ResidueField P →+* B ↦ f x) hBalg
    Nonempty (((maximalIdeal A).ResidueField ⊗[ResidueField P] B) ≃ₐ[κA]
      (κA ⊗[ResidueField P] B)) := by
  let eκ : ResidueField P ≃+* κA :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap P A))
      (residueField_map_bijective_of_surjective_localHom (algebraMap P A) hrToA)
  let _ : Algebra (ResidueField P) κA := eκ.toRingHom.toAlgebra
  let _ : Algebra (ResidueField P) (maximalIdeal A).ResidueField :=
    ((algebraMap κA (maximalIdeal A).ResidueField).comp eκ.toRingHom).toAlgebra
  let _ : IsScalarTower (ResidueField P) κA (maximalIdeal A).ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (ResidueField P) κA B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Proof comment: the transported `ResidueField P`-action on `B` is defined by composing the
      -- given `κ(A)`-action with the residue-field equivalence `eκ`.
      change algebraMap (ResidueField P) B x = algebraMap κA B (eκ x)
      exact congrArg (fun f : ResidueField P →+* B ↦ f x) hBalg
  -- Proof comment: once the scalar towers are explicit, tensor congruence replaces the closed
  -- point residue field of `A` by the ordinary residue field `κ(A)` on the left factor.
  exact ⟨Algebra.TensorProduct.congr
    (maximalIdealResidueFieldAlgEquiv (R := A))
    (.refl : B ≃ₐ[ResidueField P] B)⟩

/-- Helper for Lemma 15.40.6: after base changing a cleaned presentation ring along a surjective
local source map, the closed fiber over `A` is still the original target `B`. -/
private theorem baseChange_closedFiber_equiv_of_surjective_local_source
    {P : Type*} {Q1 : Type*} [CommRing P] [CommRing Q1]
    [IsLocalRing P] [IsLocalRing Q1] [Algebra P A] [Algebra P Q1]
    [IsLocalHom (algebraMap P A)] [IsLocalHom (algebraMap P Q1)]
    (hrToA : Function.Surjective (algebraMap P A))
    [Algebra (ResidueField P) B]
    (hBalg : algebraMap (ResidueField P) B =
      (algebraMap κA B).comp
        (RingEquiv.ofBijective (ResidueField.map (algebraMap P A))
          (residueField_map_bijective_of_surjective_localHom (algebraMap P A) hrToA)).toRingHom)
    (e : Ideal.Fiber (maximalIdeal P) Q1 ≃ₐ[ResidueField P] B) :
    Nonempty (Ideal.Fiber (maximalIdeal A) (A ⊗[P] Q1) ≃ₐ[κA] B) := by
  let eκ : ResidueField P ≃+* κA :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap P A))
      (residueField_map_bijective_of_surjective_localHom (algebraMap P A) hrToA)
  obtain ⟨eleft⟩ :=
    maximalIdealResidueField_leftTensor_restrictScalars (A := A) (B := B)
      (P := P) hrToA hBalg
  let _ := eκ
  let _ := eleft
  let q1 : PrimeSpectrum Q1 :=
    ⟨maximalIdeal Q1, (maximalIdeal.isMaximal Q1).isPrime⟩
  let pA : PrimeSpectrum A :=
    ⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩
  have hcompat :
      PrimeSpectrum.comap (algebraMap P A) pA =
        PrimeSpectrum.comap (algebraMap P Q1) q1 := by
    -- Proof comment: both closed points contract to the closed point of the local source `P`.
    simpa [pA, q1] using
      closedPoint_comap_eq_of_local_maps (P := P) (Q1 := Q1) (A := A)
  let esource :
      let p : PrimeSpectrum P := PrimeSpectrum.comap (algebraMap P Q1) q1
      let _ : Algebra p.asIdeal.ResidueField pA.asIdeal.ResidueField :=
        (Ideal.ResidueField.mapₐ p.asIdeal pA.asIdeal (Algebra.ofId P A)
          (by
            simpa [p, pA, q1, PrimeSpectrum.comap_asIdeal] using
              (congrArg PrimeSpectrum.asIdeal hcompat).symm)).toAlgebra
      pA.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Q1 ≃ₐ[pA.asIdeal.ResidueField]
        pA.asIdeal.Fiber (A ⊗[P] Q1) :=
    baseChanged_sourceFiber_algEquiv_rightOrderedFiber
      (R := P) (S := Q1) (R' := A) q1 pA hcompat
  let _ := esource
  -- TODO: the left-scalar rewrite is now isolated in
  -- `maximalIdealResidueField_leftTensor_restrictScalars`. The remaining blocker is the
  -- source-faithful closed-point owner transport that rewrites the domain of `esource` from the
  -- specialized closed-point source fiber over `PrimeSpectrum.comap (algebraMap P Q1) q1` to the
  -- canonical owner `Ideal.Fiber (maximalIdeal P) Q1`, so that `tensor_rightFactor_algEquiv_over_left_scalar e`,
  -- `eleft`, and `residueFieldTensorTarget_algEquiv eκ hBalg` can be composed.
  sorry

/-- Helper for Lemma 15.40.6: once the `15.39.3` presentation has been cleaned so that the closed
fiber is exactly `B`, the source proof finishes by formal smoothness over the presentation base
and base change to `A`. -/
private theorem exists_completeLocal_formallySmooth_lift_of_regularTarget_and_powerSeriesPresentation
    (hfs : (algebraMap κA B).formally_smooth_for_adic (maximalIdeal B))
    (hpres : HasPowerSeriesPresentation (A := A) (B := B)
      (residueCompositeToTarget (A := A) (B := B))) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C))
      (_ : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] B),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) := by
  let _ : IsRegularLocalRing B :=
    isRegularLocalRing_target_of_formallySmooth_residue (A := A) (B := B) hfs
  let _ : IsLocalHom (residueCompositeToTarget (A := A) (B := B)) :=
    residueCompositeToTarget_isLocalHom (A := A) (B := B)
  -- Route correction: keep the original `hfs` alive here so the final `15.40.5` step can use the
  -- transported residue-field formal smoothness, matching the source proof rather than rebuilding
  -- it from regularity after the branch cleanup.
  rcases hpres with hfield | hmixed
  · rcases hfield with
      ⟨hchar, σ, τ, hσfinite, hτfinite, K, L, hK, hL, rToA, sToB, rToS, hsurjA,
        hsurjB, hsq, hparam, hflat, hreg⟩
    let _ : Finite σ := hσfinite
    let _ : Finite τ := hτfinite
    let _ : Field K := hK
    let _ : Field L := hL
    let _ : Algebra (MvPowerSeries σ K) (MvPowerSeries τ L) := rToS.toAlgebra
    let _ : IsLocalHom rToA := Function.Surjective.isLocalHom _ hsurjA
    let _ : IsLocalHom sToB := Function.Surjective.isLocalHom _ hsurjB
    have hcomp : sToB.comp (algebraMap (MvPowerSeries σ K) (MvPowerSeries τ L)) =
        residueCompositeToTarget (A := A) (B := B).comp rToA := by
      simpa [RingHom.algebraMap_toAlgebra] using hsq
    let _ : IsLocalHom (sToB.comp rToS) := by
      simpa [RingHom.algebraMap_toAlgebra] using
        (hcomp ▸ (inferInstance :
          IsLocalHom (residueCompositeToTarget (A := A) (B := B).comp rToA)))
    let _ : IsLocalHom rToS := by
      simpa [RingHom.algebraMap_toAlgebra] using
        (isLocalHom_of_comp rToS sToB : IsLocalHom rToS)
    let _ : IsLocalHom (algebraMap (MvPowerSeries σ K) (MvPowerSeries τ L)) := by
      simpa [RingHom.algebraMap_toAlgebra] using (inferInstance : IsLocalHom rToS)
    rcases hparam with ⟨x, z, hx, hmap, hz⟩
    obtain ⟨gbar, hgbar⟩ :=
      closedFiber_to_target_surjective_of_presentation (A := A) (B := B)
        rToA sToB hsurjB hcomp x z hx
        (by
          intro i
          simpa [RingHom.algebraMap_toAlgebra] using hmap i)
    obtain ⟨c, w, hwpart, hwker⟩ :=
      exists_kernel_parameter_block_on_closedFiber (B := B) gbar hgbar
    let _ := hchar
    let _ := hflat
    let _ := hz
    let _ := c
    let _ := w
    let _ := hwpart
    let _ := hwker
    -- TODO: use Lemma `15.39.2` in the equal-characteristic branch to quotient by the kernel
    -- parameter block on the closed fiber, rebuild the cleaned presentation `Q1`, then apply
    -- Proposition `15.40.5` and base change to `A`.
    sorry
  · rcases hmixed with
      ⟨p, hp, hpChar, σ, τ, hσfinite, hτfinite, R₀, S₀, hR₀, hS₀, hCohenR₀, hCohenS₀,
        rToA, sToB, rToS, hsurjA, hsurjB, hsq, hparam, hflat, hreg⟩
    let _ : Finite σ := hσfinite
    let _ : Finite τ := hτfinite
    let _ : CommRing R₀ := hR₀
    let _ : CommRing S₀ := hS₀
    let _ : IsCohenRing R₀ := hCohenR₀
    let _ : IsCohenRing S₀ := hCohenS₀
    let _ : Algebra (MvPowerSeries σ R₀) (MvPowerSeries τ S₀) := rToS.toAlgebra
    let _ : IsLocalHom rToA := Function.Surjective.isLocalHom _ hsurjA
    let _ : IsLocalHom sToB := Function.Surjective.isLocalHom _ hsurjB
    have hcomp : sToB.comp (algebraMap (MvPowerSeries σ R₀) (MvPowerSeries τ S₀)) =
        residueCompositeToTarget (A := A) (B := B).comp rToA := by
      simpa [RingHom.algebraMap_toAlgebra] using hsq
    let _ : IsLocalHom (sToB.comp rToS) := by
      simpa [RingHom.algebraMap_toAlgebra] using
        (hcomp ▸ (inferInstance :
          IsLocalHom (residueCompositeToTarget (A := A) (B := B).comp rToA)))
    let _ : IsLocalHom rToS := by
      simpa [RingHom.algebraMap_toAlgebra] using
        (isLocalHom_of_comp rToS sToB : IsLocalHom rToS)
    let _ : IsLocalHom (algebraMap (MvPowerSeries σ R₀) (MvPowerSeries τ S₀)) := by
      simpa [RingHom.algebraMap_toAlgebra] using (inferInstance : IsLocalHom rToS)
    rcases hparam with ⟨x, z, hx, hmap, hz⟩
    obtain ⟨gbar, hgbar⟩ :=
      closedFiber_to_target_surjective_of_presentation (A := A) (B := B)
        rToA sToB hsurjB hcomp x z hx
        (by
          intro i
          simpa [RingHom.algebraMap_toAlgebra] using hmap i)
    obtain ⟨c, w, hwpart, hwker⟩ :=
      exists_kernel_parameter_block_on_closedFiber (B := B) gbar hgbar
    let _ := hp
    let _ := hpChar
    let _ := hflat
    let _ := hz
    let _ := c
    let _ := w
    let _ := hwpart
    let _ := hwker
    -- TODO: use the Cohen-ring form of Lemma `15.39.2` to quotient by the kernel parameter block,
    -- keeping the distinguished residue-characteristic parameter explicit, then finish as in the
    -- source proof by Proposition `15.40.5` and base change.
    sorry

/- Domain-style sampling for Lemma 15.40.6:
- primary domain: complete local commutative algebra, adic formal smoothness, and closed fibers of
  local maps;
- sampled owner declarations:
  * `Ideal.Fiber`,
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.formally_smooth_for_adic_baseChange`,
  * `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`;
- best owner abstraction: the closed fiber of the sought lift is canonically
  `Ideal.Fiber (maximalIdeal A) C`; the tensor-product model `ResidueField A ⊗[A] C` is only a
  bridge/view of that owner;
- primitive data: the complete local `ResidueField A`-algebra `B` and the adic formal smoothness
  hypothesis on `ResidueField A → B`;
- derived API: existence of a complete local `A`-algebra `C` whose structure map is adically
  formally smooth together with an explicit closed-fiber equivalence
  `Ideal.Fiber (maximalIdeal A) C ≃ₐ[ResidueField A] B`.

Source/core/bridge triage:
- `source-facing`: the existence of a formally smooth complete-local lift with prescribed closed
  fiber;
- `core/canonical`: `Ideal.Fiber` and `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-product presentation of the closed fiber.
-/
-- Proof sketch: choose the power-series presentation from Lemma `15.39.3` for the local map from a
-- Cohen ring or residue-field power series ring into `B`, then use regularity of the special
-- fiber to kill generators of the kernel so that the reduced presentation has special fiber
-- exactly `B`. Proposition `15.40.5` makes the resulting source formally smooth over the base
-- presentation ring, and Lemma `15.37.8` transports formal smoothness after base change along
-- the map to `A`.
/-- Lemma 15.40.6: if `A` is a Noetherian complete local ring and `B` is a Noetherian complete
local `ResidueField A`-algebra such that `ResidueField A → B` is formally smooth for the
`maximalIdeal B`-adic topology, then there exists a Noetherian complete local `A`-algebra `C`
whose structure map `A → C` is local and formally smooth for the `maximalIdeal C`-adic topology,
and whose closed fiber `Ideal.Fiber (maximalIdeal A) C`, canonically presented by
`ResidueField A ⊗[A] C`, is isomorphic to `B` over `ResidueField A`. -/
theorem exists_completeLocal_formallySmooth_lift_with_closedFiber
    (hfs : (algebraMap κA B).formally_smooth_for_adic (maximalIdeal B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C))
      (_ : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] B),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) := by
  -- First replace the problem by the source-faithful composite local map `A → κ(A) → B`.
  let f : A →+* B := residueCompositeToTarget (A := A) (B := B)
  have hf_local : IsLocalHom f := by
    -- The dedicated helper keeps the composite local-map setup explicit.
    simpa [f] using residueCompositeToTarget_isLocalHom (A := A) (B := B)
  -- Then isolate the mixed-universe presentation step coming from Lemma `15.39.3`.
  have hpres : HasPowerSeriesPresentation (A := A) (B := B) f := by
    -- Avoid broad simplification on the large presentation predicate and just unfold the local
    -- abbreviation `f`.
    change HasPowerSeriesPresentation (A := A) (B := B)
      (residueCompositeToTarget (A := A) (B := B))
    exact exists_powerSeries_presentation_of_residueCompositeToTarget (A := A) (B := B)
  -- Finally reduce to the kernel-killing and base-change part of the source proof while keeping
  -- the original formal-smoothness input available for the eventual `15.40.5` application.
  exact
    exists_completeLocal_formallySmooth_lift_of_regularTarget_and_powerSeriesPresentation
      (A := A) (B := B) hfs hpres

end
