import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [FinitePresentation R S]

/- Helper route map: first the maximal-ideal criterion gives unramifiedness at `q`.  The
flatness hypothesis is then used only after passing to the local map `R_p → S_q`; the
finite-presentation input is supplied by the base-change localization
`R_p ⊗[R] S ≃ S[p⁻¹]`. -/

/-- Helper for Chap10 Lemma 10 143 7: the separable residue-field extension and the displayed
maximal-ideal equality give local unramifiedness at `q`. -/
private lemma isUnramifiedAt_of_map_eq_maximalIdeal_of_isSeparableResidueField
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hmax : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q))
    [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    IsUnramifiedAt R q := by
  -- The owner criterion for local unramifiedness is exactly separability plus the supplied
  -- equality `p S_q = maximalIdeal S_q`.
  exact (Algebra.isUnramifiedAt_iff_map_eq R p q).2 ⟨inferInstance, hmax⟩

/-- Helper for Chap10 Lemma 10 143 7: the source prime localization base-changed to `S` is a
finite-presentation algebra over `R_p`. -/
private lemma finitePresentation_localizationAtPrime_to_localizedTarget
    (p : Ideal R) [p.IsPrime] :
    Algebra.FinitePresentation (Localization.AtPrime p)
      (Localization (algebraMapSubmonoid S p.primeCompl)) := by
  -- Base change preserves finite presentation, and the standard tensor-localization equivalence
  -- identifies the base change with the localization of `S` away from `p`.
  let e : TensorProduct R (Localization.AtPrime p) S ≃ₐ[Localization.AtPrime p]
      Localization (algebraMapSubmonoid S p.primeCompl) :=
    Localization.tensorRightAlgEquiv p.primeCompl S
  exact Algebra.FinitePresentation.equiv e

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 143 7: the maximal-ideal equality over `R` rewrites to the
corresponding equality for the localized local homomorphism `R_p → S_q`. -/
private lemma map_maximalIdeal_atPrime_eq_of_map_eq
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hmax : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q)) :
    Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
      (maximalIdeal (Localization.AtPrime p)) =
        maximalIdeal (Localization.AtPrime q) := by
  -- Replace the maximal ideal of `R_p` by the image of `p`, then compose the two localization
  -- maps to recover the maximal-ideal equality in the statement.
  calc
    Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
        (maximalIdeal (Localization.AtPrime p)) =
        Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
          (Ideal.map (algebraMap R (Localization.AtPrime p)) p) := by
          rw [Localization.AtPrime.map_eq_maximalIdeal]
    _ = Ideal.map (algebraMap R (Localization.AtPrime q)) p := by
          rw [Ideal.map_map]
          congr 1
          ext x
          exact (IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
            (Localization.AtPrime q) x).symm
    _ = maximalIdeal (Localization.AtPrime q) := hmax

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 143 7: flatness of the displayed localized ring homomorphism is
the same as module flatness of `S_q` over `R_p`. -/
private lemma moduleFlat_atPrime_of_localRingHom_flat
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hflat : (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).Flat) :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
  -- The ring-hom flatness predicate unfolds directly to flatness for the induced module
  -- structure on the localized target.
  simpa [RingHom.Flat] using hflat

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 143 7: elements of `S` coming from `R \ p` become units in
`S_q` when `q` lies over `p`. -/
private lemma localizedTargetToAtPrime_map_units
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∀ y : algebraMapSubmonoid S p.primeCompl,
      IsUnit ((Algebra.ofId S (Localization.AtPrime q)) y) := by
  -- Membership in `R \ p` transports across the lying-over equality to membership in
  -- `S \ q`, so the universal map into `S_q` sends it to a unit.
  rintro ⟨_, x, hx, rfl⟩
  have hxq : algebraMap R S x ∉ q := by
    simpa [q.over_def p] using hx
  exact IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q)
    ⟨algebraMap R S x, hxq⟩

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 143 7: the canonical map from `S[p⁻¹]` to `S_q`. -/
private noncomputable def localizedTargetToAtPrimeAlgHom
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Localization (algebraMapSubmonoid S p.primeCompl) →ₐ[S] Localization.AtPrime q :=
  IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
    (f := Algebra.ofId _ _) (localizedTargetToAtPrime_map_units (R := R) (S := S) p q)

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 143 7: after the canonical chart map, `S_q` is the localization
of `S[p⁻¹]` at the image of `S \ q`. -/
private lemma isLocalization_localizedTarget_to_atPrime
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
    let Sq := Localization.AtPrime q
    let f : Sp →ₐ[S] Sq := localizedTargetToAtPrimeAlgHom (R := R) (S := S) p q
    letI : Algebra Sp Sq := f.toAlgebra
    IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq := by
  -- The only set-theoretic point is the containment of the already inverted elements
  -- `S[p⁻¹]` into the elements inverted by localizing further at `q`.
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let f : Sp →ₐ[S] Sq := localizedTargetToAtPrimeAlgHom (R := R) (S := S) p q
  letI : Algebra Sp Sq := f.toAlgebra
  refine .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _ ?_
  rintro _ ⟨x, hx, rfl⟩
  simp_all [q.over_def p]

/-- Helper for Chap10 Lemma 10 143 7: formal smoothness of the closed fiber of
`R_p → S_q` upgrades, using local flatness and the finite-presentation chart, to formal
smoothness of the stalk `S_q` over `R`. -/
private lemma formallySmooth_atPrime_of_flat_localRingHom_of_formallySmooth_closedFiber
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hflat : (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).Flat)
    (hfiber : Algebra.FormallySmooth (ResidueField (Localization.AtPrime p))
      (TensorProduct (Localization.AtPrime p) (ResidueField (Localization.AtPrime p))
        (Localization.AtPrime q))) :
    Algebra.FormallySmooth R (Localization.AtPrime q) := by
  -- Cache the flatness of the displayed local hom before introducing the intermediate chart;
  -- this keeps the fiber criterion from searching through the chart algebra structure.
  have hflat' : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    moduleFlat_atPrime_of_localRingHom_flat (R := R) (S := S) p q hflat
  -- Use the standard chart `S[p⁻¹]` between `R_p` and `S_q`, exactly as in mathlib's smooth
  -- fiber criterion.
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let f : Sp →ₐ[S] Sq := localizedTargetToAtPrimeAlgHom (R := R) (S := S) p q
  algebraize [f.toRingHom]
  -- The chart and the target localization have the scalar-tower and localization instances
  -- required by `FormallySmooth.of_formallySmooth_residueField_tensor`.
  letI : Module.Flat Rp Sq := hflat'
  letI : Algebra.FormallySmooth (ResidueField Rp)
      (TensorProduct Rp (ResidueField Rp) Sq) := by
    simpa only [Rp, Sq] using hfiber
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    isLocalization_localizedTarget_to_atPrime (R := R) (S := S) p q
  have : FinitePresentation Rp Sp :=
    finitePresentation_localizationAtPrime_to_localizedTarget (R := R) (S := S) p
  -- The closed-fiber hypothesis now triggers the local flat fiber criterion, and composing with
  -- the localization `R → R_p` gives formal smoothness over the original base.
  have := FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 143 7: the displayed maximal-ideal equality and separability make
the closed fiber of `R_p → S_q` formally smooth. -/
private lemma formallySmooth_closedFiber_of_map_eq_maximalIdeal_of_isSeparableResidueField
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hmax : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q))
    [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    Algebra.FormallySmooth (ResidueField (Localization.AtPrime p))
      (TensorProduct (Localization.AtPrime p) (ResidueField (Localization.AtPrime p))
        (Localization.AtPrime q)) := by
  -- Route correction: the closed fiber is compared through the local-ring quotient
  -- `S_q / m_{R_p}S_q`, avoiding a direct prime-residue-field transport.
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  have hlocalMax : Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp) = maximalIdeal Sq := by
    exact map_maximalIdeal_atPrime_eq_of_map_eq (R := R) (S := S) p q hmax
  have hleMap : maximalIdeal Rp ≤ Ideal.comap (algebraMap Rp Sq)
      (Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)) := by
    intro x hx
    exact Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx)
  letI : Algebra (ResidueField Rp)
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)) :=
    Ideal.Quotient.algebraQuotientOfLEComap hleMap
  -- The maximal-ideal equality turns the quotient of `S_q` by `m_{R_p}S_q` into the residue
  -- field of `S_q`, compatibly with the `κ(p)`-algebra structures.
  let eRing :=
    (Ideal.quotientEquivAlgOfEq Rp hlocalMax).toRingEquiv
  have hcomm : ∀ x : ResidueField Rp,
      eRing
        (algebraMap (ResidueField Rp)
          (Sq ⧸ Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)) x) =
        algebraMap (ResidueField Rp) (ResidueField Sq) x := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  let e : (Sq ⧸ Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)) ≃ₐ[ResidueField Rp]
      ResidueField Sq :=
    AlgEquiv.ofRingEquiv (f := eRing) hcomm
  have hres : Algebra.FormallySmooth (ResidueField Rp) (ResidueField Sq) := by
    have : Algebra.FormallyEtale (ResidueField Rp) (ResidueField Sq) :=
      Algebra.FormallyEtale.of_isSeparable _ _
    exact inferInstance
  -- Transport formal smoothness back to the quotient model, then across the tensor-quotient
  -- equivalence `S_q / m_{R_p}S_q ≃ κ(p) ⊗[R_p] S_q`.
  have hquot : Algebra.FormallySmooth (ResidueField Rp)
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)) := by
    letI : Algebra.FormallySmooth (ResidueField Rp) (ResidueField Sq) := hres
    exact Algebra.FormallySmooth.of_equiv e.symm
  have hquot' : Algebra.FormallySmooth (Rp ⧸ maximalIdeal Rp)
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)) := by
    simpa only [IsLocalRing.ResidueField] using hquot
  letI : Algebra.FormallySmooth (Rp ⧸ maximalIdeal Rp)
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)) := hquot'
  have hsmooth := Algebra.FormallySmooth.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Sq (maximalIdeal Rp))
  simpa only [Rp, Sq, IsLocalRing.ResidueField] using hsmooth

/- Domain-style sampling:
- primary domain: local étaleness criteria for finitely presented ring maps;
- sampled owner declarations:
  `Algebra.IsEtaleAt`,
  `Algebra.IsUnramifiedAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `[Algebra.IsUnramifiedAt R q] → Module.Finite p.ResidueField q.ResidueField`,
  `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`,
  `Algebra.IsSmoothAt.of_formallySmooth_fiber`;
- best owner abstraction: `Algebra.IsEtaleAt R q` is the canonical local owner.

Source/core/bridge triage:
- `source-facing`: the Stacks local criterion for étaleness at `q`;
- `core/canonical`: the owner predicates `IsEtaleAt`, `IsUnramifiedAt`, and `IsSmoothAt`;
- `bridge/view`: the local flatness hypothesis together with the maximal-ideal equality and the
  separable residue-field extension.

Primitive data vs. derived API:
- primitive data: local flatness of `R_p → S_q`, the equality `pS_q = 𝔪_{S_q}`, and separability
  of `κ(q) / κ(p)`;
- derived API: local unramifiedness, finiteness of `κ(q) / κ(p)`, local smoothness, and hence
  local étaleness.

This file should keep the bridge theorem rather than collapse to the sampled owner theorem
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`, because that owner theorem assumes global
flatness `Module.Flat R S`, while the source statement only assumes flatness of the localized map
`R_p → S_q`.
-/
-- Proof sketch: use `Algebra.isUnramifiedAt_iff_map_eq` to deduce that `R → S` is unramified at
-- `q` from the equality `pS_q = 𝔪_{S_q}` and the separability of `κ(q) / κ(p)`. The flat-local
-- and finite-presentation hypotheses then give smoothness at `q` by the smooth-fiber criterion;
-- once unramifiedness is known, mathlib's local unramified API supplies the finiteness of
-- `κ(q) / κ(p)`, so the fiber identifies with a finite separable field extension. Combine
-- smoothness and unramifiedness to conclude étaleness at `q`.
/-- Chap10 Lemma 10 143 7: let `q` be a prime of `S` lying over a prime `p` of `R`. If `R → S` is of
finite presentation, the localized map `R_p → S_q` is flat, `p S_q` is the maximal ideal of the
local ring `S_q`, and the residue field extension `κ(q) / κ(p)` is separable, then `R → S` is
étale at `q`; the finiteness of `κ(q) / κ(p)` is automatic from these hypotheses. -/
@[stacks 00U6]
theorem isEtaleAt_of_flat_localRingHom_of_map_eq_maximalIdeal_of_separableResidueField
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hflat : (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).Flat)
    (hmax : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q))
    [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    IsEtaleAt R q := by
  -- First turn the residue-field and maximal-ideal data into formal unramifiedness at the stalk.
  have hunramified : IsUnramifiedAt R q :=
    isUnramifiedAt_of_map_eq_maximalIdeal_of_isSeparableResidueField
      (R := R) (S := S) p q hmax
  -- The remaining smooth part is supplied by the flat local map once the closed fiber is known to
  -- be formally smooth.
  have hfiber :
      Algebra.FormallySmooth (ResidueField (Localization.AtPrime p))
        (TensorProduct (Localization.AtPrime p) (ResidueField (Localization.AtPrime p))
          (Localization.AtPrime q)) :=
    formallySmooth_closedFiber_of_map_eq_maximalIdeal_of_isSeparableResidueField
      (R := R) (S := S) p q hmax
  have hsmooth : Algebra.FormallySmooth R (Localization.AtPrime q) :=
    formallySmooth_atPrime_of_flat_localRingHom_of_formallySmooth_closedFiber
      (R := R) (S := S) p q hflat hfiber
  -- Formal étaleness is formal unramifiedness plus formal smoothness at the same stalk.
  letI : Algebra.FormallyUnramified R (Localization.AtPrime q) := hunramified
  letI : Algebra.FormallySmooth R (Localization.AtPrime q) := hsmooth
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

end

end Algebra
