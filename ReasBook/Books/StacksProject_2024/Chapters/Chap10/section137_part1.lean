import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_137_1 (from Chap10) -/
universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
- primary domain: smooth commutative algebra maps and their cotangent-theoretic consequences;
- sampled owner declarations:
  `Algebra.Smooth`,
  `Algebra.Smooth.finitePresentation`,
  `Algebra.FormallySmooth.subsingleton_h1Cotangent`,
  `KaehlerDifferential.finite`;
- best owner abstraction: `Algebra.Smooth R S`;
- primitive data: the smoothness owner instance on the `R`-algebra `S`;
- derived API: finite presentation of `S`, vanishing of `H¹(L_{S/R})`, and projective/finite
  Kähler differentials.

This file is therefore a `core/canonical` recall file: it should reuse the owner declarations
directly and avoid any parallel local smoothness wrapper.
-/
/- Definition 10.137.1: a ring map `R → S` is smooth when the corresponding `R`-algebra `S` is
smooth, i.e. of finite presentation and with naive cotangent complex quasi-isomorphic to a finite
projective module concentrated in degree `0`. -/
recall Smooth

/- Smooth algebras are finitely presented over the base ring. -/
recall Smooth.finitePresentation

/- Smooth `R`-algebras have vanishing first homology of the naive cotangent complex. -/
recall FormallySmooth.subsingleton_h1Cotangent

/- Smooth `R`-algebras have projective Kähler differentials. -/
recall FormallySmooth.projective_kaehlerDifferential

section

variable [Smooth R S]

/- Smooth `R`-algebras have finite Kähler differentials. -/
recall KaehlerDifferential.finite

end

end Algebra

/-! ### Lemma_10_137_2 (from Chap10) -/
universe u v

/-
Domain-style sampling:
- primary domain: smooth commutative algebra maps and their behavior under source and target
  localization;
- sampled owner declarations:
  `Algebra.Smooth.comp`,
  `Algebra.Smooth.of_isLocalization_Away`,
  `RingHom.smooth_algebraMap`,
  `Algebra.TensorProduct.lidOfCompatibleSMul`;
- best owner abstraction: `Algebra.Smooth R S`, with `RingHom.Smooth` as the canonical ring-hom
  view of the induced localization map;
- primitive data: the commutative rings, the algebra structure `R → S`, the localization element,
  and the canonical source localization map `Localization.awayLift`;
- derived API: smoothness after localizing the target, and smoothness of the induced map from the
  source localization when the localized element already becomes a unit in `S`.

Source/core/bridge triage:
- `source-facing`: the two textbook localization lemmas;
- `core/canonical`: `Algebra.Smooth`, `RingHom.Smooth`, and smooth base change;
- `bridge/view`: `RingHom.smooth_algebraMap` and `Algebra.TensorProduct.lidOfCompatibleSMul`
  translate the canonical owner facts to the source-facing ring-hom statement.
-/

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: the localization map `S → S_g` is smooth by
-- `Algebra.Smooth.of_isLocalization_Away`, and smoothness is stable under composition.
/-- Lemma 10.137.2 (1): if `R → S` is smooth, then every localization `S_g` is smooth over `R`. -/
theorem smooth_localization_away_target [Smooth R S] (g : S) :
    Smooth R (Localization.Away g) := by
  letI : Smooth S (Localization.Away g) := Smooth.of_isLocalization_Away g
  exact Smooth.comp R S (Localization.Away g)

-- Proof sketch: the induced map `R_f → S` is the localization map obtained from the fact that the
-- image of `f` is a unit in `S`; use the locality of smoothness with respect to localization on
-- the source.
/-- Lemma 10.137.2 (2): if `f ∈ R` maps to a unit in `S`, then the induced map `R_f → S` is
smooth. -/
theorem smooth_away_lift_of_isUnit [Smooth R S] (f : R) (hf : IsUnit (algebraMap R S f)) :
    RingHom.Smooth (Localization.awayLift (algebraMap R S) f hf) := by
  letI : Algebra (Localization.Away f) S :=
    (Localization.awayLift (algebraMap R S) f hf).toAlgebra
  have hcomp :
      (Localization.awayLift (algebraMap R S) f hf).comp (algebraMap R (Localization.Away f)) =
        algebraMap R S := by
    ext x
    simp [Localization.awayLift]
  letI : IsScalarTower R (Localization.Away f) S := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let e := Algebra.TensorProduct.lidOfCompatibleSMul R (Localization.Away f) S
  have hsmooth : Smooth (Localization.Away f) S := Smooth.of_equiv e
  exact (RingHom.smooth_algebraMap).2 hsmooth

end Algebra

/-! ### Lemma_10_137_3 (from Chap10) -/
/- Lemma 10.137.3: if `R → S` is smooth, then for any ring map `R → R'`, the base change
`R' → R' ⊗[R] S` is again smooth. -/
recall Algebra.Smooth.baseChange

/-! ### Lemma_10_137_4 (from Chap10) -/
universe u v

namespace Algebra

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

namespace IsRelativeGlobalCompleteIntersection

/-- Over a field, a relative global complete intersection is already a global complete
intersection. -/
theorem isGlobalCompleteIntersection (hS : IsRelativeGlobalCompleteIntersection k S) :
    IsGlobalCompleteIntersection k S := by
  by_cases hsub : Subsingleton S
  · let _ : Subsingleton S := hsub
    infer_instance
  · letI : Nontrivial S := not_subsingleton_iff_nontrivial.mp hsub
    rcases hS.exists_presentation with ⟨n, c, P, hP⟩
    let p : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
    let φ : k →ₐ[k] p.asIdeal.ResidueField := IsScalarTower.toAlgHom k k p.asIdeal.ResidueField
    have hκ : Function.Bijective φ := by
      constructor
      · exact RingHom.injective _
      · simpa [p] using (Ideal.algebraMap_residueField_surjective (⊥ : Ideal k))
    let eκ : p.asIdeal.ResidueField ≃ₐ[k] k :=
      (AlgEquiv.ofBijective φ hκ).symm
    let e : p.asIdeal.Fiber S ≃ₐ[k] S :=
      (Algebra.TensorProduct.congr eκ (AlgEquiv.refl : S ≃ₐ[k] S)).trans
        (Algebra.TensorProduct.lid k S)
    have hp : ringKrullDim (p.asIdeal.Fiber S) = P.dimension := by
      letI : Nontrivial (p.asIdeal.Fiber S) := e.toRingHom.domain_nontrivial
      exact hP p inferInstance
    refine ⟨Or.inr ⟨n, c, P, ?_⟩⟩
    calc
      ringKrullDim S = ringKrullDim (p.asIdeal.Fiber S) := by
        simpa using (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
      _ = P.dimension := hp

end IsRelativeGlobalCompleteIntersection

-- Proof sketch: use the canonical smooth basic-open cover by standard smooth localizations.
-- Lemma `10.137.6` makes each standard smooth chart a relative global complete intersection, and
-- over a field that owner specializes to a global complete intersection. Packaging the resulting
-- finite cover gives the source-facing local complete intersection owner.
/-- Lemma 10.137.4: every smooth `k`-algebra is a local complete intersection over `k`. -/
instance smooth_isLocalCompleteIntersection [Smooth k S] :
    IsLocalCompleteIntersection k S := by
  obtain ⟨s, hsone, hsstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth k S
  obtain ⟨t, hts, htone⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
  refine ⟨t, htone, ?_⟩
  intro g hg
  let _ : IsStandardSmooth k (Localization.Away g) := hsstd g (hts hg)
  let _ : IsRelativeGlobalCompleteIntersection k (Localization.Away g) :=
    IsStandardSmooth.isRelativeGlobalCompleteIntersection inferInstance
  exact IsRelativeGlobalCompleteIntersection.isGlobalCompleteIntersection inferInstance

end Algebra

/-! ### Definition_10_137_5 (from Chap10) -/
namespace Algebra

/- Definition 10.137.5: a standard smooth `R`-algebra is the canonical notion
`Algebra.IsStandardSmooth`; it is presented by a quotient of a polynomial algebra by finitely many
relations together with an invertible Jacobian determinant in the quotient. -/
recall IsStandardSmooth

/- A submersive presentation packages the quotient presentation and Jacobian-unit condition used in
the definition of a standard smooth algebra. -/
recall SubmersivePresentation

end Algebra

namespace RingHom

/- Standard smoothness for a ring map is the ring-hom version of the same canonical notion. -/
recall IsStandardSmooth

/- For an algebra map, ring-hom standard smoothness agrees with algebra standard smoothness. -/
recall isStandardSmooth_algebraMap

end RingHom

/-! ### Lemma_10_137_6 (from Chap10) -/
open scoped TensorProduct

universe u v w x

namespace Algebra

section Generic

variable {R : Type u} {R' : Type v} {Rf : Type w} {S : Type x} {Sg : Type x}
variable [CommRing R] [CommRing R'] [CommRing Rf] [CommRing S] [CommRing Sg]
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: standard smooth `R`-algebras and their canonical stability/smoothness API;
- sampled owner declarations:
  `RingHom.IsStandardSmooth.smooth`,
  `Algebra.IsStandardSmooth.baseChange`,
  `Algebra.IsStandardSmooth.localization_away`,
  `SubmersivePresentation.basisKaehler`,
  `SubmersivePresentation.basisCotangent`;
- best owner abstraction: `Algebra.IsStandardSmooth R S`;
- primitive data: a submersive presentation witnessing standard smoothness;
- derived API: smoothness, localization/base-change stability, cotangent bases, and the relative
  global complete intersection bridge.
-/

/- Lemma 10.137.6 (1): a standard smooth `R`-algebra is smooth over `R`. This is exactly the
canonical theorem `RingHom.IsStandardSmooth.smooth`, specialized to `algebraMap R S`. -/
recall RingHom.IsStandardSmooth.smooth

-- Proof sketch: localize `S` away from `g`; the localization map `S → S_g` is standard smooth of
-- relative dimension `0`, and composition of standard smooth maps preserves standard smoothness.
namespace IsStandardSmooth

/-- Lemma 10.137.6 (2): for any `g : S`, any away-localization `Sg` of `S` at `g` is again
standard smooth over `R`. -/
theorem localizationAway (hS : IsStandardSmooth R S) (g : S) [Algebra R Sg] [Algebra S Sg]
    [IsScalarTower R S Sg] [IsLocalization.Away g Sg] :
    IsStandardSmooth R Sg := by
  letI := hS
  letI : IsStandardSmooth S Sg := Algebra.IsStandardSmooth.localization_away g
  exact Algebra.IsStandardSmooth.trans R S Sg

end IsStandardSmooth

/- Lemma 10.137.6 (3): for any ring map `R → R'`, the base change `R' → R' ⊗[R] S` is standard
smooth. This is exactly the canonical base-change instance
`Algebra.IsStandardSmooth.baseChange`. -/
recall Algebra.IsStandardSmooth.baseChange

variable [Algebra R Rf] [Algebra Rf S] [IsScalarTower R Rf S]

-- Proof sketch: because `S` is already an `R_f`-algebra, the image of `f` is automatically a
-- unit in `S`. Base changing the standard smooth `R`-algebra `S` along `R → R_f` yields the
-- standard smooth `R_f`-algebra `R_f ⊗[R] S`, and the canonical tensor-localization
-- identification plus the fact that localizing `S` away from a unit does nothing gives an
-- `R_f`-algebra isomorphism `R_f ⊗[R] S ≃ₐ[R_f] S`.
namespace IsStandardSmooth

/-- Lemma 10.137.6 (4): if `f : R` maps to a unit in `S`, then after localizing `R` away from
`f`, the induced map `R_f → S` is standard smooth. -/
theorem of_isUnit_base
    (hS : IsStandardSmooth R S) {f : R} [IsLocalization.Away f Rf] :
    IsStandardSmooth Rf S := by
  letI := hS
  let hu : IsUnit (algebraMap R S f) := by
    rw [show algebraMap R S f = algebraMap Rf S (algebraMap R Rf f) by
      rw [IsScalarTower.algebraMap_apply R Rf S]]
    exact (IsLocalization.Away.algebraMap_isUnit f).map (algebraMap Rf S)
  letI : IsLocalization.Away (algebraMap R S f) S :=
    IsLocalization.away_of_isUnit_of_bijective S hu Function.bijective_id
  letI : Algebra S (Rf ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let eu : S ≃ₐ[S] Localization.Away (algebraMap R S f) :=
    IsLocalization.atUnit S (Localization.Away (algebraMap R S f)) (algebraMap R S f) hu
  let eS : Rf ⊗[R] S ≃ₐ[S] S :=
    (IsLocalization.Away.tensorRightEquiv S f Rf).trans eu.symm
  have hcomm : (eS : Rf ⊗[R] S →+* S).comp (algebraMap Rf (Rf ⊗[R] S)) = algebraMap Rf S := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    change eS (algebraMap Rf (Rf ⊗[R] S) (algebraMap R Rf r)) = algebraMap Rf S (algebraMap R Rf r)
    rw [← IsScalarTower.algebraMap_apply R Rf (Rf ⊗[R] S), ← IsScalarTower.algebraMap_apply R Rf S]
    have hmap : algebraMap R (Rf ⊗[R] S) r = algebraMap S (Rf ⊗[R] S) (algebraMap R S r) :=
      IsScalarTower.algebraMap_apply R S (Rf ⊗[R] S) r
    rw [hmap]
    exact eS.commutes _
  let e : Rf ⊗[R] S ≃ₐ[Rf] S :=
    { __ := eS.toRingEquiv
      commutes' := by
        intro x
        exact RingHom.ext_iff.mp hcomm x }
  letI : IsStandardSmooth Rf (Rf ⊗[R] S) := inferInstance
  exact IsStandardSmooth.of_algEquiv e

-- Proof sketch: after base change to each residue field `κ(p)`, clause (5) reduces the statement
-- to the field case. There the standard smooth algebra is a local complete intersection, and the
-- cotangent and conormal freeness from clauses (2) and (3) give the expected fiber dimension,
-- which is exactly the relative global complete intersection condition.
/-- Lemma 10.137.6 (5): a standard smooth `R`-algebra is a relative global complete
intersection over `R`. -/
theorem isRelativeGlobalCompleteIntersection (hS : IsStandardSmooth R S) :
    IsRelativeGlobalCompleteIntersection R S := sorry

end IsStandardSmooth

end Generic

section Presentation

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Finite σ]
variable (P : SubmersivePresentation R S ι σ)

/- For a standard smooth presentation `P`, the canonical basis
`P.basisKaehler` exhibits `Ω[S⁄R]` as free on the images of the differentials `dxᵢ` indexed by
the complement of `P.map`; this is the library-facing form of the basis
`dx_{c + 1}, …, dx_n`. -/
#check P.basisKaehler

/- For a standard smooth presentation `P`, the canonical basis
`P.basisCotangent` exhibits `I/I²` as free on the classes of the defining relations `P.relation`;
this is the library-facing form of the basis given by the classes of `f₁, …, f_c`. -/
#check P.basisCotangent

end Presentation

end Algebra

/-! ### Example_10_137_7 (from Chap10) -/
open MvPolynomial

attribute [local instance high] Semiring.toModule Algebra.toModule

universe u

namespace Algebra

variable (R : Type u) [CommRing R]

/-- The original variables `x₁, …, x_c, x_{c+1}, …, x_n` occurring in the equations `fᵢ`. -/
abbrev SmoothExampleBaseVars (c m : ℕ) : Type := Sum (Fin c) (Fin m)

/-- The reordered variables `x₁, …, x_c, x_{n+1}, x_{c+1}, …, x_n`. -/
abbrev SmoothExampleVars (c m : ℕ) : Type := Sum (Fin c) (Sum Unit (Fin m))

/-- The relation indices `f₁, …, f_c` together with the inverse-Jacobian relation. -/
abbrev SmoothExampleRelations (c : ℕ) : Type := Sum (Fin c) Unit

/-- The new variable `x_{n + 1}` adjoining an inverse to the Jacobian determinant. -/
abbrev smoothExampleInverseVar (c m : ℕ) : SmoothExampleVars c m := Sum.inr (Sum.inl ())

/-- The inclusion of the original variables into the reordered variable set, skipping the new
inverse-Jacobian variable. -/
def smoothExampleBaseVarInclusion (c m : ℕ) :
    SmoothExampleBaseVars c m → SmoothExampleVars c m
  | Sum.inl i => Sum.inl i
  | Sum.inr i => Sum.inr (Sum.inr i)

/-- The Jacobian determinant of `f₁, …, f_c` with respect to the first `c` variables. -/
noncomputable def smoothExampleJacobian (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    MvPolynomial (SmoothExampleBaseVars c m) R :=
  Matrix.det fun i j ↦ MvPolynomial.pderiv (Sum.inl i) (f j)

/-- The reordered defining relations `f₁, …, f_c, h`, where `h` expresses that the new variable is
an inverse to the Jacobian determinant. -/
noncomputable def smoothExampleRelation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SmoothExampleRelations c → MvPolynomial (SmoothExampleVars c m) R
  | Sum.inl i => rename (smoothExampleBaseVarInclusion c m) (f i)
  | Sum.inr _ =>
      rename (smoothExampleBaseVarInclusion c m) (smoothExampleJacobian R c m f) *
        X (smoothExampleInverseVar c m) - 1

/-- The explicit quotient ring from Example 10.137.7. -/
noncomputable abbrev smoothExampleQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) : Type u :=
  MvPolynomial (SmoothExampleVars c m) R ⧸
    Ideal.span (Set.range (smoothExampleRelation R c m f))

/-- The inverse permutation sending the source-facing variable order to the canonical composition
order where the localization variable comes first. -/
private def smoothExampleVarEquiv (c m : ℕ) :
    SmoothExampleVars c m ≃ Sum Unit (SmoothExampleBaseVars c m) where
  toFun
    | Sum.inl i => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inl u) => Sum.inl u
    | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl u => Sum.inr (Sum.inl u)
    | Sum.inr (Sum.inl i) => Sum.inl i
    | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr i)
  left_inv := by
    intro x
    cases x with
    | inl i => rfl
    | inr x =>
        cases x with
        | inl u => rfl
        | inr i => rfl
  right_inv := by
    intro x
    cases x with
    | inl u => rfl
    | inr x =>
        cases x with
        | inl i => rfl
        | inr i => rfl

/-- The inverse permutation sending the source-facing relation order `(f₁, …, f_c, h)` to the
canonical composition order `(h, f₁, …, f_c)`. -/
private def smoothExampleRelEquiv (c : ℕ) :
    SmoothExampleRelations c ≃ Sum Unit (Fin c) :=
  Equiv.sumComm (Fin c) Unit

/-- The quotient by the equations `f₁, …, f_c` before adjoining the inverse Jacobian variable. -/
private noncomputable abbrev smoothExampleBaseQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) : Type u :=
  MvPolynomial (SmoothExampleBaseVars c m) R ⧸ Ideal.span (Set.range f)

/-- The canonical pre-submersive presentation of the quotient by `f₁, …, f_c`, using the first
`c` variables to compute the Jacobian. -/
private noncomputable abbrev smoothExampleBasePresentation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    PreSubmersivePresentation R (smoothExampleBaseQuotient R c m f)
      (SmoothExampleBaseVars c m) (Fin c) :=
  PreSubmersivePresentation.naive Sum.inl Sum.inl_injective

/-- The canonical localized submersive presentation obtained by adjoining an inverse to the
Jacobian determinant in the quotient by `f₁, …, f_c`, then reordering variables and relations into
the source-facing order. -/
private noncomputable def smoothExampleRawPresentation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SubmersivePresentation R
      (Localization.Away (smoothExampleBasePresentation R c m f).jacobian)
      (SmoothExampleVars c m) (SmoothExampleRelations c) := by
  let P := smoothExampleBasePresentation R c m f
  letI : Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f) :=
    Semiring.toModule
  letI : DistribMulAction (smoothExampleBaseQuotient R c m f)
      (smoothExampleBaseQuotient R c m f) :=
    { (Semiring.toModule :
        Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f)) with }
  let Q :
      SubmersivePresentation
        (smoothExampleBaseQuotient R c m f)
        (Localization.Away P.jacobian) Unit Unit :=
    SubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian
  let PQ :
      SubmersivePresentation R (Localization.Away P.jacobian)
        (Sum Unit (SmoothExampleBaseVars c m)) (Sum Unit (Fin c)) :=
    { toPreSubmersivePresentation :=
        PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P
      jacobian_isUnit := by
        have hP :
            IsUnit
              (algebraMap (smoothExampleBaseQuotient R c m f) (Localization.Away P.jacobian)
                P.jacobian) :=
          IsLocalization.map_units _ (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
        have hQ :
            IsUnit
              ((algebraMap (smoothExampleBaseQuotient R c m f) (Localization.Away P.jacobian)
                  P.jacobian) * Q.jacobian) :=
          hP.mul Q.jacobian_isUnit
        change IsUnit
          (PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P).jacobian
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def]
        exact hQ }
  simpa [P] using PQ.reindex (smoothExampleVarEquiv c m) (smoothExampleRelEquiv c)

/-- The polynomial map sending the original variables to their images in the explicit reordered
quotient. -/
private noncomputable def smoothExampleBaseToQuotientPolynomial (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    MvPolynomial (SmoothExampleBaseVars c m) R →ₐ[R] smoothExampleQuotient R c m f :=
  aeval fun i ↦ Ideal.Quotient.mk _ (X (smoothExampleBaseVarInclusion c m i))

private lemma smoothExampleBaseToQuotientPolynomial_mem (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    ∀ p : MvPolynomial (SmoothExampleBaseVars c m) R,
      p ∈ Ideal.span (Set.range f) →
        smoothExampleBaseToQuotientPolynomial R c m f p = 0 := by
  sorry

/-- The canonical map from the base quotient by `f₁, …, f_c` to the explicit quotient of Example
10.137.7. -/
private noncomputable def smoothExampleBaseToQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseQuotient R c m f →ₐ[R] smoothExampleQuotient R c m f :=
  Ideal.Quotient.liftₐ _ (smoothExampleBaseToQuotientPolynomial R c m f)
    (smoothExampleBaseToQuotientPolynomial_mem R c m f)

private lemma smoothExampleBaseToQuotient_apply_mk (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R)
    (p : MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseToQuotient R c m f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename (smoothExampleBaseVarInclusion c m) p) := by
  sorry

private noncomputable abbrev smoothExampleBaseJacobianClass (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseQuotient R c m f :=
  algebraMap _ _ (smoothExampleJacobian R c m f)

private noncomputable abbrev smoothExampleInverseVarClass (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleQuotient R c m f :=
  Ideal.Quotient.mk _ (X (smoothExampleInverseVar c m))

private lemma smoothExampleBaseToQuotient_jacobian_mul_inverseVar (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseToQuotient R c m f (smoothExampleBaseJacobianClass R c m f) *
      smoothExampleInverseVarClass R c m f = 1 := by
  sorry

private lemma smoothExampleBaseJacobian_isUnit_in_quotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    IsUnit (smoothExampleBaseToQuotient R c m f (smoothExampleBaseJacobianClass R c m f)) := by
  sorry

/-- The canonical algebra map from the quotient by `f₁, …, f_c` to its localization away from the
Jacobian class. -/
private noncomputable def smoothExampleBaseToLocalization (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseQuotient R c m f →ₐ[R]
      Localization.Away (smoothExampleBaseJacobianClass R c m f) where
  toRingHom := algebraMap _ _
  commutes' r := by
    letI : Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f) :=
      Semiring.toModule
    letI : DistribMulAction (smoothExampleBaseQuotient R c m f)
        (smoothExampleBaseQuotient R c m f) :=
      { (Semiring.toModule :
          Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f)) with }
    exact
    IsScalarTower.algebraMap_apply R
      (smoothExampleBaseQuotient R c m f)
      (Localization.Away (smoothExampleBaseJacobianClass R c m f)) r

/-- The canonical map from the localization away from the Jacobian class to the explicit quotient
of Example 10.137.7. -/
private noncomputable def smoothExampleLocalizationToQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    Localization.Away (smoothExampleBaseJacobianClass R c m f) →ₐ[R]
      smoothExampleQuotient R c m f where
  toRingHom :=
    Localization.awayLift (smoothExampleBaseToQuotient R c m f).toRingHom
      (smoothExampleBaseJacobianClass R c m f)
      (smoothExampleBaseJacobian_isUnit_in_quotient R c m f)
  commutes' r := by
    change
      Localization.awayLift (smoothExampleBaseToQuotient R c m f).toRingHom
        (smoothExampleBaseJacobianClass R c m f)
        (smoothExampleBaseJacobian_isUnit_in_quotient R c m f)
        (algebraMap _ _ (algebraMap R (smoothExampleBaseQuotient R c m f) r)) = _
    rw [← RingHom.comp_apply]
    rw [IsLocalization.Away.lift_comp]
    exact (smoothExampleBaseToQuotient R c m f).commutes r

private lemma smoothExampleLocalizationToQuotient_comp_base (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleLocalizationToQuotient R c m f).comp
      (smoothExampleBaseToLocalization R c m f) =
      smoothExampleBaseToQuotient R c m f := by
  sorry

private noncomputable def smoothExampleQuotientToLocalizationVar (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SmoothExampleVars c m →
      Localization.Away (smoothExampleBaseJacobianClass R c m f)
  | Sum.inl i =>
      algebraMap (smoothExampleBaseQuotient R c m f)
        (Localization.Away (smoothExampleBaseJacobianClass R c m f))
        (Ideal.Quotient.mk _ (X (Sum.inl i)))
  | Sum.inr (Sum.inl _) =>
      IsLocalization.Away.invSelf (smoothExampleBaseJacobianClass R c m f)
  | Sum.inr (Sum.inr i) =>
      algebraMap (smoothExampleBaseQuotient R c m f)
        (Localization.Away (smoothExampleBaseJacobianClass R c m f))
        (Ideal.Quotient.mk _ (X (Sum.inr i)))

/-- The polynomial map defining the comparison from the explicit quotient to the localization away
from the Jacobian class. -/
private noncomputable def smoothExampleQuotientToLocalizationPolynomial (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    MvPolynomial (SmoothExampleVars c m) R →ₐ[R]
      Localization.Away (smoothExampleBaseJacobianClass R c m f) :=
  aeval (smoothExampleQuotientToLocalizationVar R c m f)

private lemma smoothExampleQuotientToLocalizationPolynomial_mem (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    ∀ p : MvPolynomial (SmoothExampleVars c m) R,
      p ∈ Ideal.span (Set.range (smoothExampleRelation R c m f)) →
        smoothExampleQuotientToLocalizationPolynomial R c m f p = 0 := by
  sorry

/-- The canonical map from the explicit quotient of Example 10.137.7 to the localization away from
the Jacobian class in the base quotient. -/
private noncomputable def smoothExampleQuotientToLocalization (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleQuotient R c m f →ₐ[R]
      Localization.Away (smoothExampleBaseJacobianClass R c m f) :=
  Ideal.Quotient.liftₐ _ (smoothExampleQuotientToLocalizationPolynomial R c m f)
    (smoothExampleQuotientToLocalizationPolynomial_mem R c m f)

private lemma smoothExampleQuotientToLocalization_apply_mk (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R)
    (p : MvPolynomial (SmoothExampleVars c m) R) :
    smoothExampleQuotientToLocalization R c m f (Ideal.Quotient.mk _ p) =
      smoothExampleQuotientToLocalizationPolynomial R c m f p := by
  sorry

private lemma smoothExampleQuotientToLocalization_comp_baseToQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleQuotientToLocalization R c m f).comp
      (smoothExampleBaseToQuotient R c m f) =
      smoothExampleBaseToLocalization R c m f := by
  sorry

private lemma smoothExampleLocalizationToQuotient_invSelf (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleLocalizationToQuotient R c m f
        (IsLocalization.Away.invSelf (smoothExampleBaseJacobianClass R c m f)) =
      smoothExampleInverseVarClass R c m f := by
  sorry

private lemma smoothExampleLocalization_quotient_roundtrip (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleQuotientToLocalization R c m f).comp
      (smoothExampleLocalizationToQuotient R c m f) =
      AlgHom.id R _ := by
  sorry

private lemma smoothExampleQuotient_localization_roundtrip (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleLocalizationToQuotient R c m f).comp
      (smoothExampleQuotientToLocalization R c m f) =
      AlgHom.id R _ := by
  sorry

private noncomputable def smoothExampleLocalizationEquiv (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    Localization.Away (smoothExampleBaseJacobianClass R c m f) ≃ₐ[R]
      smoothExampleQuotient R c m f :=
  AlgEquiv.ofAlgHom
    (smoothExampleLocalizationToQuotient R c m f)
    (smoothExampleQuotientToLocalization R c m f)
    (smoothExampleQuotient_localization_roundtrip R c m f)
    (smoothExampleLocalization_quotient_roundtrip R c m f)

private lemma smoothExampleBasePresentation_jacobian (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleBasePresentation R c m f).jacobian =
      smoothExampleBaseJacobianClass R c m f := by
  sorry

/-- The submersive presentation on the explicit quotient model of Example 10.137.7. -/
private noncomputable def smoothExamplePresentation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SubmersivePresentation R (smoothExampleQuotient R c m f)
      (SmoothExampleVars c m) (SmoothExampleRelations c) :=
  let P :
      SubmersivePresentation R
        (Localization.Away (smoothExampleBaseJacobianClass R c m f))
        (SmoothExampleVars c m) (SmoothExampleRelations c) := by
      exact (smoothExampleBasePresentation_jacobian R c m f) ▸
        smoothExampleRawPresentation R c m f
  P.ofAlgEquiv (smoothExampleLocalizationEquiv R c m f)

-- Proof sketch: start from the canonical pre-submersive presentation of
-- `R[x₁, …, x_n] / (f₁, …, f_c)`, localize away its Jacobian determinant, and then transport the
-- resulting submersive presentation to the explicit reordered quotient by its quotient equivalence.
/-- Example 10.137.7: after ordering the variables as `x₁, …, x_c, x_{n+1}, x_{c+1}, …, x_n`,
the quotient by `f₁, …, f_c` and the inverse-Jacobian relation is a standard smooth `R`-algebra.
-/
theorem jacobian_inverted_quotient_isStandardSmooth (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    IsStandardSmooth R
      (MvPolynomial (SmoothExampleVars c m) R ⧸
        Ideal.span (Set.range (smoothExampleRelation R c m f))) := by
  simpa [smoothExampleQuotient] using
    (smoothExamplePresentation R c m f).isStandardSmooth

end Algebra

/-! ### Lemma_10_137_8 (from Chap10) -/
/- Lemma 10.137.8: the composition of two standard smooth ring maps is standard smooth. This is
exactly the canonical theorem `RingHom.IsStandardSmooth.comp`. -/
recall RingHom.IsStandardSmooth.comp

/-! ### Lemma_10_137_9 (from Chap10) -/
/- Lemma 10.137.9: if `R → S` is smooth, then `Spec S` admits a standard-open cover by
basic opens `D(g)` such that each localization `S[1 / g]` is standard smooth over `R`. This is
exactly the canonical theorem `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`. -/
recall Algebra.Smooth.exists_span_eq_top_isStandardSmooth

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: smooth and syntomic morphisms in commutative algebra, localized on standard-open
  charts and tested fiberwise over residue fields;
- sampled owner declarations:
  `RingHom.smooth_algebraMap`,
  `RingHom.Smooth.flat`,
  `RingHom.Smooth.finitePresentation`,
  `Algebra.Smooth.baseChange`,
  `Algebra.smooth_isLocalCompleteIntersection`;
- best owner abstraction:
  `RingHom.Syntomic` is the canonical owner on the conclusion side, and its primitive fields are
  supplied directly from the owner `Smooth R S` together with the fiberwise smooth-to-local-
  complete-intersection bridge over fields;
- primitive vs. derived:
  the primitive source hypothesis is `[Smooth R S]`; ring-hom smoothness, flatness, finite
  presentation, and the local complete intersection property of the fibers are all derived API
  from the sampled owners and should not be repackaged locally.

Source/core/bridge triage:
- `source-facing`: the bridge theorem that a smooth ring map is syntomic;
- `core/canonical`: `RingHom.Syntomic`;
- `bridge/view`: the ring-hom smoothness view of `[Smooth R S]`, its flatness and finite-
  presentation projections, and the fiberwise base-change view reducing the last field to
  `Algebra.smooth_isLocalCompleteIntersection`.
-/

open PrimeSpectrum

-- Proof sketch: reinterpret `[Smooth R S]` as the ring-hom owner on `algebraMap R S`, whose
-- canonical projections provide flatness and finite presentation. For each prime `p` of `R`, the
-- fiber `κ(p) ⊗[R] S` is smooth over the field `κ(p)` by `Algebra.Smooth.baseChange`, hence a
-- local complete intersection by Lemma `10.137.4`.
/-- A smooth ring map `R → S` is syntomic. -/
theorem smooth_syntomic [Smooth R S] :
    (algebraMap R S).Syntomic := by
  let hsmooth : (algebraMap R S).Smooth := (RingHom.smooth_algebraMap).2 inferInstance
  refine ⟨hsmooth.flat, hsmooth.finitePresentation, ?_⟩
  let _ : Algebra R S := (algebraMap R S).toAlgebra
  let _ : Smooth R S := (RingHom.smooth_algebraMap).1 hsmooth
  intro p
  let _ : Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  exact inferInstance

end Algebra

/-! ### Definition_10_137_10 (from Chap10) -/
universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.137.10: the source-facing Stacks condition that `R → S` is smooth at the prime
`q`, meaning that some basic open neighborhood `S_g` with `g ∉ q` is smooth over `R`. -/
def SmoothAtPrime (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Smooth R (Localization.Away g)

-- Proof sketch: if `S_g` is smooth over `R` for some `g ∉ q`, then localizing further at the
-- prime corresponding to `q` gives `S_q`, so `S_q` is formally smooth over `R`. Conversely, for a
-- finitely presented `R`-algebra, mathlib's theorem `Algebra.IsSmoothAt.exists_notMem_smooth`
-- produces such a neighborhood from the formal smoothness of `S_q`.
/-- For finitely presented algebras, the source-facing condition `SmoothAtPrime R S q` is
equivalent to the canonical owner predicate `IsSmoothAt R q.asIdeal`. -/
theorem smoothAtPrime_iff_isSmoothAt [FinitePresentation R S] (q : PrimeSpectrum S) :
    SmoothAtPrime R S q ↔ IsSmoothAt R q.asIdeal := sorry

end Algebra

/-! ### Lemma_10_137_11 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling for the local smoothness criterion:
- primary domain: commutative algebra of smooth ring maps, localized cotangent homology, and
  localized Kähler differentials at a prime;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.smoothLocus_eq_compl_support_inter`,
  `Module.free_of_flat_of_isLocalRing`,
  `module_finite_projective_iff_finitePresentation_and_flat`;
- best owner abstraction: the source-facing owner at this stage is `Algebra.SmoothAtPrime`,
  with `Algebra.IsSmoothAt` used only as the canonical local bridge;
- primitive data: the prime `q`, the local ring `S_q`, the localized cotangent homology, and the
  localized module of Kähler differentials;
- derived API: the finite-free/projective/flat reformulations of the same localized criterion.

Source/core/bridge triage:
- `source-facing`: the textbook `List.TFAE` statement with first clause `SmoothAtPrime R S q`;
- `core/canonical`: `Algebra.IsSmoothAt`, the localized cotangent-homology support criterion, and
  the local-ring projective/free criterion;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt`, used internally to pass from the source-facing
  predicate to the canonical local owner.

This file remains `source-facing`: it keeps the textbook `List.TFAE` packaging while exposing the
canonical local criterion only through a private bridge theorem.
-/

variable [FinitePresentation R S]

section

variable (q : PrimeSpectrum S)

local notation "S₍q₎" => Localization.AtPrime q.asIdeal
local notation "H¹₍q₎" => LocalizedModule.AtPrime q.asIdeal (H1Cotangent R S)
local notation "Ω₍q₎" => LocalizedModule.AtPrime q.asIdeal Ω[S⁄R]

private theorem isSmoothAt_iff_subsingleton_localizedH1Cotangent_and_localizedKaehler_free
    :
    IsSmoothAt R q.asIdeal ↔
      Subsingleton H¹₍q₎ ∧
        Module.Free S₍q₎ Ω₍q₎ := by
  sorry

-- Proof sketch: use `Algebra.smoothLocus_eq_compl_support_inter` to identify `IsSmoothAt R q.asIdeal`
-- with vanishing of the localized cotangent homology and freeness of the localized Kähler
-- differentials. Since `R → S` is finitely presented, `Ω[S⁄R]` is finitely presented over `S`, so
-- after localizing at `q` the local module criterion for finite projective modules identifies the
-- finite-free, projective, and flat clauses over the local ring `S_q`.
/-- Lemma 10.137.11: for a finitely presented ring map `R → S` and a prime `q` of `S`, the
following are equivalent: `R → S` is smooth at `q` in the source-facing sense `SmoothAtPrime R S q`;
the localized first cotangent homology `H¹(L_{S/R})_q` vanishes and the localized module of Kähler
differentials `Ω[S⁄R]_q` is finite free over `S_q`; `H¹(L_{S/R})_q` vanishes and `Ω[S⁄R]_q` is
projective over `S_q`; and `H¹(L_{S/R})_q` vanishes and `Ω[S⁄R]_q` is flat over `S_q`. -/
theorem smoothAtPrime_tfae_subsingleton_localizedH1Cotangent_and_localizedKaehler_finiteFree_projective_flat
    :
    List.TFAE
      [ SmoothAtPrime R S q
      , Subsingleton H¹₍q₎ ∧
          Module.Finite S₍q₎ Ω₍q₎ ∧
          Module.Free S₍q₎ Ω₍q₎
      , Subsingleton H¹₍q₎ ∧
          Module.Projective S₍q₎ Ω₍q₎
      , Subsingleton H¹₍q₎ ∧
          Module.Flat S₍q₎ Ω₍q₎
      ] := by
  sorry

end

end Algebra

/-! ### Lemma_10_137_12 (from Chap10) -/
universe u v

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for the local-global smoothness criterion:
- primary domain: smooth commutative `R`-algebras and the smooth locus on `Spec S`;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.smoothLocus_eq_univ`,
  `Algebra.smoothLocus_eq_univ_iff`,
  `Algebra.FinitePresentation.of_span_eq_top_target`,
  `PrimeSpectrum.iSup_basicOpen_eq_top_iff'`;
- best owner abstraction: the canonical global owner is the smooth locus `smoothLocus R S`
  together with the locality owner for finite presentation on a standard-open cover of `Spec S`;
- primitive data: the basic-open neighborhoods `D(g)` on which `Localization.Away g` is smooth;
- derived API: the source-facing predicate `SmoothAtPrime` and the global equivalence below.

Source/core/bridge triage:
- `source-facing`: the textbook statement `Smooth R S ↔ ∀ q, SmoothAtPrime R S q`;
- `core/canonical`: `smoothLocus R S`, `IsSmoothAt`, and
  `FinitePresentation.of_span_eq_top_target`;
- `bridge/view`: this theorem, which converts the primewise neighborhood condition into the
  canonical owner data `FormallySmooth R S` and `FinitePresentation R S`.
-/

-- Proof sketch: if `R → S` is smooth, then the smooth locus is all of `Spec S`, so every prime is
-- smooth via `smoothAtPrime_iff_isSmoothAt`. Conversely, let `s = { g | S_g is smooth over R }`.
-- The hypothesis says that the basic opens `D(g)` for `g ∈ s` cover `Spec S`, hence
-- `Ideal.span s = ⊤` by `PrimeSpectrum.iSup_basicOpen_eq_top_iff'`. The canonical locality theorem
-- `FinitePresentation.of_span_eq_top_target` yields finite presentation, while
-- `smoothLocus_eq_univ_iff` upgrades the primewise `IsSmoothAt` condition to formal smoothness.
/-- Lemma 10.137.12: the ring map `R → S` is smooth if and only if every prime of `S` admits a
basic open neighborhood on which the localized `R`-algebra is smooth, i.e. every prime satisfies
`SmoothAtPrime R S`. -/
theorem smooth_iff_forall_smoothAtPrime :
    Smooth R S ↔ ∀ q : PrimeSpectrum S, SmoothAtPrime R S q := by
  constructor
  · intro hS q
    letI : Smooth R S := hS
    letI : FinitePresentation R S := hS.2
    have hsmoothLocus : smoothLocus R S = Set.univ := smoothLocus_eq_univ
    exact (smoothAtPrime_iff_isSmoothAt R S q).2 <|
      by
        simpa [smoothLocus] using
          (Set.eq_univ_iff_forall.mp hsmoothLocus) q
  · intro hq
    let s : Set S := { g | Smooth R (Localization.Away g) }
    have hscover : (⨆ g ∈ s, basicOpen g) = ⊤ := by
      apply SetLike.ext'
      change (↑(⨆ g ∈ s, basicOpen g) : Set (PrimeSpectrum S)) = Set.univ
      rw [Set.eq_univ_iff_forall]
      intro q
      rcases hq q with ⟨g, hgq, hg⟩
      have hgmem : q ∈ (basicOpen g : Set (PrimeSpectrum S)) := by
        simpa [mem_basicOpen] using hgq
      exact
        (show (basicOpen g : TopologicalSpace.Opens (PrimeSpectrum S)) ≤ ⨆ h ∈ s, basicOpen h from
          le_iSup_of_le g <| le_iSup_of_le hg le_rfl) hgmem
    have hsone : Ideal.span s = ⊤ :=
      iSup_basicOpen_eq_top_iff'.mp hscover
    have hfp : FinitePresentation R S :=
      FinitePresentation.of_span_eq_top_target s hsone fun g hg ↦ by
        letI : Smooth R (Localization.Away g) := hg
        infer_instance
    letI : FinitePresentation R S := hfp
    have hformallySmooth : FormallySmooth R S := by
      rw [← smoothLocus_eq_univ_iff]
      exact Set.eq_univ_iff_forall.mpr fun q ↦ by
        simpa [smoothLocus] using (smoothAtPrime_iff_isSmoothAt R S q).mp (hq q)
    exact ⟨hformallySmooth, hfp⟩

end Algebra

/-! ### Lemma_10_137_13 (from Chap10) -/
/- Domain-style sampling:
- primary domain: smooth commutative ring homomorphisms and their stability properties;
- sampled owner declarations:
  `RingHom.Smooth`,
  `RingHom.Smooth.comp`,
  `Algebra.Smooth`,
  `Algebra.Smooth.comp`;
- best owner abstraction: `RingHom.Smooth` for ring-hom statements, with `Algebra.Smooth` as the
  algebra-side owner bridged by mathlib;
- primitive data: smoothness of the two ring maps being composed;
- derived API: smoothness of the composite map;

Source/core/bridge triage:
- `source-facing`: the composition statement below;
- `core/canonical`: `Algebra.Smooth.comp`;
- `bridge/view`: `RingHom.Smooth.comp`, which is exactly the right owner-level surface for this
  ring-hom formulation.
-/

/- Lemma 10.137.13: a composition of smooth ring maps is smooth. This is exactly the canonical
mathlib theorem `RingHom.Smooth.comp`. -/
recall RingHom.Smooth.comp

/-! ### Lemma_10_137_14 (from Chap10) -/
universe u v w

namespace Algebra

variable (R : Type u) (S' : Type v) (S'' : Type w)
variable [CommRing R] [CommRing S'] [CommRing S''] [Algebra R S'] [Algebra R S'']

/- Domain-style sampling:
- primary domain: smooth commutative `R`-algebras and their stability under finite products;
- sampled owner declarations:
  `Algebra.Smooth`,
  `Algebra.FormallySmooth.pi_iff`,
  `Algebra.FinitePresentation.of_isLocalizationAway`,
  `IsLocalization.away_of_isIdempotentElem`;
- best owner abstraction: `Algebra.Smooth R A`;
- primitive data: the smooth owner on `S' × S''`, or the two smooth owners on `S'` and `S''`;
- derived API: the factorwise formal smoothness and finite presentation coming from the canonical
  idempotent localizations, and the converse product smoothness obtained by transporting along the
  canonical `Bool`-indexed product view and applying `FormallySmooth.pi_iff`.

Source/core/bridge triage:
- `source-facing`: the binary-product statement below;
- `core/canonical`: `Algebra.Smooth`, `Algebra.FormallySmooth`, `Algebra.FinitePresentation`, and
  `IsLocalization.Away`;
- `bridge/view`: the equivalence between `S' × S''` and the `Bool`-indexed product used only to
  invoke the finite-product owner API.
-/

/-- Lemma 10.137.14: a product `R`-algebra `S' × S''` is smooth over `R` if and only if both
factors `S'` and `S''` are smooth over `R`. -/
theorem smooth_prod_iff :
    Smooth R (S' × S'') ↔ Smooth R S' ∧ Smooth R S'' := by
  let A : Bool → Type (max v w) := fun b ↦ cond b (ULift.{v} S'') (ULift.{w} S')
  letI : ∀ b, CommRing (A b) := by
    intro b
    cases b
    · change CommRing (ULift.{w} S')
      infer_instance
    · change CommRing (ULift.{v} S'')
      infer_instance
  letI : ∀ b, Algebra R (A b) := by
    intro b
    cases b
    · change Algebra R (ULift.{w} S')
      infer_instance
    · change Algebra R (ULift.{v} S'')
      infer_instance
  let eBool : ((b : Bool) → A b) ≃ₐ[R] A false × A true :=
    AlgEquiv.mk
      (Equiv.mk
        (fun f ↦ (f false, f true))
        (fun x b ↦ by
          cases b
          · exact x.1
          · exact x.2)
        (by
          intro f
          funext b
          cases b
          · rfl
          · rfl)
        (by
          intro x
          rfl))
      (by intro x y; rfl)
      (by intro x y; rfl)
      (by intro r; rfl)
  let eLeft : A false ≃ₐ[R] S' := by
    change ULift.{w} S' ≃ₐ[R] S'
    exact ULift.algEquiv
  let eRight : A true ≃ₐ[R] S'' := by
    change ULift.{v} S'' ≃ₐ[R] S''
    exact ULift.algEquiv
  let e : ((b : Bool) → A b) ≃ₐ[R] S' × S'' :=
    eBool.trans (AlgEquiv.prodCongr eLeft eRight)
  constructor
  · intro h
    letI : Smooth R (S' × S'') := h
    constructor
    · letI : Algebra (S' × S'') S' := (AlgHom.fst R S' S'').toAlgebra
      have hker : RingHom.ker (algebraMap (S' × S'') S') = Ideal.span {((0 : S'), (1 : S''))} := by
        ext x
        rw [Ideal.mem_span_singleton, RingHom.mem_ker]
        constructor
        · intro hx
          change x.1 = 0 at hx
          exact ⟨(0, x.2), by
            ext
            · simp [hx]
            · simp⟩
        · rintro ⟨y, rfl⟩
          change (((0 : S'), (1 : S'')) * y).1 = 0
          simp
      have h01 : ((0 : S'), (1 : S'')) = 1 - ((1 : S'), (0 : S'')) := by
        ext
        · simp
        · simp
      have hloc : IsLocalization.Away ((1 : S'), (0 : S'')) S' := by
        refine IsLocalization.away_of_isIdempotentElem ?_ ?_ Prod.fst_surjective
        · simp [IsIdempotentElem]
        · simpa [h01] using hker
      letI : FormallySmooth (S' × S'') S' :=
        FormallySmooth.of_isLocalization (Submonoid.powers ((1 : S'), (0 : S'')))
      exact ⟨FormallySmooth.comp R (S' × S'') S', Algebra.FinitePresentation.of_isLocalizationAway ((1 : S'), (0 : S''))⟩
    · letI : Algebra (S' × S'') S'' := (AlgHom.snd R S' S'').toAlgebra
      have hker : RingHom.ker (algebraMap (S' × S'') S'') = Ideal.span {((1 : S'), (0 : S''))} := by
        ext x
        rw [Ideal.mem_span_singleton, RingHom.mem_ker]
        constructor
        · intro hx
          change x.2 = 0 at hx
          exact ⟨(x.1, 0), by
            ext
            · simp
            · simp [hx]⟩
        · rintro ⟨y, rfl⟩
          change (((1 : S'), (0 : S'')) * y).2 = 0
          simp
      have h10 : ((1 : S'), (0 : S'')) = 1 - ((0 : S'), (1 : S'')) := by
        ext
        · simp
        · simp
      have hloc : IsLocalization.Away ((0 : S'), (1 : S'')) S'' := by
        refine IsLocalization.away_of_isIdempotentElem ?_ ?_ Prod.snd_surjective
        · simp [IsIdempotentElem]
        · simpa [h10] using hker
      letI : FormallySmooth (S' × S'') S'' :=
        FormallySmooth.of_isLocalization (Submonoid.powers ((0 : S'), (1 : S'')))
      exact ⟨FormallySmooth.comp R (S' × S'') S'', Algebra.FinitePresentation.of_isLocalizationAway ((0 : S'), (1 : S''))⟩
  · rintro ⟨h', h''⟩
    let _ : ∀ b, Smooth R (A b) := by
      intro b
      cases b
      · exact Smooth.of_equiv eLeft.symm
      · exact Smooth.of_equiv eRight.symm
    letI : Smooth R ((b : Bool) → A b) := by
      rw [smooth_iff]
      constructor
      · simpa using (FormallySmooth.pi_iff A).2 fun b ↦ (inferInstance : FormallySmooth R (A b))
      · infer_instance
    exact Smooth.of_equiv e

end Algebra

/-! ### Lemma_10_137_15 (from Chap10) -/
universe u

namespace Algebra

open Presentation

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

section

variable (f : Fin c → MvPolynomial (Fin n) R)

/- Domain-style sampling:
- primary domain: Jacobian criteria for smoothness of explicit polynomial-quotient presentations of
  relative global complete intersections;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.Presentation.naive`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.jacobianColumnMinor`;
- best owner abstraction: the public source-facing smoothness owner in this chapter is
  `Algebra.SmoothAtPrime`, while the presentation-theoretic primitive data for the displayed
  quotient `R[x₁, …, xₙ] / (f₁, …, f_c)` already live on the canonical owner
  `Algebra.Presentation`; the Jacobian-minor criterion should therefore be exposed as a theorem
  about `SmoothAtPrime`, with `IsSmoothAt` used only as the internal bridge;
- primitive vs. derived:
  the primitive source-facing data are the relations `f` and the induced naive presentation of the
  quotient; the quotient type and the Jacobian minors are derived owner API coming from
  `Algebra.Presentation`, and `IsSmoothAt` is derived bridge API coming from
  `smoothAtPrime_iff_isSmoothAt`.

Source/core/bridge triage:
- `source-facing`: Lemma `10.137.15`, the Jacobian criterion for smoothness at a prime of the
  explicit quotient, stated using `SmoothAtPrime`;
- `core/canonical`: `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.jacobianColumnMinor`, and `IsSmoothAt`;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt`, which passes between the source-facing smoothness
  predicate and the canonical local owner.
-/

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal

/-- Lemma 10.137.15: for a relative global complete intersection presentation
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` with `c ≤ n` and a prime `q` of `S`, the map `R → S` is smooth
at `q` in the source-facing Stacks sense if and only if some Jacobian minor
`det(∂f_j / ∂x_i)` indexed by a `c`-element subset of the variables avoids `q`. -/
theorem smoothAtPrime_iff_exists_jacobian_minor_not_mem
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) :
    SmoothAtPrime R PresentedAlgebra q ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I) ∉
          q.asIdeal := sorry

-- Proof sketch: use Lemma `10.136.12` to identify the naive cotangent complex of the quotient
-- presentation with the Jacobian matrix `(∂f_j/∂x_i)`. By Lemma `10.134.13`, smoothness at `q`
-- is equivalent to the localized conormal map becoming split injective. For a map between free
-- modules of ranks `c` and `n`, this happens exactly when some `c × c` minor is invertible in the
-- localization at `q`, i.e. when one Jacobian minor avoids `q`.
/-- Companion bridge for Lemma `10.137.15`: for the canonical naive presentation
`R[x₁, …, xₙ] / (f₁, …, f_c)`, formal smoothness at `q` is equivalent to the existence of a
Jacobian minor indexed by a `c`-element subset of the variables whose image in the quotient avoids
`q`. -/
theorem isSmoothAt_iff_exists_jacobian_minor_not_mem
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) :
    IsSmoothAt R q.asIdeal ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I) ∉
          q.asIdeal := by
  let _ : FinitePresentation R PresentedAlgebra :=
    Presentation.finitePresentation_of_isFinite
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
  rw [← smoothAtPrime_iff_isSmoothAt R PresentedAlgebra q]
  exact smoothAtPrime_iff_exists_jacobian_minor_not_mem f hc hP q

end

end Algebra

/-! ### Lemma_10_137_16 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: local smoothness criteria for commutative algebras at a prime, with fiber rings
  over residue fields;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.fiberPrimeAt`,
  `Algebra.IsSmoothAt.of_formallySmooth_fiber`;
- best owner abstraction: `SmoothAtPrime` is the source-facing owner for smoothness on a basic open
  neighborhood, and `fiberPrimeAt R S q` is the chapter-owned point of the fiber ring over
  `q ∩ R`; the fiber smoothness hypothesis should therefore be stated directly as
  `SmoothAtPrime` at `fiberPrimeAt R S q`, not via a parallel witness prime plus compatibility
  equality;
- primitive vs. derived:
  the primitive source-facing inputs are the point `q`, a finite-presentation neighborhood near
  `q`, the local flatness of `R_(q ∩ R) → S_q`, and smoothness of the fiber ring at the canonical
  fiber prime. The auxiliary prime `qf` and the equality
  `q.asIdeal = qf.asIdeal.comap includeRight.toRingHom` were derived bridge data already owned by
  `fiberPrimeAt`.

Source/core/bridge triage:
- `source-facing`: the local Stacks criterion proving `SmoothAtPrime R S q`;
- `core/canonical`: `SmoothAtPrime`, `fiberPrimeAt`, and the local owner `IsSmoothAt`;
- `bridge/view`: the finite-presentation neighborhood witness and the implicit identification of
  `q` with the canonical fiber prime.
-/

-- Proof sketch: choose `g ∉ q` such that `R → S_g` is of finite presentation. The local map
-- `R_(q ∩ R) → S_q` is unchanged after replacing `S` by `S_g`, and the prime `qf` of the fiber
-- ring corresponds to `q`. The fiber smoothness hypothesis gives a principal-open neighborhood of
-- `qf` on which the fiber is smooth over `κ(q ∩ R)`, and the finitely presented local flatness +
-- smooth-fiber criterion then produces a principal-open neighborhood of `q` on which `R → S` is
-- smooth.
/-- Lemma 10.137.16: if some basic open neighborhood `S_g` of `q` is of finite presentation over
`R`, the local ring homomorphism `R_(q ∩ R) → S_q` is flat, and the fiber
`κ(q ∩ R) ⊗[R] S` is smooth over `κ(q ∩ R)` at the prime corresponding to `q`, then `R → S` is
smooth at `q`, i.e. some localization `S_h` with `h ∉ q` is smooth over `R`. -/
lemma smoothAtPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberSmoothAtPrime
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat)
    (hfiber :
      SmoothAtPrime (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S)
        (fiberPrimeAt R S q)) :
    SmoothAtPrime R S q := sorry

end Algebra

/-! ### Lemma_10_137_17 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [FinitePresentation R S] [Module.Flat R R']

/- 
Domain-style sampling:
- primary domain: base change on `PrimeSpectrum` for the canonical smooth locus of a finitely
  presented ring map;
- sampled owner declarations of the same kind:
  `Algebra.smoothLocus`,
  `Algebra.smoothLocus_eq_compl_support_inter`,
  `Algebra.smoothLocus_comap_of_isLocalization`,
  `relativeDimensionAt_le_preimage_eq_baseChange`,
  `cohenMacaulayFiberLocus_baseChange_preimage_eq`;
- best owner abstraction: the canonical owner is `smoothLocus R S`; this file should state the
  base-change result directly for that owner rather than through a parallel set-builder or local
  wrapper;
- primitive data: the finitely presented map `R → S`, the flat base change `R → R'`, and the
  induced map `Spec(R' ⊗[R] S) → Spec(S)`;
- derived API: the inverse-image equality for the smooth locus under `PrimeSpectrum.comap
  includeRight.toRingHom`.

Source/core/bridge triage:
* `source-facing`: the smooth locus of a ring map;
* `core/canonical`: `Algebra.smoothLocus` and its local description via `IsSmoothAt`;
* `bridge/view`: inverse image along `PrimeSpectrum.comap includeRight.toRingHom`.
-/

-- Proof sketch: identify `smoothLocus` with the locus where the localized cotangent homology
-- vanishes and the localized Kähler differentials are free. Flat base change gives the forward
-- implication by `Algebra.tensorH1CotangentOfFlat` and preservation of freeness/projectivity.
-- For the reverse implication, localize at a prime `q'` of `R' ⊗[R] S`; since `S_q → S'_{q'}`
-- is faithfully flat, vanishing of localized `H¹(L)` descends along faithful flatness, and
-- finite-projectivity of localized Kähler differentials descends by Lemma `10.78.6`. Then apply
-- the local smoothness criterion of Lemma `10.137.11`.
/-- Lemma 10.137.17: for a finitely presented ring map `R → S` and a flat base change `R → R'`,
if `S' = R' ⊗[R] S`, then the smooth locus of `R' → S'` is the inverse image of the smooth locus
of `R → S` under the induced map `Spec(S') → Spec(S)`. -/
theorem smoothLocus_baseChange_preimage_eq :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        smoothLocus R S =
      smoothLocus R' (R' ⊗[R] S) := sorry

end Algebra

/-! ### Lemma_10_137_18 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

section

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S]
variable [Algebra k K] [Algebra k S] [FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- Domain-style sampling pass:

Primary domain: smoothness at a prime under tensor base change along a field extension.

Sampled owner declarations:
* `Algebra.SmoothAtPrime`;
* `Algebra.smoothAtPrime_iff_isSmoothAt`;
* `Algebra.IsSmoothAt`;
* `Algebra.smoothLocus_baseChange_preimage_eq`;
* `Algebra.smoothLocus`.

Best owner abstraction: the source-facing owner in this chapter is `SmoothAtPrime`; the canonical
local owner remains `IsSmoothAt`, and the global base-change theorem for the owner set
`smoothLocus` already exists upstream. This file should therefore state the primewise
field-extension invariance theorem using `SmoothAtPrime`, with `IsSmoothAt` kept only as a
companion bridge.

Primitive vs. derived:
* primitive data: the field extension `K / k`, the finite-type `k`-algebra `S`, and the upstairs
  prime `qK : PrimeSpectrum S_K`;
* derived API: the contracted prime `q := PrimeSpectrum.comap iSK qK`, the finite-presentation
  instances coming from finite type over fields, and the bridge to the canonical predicate
  `IsSmoothAt`.

Source/core/bridge triage:
* `source-facing`: the pointwise field-extension invariance statement at a prime;
* `core/canonical`: `SmoothAtPrime`, `IsSmoothAt`, and the owner locus `smoothLocus`;
* `bridge/view`: contraction along `iSK`, obtained by specializing
  `smoothLocus_baseChange_preimage_eq` and `smoothAtPrime_iff_isSmoothAt`.
-/

-- Proof sketch: this is the field-extension specialization of the smooth-locus base-change
-- theorem from Lemma `10.137.17`. Since finite type over a field implies finite presentation, one
-- rewrites both source-facing smoothness predicates via `smoothAtPrime_iff_isSmoothAt`, then
-- identifies both sides with membership in the corresponding smooth locus; the prime of `S`
-- corresponding to `qK` is obtained by contraction along `includeRight`.
/-- Lemma 10.137.18: for a field extension `K / k`, a finite-type `k`-algebra `S`, and a prime
`qK` of `K ⊗[k] S`, letting `q` be the corresponding prime of `S`, the algebra `S` is smooth over
`k` at `q` in the source-facing Stacks sense if and only if `K ⊗[k] S` is smooth over `K` at
`qK`. -/
theorem smoothAtPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    SmoothAtPrime k S q ↔ SmoothAtPrime K S_K qK := by
  letI : FinitePresentation k S :=
    FinitePresentation.of_finiteType.mp inferInstance
  letI : FiniteType K S_K := FiniteType.baseChange K
  letI : FinitePresentation K S_K :=
    FinitePresentation.of_finiteType.mp inferInstance
  let q := PrimeSpectrum.comap iSK qK
  change SmoothAtPrime k S q ↔ SmoothAtPrime K S_K qK
  rw [smoothAtPrime_iff_isSmoothAt k S q, smoothAtPrime_iff_isSmoothAt K S_K qK]
  change
      qK ∈ PrimeSpectrum.comap ((includeRight : S →ₐ[k] S_K).toRingHom) ⁻¹' smoothLocus k S ↔
        qK ∈ smoothLocus K S_K
  have hsmooth :
      PrimeSpectrum.comap ((includeRight : S →ₐ[k] S_K).toRingHom) ⁻¹' smoothLocus k S =
        smoothLocus K S_K :=
    smoothLocus_baseChange_preimage_eq
  rw [hsmooth]

-- Proof sketch: this is the canonical local-owner reformulation of Lemma `10.137.18`, obtained
-- by rewriting both source-facing smoothness predicates using `smoothAtPrime_iff_isSmoothAt`.
/-- Companion bridge for Lemma `10.137.18`: after rewriting `SmoothAtPrime` through the canonical
predicate `IsSmoothAt`, field extension along `K / k` preserves smoothness at the corresponding
prime ideals. -/
theorem isSmoothAt_iff_isSmoothAt_tensor_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    IsSmoothAt k q.asIdeal ↔ IsSmoothAt K qK.asIdeal := by
  letI : FinitePresentation k S :=
    FinitePresentation.of_finiteType.mp inferInstance
  letI : FiniteType K S_K := FiniteType.baseChange K
  letI : FinitePresentation K S_K :=
    FinitePresentation.of_finiteType.mp inferInstance
  let q := PrimeSpectrum.comap iSK qK
  change IsSmoothAt k q.asIdeal ↔ IsSmoothAt K qK.asIdeal
  simpa [q] using
    (smoothAtPrime_iff_isSmoothAt k S q).symm.trans
      ((smoothAtPrime_iff_of_tensorProduct_fieldExtension qK).trans
        (smoothAtPrime_iff_isSmoothAt K S_K qK))

end

end Algebra

/-! ### Lemma_10_137_19 (from Chap10) -/
universe u v

namespace Algebra

section

variable {R : Type u} {Sbar : Type v} [CommRing R] (I : Ideal R)
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar] [Smooth (R ⧸ I) Sbar]

/- Domain-style sampling:
* primary domain: smooth commutative algebras over quotient rings and their local standard-smooth
  presentations;
* sampled declarations:
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`,
  `Algebra.IsStandardSmooth`,
  `jacobian_inverted_quotient_isStandardSmooth`,
  `exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic`;
* best owner abstraction: on each lifted chart, the target structure should be expressed directly
  by the canonical owner `Algebra.IsStandardSmooth R S`, not by a parallel presentation wrapper;
* primitive vs. derived:
  the primitive source data are the quotient ideal `I`, the quotient algebra `Sbar`, and the
  ambient owner `[Smooth (R ⧸ I) Sbar]`;
  the cover, the lifted chart algebra `S`, its standard-smooth owner, and the quotient comparison
  `Localization.Away g ≃ₐ[R ⧸ I] S ⧸ Ideal.map (algebraMap R S) I` are derived existence data.

Source/core/bridge triage:
* `source-facing`: the existence of a standard-open cover of `Spec Sbar` by charts that lift to
  standard smooth `R`-algebras;
* `core/canonical`: `Algebra.IsStandardSmooth`;
* `bridge/view`: the quotient comparison equivalence identifying each chart
  `Localization.Away g` with the reduction modulo `I` of its lift.

The weaker Chapter 10 theorem
`exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic` has the same local
quotient-lift shape, but its owner conclusion is only the relative-global-complete-intersection
structure. This file keeps the stronger source-facing standard-smooth conclusion rather than
introducing any intermediate wrapper.
-/

-- Proof sketch: apply `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` to the smooth map
-- `R ⧸ I → Sbar` to obtain a unit-ideal cover by basic opens on which `Sbar` is standard smooth
-- over `R ⧸ I`. For each chart, extract a submersive presentation from the owner
-- `Algebra.IsStandardSmooth`, lift the defining equations and Jacobian determinant to `R`, and
-- use Example `10.137.7` to produce a standard smooth `R`-algebra whose reduction modulo `I`
-- identifies with the given localization.
/-- Lemma 10.137.19: a smooth `(R ⧸ I)`-algebra admits a standard-open cover by localizations which
are reductions modulo `I` of standard smooth `R`-algebras. -/
theorem exists_standardSmooth_lift_cover_of_quotient_smooth :
    ∃ s : Set Sbar, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsStandardSmooth R S),
          Nonempty ((Localization.Away g) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := sorry

end

end Algebra
