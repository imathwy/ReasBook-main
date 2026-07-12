import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w uP

open scoped TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Definition 10.54.1 (1): a ring homomorphism `R → S` is essentially of finite type if it is the
canonical mathlib notion `RingHom.EssFiniteType`, equivalently if `S` is the localization of an
`R`-algebra of finite type. -/
recall RingHom.EssFiniteType

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.54.1 (2): an `R`-algebra `S` is essentially of finite presentation if it is the
localization of a quotient-model finitely presented `R`-algebra. This quotient witness stays in
the base universe, so the usual equivalence and base-change transports do not need `ULift`
bookkeeping. -/
@[stacks 00QM]
class EssFinitePresentation : Prop where
  cond :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) (_ : I.FG)
      (_ : Algebra (MvPolynomial (Fin n) R ⧸ I) S)
      (_ : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S)
      (M : Submonoid (MvPolynomial (Fin n) R ⧸ I)),
      IsLocalization M S

/-- Unfolding `Algebra.EssFinitePresentation` gives the standard localization-of-a-finitely-
presented quotient-model condition. -/
theorem essFinitePresentation_iff :
    EssFinitePresentation R S ↔
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) (_ : I.FG)
        (_ : Algebra (MvPolynomial (Fin n) R ⧸ I) S)
        (_ : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S)
        (M : Submonoid (MvPolynomial (Fin n) R ⧸ I)),
        IsLocalization M S := by
  constructor
  · intro h
    -- This is just the class field unpacked.
    exact h.cond
  · intro h
    -- Repack the quotient-model witness into the class.
    exact ⟨h⟩

/-- A finitely presented `R`-algebra is essentially of finite presentation over `R`. -/
theorem EssFinitePresentation.of_finitePresentation [Algebra.FinitePresentation R S] :
    EssFinitePresentation R S := by
  obtain ⟨n, I, e, hI⟩ := (Algebra.FinitePresentation.iff (R := R) (A := S)).mp inferInstance
  letI : Algebra (MvPolynomial (Fin n) R ⧸ I) S := e.toRingHom.toAlgebra
  letI : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S := by
    -- The quotient-model map already extends the structural map `R → S`.
    exact IsScalarTower.of_algebraMap_eq' (R := R) (S := MvPolynomial (Fin n) R ⧸ I) (A := S) <|
      by
        ext x
        simpa [RingHom.algebraMap_toAlgebra] using (e.commutes x).symm
  let M : Submonoid (MvPolynomial (Fin n) R ⧸ I) := IsUnit.submonoid _
  have hloc : IsLocalization M S := by
    -- The quotient-model witness is itself a localization at the units.
    letI : IsLocalization M (MvPolynomial (Fin n) R ⧸ I) := IsLocalization.self (R := _)
      (M := M) le_rfl
    let eQ : (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[MvPolynomial (Fin n) R ⧸ I] S :=
      { e with
        commutes' := fun x => by
          simp [RingHom.algebraMap_toAlgebra] }
    exact IsLocalization.isLocalization_of_algEquiv M eQ
  -- Use the lifted copy of `S` so the witness lives in the owner's fixed universe.
  rw [essFinitePresentation_iff]
  exact ⟨n, I, hI, inferInstance, inferInstance, M, hloc⟩

/-- A finitely presented `R`-algebra is essentially of finite presentation over `R`. -/
instance of_finitePresentation [Algebra.FinitePresentation R S] :
    EssFinitePresentation R S :=
  EssFinitePresentation.of_finitePresentation R S

/-- A localization of a finitely presented `R`-algebra is essentially of finite presentation
over `R`. -/
theorem EssFinitePresentation.of_isLocalization
    (P : Type uP) [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (M : Submonoid P) [IsLocalization M S] :
    EssFinitePresentation R S := by
  obtain ⟨n, I, e, hI⟩ := (Algebra.FinitePresentation.iff (R := R) (A := P)).mp inferInstance
  letI : Algebra (MvPolynomial (Fin n) R ⧸ I) S :=
    ((algebraMap P S).comp e.toRingHom).toAlgebra
  letI : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S := by
    -- The composite quotient-model map factors through `P`, so the tower equation is the
    -- original `R → P → S` compatibility rewritten across `e`.
    exact IsScalarTower.of_algebraMap_eq' (R := R) (S := MvPolynomial (Fin n) R ⧸ I) (A := S) <|
      by
        ext x
        change algebraMap R S x =
            algebraMap P S (e (algebraMap R (MvPolynomial (Fin n) R ⧸ I) x))
        rw [e.commutes]
        exact DFunLike.congr_fun (IsScalarTower.algebraMap_eq R P S) x
  let M' : Submonoid (MvPolynomial (Fin n) R ⧸ I) := M.comap e.toRingHom
  have hloc : IsLocalization M' S := by
    -- Route correction: transport the localization witness across the quotient-model equivalence
    -- so the class stores only the canonical base-universe witness.
    refine IsLocalization.of_ringEquiv_left (K := S) (M₁ := M) (M₂ := M') e.toRingEquiv ?_ ?_
    · ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact hx'
      · intro hx
        refine ⟨e.symm x, ?_, by simp⟩
        change e (e.symm x) ∈ M
        simpa using hx
    · intro x
      rfl
  rw [essFinitePresentation_iff]
  exact ⟨n, I, hI, inferInstance, inferInstance, M', hloc⟩

/-- Unfolding `Algebra.EssFinitePresentation` also recovers the traditional witness by an
arbitrary finitely presented `R`-algebra. -/
theorem essFinitePresentation_iff_exists_finitePresentation :
    EssFinitePresentation R S ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (_ : Algebra.FinitePresentation R P) (M : Submonoid P),
        IsLocalization M S := by
  constructor
  · intro h
    rw [essFinitePresentation_iff] at h
    rcases h with ⟨n, I, hI, hQS, hTowerQS, M, hloc⟩
    letI : Algebra (MvPolynomial (Fin n) R ⧸ I) S := hQS
    letI : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S := hTowerQS
    let Q : Type u := MvPolynomial (Fin n) R ⧸ I
    let P : Type (max u v) := ULift.{max u v, u} Q
    let eP : P ≃ₐ[R] Q := ULift.algEquiv (R := R) (A := Q)
    letI : CommRing P := inferInstance
    letI : Algebra R P := inferInstance
    letI : Algebra P S := ULift.algebra' Q S
    letI : IsScalarTower R P S :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := P) (A := S) fun x ↦ by
        change algebraMap R S x = algebraMap Q S (ULift.down (algebraMap R P x))
        rw [ULift.down_algebraMap]
        exact DFunLike.congr_fun (IsScalarTower.algebraMap_eq R Q S) x
    letI : Algebra.FinitePresentation R P :=
      letI : Algebra.FinitePresentation R Q :=
        Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin n) R) hI
      Algebra.FinitePresentation.equiv (ULift.algEquiv (R := R) (A := Q)).symm
    let M' : Submonoid P := M.comap eP.toRingHom
    have hloc' : IsLocalization M' S := by
      refine IsLocalization.of_ringEquiv_left (K := S) (M₁ := M) (M₂ := M') eP.toRingEquiv ?_ ?_
      · ext x
        constructor
        · rintro ⟨x', hx', rfl⟩
          exact hx'
        · intro hx
          refine ⟨eP.symm x, ?_, by simp⟩
          change eP (eP.symm x) ∈ M
          simpa using hx
      · intro x
        rfl
    -- The quotient-model witness is already a finitely presented witness in the traditional form.
    exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, M', hloc'⟩
  · rintro ⟨P, _, _, _, _, _, M, hloc⟩
    -- Convert the arbitrary finitely presented witness back to the quotient model before packaging.
    exact EssFinitePresentation.of_isLocalization (R := R) (S := S) P M

/-- The identity `R`-algebra is essentially of finite presentation over `R`. -/
instance : EssFinitePresentation R R :=
  inferInstance

/-- Essential finite presentation is preserved by `R`-algebra equivalence. -/
theorem EssFinitePresentation.equiv (T : Type w) [CommRing T] [Algebra R T]
    [EssFinitePresentation R S] (e : S ≃ₐ[R] T) : EssFinitePresentation R T := by
  have hS : EssFinitePresentation R S := inferInstance
  rw [essFinitePresentation_iff] at hS ⊢
  rcases hS with ⟨n, I, hI, hQS, hTowerQS, M, hloc⟩
  letI : Algebra (MvPolynomial (Fin n) R ⧸ I) S := hQS
  letI : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S := hTowerQS
  letI : Algebra (MvPolynomial (Fin n) R ⧸ I) T :=
    ((e.toRingHom).comp (algebraMap (MvPolynomial (Fin n) R ⧸ I) S)).toAlgebra
  letI : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) T := by
    -- Transport the existing tower equation for `S` across the target equivalence `e`.
    exact IsScalarTower.of_algebraMap_eq' (R := R) (S := MvPolynomial (Fin n) R ⧸ I) (A := T) <|
      by
        ext x
        change algebraMap R T x = e ((algebraMap (MvPolynomial (Fin n) R ⧸ I) S)
          (algebraMap R (MvPolynomial (Fin n) R ⧸ I) x))
        rw [← e.commutes]
        exact congrArg e
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R ⧸ I) S) x)
  have hlocT : IsLocalization M T := by
    -- Keep the same quotient-model witness and transport only the localization target.
    let eQ : S ≃ₐ[MvPolynomial (Fin n) R ⧸ I] T :=
      { e with
        commutes' := fun x => by
          rfl }
    exact IsLocalization.isLocalization_of_algEquiv M eQ
  exact ⟨n, I, hI, inferInstance, inferInstance, M, hlocT⟩

/-- Helper for Definition 10.54.1: one denominator from the original localization witness clears a
finite subset of the target, so every chosen element comes from a single principal localization. -/
theorem exists_awayMap_range_finset {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] (M : Submonoid Q) [IsLocalization M S]
    (u : Finset S) :
    ∃ m : M, ∀ x ∈ u,
      x ∈ Set.range
        (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)) := by
  classical
  choose a s hs using fun x : { x // x ∈ u } ↦ IsLocalization.exists_mk'_eq M (x : S)
  let m : M := u.attach.prod s
  refine ⟨m, ?_⟩
  intro x hx
  let x' : { x // x ∈ u } := ⟨x, hx⟩
  let t : M := (u.attach.erase x').prod s
  have hm : m = s x' * t := by
    -- Split the global denominator into the chosen factor and the complementary product.
    simp [m, t, Finset.mul_prod_erase]
  letI : IsLocalization.Away (algebraMap Q S (m : Q)) S :=
    IsLocalization.away_of_isUnit_of_bijective S (IsLocalization.map_units S m)
      Function.bijective_id
  have hAway :
      Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m) =
        IsLocalization.Away.map (S := Localization.Away (m : Q)) (Q := S)
          (algebraMap Q S) (m : Q) := by
    -- Both maps agree on `Q`, so localization extensionality identifies them.
    apply IsLocalization.ringHom_ext (Submonoid.powers (m : Q))
    ext q
    simp [Localization.awayLift, IsLocalization.Away.map]
  refine ⟨Localization.mk (a x' * (t : Q)) ⟨(m : Q), by exact ⟨1, by simp⟩⟩, ?_⟩
  -- Evaluate the chosen fraction in the principal localization, then compare it to the original
  -- representation `a x' / s x'` by multiplying through by `s x'`.
  rw [Localization.mk_eq_mk']
  rw [hAway]
  simp only [IsLocalization.Away.map, IsLocalization.map_mk', map_mul]
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  rw [show x = ↑x' by rfl, ← hs x']
  rw [hm, map_mul]
  calc
    algebraMap Q S (a x') * algebraMap Q S (t : Q)
        = (algebraMap Q S (s x') * IsLocalization.mk' S (a x') (s x')) *
            algebraMap Q S (t : Q) := by
              rw [IsLocalization.mk'_spec']
    _ = IsLocalization.mk' S (a x') (s x') *
          (algebraMap Q S (s x') * algebraMap Q S (t : Q)) := by
            ring
    _ = _ := by
          simpa [hm, map_mul]

/-- Helper for Definition 10.54.1: the away-lift determined by one denominator of a localization
extends the original algebra map, so it supplies the expected scalar tower through the principal
localization. -/
theorem isScalarTower_awayLift {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    IsScalarTower Q A0 S := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  -- The away-lift agrees with `Q → S` on the image of `Q`, so the tower equation is immediate.
  exact IsScalarTower.of_algebraMap_eq (R := Q) (S := A0) (A := S) fun a ↦ by
    simp [Localization.awayLift, RingHom.algebraMap_toAlgebra]

omit [Algebra R S] in
/-- Helper for Definition 10.54.1: on the explicit principal-localization surface
`A0 := Localization.Away (m : Q)`, the chosen away-lift algebra map extends the original owner
map `Q → S`. -/
theorem awayLift_owner_surface_eq {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    (algebraMap A0 S).comp (algebraMap Q A0) = algebraMap Q S := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  -- Evaluate both maps on `Q`; the away-lift is defined to agree with the original structure map.
  ext q
  simp [Localization.awayLift, RingHom.algebraMap_toAlgebra]

/-- Helper for Definition 10.54.1: on the fixed principal-localization surface
`A₀ := Localization.Away (m : Q)`, the explicit away-lift map still agrees with the original
base map `R → S`. -/
theorem awayLift_base_surface_eq {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R A0 := ((algebraMap Q A0).comp (algebraMap R Q)).toAlgebra
    (algebraMap A0 S).comp (algebraMap R A0) = algebraMap R S := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  letI : Algebra R A0 := ((algebraMap Q A0).comp (algebraMap R Q)).toAlgebra
  have howner :
      (algebraMap A0 S).comp (algebraMap Q A0) = algebraMap Q S :=
    awayLift_owner_surface_eq (R := R) (Q := Q) (S := S) (M := M) m
  -- Rewrite the composite through `Q`, then compare with the original `R → Q → S` tower.
  ext r
  calc
    ((algebraMap A0 S).comp (algebraMap R A0)) r
        = algebraMap A0 S (algebraMap Q A0 (algebraMap R Q r)) := by
            rfl
    _ = algebraMap Q S (algebraMap R Q r) := by
          exact DFunLike.congr_fun howner (algebraMap R Q r)
    _ = algebraMap R S r := by
          symm
          exact DFunLike.congr_fun (IsScalarTower.algebraMap_eq R Q S) r

/-- Helper for Definition 10.54.1: after composing the away-lift surface `A₀ → S` with
`S → P`, the resulting map `A₀ → P` still recovers the original structural map `R → P`. -/
theorem awayLift_comp_surface_eq {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {P : Type*} [CommRing P] [Algebra R P] [Algebra S P]
    [IsScalarTower R S P] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R A0 := ((algebraMap Q A0).comp (algebraMap R Q)).toAlgebra
    letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
    (algebraMap A0 P).comp (algebraMap R A0) = algebraMap R P := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  letI : Algebra R A0 := ((algebraMap Q A0).comp (algebraMap R Q)).toAlgebra
  letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
  have hbase :
      (algebraMap A0 S).comp (algebraMap R A0) = algebraMap R S :=
    awayLift_base_surface_eq (R := R) (Q := Q) (S := S) (M := M) m
  -- Evaluate the composite on `R`, then rewrite it through the already identified `A₀ → S`
  -- surface and the given `R → S → P` tower.
  ext r
  calc
    ((algebraMap A0 P).comp (algebraMap R A0)) r
        = algebraMap S P (((algebraMap A0 S).comp (algebraMap R A0)) r) := by
            simp [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    _ = algebraMap S P (algebraMap R S r) := by
          rw [DFunLike.congr_fun hbase r]
    _ = algebraMap R P r := by
          symm
          exact DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S P) r

/-- Helper for Definition 10.54.1: after clearing the finitely many coefficients of a finite
presentation over `S`, one denominator of the localization witness already realizes those
coefficients over the corresponding principal localization of `Q`. -/
theorem Presentation.exists_away_hasCoeffs {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) [Finite ι] [Finite σ] (M : Submonoid Q)
    [IsLocalization M S] :
    ∃ m : M,
      let A0 := Localization.Away (m : Q)
      letI : CommRing A0 := inferInstance
      letI : Algebra Q A0 := inferInstance
      letI : Algebra A0 S :=
        (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
      letI : IsScalarTower Q A0 S := isScalarTower_awayLift (R := R) (Q := Q) (S := S) (m := m)
      letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
      letI : IsScalarTower A0 S P := IsScalarTower.of_algebraMap_eq' rfl
      Ppres.HasCoeffs A0 := by
  classical
  let coeffs : Finset S := Ppres.finite_coeffs.toFinset
  obtain ⟨m, hm⟩ := exists_awayMap_range_finset (R := R) (S := S) (Q := Q) (M := M) coeffs
  refine ⟨m, ?_⟩
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  have hQSurface :
      (algebraMap A0 S).comp (algebraMap Q A0) = algebraMap Q S :=
    awayLift_owner_surface_eq (R := R) (Q := Q) (S := S) (M := M) m
  letI : IsScalarTower Q A0 S :=
    IsScalarTower.of_algebraMap_eq' (R := Q) (S := A0) (A := S) hQSurface.symm
  letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
  letI : IsScalarTower A0 S P := IsScalarTower.of_algebraMap_eq' rfl
  -- Every coefficient lies in the chosen finite set, so the common denominator clears it.
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : x ∈ coeffs := by
    exact (Set.Finite.mem_toFinset Ppres.finite_coeffs).2 hx
  simpa [coeffs, RingHom.algebraMap_toAlgebra] using hm x hx'

/-- Helper for Definition 10.54.1: after passing from `Q` to the principal localization away from
one chosen denominator, the original target `S` remains a localization at the image of the
original submonoid. -/
theorem isLocalization_away_target_of_mem {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] (M : Submonoid Q) [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : IsScalarTower Q A0 S := isScalarTower_awayLift (R := R) (Q := Q) (S := S) (m := m)
    IsLocalization (Algebra.algebraMapSubmonoid A0 M) S := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  have hQSurface :
      (algebraMap A0 S).comp (algebraMap Q A0) = algebraMap Q S :=
    awayLift_owner_surface_eq (R := R) (Q := Q) (S := S) (M := M) m
  letI : IsScalarTower Q A0 S :=
    IsScalarTower.of_algebraMap_eq' (R := Q) (S := A0) (A := S) hQSurface.symm
  have hm : Submonoid.powers (m : Q) ≤ M := Submonoid.powers_le.2 m.2
  -- This is the standard localization-refinement step from the principal localization to `M`.
  exact IsLocalization.isLocalization_of_submonoid_le A0 S (Submonoid.powers (m : Q)) M hm

/-- Helper for Definition 10.54.1: if `S` is a localization of `A₀` and `P` is the tensor-model
coming from a presentation with coefficients in `A₀`, then `P` is a localization of the descended
model at the image of the same denominator submonoid. -/
theorem Presentation.isLocalization_modelOfHasCoeffs {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0] [Algebra A0 S] [Algebra A0 P]
    [IsScalarTower A0 S P] [Ppres.HasCoeffs A0] (M0 : Submonoid A0) [IsLocalization M0 S] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid P0 M0) P := by
  let P0 := Ppres.ModelOfHasCoeffs A0
  letI : CommRing P0 := inferInstance
  letI : Algebra A0 P0 := inferInstance
  letI : Algebra P0 P :=
    (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  letI : Algebra P0 (S ⊗[A0] P0) :=
    Algebra.TensorProduct.rightAlgebra (R := A0) (A := S) (B := P0)
  have hTensor : IsLocalization (Algebra.algebraMapSubmonoid P0 M0) (S ⊗[A0] P0) :=
    IsLocalization.tensorRight (R := A0) (S := P0) (A := S) M0
  let eP0 : S ⊗[A0] P0 ≃ₐ[P0] P :=
    { Ppres.tensorModelOfHasCoeffsEquiv A0 with
      commutes' := fun y ↦ by
        -- The descended-model action on `P` is defined through the right tensor factor.
        simp [RingHom.algebraMap_toAlgebra] }
  -- Transport the tensor-right localization witness across the canonical tensor-model equivalence.
  exact IsLocalization.isLocalization_of_algEquiv (Algebra.algebraMapSubmonoid P0 M0) eP0

/-- Helper for Definition 10.54.1: the descended model map `A₀ → P₀ → P` agrees with the original
`A₀ → P` algebra map. -/
theorem Presentation.descended_model_algebraMap_eq {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0] [Algebra A0 S] [Algebra A0 P]
    [IsScalarTower A0 S P] [Ppres.HasCoeffs A0] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    (algebraMap P0 P).comp (algebraMap A0 P0) = algebraMap A0 P := by
  let P0 := Ppres.ModelOfHasCoeffs A0
  letI : CommRing P0 := inferInstance
  letI : Algebra A0 P0 := inferInstance
  letI : Algebra P0 P :=
    (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  ext a
  -- Rewrite the descended coefficient as the quotient class of `C a`, then evaluate the tensor
  -- model on the corresponding simple tensor.
  change Ppres.tensorModelOfHasCoeffsEquiv A0 (1 ⊗ₜ[A0] (algebraMap A0 P0 a)) = algebraMap A0 P a
  rw [show algebraMap A0 P0 a = Ideal.Quotient.mk _ (MvPolynomial.C a) by rfl]
  simp

omit [Algebra R S] in
/-- Helper for Definition 10.54.1: the descended model inherits the original `R`-algebra structure
through the tensor-model equivalence, so `R → P₀ → P` is a scalar tower. -/
theorem Presentation.isScalarTower_modelOfHasCoeffs {P : Type*} [CommRing P] [Algebra R P]
    [Algebra S P] (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0]
    [Algebra R A0] [Algebra A0 S] [Algebra A0 P] [IsScalarTower A0 S P]
    [IsScalarTower R A0 P] [Ppres.HasCoeffs A0] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra R P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    IsScalarTower R P0 P := by
  let P0 := Ppres.ModelOfHasCoeffs A0
  letI : CommRing P0 := inferInstance
  letI : Algebra A0 P0 := inferInstance
  letI : Algebra R P0 := inferInstance
  letI : Algebra P0 P :=
    (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  have hA0 :
      (algebraMap P0 P).comp (algebraMap A0 P0) = algebraMap A0 P :=
    Presentation.descended_model_algebraMap_eq (Ppres := Ppres) (A0 := A0)
  -- First identify the descended map on the coefficient ring `A₀`, then compose with the given
  -- `R → A₀ → P` tower to recover the desired `R → P₀ → P` factorization.
  exact IsScalarTower.of_algebraMap_eq' (R := R) (S := P0) (A := P) <| by
    ext r
    calc
      algebraMap R P r
          = algebraMap A0 P (algebraMap R A0 r) := by
              exact DFunLike.congr_fun (IsScalarTower.algebraMap_eq R A0 P) r
      _ = (algebraMap P0 P) (algebraMap A0 P0 (algebraMap R A0 r)) := by
            symm
            exact DFunLike.congr_fun hA0 (algebraMap R A0 r)
      _ = ((algebraMap P0 P).comp (algebraMap R P0)) r := by
            simp [RingHom.comp_apply,
              DFunLike.congr_fun (IsScalarTower.algebraMap_eq R A0 P0) r]

/-- Helper for Definition 10.54.1: once the descended model `P₀` localizes to `P`, composing with
the given localization `P → T` makes `T` a localization of `P₀` at the localization-of-
localization submonoid. -/
theorem Presentation.isLocalization_modelOfHasCoeffs_comp {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0] [Algebra A0 S] [Algebra A0 P]
    [IsScalarTower A0 S P] [Ppres.HasCoeffs A0] (M0 : Submonoid A0) [IsLocalization M0 S]
    {T : Type*} [CommRing T] [Algebra P T] (N : Submonoid P) [IsLocalization N T] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    letI : Algebra P0 T := ((algebraMap P T).comp (algebraMap P0 P)).toAlgebra
    IsLocalization
      (IsLocalization.localizationLocalizationSubmodule
        (Algebra.algebraMapSubmonoid P0 M0) N) T := by
  let P0 := Ppres.ModelOfHasCoeffs A0
  letI : CommRing P0 := inferInstance
  letI : Algebra A0 P0 := inferInstance
  letI : Algebra P0 P :=
    (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  letI : Algebra P0 T := ((algebraMap P T).comp (algebraMap P0 P)).toAlgebra
  letI : IsScalarTower P0 P T := IsScalarTower.of_algebraMap_eq' rfl
  have hlocP : IsLocalization (Algebra.algebraMapSubmonoid P0 M0) P :=
    Presentation.isLocalization_modelOfHasCoeffs (Ppres := Ppres) (A0 := A0) (M0 := M0)
  letI : IsLocalization (Algebra.algebraMapSubmonoid P0 M0) P := hlocP
  -- The localization-of-a-localization theorem now applies directly to `P₀ → P → T`.
  exact IsLocalization.localization_localization_isLocalization
    (M := Algebra.algebraMapSubmonoid P0 M0) (N := N) (T := T)

/-- Helper for Definition 10.54.1: once the coefficient ring `A₀` is finitely presented over the
base ring `R`, the descended model cut out by the same finite presentation is again finitely
presented over `R`. -/
theorem Presentation.finitePresentation_modelOfHasCoeffs_base {P : Type*} [CommRing P]
    [Algebra S P] (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0]
    [Algebra R A0] [Algebra A0 S] [Algebra A0 P] [IsScalarTower R A0 S] [IsScalarTower A0 S P]
    [Ppres.HasCoeffs A0] [Finite ι] [Finite σ] [Algebra.FinitePresentation R A0] :
    Algebra.FinitePresentation R (Ppres.ModelOfHasCoeffs A0) := by
  letI : Algebra A0 (Ppres.ModelOfHasCoeffs A0) := inferInstance
  letI : Algebra R (Ppres.ModelOfHasCoeffs A0) := inferInstance
  letI : IsScalarTower R A0 (Ppres.ModelOfHasCoeffs A0) := inferInstance
  letI : Algebra.FinitePresentation A0 (Ppres.ModelOfHasCoeffs A0) := inferInstance
  -- The descended model is finitely presented over `A₀`, so composition with `R → A₀` finishes.
  exact Algebra.FinitePresentation.trans R A0 (Ppres.ModelOfHasCoeffs A0)

/-- Helper for Definition 10.54.1: on the concrete principal-localization surface
`A₀ := Localization.Away (m : Q)`, the explicit `R`-algebra structure and away-lift map make
`R → A₀ → S` into a scalar tower. -/
theorem canonical_away_scalarTower_base {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    letI : Algebra (Localization.Away (m : Q)) S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R (Localization.Away (m : Q)) := inferInstance
    IsScalarTower R (Localization.Away (m : Q)) S := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  have hbase :
      (algebraMap A0 S).comp (algebraMap R A0) = algebraMap R S :=
    awayLift_base_surface_eq (R := R) (Q := Q) (S := S) (M := M) m
  -- Freeze the concrete principal-localization surface once, then turn the already proved map
  -- identity into the required scalar-tower instance.
  exact IsScalarTower.of_algebraMap_eq' (R := R) (S := A0) (A := S) hbase.symm

/-- Helper for Definition 10.54.1: after composing the canonical away surface `A₀ → S` with
`S → P`, the resulting `A₀ → P` map still extends the original `R`-algebra structure. -/
theorem canonical_away_scalarTower_comp {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {P : Type*} [CommRing P] [Algebra R P] [Algebra S P]
    [IsScalarTower R S P] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    letI : Algebra (Localization.Away (m : Q)) S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R (Localization.Away (m : Q)) := inferInstance
    letI : Algebra (Localization.Away (m : Q)) P :=
      ((algebraMap S P).comp (algebraMap (Localization.Away (m : Q)) S)).toAlgebra
    IsScalarTower R (Localization.Away (m : Q)) P := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
  have hcomp :
      (algebraMap A0 P).comp (algebraMap R A0) = algebraMap R P :=
    awayLift_comp_surface_eq (R := R) (Q := Q) (S := S) (P := P) (M := M) m
  -- The composed `A₀ → S → P` surface already knows the correct map on `R`, so the tower follows
  -- from the same `algebraMap` equality criterion.
  exact IsScalarTower.of_algebraMap_eq' (R := R) (S := A0) (A := P) hcomp.symm

/-- Helper for Definition 10.54.1: if `Q` is finitely presented over `R`, then the concrete
principal localization `Localization.Away (m : Q)` is finitely presented over `R` as well. -/
theorem canonical_away_finitePresentation_base {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra.FinitePresentation R Q] {M : Submonoid Q} (m : M) :
    Algebra.FinitePresentation R (Localization.Away (m : Q)) := by
  let A0 := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra R A0 := inferInstance
  -- This is exactly the standard finite-presentation stability under principal localization.
  exact Algebra.FinitePresentation.of_isLocalizationAway (R := R) (S := Q) (S' := A0) (m : Q)

/-- Helper for Definition 10.54.1: clearing coefficients in the intermediate finitely presented
model over `S` yields a descended finitely presented `R`-algebra whose localization is `T`. -/
theorem exists_away_descended_model_witness {T : Type w} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (hRS : EssFinitePresentation R S) (hST : EssFinitePresentation S T) :
    ∃ (P0 : Type u) (_ : CommRing P0) (_ : Algebra R P0) (_ : Algebra P0 T)
      (_ : IsScalarTower R P0 T) (_ : Algebra.FinitePresentation R P0) (N0 : Submonoid P0),
      IsLocalization N0 T := by
  rw [essFinitePresentation_iff] at hRS
  rw [essFinitePresentation_iff_exists_finitePresentation] at hST
  rcases hRS with ⟨n, I, hI, hQS, hTowerQS, M, hlocS⟩
  rcases hST with ⟨P, hPCommRing, hSP, hPT, hTowerSPT, hPfp, N, hlocT⟩
  let Q : Type u := MvPolynomial (Fin n) R ⧸ I
  letI : CommRing Q := inferInstance
  letI : Algebra Q S := hQS
  letI : IsScalarTower R Q S := hTowerQS
  letI : IsLocalization M S := hlocS
  letI : CommRing P := hPCommRing
  letI : Algebra S P := hSP
  letI : Algebra P T := hPT
  letI : IsScalarTower S P T := hTowerSPT
  letI : Algebra.FinitePresentation S P := hPfp
  letI : IsLocalization N T := hlocT
  letI : Algebra R P := ((algebraMap S P).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S P := IsScalarTower.of_algebraMap_eq' rfl
  let Ppres := Algebra.Presentation.ofFinitePresentation S P
  obtain ⟨m, hm⟩ :=
    Presentation.exists_away_hasCoeffs (R := R) (S := S) (Q := Q) (P := P)
      (Ppres := Ppres) (M := M)
  let A0 : Type u := Localization.Away (m : Q)
  letI : CommRing A0 := inferInstance
  letI : Algebra Q A0 := inferInstance
  letI : Algebra A0 S :=
    (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
  letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
  letI : IsScalarTower A0 S P := IsScalarTower.of_algebraMap_eq' rfl
  have hcoeffs : Ppres.HasCoeffs A0 := by
    -- The coefficient-clearing step already packaged the chosen denominator on this concrete away
    -- surface, so we just reuse that witness under the same local instances.
    simpa [A0] using hm
  letI : Ppres.HasCoeffs A0 := hcoeffs
  letI : Algebra R A0 := inferInstance
  letI : IsScalarTower R A0 S :=
    canonical_away_scalarTower_base (R := R) (Q := Q) (S := S) (M := M) m
  letI : IsScalarTower R A0 P :=
    canonical_away_scalarTower_comp (R := R) (Q := Q) (S := S) (P := P) (M := M) m
  letI : Algebra.FinitePresentation R Q :=
    Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin n) R) hI
  letI : Algebra.FinitePresentation R A0 :=
    canonical_away_finitePresentation_base (R := R) (Q := Q) (M := M) m
  let M0 : Submonoid A0 := Algebra.algebraMapSubmonoid A0 M
  letI : IsLocalization M0 S :=
    isLocalization_away_target_of_mem (R := R) (S := S) (Q := Q) (M := M) m
  let P0 : Type u := Ppres.ModelOfHasCoeffs A0
  letI : CommRing P0 := inferInstance
  letI : Algebra A0 P0 := inferInstance
  letI : Algebra R P0 := inferInstance
  letI : Algebra P0 P :=
    (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  letI : IsScalarTower R P0 P :=
    Presentation.isScalarTower_modelOfHasCoeffs (R := R) (S := S) (P := P)
      (Ppres := Ppres) (A0 := A0)
  letI : Algebra.FinitePresentation R P0 :=
    Presentation.finitePresentation_modelOfHasCoeffs_base (R := R) (S := S) (P := P)
      (Ppres := Ppres) (A0 := A0)
  letI : Algebra P0 T := ((algebraMap P T).comp (algebraMap P0 P)).toAlgebra
  letI : IsScalarTower P0 P T := IsScalarTower.of_algebraMap_eq' rfl
  have hRPT : (algebraMap P T).comp (algebraMap R P) = algebraMap R T := by
    -- Compare both composites with the common route `R → S → P → T`.
    ext r
    calc
      ((algebraMap P T).comp (algebraMap R P)) r
          = algebraMap P T (algebraMap R P r) := by
              rfl
      _ = algebraMap P T (((algebraMap S P).comp (algebraMap R S)) r) := by
            rw [DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S P) r]
      _ = algebraMap P T (algebraMap S P (algebraMap R S r)) := by
            rw [RingHom.comp_apply]
      _ = algebraMap S T (algebraMap R S r) := by
            -- The `S → T` structure map is the composite `S → P → T`.
            simpa [RingHom.comp_apply] using
              (DFunLike.congr_fun (IsScalarTower.algebraMap_eq S P T) (algebraMap R S r)).symm
      _ = algebraMap R T r := by
            rw [← RingHom.comp_apply]
            exact (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S T) r).symm
  have hTowerRP0T : IsScalarTower R P0 T :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := P0) (A := T) <| by
      -- First factor `R → T` through `P`, then replace `R → P` by the descended map `R → P₀ → P`.
      ext r
      calc
        algebraMap R T r = algebraMap P T (algebraMap R P r) := by
          exact (DFunLike.congr_fun hRPT r).symm
        _ = algebraMap P T (((algebraMap P0 P).comp (algebraMap R P0)) r) := by
          rw [DFunLike.congr_fun (IsScalarTower.algebraMap_eq R P0 P) r]
        _ = algebraMap P T ((algebraMap P0 P) (algebraMap R P0 r)) := by
          rw [RingHom.comp_apply]
        _ = algebraMap P0 T (algebraMap R P0 r) := by
          rfl
        _ = ((algebraMap P0 T).comp (algebraMap R P0)) r := by
          rw [RingHom.comp_apply]
  let N0 : Submonoid P0 :=
    IsLocalization.localizationLocalizationSubmodule (Algebra.algebraMapSubmonoid P0 M0) N
  have hlocP0T : IsLocalization N0 T := by
    -- Once `P₀ → P` is the descended localization and `P → T` is the original localization,
    -- the localization-of-a-localization theorem packages the final witness on `T`.
    simpa [N0, M0] using
      (Presentation.isLocalization_modelOfHasCoeffs_comp (S := S) (P := P) (Ppres := Ppres)
        (A0 := A0) (M0 := M0) (T := T) (N := N))
  -- The descended model `P₀` now carries the full source-faithful witness over `R`.
  exact ⟨P0, inferInstance, inferInstance, inferInstance, hTowerRP0T, inferInstance, N0, hlocP0T⟩

section TensorRightHelpers

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Definition 10.54.1: the canonical right-tensor map induced by `Q →ₐ[R] S`. -/
noncomputable def tensor_right_map {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T] :
    Q ⊗[R] T →ₐ[T] S ⊗[R] T :=
  show Q ⊗[R] T →ₐ[T] S ⊗[R] T from
    (Algebra.TensorProduct.commRight R T S).toAlgHom.comp <|
      (show T ⊗[R] Q →ₐ[T] T ⊗[R] S from
        Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R Q S)).comp <|
        (Algebra.TensorProduct.commRight R T Q).symm.toAlgHom

/-- Helper for Definition 10.54.1: `tensor_right_map` sends a simple tensor to the tensor of the
structure-map image. -/
@[simp]
theorem tensor_right_map_tmul {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T]
    (q : Q) (t : T) :
    tensor_right_map (R := R) (S := S) (Q := Q) (T := T) (q ⊗ₜ[R] t) =
      (algebraMap Q S q) ⊗ₜ[R] t := by
  -- Move to `T ⊗[R] Q`, tensor the structure map there, and commute back.
  simp [tensor_right_map]

/-- Helper for Definition 10.54.1: after installing the `Q ⊗[R] T`-algebra structure on
`S ⊗[R] T` via `tensor_right_map`, the resulting map still extends the original `Q`-algebra map. -/
theorem tensor_right_map_q_tower {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T] :
    (letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
      (tensor_right_map (R := R) (S := S) (Q := Q) (T := T)).toAlgebra
    (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp (algebraMap Q (Q ⊗[R] T)) =
      algebraMap Q (S ⊗[R] T)) := by
  ext q
  -- Evaluate both ring maps on `q`, then rewrite the induced algebra map by `tensor_right_map`.
  rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  simp [tensor_right_map_tmul]

/-- Helper for Definition 10.54.1: the `Q ⊗[R] T`-algebra map on `S ⊗[R] T` fixes the canonical
right tensor inclusion, which is the compatibility needed for tensor-product localization. -/
theorem tensor_right_map_includeRight_comp {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T] :
    (letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
      (tensor_right_map (R := R) (S := S) (Q := Q) (T := T)).toAlgebra
    (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) := by
  ext t
  -- Both sides send `t` to the simple tensor `1 ⊗ₜ t`.
  rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  simp [tensor_right_map_tmul]

/-- Helper for Definition 10.54.1: finite presentation survives right tensoring after commuting the
tensor factors back to the usual base-change orientation. -/
theorem finitePresentation_tensor_right {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra.FinitePresentation R Q] {T : Type w} [CommRing T] [Algebra R T] :
    Algebra.FinitePresentation T (Q ⊗[R] T) := by
  -- First use the standard base-change instance on `T ⊗[R] Q`.
  letI : Algebra.FinitePresentation T (T ⊗[R] Q) := inferInstance
  -- Then commute the tensor factors to recover the right-oriented tensor product.
  exact Algebra.FinitePresentation.equiv (Algebra.TensorProduct.commRight R T Q)

end TensorRightHelpers

/-- Helper for Definition 10.54.1: tensoring a localization witness on the right preserves the
same denominator submonoid. -/
theorem isLocalization_tensor_right_of_isLocalization {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] (M : Submonoid Q) {T : Type w} [CommRing T] [Algebra R T]
    [Algebra T (Q ⊗[R] T)] [Algebra T (S ⊗[R] T)] [Algebra (Q ⊗[R] T) (S ⊗[R] T)]
    [IsScalarTower Q (Q ⊗[R] T) (S ⊗[R] T)]
    [IsLocalization M S]
    (hcompat : (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    IsLocalization (Algebra.algebraMapSubmonoid (Q ⊗[R] T) M) (S ⊗[R] T) := by
  -- This is exactly the tensor-product localization theorem once the square is aligned.
  exact IsLocalization.tensorProduct_tensorProduct R T M S hcompat

/-- Essential finite presentation is preserved by base change. -/
instance EssFinitePresentation.baseChange (T : Type w) [CommRing T] [Algebra R T]
    [EssFinitePresentation R S] : EssFinitePresentation T (T ⊗[R] S) := by
  -- Route correction: use the original localization witness for `S`, tensor it on the right,
  -- and only then commute the tensor factors back to the target `T ⊗[R] S`.
  have hS : EssFinitePresentation R S := inferInstance
  rw [essFinitePresentation_iff] at hS
  rcases hS with ⟨n, I, hI, hQS, hTowerQS, M, hloc⟩
  let Q : Type u := MvPolynomial (Fin n) R ⧸ I
  letI : CommRing Q := inferInstance
  letI : Algebra R Q := inferInstance
  letI : Algebra Q S := hQS
  letI : IsScalarTower R Q S := hTowerQS
  let rightQ : Algebra T (Q ⊗[R] T) := Algebra.TensorProduct.rightAlgebra (R := R) (A := Q)
    (B := T)
  let rightS : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra (R := R) (A := S)
    (B := T)
  let leftQ : Algebra Q (Q ⊗[R] T) := Algebra.TensorProduct.leftAlgebra
  let leftS : Algebra Q (S ⊗[R] T) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra.FinitePresentation R Q :=
    Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin n) R) hI
  letI : Algebra.FinitePresentation T (Q ⊗[R] T) :=
    finitePresentation_tensor_right (R := R) (Q := Q) (T := T)
  let tensorQS : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
    (tensor_right_map (R := R) (S := S) (Q := Q) (T := T)).toAlgebra
  have hQtower :
      (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp (algebraMap Q (Q ⊗[R] T)) =
        algebraMap Q (S ⊗[R] T) :=
    by
      letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) := tensorQS
      letI : Algebra Q (Q ⊗[R] T) := leftQ
      letI : Algebra Q (S ⊗[R] T) := leftS
      exact tensor_right_map_q_tower (R := R) (S := S) (Q := Q) (T := T)
  have hQtowerInst :=
    @IsScalarTower.of_algebraMap_eq' Q (Q ⊗[R] T) (S ⊗[R] T)
      inferInstance inferInstance inferInstance leftQ tensorQS leftS hQtower
  have hcompat :
      (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom :=
    by
      letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) := tensorQS
      exact tensor_right_map_includeRight_comp (R := R) (S := S) (Q := Q) (T := T)
  have hlocTensor :
      IsLocalization (Algebra.algebraMapSubmonoid (Q ⊗[R] T) M) (S ⊗[R] T) :=
    @isLocalization_tensor_right_of_isLocalization R S inferInstance inferInstance inferInstance
      Q inferInstance inferInstance inferInstance inferInstance M T inferInstance inferInstance
      rightQ rightS tensorQS hQtowerInst hloc hcompat
  have hTensor : EssFinitePresentation T (S ⊗[R] T) := by
    letI : Algebra T (Q ⊗[R] T) := rightQ
    letI : Algebra T (S ⊗[R] T) := rightS
    letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) := tensorQS
    letI : IsScalarTower T (Q ⊗[R] T) (S ⊗[R] T) := inferInstance
    letI : IsLocalization (Algebra.algebraMapSubmonoid (Q ⊗[R] T) M) (S ⊗[R] T) := hlocTensor
    -- Package the base-changed quotient model before commuting the tensor factors back.
    exact EssFinitePresentation.of_isLocalization
      (R := T) (S := S ⊗[R] T) (P := Q ⊗[R] T)
      (Algebra.algebraMapSubmonoid (Q ⊗[R] T) M)
  letI : EssFinitePresentation T (S ⊗[R] T) := hTensor
  -- The target uses the left-oriented tensor product, so commute the factors at the end.
  exact EssFinitePresentation.equiv (R := T) (S := S ⊗[R] T) (T := T ⊗[R] S)
    (Algebra.TensorProduct.commRight R T S).symm

/-- Composition preserves essential finite presentation. -/
theorem EssFinitePresentation.trans {T : Type w} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (hRS : EssFinitePresentation R S) (hST : EssFinitePresentation S T) :
    EssFinitePresentation R T := by
  -- Route correction: finish the source-faithful coefficient-clearing descent first, then invoke
  -- the standard localization packaging theorem once on the descended witness.
  obtain ⟨P0, hP0CommRing, hRP0, hP0T, hTowerRP0T, hP0fp, N0, hloc⟩ :=
    exists_away_descended_model_witness (R := R) (S := S) (T := T) hRS hST
  letI : CommRing P0 := hP0CommRing
  letI : Algebra R P0 := hRP0
  letI : Algebra P0 T := hP0T
  letI : IsScalarTower R P0 T := hTowerRP0T
  letI : Algebra.FinitePresentation R P0 := hP0fp
  letI : IsLocalization N0 T := hloc
  -- The descended finitely presented model now packages the final witness directly.
  exact EssFinitePresentation.of_isLocalization (R := R) (S := T) (P := P0) N0

/-- Essentially finitely presented algebras are essentially of finite type. -/
theorem EssFinitePresentation.toEssFiniteType (h : EssFinitePresentation R S) :
    EssFiniteType R S := by
  rw [essFinitePresentation_iff_exists_finitePresentation] at h
  rcases h with ⟨P, _, _, _, _, _, M, _⟩
  -- Compose the finite-type witness `R → P` with the localization witness `P → S`.
  letI : Algebra.EssFiniteType P S := Algebra.EssFiniteType.of_isLocalization S M
  exact Algebra.EssFiniteType.comp R P S

/-- Essentially finitely presented algebras are essentially of finite type. -/
instance [EssFinitePresentation R S] : EssFiniteType R S :=
  EssFinitePresentation.toEssFiniteType R S inferInstance

end Algebra

namespace RingHom

/-- A ring homomorphism presents its target as a localization of a quotient of its source. -/
def IsLocalizationOfQuotient (f : R →+* S) : Prop :=
  ∃ (I : Ideal R) (_ : Algebra (R ⧸ I) S) (M : Submonoid (R ⧸ I))
    (_ : IsLocalization M S),
      f = (algebraMap (R ⧸ I) S).comp (Ideal.Quotient.mk I)

/-- Definition 10.54.1 (2): a ring homomorphism `R → S` is essentially of finite presentation if
the corresponding `R`-algebra is essentially of finite presentation. -/
@[stacks 00QM, algebraize Algebra.EssFinitePresentation]
def EssFinitePresentation (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.EssFinitePresentation R S

/-- Unfolding `RingHom.EssFinitePresentation` gives the standard localization-of-a-finitely-
presented-source-algebra condition. -/
theorem essFinitePresentation_iff (f : R →+* S) :
    f.EssFinitePresentation ↔
      letI := f.toAlgebra
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (_ : Algebra.FinitePresentation R P) (M : Submonoid P),
        IsLocalization M S := by
  letI := f.toAlgebra
  rw [RingHom.EssFinitePresentation]
  exact Algebra.essFinitePresentation_iff_exists_finitePresentation R S

/-- Unfolding `RingHom.EssFinitePresentation` gives the standard factorization of `f` as a
finitely presented ring map followed by a localization. -/
theorem essFinitePresentation_iff_exists_finitePresentation (f : R →+* S) :
    f.EssFinitePresentation ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (g : R →+* P) (_ : g.FinitePresentation)
        (M : Submonoid P) (_ : Algebra P S) (_ : IsLocalization M S),
        f = (algebraMap P S).comp g := by
  constructor
  · intro hf
    rw [essFinitePresentation_iff] at hf
    letI := f.toAlgebra
    rcases hf with ⟨P, _, _, _, _, hP, M, hloc⟩
    refine ⟨P, inferInstance, algebraMap R P, ?_, M, inferInstance, hloc, ?_⟩
    · rw [finitePresentation_algebraMap]
      exact hP
    · simpa [RingHom.algebraMap_toAlgebra] using (IsScalarTower.algebraMap_eq R P S)
  · rintro ⟨P, _, g, hg, M, _, hloc, hgS⟩
    subst hgS
    letI := g.toAlgebra
    letI : Algebra R S := ((algebraMap P S).comp g).toAlgebra
    have hP : Algebra.FinitePresentation R P := by
      rw [← finitePresentation_algebraMap]
      exact hg
    letI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' rfl
    rw [essFinitePresentation_iff]
    exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, hP, M, hloc⟩

@[simp]
theorem essFinitePresentation_algebraMap [Algebra R S] :
    (algebraMap R S).EssFinitePresentation ↔ Algebra.EssFinitePresentation R S := by
  rw [RingHom.EssFinitePresentation, toAlgebra_algebraMap]

namespace EssFinitePresentation

/-- The identity ring map is essentially of finite presentation. -/
theorem id (R : Type u) [CommRing R] : (RingHom.id R).EssFinitePresentation := by
  change Algebra.EssFinitePresentation R R
  infer_instance

end EssFinitePresentation

end RingHom

namespace RingHom.EssFinitePresentation

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

/-- Composition preserves essential finite presentation. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.EssFinitePresentation)
    (hg : g.EssFinitePresentation) : (g.comp f).EssFinitePresentation := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFinitePresentation.trans R S hf hg

/-- Essential finite presentation is stable under composition. -/
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.EssFinitePresentation :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg

/-- Essential finite presentation is stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.EssFinitePresentation := by
  refine .mk (stableUnderComposition.respectsIso fun {R S} _ _ e ↦ ?_) ?_
  · algebraize [e.toRingHom]
    simpa using
      (Algebra.EssFinitePresentation.equiv R R S <| AlgEquiv.ofRingEquiv (congrFun rfl))
  · introv h
    rw [essFinitePresentation_algebraMap] at h ⊢
    letI : Algebra.EssFinitePresentation R T := h
    infer_instance

end RingHom.EssFinitePresentation
