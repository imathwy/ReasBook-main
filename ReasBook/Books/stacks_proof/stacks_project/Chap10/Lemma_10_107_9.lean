import StacksProject_2024.Chap10.Lemma_10_107_8
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open scoped TensorProduct

noncomputable section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsEpi R S]

/-- Helper for Lemma 10.107.9: an epic algebra has at most one algebra map into any target. -/
private theorem algHom_eq_of_isEpi
    {T : Type*} [CommRing T] [Algebra R T] (f g : S →ₐ[R] T) :
    f = g := by
  ext s
  simpa using
    congr(Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)
      $((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp inferInstance s)).symm

/-- Helper for Lemma 10.107.9: base change of an epimorphism stays epic without a same-universe
restriction on the target ring. -/
private theorem algebra_isEpi_tensorProduct_of_isEpi_univ
    {R' : Type u} [CommRing R'] [Algebra R R'] :
    Algebra.IsEpi R' (R' ⊗[R] S) := by
  -- The tensor product is initial among `R'`-algebras equipped with an `R`-algebra map from `S`.
  refine (algebra_isEpi_iff_includeLeft_eq_includeRight (R := R') (S := R' ⊗[R] S)).mpr ?_
  apply Algebra.TensorProduct.ext
  · -- Both maps are `R'`-algebra morphisms, so they agree on the left tensor factor.
    apply AlgHom.ext
    intro x
    simpa using
      (Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := R') (A := R' ⊗[R] S) (B := R' ⊗[R] S) x)
  · -- On the right tensor factor, equality reduces to the original epimorphism `R → S`.
    exact algHom_eq_of_isEpi (R := R) (S := S)
      ((Algebra.TensorProduct.includeLeft : R' ⊗[R] S →ₐ[R'] (R' ⊗[R] S) ⊗[R'] (R' ⊗[R] S))
        |>.restrictScalars R |>.comp Algebra.TensorProduct.includeRight)
      ((Algebra.TensorProduct.includeRight : R' ⊗[R] S →ₐ[R'] (R' ⊗[R] S) ⊗[R'] (R' ⊗[R] S))
        |>.restrictScalars R |>.comp Algebra.TensorProduct.includeRight)

/-- Helper for Lemma 10.107.9: each fiber ring over a prime of `R` has at most one prime ideal. -/
private theorem fiber_primeSpectrum_subsingleton (p : PrimeSpectrum R) :
    Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) := by
  -- Base change preserves epimorphisms, so the fiber ring over `p` is again an epic algebra over
  -- the field `κ(p)`.
  let _ : Algebra.IsEpi p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    algebra_isEpi_tensorProduct_of_isEpi_univ (R := R) (R' := p.asIdeal.ResidueField)
  rcases epi_field_subsingleton_or_alg_equiv (k := p.asIdeal.ResidueField)
      (S := p.asIdeal.Fiber S) with hsub | he
  · -- If the fiber ring is the zero ring, then its prime spectrum is empty.
    let _ : IsEmpty (PrimeSpectrum (p.asIdeal.Fiber S)) :=
      PrimeSpectrum.isEmpty_iff_subsingleton.mpr hsub
    infer_instance
  · -- Otherwise the fiber ring is identified with the base field, whose spectrum is a singleton.
    let e := he.some
    have hfield : Subsingleton (PrimeSpectrum p.asIdeal.ResidueField) := by
      refine ⟨fun x y ↦ ?_⟩
      ext z
      simp [Ideal.eq_bot_of_prime (I := x.asIdeal), Ideal.eq_bot_of_prime (I := y.asIdeal)]
    let eSpec := PrimeSpectrum.comapEquiv e.toRingEquiv
    refine ⟨fun x y ↦ ?_⟩
    exact eSpec.symm.injective <| hfield.elim (eSpec.symm x) (eSpec.symm y)

/-- Helper for Lemma 10.107.9: localizing at a prime of `S` preserves epimorphy of `R → S`. -/
private theorem localRingHom_isEpi_of_isEpi (q : PrimeSpectrum S) :
    let p := q.asIdeal.under R
    let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
      (Localization.localRingHom p q.asIdeal (algebraMap R S) rfl).toAlgebra
    Algebra.IsEpi (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := by
  let p := q.asIdeal.under R
  let f : Localization.AtPrime p →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := f.toAlgebra
  -- Two `A`-algebra maps out of `S_q` are determined by their restrictions to `S`, and those
  -- restrictions are already equal because `R → S` is epic.
  refine (algebra_isEpi_iff_includeLeft_eq_includeRight
    (R := Localization.AtPrime p) (S := Localization.AtPrime q.asIdeal)).mpr ?_
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext q.asIdeal.primeCompl ?_
  let j :
      S →+* Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime p] Localization.AtPrime q.asIdeal :=
    (((Algebra.TensorProduct.includeLeft :
        Localization.AtPrime q.asIdeal →ₐ[Localization.AtPrime p]
          Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime p]
            Localization.AtPrime q.asIdeal).restrictScalars R).comp
      ((Algebra.ofId S (Localization.AtPrime q.asIdeal)).restrictScalars R)).toRingHom
  let k :
      S →+* Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime p] Localization.AtPrime q.asIdeal :=
    (((Algebra.TensorProduct.includeRight :
        Localization.AtPrime q.asIdeal →ₐ[Localization.AtPrime p]
          Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime p]
            Localization.AtPrime q.asIdeal).restrictScalars R).comp
      ((Algebra.ofId S (Localization.AtPrime q.asIdeal)).restrictScalars R)).toRingHom
  change j = k
  exact congrArg AlgHom.toRingHom <| algHom_eq_of_isEpi (R := R) (S := S)
    (((Algebra.TensorProduct.includeLeft :
        Localization.AtPrime q.asIdeal →ₐ[Localization.AtPrime p]
          Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime p]
            Localization.AtPrime q.asIdeal).restrictScalars R).comp
      ((Algebra.ofId S (Localization.AtPrime q.asIdeal)).restrictScalars R))
    (((Algebra.TensorProduct.includeRight :
        Localization.AtPrime q.asIdeal →ₐ[Localization.AtPrime p]
          Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime p]
            Localization.AtPrime q.asIdeal).restrictScalars R).comp
      ((Algebra.ofId S (Localization.AtPrime q.asIdeal)).restrictScalars R))

/-- Helper for Lemma 10.107.9: residue-field maps out of a local epic target are unique. -/
private theorem residueField_algHom_eq_of_local_algebra_isEpi
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.IsEpi A B]
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (hκ :
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) =
        IsLocalRing.ResidueField.map (algebraMap A B))
    {T : Type*} [CommRing T]
    [Algebra (IsLocalRing.ResidueField A) T]
    (g h : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A] T) :
    g = h := by
  letI : Algebra A T :=
    ((algebraMap (IsLocalRing.ResidueField A) T).comp
      (algebraMap A (IsLocalRing.ResidueField A))).toAlgebra
  let gB : B →ₐ[A] T :=
    { toRingHom := g.toRingHom.comp (IsLocalRing.residue B)
      commutes' := fun a ↦ by
        calc
          g (IsLocalRing.residue B ((algebraMap A B) a))
              = g ((algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
                  (IsLocalRing.residue A a)) := by
                    rw [hκ, IsLocalRing.ResidueField.map_residue]
          _ = algebraMap (IsLocalRing.ResidueField A) T (IsLocalRing.residue A a) := by
                simpa using g.commutes (IsLocalRing.residue A a)
          _ = algebraMap A T a := rfl }
  let hB : B →ₐ[A] T :=
    { toRingHom := h.toRingHom.comp (IsLocalRing.residue B)
      commutes' := fun a ↦ by
        calc
          h (IsLocalRing.residue B ((algebraMap A B) a))
              = h ((algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
                  (IsLocalRing.residue A a)) := by
                    rw [hκ, IsLocalRing.ResidueField.map_residue]
          _ = algebraMap (IsLocalRing.ResidueField A) T (IsLocalRing.residue A a) := by
                simpa using h.commutes (IsLocalRing.residue A a)
          _ = algebraMap A T a := rfl }
  have hBh : gB = hB := algHom_eq_of_isEpi (R := A) (S := B) gB hB
  apply AlgHom.ext
  intro x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
  exact congrArg (fun φ : B →ₐ[A] T ↦ φ b) hBh

/-- Helper for Lemma 10.107.9: a local epimorphism induces an epimorphism on residue fields. -/
private theorem residueField_map_isEpi_of_local_algebra_isEpi
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.IsEpi A B] :
    let _ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
      (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra
    Algebra.IsEpi (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  let _ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra
  refine (algebra_isEpi_iff_includeLeft_eq_includeRight
    (R := IsLocalRing.ResidueField A) (S := IsLocalRing.ResidueField B)).mpr ?_
  let left :
      IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
        IsLocalRing.ResidueField B ⊗[IsLocalRing.ResidueField A] IsLocalRing.ResidueField B :=
    Algebra.TensorProduct.includeLeft
  let right :
      IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
        IsLocalRing.ResidueField B ⊗[IsLocalRing.ResidueField A] IsLocalRing.ResidueField B :=
    Algebra.TensorProduct.includeRight
  exact residueField_algHom_eq_of_local_algebra_isEpi
    (A := A) (B := B) (hκ := rfl)
    (T := IsLocalRing.ResidueField B ⊗[IsLocalRing.ResidueField A] IsLocalRing.ResidueField B)
    left right

-- Proof sketch: identify the fiber over `p` with `Spec (κ(p) ⊗[R] S)` using
-- `PrimeSpectrum.preimageEquivFiber`. Base change preserves `Algebra.IsEpi`, so Lemma `10.107.8`
-- applied to `κ(p) → κ(p) ⊗[R] S` shows that this fiber spectrum is subsingleton.
/-- Lemma 10.107.9 (1): if `R → S` is an epimorphism of commutative rings, then the induced map
`Spec(S) → Spec(R)` is injective. -/
@[stacks 04VW]
theorem spec_comap_injective_of_isEpi :
    Function.Injective (comap (algebraMap R S)) := by
  intro q₁ q₂ hq
  let p : PrimeSpectrum R := comap (algebraMap R S) q₁
  let e := preimageEquivFiber R S p
  have hsub : Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    fiber_primeSpectrum_subsingleton p
  have hfiber :
      Subsingleton (comap (algebraMap R S) ⁻¹' ({p} : Set (PrimeSpectrum R))) :=
    let _ := hsub
    e.injective.subsingleton
  have hq₁ : comap (algebraMap R S) q₁ = p := rfl
  have hq₂ : comap (algebraMap R S) q₂ = p := by
    simpa [p] using hq.symm
  exact congr_arg Subtype.val <| hfiber.elim ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩

-- Proof sketch: the induced map `(q ∩ R).ResidueField → q.ResidueField` is again an epimorphism
-- of `((q ∩ R).ResidueField)`-algebras. Since both source and target are fields, Lemma `10.107.8`
-- forces this map to be an algebra equivalence, hence bijective.
/-- Lemma 10.107.9 (2): for `q : Spec(S)`, the canonical map
`κ(q ∩ R) → κ(q)` is bijective. -/
@[stacks 04VW]
theorem residueField_map_bijective_of_isEpi (q : PrimeSpectrum S) :
    Function.Bijective
      (Ideal.ResidueField.map (q.asIdeal.under R) q.asIdeal (algebraMap R S)
        (Ideal.over_def q.asIdeal (q.asIdeal.under R))) := by
  let p := q.asIdeal.under R
  let f : Localization.AtPrime p →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := f.toAlgebra
  let _ : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal)) := by
    simpa [f] using Localization.isLocalHom_localRingHom p q.asIdeal (algebraMap R S) rfl
  have hloc : Algebra.IsEpi (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    localRingHom_isEpi_of_isEpi (R := R) (S := S) q
  let _ : Algebra.IsEpi (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := hloc
  let _ : Algebra p.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p q.asIdeal (algebraMap R S) rfl).toAlgebra
  have hκ : Algebra.IsEpi p.ResidueField q.asIdeal.ResidueField :=
    show Algebra.IsEpi p.ResidueField q.asIdeal.ResidueField from
      residueField_map_isEpi_of_local_algebra_isEpi
  let _ : Algebra.IsEpi p.ResidueField q.asIdeal.ResidueField := hκ
  -- The induced map on residue fields is an epimorphism between fields, so it is an isomorphism.
  rcases epi_field_subsingleton_or_alg_equiv (k := p.ResidueField) (S := q.asIdeal.ResidueField)
      with hsub | he
  · exact (zero_ne_one (α := q.asIdeal.ResidueField) (hsub.elim 0 1)).elim
  · let e := he.some
    have heq :
        e.toRingHom =
          Ideal.ResidueField.map (q.asIdeal.under R) q.asIdeal (algebraMap R S)
            (Ideal.over_def q.asIdeal (q.asIdeal.under R)) := by
      exact RingHom.ext fun x : p.ResidueField ↦ by
        simpa [p] using e.commutes x
    rw [← heq]
    exact e.bijective

end
