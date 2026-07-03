import Mathlib
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_107_1 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]

local notation "includeLeft" =>
  (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)
local notation "includeRight" =>
  (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)
local notation "lmul'" =>
  (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S)

theorem algebra_isEpi_iff_includeLeft_eq_includeRight :
    Algebra.IsEpi R S ↔ includeLeft = includeRight := by
  constructor
  · intro h
    ext s
    simpa using ((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp h s).symm
  · intro h
    exact (Algebra.isEpi_iff_forall_one_tmul_eq R S).mpr fun s ↦ by
      simpa using (congrArg (fun f ↦ f s) h).symm

theorem algebra_isEpi_iff_bijective_lmul :
    Algebra.IsEpi R S ↔ Function.Bijective lmul' := by
  constructor
  · intro h
    letI : Algebra.IsEpi R S := h
    refine ⟨?_, fun s ↦ ⟨1 ⊗ₜ[R] s, by simp⟩⟩
    simpa [lmul'_toLinearMap] using Algebra.injective_lift_lsmul R S S
  · rintro ⟨h, -⟩
    exact ⟨by simpa [lmul'_toLinearMap] using h⟩

theorem algebra_isEpi_iff_bijective_includeLeft :
    Algebra.IsEpi R S ↔ Function.Bijective includeLeft := by
  rw [algebra_isEpi_iff_bijective_lmul]
  constructor
  · intro h
    have hleft : Function.LeftInverse lmul' includeLeft := fun s ↦ by
      simp
    have hright : Function.RightInverse lmul' includeLeft := fun x ↦ by
      apply h.1
      simp
    exact ⟨hleft.injective, hright.surjective⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x', rfl⟩ := h.2 x
      obtain ⟨y', rfl⟩ := h.2 y
      have hxy' : x' = y' := by
        simpa using hxy
      simp [hxy']
    · intro s
      exact ⟨includeLeft s, by simp⟩

-- Proof sketch: use `Algebra.isEpi_iff_forall_one_tmul_eq` to identify epimorphy with equality of
-- the two canonical tensor-factor maps; the multiplication map is inverse to `includeLeft` once
-- these maps agree, and conversely any inverse for one of the canonical maps forces the tensor
-- product to collapse to the diagonal.
/-- Lemma 10.107.1: for a commutative semiring map `R → S` (in particular for a commutative ring
map `R → S`), the following are equivalent: `R → S` is an epimorphism, the two canonical algebra
maps `S → S ⊗[R] S` are equal, the left canonical algebra map `S → S ⊗[R] S` is bijective, and
the multiplication map `S ⊗[R] S → S` is bijective. This uses the left tensor-factor map as the
canonical representative of the source-text clause that either of the two maps `S → S ⊗[R] S` is
an isomorphism. -/
theorem algebra_isEpi_tfae_includeLeft_eq_bijective_lmul :
    List.TFAE
      [ Algebra.IsEpi R S
      , includeLeft = includeRight
      , Function.Bijective includeLeft
      , Function.Bijective lmul'
      ] := by
  tfae_have 1 ↔ 2 := algebra_isEpi_iff_includeLeft_eq_includeRight
  tfae_have 1 ↔ 3 := algebra_isEpi_iff_bijective_includeLeft
  tfae_have 1 ↔ 4 := algebra_isEpi_iff_bijective_lmul
  tfae_finish

end

/-! ### Lemma_10_107_2 (from Chap10) -/
/- Lemma 10.107.2: the composition of two epimorphisms of rings is an epimorphism. This is the
general categorical composition law for epimorphisms, specialized in later use to
`CommRingCat` or `RingCat`. -/
recall CategoryTheory.epi_comp

/-! ### Lemma_10_107_3 (from Chap10) -/
open CategoryTheory
open scoped TensorProduct

universe u

section

variable {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- Lemma 10.107.3: base change of an epimorphism of commutative rings along any map `R → R'`
remains an epimorphism. Equivalently, if `R → S` is epic, then the canonical map
`R' → R' ⊗[R] S` is again epic. -/
theorem algebra_isEpi_tensorProduct_of_isEpi [Algebra.IsEpi R S] :
    Algebra.IsEpi R' (R' ⊗[R] S) := by
  letI : Epi (CommRingCat.ofHom (algebraMap R S)) := (CommRingCat.epi_iff_epi).2 inferInstance
  exact (CommRingCat.epi_iff_epi).1 <| by
    simpa using (CommRingCat.isPushout_tensorProduct R R' S).epi_inl_of_epi

end

/-! ### Lemma_10_107_4 (from Chap10) -/
/- Lemma 10.107.4: if `A ⟶ B ⟶ C` are ring maps and the composite `A ⟶ C` is an epimorphism, then
`B ⟶ C` is an epimorphism. This is the general categorical fact that if `f ≫ g` is epic, then
`g` is epic. -/
recall CategoryTheory.epi_of_epi

/-! ### Lemma_10_107_5 (from Chap10) -/
open LocalizedModule
open Algebra.TensorProduct
open CategoryTheory
open scoped TensorProduct

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

private theorem algHom_eq_of_forall_localizationAtPrime_isEpi
    (h :
      ∀ p : PrimeSpectrum R,
        Algebra.IsEpi (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S))
    {T : Type*} [CommRing T] [Algebra R T] (f g : S →ₐ[R] T) :
    f = g := by
  ext s
  apply sub_eq_zero.mp
  refine Module.eq_zero_of_localization_maximal
    (fun P _ ↦ LocalizedModule.AtPrime P T)
    (fun P _ ↦
      (LocalizedModule.mkLinearMap P.primeCompl T : T →ₗ[R] LocalizedModule.AtPrime P T))
    (f s - g s)
    fun P _ ↦ ?_
  let A := Localization.AtPrime P
  let B := A ⊗[R] S
  let C := A ⊗[R] T
  let fA : B →ₐ[A] C :=
    { toRingHom := Algebra.TensorProduct.map (AlgHom.id R A) f
      commutes' := by
        intro a
        change (Algebra.TensorProduct.map (AlgHom.id R A) f) (a ⊗ₜ[R] (1 : S)) = a ⊗ₜ[R] (1 : T)
        simp }
  let gA : B →ₐ[A] C :=
    { toRingHom := Algebra.TensorProduct.map (AlgHom.id R A) g
      commutes' := by
        intro a
        change (Algebra.TensorProduct.map (AlgHom.id R A) g) (a ⊗ₜ[R] (1 : S)) = a ⊗ₜ[R] (1 : T)
        simp }
  have hs : fA (1 ⊗ₜ[R] s) = gA (1 ⊗ₜ[R] s) := by
    letI : Algebra.IsEpi A B := h ⟨P, inferInstance⟩
    have hB :
        (1 : B) ⊗ₜ[A] (1 ⊗ₜ[R] s) = (1 ⊗ₜ[R] s) ⊗ₜ[A] (1 : B) :=
      (Algebra.isEpi_iff_forall_one_tmul_eq A B).mp inferInstance (1 ⊗ₜ[R] s)
    have :=
      congr(Algebra.TensorProduct.lift fA gA (fun _ _ ↦ .all _ _) $hB)
    simpa [fA, gA, A, B, C] using this.symm
  have hs_map :
      (Algebra.TensorProduct.map (AlgHom.id R A) f) (1 ⊗ₜ[R] s) =
        (Algebra.TensorProduct.map (AlgHom.id R A) g) (1 ⊗ₜ[R] s) := by
    simpa [fA, gA] using hs
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at hs_map
  have hmk :
      LocalizedModule.mkLinearMap P.primeCompl T (f s) =
        LocalizedModule.mkLinearMap P.primeCompl T (g s) := by
    apply (equivTensorProduct P.primeCompl T).injective
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply]
    rw [LocalizedModule.equivTensorProduct_apply_mk, LocalizedModule.equivTensorProduct_apply_mk]
    rw [Localization.mk_one_eq_algebraMap]
    simpa using hs_map
  simpa [map_sub] using sub_eq_zero.mpr hmk

/-- Lemma 10.107.5: a ring map `R → S` is an epimorphism if and only if, for every prime ideal
`𝔭` of `R`, the localized map `R_𝔭 → S_𝔭` is an epimorphism. Here `S_𝔭` is expressed canonically
as the base change `Localization.AtPrime p.asIdeal ⊗[R] S`. -/
-- Proof sketch: if `R → S` is an epimorphism, base change along `R → R_𝔭` preserves epimorphisms,
-- using the tensor-product description of localization. Conversely, if every localized map is an
-- epimorphism, compare any two `R`-algebra maps out of `S`; their localizations agree for every
-- prime of `R`, hence they are equal by the local criterion detected on all prime localizations.
lemma algebra_isEpi_iff_forall_localizationAtPrime :
    Algebra.IsEpi R S ↔
      ∀ p : PrimeSpectrum R,
        Algebra.IsEpi (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S) := by
  constructor
  · intro h p
    letI : Algebra.IsEpi R S := h
    letI : Epi (CommRingCat.ofHom (algebraMap R S)) :=
      (CommRingCat.epi_iff_epi).2 inferInstance
    exact (CommRingCat.epi_iff_epi).1 <| by
      simpa using
        (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime p.asIdeal) S).epi_inl_of_epi
  · intro h
    refine (Algebra.isEpi_iff_forall_one_tmul_eq R S).mpr fun s ↦ ?_
    simpa using
      (congrArg (fun φ : S →ₐ[R] S ⊗[R] S ↦ φ s) <|
        algHom_eq_of_forall_localizationAtPrime_isEpi h includeLeft includeRight).symm

end

/-! ### Lemma_10_107_6 (from Chap10) -/
/- Lemma 10.107.6: a ring map is surjective if and only if it is both an epimorphism and finite.
This is exactly the canonical theorem `RingHom.surjective_iff_epi_and_finite` in
`CommRingCat`. -/
recall RingHom.surjective_iff_epi_and_finite

/-! ### Lemma_10_107_7 (from Chap10) -/
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: use the canonical faithfully-flat codescent theorem for bijectivity, reducing to
-- the base-changed map `algebraMap S (S ⊗[R] S)`. Under the epimorphism hypothesis, Lemma
-- `10.107.1` identifies this map with the canonical tensor-factor map and proves it bijective.
/-- Lemma 10.107.7: a faithfully flat epimorphism of commutative rings is bijective, hence an
isomorphism. -/
theorem faithfullyFlat_epi_bijective [Algebra.IsEpi R S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    Function.Bijective (algebraMap R S) := by
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  letI : Module.FaithfullyFlat R S := hff
  have hbase : Function.Bijective (algebraMap S (S ⊗[R] S)) := by
    simpa using
      (algebra_isEpi_iff_bijective_includeLeft.mp (inferInstance : Algebra.IsEpi R S))
  exact Module.FaithfullyFlat.bijective_of_tensorProduct hbase

end

/-! ### Lemma_10_107_8 (from Chap10) -/
universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

-- Proof sketch: split into the cases where `S` is subsingleton or nontrivial. In the nontrivial
-- case, `S` is faithfully flat as a `k`-module because `k` is a field, so the canonical
-- bijectivity theorem from Lemma `10.107.7` applies to `algebraMap k S`; then
-- `AlgEquiv.ofBijective (Algebra.ofId k S)` upgrades that bijection to a `k`-algebra equivalence.
/-- Lemma 10.107.8: if `k → S` is an epimorphism with `k` a field, then `S` is either the zero
ring or isomorphic to `k` as a `k`-algebra. -/
theorem epi_field_subsingleton_or_alg_equiv [Algebra.IsEpi k S] :
    Subsingleton S ∨ Nonempty (k ≃ₐ[k] S) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact .inl hS
  · right
    letI : Module.FaithfullyFlat k S := by
      exact
        { toFlat := inferInstance
          submodule_ne_top := by
            intro m hm
            have hm0 : m = ⊥ := by
              have hbot : (⊥ : Ideal k).IsMaximal := Ideal.bot_isMaximal
              simpa using (hbot.eq_of_le hm.ne_top bot_le).symm
            simp [hm0] }
    refine ⟨AlgEquiv.ofBijective (Algebra.ofId k S) ?_⟩
    exact faithfullyFlat_epi_bijective <| by
      rw [RingHom.faithfullyFlat_algebraMap_iff]
      infer_instance

end

/-! ### Lemma_10_107_9 (from Chap10) -/
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

/-! ### Lemma_10_107_10 (from Chap10) -/
open scoped TensorProduct
open Finsupp Submodule TensorProduct

universe u v w x y

section

variable {R : Type u} {M : Type v} {N : Type w} {I : Type x} {J : Type y}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- Proof sketch: lift the displayed tensor relation through the surjection
-- `Finsupp.linearCombination R y : (J →₀ R) →ₗ[R] N`, use right exactness of tensor product to land
-- in `LinearMap.ker (linearCombination R y) ⊗ M`, then use the generators `x` to write that lift as
-- a finitely supported family of kernel elements. Reading off the coordinates of those kernel
-- elements yields the desired coefficient matrix.
/- Layering for this item:
- `source-facing`: the finitely supported tensor relation `m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = 0`
  expressed in terms of the generating families `x` and `y`;
- `core/canonical`: right exactness of tensor product together with the free-module identifications
  `TensorProduct.finsuppScalarLeft` and `TensorProduct.finsuppScalarRight`;
- `bridge/view`: the surjective linear-combination maps attached to `x` and `y`, plus the explicit
  formulas that read a kernel family back into row and column identities.
-/
/-- Helper for Lemma 10.107.10: expand a finitely supported family into the canonical tensor on the
free module with basis indexed by the same set. -/
lemma finsuppScalarLeft_symm_apply_sum [DecidableEq J]
    (m : J →₀ M) :
    ((TensorProduct.finsuppScalarLeft R M J).symm m)
      = m.sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) := by
  -- Reduce the statement to the single-support case and extend by linearity.
  refine Finsupp.induction_linear m ?_ ?_ ?_
  · simp
  · intro m1 m2 hm1 hm2
    calc
      ((TensorProduct.finsuppScalarLeft R M J).symm (m1 + m2))
          = ((TensorProduct.finsuppScalarLeft R M J).symm m1) +
              ((TensorProduct.finsuppScalarLeft R M J).symm m2) := by
                simp
      _ = m1.sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) +
            m2.sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) := by
              rw [hm1, hm2]
      _ = (m1 + m2).sum (fun j mj ↦ Finsupp.single j (1 : R) ⊗ₜ[R] mj) := by
            symm
            rw [Finsupp.sum_add_index]
            · intro j _
              simp
            · intro j _ mj1 mj2
              simp [TensorProduct.tmul_add]
  · intro j mj
    simp [TensorProduct.finsuppScalarLeft_symm_apply_single]

/-- Helper for Lemma 10.107.10: convert a finitely supported family of coefficients into the
corresponding tensor against the free module on `I`. -/
lemma finsuppScalarRight_symm_apply_sum [DecidableEq I]
    (b : I →₀ M) :
    ((TensorProduct.finsuppScalarRight R R M I).symm b)
      = b.sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) := by
  -- As above, the linear equivalence is determined by its behavior on single-support families.
  refine Finsupp.induction_linear b ?_ ?_ ?_
  · simp
  · intro b1 b2 hb1 hb2
    calc
      ((TensorProduct.finsuppScalarRight R R M I).symm (b1 + b2))
          = ((TensorProduct.finsuppScalarRight R R M I).symm b1) +
              ((TensorProduct.finsuppScalarRight R R M I).symm b2) := by
                simp
      _ = b1.sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) +
            b2.sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) := by
              rw [hb1, hb2]
      _ = (b1 + b2).sum (fun i bi ↦ bi ⊗ₜ[R] Finsupp.single i (1 : R)) := by
            symm
            rw [Finsupp.sum_add_index]
            · intro i _
              simp
            · intro i _ bi1 bi2
              simp [add_tmul]
  · intro i bi
    simp [TensorProduct.finsuppScalarRight_symm_apply_single]

/-- Helper for Lemma 10.107.10: commuting the tensor lift through the free module on `J`
recovers the displayed finite tensor sum. -/
lemma comm_rTensor_finsuppScalarLeft_symm [DecidableEq J]
    (y : J → N) (m : J →₀ M) :
    TensorProduct.comm R N M
        (((Finsupp.linearCombination R y).rTensor M)
          ((TensorProduct.finsuppScalarLeft R M J).symm m))
      = m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) := by
  -- The free-module lift is a sum of basis vectors, so the commuted tensor map is termwise.
  refine Finsupp.induction_linear m ?_ ?_ ?_
  · simp
  · intro m1 m2 hm1 hm2
    calc
      TensorProduct.comm R N M
          (((Finsupp.linearCombination R y).rTensor M)
            ((TensorProduct.finsuppScalarLeft R M J).symm (m1 + m2)))
          = TensorProduct.comm R N M
              (((Finsupp.linearCombination R y).rTensor M)
                ((TensorProduct.finsuppScalarLeft R M J).symm m1) +
                  ((Finsupp.linearCombination R y).rTensor M)
                    ((TensorProduct.finsuppScalarLeft R M J).symm m2)) := by
                  simp
      _ = TensorProduct.comm R N M
            (((Finsupp.linearCombination R y).rTensor M)
              ((TensorProduct.finsuppScalarLeft R M J).symm m1)) +
          TensorProduct.comm R N M
            (((Finsupp.linearCombination R y).rTensor M)
              ((TensorProduct.finsuppScalarLeft R M J).symm m2)) := by
                simp
      _ = m1.sum (fun j mj ↦ mj ⊗ₜ[R] y j) + m2.sum (fun j mj ↦ mj ⊗ₜ[R] y j) := by
            rw [hm1, hm2]
      _ = (m1 + m2).sum (fun j mj ↦ mj ⊗ₜ[R] y j) := by
            symm
            rw [Finsupp.sum_add_index]
            · intro j _
              simp
            · intro j _ mj1 mj2
              exact add_tmul mj1 mj2 (y j)
  · intro j mj
    simp [TensorProduct.finsuppScalarLeft_symm_apply_single, LinearMap.rTensor_tmul]

/-- Helper for Lemma 10.107.10: a finitely supported family of kernel vectors records the row
expansions needed for the coefficient matrix. -/
lemma kernel_family_rows_raw [DecidableEq I] [DecidableEq J]
    (x : I → M) {π : (J →₀ R) →ₗ[R] N} (b : I →₀ LinearMap.ker π) :
    TensorProduct.finsuppScalarLeft R M J
        (((LinearMap.ker π).subtype.rTensor M)
          (((Finsupp.linearCombination R x).lTensor (LinearMap.ker π))
            ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b)))
      = b.sum (fun i bi ↦ (bi : J →₀ R).sum (fun j rij ↦ Finsupp.single j (rij • x i))) := by
  -- Expand the tensor via `finsuppScalarRight`, then evaluate each pure tensor explicitly.
  ext j
  rw [finsuppScalarRight_symm_apply_sum]
  simp [Finsupp.sum, LinearMap.lTensor_tmul, Finsupp.linearCombination_apply,
    LinearMap.rTensor_tmul, TensorProduct.finsuppScalarLeft_apply_tmul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro c hc
  by_cases h : c = j
  · have hs' : Finsupp.linearCombination R x (Finsupp.single i (1 : R)) = x i := by
      exact (Finsupp.linearCombination_single (R := R) (v := x) (c := (1 : R)) (a := i)).trans
        (one_smul R (x i))
    have hs : ∑ x_1 ∈ (fun₀ | i => (1 : R)).support, (fun₀ | i => (1 : R)) x_1 • x x_1 = x i := by
      change Finsupp.linearCombination R x (Finsupp.single i (1 : R)) = x i
      exact hs'
    simp [h, hs]
  · simp [h]

/-- Helper for Lemma 10.107.10: the finitely supported family of kernel vectors defines a direct
coefficient matrix by recording the `(i,j)` coefficient as the `j`th coordinate of the `i`th
kernel vector. -/
noncomputable def kernelFamilyMatrix [DecidableEq I] [DecidableEq J] (c : I →₀ J →₀ R) :
    J →₀ I →₀ R :=
  c.sum (fun i ci ↦ ci.sum (fun j rij ↦ Finsupp.single j (Finsupp.single i rij)))

/-- Helper for Lemma 10.107.10: the `j`th row of `kernelFamilyMatrix c` is the finitely supported
family of coefficients `i ↦ c i j`. -/
lemma kernel_family_matrix_row [DecidableEq I] [DecidableEq J]
    (c : I →₀ J →₀ R) (j : J) :
    kernelFamilyMatrix c j = c.sum (fun i ci ↦ Finsupp.single i (ci j)) := by
  -- Route correction: normalize the whole row before reading individual coefficients.
  ext i
  calc
    kernelFamilyMatrix c j i = c i j := by
      rw [kernelFamilyMatrix, Finsupp.sum, Finset.sum_apply', Finset.sum_apply']
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.sum, Finset.sum_apply', Finset.sum_apply']
        rw [Finset.sum_eq_single j]
        · simp
        · intro j' hj' hne
          simp [hne]
        · simp
      · intro i' hi' hne
        rw [Finsupp.sum, Finset.sum_apply', Finset.sum_apply']
        refine Finset.sum_eq_zero ?_
        intro j' hj'
        by_cases hjj : j' = j
        · subst hjj
          simp [hne]
        · simp [hjj]
      · intro hzero
        have hci : c i = 0 := by
          exact notMem_support_iff.mp hzero
        simp [hci]
    _ = (c.sum (fun i' ci ↦ Finsupp.single i' (ci j))) i := by
      rw [Finsupp.sum, Finset.sum_apply']
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' hi' hne
        simp [hne]
      · intro hzero
        have hci : c i = 0 := by
          exact notMem_support_iff.mp hzero
        simp [hci]

/-- Helper for Lemma 10.107.10: the direct matrix records exactly the original coefficient
`c i j` in row `j` and column `i`. -/
lemma kernel_family_matrix_apply [DecidableEq I] [DecidableEq J]
    (c : I →₀ J →₀ R) (j : J) (i : I) :
    kernelFamilyMatrix c j i = c i j := by
  -- Read the coefficient from the normalized row description.
  calc
    kernelFamilyMatrix c j i = (c.sum (fun i' ci ↦ Finsupp.single i' (ci j))) i := by
      simpa using
        congrArg (fun z ↦ z i) (kernel_family_matrix_row (R := R) (I := I) (J := J) c j)
    _ = c i j := by
      rw [Finsupp.sum, Finset.sum_apply']
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' hi' hne
        simp [hne]
      · intro hzero
        have hci : c i = 0 := by
          exact notMem_support_iff.mp hzero
        simp [hci]

/-- Helper for Lemma 10.107.10: forgetting the subtype on a kernel family does not change the
row sum obtained by evaluating at a fixed `j`. -/
lemma row_sum_mapRange_subtype
    (x : I → M) {π : (J →₀ R) →ₗ[R] N} (b : I →₀ LinearMap.ker π) (j : J) :
    ((Finsupp.mapRange.linearMap ((LinearMap.ker π).subtype : LinearMap.ker π →ₗ[R] J →₀ R) b).sum
      (fun i ci ↦ ci j • x i))
      = b.sum (fun i bi ↦ (bi : J →₀ R) j • x i) := by
  -- Passing from `b` to the mapped family `c` only removes the subtype wrapper on coefficients.
  simpa [Finsupp.sum_mapRange_index]

/-- Helper for Lemma 10.107.10: each row of the direct matrix gives the corresponding linear
combination of the generators `x`. -/
lemma row_linearCombination_of_kernel_family_matrix [DecidableEq I] [DecidableEq J]
    (x : I → M) (c : I →₀ J →₀ R) (j : J) :
    linearCombination R x (kernelFamilyMatrix c j) = c.sum (fun i ci ↦ ci j • x i) := by
  -- First rewrite the row in canonical `Finsupp.single` form, then evaluate `linearCombination`.
  calc
    linearCombination R x (kernelFamilyMatrix c j)
      = linearCombination R x (c.sum (fun i ci ↦ Finsupp.single i (ci j))) := by
          rw [kernel_family_matrix_row]
    _ = c.sum (fun i ci ↦ linearCombination R x (Finsupp.single i (ci j))) := by
          rw [map_finsuppSum]
    _ = c.sum (fun i ci ↦ ci j • x i) := by
          simp [Finsupp.linearCombination_single]

/-- Helper for Lemma 10.107.10: transposing twice returns the original finitely supported matrix. -/
lemma kernel_family_matrix_involutive [DecidableEq I] [DecidableEq J]
    (c : I →₀ J →₀ R) :
    kernelFamilyMatrix (R := R) (I := J) (J := I) (kernelFamilyMatrix c) = c := by
  -- Each entry survives exactly once under the second transpose.
  ext i j
  simp [kernel_family_matrix_apply]

/-- Helper for Lemma 10.107.10: the `i`th column sum of the direct matrix is the linear
combination of the family `y` with coefficients `c i`. -/
lemma column_sum_eq_linearCombination_of_kernel_family_matrix [DecidableEq I] [DecidableEq J]
    (y : J → N) (c : I →₀ J →₀ R) (i : I) :
    (kernelFamilyMatrix c).sum (fun j aij ↦ aij i • y j) = linearCombination R y (c i) := by
  -- View the `i`th column as the `i`th row of the transposed matrix, then transpose back.
  calc
    (kernelFamilyMatrix c).sum (fun j aij ↦ aij i • y j)
      = linearCombination R y
          (kernelFamilyMatrix (R := R) (I := J) (J := I) (kernelFamilyMatrix c) i) := by
            symm
            simpa using
              row_linearCombination_of_kernel_family_matrix
                (R := R) (M := N) (I := J) (J := I) y (kernelFamilyMatrix c) i
    _ = linearCombination R y (c i) := by
          rw [kernel_family_matrix_involutive]

/-- Helper for Lemma 10.107.10: rewriting the row formulas `hm` as a single finitely supported
family removes the support mismatch before taking the tensor sum. -/
lemma generator_matrix_rows_as_finsupp
    (x : I → M) (m : J →₀ M) (a : J →₀ I →₀ R)
    (hm : ∀ j, m j = linearCombination R x (a j)) :
    m = a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij)) := by
  classical
  -- Evaluate both finitely supported families at a fixed index `j`.
  ext j
  -- Only the singleton row at `j` survives when reading the `j`th coordinate.
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single j]
  · simpa using hm j
  · intro j' _ hne
    rw [Finsupp.single_apply]
    simp [hne]
  · simp

/-- Helper for Lemma 10.107.10: after rewriting `m` as a sum of singleton rows, the outer
`Finsupp.sum` collapses to the row-indexed tensor sum. -/
lemma generator_matrix_sum_single_rows
    (x : I → M) (y : J → N) (a : J →₀ I →₀ R) :
    (a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij))).sum
        (fun j mj ↦ mj ⊗ₜ[R] y j)
      = a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j) := by
  classical
  -- Flatten the outer `Finsupp.sum` and then collapse each singleton row.
  calc
    (a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij))).sum
        (fun j mj ↦ mj ⊗ₜ[R] y j)
      = a.sum (fun j aij ↦
          (Finsupp.single j (linearCombination R x aij)).sum
            (fun j' mj ↦ mj ⊗ₜ[R] y j')) := by
            rw [Finsupp.sum_sum_index]
            · intro j
              simp
            · intro j mj₁ mj₂
              exact add_tmul mj₁ mj₂ (y j)
    _ = a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          simpa using
            (Finsupp.sum_single_index
              (m := j) (r := linearCombination R x (a j))
              (h := fun j' mj ↦ mj ⊗ₜ[R] y j')
              (by simp))

/-- Helper for Lemma 10.107.10: transposing the finitely supported coefficient matrix commutes the
finite double tensor sum. -/
lemma generator_matrix_tensor_transpose [DecidableEq I] [DecidableEq J]
    (x : I → M) (y : J → N) (a : J →₀ I →₀ R) :
    a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j)
      = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
  classical
  -- Expand each row tensor into a finite double sum over the matrix coefficients.
  calc
    a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j)
      = a.sum (fun j aij ↦ aij.sum (fun i rij ↦ x i ⊗ₜ[R] (rij • y j))) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          calc
            linearCombination R x (a j) ⊗ₜ[R] y j
              = (a j).sum (fun i rij ↦ (rij • x i) ⊗ₜ[R] y j) := by
                  rw [Finsupp.linearCombination_apply]
                  simpa [Finsupp.sum] using
                    (TensorProduct.sum_tmul (R := R) (s := (a j).support)
                      (m := fun i ↦ (a j) i • x i) (n := y j))
            _ = (a j).sum (fun i rij ↦ x i ⊗ₜ[R] (rij • y j)) := by
                  refine Finsupp.sum_congr ?_
                  intro i hi
                  rw [TensorProduct.smul_tmul]
    _ = a.sum (fun j aij ↦ aij.sum (fun i rij ↦
          (Finsupp.single i (Finsupp.single j rij)).sum
            (fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col))) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          refine Finsupp.sum_congr ?_
          intro i hi
          calc
            x i ⊗ₜ[R] (a j i • y j)
              = x i ⊗ₜ[R] linearCombination R y (Finsupp.single j (a j i)) := by
                  simp [Finsupp.linearCombination_single, TensorProduct.tmul_smul]
            _ = (Finsupp.single i (Finsupp.single j (a j i))).sum
                  (fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col) := by
                  symm
                  simpa using
                    (Finsupp.sum_single_index
                      (m := i) (r := Finsupp.single j (a j i))
                      (h := fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col)
                      (by simp))
    _ = a.sum (fun j aij ↦
          (aij.sum (fun i rij ↦ Finsupp.single i (Finsupp.single j rij))).sum
            (fun i' col ↦ x i' ⊗ₜ[R] linearCombination R y col)) := by
          refine Finsupp.sum_congr ?_
          intro j hj
          -- Commute the inner finite sum so that each row becomes a finitely supported family on `I`.
          symm
          rw [Finsupp.sum_sum_index]
          · intro i'
            simp
          · intro i' col₁ col₂
            simp [TensorProduct.tmul_add, map_add]
    _ = (a.sum (fun j aij ↦ aij.sum (fun i rij ↦ Finsupp.single i (Finsupp.single j rij)))).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
          -- Commute the outer finite sum once to package the transposed matrix.
          symm
          rw [Finsupp.sum_sum_index]
          · intro i
            simp
          · intro i col₁ col₂
            simp [TensorProduct.tmul_add, map_add]
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
          simp [kernelFamilyMatrix]

/-- Helper for Lemma 10.107.10: a coefficient matrix whose rows express the `m j` in the
generators `x` and whose columns are relations among the `y j` yields a vanishing tensor sum. -/
lemma generator_matrix_sum_tmul_eq_zero
    (x : I → M) (y : J → N) (m : J →₀ M) (a : J →₀ I →₀ R)
    (hm : ∀ j, m j = linearCombination R x (a j))
    (ha : ∀ i, a.sum (fun j aij ↦ aij i • y j) = 0) :
    m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = (0 : M ⊗[R] N) := by
  classical
  -- Route correction: rewrite the entire family `m` first, so later steps never compare
  -- `m.support` with `a.support`.
  calc
    m.sum (fun j mj ↦ mj ⊗ₜ[R] y j)
      = (a.sum (fun j aij ↦ Finsupp.single j (linearCombination R x aij))).sum
          (fun j mj ↦ mj ⊗ₜ[R] y j) := by
            rw [generator_matrix_rows_as_finsupp (R := R) (M := M) (I := I) (J := J) x m a hm]
    _ = a.sum (fun j aij ↦ linearCombination R x aij ⊗ₜ[R] y j) := by
          simpa using
            generator_matrix_sum_single_rows (R := R) (M := M) (N := N) (I := I) (J := J) x y a
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] linearCombination R y col) := by
            simpa using
              generator_matrix_tensor_transpose
                (R := R) (M := M) (N := N) (I := I) (J := J) x y a
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] (a.sum (fun j aij ↦ aij i • y j))) := by
            refine Finsupp.sum_congr ?_
            intro i hi
            rw [row_linearCombination_of_kernel_family_matrix
              (R := R) (M := N) (I := J) (J := I) y a i]
    _ = (kernelFamilyMatrix (R := R) (I := J) (J := I) a).sum
          (fun i col ↦ x i ⊗ₜ[R] 0) := by
            refine Finsupp.sum_congr ?_
            intro i hi
            rw [ha i]
    _ = 0 := by
          simp

/-- Lemma 10.107.10: let `x : I → M` and `y : J → N` be generating families of the `R`-modules
`M` and `N`. For a finitely supported family `m : J →₀ M`, the tensor relation
`∑ j, m j ⊗ y j = 0` is equivalent to the existence of a finitely supported coefficient matrix
whose rows express the `m j` in terms of the generators `x i` and whose columns give relations
among the generators `y j`. -/
theorem finsupp_sum_tmul_eq_zero_iff_exists_generator_matrix
    (x : I → M) (y : J → N) (m : J →₀ M)
    (hx : span R (Set.range x) = ⊤)
    (hy : span R (Set.range y) = ⊤) :
    (m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = (0 : M ⊗[R] N)) ↔
      ∃ a : J →₀ I →₀ R,
        (∀ j, m j = linearCombination R x (a j)) ∧
          ∀ i, a.sum (fun j aij ↦ aij i • y j) = 0 := by
  classical
  constructor
  · intro hmzero
    let π : (J →₀ R) →ₗ[R] N := Finsupp.linearCombination R y
    let σ : (I →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
    -- Turn the generating hypotheses into surjectivity of the canonical linear-combination maps.
    have hπ_surj : Function.Surjective π :=
      (_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination (R := R) (v := y)).1 hy
    have hσ_surj : Function.Surjective σ :=
      (_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination (R := R) (v := x)).1 hx
    let u : (J →₀ R) ⊗[R] M := (TensorProduct.finsuppScalarLeft R M J).symm m
    -- The given tensor relation says exactly that the lifted element `u` is killed by `π.rTensor M`.
    have hu_mem_ker : u ∈ LinearMap.ker (π.rTensor M) := by
      rw [LinearMap.mem_ker]
      apply (TensorProduct.comm R N M).injective
      rw [comm_rTensor_finsuppScalarLeft_symm (R := R) (M := M) (N := N) (J := J) y m]
      exact hmzero
    -- Exactness lifts `u` to the tensor product with `ker π`.
    have hu_range : u ∈ LinearMap.range ((LinearMap.ker π).subtype.rTensor M) := by
      rw [← Function.Exact.linearMap_ker_eq (rTensor_exact M (LinearMap.exact_subtype_ker_map π) hπ_surj)]
      exact hu_mem_ker
    obtain ⟨v, hv⟩ := hu_range
    -- Surjectivity of `σ` lets us write that lift using the generators `x`.
    obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective (LinearMap.ker π) hσ_surj v
    let b : I →₀ LinearMap.ker π := TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I w
    let c : I →₀ J →₀ R :=
      Finsupp.mapRange.linearMap ((LinearMap.ker π).subtype : LinearMap.ker π →ₗ[R] J →₀ R) b
    let a : J →₀ I →₀ R := kernelFamilyMatrix c
    have hw' :
        ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b) = w := by
      simp [b]
    have hu_eq :
        ((LinearMap.ker π).subtype.rTensor M)
            ((σ.lTensor (LinearMap.ker π))
              ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b))
          = u := by
      rw [hw', hw, hv]
    -- Applying `finsuppScalarLeft` turns the lifted tensor equality into a row-wise identity.
    have hm_rows :
        m = b.sum (fun i bi ↦ (bi : J →₀ R).sum (fun j rij ↦ Finsupp.single j (rij • x i))) := by
      have hm_rows' := congrArg (TensorProduct.finsuppScalarLeft R M J) hu_eq
      calc
        m = TensorProduct.finsuppScalarLeft R M J
              (((LinearMap.ker π).subtype.rTensor M)
                ((σ.lTensor (LinearMap.ker π))
                  ((TensorProduct.finsuppScalarRight R R (LinearMap.ker π) I).symm b))) := by
                simpa [u] using hm_rows'.symm
        _ = b.sum (fun i bi ↦ (bi : J →₀ R).sum (fun j rij ↦ Finsupp.single j (rij • x i))) := by
              simpa [σ] using
                kernel_family_rows_raw (R := R) (M := M) (N := N) (I := I) (J := J) x (π := π) b
    refine ⟨a, ?_, ?_⟩
    · intro j
      -- Evaluate the row identity at `j`, then rewrite the resulting coefficient sum as the
      -- linear combination attached to the `j`th row of the direct matrix.
      have hmj := congrArg (fun z ↦ z j) hm_rows
      -- Evaluate the row-wise identity at the fixed index `j`.
      calc
        m j = b.sum (fun i bi ↦ ((bi : J →₀ R).sum
            (fun j' rij ↦ Finsupp.single j' (rij • x i))) j) := by
          simpa using hmj
        _ = b.sum (fun i bi ↦ (bi : J →₀ R) j • x i) := by
          refine Finsupp.sum_congr ?_
          intro i hi
          simpa [Finsupp.linearCombination_apply, Pi.single_apply, Finsupp.single_apply] using
            (Finsupp.linearCombination_single_index (R := R) (M := M) (c := x i) (a := j)
              (f := ((b i : LinearMap.ker π) : J →₀ R)))
        _ = c.sum (fun i ci ↦ ci j • x i) := by
          symm
          simpa [c] using row_sum_mapRange_subtype (R := R) (M := M) (I := I) (J := J) x b j
        _ = linearCombination R x (a j) := by
          simpa [a] using
            (row_linearCombination_of_kernel_family_matrix
              (R := R) (M := M) (I := I) (J := J) x c j).symm
    · intro i
      -- Read the `i`th column of the direct matrix and use that `b i` lies in `ker π`.
      have hci : linearCombination R y (c i) = 0 := by
        -- Membership of `b i` in `ker π` is exactly the vanishing column relation.
        simpa [c, π] using (b i).2
      -- Replace the explicit column sum by the corresponding linear combination in `N`.
      rw [column_sum_eq_linearCombination_of_kernel_family_matrix (R := R) (N := N) (I := I)
        (J := J) y c i]
      exact hci
  · intro h
    rcases h with ⟨a, hm, ha⟩
    -- Collapse the tensor relation by rewriting the rows, transposing the finite matrix sum once,
    -- and then applying the column relations.
    simpa using
      generator_matrix_sum_tmul_eq_zero
        (R := R) (M := M) (N := N) (I := I) (J := J) x y m a hm ha

end
