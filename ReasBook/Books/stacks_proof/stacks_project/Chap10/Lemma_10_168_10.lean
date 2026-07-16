import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_17_7
import stacks_proof.stacks_project.Chap10.Lemma_10_123_13
import stacks_proof.stacks_project.Chap10.Theorem_10_129_4
import stacks_proof.stacks_project.Chap10.Lemma_10_130_5
import stacks_proof.stacks_project.Chap10.Lemma_10_168_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w uA uR uB uS uT

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
* primary domain: faithfully flat finitely presented ring maps and quasi-finite factorization in
  commutative algebra;
* sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `RingHom.FinitePresentation`,
  `RingHom.QuasiFinite`,
  `Algebra.FiniteType.QuasiFinite`;
* best owner abstraction:
  - `source-facing`: the existence of a factorization of `f` through a quasi-finite faithfully flat
    finitely presented map;
  - `core/canonical`: the ring-hom owner predicates `RingHom.FaithfullyFlat`,
    `RingHom.FinitePresentation`, and `RingHom.QuasiFinite`;
  - `bridge/view`: the comparison morphism `φ : S →+* S'`.
* primitive vs. derived:
  - primitive data: the target ring `S'` and the factor map `φ : S →+* S'`;
  - derived API: the induced composite `φ.comp f` and its owner properties.
-/

/-- Helper for Chap10 Lemma 10 168 10: a quasi-finite faithfully flat finitely presented map
already gives the required factorization after lifting the target ring to the theorem's universe. -/
lemma exists_ulift_factorization_of_quasiFinite
    (f : R →+* S) (hqf : f.QuasiFinite) (hff : f.FaithfullyFlat)
    (hfp : f.FinitePresentation) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (φ : S →+* S'),
      (φ.comp f).QuasiFinite ∧ (φ.comp f).FaithfullyFlat ∧
        (φ.comp f).FinitePresentation := by
  -- Work in the algebra structure induced by `f`; the `ULift` algebra structure is then the
  -- same composite through `ULift.ringEquiv.symm`.
  letI : Algebra R S := f.toAlgebra
  letI : Module.FaithfullyFlat R S := hff
  letI : Algebra.FinitePresentation R S := hfp
  let φ : S →+* ULift.{max u v, v} S := ULift.ringEquiv.symm.toRingHom
  refine ⟨ULift.{max u v, v} S, inferInstance, φ, ?_, ?_, ?_⟩
  · -- Quasi-finiteness is transported across the canonical `R`-algebra equivalence.
    rw [RingHom.QuasiFinite]
    exact (Algebra.QuasiFinite.iff_of_algEquiv
      (ULift.algEquiv (R := R) (A := S))).mpr hqf
  · -- Faithful flatness is transported across the corresponding `R`-linear equivalence.
    rw [RingHom.FaithfullyFlat]
    exact Module.FaithfullyFlat.of_linearEquiv R S
      (ULift.moduleEquiv (R := R) (M := S))
  · -- Finite presentation is invariant under the same algebra equivalence.
    rw [RingHom.FinitePresentation]
    exact Algebra.FinitePresentation.equiv (ULift.algEquiv (R := R) (A := S)).symm

/-- Helper for Chap10 Lemma 10 168 10: a ring finitely presented over `ℤ` is noetherian. -/
lemma isNoetherianRing_of_int_finitePresentation
    {A : Type w} [CommRing A] (r : ℤ →+* A) (hr : r.FinitePresentation) :
    IsNoetherianRing A := by
  -- Convert the map-level finite-presentation statement to the canonical algebra owner.
  letI : Algebra ℤ A := r.toAlgebra
  have hfp : Algebra.FinitePresentation ℤ A := by
    rw [← RingHom.finitePresentation_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using hr
  -- Finite presentation implies finite type, and finite type over `ℤ` is noetherian.
  letI : Algebra.FinitePresentation ℤ A := hfp
  exact Algebra.FiniteType.isNoetherianRing ℤ A

/-- Helper for Chap10 Lemma 10 168 10: a finite product of finite modules is finite. -/
lemma moduleFinitePi
    {ι : Type*} [Finite ι] {A : Type u} [CommRing A] (T : ι → Type v)
    [∀ i, AddCommMonoid (T i)] [∀ i, Module A (T i)]
    [∀ i, Module.Finite A (T i)] :
    Module.Finite A (∀ i, T i) := by
  classical
  -- Pass through finitely supported dependent functions, where mathlib has the finite-module
  -- instance, and then transport along the finite-support equivalence.
  letI : Fintype ι := Fintype.ofFinite ι
  have hdf : Module.Finite A (Π₀ i, T i) := inferInstance
  letI : Module.Finite A (Π₀ i, T i) := hdf
  exact Module.Finite.equiv
    (DFinsupp.linearEquivFunOnFintype : (Π₀ i, T i) ≃ₗ[A] (∀ i, T i))

/-- Helper for Chap10 Lemma 10 168 10: quasi-finiteness is preserved by finite products of
`A`-algebras. -/
lemma quasiFinitePi
    {ι : Type*} [Finite ι] {A : Type u} [CommRing A] (T : ι → Type v)
    [∀ i, CommRing (T i)] [∀ i, Algebra A (T i)]
    [∀ i, Algebra.QuasiFinite A (T i)] :
    Algebra.QuasiFinite A (∀ i, T i) := by
  classical
  -- On each fiber, tensor product commutes with the finite product; the resulting finite product
  -- of finite residue-field modules is finite.
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun P hP ↦ ?_⟩
  let e : P.Fiber (∀ i, T i) ≃ₐ[P.ResidueField] ∀ i, P.Fiber (T i) :=
    Algebra.TensorProduct.piRight A P.ResidueField P.ResidueField T
  have hfinite : Module.Finite P.ResidueField (∀ i, P.Fiber (T i)) := by
    apply moduleFinitePi
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Helper for Chap10 Lemma 10 168 10: flatness is preserved by finite products of modules. -/
lemma flatPi
    {ι : Type*} [Finite ι] {A : Type u} [CommRing A] (T : ι → Type v)
    [∀ i, AddCommGroup (T i)] [∀ i, Module A (T i)]
    [∀ i, Module.Flat A (T i)] :
    Module.Flat A (∀ i, T i) := by
  classical
  -- Flatness of a finite product is transported from the corresponding dependent finitely
  -- supported functions, where it is a direct-sum statement.
  letI : Fintype ι := Fintype.ofFinite ι
  have hdf : Module.Flat A (Π₀ i, T i) := by
    rw [Module.Flat.dfinsupp_iff]
    intro i
    infer_instance
  letI : Module.Flat A (Π₀ i, T i) := hdf
  exact Module.Flat.of_linearEquiv
    (DFinsupp.linearEquivFunOnFintype : (Π₀ i, T i) ≃ₗ[A] (∀ i, T i)).symm

/-- Helper for Chap10 Lemma 10 168 10: a finite family of factorizations whose spectrum images
cover `Spec A` gives one diagonal quasi-finite faithfully flat finitely presented factorization. -/
lemma diagonalFactorizationOfRangeCover
    {ι : Type w} [Finite ι] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (T : ι → Type (max u v w)) [∀ i, CommRing (T i)]
    (ψ : ∀ i, B →+* T i)
    (hqf : ∀ i, ((ψ i).comp f).QuasiFinite)
    (hflat : ∀ i, ((ψ i).comp f).Flat)
    (hfp : ∀ i, ((ψ i).comp f).FinitePresentation)
    (hcover : Set.univ ⊆ ⋃ i, Set.range (PrimeSpectrum.comap ((ψ i).comp f))) :
    ∃ (TProd : Type (max u v w)) (_ : CommRing TProd) (φ : B →+* TProd),
      (φ.comp f).QuasiFinite ∧ (φ.comp f).FaithfullyFlat ∧
        (φ.comp f).FinitePresentation := by
  classical
  -- Assemble the component maps into the diagonal map and identify its composite with the
  -- product algebra map over `A`.
  let φ : B →+* ∀ i, T i := Pi.ringHom ψ
  letI (i : ι) : Algebra A (T i) := ((ψ i).comp f).toAlgebra
  have hφ : φ.comp f = algebraMap A (∀ i, T i) := by
    ext x i
    simp [φ, RingHom.algebraMap_toAlgebra]
  -- Convert component ring-hom hypotheses into the algebra/module instances consumed by the
  -- finite-product lemmas.
  have hqfAlg (i : ι) : Algebra.QuasiFinite A (T i) := by
    rw [← RingHom.quasiFinite_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using hqf i
  have hflatAlg (i : ι) : Module.Flat A (T i) := by
    rw [← RingHom.flat_algebraMap_iff]
    simpa [RingHom.algebraMap_toAlgebra] using hflat i
  have hfpAlg (i : ι) : Algebra.FinitePresentation A (T i) := by
    rw [← RingHom.finitePresentation_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using hfp i
  letI (i : ι) : Algebra.QuasiFinite A (T i) := hqfAlg i
  letI (i : ι) : Module.Flat A (T i) := hflatAlg i
  letI (i : ι) : Algebra.FinitePresentation A (T i) := hfpAlg i
  refine ⟨∀ i, T i, inferInstance, φ, ?_, ?_, ?_⟩
  · -- Quasi-finiteness is now the finite-product lemma after rewriting the composite.
    rw [hφ, RingHom.quasiFinite_algebraMap]
    exact quasiFinitePi T
  · -- Faithful flatness is flatness plus surjectivity on spectra; the cover hypothesis supplies
    -- the surjectivity after rewriting the spectrum of a finite product.
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    constructor
    · rw [hφ, RingHom.flat_algebraMap_iff]
      exact flatPi T
    · have hcomp (i : ι) : (Pi.evalRingHom T i).comp (φ.comp f) = (ψ i).comp f := by
        ext x
        simp [φ]
      have hcover' :
          Set.univ ⊆
            ⋃ i, Set.range (PrimeSpectrum.comap ((Pi.evalRingHom T i).comp (φ.comp f))) := by
        simpa [hcomp] using hcover
      rw [PrimeSpectrum.iUnion_range_comap_comp_evalRingHom (f := φ.comp f)] at hcover'
      intro x
      exact hcover' trivial
  · -- Finite presentation for a finite product is already available as an algebra instance.
    rw [hφ, RingHom.finitePresentation_algebraMap]
    infer_instance

/-- Helper for Chap10 Lemma 10 168 10: a flat finitely presented ring map has open image on
prime spectra. -/
lemma isOpen_range_comap_of_flat_finitePresentation
    {A T : Type*} [CommRing A] [CommRing T] (f : A →+* T)
    (hflat : f.Flat) (hfp : f.FinitePresentation) :
    IsOpen (Set.range (PrimeSpectrum.comap f)) := by
  -- Move to the algebra spelling where mathlib's going-down open-map theorem applies.
  letI : Algebra A T := f.toAlgebra
  have hflatAlg : Module.Flat A T := by
    rw [← RingHom.flat_algebraMap_iff]
    simpa [RingHom.algebraMap_toAlgebra] using hflat
  have hfpAlg : Algebra.FinitePresentation A T := by
    rw [← RingHom.finitePresentation_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using hfp
  letI : Module.Flat A T := hflatAlg
  letI : Algebra.FinitePresentation A T := hfpAlg
  letI : Algebra.HasGoingDown A T := Algebra.HasGoingDown.of_flat
  -- The open-map theorem gives openness of the whole range after rewriting the algebra map.
  simpa [RingHom.algebraMap_toAlgebra] using
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := A) (S := T)).isOpen_range

/-- Helper for Chap10 Lemma 10 168 10: primewise local factorizations with open spectrum
images admit a finite subcover of `Spec A`. -/
lemma finiteCoveringFactorizationsOfPrimewiseWitnesses
    {A B : Type w} [CommRing A] [CommRing B] (g : A →+* B)
    (hloc : ∀ p : PrimeSpectrum A,
      ∃ (T : Type w) (_ : CommRing T) (ψ : B →+* T),
        ((ψ.comp g).QuasiFinite) ∧
          ((ψ.comp g).Flat) ∧
          ((ψ.comp g).FinitePresentation) ∧
          p ∈ Set.range (PrimeSpectrum.comap (ψ.comp g))) :
    ∃ (ι : Type w) (_ : Finite ι) (T : ι → Type w) (_hT : ∀ i, CommRing (T i))
      (ψ : ∀ i, B →+* T i),
      (∀ i, ((ψ i).comp g).QuasiFinite) ∧
        (∀ i, ((ψ i).comp g).Flat) ∧
        (∀ i, ((ψ i).comp g).FinitePresentation) ∧
        Set.univ ⊆ ⋃ i, Set.range (PrimeSpectrum.comap ((ψ i).comp g)) := by
  classical
  -- Choose one local factorization over each prime and name its image in `Spec A`.
  let Tof : PrimeSpectrum A → Type w := fun p ↦ Classical.choose (hloc p)
  let hTof : ∀ p : PrimeSpectrum A, CommRing (Tof p) := fun p ↦
    Classical.choose (Classical.choose_spec (hloc p))
  let ψof : ∀ p : PrimeSpectrum A, B →+* Tof p := fun p ↦ by
    unfold Tof
    letI : CommRing (Classical.choose (hloc p)) :=
      Classical.choose (Classical.choose_spec (hloc p))
    exact Classical.choose (Classical.choose_spec (Classical.choose_spec (hloc p)))
  have hspec : ∀ p : PrimeSpectrum A,
      ((ψof p).comp g).QuasiFinite ∧
        ((ψof p).comp g).Flat ∧
        ((ψof p).comp g).FinitePresentation ∧
        p ∈ Set.range (PrimeSpectrum.comap ((ψof p).comp g)) := by
    intro p
    dsimp [ψof]
    unfold Tof
    letI : CommRing (Classical.choose (hloc p)) :=
      Classical.choose (Classical.choose_spec (hloc p))
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hloc p)))
  have hUo : ∀ p : PrimeSpectrum A,
      IsOpen (Set.range (PrimeSpectrum.comap ((ψof p).comp g))) := by
    intro p
    letI : CommRing (Tof p) := hTof p
    -- Each chosen image is open because the corresponding composite is flat and finitely
    -- presented.
    exact isOpen_range_comap_of_flat_finitePresentation
      ((ψof p).comp g) (hspec p).2.1 (hspec p).2.2.1
  have hcover : Set.univ ⊆ ⋃ p : PrimeSpectrum A,
      Set.range (PrimeSpectrum.comap ((ψof p).comp g)) := by
    intro x hx
    -- The witness chosen at `x` contains `x`, so the chosen images cover all of `Spec A`.
    exact Set.mem_iUnion.mpr ⟨x, (hspec x).2.2.2⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (PrimeSpectrum A))).elim_finite_subcover
      (fun p : PrimeSpectrum A ↦ Set.range (PrimeSpectrum.comap ((ψof p).comp g)))
      hUo hcover
  -- Reindex the finite subcover by the finite subtype of selected primes.
  let ι : Type w := {p : PrimeSpectrum A // p ∈ t}
  have hι : Finite ι := inferInstance
  let Tι : ι → Type w := fun i ↦ Tof i.1
  let hTι : ∀ i : ι, CommRing (Tι i) := fun i ↦ hTof i.1
  let ψι : ∀ i : ι, B →+* Tι i := fun i ↦ by
    dsimp [Tι]
    exact ψof i.1
  refine ⟨ι, hι, Tι, hTι, ψι, ?_, ?_, ?_, ?_⟩
  · -- The algebraic properties are inherited from the chosen primewise witnesses.
    intro i
    dsimp [ψι, Tι]
    exact (hspec i.1).1
  · intro i
    dsimp [ψι, Tι]
    exact (hspec i.1).2.1
  · intro i
    dsimp [ψι, Tι]
    exact (hspec i.1).2.2.1
  · -- The compactness subcover transfers directly to the finite subtype indexing.
    intro x hx
    have hx' := ht hx
    rcases Set.mem_iUnion.mp hx' with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hpt, hxU⟩
    exact Set.mem_iUnion.mpr ⟨⟨p, hpt⟩, hxU⟩

/-- Helper for Chap10 Lemma 10 168 10: in each fiber of a flat finitely presented map with
surjective spectrum map, one can choose a closed point in the Cohen-Macaulay fiber locus. -/
lemma existsClosedCohenMacaulayFiberPointOver
    {A B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FinitePresentation A B] [Module.Flat A B]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    (p : PrimeSpectrum A) :
    ∃ q : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap A B) q = p ∧
        q ∈ PrimeSpectrum.cohenMacaulayFiberLocus A B ∧
          (fiberPrimeAt A B q).asIdeal.IsMaximal := by
  classical
  let F : Type w :=
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' ({p} : Set (PrimeSpectrum A))
  let e : F ≃ₜ PrimeSpectrum (p.asIdeal.Fiber B) :=
    PrimeSpectrum.preimageHomeomorphFiber A B p
  let V : Set F :=
    ((↑) : F → PrimeSpectrum B) ⁻¹' PrimeSpectrum.cohenMacaulayFiberLocus A B
  have hCM :=
    isOpen_and_fiberwiseDense_cohenMacaulayFiberLocus_of_finitePresentation_flat
      (R := A) (S := B)
  have hVdense : Dense V := by
    simpa [F, V] using hCM.2 p
  have hVopen : IsOpen V :=
    hCM.1.preimage continuous_subtype_val
  have hF_nonempty : Nonempty F := by
    -- Faithful flatness supplies a point in the set-theoretic fiber over `p`.
    obtain ⟨q, hq⟩ := hsurj p
    exact ⟨⟨q, by simpa using hq⟩⟩
  have hVne : V.Nonempty := by
    -- Density of the Cohen-Macaulay locus in the nonempty fiber makes the open fiber locus
    -- nonempty.
    letI : Nonempty F := hF_nonempty
    exact hVdense.nonempty
  let U : Set (PrimeSpectrum (p.asIdeal.Fiber B)) := e '' V
  have hUopen : IsOpen U :=
    e.isOpenMap _ hVopen
  have hUne : U.Nonempty :=
    hVne.image e
  haveI : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber B) := inferInstance
  letI : IsJacobsonRing (p.asIdeal.Fiber B) :=
    isJacobsonRing_of_finiteType (A := p.asIdeal.ResidueField)
  obtain ⟨m, hmU, hmclosed⟩ :=
    PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing U hUopen hUne
  have hmmax : m.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mp hmclosed
  obtain ⟨x, hxV, hxm⟩ := hmU
  rcases x with ⟨q, hqmem⟩
  have hq : PrimeSpectrum.comap (algebraMap A B) q = p := by
    simpa using hqmem
  -- Transport the maximal closed point back through the fiber homeomorphism; after rewriting the
  -- fiber equality, this is the public `fiberPrimeAt` attached to `q`.
  subst p
  refine ⟨q, rfl, hxV, ?_⟩
  subst m
  simpa [e, F, fiberPrimeAt] using hmmax

/-- Helper for Chap10 Lemma 10 168 10: a prime of the final factor ring lying over the chosen
prime of `B` witnesses that the base prime lies in the image of the composite spectrum map. -/
lemma mem_range_comap_comp_of_comap_eq
    {A B T : Type w} [CommRing A] [CommRing B] [CommRing T]
    (f : A →+* B) (ψ : B →+* T)
    {p : PrimeSpectrum A} {q : PrimeSpectrum B} {Q : PrimeSpectrum T}
    (hqmap : PrimeSpectrum.comap f q = p)
    (hQmap : PrimeSpectrum.comap ψ Q = q) :
    p ∈ Set.range (PrimeSpectrum.comap (ψ.comp f)) := by
  -- Compose the two comap equalities and then package the final prime as the range witness.
  refine Set.mem_range.mpr ⟨Q, ?_⟩
  calc
    PrimeSpectrum.comap (ψ.comp f) Q = PrimeSpectrum.comap f (PrimeSpectrum.comap ψ Q) := by
      rw [PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap f q := by
      rw [hQmap]
    _ = p := hqmap

/-- Helper for Chap10 Lemma 10 168 10: quotienting by an ideal contained in a prime produces a
prime of the quotient whose contraction is the original prime. -/
lemma quotientPrimeOver_of_le
    {B : Type w} [CommRing B] {I : Ideal B} (q : PrimeSpectrum B)
    (hI : I ≤ q.asIdeal) :
    ∃ Q : PrimeSpectrum (B ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = q := by
  -- Use the standard homeomorphism between `Spec(B ⧸ I)` and the closed set `V(I)`.
  let Q : PrimeSpectrum (B ⧸ I) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨q, hI⟩
  refine ⟨Q, ?_⟩
  -- The forward direction of that homeomorphism records exactly the quotient contraction.
  change ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I) Q).1 = q
  simp [Q]

/-- Helper for Chap10 Lemma 10 168 10: quotienting a finitely presented algebra by a
list-generated ideal is still finitely presented over the base. -/
lemma finitePresentation_quotient_ofList
    {A B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] (fs : List B) :
    Algebra.FinitePresentation A (B ⧸ Ideal.ofList fs) := by
  -- A list-generated ideal is finitely generated, so the standard quotient theorem applies.
  exact Algebra.FinitePresentation.quotient
    (I := Ideal.ofList fs) (Submodule.fg_span (List.finite_toSet fs))

/-- Helper for Chap10 Lemma 10 168 10: the quotient map is compatible with the inherited
`A`-algebra structure. -/
lemma quotient_mk_comp_algebraMap
    {A B : Type w} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) :
    (Ideal.Quotient.mk I).comp (algebraMap A B) = algebraMap A (B ⧸ I) := by
  -- The quotient algebra structure is defined through this composite.
  rfl

/-- Helper for Chap10 Lemma 10 168 10: a prime of `B ⧸ I` lying over a fixed prime `q` of `B`
is unique. -/
lemma quotientPrime_eq_of_comap_eq
    {B : Type w} [CommRing B] {I : Ideal B} {q : PrimeSpectrum B}
    {Q Q' : PrimeSpectrum (B ⧸ I)}
    (hQ : PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = q)
    (hQ' : PrimeSpectrum.comap (Ideal.Quotient.mk I) Q' = q) :
    Q = Q' := by
  -- The quotient-spectrum homeomorphism identifies primes of `B ⧸ I` with primes of `B`
  -- containing `I`; over a fixed underlying prime, the subtype point is unique.
  let e := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I
  apply e.injective
  apply Subtype.ext
  change PrimeSpectrum.comap (Ideal.Quotient.mk I) Q =
    PrimeSpectrum.comap (Ideal.Quotient.mk I) Q'
  rw [hQ, hQ']

/-- Helper for Chap10 Lemma 10 168 10: the closed Cohen-Macaulay fiber point admits a quotient
prime model at the unique quotient prime over `q`. -/
lemma existsQuotientPrimeLocalModelAtClosedCohenMacaulayFiberPoint
    {A B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FinitePresentation A B] [Module.Flat A B]
    {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    (hqmap : PrimeSpectrum.comap (algebraMap A B) q = p)
    (hqCM : q ∈ PrimeSpectrum.cohenMacaulayFiberLocus A B)
    (hqclosed : (fiberPrimeAt A B q).asIdeal.IsMaximal) :
    ∃ fs : List B,
      Ideal.ofList fs ≤ q.asIdeal ∧
        ∃ Q : PrimeSpectrum (B ⧸ Ideal.ofList fs),
          PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.ofList fs)) Q = q ∧
            Q ∈ Module.flatOverBaseLocus A (B ⧸ Ideal.ofList fs) (B ⧸ Ideal.ofList fs) ∧
              Algebra.QuasiFiniteAt A Q.asIdeal := by
  -- TODO: construct a full regular sequence in `fiberLocalRingAt A B q`, clear denominators to
  -- a global list in `B` lying in `q.asIdeal`, then apply Lemma 10.128.6 for flatness and
  -- Lemma 10.124.2 for quasi-finiteness at the resulting quotient prime.
  sorry

/-- Helper for Chap10 Lemma 10 168 10: the closed Cohen-Macaulay fiber point admits a direct
quotient model by global generators whose primes over `q` are flat over `A` and quasi-finite at
the chosen point. -/
lemma existsDirectQuotientLocalModelAtClosedCohenMacaulayFiberPoint
    {A B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FinitePresentation A B] [Module.Flat A B]
    {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    (hqmap : PrimeSpectrum.comap (algebraMap A B) q = p)
    (hqCM : q ∈ PrimeSpectrum.cohenMacaulayFiberLocus A B)
    (hqclosed : (fiberPrimeAt A B q).asIdeal.IsMaximal) :
    ∃ fs : List B,
      Ideal.ofList fs ≤ q.asIdeal ∧
        ∀ Q : PrimeSpectrum (B ⧸ Ideal.ofList fs),
          PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.ofList fs)) Q = q →
            Q ∈ Module.flatOverBaseLocus A (B ⧸ Ideal.ofList fs) (B ⧸ Ideal.ofList fs) ∧
              Algebra.QuasiFiniteAt A Q.asIdeal := by
  -- Route correction: separate the source construction of one quotient prime from the elementary
  -- fact that the quotient prime lying over `q` is unique.
  obtain ⟨fs, hfsle, Q₀, hQ₀, hQ₀flat, hQ₀qf⟩ :=
    existsQuotientPrimeLocalModelAtClosedCohenMacaulayFiberPoint
      (A := A) (B := B) hqmap hqCM hqclosed
  refine ⟨fs, hfsle, ?_⟩
  intro Q hQ
  -- Any requested quotient prime is the same point as the constructed one, so the source
  -- properties transfer by rewriting.
  have hQQ₀ : Q = Q₀ :=
    quotientPrime_eq_of_comap_eq (I := Ideal.ofList fs) hQ hQ₀
  subst Q
  exact ⟨hQ₀flat, hQ₀qf⟩

/-- Helper for Chap10 Lemma 10 168 10: the regular-sequence quotient construction at a closed
Cohen-Macaulay fiber point gives a finite-presentation model with one prime over `q` where the
map is locally flat and quasi-finite. -/
lemma existsLocalModelAtClosedCohenMacaulayFiberPoint
    {A B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FinitePresentation A B] [Module.Flat A B]
    {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    (hqmap : PrimeSpectrum.comap (algebraMap A B) q = p)
    (hqCM : q ∈ PrimeSpectrum.cohenMacaulayFiberLocus A B)
    (hqclosed : (fiberPrimeAt A B q).asIdeal.IsMaximal) :
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra A C) (χ : B →+* C)
      (Q : PrimeSpectrum C),
      χ.comp (algebraMap A B) = algebraMap A C ∧
        PrimeSpectrum.comap χ Q = q ∧
        Algebra.FinitePresentation A C ∧
        Q ∈ Module.flatOverBaseLocus A C C ∧
        Algebra.QuasiFiniteAt A Q.asIdeal := by
  -- Route correction: the final witness is now the direct quotient by global numerators; quotient
  -- prime construction and finite presentation are handled by the small adapters above.
  obtain ⟨fs, hfsle, hprops⟩ :=
    existsDirectQuotientLocalModelAtClosedCohenMacaulayFiberPoint
      (A := A) (B := B) hqmap hqCM hqclosed
  let C : Type w := B ⧸ Ideal.ofList fs
  letI : CommRing C := inferInstance
  letI : Algebra A C := inferInstance
  let χ : B →+* C := Ideal.Quotient.mk (Ideal.ofList fs)
  obtain ⟨Q, hQχ⟩ := quotientPrimeOver_of_le (I := Ideal.ofList fs) q hfsle
  have hQprops :
      Q ∈ Module.flatOverBaseLocus A C C ∧ Algebra.QuasiFiniteAt A Q.asIdeal := by
    -- The direct-quotient helper supplies the local flatness and quasi-finiteness for the
    -- quotient prime just constructed.
    simpa [C, χ] using hprops Q hQχ
  refine ⟨C, inferInstance, inferInstance, χ, Q, ?_, ?_, ?_, ?_, ?_⟩
  · -- The quotient map is the inherited `A`-algebra map on the quotient.
    exact quotient_mk_comp_algebraMap (A := A) (B := B) (Ideal.ofList fs)
  · -- The quotient prime was chosen to contract back to `q`.
    simpa [χ] using hQχ
  · -- Finite presentation survives quotienting by the finite list of global generators.
    exact finitePresentation_quotient_ofList (A := A) (B := B) fs
  · -- Local flatness is one of the properties of the quotient prime.
    exact hQprops.1
  · -- Quasi-finiteness at the quotient prime is the other property supplied by the helper.
    exact hQprops.2

/-- Helper for Chap10 Lemma 10 168 10: quasi-finiteness at a prime is transported through a
target localization whose contracted prime is the given one. -/
private lemma quasiFiniteAt_of_localization_comap
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C] (M : Submonoid C)
    (q : Ideal C) [q.IsPrime] (Q : Ideal (Localization M)) [Q.IsPrime]
    (hcomap : Ideal.comap (algebraMap C (Localization M)) Q = q)
    (hq : Algebra.QuasiFiniteAt A q) :
    Algebra.QuasiFiniteAt A Q := by
  -- Compare the two stalks by the canonical iterated-localization equivalence, then rewrite the
  -- source prime to the requested contracted prime.
  have hiff :
      Algebra.QuasiFinite A
          (Localization.AtPrime (Ideal.comap (algebraMap C (Localization M)) Q)) ↔
        Algebra.QuasiFinite A (Localization.AtPrime Q) := by
    exact Algebra.QuasiFinite.iff_of_algEquiv
      ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := M) Q).restrictScalars A)
  subst q
  exact hiff.mp hq

/-- Helper for Chap10 Lemma 10 168 10: in a finite-type fiber, the quasi-finite-at locus is
finite. -/
private lemma finiteQuasiFiniteAtFiberPrimes
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (p : PrimeSpectrum A) :
    Set.Finite { Q : PrimeSpectrum (p.asIdeal.Fiber C) |
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal } := by
  -- A finite-type fiber over the residue field is noetherian, so a compact discrete
  -- quasi-finite-at subspace is finite.
  let T : Set (PrimeSpectrum (p.asIdeal.Fiber C)) :=
    { Q | Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal }
  have hnoeth : IsNoetherianRing (p.asIdeal.Fiber C) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  letI : IsNoetherianRing (p.asIdeal.Fiber C) := hnoeth
  have hcompact : IsCompact T :=
    TopologicalSpace.NoetherianSpace.isCompact T
  have hdiscrete : IsDiscrete T := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro Q hQ
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal := hQ
    refine ⟨{Q}, ?_, ?_⟩
    · exact (Algebra.QuasiFiniteAt.isClopen_singleton (R := p.asIdeal.ResidueField) Q).isOpen
    · ext Q'
      constructor
      · intro h
        exact h.1
      · intro h
        subst Q'
        exact ⟨rfl, hQ⟩
  simpa [T] using hcompact.finite hdiscrete

/-- Helper for Chap10 Lemma 10 168 10: over a fixed base prime, only finitely many primes are
quasi-finite-at. -/
private lemma finiteQuasiFinitePrimesOver
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (p : Ideal A) [p.IsPrime] :
    Set.Finite { q : p.primesOver C | Algebra.QuasiFiniteAt A q.1 } := by
  -- Transfer the finite quasi-finite-at locus in the fiber across the canonical primes-over
  -- equivalence.
  let e := PrimeSpectrum.primesOverOrderIsoFiber A C p
  let T : Set (p.primesOver C) := { q | Algebra.QuasiFiniteAt A q.1 }
  have hImage : Set.Finite (e '' T) := by
    refine (finiteQuasiFiniteAtFiberPrimes (A := A) (C := C)
      (p := ⟨p, inferInstance⟩)).subset ?_
    intro Q hQ
    rcases hQ with ⟨q, hqT, rfl⟩
    have hcomap : (e q).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.1 := by
      change ((PrimeSpectrum.primesOverOrderIsoFiber A C p).symm (e q)).1 = q.1
      simp [e]
    letI : Algebra.QuasiFiniteAt A q.1 := hqT
    exact Algebra.QuasiFiniteAt.baseChange q.1 (e q).asIdeal hcomap.symm
  have hinj : Set.InjOn e T := by
    intro x _ y _ hxy
    exact e.injective hxy
  exact hImage.of_finite_image hinj

/-- Helper for Chap10 Lemma 10 168 10: a finite-type algebra is quasi-finite if it is
quasi-finite at every target prime. -/
private lemma quasiFinite_of_forall_quasiFiniteAt
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (h : ∀ Q : PrimeSpectrum C, Algebra.QuasiFiniteAt A Q.asIdeal) :
    Algebra.QuasiFinite A C := by
  -- Use the finite-fiber characterization of quasi-finiteness and the preceding primewise
  -- finiteness lemma.
  rw [Algebra.QuasiFinite.iff_finite_primesOver]
  intro p hp
  letI : p.IsPrime := hp
  have hfin : Set.Finite { q : p.primesOver C | Algebra.QuasiFiniteAt A q.1 } :=
    finiteQuasiFinitePrimesOver (A := A) (C := C) p
  have hset :
      ({ q : p.primesOver C | Algebra.QuasiFiniteAt A q.1 } : Set (p.primesOver C)) =
        Set.univ := by
    ext q
    simp [h ⟨q.1, inferInstance⟩]
  rw [hset] at hfin
  simpa [Set.image_univ] using hfin.image (fun q : p.primesOver C => (q : Ideal C))

/-- Helper for Chap10 Lemma 10 168 10: a flat localized stalk over `A` gives the flat
local-ring map used by target-prime flatness descent for an away localization. -/
private lemma flat_localRingHom_of_flat_localizationAway_comap
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C] (g : C)
    (J : Ideal (Localization.Away g)) [J.IsPrime]
    (hflat : Module.Flat A
      (Localization.AtPrime (Ideal.comap (algebraMap C (Localization.Away g)) J))) :
    (Localization.localRingHom (Ideal.comap (algebraMap A (Localization.Away g)) J) J
      (algebraMap A (Localization.Away g)) rfl).Flat := by
  -- Cache the stalk-flatness instance in this small bridge so the main away-flatness proof does
  -- not repeatedly search through the iterated-localization instance graph.
  rw [RingHom.Flat]
  let e :=
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Submonoid.powers g) J).restrictScalars A
  have hflatTargetA : Module.Flat A (Localization.AtPrime J) := by
    letI : Module.Flat A
        (Localization.AtPrime (Ideal.comap (algebraMap C (Localization.Away g)) J)) := hflat
    exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  rw [Module.flat_iff_of_isLocalization
    (S := Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away g)) J))
    (p := (Ideal.comap (algebraMap A (Localization.Away g)) J).primeCompl)]
  exact hflatTargetA

/-- Helper for Chap10 Lemma 10 168 10: if a basic open is contained in the quasi-finite-at locus,
then the corresponding away localization is quasi-finite over the base. -/
private lemma quasiFinite_localizationAway_of_basicOpen_subset_quasiFiniteAt
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (g : C)
    (hbasic : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
      { Q : PrimeSpectrum C | Algebra.QuasiFiniteAt A Q.asIdeal }) :
    Algebra.QuasiFinite A (Localization.Away g) := by
  -- Every prime of `C_g` contracts to a point of `D(g)`, where the pointwise quasi-finiteness
  -- hypothesis lives; then global quasi-finiteness follows from the previous helper.
  apply quasiFinite_of_forall_quasiFiniteAt (A := A) (C := Localization.Away g)
  intro Q
  let q : PrimeSpectrum C := PrimeSpectrum.comap (algebraMap C (Localization.Away g)) Q
  have hqbasic : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) := by
    have hRange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away g))) := by
      exact ⟨Q, rfl⟩
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hRange
  have hq : Algebra.QuasiFiniteAt A q.asIdeal :=
    hbasic hqbasic
  have hcomap : Ideal.comap (algebraMap C (Localization.Away g)) Q.asIdeal = q.asIdeal := by
    exact (PrimeSpectrum.comap_asIdeal (f := algebraMap C (Localization.Away g)) Q).symm
  exact quasiFiniteAt_of_localization_comap
    (A := A) (M := Submonoid.powers g) q.asIdeal Q.asIdeal hcomap hq

/-- Helper for Chap10 Lemma 10 168 10: if a basic open is contained in the flat-over-base locus,
then the corresponding away localization is flat over the base. -/
private lemma flat_localizationAway_of_basicOpen_subset_flatOverBaseLocus
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FinitePresentation A C]
    (g : C)
    (hbasic : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
      Module.flatOverBaseLocus A C C) :
    Module.Flat A (Localization.Away g) := by
  -- Flatness of `A → C_g` is checked after localizing at every target prime; each such prime
  -- comes from a point of `D(g)`, where the flat-over-base locus gives the needed flat stalk.
  rw [← RingHom.flat_algebraMap_iff]
  refine RingHom.Flat.ofLocalizationPrime (algebraMap A (Localization.Away g)) ?_
  intro J hJ
  letI : J.IsPrime := hJ
  let Q : PrimeSpectrum (Localization.Away g) := ⟨J, hJ⟩
  let q : PrimeSpectrum C := PrimeSpectrum.comap (algebraMap C (Localization.Away g)) Q
  have hqbasic : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) := by
    have hRange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away g))) := by
      exact ⟨Q, rfl⟩
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hRange
  have hflatq : Module.Flat A (Localization.AtPrime q.asIdeal) := by
    exact (Module.mem_flatOverBaseLocus A C C q).1 (hbasic hqbasic)
  exact flat_localRingHom_of_flat_localizationAway_comap (A := A) (C := C) g J hflatq

/-- Helper for Chap10 Lemma 10 168 10: a finite-presentation algebra that is flat and
quasi-finite at one prime can be localized around that prime so the resulting composite is
globally flat, quasi-finite, and finitely presented. -/
lemma existsLocalizationWithGlobalFlatAndQuasiFinite
    {A C : Type w} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.FinitePresentation A C] (Q : PrimeSpectrum C)
    (hflatQ : Q ∈ Module.flatOverBaseLocus A C C)
    (hqfQ : Algebra.QuasiFiniteAt A Q.asIdeal) :
    ∃ (T : Type w) (_ : CommRing T) (η : C →+* T) (Q' : PrimeSpectrum T),
      PrimeSpectrum.comap η Q' = Q ∧
        (η.comp (algebraMap A C)).QuasiFinite ∧
        (η.comp (algebraMap A C)).Flat ∧
        (η.comp (algebraMap A C)).FinitePresentation := by
  -- Intersect the open flat locus with the open quasi-finite-at locus and choose a principal
  -- neighborhood of `Q` inside it.
  let U : Set (PrimeSpectrum C) :=
    Module.flatOverBaseLocus A C C ∩ {Q : PrimeSpectrum C | Algebra.QuasiFiniteAt A Q.asIdeal}
  have hUopen : IsOpen U := by
    exact (Module.isOpen_flatOverBaseLocus_of_finitePresentation
      (R := A) (S := C) (M := C)).inter
      (isOpen_setOf_quasiFiniteAt (R := A) (S := C))
  have hQU : Q ∈ U :=
    ⟨hflatQ, hqfQ⟩
  obtain ⟨V, hVbasis, hQV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hUopen Q hQU
  rcases hVbasis with ⟨g, rfl⟩
  let T : Type w := Localization.Away g
  let η : C →+* T := algebraMap C T
  have hRange : Q ∈ Set.range (PrimeSpectrum.comap η) := by
    rw [PrimeSpectrum.localization_away_comap_range T g]
    exact hQV
  obtain ⟨Q', hQ'⟩ := hRange
  -- The chosen basic open lies in both loci, so the two localization helpers supply the global
  -- algebraic properties after passing to `C_g`.
  have hbasicFlat : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
      Module.flatOverBaseLocus A C C := by
    intro x hx
    exact (hVU hx).1
  have hbasicQF : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
      {Q : PrimeSpectrum C | Algebra.QuasiFiniteAt A Q.asIdeal} := by
    intro x hx
    exact (hVU hx).2
  have hqfT : Algebra.QuasiFinite A T :=
    quasiFinite_localizationAway_of_basicOpen_subset_quasiFiniteAt
      (A := A) (C := C) g hbasicQF
  have hflatT : Module.Flat A T :=
    flat_localizationAway_of_basicOpen_subset_flatOverBaseLocus
      (A := A) (C := C) g hbasicFlat
  have hfpT : Algebra.FinitePresentation A T :=
    inferInstance
  have hηcomp : η.comp (algebraMap A C) = algebraMap A T := by
    ext x
    exact IsScalarTower.algebraMap_apply A C T x
  refine ⟨T, inferInstance, η, Q', ?_, ?_, ?_, ?_⟩
  · exact hQ'
  · rw [hηcomp, RingHom.quasiFinite_algebraMap]
    exact hqfT
  · rw [hηcomp, RingHom.flat_algebraMap_iff]
    exact hflatT
  · rw [hηcomp, RingHom.finitePresentation_algebraMap]
    exact hfpT

/-- Helper for Chap10 Lemma 10 168 10: from a closed Cohen-Macaulay fiber point, the source
regular-sequence quotient and shrinking construction gives the desired local factorization. -/
lemma existsFactorizationAtClosedCohenMacaulayFiberPoint
    {A B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FinitePresentation A B] [Module.Flat A B]
    {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    (hqmap : PrimeSpectrum.comap (algebraMap A B) q = p)
    (hqCM : q ∈ PrimeSpectrum.cohenMacaulayFiberLocus A B)
    (hqclosed : (fiberPrimeAt A B q).asIdeal.IsMaximal) :
    ∃ (T : Type w) (_ : CommRing T) (ψ : B →+* T),
      ((ψ.comp (algebraMap A B)).QuasiFinite) ∧
        ((ψ.comp (algebraMap A B)).Flat) ∧
        ((ψ.comp (algebraMap A B)).FinitePresentation) ∧
        p ∈ Set.range (PrimeSpectrum.comap (ψ.comp (algebraMap A B))) := by
  -- Route correction: the source quotient construction and the open-locus shrinking are now
  -- separated from the final packaging, so this proof only composes the two produced maps and
  -- carries the chosen prime through `Spec`.
  obtain ⟨C, hC, hAC, χ, Q, hχcomp, hQχ, hfpC, hflatQ, hqfQ⟩ :=
    existsLocalModelAtClosedCohenMacaulayFiberPoint
      (A := A) (B := B) hqmap hqCM hqclosed
  letI : CommRing C := hC
  letI : Algebra A C := hAC
  letI : Algebra.FinitePresentation A C := hfpC
  obtain ⟨T, hT, η, Q', hQη, hηqf, hηflat, hηfp⟩ :=
    existsLocalizationWithGlobalFlatAndQuasiFinite (A := A) (C := C) Q hflatQ hqfQ
  let ψ : B →+* T := η.comp χ
  have hψcomp : ψ.comp (algebraMap A B) = η.comp (algebraMap A C) := by
    -- The model map `χ` is compatible with the two `A`-algebra structures, so associativity
    -- identifies the final composite with the localized model map.
    calc
      ψ.comp (algebraMap A B) = (η.comp χ).comp (algebraMap A B) := rfl
      _ = η.comp (χ.comp (algebraMap A B)) := by
        rw [RingHom.comp_assoc]
      _ = η.comp (algebraMap A C) := by
        rw [hχcomp]
  have hQψ : PrimeSpectrum.comap ψ Q' = q := by
    -- The final prime lies over `q` by composing its image over the model prime with `hQχ`.
    calc
      PrimeSpectrum.comap ψ Q' = PrimeSpectrum.comap (η.comp χ) Q' := rfl
      _ = PrimeSpectrum.comap χ (PrimeSpectrum.comap η Q') := by
        rw [PrimeSpectrum.comap_comp_apply]
      _ = PrimeSpectrum.comap χ Q := by
        rw [hQη]
      _ = q := hQχ
  refine ⟨T, hT, ψ, ?_, ?_, ?_, ?_⟩
  · -- The global quasi-finiteness statement is exactly the shrunk model statement after
    -- rewriting the composite.
    simpa [hψcomp] using hηqf
  · -- The same composite rewrite transports flatness.
    simpa [hψcomp] using hηflat
  · -- Finite presentation is transported along the same identified composite.
    simpa [hψcomp] using hηfp
  · -- The composed prime gives the required spectrum-image witness for the base prime.
    exact mem_range_comap_comp_of_comap_eq (algebraMap A B) ψ hqmap hQψ

/-- Helper for Chap10 Lemma 10 168 10: source-facing primewise construction over a noetherian
base.  Starting from a base prime, one must choose a local Cohen-Macaulay fiber point and shrink
by a regular-sequence quotient to obtain a flat quasi-finite finitely presented factorization
whose spectrum image contains that base prime. -/
lemma existsPrimewiseFactorizationOfNoetherian
    {A B : Type w} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (g : A →+* B) (hff : g.FaithfullyFlat) (hfp : g.FinitePresentation)
    (p : PrimeSpectrum A) :
    ∃ (T : Type w) (_ : CommRing T) (ψ : B →+* T),
      ((ψ.comp g).QuasiFinite) ∧
        ((ψ.comp g).Flat) ∧
        ((ψ.comp g).FinitePresentation) ∧
        p ∈ Set.range (PrimeSpectrum.comap (ψ.comp g)) := by
  -- Route correction: first put `g` in algebra-map form and choose a closed
  -- Cohen-Macaulay point in the fiber; only the regular-sequence quotient and shrinking
  -- construction remains in the dedicated helper.
  letI : Algebra A B := g.toAlgebra
  have hAlgMap : algebraMap A B = g :=
    RingHom.algebraMap_toAlgebra g
  have hffAlg : (algebraMap A B).FaithfullyFlat := by
    simpa [hAlgMap] using hff
  have hflatAlg : Module.Flat A B := by
    rw [← RingHom.flat_algebraMap_iff]
    exact hffAlg.flat
  have hfpAlg : Algebra.FinitePresentation A B := by
    rw [← RingHom.finitePresentation_algebraMap]
    simpa [hAlgMap] using hfp
  letI : Module.Flat A B := hflatAlg
  letI : Algebra.FinitePresentation A B := hfpAlg
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) :=
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hffAlg).2
  obtain ⟨q, hqmap, hqCM, hqclosed⟩ :=
    existsClosedCohenMacaulayFiberPointOver (A := A) (B := B) hsurj p
  obtain ⟨T, hT, ψ, hψqf, hψflat, hψfp, hψrange⟩ :=
    existsFactorizationAtClosedCohenMacaulayFiberPoint
      (A := A) (B := B) hqmap hqCM hqclosed
  -- Rewrite the algebra-map composite back to the original ring hom `g`.
  refine ⟨T, hT, ψ, ?_, ?_, ?_, ?_⟩
  · simpa [hAlgMap] using hψqf
  · simpa [hAlgMap] using hψflat
  · simpa [hAlgMap] using hψfp
  · simpa [hAlgMap] using hψrange

/-- Helper for Chap10 Lemma 10 168 10: over a noetherian base, one can choose finitely many
local factorizations whose images cover the prime spectrum. -/
lemma existsFiniteCoveringFactorizationsOfNoetherian
    {A B : Type w} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (g : A →+* B) (hff : g.FaithfullyFlat) (hfp : g.FinitePresentation) :
    ∃ (ι : Type w) (_ : Finite ι) (T : ι → Type w) (_hT : ∀ i, CommRing (T i))
      (ψ : ∀ i, B →+* T i),
      (∀ i, ((ψ i).comp g).QuasiFinite) ∧
        (∀ i, ((ψ i).comp g).Flat) ∧
        (∀ i, ((ψ i).comp g).FinitePresentation) ∧
        Set.univ ⊆ ⋃ i, Set.range (PrimeSpectrum.comap ((ψ i).comp g)) := by
  classical
  -- The noetherian source work is now isolated to the primewise construction; compactness turns
  -- those local images into the finite family consumed by the diagonal product helper.
  exact finiteCoveringFactorizationsOfPrimewiseWitnesses g
    (existsPrimewiseFactorizationOfNoetherian g hff hfp)

/-- Helper for Chap10 Lemma 10 168 10: over a noetherian base, a faithfully flat finitely
presented map admits a quasi-finite faithfully flat finitely presented factorization. -/
lemma exists_factorization_noetherian_base
    {A B : Type w} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (g : A →+* B) (hff : g.FaithfullyFlat) (hfp : g.FinitePresentation) :
    ∃ (T : Type w) (_ : CommRing T) (ψ : B →+* T),
      (ψ.comp g).QuasiFinite ∧ (ψ.comp g).FaithfullyFlat ∧
        (ψ.comp g).FinitePresentation := by
  classical
  -- Replace the monolithic noetherian step by the source finite-cover construction followed by
  -- the diagonal product assembly.
  obtain ⟨ι, hι, T, hT, ψ, hqf, hflat, hfp', hcover⟩ :=
    existsFiniteCoveringFactorizationsOfNoetherian g hff hfp
  letI : Finite ι := hι
  letI (i : ι) : CommRing (T i) := hT i
  simpa using diagonalFactorizationOfRangeCover g T ψ hqf hflat hfp' hcover

/-- Helper for Chap10 Lemma 10 168 10: a model factorization transports across a pushout square
by base change. -/
lemma baseChange_factorization_of_isPushout
    {A : Type uA} {R : Type uR} {B : Type uB} {S : Type uS} {T : Type uT}
    [CommRing A] [CommRing R] [CommRing B] [CommRing S]
    [CommRing T] [Algebra A R] [Algebra A B] [Algebra R S] [Algebra B S]
    [Algebra A S] [IsScalarTower A R S] [IsScalarTower A B S]
    [Algebra.IsPushout A R B S]
    (ψ : B →+* T)
    (hqf : (ψ.comp (algebraMap A B)).QuasiFinite)
    (hff : (ψ.comp (algebraMap A B)).FaithfullyFlat)
    (hfp : (ψ.comp (algebraMap A B)).FinitePresentation) :
    ∃ (S' : Type (max uR uT)) (_ : CommRing S') (φ : S →+* S'),
      (φ.comp (algebraMap R S)).QuasiFinite ∧
        (φ.comp (algebraMap R S)).FaithfullyFlat ∧
        (φ.comp (algebraMap R S)).FinitePresentation := by
  -- Equip `T` with the algebra structures induced by `ψ`; the tensor product is then the
  -- base change of the model composite `A → T` along `A → R`.
  letI : Algebra B T := ψ.toAlgebra
  letI : Algebra A T := (ψ.comp (algebraMap A B)).toAlgebra
  letI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  have hqfAlg : Algebra.QuasiFinite A T := by
    rw [← RingHom.quasiFinite_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using hqf
  have hffAlg : Module.FaithfullyFlat A T := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    simpa [RingHom.algebraMap_toAlgebra] using hff
  have hfpAlg : Algebra.FinitePresentation A T := by
    rw [← RingHom.finitePresentation_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using hfp
  letI : Algebra.QuasiFinite A T := hqfAlg
  letI : Module.FaithfullyFlat A T := hffAlg
  letI : Algebra.FinitePresentation A T := hfpAlg
  -- Build the map out of the pushout by first moving `S` back to `R ⊗[A] B`, then mapping the
  -- right tensor factor through `ψ`.
  let θ : R ⊗[A] B →ₐ[A] R ⊗[A] T :=
    Algebra.TensorProduct.map (AlgHom.id A R) (IsScalarTower.toAlgHom A B T)
  let φ : S →+* R ⊗[A] T :=
    θ.toRingHom.comp (Algebra.IsPushout.equiv A R B S).symm.toRingHom
  have hφ : φ.comp (algebraMap R S) = algebraMap R (R ⊗[A] T) := by
    ext x
    dsimp [φ, θ]
    calc
      (Algebra.TensorProduct.map (AlgHom.id A R) (IsScalarTower.toAlgHom A B T))
          ((Algebra.IsPushout.equiv A R B S).symm ((algebraMap R S) x))
        = (Algebra.TensorProduct.map (AlgHom.id A R) (IsScalarTower.toAlgHom A B T))
            (x ⊗ₜ[A] (1 : B)) := by
            exact congrArg
              (Algebra.TensorProduct.map (AlgHom.id A R) (IsScalarTower.toAlgHom A B T))
              (Algebra.IsPushout.equiv_symm_algebraMap_left (R := A) (S := R)
                (R' := B) (S' := S) x)
      _ = x ⊗ₜ[A] (1 : T) := by simp
  refine ⟨R ⊗[A] T, inferInstance, φ, ?_, ?_, ?_⟩
  · -- Quasi-finiteness of `A → T` is preserved by the tensor base change.
    rw [hφ, RingHom.quasiFinite_algebraMap]
    infer_instance
  · -- Faithful flatness is likewise supplied by the tensor-product base-change instance.
    rw [hφ, RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  · -- The finite-presentation instance gives the final transported property.
    rw [hφ, RingHom.finitePresentation_algebraMap]
    infer_instance

-- Proof sketch: first descend the faithfully flat finitely presented map `f` to a finitely
-- generated `ℤ`-model using Lemma `10.168.2`, reducing to the Noetherian case by base change.
-- Then use the Cohen--Macaulay open locus from Lemma `10.130.4` and openness of flatness and
-- quasi-finiteness to construct, for each prime of `R`, a localization-and-quotient of `S`
-- through which `f` factors and which is quasi-finite, flat, and of finite presentation near that
-- prime. Finally cover `Spec R` by finitely many such opens and take their product to recover
-- faithful flatness.
/-- Lemma 10.168.10: if `f : R →+* S` is faithfully flat and of finite presentation, then there
exists a commutative triangle `R → S → S'` such that the induced map `R → S'` is quasi-finite,
faithfully flat, and of finite presentation. -/
@[stacks 034Z]
theorem exists_factorization_as_quasiFinite_faithfullyFlat_finitePresentation
    (f : R →+* S) (hff : f.FaithfullyFlat) (hfp : f.FinitePresentation) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (φ : S →+* S'),
      (φ.comp f).QuasiFinite ∧ (φ.comp f).FaithfullyFlat ∧ (φ.comp f).FinitePresentation := by
  classical
  -- First put the arbitrary ring hom into the algebra-map spelling required by the
  -- approximation theorem.
  letI : Algebra R S := f.toAlgebra
  have hAlgMap : algebraMap R S = f := RingHom.algebraMap_toAlgebra f
  have hffAlg : (algebraMap R S).FaithfullyFlat := by
    simpa [hAlgMap] using hff
  have hfpAlg : Algebra.FinitePresentation R S := by
    rw [← RingHom.finitePresentation_algebraMap]
    simpa [hAlgMap] using hfp
  letI : Algebra.FinitePresentation R S := hfpAlg
  -- Lemma 10.168.2 supplies the finitely presented faithfully flat model over a
  -- finitely presented `ℤ`-algebra; the remaining source proof is the noetherian
  -- quasi-finite factorization on this model followed by base change along the pushout.
  obtain ⟨A₀, hA₀comm, r, a, ha, hrfp, B₀, hB₀comm, g, b, hb, hgfp, hgff, hpush⟩ :=
    exists_faithfullyFlat_finitePresentation_approximation (R := ℤ) (A := R) (B := S) hffAlg
  letI : CommRing A₀ := hA₀comm
  letI : CommRing B₀ := hB₀comm
  -- The finite-presentation hypothesis on `r : ℤ → A₀` supplies the noetherian model base.
  letI : IsNoetherianRing A₀ := isNoetherianRing_of_int_finitePresentation r hrfp
  obtain ⟨T₀, hT₀comm, ψ₀, hψqf, hψff, hψfp⟩ :=
    exists_factorization_noetherian_base g hgff hgfp
  letI : CommRing T₀ := hT₀comm
  -- Reinstall the algebra structures used by the pushout data so the transport helper applies.
  letI : Algebra A₀ R := a.toAlgebra
  letI : Algebra A₀ B₀ := g.toAlgebra
  letI : Algebra B₀ S := b.toAlgebra
  letI : Algebra A₀ S := ((algebraMap R S).comp a).toAlgebra
  letI : IsScalarTower A₀ R S := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A₀ B₀ S := IsScalarTower.of_algebraMap_eq' <| by
    simpa [RingHom.algebraMap_toAlgebra] using hb.symm
  letI : Algebra.IsPushout A₀ R B₀ S := hpush
  have hψqfAlg : (ψ₀.comp (algebraMap A₀ B₀)).QuasiFinite := by
    simpa [RingHom.algebraMap_toAlgebra] using hψqf
  have hψffAlg : (ψ₀.comp (algebraMap A₀ B₀)).FaithfullyFlat := by
    simpa [RingHom.algebraMap_toAlgebra] using hψff
  have hψfpAlg : (ψ₀.comp (algebraMap A₀ B₀)).FinitePresentation := by
    simpa [RingHom.algebraMap_toAlgebra] using hψfp
  obtain ⟨S', hS'comm, φ, hφqf, hφff, hφfp⟩ :=
    baseChange_factorization_of_isPushout (A := A₀) (R := R) (B := B₀) (S := S)
      (T := T₀) ψ₀ hψqfAlg hψffAlg hψfpAlg
  -- Finally rewrite the algebra-map spelling of `R → S` back to the original map `f`.
  refine ⟨S', hS'comm, φ, ?_, ?_, ?_⟩
  · simpa [hAlgMap] using hφqf
  · simpa [hAlgMap] using hφff
  · simpa [hAlgMap] using hφfp

end
