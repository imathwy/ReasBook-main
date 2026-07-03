import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_149_1 (from Chap10) -/
noncomputable section

open Algebra
open Algebra.Extension
open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

/-- Helper for Lemma 10.149.1: for the canonical polynomial presentation of `S`, the conormal map
onto the Kähler differentials is surjective when `R → S` is formally unramified. -/
lemma selfPresentation_cotangentComplex_surjective [Algebra.FormallyUnramified R S] :
    Function.Surjective ((Generators.self R S).toExtension.cotangentComplex) := by
  let P : Extension R S := (Generators.self R S).toExtension
  have hExact : LinearMap.ker P.toKaehler = LinearMap.range P.cotangentComplex := by
    exact (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
  have hKer : LinearMap.ker P.toKaehler = ⊤ := by
    rw [LinearMap.ker_eq_top]
    ext x
    exact Subsingleton.elim _ _
  exact LinearMap.range_eq_top.mp <| hExact.symm.trans hKer

/-- Helper for Lemma 10.149.1: the cotangent complex of the canonical polynomial presentation of
`S` admits an `S`-linear section when `R → S` is formally unramified. -/
lemma selfPresentation_cotangentComplex_has_section [Algebra.FormallyUnramified R S] :
    ∃ l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
        (Generators.self R S).toExtension.Cotangent,
      (Generators.self R S).toExtension.cotangentComplex ∘ₗ l = LinearMap.id := by
  let P : Extension R S := (Generators.self R S).toExtension
  obtain ⟨l, hl⟩ :=
    P.cotangentComplex.exists_rightInverse_of_surjective <|
      LinearMap.range_eq_top.mpr (selfPresentation_cotangentComplex_surjective (R := R) (S := S))
  exact ⟨l, hl⟩

/-- Helper for Lemma 10.149.1: the chosen section of the cotangent complex determines an ideal in
the infinitesimal self-presentation by taking the ideal span of the transported image of the
section. -/
noncomputable def selfPresentation_section_image_ideal
    (l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
      (Generators.self R S).toExtension.Cotangent) :
    Ideal ((Generators.self R S).toExtension.infinitesimal.Ring) :=
  let P : Extension R S := (Generators.self R S).toExtension
  Ideal.span <|
    Set.range fun x : P.CotangentSpace ↦
      (((Ideal.cotangentEquivIdeal P.ker) (P.cotangentEquivCotangentKer (l x)) :
        P.ker.cotangentIdeal)).1

/-- Helper for Lemma 10.149.1: the section-image ideal lies in the kernel of the infinitesimal
self-presentation. -/
lemma selfPresentation_section_image_ideal_le_ker
    (l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
      (Generators.self R S).toExtension.Cotangent) :
    selfPresentation_section_image_ideal (R := R) (S := S) l ≤
      ((Generators.self R S).toExtension.infinitesimal.ker) := by
  let P : Extension R S := (Generators.self R S).toExtension
  -- Each generator already lands in `P.infinitesimal.ker`, so the ideal span does as well.
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨x, rfl⟩
  change
    (((Ideal.cotangentEquivIdeal P.ker) (P.cotangentEquivCotangentKer (l x)) :
      P.ker.cotangentIdeal)).1 ∈ P.infinitesimal.ker
  simpa [Extension.ker_infinitesimal] using
    (((Ideal.cotangentEquivIdeal P.ker) (P.cotangentEquivCotangentKer (l x)) :
      P.ker.cotangentIdeal)).2

/-- Helper for Lemma 10.149.1: quotienting the infinitesimal self-presentation by the
section-image ideal still maps surjectively to `S`. -/
noncomputable def selfPresentation_section_quotient_map
    (l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
      (Generators.self R S).toExtension.Cotangent) :
    ((Generators.self R S).toExtension.infinitesimal.Ring ⧸
      selfPresentation_section_image_ideal (R := R) (S := S) l) →ₐ[R] S :=
  let P : Extension R S := (Generators.self R S).toExtension
  let Jbar := selfPresentation_section_image_ideal (R := R) (S := S) l
  Ideal.Quotient.liftₐ Jbar
    (IsScalarTower.toAlgHom R P.infinitesimal.Ring S)
    (selfPresentation_section_image_ideal_le_ker (R := R) (S := S) l)

/-- Helper for Lemma 10.149.1: the quotient by the section-image ideal is still an extension of
`S`. -/
lemma selfPresentation_section_quotient_map_surjective
    (l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
      (Generators.self R S).toExtension.Cotangent) :
    Function.Surjective (selfPresentation_section_quotient_map (R := R) (S := S) l) := by
  let P : Extension R S := (Generators.self R S).toExtension
  intro s
  -- The chosen section of the original infinitesimal extension still maps to `s` after quotienting.
  refine ⟨Ideal.Quotient.mk _ (P.infinitesimal.σ s), ?_⟩
  change algebraMap P.infinitesimal.Ring S (P.infinitesimal.σ s) = s
  simpa

/-- Helper for Lemma 10.149.1: this is the quotient infinitesimal extension obtained by killing
the chosen section image. -/
noncomputable def selfPresentation_section_quotient
    (l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
      (Generators.self R S).toExtension.Cotangent) :
    Extension R S :=
  Extension.ofSurjective
    (selfPresentation_section_quotient_map (R := R) (S := S) l)
    (selfPresentation_section_quotient_map_surjective (R := R) (S := S) l)

/-- Helper for Lemma 10.149.1: the canonical self presentation lifts any map `S → A/I` across a
square-zero quotient because its source ring is a polynomial algebra. -/
lemma selfPresentation_exists_polynomial_lift
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) (f : S →ₐ[R] A ⧸ I) :
    ∃ β : (Generators.self R S).toExtension.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp β =
        f.comp (IsScalarTower.toAlgHom R (Generators.self R S).toExtension.Ring S) := by
  let P : Extension R S := (Generators.self R S).toExtension
  let _ : Algebra.FormallySmooth R P.Ring := by
    change Algebra.FormallySmooth R (MvPolynomial S R)
    infer_instance
  -- Lift the composite `P.Ring → S → A/I` using formal smoothness of the polynomial ring.
  simpa [P] using
    (Algebra.FormallySmooth.exists_lift
      (R := R)
      (A := P.Ring)
      (B := A)
      I
      ⟨2, hI⟩
      (f.comp (IsScalarTower.toAlgHom R P.Ring S)))

/-- Helper for Lemma 10.149.1: the quotient extension `A → A ⧸ I` has square-zero kernel when
`I² = 0`. This is the target square-zero owner used for the corrected lift. -/
lemma squareZeroQuotient_extension_square_zero
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) :
    let Q : Extension R (A ⧸ I) :=
      Extension.ofSurjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
    Q.ker ^ 2 = ⊥ := by
  intro Q
  -- The extension kernel is exactly the ideal `I`, so the assumed square-zero relation applies.
  change RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom ^ 2 = ⊥
  simpa using hI

/-- Helper for Lemma 10.149.1: a polynomial lift to `A` packages as a morphism from the canonical
self presentation into the square-zero quotient extension `A → A ⧸ I`. -/
lemma selfPresentation_polynomial_lift_to_extension_hom
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A) (f : S →ₐ[R] A ⧸ I)
    (β : (Generators.self R S).toExtension.Ring →ₐ[R] A)
    (hβ : (Ideal.Quotient.mkₐ R I).comp β =
      f.comp (IsScalarTower.toAlgHom R (Generators.self R S).toExtension.Ring S)) :
    let P0 : Extension R S := (Generators.self R S).toExtension
    let _ : Algebra S (A ⧸ I) := f.toAlgebra
    let Q : Extension R (A ⧸ I) :=
      Extension.ofSurjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
    ∃ φ : P0.Hom Q, φ.toAlgHom = β := by
  intro P0 _ Q
  -- Repackage the lifted algebra map as a hom between the source and target extensions.
  refine ⟨Extension.Hom.ofAlgHom β ?_, rfl⟩
  simpa [P0, Q] using hβ

/-- Helper for Lemma 10.149.1: the kernel of the section-image quotient is the image of the square
zero infinitesimal kernel, hence it is square-zero. -/
lemma selfPresentation_section_quotient_ker_eq_map
    (l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
      (Generators.self R S).toExtension.Cotangent) :
    RingHom.ker (selfPresentation_section_quotient_map (R := R) (S := S) l).toRingHom =
      ((Generators.self R S).toExtension.infinitesimal.ker).map
        (Ideal.Quotient.mk (selfPresentation_section_image_ideal (R := R) (S := S) l)) := by
  let P : Extension R S := (Generators.self R S).toExtension
  let Jbar := selfPresentation_section_image_ideal (R := R) (S := S) l
  -- Reduce the extension wrapper to the quotient-ring kernel formula.
  simpa [selfPresentation_section_quotient_map, P, Jbar, Ideal.Quotient.liftₐ] using
    (Ideal.ker_quotient_lift
      (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).toRingHom
      (selfPresentation_section_image_ideal_le_ker (R := R) (S := S) l))

/-- Helper for Lemma 10.149.1: the section-image quotient inherits square-zero kernel from the
square-zero infinitesimal kernel of the self presentation. -/
lemma selfPresentation_section_quotient_square_zero
    (l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
      (Generators.self R S).toExtension.Cotangent) :
    (selfPresentation_section_quotient (R := R) (S := S) l).ker ^ 2 = ⊥ := by
  let P : Extension R S := (Generators.self R S).toExtension
  let Jbar := selfPresentation_section_image_ideal (R := R) (S := S) l
  have hker :
      (selfPresentation_section_quotient (R := R) (S := S) l).ker =
        P.infinitesimal.ker.map (Ideal.Quotient.mk Jbar) := by
    -- The new kernel is exactly the quotient image of the infinitesimal kernel.
    change RingHom.ker (selfPresentation_section_quotient_map (R := R) (S := S) l).toRingHom =
      P.infinitesimal.ker.map (Ideal.Quotient.mk Jbar)
    simpa [P, Jbar] using
      selfPresentation_section_quotient_ker_eq_map (R := R) (S := S) l
  have hsqInf : P.infinitesimal.ker ^ 2 = ⊥ := by
    -- The infinitesimal kernel is `P.ker / P.ker²`, whose square vanishes canonically.
    simpa [Extension.ker_infinitesimal] using Ideal.cotangentIdeal_square P.ker
  -- Push the square-zero relation through the quotient map.
  rw [hker]
  calc
    (P.infinitesimal.ker.map (Ideal.Quotient.mk Jbar)) ^ 2 =
        Ideal.map (Ideal.Quotient.mk Jbar) (P.infinitesimal.ker ^ 2) := by
          symm
          exact Ideal.map_pow (Ideal.Quotient.mk Jbar) P.infinitesimal.ker 2
    _ = ⊥ := by
          simpa [hsqInf]

/-- Helper for Lemma 10.149.1: over a square-zero target extension, any prescribed cotangent-space
map from the self presentation is realized by correcting a fixed owner lift on the self
generators. -/
lemma selfPresentation_exists_corrected_extension_hom
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (u : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S] Q.Cotangent) :
    ∃ φu : ((Generators.self R S).toExtension).Hom Q, φu.sub φ = u := by
  let G : Generators R S S := Generators.self R S
  let P0 : Extension R S := G.toExtension
  let δ : S → Q.ker := fun s ↦
    Extension.ConormalModule.val
      (((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm) (u (G.cotangentSpaceBasis s)))
  have hδ : ∀ s, Extension.Cotangent.mk (δ s) = u (G.cotangentSpaceBasis s) := by
    intro s
    -- The chosen kernel correction represents the prescribed cotangent value on each basis vector.
    change
      (Q.conormalModuleEquivCotangentOfSquareZero hQsq)
          (((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm) (u (G.cotangentSpaceBasis s))) =
        _
    simp
  let ψ : P0.Ring →ₐ[R] Q.Ring :=
    MvPolynomial.aeval fun s ↦ φ.toAlgHom (.X s) + (δ s : Q.Ring)
  have hψX : ∀ s, ψ (MvPolynomial.X s) = φ.toAlgHom (MvPolynomial.X s) + (δ s : Q.Ring) := by
    intro s
    -- On each self generator, the corrected owner map is the old value plus the kernel error.
    change MvPolynomial.aeval (fun t : S ↦ φ.toAlgHom (MvPolynomial.X t) + (δ t : Q.Ring))
        (MvPolynomial.X s) = _
    simp
  have hψcomm :
      (IsScalarTower.toAlgHom R Q.Ring S').comp ψ =
        (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P0.Ring S) := by
    apply MvPolynomial.algHom_ext
    intro s
    -- The correction lies in the kernel, so it disappears after passing to the quotient algebra.
    change algebraMap Q.Ring S' (ψ (MvPolynomial.X s)) =
      algebraMap S S' ((algebraMap P0.Ring S) (MvPolynomial.X s))
    rw [hψX]
    rw [map_add,
      show algebraMap Q.Ring S' (δ s : Q.Ring) = 0 by exact (δ s).2,
      add_zero]
    simpa [P0, G] using φ.algebraMap_toRingHom (MvPolynomial.X s)
  let φu : P0.Hom Q := Extension.Hom.ofAlgHom ψ hψcomm
  have hsubToKer_X : ∀ s, (φu.subToKer φ) (MvPolynomial.X s) = δ s := by
    intro s
    -- On each generator, the difference between the corrected and original lifts is exactly `δ s`.
    apply Subtype.ext
    change ψ (MvPolynomial.X s) - φ.toAlgHom (MvPolynomial.X s) = (δ s : Q.Ring)
    rw [hψX]
    abel
  refine ⟨φu, ?_⟩
  apply G.cotangentSpaceBasis.ext
  intro s
  -- Compare both cotangent-space maps on the canonical basis of the self presentation.
  calc
    φu.sub φ (G.cotangentSpaceBasis s) =
        Extension.Cotangent.mk ((φu.subToKer φ) (MvPolynomial.X s)) := by
          simpa [P0, G, Generators.cotangentSpaceBasis_apply] using
            (Extension.Hom.sub_one_tmul (f := φu) (g := φ) (x := MvPolynomial.X s))
    _ = Extension.Cotangent.mk (δ s) := by rw [hsubToKer_X s]
    _ = u (G.cotangentSpaceBasis s) := hδ s

/-- Helper for Lemma 10.149.1: correcting a self-presentation lift by the negative cotangent
obstruction forces the corrected cotangent map to vanish on the chosen section. -/
lemma selfPresentation_corrected_extension_hom_cotangent_vanish
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hl : ((Generators.self R S).toExtension).cotangentComplex ∘ₗ l = LinearMap.id) :
    ∃ φu : ((Generators.self R S).toExtension).Hom Q,
      (Extension.Cotangent.map φu) ∘ₗ l = 0 := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  let u : P0.CotangentSpace →ₗ[S] Q.Cotangent := -((Extension.Cotangent.map φ) ∘ₗ l)
  obtain ⟨φu, hsub⟩ :=
    selfPresentation_exists_corrected_extension_hom (R := R) (S := S) Q hQsq φ u
  refine ⟨φu, ?_⟩
  apply LinearMap.ext
  intro x
  have hmap := LinearMap.congr_fun (Extension.Cotangent.map_sub_map φu φ) (l x)
  have hsplit : P0.cotangentComplex (l x) = x := by
    -- The chosen section splits the cotangent complex on the nose.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hl x
  have hdiff :
      Extension.Cotangent.map φu (l x) - Extension.Cotangent.map φ (l x) =
        -Extension.Cotangent.map φ (l x) := by
    -- The correction was defined to cancel the original cotangent obstruction.
    calc
      Extension.Cotangent.map φu (l x) - Extension.Cotangent.map φ (l x) =
          φu.sub φ (P0.cotangentComplex (l x)) := by
            simpa [LinearMap.comp_apply] using hmap
      _ = u (P0.cotangentComplex (l x)) := by rw [hsub]
      _ = u x := by rw [hsplit]
      _ = -Extension.Cotangent.map φ (l x) := by rfl
  have hfinal := hdiff
  abel_nf at hfinal
  simpa using hfinal

/-- Helper for Lemma 10.149.1: a map from the canonical self presentation into a square-zero
extension kills the square of the presentation kernel. -/
lemma selfPresentation_extension_hom_zero_of_mem_ker_sq
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    {x : ((Generators.self R S).toExtension).Ring}
    (hx : x ∈ ((Generators.self R S).toExtension).ker ^ 2) :
    φ.toAlgHom x = 0 := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  have hker :
      P0.ker ≤ Ideal.comap φ.toAlgHom.toRingHom Q.ker := by
    intro y hy
    -- Elements of the source kernel still map to the target kernel.
    change algebraMap Q.Ring S' (φ.toRingHom y) = 0
    rw [φ.algebraMap_toRingHom]
    have hy0 : algebraMap P0.Ring S y = 0 := by
      simpa [P0, RingHom.mem_ker] using hy
    rw [hy0]
    simp
  have hsq :
      P0.ker ^ 2 ≤ Ideal.comap φ.toAlgHom.toRingHom (Q.ker ^ 2) :=
    (Ideal.pow_right_mono hker 2).trans <|
      Ideal.le_comap_pow (f := φ.toAlgHom.toRingHom) (K := Q.ker) 2
  have hxsq : φ.toAlgHom x ∈ Q.ker ^ 2 := by
    simpa [P0, Ideal.mem_comap] using hsq hx
  -- Square-zero of the target kernel forces the image to vanish.
  simpa [hQsq, Ideal.mem_bot] using hxsq

/-- Helper for Lemma 10.149.1: after correcting the owner map into a square-zero target, the map
descends from the polynomial self presentation to its infinitesimal quotient by `ker²`. -/
noncomputable def selfPresentation_infinitesimal_lift
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q) :
    ((Generators.self R S).toExtension.infinitesimal.Ring) →ₐ[R] Q.Ring :=
  let P0 : Extension R S := (Generators.self R S).toExtension
  Ideal.Quotient.liftₐ (P0.ker ^ 2) φ.toAlgHom
    (fun _ hx ↦
      selfPresentation_extension_hom_zero_of_mem_ker_sq
        (R := R) (S := S) Q hQsq φ hx)

/-- Helper for Lemma 10.149.1: the descended infinitesimal lift still reduces to the original
target map on `S`. -/
lemma selfPresentation_infinitesimal_lift_comp_eq
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q) :
    (IsScalarTower.toAlgHom R Q.Ring S').comp
        (selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ) =
      (IsScalarTower.toAlgHom R S S').comp
        (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S) := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  -- Compare the two quotient maps after precomposing with `P0.Ring → P0.Ring / P0.ker²`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
  change algebraMap Q.Ring S'
      ((selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ)
        (Ideal.Quotient.mk (P0.ker ^ 2) x)) =
    algebraMap S S' (algebraMap P0.Ring S x)
  rw [selfPresentation_infinitesimal_lift]
  simpa [P0] using φ.algebraMap_toRingHom x

/-- Helper for Lemma 10.149.1: evaluating the descended infinitesimal lift on the explicit
cotangent representative agrees with the square-zero target's conormal representative of the
transported cotangent class. -/
lemma selfPresentation_infinitesimal_lift_apply_cotangent_representative
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (y : ((Generators.self R S).toExtension).Cotangent) :
    selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ
        (((Ideal.cotangentEquivIdeal ((Generators.self R S).toExtension.ker))
          (((Generators.self R S).toExtension).cotangentEquivCotangentKer y) :
            ((Generators.self R S).toExtension).ker.cotangentIdeal)).1 =
      (Extension.ConormalModule.val
        (((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm)
          (Extension.Cotangent.map φ y)) : Q.Ring) := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective y
  have hxker :
      φ.toAlgHom x ∈ Q.ker := by
    -- The image of a source-kernel element is again in the target kernel.
    change algebraMap Q.Ring S' (φ.toAlgHom x) = 0
    rw [show φ.toAlgHom x = φ.toRingHom x by rfl, φ.algebraMap_toRingHom]
    simpa using congrArg (algebraMap S S') x.2
  -- Rewrite the source representative to the quotient class of `x`, then evaluate the quotient lift.
  change
    selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ
        (Ideal.Quotient.mk (P0.ker ^ 2) x) =
      (Extension.ConormalModule.val
        (((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm)
          (Extension.Cotangent.mk ⟨φ.toAlgHom x, hxker⟩)) : Q.Ring)
  rw [selfPresentation_infinitesimal_lift]
  change φ.toAlgHom x =
    (Extension.ConormalModule.val
      (((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm)
        (Extension.Cotangent.mk ⟨φ.toAlgHom x, hxker⟩)) : Q.Ring)
  have hsymm :
      ((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm)
          (Extension.Cotangent.mk ⟨φ.toAlgHom x, hxker⟩) =
        Extension.ConormalModule.of ⟨φ.toAlgHom x, hxker⟩ := by
    -- The square-zero cotangent equivalence is inverted exactly by the conormal representative.
    apply (Q.conormalModuleEquivCotangentOfSquareZero hQsq).injective
    simp [Extension.conormalModuleEquivCotangentOfSquareZero_apply]
  simpa using (congrArg Subtype.val (congrArg Extension.ConormalModule.val hsymm)).symm

/-- Helper for Lemma 10.149.1: if the corrected cotangent obstruction vanishes on the chosen
section, then each explicit section generator maps to zero under the descended infinitesimal lift. -/
lemma selfPresentation_section_generator_image_eq_zero_of_cotangent_vanish
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hφ : (Extension.Cotangent.map φ) ∘ₗ l = 0)
    (x : ((Generators.self R S).toExtension).CotangentSpace) :
    selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ
        (((Ideal.cotangentEquivIdeal ((Generators.self R S).toExtension.ker))
          (((Generators.self R S).toExtension).cotangentEquivCotangentKer (l x)) :
            ((Generators.self R S).toExtension).ker.cotangentIdeal)).1 = 0 := by
  -- Specialize the generic cotangent-representative formula to the chosen summand element `l x`.
  rw [selfPresentation_infinitesimal_lift_apply_cotangent_representative
    (R := R) (S := S) Q hQsq φ (l x)]
  have hx : Extension.Cotangent.map φ (l x) = 0 := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hφ x
  rw [hx]
  have hz :
      ((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm) (0 : Q.Cotangent) = 0 := by
    simp
  rw [hz]
  rfl

/-- Helper for Lemma 10.149.1: generatorwise vanishing on the chosen section forces the entire
section-image ideal to lie in the kernel of the infinitesimal lift. -/
lemma selfPresentation_section_image_ideal_le_ker_of_generator_vanishing
    {A : Type*} [CommRing A] [Algebra R A]
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (φInf : ((Generators.self R S).toExtension.infinitesimal.Ring) →ₐ[R] A)
    (hzero : ∀ x : ((Generators.self R S).toExtension).CotangentSpace,
      φInf
          (((Ideal.cotangentEquivIdeal ((Generators.self R S).toExtension.ker))
            (((Generators.self R S).toExtension).cotangentEquivCotangentKer (l x)) :
              ((Generators.self R S).toExtension).ker.cotangentIdeal)).1 = 0) :
    selfPresentation_section_image_ideal (R := R) (S := S) l ≤ RingHom.ker φInf.toRingHom := by
  -- The source construction defines `J'` as the span of these explicit section generators.
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨x, rfl⟩
  simpa [RingHom.mem_ker] using hzero x

/-- Helper for Lemma 10.149.1: once the corrected infinitesimal lift kills the section-image
ideal, it factors through the quotient self-presentation `P/J'`. -/
lemma selfPresentation_factor_through_section_quotient_of_cotangent_vanish
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A) (f : S →ₐ[R] A ⧸ I)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (φInf : ((Generators.self R S).toExtension.infinitesimal.Ring) →ₐ[R] A)
    (hφInf : (Ideal.Quotient.mkₐ R I).comp φInf =
      f.comp (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S))
    (hzero : ∀ x : ((Generators.self R S).toExtension).CotangentSpace,
      φInf
          (((Ideal.cotangentEquivIdeal ((Generators.self R S).toExtension.ker))
            (((Generators.self R S).toExtension).cotangentEquivCotangentKer (l x)) :
              ((Generators.self R S).toExtension).ker.cotangentIdeal)).1 = 0) :
    ∃ g : (selfPresentation_section_quotient (R := R) (S := S) l).Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp g =
        f.comp (IsScalarTower.toAlgHom R (selfPresentation_section_quotient (R := R) (S := S) l).Ring S) := by
  let Jbar := selfPresentation_section_image_ideal (R := R) (S := S) l
  have hker : Jbar ≤ RingHom.ker φInf.toRingHom :=
    selfPresentation_section_image_ideal_le_ker_of_generator_vanishing
      (R := R) (S := S) (A := A) l φInf hzero
  have hquot :
      (IsScalarTower.toAlgHom R
          (selfPresentation_section_quotient (R := R) (S := S) l).Ring S).comp
        (Ideal.Quotient.mkₐ R Jbar) =
        IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S := by
    -- The quotient extension still reduces to the original infinitesimal self presentation.
    simpa [selfPresentation_section_quotient, selfPresentation_section_quotient_map, Jbar] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := Jbar)
        (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S)
        (selfPresentation_section_image_ideal_le_ker (R := R) (S := S) l))
  refine ⟨Ideal.Quotient.liftₐ Jbar φInf hker, ?_⟩
  -- Compare the two candidate reductions after precomposing with the quotient map from `P0.inf/J'`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) (I := Jbar) ?_
  calc
    (((Ideal.Quotient.mkₐ R I).comp (Ideal.Quotient.liftₐ Jbar φInf hker)).comp
        (Ideal.Quotient.mkₐ R Jbar)) =
        (Ideal.Quotient.mkₐ R I).comp φInf := by
          rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
    _ = f.comp
        (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S) := hφInf
    _ =
        f.comp
          ((IsScalarTower.toAlgHom R
              (selfPresentation_section_quotient (R := R) (S := S) l).Ring S).comp
            (Ideal.Quotient.mkₐ R Jbar)) := by
              rw [hquot]
    _ =
        (f.comp
          (IsScalarTower.toAlgHom R
            (selfPresentation_section_quotient (R := R) (S := S) l).Ring S)).comp
          (Ideal.Quotient.mkₐ R Jbar) := by
            rw [← AlgHom.comp_assoc]

/-- Helper for Lemma 10.149.1: if the descended infinitesimal lift kills the section-image ideal,
then the owner cotangent obstruction already vanishes on the chosen section. -/
lemma selfPresentation_cotangent_vanish_of_section_image_ideal_le_ker
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hker : selfPresentation_section_image_ideal (R := R) (S := S) l ≤
      RingHom.ker (selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ).toRingHom) :
    (Extension.Cotangent.map φ) ∘ₗ l = 0 := by
  -- Each explicit generator of the section-image ideal already maps to zero under the descended
  -- infinitesimal lift, so the corresponding cotangent class vanishes as well.
  apply LinearMap.ext
  intro x
  have hgen :
      (((Ideal.cotangentEquivIdeal ((Generators.self R S).toExtension.ker))
        (((Generators.self R S).toExtension).cotangentEquivCotangentKer (l x)) :
          ((Generators.self R S).toExtension).ker.cotangentIdeal)).1 ∈
        selfPresentation_section_image_ideal (R := R) (S := S) l := by
    exact Ideal.subset_span ⟨x, rfl⟩
  have hzero :
      selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ
          (((Ideal.cotangentEquivIdeal ((Generators.self R S).toExtension.ker))
            (((Generators.self R S).toExtension).cotangentEquivCotangentKer (l x)) :
              ((Generators.self R S).toExtension).ker.cotangentIdeal)).1 = 0 := by
    simpa [RingHom.mem_ker] using hker hgen
  rw [selfPresentation_infinitesimal_lift_apply_cotangent_representative
    (R := R) (S := S) Q hQsq φ (l x)] at hzero
  have hconormal_zero :
      ((Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm)
          (Extension.Cotangent.map φ (l x)) = 0 := by
    apply Extension.ConormalModule.ext
    simpa using hzero
  apply (Q.conormalModuleEquivCotangentOfSquareZero hQsq).symm.injective
  simpa using hconormal_zero

/-- Helper for Lemma 10.149.1: once the owner homotopy difference vanishes, the two induced
infinitesimal lifts on `P/ker²` agree. -/
lemma selfPresentation_infinitesimal_lift_eq_of_sub_eq_zero
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ₁ φ₂ : ((Generators.self R S).toExtension).Hom Q)
    (hsub : φ₁.sub φ₂ = 0) :
    selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₁ =
      selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₂ := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  have hAlg : φ₁.toAlgHom = φ₂.toAlgHom := by
    -- The vanishing homotopy forces the two owner maps to agree on the polynomial generators.
    apply MvPolynomial.algHom_ext
    intro s
    have hmk_zero :
        Extension.Cotangent.mk ((φ₁.subToKer φ₂) (MvPolynomial.X s)) = 0 := by
      have htmp := LinearMap.congr_fun hsub (1 ⊗ₜ .D _ _ (MvPolynomial.X s))
      rw [Extension.Hom.sub_one_tmul] at htmp
      simpa using htmp
    have hconormal_zero :
        (Extension.ConormalModule.of ((φ₁.subToKer φ₂) (MvPolynomial.X s)) :
          Extension.ConormalModule Q hQsq) = 0 := by
      apply (Q.conormalModuleEquivCotangentOfSquareZero hQsq).injective
      simpa using hmk_zero
    have hsubToKer_zero : ((φ₁.subToKer φ₂) (MvPolynomial.X s) : Q.ker) = 0 := by
      simpa using congrArg Extension.ConormalModule.val hconormal_zero
    have hsub_apply :
        φ₁.toAlgHom (MvPolynomial.X s) - φ₂.toAlgHom (MvPolynomial.X s) = 0 := by
      have hring_zero :
          (((φ₁.subToKer φ₂) (MvPolynomial.X s) : Q.ker) : Q.Ring) = 0 := by
        exact congrArg Subtype.val hsubToKer_zero
      change (((φ₁.subToKer φ₂) (MvPolynomial.X s) : Q.ker) : Q.Ring) = 0
      simpa [Extension.Hom.subToKer_apply_coe] using hring_zero
    exact sub_eq_zero.mp hsub_apply
  -- The quotient lift is determined by the owner map before modding out by `ker²`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
  rw [selfPresentation_infinitesimal_lift, selfPresentation_infinitesimal_lift]
  simpa [P0] using congrArg (fun ψ : P0.Ring →ₐ[R] Q.Ring ↦ ψ x) hAlg

/-- Helper for Lemma 10.149.1: two lifts out of the section quotient are equal once they induce
the same map modulo `I`. -/
lemma selfPresentation_factored_lift_unique
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A)
    (f : S →ₐ[R] A ⧸ I)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hl : ((Generators.self R S).toExtension).cotangentComplex ∘ₗ l = LinearMap.id)
    (hI : I ^ 2 = ⊥)
    (g₁ g₂ : (selfPresentation_section_quotient (R := R) (S := S) l).Ring →ₐ[R] A)
    (hg₁ : (Ideal.Quotient.mkₐ R I).comp g₁ =
      f.comp (IsScalarTower.toAlgHom R (selfPresentation_section_quotient (R := R) (S := S) l).Ring S))
    (hg₂ : (Ideal.Quotient.mkₐ R I).comp g₂ =
      f.comp (IsScalarTower.toAlgHom R (selfPresentation_section_quotient (R := R) (S := S) l).Ring S)) :
    g₁ = g₂ := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  let Jbar := selfPresentation_section_image_ideal (R := R) (S := S) l
  let _ : Algebra S (A ⧸ I) := f.toAlgebra
  let Q : Extension R (A ⧸ I) :=
    Extension.ofSurjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
  let φInf₁ : P0.infinitesimal.Ring →ₐ[R] A := g₁.comp (Ideal.Quotient.mkₐ R Jbar)
  let φInf₂ : P0.infinitesimal.Ring →ₐ[R] A := g₂.comp (Ideal.Quotient.mkₐ R Jbar)
  have hQsq : Q.ker ^ 2 = ⊥ := by
    simpa [Q] using squareZeroQuotient_extension_square_zero (R := R) (I := I) hI
  have hquot :
      (IsScalarTower.toAlgHom R
          (selfPresentation_section_quotient (R := R) (S := S) l).Ring S).comp
        (Ideal.Quotient.mkₐ R Jbar) =
        IsScalarTower.toAlgHom R P0.infinitesimal.Ring S := by
    -- The section quotient still reduces to the infinitesimal self presentation before quotienting
    -- further by `Jbar`.
    simpa [selfPresentation_section_quotient, selfPresentation_section_quotient_map, Jbar, P0] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := Jbar)
        (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S)
        (selfPresentation_section_image_ideal_le_ker (R := R) (S := S) l))
  have hφInf₁ :
      (Ideal.Quotient.mkₐ R I).comp φInf₁ =
        f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by
    -- Pull the reduction identity for `g₁` back across the quotient by `Jbar`.
    calc
      (Ideal.Quotient.mkₐ R I).comp φInf₁ =
          ((Ideal.Quotient.mkₐ R I).comp g₁).comp (Ideal.Quotient.mkₐ R Jbar) := by
            rfl
      _ =
          (f.comp
            (IsScalarTower.toAlgHom R
              (selfPresentation_section_quotient (R := R) (S := S) l).Ring S)).comp
            (Ideal.Quotient.mkₐ R Jbar) := by rw [hg₁]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R
                (selfPresentation_section_quotient (R := R) (S := S) l).Ring S).comp
              (Ideal.Quotient.mkₐ R Jbar)) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by rw [hquot]
  have hφInf₂ :
      (Ideal.Quotient.mkₐ R I).comp φInf₂ =
        f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by
    -- The same reduction identity holds for the second quotient lift.
    calc
      (Ideal.Quotient.mkₐ R I).comp φInf₂ =
          ((Ideal.Quotient.mkₐ R I).comp g₂).comp (Ideal.Quotient.mkₐ R Jbar) := by
            rfl
      _ =
          (f.comp
            (IsScalarTower.toAlgHom R
              (selfPresentation_section_quotient (R := R) (S := S) l).Ring S)).comp
            (Ideal.Quotient.mkₐ R Jbar) := by rw [hg₂]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R
                (selfPresentation_section_quotient (R := R) (S := S) l).Ring S).comp
              (Ideal.Quotient.mkₐ R Jbar)) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by rw [hquot]
  have hInfquot :
      (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S).comp
        (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) =
        IsScalarTower.toAlgHom R P0.Ring S := by
    -- Passing from `P0` to `P0/ker²` does not change the reduction to `S`.
    exact AlgHom.ext fun _ ↦ rfl
  let β₁ : P0.Ring →ₐ[R] A := φInf₁.comp (Ideal.Quotient.mkₐ R (P0.ker ^ 2))
  let β₂ : P0.Ring →ₐ[R] A := φInf₂.comp (Ideal.Quotient.mkₐ R (P0.ker ^ 2))
  have hβ₁ :
      (Ideal.Quotient.mkₐ R I).comp β₁ =
        f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by
    -- Re-express the first quotient lift as a polynomial-owner lift.
    calc
      (Ideal.Quotient.mkₐ R I).comp β₁ =
          ((Ideal.Quotient.mkₐ R I).comp φInf₁).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by
              rfl
      _ =
          (f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S)).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by rw [hφInf₁]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R P0.infinitesimal.Ring S).comp
              (Ideal.Quotient.mkₐ R (P0.ker ^ 2))) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by rw [hInfquot]
  have hβ₂ :
      (Ideal.Quotient.mkₐ R I).comp β₂ =
        f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by
    -- The second quotient lift yields the same owner-level reduction.
    calc
      (Ideal.Quotient.mkₐ R I).comp β₂ =
          ((Ideal.Quotient.mkₐ R I).comp φInf₂).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by
              rfl
      _ =
          (f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S)).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by rw [hφInf₂]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R P0.infinitesimal.Ring S).comp
              (Ideal.Quotient.mkₐ R (P0.ker ^ 2))) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by rw [hInfquot]
  obtain ⟨φ₁, hφ₁⟩ :=
    selfPresentation_polynomial_lift_to_extension_hom
      (R := R) (S := S) I f β₁ hβ₁
  obtain ⟨φ₂, hφ₂⟩ :=
    selfPresentation_polynomial_lift_to_extension_hom
      (R := R) (S := S) I f β₂ hβ₂
  have hφInf_eq₁ :
      selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₁ = φInf₁ := by
    -- Both infinitesimal maps agree after precomposing with the quotient map from `P0.Ring`.
    refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
    rw [selfPresentation_infinitesimal_lift]
    change φ₁.toAlgHom x = φInf₁ (Ideal.Quotient.mk (P0.ker ^ 2) x)
    rw [hφ₁]
    rfl
  have hφInf_eq₂ :
      selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₂ = φInf₂ := by
    -- The same comparison identifies the second pulled-back owner with its infinitesimal lift.
    refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
    rw [selfPresentation_infinitesimal_lift]
    change φ₂.toAlgHom x = φInf₂ (Ideal.Quotient.mk (P0.ker ^ 2) x)
    rw [hφ₂]
    rfl
  have hJbar₁ : Jbar ≤ RingHom.ker φInf₁.toRingHom := by
    -- Because `φInf₁` factors through the quotient by `Jbar`, it kills `Jbar` tautologically.
    intro y hy
    change g₁ (Ideal.Quotient.mk Jbar y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact map_zero g₁
  have hJbar₂ : Jbar ≤ RingHom.ker φInf₂.toRingHom := by
    -- The same tautological vanishing holds for `φInf₂`.
    intro y hy
    change g₂ (Ideal.Quotient.mk Jbar y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact map_zero g₂
  have hvanish₁ : (Extension.Cotangent.map φ₁) ∘ₗ l = 0 := by
    -- Reverse the quotient-kernel containment back into vanishing of the cotangent obstruction.
    have hker₁ :
        selfPresentation_section_image_ideal (R := R) (S := S) l ≤
          RingHom.ker (selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₁).toRingHom := by
      intro y hy
      change selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₁ y = 0
      rw [hφInf_eq₁]
      exact hJbar₁ <| by simpa [Jbar] using hy
    exact selfPresentation_cotangent_vanish_of_section_image_ideal_le_ker
      (R := R) (S := S) Q hQsq φ₁ l hker₁
  have hvanish₂ : (Extension.Cotangent.map φ₂) ∘ₗ l = 0 := by
    -- The second owner lift has the same vanishing obstruction on the chosen section.
    have hker₂ :
        selfPresentation_section_image_ideal (R := R) (S := S) l ≤
          RingHom.ker (selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₂).toRingHom := by
      intro y hy
      change selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φ₂ y = 0
      rw [hφInf_eq₂]
      exact hJbar₂ <| by simpa [Jbar] using hy
    exact selfPresentation_cotangent_vanish_of_section_image_ideal_le_ker
      (R := R) (S := S) Q hQsq φ₂ l hker₂
  have hsub_zero : φ₁.sub φ₂ = 0 := by
    -- Route correction: compare the two owner lifts only at the infinitesimal layer. The section
    -- `l` splits `P0.cotangentComplex`, so vanishing on `l` forces the homotopy difference to be
    -- zero everywhere.
    apply LinearMap.ext
    intro x
    have hsplit : P0.cotangentComplex (l x) = x := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hl x
    have hmap :
        Extension.Cotangent.map φ₁ (l x) - Extension.Cotangent.map φ₂ (l x) =
          φ₁.sub φ₂ (P0.cotangentComplex (l x)) := by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun (Extension.Cotangent.map_sub_map φ₁ φ₂) (l x)
    have hzero₁ : Extension.Cotangent.map φ₁ (l x) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hvanish₁ x
    have hzero₂ : Extension.Cotangent.map φ₂ (l x) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hvanish₂ x
    calc
      φ₁.sub φ₂ x = φ₁.sub φ₂ (P0.cotangentComplex (l x)) := by rw [hsplit]
      _ = Extension.Cotangent.map φ₁ (l x) - Extension.Cotangent.map φ₂ (l x) := by
            rw [← hmap]
      _ = 0 := by rw [hzero₁, hzero₂, sub_self]
  have hφInf :
      φInf₁ = φInf₂ := by
    -- Zero owner homotopy difference is exactly the input needed to compare the infinitesimal
    -- quotient lifts.
    rw [← hφInf_eq₁, ← hφInf_eq₂]
    exact selfPresentation_infinitesimal_lift_eq_of_sub_eq_zero
      (R := R) (S := S) Q hQsq φ₁ φ₂ hsub_zero
  -- The quotient by `Jbar` is determined by its pullback to the infinitesimal self presentation.
  refine Ideal.Quotient.algHom_ext (R₁ := R) (I := Jbar) ?_
  simpa [φInf₁, φInf₂] using hφInf

/-- Lemma 10.149.1: if `R → S` is formally unramified, then there exists an `R`-algebra extension
`P → S` with square-zero kernel such that every map `S → A ⧸ I` to a square-zero quotient lifts
uniquely to an `R`-algebra map `P.Ring → A`. -/
theorem exists_universal_squareZeroThickening [Algebra.FormallyUnramified R S] :
    ∃ P : Extension.{max u v} R S, P.IsUniversalFirstOrderThickening := by
  -- Route correction: first stabilize the Stacks construction of the quotient extension cut out by
  -- a section of the cotangent complex; the remaining blocker is the owner-form lifting argument.
  obtain ⟨l, hl⟩ := selfPresentation_cotangentComplex_has_section (R := R) (S := S)
  let P : Extension.{max u v} R S := selfPresentation_section_quotient (R := R) (S := S) l
  have hsq : P.ker ^ 2 = ⊥ := by
    simpa [P] using selfPresentation_section_quotient_square_zero (R := R) (S := S) l
  refine ⟨P, hsq, ?_⟩
  intro A _ _ I hI f
  obtain ⟨β, hβ⟩ :=
    selfPresentation_exists_polynomial_lift
      (R := R) (S := S) (A := A) I hI f
  let _ : Algebra S (A ⧸ I) := f.toAlgebra
  let P0 : Extension R S := (Generators.self R S).toExtension
  let Q : Extension R (A ⧸ I) :=
    Extension.ofSurjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
  obtain ⟨φ, rfl⟩ :=
    selfPresentation_polynomial_lift_to_extension_hom
      (R := R) (S := S) I f β hβ
  have hQsq : Q.ker ^ 2 = ⊥ := by
    simpa [Q] using squareZeroQuotient_extension_square_zero (R := R) (I := I) hI
  obtain ⟨φu, hφu⟩ :=
    selfPresentation_corrected_extension_hom_cotangent_vanish
      (R := R) (S := S) Q hQsq φ l hl
  let φInf := selfPresentation_infinitesimal_lift (R := R) (S := S) Q hQsq φu
  have hφInf :
      (Ideal.Quotient.mkₐ R I).comp φInf =
        f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by
    -- The corrected owner map already descends through `P0.ker²`, so we can work on the
    -- infinitesimal self presentation before handling the section-image quotient.
    simpa [φInf, Q] using
      selfPresentation_infinitesimal_lift_comp_eq (R := R) (S := S) Q hQsq φu
  have hφInf_zero :
      ∀ x : P0.CotangentSpace,
        φInf
            (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
              P0.ker.cotangentIdeal)).1 = 0 := by
    -- The corrected owner map was chosen so that its cotangent obstruction vanishes on the chosen
    -- section, hence every explicit section generator already maps to zero.
    intro x
    exact selfPresentation_section_generator_image_eq_zero_of_cotangent_vanish
      (R := R) (S := S) Q hQsq φu l hφu x
  obtain ⟨g, hg⟩ :=
    selfPresentation_factor_through_section_quotient_of_cotangent_vanish
      (R := R) (S := S) (A := A) I f l φInf hφInf hφInf_zero
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  exact (selfPresentation_factored_lift_unique
    (R := R) (S := S) (A := A) I f l hl hI g g' hg hg').symm

/-! ### Definition_10_149_2 (from Chap10) -/
noncomputable section

open Algebra

universe u v w

namespace Algebra.Extension

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling for Definition 10.149.2:
- primary domain: commutative-ring extensions, square-zero thickenings, and the conormal/cotangent
  module attached to an extension;
- sampled owner declarations:
  `Extension.Cotangent`,
  `Extension.cotangentEquivCotangentKer`,
  `Extension.Cotangent.mk`,
  `Extension.Cotangent.map`;
- best owner abstraction: the mathlib owner `Extension.Cotangent`, i.e. the cotangent module
  `P.ker / P.ker²` attached to an extension `P : Extension R S`;
- primitive data vs. derived API:
  the primitive data are only the extension `P` and its kernel ideal `P.ker`,
  while the source-facing conormal module for a square-zero thickening is the same kernel ideal
  with its induced `S`-module structure, and its bridge to the owner `Extension.Cotangent` is
  derived API;
- source/core/bridge triage:
  `source-facing`: the universal first-order thickening predicate on an extension and the conormal
  module of a chosen universal thickening,
  `core/canonical`: `Extension.Cotangent`,
  `bridge/view`: the source-defined conormal module is the square-zero kernel ideal of the chosen
  universal thickening, regarded as an `S`-module and canonically equivalent to
  `Extension.Cotangent`, so the file should expose that thin bridge instead of a parallel owner. -/

/-- An `R`-algebra extension `P → S` is a universal first-order thickening if it has square-zero
kernel and satisfies the expected unique lifting property against square-zero quotients. -/
def IsUniversalFirstOrderThickening (P : Extension R S) : Prop :=
  P.ker ^ 2 = ⊥ ∧
    ∀ {A : Type w} [CommRing A] [Algebra R A] (I : Ideal A) (_ : I ^ 2 = ⊥)
      (f : S →ₐ[R] A ⧸ I),
        ∃! f' : P.Ring →ₐ[R] A,
          (Ideal.Quotient.mkₐ R I).comp f' = f.comp (IsScalarTower.toAlgHom R P.Ring S)

variable (P : Extension R S)

/-- The kernel of a universal first-order thickening is square-zero. -/
theorem IsUniversalFirstOrderThickening.square_zero
    (hP : P.IsUniversalFirstOrderThickening) : P.ker ^ 2 = ⊥ :=
  hP.1

/-- For a square-zero extension `P → S`, the source-facing conormal module is the kernel ideal
viewed as an `S`-module through the quotient `P.Ring ⟶ S`. -/
def ConormalModule (_ : P.ker ^ 2 = ⊥) : Type _ := P.ker

namespace ConormalModule

attribute [local simp] RingHom.mem_ker

variable {P}
variable {hsq : P.ker ^ 2 = ⊥}

/-- The identity map from the kernel ideal into the conormal module type synonym. -/
def of (x : P.ker) : ConormalModule P hsq := x

/-- The identity map from the conormal module type synonym back to the kernel ideal. -/
def val (x : ConormalModule P hsq) : P.ker := x

@[simp] lemma of_val (x : ConormalModule P hsq) : of x.val = x := rfl
@[simp] lemma val_of (x : P.ker) : ((of x : ConormalModule P hsq)).val = x := rfl

@[ext] lemma ext {x y : ConormalModule P hsq} (h : x.val = y.val) : x = y := h

instance : AddCommGroup (ConormalModule P hsq) := inferInstanceAs (AddCommGroup P.ker)

lemma mul_eq_zero_of_mem (x : P.Ring) (hx : x ∈ P.ker) (y : ConormalModule P hsq) :
    x * y.val = 0 := by
  have hxy : x * y.val ∈ P.ker ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx y.val.2
  simpa [hsq, Ideal.mem_bot] using hxy

noncomputable instance : SMul S (ConormalModule P hsq) where
  smul r x := of ⟨P.σ r * x.val, Ideal.mul_mem_left _ _ x.val.2⟩

@[simp] lemma val_smul (r : S) (x : ConormalModule P hsq) :
    (r • x).val = ⟨P.σ r * x.val, Ideal.mul_mem_left _ _ x.val.2⟩ := rfl

noncomputable instance : Module S (ConormalModule P hsq) where
  smul_zero r := by
    apply ext
    apply Subtype.ext
    exact mul_zero (P.σ r)
  smul_add r x y := by
    apply ext
    apply Subtype.ext
    exact mul_add (P.σ r) x.val y.val
  add_smul r s x := by
    apply ext
    apply Subtype.ext
    have hzero := mul_eq_zero_of_mem
      (P.σ (r + s) - (P.σ r + P.σ s)) (by simp) x
    simpa [sub_eq_zero, sub_mul, add_mul] using hzero
  zero_smul x := by
    apply ext
    apply Subtype.ext
    exact mul_eq_zero_of_mem (P.σ 0) (by simp) x
  one_smul x := by
    apply ext
    apply Subtype.ext
    have hzero := mul_eq_zero_of_mem (P.σ 1 - 1) (by simp) x
    simpa [sub_eq_zero, sub_mul] using hzero
  mul_smul r s x := by
    apply ext
    apply Subtype.ext
    have hzero := mul_eq_zero_of_mem
      (P.σ (r * s) - P.σ r * P.σ s) (by simp) x
    simpa [sub_eq_zero, sub_mul, mul_assoc] using hzero

noncomputable instance {R₀ : Type*} [CommRing R₀] [Algebra R₀ S] :
    Module R₀ (ConormalModule P hsq) :=
  Module.compHom _ (algebraMap R₀ S)

end ConormalModule

/-- Over the base ring `R`, the raw kernel ideal and the source-facing conormal module of a
square-zero extension are canonically identified. -/
noncomputable def kerEquivConormalModuleOfSquareZeroRestrictScalars
    (hsq : P.ker ^ 2 = ⊥) : P.ker ≃ₗ[R] ConormalModule P hsq := by
  let toConormal : P.ker →ₗ[R] ConormalModule P hsq :=
    { toFun := fun x ↦ (ConormalModule.of x : ConormalModule P hsq)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro r x
        apply ConormalModule.ext
        apply Subtype.ext
        have hk : P.σ (algebraMap R S r) - algebraMap R P.Ring r ∈ P.ker := by
          change algebraMap P.Ring S
              (P.σ (algebraMap R S r) - algebraMap R P.Ring r) = 0
          rw [map_sub, P.algebraMap_σ, IsScalarTower.algebraMap_eq R P.Ring S]
          simp
        have hzero := ConormalModule.mul_eq_zero_of_mem
          (P.σ (algebraMap R S r) - algebraMap R P.Ring r) hk
          (ConormalModule.of x : ConormalModule P hsq)
        have hEq : P.σ (algebraMap R S r) * x = (algebraMap R P.Ring r) * x := by
          simpa [sub_eq_zero, sub_mul] using hzero
        simpa [ConormalModule.val_smul, Algebra.smul_def] using hEq.symm }
  refine LinearEquiv.ofBijective toConormal ⟨?_, ?_⟩
  · intro x y h
    exact by simpa using congrArg ConormalModule.val h
  · intro x
    exact ⟨x.val, by rfl⟩

/-- For a square-zero extension `P → S`, the source-facing conormal module is canonically
identified with the owner cotangent module `P.Cotangent`. -/
noncomputable def conormalModuleEquivCotangentOfSquareZero
    (hsq : P.ker ^ 2 = ⊥) : ConormalModule P hsq ≃ₗ[S] P.Cotangent := by
  let mk : ConormalModule P hsq →ₗ[S] P.Cotangent :=
    { toFun := fun x ↦ Extension.Cotangent.mk x.val
      map_add' := by
        intro x y
        exact (Ideal.toCotangent P.ker).map_add x.val y.val
      map_smul' := by
        intro r x
        apply Extension.Cotangent.ext
        exact (Ideal.toCotangent P.ker).map_smul (P.σ r) x.val }
  refine LinearEquiv.ofBijective mk ⟨?_, ?_⟩
  · intro x y hxy
    apply ConormalModule.ext
    apply Subtype.ext
    have hmem : x.val.1 - y.val.1 ∈ P.ker ^ 2 :=
      (Extension.Cotangent.mk_eq_mk_iff_sub_mem x.val y.val).mp hxy
    exact sub_eq_zero.mp <| by
      simpa [hsq, Ideal.mem_bot] using hmem
  · intro x
    have hmk :
        Function.Surjective (Extension.Cotangent.mk : P.ker →ₗ[P.Ring] P.Cotangent) :=
      Extension.Cotangent.mk_surjective
    obtain ⟨y, rfl⟩ := hmk x
    exact ⟨ConormalModule.of y, rfl⟩

/-- The `R`-linear companion of
`conormalModuleEquivCotangentOfSquareZero`, used when comparing the conormal module to owners that
still live over the base ring. -/
noncomputable def conormalModuleEquivCotangentOfSquareZeroRestrictScalars
    (hsq : P.ker ^ 2 = ⊥) : ConormalModule P hsq ≃ₗ[R] P.Cotangent where
  toFun := conormalModuleEquivCotangentOfSquareZero P hsq
  invFun := (conormalModuleEquivCotangentOfSquareZero P hsq).symm
  left_inv := (conormalModuleEquivCotangentOfSquareZero P hsq).left_inv
  right_inv := (conormalModuleEquivCotangentOfSquareZero P hsq).right_inv
  map_add' _ _ := (conormalModuleEquivCotangentOfSquareZero P hsq).map_add _ _
  map_smul' _ _ := rfl

@[simp] theorem conormalModuleEquivCotangentOfSquareZero_apply
    (hsq : P.ker ^ 2 = ⊥) (x : ConormalModule P hsq) :
    conormalModuleEquivCotangentOfSquareZero P hsq x = Extension.Cotangent.mk x.val :=
  rfl

/-- Definition 10.149.2: if `P` is a universal first-order thickening of the `R`-algebra `S`,
then the source-defined conormal module `C_{S/R}` is the square-zero kernel of `P`, viewed as an
`S`-module, and it is canonically identified with the owner cotangent module `P.Cotangent`. -/
noncomputable def conormalModuleEquivCotangent
    (hP : P.IsUniversalFirstOrderThickening) :
    ConormalModule P hP.square_zero ≃ₗ[S] P.Cotangent :=
  conormalModuleEquivCotangentOfSquareZero P hP.square_zero

/-- The base-ring linear companion of `conormalModuleEquivCotangent`, for source-facing conormal
comparisons that are still formulated over `R`. -/
noncomputable def conormalModuleEquivCotangentRestrictScalars
    (hP : P.IsUniversalFirstOrderThickening) :
    ConormalModule P hP.square_zero ≃ₗ[R] P.Cotangent :=
  conormalModuleEquivCotangentOfSquareZeroRestrictScalars P hP.square_zero

end Algebra.Extension

/-! ### Lemma_10_149_3 (from Chap10) -/
open Algebra
open Algebra.Extension
open Ideal.Quotient (eq_zero_iff_mem)

universe u

noncomputable section

section

variable {R : Type u} [CommRing R] (I : Ideal R)

/- Domain-style sampling:
* primary domain: square-zero quotient thickenings of commutative rings and their conormal modules;
* sampled owner declarations:
  - `Ideal.Quotient.factorₐ`, the canonical quotient map `R ⧸ I² →ₐ[R] R ⧸ I`;
  - `Extension.ofSurjective`, the owner abstraction packaging a surjective algebra map as an
    extension;
  - `Extension.conormalModuleEquivCotangent`, the Chapter 10 bridge from a square-zero kernel ideal
    with its induced `R ⧸ I`-module structure to the owner cotangent module of a universal
    first-order thickening;
  - `Ideal.cotangentEquivIdeal`, the canonical bridge from `I / I²` to the square-zero kernel
    ideal inside `R ⧸ I²`.
* best owner abstraction: the source-facing quotient thickening should be expressed through the
  owner-level quotient map `Ideal.Quotient.factorₐ` and the extension it induces via
  `Extension.ofSurjective`; the conormal module statement should use the canonical linear
  equivalence to `I.Cotangent`, not a noncanonical type equality.
* primitive data vs. derived API:
  - primitive data: the ideal `I` and the canonical quotient map `R ⧸ I² →ₐ[R] R ⧸ I`;
  - derived API: the induced extension and the canonical equivalence from its conormal module to
    `I / I²`.
* layer triage:
  - `source-facing`: the quotient thickening `R ⧸ I² → R ⧸ I` and its conormal module;
  - `core/canonical`: `Ideal.Quotient.factorₐ`, `Extension.ofSurjective`, and `I.Cotangent`;
  - `bridge/view`: the identification of the kernel ideal of `R ⧸ I² → R ⧸ I` with
    `I.cotangentIdeal`. -/

-- Proof sketch: every class in `R ⧸ I` is represented by some `r : R`, and the class of the same
-- `r` in `R ⧸ I²` maps to it.
private theorem quotientIdealSquareFactor_surjective :
    Function.Surjective
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
        (R ⧸ I ^ 2) →ₐ[R] R ⧸ I) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

local notation "quotSqMap" =>
  (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
    (R ⧸ I ^ 2) →ₐ[R] R ⧸ I)

local notation "quotSqExt" =>
  Extension.ofSurjective quotSqMap (quotientIdealSquareFactor_surjective I)

/-- Helper for Lemma 10.149.3: the kernel of the quotient map `R ⧸ I² → R ⧸ I` is the canonical
copy of `I / I²` inside `R ⧸ I²`. -/
lemma quotientIdealSquareFactor_ker_eq_cotangentIdeal :
    RingHom.ker
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
          (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom =
      I.cotangentIdeal := by
  -- Compute the kernel as the image ideal of `I` in the quotient by `I²`.
  have h :
      RingHom.ker
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
            (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom =
        I.map (Ideal.Quotient.mk (I ^ 2)) := by
    simpa [Ideal.Quotient.factorₐ, Ideal.Quotient.factor, Ideal.mk_ker] using
      (Ideal.ker_quotient_lift
        (Ideal.Quotient.mk I)
        (fun x hx ↦ eq_zero_iff_mem.mpr (Ideal.pow_le_self two_ne_zero hx)))
  -- The quotient-side image ideal is exactly `I.cotangentIdeal`.
  rw [Ideal.map_eq_submodule_map] at h
  exact h

/-- Helper for Lemma 10.149.3: the structure map of the quotient extension is the canonical
quotient map `R ⧸ I² → R ⧸ I`. -/
lemma quotSqExt_toAlgHom_eq_factor :
    IsScalarTower.toAlgHom R (quotSqExt : Extension R (R ⧸ I)).Ring (R ⧸ I) = quotSqMap :=
  rfl

/-- Helper for Lemma 10.149.3: a map `R/I → A/J` into a square-zero quotient kills `I²` after
lifting representatives along `R → A`. -/
lemma algebraMap_zero_of_mem_square_of_square_zero_quotient
    {A : Type*} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (f : R ⧸ I →ₐ[R] A ⧸ J)
    {x : R} (hx : x ∈ I ^ 2) :
    algebraMap R A x = 0 := by
  -- First show that elements of `I` land inside `J`.
  have hIle : I ≤ J.comap (algebraMap R A) := by
    intro y hy
    change algebraMap R A y ∈ J
    have hy0 : (Ideal.Quotient.mk I y : R ⧸ I) = 0 := eq_zero_iff_mem.mpr hy
    have hleft : f (Ideal.Quotient.mk I y) = 0 := by
      simpa [hy0] using congrArg f hy0
    have hcomm := f.commutes y
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.alg_map_eq] at hcomm
    rw [hcomm] at hleft
    exact eq_zero_iff_mem.mp (by simpa [RingHom.comp_apply] using hleft)
  -- Then square-zero of `J` forces every element of `I²` to map to zero.
  have hcomap_sq :
      (J.comap (algebraMap R A)) ^ 2 ≤ RingHom.ker (algebraMap R A) := by
    intro z hz
    have hz' : z ∈ (J ^ 2).comap (algebraMap R A) :=
      (Ideal.le_comap_pow (f := algebraMap R A) (K := J) 2) hz
    have : algebraMap R A z ∈ (⊥ : Ideal A) := by
      simpa [hJ] using hz'
    simpa [RingHom.mem_ker] using this
  have hsq :
      I ^ 2 ≤ RingHom.ker (algebraMap R A) := by
    exact (Ideal.pow_right_mono hIle 2).trans hcomap_sq
  simpa [RingHom.mem_ker] using hsq hx

/-- Helper for Lemma 10.149.3: the descended map `R/I² → A` reduces modulo `J` to the original
map `R/I → A/J`. -/
lemma quotientIdealSquare_lift_comp_eq
    {A : Type*} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (f : R ⧸ I →ₐ[R] A ⧸ J) :
    let lift : R ⧸ I ^ 2 →ₐ[R] A :=
      Ideal.Quotient.liftₐ (I ^ 2) (Algebra.ofId R A)
        (fun _ hx ↦
          algebraMap_zero_of_mem_square_of_square_zero_quotient
            (R := R) (I := I) J hJ f hx)
    (Ideal.Quotient.mkₐ R J).comp lift = f.comp quotSqMap := by
  intro lift
  -- Compare both maps after precomposing with the quotient map from `R`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) <|
    AlgHom.ext fun x ↦ (f.commutes x).symm

-- Proof sketch: identify the canonical quotient extension `R ⧸ I² → R ⧸ I` with the
-- infinitesimal extension attached to `R → R ⧸ I`, then apply the universal square-zero lifting
-- property of that infinitesimal extension.
/-- Lemma 10.149.3 (1): the universal first-order thickening of `R ⧸ I` over `R` is the canonical
quotient extension `R ⧸ I² → R ⧸ I`. -/
theorem quotientIdealFirstOrderThickening_isUniversal :
    (quotSqExt : Extension R (R ⧸ I)).IsUniversalFirstOrderThickening :=
  by
    refine ⟨?_, ?_⟩
    · -- The kernel is `I/I²`, so its square vanishes by the cotangent-ideal calculation.
      have hker : (quotSqExt : Extension R (R ⧸ I)).ker = I.cotangentIdeal := by
        change RingHom.ker
            ((Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
                (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom) = I.cotangentIdeal
        exact quotientIdealSquareFactor_ker_eq_cotangentIdeal (R := R) (I := I)
      rw [hker]
      exact Ideal.cotangentIdeal_square I
    · intro A _ _ J hJ f
      rw [quotSqExt_toAlgHom_eq_factor (R := R) (I := I)]
      let lift : R ⧸ I ^ 2 →ₐ[R] A :=
        Ideal.Quotient.liftₐ (I ^ 2) (Algebra.ofId R A)
          (fun _ hx ↦
            algebraMap_zero_of_mem_square_of_square_zero_quotient
              (R := R) (I := I) (A := A) J hJ f hx)
      refine ⟨lift, ?_, ?_⟩
      · -- The descended algebra map is the lift required by the universal square.
        exact quotientIdealSquare_lift_comp_eq (R := R) (I := I) J hJ f
      · intro g hg
        -- Any `R`-algebra map out of `R/I²` is determined by its values on representatives from `R`.
        refine Ideal.Quotient.algHom_ext (R₁ := R) <| by
          calc
            g.comp (Ideal.Quotient.mkₐ R (I ^ 2)) = Algebra.ofId R A := by
              exact AlgHom.ext fun x ↦ g.commutes x
            _ = lift.comp (Ideal.Quotient.mkₐ R (I ^ 2)) := by
              symm
              exact Ideal.Quotient.liftₐ_comp (I ^ 2) (Algebra.ofId R A)
                (fun _ hx ↦
                  algebraMap_zero_of_mem_square_of_square_zero_quotient
                    (R := R) (I := I) (A := A) J hJ f hx)

-- Proof sketch: the conormal module of a universal first-order thickening is its cotangent module,
-- and for the quotient extension `R ⧸ I² → R ⧸ I` the kernel ideal is `I.cotangentIdeal`, whose
-- square is zero and whose underlying `R`-module is canonically `I/I²`.
/-- Lemma 10.149.3 (2): the conormal module of `R ⧸ I` over `R`, computed from the canonical
quotient thickening `R ⧸ I² → R ⧸ I`, is canonically isomorphic to `I / I²`. -/
noncomputable def quotientIdeal_conormalModuleEquiv :
    (quotSqExt : Extension R (R ⧸ I)).Cotangent ≃ₗ[R ⧸ I] I.Cotangent := by
  let P : Extension R (R ⧸ I) := quotSqExt
  let hP : P.IsUniversalFirstOrderThickening := quotientIdealFirstOrderThickening_isUniversal I
  -- Reuse the quotient-kernel identification from the universal-thickening proof.
  have hker : P.ker = I.cotangentIdeal := by
    change RingHom.ker
        ((Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
            (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom) = I.cotangentIdeal
    exact quotientIdealSquareFactor_ker_eq_cotangentIdeal (R := R) (I := I)
  let eEq : I.cotangentIdeal ≃ₗ[R] ConormalModule P hP.square_zero :=
    ((LinearEquiv.ofEq I.cotangentIdeal P.ker hker.symm).restrictScalars R).trans <|
      kerEquivConormalModuleOfSquareZeroRestrictScalars P hP.square_zero
  let eR : I.Cotangent ≃ₗ[R] P.Cotangent :=
    (Ideal.cotangentEquivIdeal I).trans <|
      eEq.trans <|
        conormalModuleEquivCotangentRestrictScalars.{u, u, u, u} P hP
  have hquot : Function.Surjective (algebraMap R (R ⧸ I)) := by
    simpa [Ideal.Quotient.algebraMap_eq] using (Ideal.Quotient.mk_surjective : _)
  let _ : IsScalarTower R (R ⧸ I) I.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent I)
  exact (eR.extendScalarsOfSurjective hquot).symm

end
