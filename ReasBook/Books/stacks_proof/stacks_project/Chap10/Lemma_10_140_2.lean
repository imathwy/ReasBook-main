import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Lemma_10_140_1
import StacksProject_2024.Chap10.Lemma_10_140_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsAlgClosed k]
variable (m : Ideal S) [m.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/- Domain-style sampling for Lemma 10.140.2:
- primary domain: smoothness and regularity criteria at a closed point of a finite type
  `k`-algebra, expressed via the Kähler fiber and the cotangent space;
- sampled owner declarations:
  `smoothAtPrime_iff_isSmoothAt`,
  `isSmoothAt_tfae_finrank_kaehlerFiber_le_eq`,
  `isRegularLocalRing_of_isSmoothAt`,
  `finrank_kaehlerFiber_eq_finrank_cotangent`;
- best owner abstraction: the core/canonical owner is the primewise criterion
  `IsSmoothAt k q.asIdeal`, with the present file staying `source-facing` by packaging the closed
  point `q = ⟨m, inferInstance⟩`, the quotient-fiber form `κ(m) = S ⧸ m`, and the extra regular
  local clause from the Stacks statement;
- primitive data: the maximal ideal `m` of the finite type `k`-algebra `S`;
- derived API: the quotient presentation of the Kähler fiber at `m`, the cotangent comparison from
  `Lemma 10.140.1`, and the regular-local clause on `Localization.AtPrime m`.

Source/core/bridge triage:
- `source-facing`: the four-way closed-point `List.TFAE` statement in the quotient form used by the
  source text;
- `core/canonical`: `IsSmoothAt k m`, `IsRegularLocalRing (Localization.AtPrime m)`, and the
  prime-level three-way TFAE from `Lemma 10.140.3`;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt` and the closed-point quotient bridge
  `finrank_kaehlerFiber_eq_finrank_cotangent`. -/

omit [IsAlgClosed k] in
/-- Helper for Chap10 Lemma 10 140 2: replacing the residue field of a maximal ideal by the
quotient field does not change the Kähler-fiber dimension. -/
private theorem finrank_residueField_kaehlerFiber_eq_quotient :
    Module.finrank m.ResidueField (m.ResidueField ⊗[S] Ω[S⁄k]) =
      Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) := by
  -- The quotient-to-residue-field map is an isomorphism for a maximal ideal; base change records
  -- the same dimension after cancelling the intermediate tensor over `S ⧸ m`.
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ m) m.ResidueField
    m.ResidueField Ω[S⁄k]
  rw [← e.finrank_eq]
  exact Module.finrank_baseChange

omit [IsAlgClosed k] in
/-- Helper for Chap10 Lemma 10 140 2: at a closed point, smoothness is equivalent to the
quotient-field Kähler-fiber dimension bounds. -/
private theorem smoothAtPrime_tfae_finrank_kaehlerFiber_le_eq :
    List.TFAE
      ([ Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :
        List Prop) := by
  letI : Algebra.FinitePresentation k S :=
    (show Algebra.FiniteType k S ↔ Algebra.FinitePresentation k S from
      Algebra.FinitePresentation.of_finiteType).mp inferInstance
  let q : PrimeSpectrum S := ⟨m, inferInstance⟩
  have howner :
      List.TFAE
        [ Algebra.IsSmoothAt k m
        , Module.finrank (Ideal.ResidueField m)
            ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
        , Module.finrank (Ideal.ResidueField m)
            ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :=
    Algebra.isSmoothAt_tfae_finrank_kaehlerFiber_le_eq m
  have hsmooth :
      Algebra.SmoothAtPrime k S q ↔ Algebra.IsSmoothAt k q.asIdeal :=
    Algebra.smoothAtPrime_iff_isSmoothAt k S q
  have hfiberResidue := finrank_residueField_kaehlerFiber_eq_quotient (k := k) (S := S) m
  have howner_smooth_le :
      Algebra.IsSmoothAt k m ↔
        Module.finrank (Ideal.ResidueField m)
          ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m) :=
    howner.out 0 1
  have howner_le_eq :
      Module.finrank (Ideal.ResidueField m)
          ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m) ↔
        Module.finrank (Ideal.ResidueField m)
          ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) :=
    howner.out 1 2
  -- Transport the owner smoothness criterion from `Ideal.ResidueField m` to the quotient field.
  tfae_have 1 ↔ 2 := by
    simpa [q, hfiberResidue] using hsmooth.trans howner_smooth_le
  tfae_have 2 ↔ 3 := by
    simpa [hfiberResidue] using howner_le_eq
  tfae_finish

/-- Helper for Chap10 Lemma 10 140 2: an ideal maps into the comap of its image under an algebra
equivalence. -/
private theorem ideal_le_comap_map_algEquiv {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I ≤ Ideal.comap e.toAlgHom (I.map e.toRingHom) := by
  -- Membership in the image ideal gives the required comap membership.
  intro x hx
  exact Ideal.mem_map_of_mem e.toRingHom hx

/-- Helper for Chap10 Lemma 10 140 2: the image ideal under an algebra equivalence maps back into
the original ideal under the inverse equivalence. -/
private theorem ideal_map_algEquiv_le_comap_symm {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.map e.toRingHom ≤ Ideal.comap e.symm.toAlgHom I := by
  -- Rewrite the image ideal as the comap along the inverse ring equivalence.
  intro y hy
  change y ∈ Ideal.comap e.toRingEquiv.symm I
  rw [← Ideal.map_comap_of_equiv (I := I) e.toRingEquiv]
  exact hy

/-- Helper for Chap10 Lemma 10 140 2: the forward cotangent map induced by an algebra
equivalence. -/
private noncomputable def cotangentMapAlgEquivForward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent →ₗ[R] (I.map e.toRingHom).Cotangent :=
  I.mapCotangent (I.map e.toRingHom) e.toAlgHom (ideal_le_comap_map_algEquiv e I)

/-- Helper for Chap10 Lemma 10 140 2: the backward cotangent map induced by the inverse algebra
equivalence. -/
private noncomputable def cotangentMapAlgEquivBackward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    (I.map e.toRingHom).Cotangent →ₗ[R] I.Cotangent :=
  (I.map e.toRingHom).mapCotangent I e.symm.toAlgHom
    (ideal_map_algEquiv_le_comap_symm e I)

/-- Helper for Chap10 Lemma 10 140 2: the forward cotangent map after the backward map is the
identity. -/
private theorem cotangentMapAlgEquiv_forward_comp_backward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    cotangentMapAlgEquivForward e I ∘ₗ cotangentMapAlgEquivBackward e I = LinearMap.id := by
  -- It is enough to check the identity on cotangent quotient generators.
  ext y
  obtain ⟨y, rfl⟩ := (I.map e.toRingHom).toCotangent_surjective y
  rw [LinearMap.comp_apply]
  unfold cotangentMapAlgEquivForward cotangentMapAlgEquivBackward
  rw [Ideal.mapCotangent_toCotangent]
  rw [Ideal.mapCotangent_toCotangent]
  apply (I.map e.toRingHom).toCotangent_eq.mpr
  simp

/-- Helper for Chap10 Lemma 10 140 2: the backward cotangent map after the forward map is the
identity. -/
private theorem cotangentMapAlgEquiv_backward_comp_forward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    cotangentMapAlgEquivBackward e I ∘ₗ cotangentMapAlgEquivForward e I = LinearMap.id := by
  -- The inverse identity is checked on the original cotangent quotient generators.
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [LinearMap.comp_apply]
  unfold cotangentMapAlgEquivForward cotangentMapAlgEquivBackward
  rw [Ideal.mapCotangent_toCotangent]
  rw [Ideal.mapCotangent_toCotangent]
  apply I.toCotangent_eq.mpr
  simp

/-- Helper for Chap10 Lemma 10 140 2: an algebra equivalence transports the cotangent space of
an ideal to the cotangent space of its image ideal. -/
private noncomputable def cotangentEquivMapAlgEquiv {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent ≃ₗ[R] (I.map e.toRingHom).Cotangent :=
  LinearEquiv.ofLinear (cotangentMapAlgEquivForward e I) (cotangentMapAlgEquivBackward e I)
    (cotangentMapAlgEquiv_forward_comp_backward e I)
    (cotangentMapAlgEquiv_backward_comp_forward e I)

/-- Helper for Chap10 Lemma 10 140 2: the extension of a maximal ideal to its localization at
that ideal is the maximal ideal of the local ring. -/
private theorem localizedIdeal_eq_maximalIdeal :
    m.map (algebraMap S (Localization.AtPrime m)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  -- This is exactly the at-prime localization computation for maximal ideals.
  simpa using (Localization.AtPrime.map_eq_maximalIdeal (I := m))

/-- Helper for Chap10 Lemma 10 140 2: under the tensor-product right-unit equivalence, the
tensor-extended ideal is the usual localized ideal. -/
private theorem map_tensorIdeal_eq_localizedIdeal :
    Ideal.map
        (Algebra.TensorProduct.rid S (Localization.AtPrime m) (Localization.AtPrime m)).toRingHom
        (Ideal.map
          (Algebra.TensorProduct.includeRight.toRingHom :
            S →+* Localization.AtPrime m ⊗[S] S) m) =
      Ideal.map (algebraMap S (Localization.AtPrime m)) m := by
  -- Push the two ideal maps into one ring hom and compare the resulting maps on elements of `S`.
  rw [Ideal.map_map]
  congr 1
  ext x
  simp [Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

/-- Helper for Chap10 Lemma 10 140 2: after extending scalars to the residue field of
`Sₘ`, the closed-point cotangent space identifies with the cotangent space of the local ring. -/
private theorem finrank_residueTensor_cotangent_eq_localization :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.ResidueField (Localization.AtPrime m) ⊗[S ⧸ m] m.Cotangent) =
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) := by
  let T := Localization.AtPrime m
  let K := IsLocalRing.ResidueField T
  letI : IsScalarTower S (S ⧸ m) m.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent (R := S) (I := m))
  haveI : Algebra.IsEpi S (S ⧸ m) :=
    Algebra.isEpi_of_surjective_algebraMap S (S ⧸ m) Ideal.Quotient.mk_surjective
  -- First cancel the redundant quotient base-change from `S` to `S ⧸ m`.
  let eQuot : K ⊗[S ⧸ m] m.Cotangent ≃ₗ[K] K ⊗[S] m.Cotangent :=
    let e₁ : (S ⧸ m) ⊗[S] m.Cotangent ≃ₗ[S ⧸ m] m.Cotangent :=
      TensorProduct.lid' S (S ⧸ m) m.Cotangent
    let e₂ : K ⊗[S ⧸ m] ((S ⧸ m) ⊗[S] m.Cotangent) ≃ₗ[K]
        K ⊗[S] m.Cotangent :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ m) K K m.Cotangent
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e₁.symm).trans e₂
  -- Then insert the localization base-change and apply the flat cotangent base-change theorem.
  let eLocBase : K ⊗[S] m.Cotangent ≃ₗ[K] K ⊗[T] (T ⊗[S] m.Cotangent) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S T K K m.Cotangent).symm
  let tensorIdeal : Ideal (T ⊗[S] S) :=
    m.map (Algebra.TensorProduct.includeRight.toRingHom : S →+* T ⊗[S] S)
  let eTensorCot : K ⊗[T] (T ⊗[S] m.Cotangent) ≃ₗ[K]
      K ⊗[T] tensorIdeal.Cotangent :=
    let e : T ⊗[S] m.Cotangent ≃ₗ[T] tensorIdeal.Cotangent :=
      Ideal.tensorCotangentEquiv S T m
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e
  -- Normalize the tensor-product target ideal to the maximal ideal of the local ring.
  let eRid : T ⊗[S] S ≃ₐ[T] T := Algebra.TensorProduct.rid S T T
  have hTensorIdeal : tensorIdeal.map eRid.toRingHom = m.map (algebraMap S T) := by
    simpa [T, tensorIdeal, eRid] using map_tensorIdeal_eq_localizedIdeal (S := S) m
  let eRidCot : tensorIdeal.Cotangent ≃ₗ[T] (m.map (algebraMap S T)).Cotangent :=
    (cotangentEquivMapAlgEquiv eRid tensorIdeal).trans
      (Ideal.Cotangent.equivOfEq _ _ hTensorIdeal)
  have hMax : m.map (algebraMap S T) = IsLocalRing.maximalIdeal T := by
    simpa [T] using localizedIdeal_eq_maximalIdeal (S := S) m
  let eMaxCot : tensorIdeal.Cotangent ≃ₗ[T] IsLocalRing.CotangentSpace T :=
    eRidCot.trans (Ideal.Cotangent.equivOfEq _ _ hMax)
  let eCot : K ⊗[T] tensorIdeal.Cotangent ≃ₗ[K] K ⊗[T] IsLocalRing.CotangentSpace T :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) eMaxCot
  letI : IsScalarTower T K (IsLocalRing.CotangentSpace T) :=
    Module.IsTorsionBySet.isScalarTower
      (Ideal.isTorsionBySet_cotangent (R := T) (I := IsLocalRing.maximalIdeal T))
  haveI : Algebra.IsEpi T K :=
    Algebra.isEpi_of_surjective_algebraMap T K Ideal.Quotient.mk_surjective
  let eLid : K ⊗[T] IsLocalRing.CotangentSpace T ≃ₗ[K] IsLocalRing.CotangentSpace T :=
    TensorProduct.lid' T K (IsLocalRing.CotangentSpace T)
  -- The composed equivalence preserves finrank over the localized residue field.
  let e : K ⊗[S ⧸ m] m.Cotangent ≃ₗ[K] IsLocalRing.CotangentSpace T :=
    (((eQuot.trans eLocBase).trans eTensorCot).trans eCot).trans eLid
  exact e.finrank_eq

/-- Helper for Chap10 Lemma 10 140 2: localizing at a maximal ideal preserves the dimension of
the cotangent space at the corresponding closed point. -/
private theorem finrank_quotient_cotangent_eq_localization :
    Module.finrank (S ⧸ m) m.Cotangent =
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) := by
  -- Base-changing the closed-point cotangent from `S ⧸ m` to the localized residue field does
  -- not change finrank, and the previous helper identifies that base change with the local
  -- cotangent space.
  rw [← Module.finrank_baseChange
    (R := IsLocalRing.ResidueField (Localization.AtPrime m)) (S := S ⧸ m)
    (M' := m.Cotangent)]
  exact finrank_residueTensor_cotangent_eq_localization (S := S) m

-- Proof sketch: Lemma `10.140.1` identifies the Kähler-differential fiber
-- `κ(m) ⊗[S] Ω[S⁄k]` with the cotangent space `m / m²`, so clauses `(1)`, `(2)`, and `(3)` are
-- equivalent by the regular-local criterion comparing dimension with embedding dimension. If
-- `SmoothAtPrime k S ⟨m, inferInstance⟩` holds, then standard smoothness on a basic open
-- neighborhood gives a free Kähler module of rank equal to the local dimension, yielding
-- regularity of `S_m`. Conversely, if `S_m` is regular, cut out a local complete intersection
-- presentation near `m` and apply the Jacobian criterion to obtain `SmoothAtPrime k S
-- ⟨m, inferInstance⟩`.
/-- Chap10 Lemma 10 140 2: for an algebraically closed field `k`, a finite type `k`-algebra `S`,
and a maximal ideal `m ⊂ S`, the following are equivalent: the local ring `Sₘ`, formalized as
`Localization.AtPrime m`, is regular; the fiber of `Ω[S⁄k]` at `m` has dimension at most
`dim(Sₘ)` over `κ(m) = S ⧸ m`; the same fiber dimension equals `dim(Sₘ)`; and `S/k` is smooth at
`m`, formalized as `Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩`. -/
@[stacks 00TS]
theorem regularLocalRing_finrank_kaehlerFiber_le_eq_and_exists_smoothLocalization_tfae :
    List.TFAE
      ([ IsRegularLocalRing (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m)
      , Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩ ] : List Prop) := by
  letI : Algebra.FinitePresentation k S :=
    (show Algebra.FiniteType k S ↔ Algebra.FinitePresentation k S from
      Algebra.FinitePresentation.of_finiteType).mp inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hcore :
      List.TFAE
        ([ Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩
        , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
        , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :
          List Prop) :=
    smoothAtPrime_tfae_finrank_kaehlerFiber_le_eq m
  let q : PrimeSpectrum S := ⟨m, inferInstance⟩
  have hsmooth :
      Algebra.SmoothAtPrime k S q ↔ Algebra.IsSmoothAt k q.asIdeal :=
    Algebra.smoothAtPrime_iff_isSmoothAt k S q
  have hregular_of_smooth :
      Algebra.SmoothAtPrime k S q → IsRegularLocalRing (Localization.AtPrime m) := by
    intro h
    exact Algebra.isRegularLocalRing_of_isSmoothAt q.asIdeal (hsmooth.mp h)
  have hregular_le :
      IsRegularLocalRing (Localization.AtPrime m) →
        Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤
          ringKrullDim (Localization.AtPrime m) := by
    intro hreg
    -- Regularity identifies the local embedding dimension with the Krull dimension, and the
    -- closed-point cotangent comparison rewrites the Kähler fiber into that cotangent space.
    have hregEq :
        Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
          (IsLocalRing.CotangentSpace (Localization.AtPrime m)) =
            ringKrullDim (Localization.AtPrime m) :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace (R := Localization.AtPrime m)).mp hreg
    have hfiber :
        Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
          Module.finrank (S ⧸ m) m.Cotangent :=
      finrank_kaehlerFiber_eq_finrank_cotangent m
    have hcot := finrank_quotient_cotangent_eq_localization (S := S) m
    simpa [hfiber, hcot] using le_of_eq hregEq
  -- Add the regular-local clause to the three-way smooth/fiber TFAE by the two directed links.
  tfae_have 1 → 2 := hregular_le
  tfae_have 4 → 1 := by
    simpa [q] using hregular_of_smooth
  tfae_have 4 ↔ 2 := hcore.out 0 1
  tfae_have 2 ↔ 3 := hcore.out 1 2
  tfae_finish

end
