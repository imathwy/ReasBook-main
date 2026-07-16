import stacks_proof.stacks_project.Chap10.Lemma_10_159_1.LocalAlgebra

universe u v w

open IsLocalRing
open CategoryTheory Limits
open scoped RatFunc

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Lemma 10.159.1: a partial stage of the source proof consists of a local flat
`R`-algebra whose residue field has already been identified with an intermediate field of `K`. -/
structure ResidueExtensionStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (L : IntermediateField (ResidueField R) K) where
  A : Type*
  commRing : CommRing A
  localRing : IsLocalRing A
  algebra : Algebra R A
  localHom : IsLocalHom (algebraMap R A)
  flat : (algebraMap R A).Flat
  map_maximalIdeal : Ideal.map (algebraMap R A) (maximalIdeal R) = maximalIdeal A
  residueEquiv : ResidueField A ≃+* L

attribute [instance] ResidueExtensionStage.commRing
attribute [instance] ResidueExtensionStage.localRing
attribute [instance] ResidueExtensionStage.algebra
attribute [instance] ResidueExtensionStage.localHom

namespace ResidueExtensionStage

variable {K : Type v} [Field K] [Algebra (ResidueField R) K]
variable {L M N : IntermediateField (ResidueField R) K}

/-- Helper for Lemma 10.159.1: the residue-field identification of a stage induces the canonical
map from the stage residue field into the ambient field `K`. -/
noncomputable def residueToAmbient
    (S : ResidueExtensionStage (R := R) K L) :
    ResidueField S.A →+* K :=
  L.val.toRingHom.comp S.residueEquiv.toRingHom

/-- Helper for Lemma 10.159.1: a stage already carries a canonical surjective ring map onto the
intermediate field it realizes. This is the stage-level quotient map needed for the later
direct-limit kernel argument. -/
noncomputable def toIntermediateFieldHom
    (S : ResidueExtensionStage (R := R) K L) :
    S.A →+* L :=
  S.residueEquiv.toRingHom.comp (algebraMap S.A (ResidueField S.A))

/-- Helper for Lemma 10.159.1: the stage map to its intermediate field is surjective because the
residue map is surjective and the chosen residue-field equivalence is bijective. -/
theorem toIntermediateFieldHom_surjective
    (S : ResidueExtensionStage (R := R) K L) :
    Function.Surjective S.toIntermediateFieldHom := by
  -- Lift an intermediate-field element to the stage residue field and then to the stage ring.
  intro x
  obtain ⟨y, rfl⟩ := S.residueEquiv.surjective x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨a, ?_⟩
  rfl

/-- Helper for Lemma 10.159.1: the canonical quotient map from a stage onto its intermediate
field kills exactly the maximal ideal. This is the residue-field kernel computation needed for the
later direct-limit local-ring argument. -/
theorem ker_toIntermediateFieldHom
    (S : ResidueExtensionStage (R := R) K L) :
    RingHom.ker S.toIntermediateFieldHom = maximalIdeal S.A := by
  -- Compare vanishing in `L` with vanishing in the stage residue field through the chosen
  -- residue-field equivalence.
  ext a
  change S.toIntermediateFieldHom a = 0 ↔ a ∈ maximalIdeal S.A
  change S.residueEquiv (residue S.A a) = 0 ↔ a ∈ maximalIdeal S.A
  rw [S.residueEquiv.map_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]

/-- Helper for Lemma 10.159.1: the ambient residue-field map of a stage factors through the
canonical quotient map onto the realized intermediate field. -/
noncomputable def toAmbientRingHom
    (S : ResidueExtensionStage (R := R) K L) :
    S.A →+* K :=
  S.residueToAmbient.comp (algebraMap S.A (ResidueField S.A))

/-- Helper for Lemma 10.159.1: the canonical residue-field map of a stage is injective because
it factors through the embedding of the intermediate field into `K`. -/
theorem residueToAmbient_injective
    (S : ResidueExtensionStage (R := R) K L) :
    Function.Injective S.residueToAmbient := by
  -- First recover equality in the intermediate field `L`, then use the stage residue-field
  -- equivalence.
  intro x y hxy
  have hL : S.residueEquiv x = S.residueEquiv y := Subtype.ext hxy
  exact S.residueEquiv.injective hL

/-- Helper for Lemma 10.159.1: the transcendental branch only differs by transporting the
coefficient field from the maximal-ideal residue field of `S.A` to the ordinary residue field of
`S.A`. This isolates the one `RatFunc` transport used in the source proof's successor step. -/
noncomputable def ratFunc_residueField_transport
    (S : ResidueExtensionStage (R := R) K L) :
    RatFunc ((maximalIdeal S.A).ResidueField) ≃+* RatFunc (ResidueField S.A) :=
  -- Transport the coefficient field first, then pass to the fraction field of the polynomial ring.
  IsFractionRing.ringEquivOfRingEquiv
    (Polynomial.mapEquiv (maximalIdealResidueFieldEquiv S.A))

/-- Helper for Lemma 10.159.1: the `RatFunc` transport from
`(maximalIdeal S.A).ResidueField` to `ResidueField S.A` sends constant polynomials to the
corresponding constant polynomials via the canonical residue-field equivalence. -/
theorem ratFunc_residueField_transport_C
    (S : ResidueExtensionStage (R := R) K L)
    (x : (maximalIdeal S.A).ResidueField) :
    S.ratFunc_residueField_transport
        (algebraMap (Polynomial ((maximalIdeal S.A).ResidueField))
          (RatFunc ((maximalIdeal S.A).ResidueField)) (Polynomial.C x)) =
      algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
        (Polynomial.C (maximalIdealResidueFieldEquiv S.A x)) := by
  -- Rewrite the constant rational function as an `algebraMap`, then apply the fraction-field
  -- transport compatibility for the coefficient-ring equivalence.
  simpa [ResidueExtensionStage.ratFunc_residueField_transport, Polynomial.mapEquiv] using
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (K := RatFunc ((maximalIdeal S.A).ResidueField))
      (L := RatFunc (ResidueField S.A))
      (h := Polynomial.mapEquiv (maximalIdealResidueFieldEquiv S.A))
      (a := Polynomial.C x))

/-- Helper for Lemma 10.159.1: if a transcendental element `α` generates `Lx` over the residue
field of a stage, then `Lx` is canonically the rational function field on `α`. This isolates the
field-theoretic part of the transcendental successor step. -/
noncomputable def ratFunc_algEquiv_of_transcendental_generator
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      RatFunc (ResidueField S.A) ≃ₐ[ResidueField S.A] Lx :=
  fun α hgen htrans ↦
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
      (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
    -- First identify `Lx` with the simple transcendental extension generated by `α`, then
    -- compose with the standard rational-function-field equivalence.
    (RatFunc.algEquivOfTranscendental α htrans).trans eTop

/-- Helper for Lemma 10.159.1: the transcendental generator equivalence sends a constant rational
function to the corresponding scalar in `Lx`. This is the constant-term computation needed when
comparing residue-field maps in the transcendental successor stage. -/
theorem ratFunc_algEquiv_of_transcendental_generator_C
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      ∀ x : ResidueField S.A,
      ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans
        (algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
          (Polynomial.C x)) =
        algebraMap (ResidueField S.A) Lx x := by
  intro α hgen htrans x
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  -- Evaluate the rational-function equivalence on constants before transporting along the
  -- generator identification `ResidueField S.A(α) = Lx`.
  calc
    ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans
        (algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
          (Polynomial.C x))
      =
        eTop
          (RatFunc.algEquivOfTranscendental α htrans
            (algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
              (Polynomial.C x))) := by
            simp [ratFunc_algEquiv_of_transcendental_generator, eTop]
    _ =
        eTop
          (Polynomial.aeval (IntermediateField.AdjoinSimple.gen (ResidueField S.A) α)
            (Polynomial.C x)) := by
          rw [RatFunc.algEquivOfTranscendental_algebraMap]
    _ = algebraMap (ResidueField S.A) Lx x := by
          simp [eTop]

/-- Helper for Lemma 10.159.1: after transporting coefficients from the maximal-ideal residue
field of `S.A` to the ordinary residue field of `S.A`, the transcendental generator equivalence
still sends constants to the expected scalars in `Lx`. -/
theorem ratFunc_transport_then_transcendental_generator_C
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      ∀ x : (maximalIdeal S.A).ResidueField,
      ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans
        (S.ratFunc_residueField_transport
          (algebraMap (Polynomial ((maximalIdeal S.A).ResidueField))
            (RatFunc ((maximalIdeal S.A).ResidueField)) (Polynomial.C x))) =
        algebraMap (ResidueField S.A) Lx (maximalIdealResidueFieldEquiv S.A x) := by
  intro α hgen htrans x
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Rewrite the transported constant in `RatFunc (ResidueField S.A)`, then invoke the constant
  -- computation for the transcendental generator equivalence.
  rw [ratFunc_residueField_transport_C]
  simpa using
    ratFunc_algEquiv_of_transcendental_generator_C (S := S) hLLx α hgen htrans
      (maximalIdealResidueFieldEquiv S.A x)

/-- Helper for Lemma 10.159.1: a morphism of stages is an `R`-algebra map compatible with the
chosen embeddings of the stage residue fields into `K`. -/
structure Hom (hLM : L ≤ M)
    (S : ResidueExtensionStage (R := R) K L)
    (T : ResidueExtensionStage (R := R) K M) where
  toAlgHom : S.A →ₐ[R] T.A
  isLocalHom : IsLocalHom toAlgHom.toRingHom
  residue_comm :
      T.residueToAmbient.comp (ResidueField.map toAlgHom.toRingHom) =
        S.residueToAmbient

attribute [instance] ResidueExtensionStage.Hom.isLocalHom

/-- Helper for Lemma 10.159.1: stage morphisms compose by composing the underlying algebra maps,
and the residue-field compatibility squares compose with them. -/
noncomputable def Hom.comp
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    {U : ResidueExtensionStage (R := R) K N}
    {hLM : L ≤ M} {hMN : M ≤ N}
    (f : Hom hLM S T) (g : Hom hMN T U) :
    Hom (hLM.trans hMN) S U where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  isLocalHom := by
    -- Composition of local ring maps is again a local ring map.
    simpa using
      (inferInstance :
        IsLocalHom ((g.toAlgHom.toRingHom).comp f.toAlgHom.toRingHom))
  residue_comm := by
    -- Evaluate the commutative squares on residue-field elements and compose the two
    -- compatibility identities already stored in `f` and `g`.
    ext x
    calc
      U.residueToAmbient
          (ResidueField.map (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom) x)
          =
        U.residueToAmbient
          (ResidueField.map g.toAlgHom.toRingHom
            (ResidueField.map f.toAlgHom.toRingHom x)) := by
              simpa using
                (IsLocalRing.ResidueField.map_map
                  f.toAlgHom.toRingHom g.toAlgHom.toRingHom x)
      _ =
        T.residueToAmbient
          (ResidueField.map f.toAlgHom.toRingHom x) := by
            simpa [RingHom.comp_apply] using
              congrArg (fun φ : ResidueField T.A →+* K ↦ φ (ResidueField.map f.toAlgHom.toRingHom x))
                g.residue_comm
      _ = S.residueToAmbient x := by
            simpa [RingHom.comp_apply] using
              congrArg (fun φ : ResidueField S.A →+* K ↦ φ x) f.residue_comm

/-- Helper for Lemma 10.159.1: every stage carries the identity morphism to itself, providing
the base case for later prefix-system transition maps. -/
noncomputable def Hom.id
    (S : ResidueExtensionStage (R := R) K L) :
    Hom (show L ≤ L by exact le_rfl) S S where
  toAlgHom := AlgHom.id R S.A
  isLocalHom := by
    -- The identity of a local ring is a local ring homomorphism.
    simpa using (inferInstance : IsLocalHom (RingHom.id S.A))
  residue_comm := by
    -- The residue-field comparison square is definitionally the identity square.
    ext x
    simp

/-- Helper for Lemma 10.159.1: a stage morphism already commutes with the chosen residue-field
equivalences before passing to the ambient field `K`. This is the intrinsic square needed for the
later direct-limit comparison on residue fields. -/
theorem Hom.residueEquiv_comm
    {hLM : L ≤ M}
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    (f : Hom hLM S T) :
    T.residueEquiv.toRingHom.comp (ResidueField.map f.toAlgHom.toRingHom) =
      (IntermediateField.inclusion hLM).toRingHom.comp S.residueEquiv.toRingHom := by
  -- Forget the subtype structure and compare the two maps after evaluating in the ambient field.
  ext x
  simpa [ResidueExtensionStage.residueToAmbient, RingHom.comp_apply] using
    congrArg (fun φ : ResidueField S.A →+* K ↦ φ x) f.residue_comm

/-- Helper for Lemma 10.159.1: stage morphisms commute with the canonical quotient maps onto the
realized intermediate fields. This is the ring-level compatibility needed to pass the stage maps
to the later direct limit. -/
theorem Hom.toIntermediateFieldHom_comm
    {hLM : L ≤ M}
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    (f : Hom hLM S T) :
    T.toIntermediateFieldHom.comp f.toAlgHom.toRingHom =
      (IntermediateField.inclusion hLM).toRingHom.comp S.toIntermediateFieldHom := by
  -- This is the intrinsic residue-field square for `f`, precomposed with the residue maps from
  -- the stage rings.
  ext a
  simpa [ResidueExtensionStage.toIntermediateFieldHom, RingHom.comp_apply,
    IsLocalRing.ResidueField.map_residue] using
    congrArg Subtype.val <|
      congrArg
        (fun φ : ResidueField S.A →+* M ↦ φ (residue S.A a))
        f.residueEquiv_comm

/-- Helper for Lemma 10.159.1: the trivial stage at the bottom intermediate field is the original
local ring `R` itself. This is the verified starting point of the transfinite construction. -/
noncomputable def base
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ResidueExtensionStage (R := R) K (⊥ : IntermediateField (ResidueField R) K) where
  A := R
  commRing := inferInstance
  localRing := inferInstance
  algebra := inferInstance
  localHom := by
    -- The identity map of a local ring is a local ring homomorphism.
    simpa using (inferInstance : IsLocalHom (RingHom.id R))
  flat := by
    -- The identity map is flat.
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  map_maximalIdeal := by
    -- The maximal ideal is unchanged under the identity algebra map.
    simp
  residueEquiv := by
    -- The residue field of the base stage is the bottom intermediate field.
    refine
      { toFun := fun x ↦
          ⟨algebraMap (ResidueField R) K x, by
            rw [IntermediateField.mem_bot]
            exact ⟨x, rfl⟩⟩
        invFun := fun x ↦ IntermediateField.botEquiv (ResidueField R) K x
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_
        map_add' := ?_ }
    · intro x
      exact IntermediateField.botEquiv_def (F := ResidueField R) (E := K) x
    · intro x
      change (IntermediateField.botEquiv (ResidueField R) K).symm
          (IntermediateField.botEquiv (ResidueField R) K x) = x
      exact (IntermediateField.botEquiv (ResidueField R) K).symm_apply_apply x
    · intro x y
      ext
      simp
    · intro x y
      ext
      simp

/-- Helper for Lemma 10.159.1: the ambient residue-field map of the base stage is the original
scalar map from `ResidueField R` into `K`. -/
theorem base_residueToAmbient_eq_algebraMap
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    (base (R := R) K).residueToAmbient = algebraMap (ResidueField R) K := by
  -- The base stage residue-field equivalence is the bottom-field embedding, so the induced ambient
  -- map is definitionally the original scalar map into `K`.
  ext x
  rfl

/-- Helper for Lemma 10.159.1: after transporting the stage residue-field algebra onto the
one-generator extension `L(x)`, the adjoined element still generates the whole field over the new
base residue field. This isolates the source proof's simple-extension input before the
transcendental/algebraic branch split. -/
theorem stage_adjoin_singleton_top
    (S : ResidueExtensionStage (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx :=
      (IntermediateField.inclusion
        (show L ≤ Lx by
          intro y hy
          change y ∈ IntermediateField.adjoin L ({x} : Set K)
          simpa using
            (IntermediateField.adjoin.algebraMap_mem (F := L) (S := ({x} : Set K))
              ⟨y, hy⟩))).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    ∃ α : Lx, IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤ := by
  let Lx : IntermediateField (ResidueField R) K :=
    (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx :=
    (IntermediateField.inclusion
      (show L ≤ Lx by
        intro y hy
        change y ∈ IntermediateField.adjoin L ({x} : Set K)
        simpa using
          (IntermediateField.adjoin.algebraMap_mem (F := L) (S := ({x} : Set K))
            ⟨y, hy⟩))
      ).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let α : Lx :=
    ⟨x, by
      change x ∈ IntermediateField.adjoin L ({x} : Set K)
      exact IntermediateField.mem_adjoin_of_mem (F := L) (S := ({x} : Set K)) (by simp)⟩
  refine ⟨α, ?_⟩
  let e : ResidueField S.A ≃ₐ[ResidueField S.A] L :=
    { toRingEquiv := S.residueEquiv
      commutes' := fun a ↦ rfl }
  have hL_top : IntermediateField.adjoin L ({α} : Set Lx) = ⊤ := by
    -- Every element of `Lx = L(x)` is a rational expression in the chosen generator `α`.
    apply eq_top_iff.mpr
    intro y hy
    exact
      IntermediateField.adjoin_induction (F := L) (s := ({x} : Set K))
        (p := fun z hz ↦
          (⟨z, by
            simpa [Lx] using hz⟩ : Lx) ∈ IntermediateField.adjoin L ({α} : Set Lx))
        (fun z hz ↦ by
          have hz' : z = x := by simpa using hz
          subst z
          simpa using
            (show α ∈ IntermediateField.adjoin L ({α} : Set Lx) from
              IntermediateField.mem_adjoin_of_mem (F := L) (S := ({α} : Set Lx)) (by simp)))
        (fun z ↦ by
          exact IntermediateField.algebraMap_mem (IntermediateField.adjoin L ({α} : Set Lx)) z)
        (fun z w hz hw hzmem hwmem ↦ by
          simpa using
            IntermediateField.add_mem (IntermediateField.adjoin L ({α} : Set Lx)) hzmem hwmem)
        (fun z hz hzmem ↦ by
          change ((⟨z, by simpa [Lx] using hz⟩ : Lx)⁻¹) ∈
              IntermediateField.adjoin L ({α} : Set Lx)
          exact IntermediateField.inv_mem (IntermediateField.adjoin L ({α} : Set Lx)) hzmem)
        (fun z w hz hw hzmem hwmem ↦ by
          simpa using
            IntermediateField.mul_mem (IntermediateField.adjoin L ({α} : Set Lx)) hzmem hwmem)
        y.2
  have htransport :
      IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) =
        (IntermediateField.adjoin L ({α} : Set Lx)).restrictScalars (ResidueField S.A) := by
    -- Transport the base field from `L` to `ResidueField S.A` through the stage residue-field
    -- identification, which was chosen as the scalar action on `L`.
    simpa using
      (IntermediateField.restrictScalars_adjoin_of_algEquiv
        (F := ResidueField S.A) (E := Lx) e rfl ({α} : Set Lx))
  rw [htransport, hL_top]
  simp

/-- Helper for Lemma 10.159.1: any local flat extension of a stage whose residue field is already
identified with a larger intermediate field packages into the next source-faithful stage. This
factors the common bookkeeping needed in both the transcendental and algebraic successor steps. -/
theorem of_local_extension
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [Algebra R B]
    [IsScalarTower R S.A B] [IsLocalHom (algebraMap S.A B)]
    (hflatB : (algebraMap S.A B).Flat)
    (hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B)
    (eB : ResidueField B ≃+* Lx)
    (hcompat :
      (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
        S.residueToAmbient) :
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx, Nonempty (Hom hLLx S T) := by
  let T : ResidueExtensionStage.{u, v, w} (R := R) K Lx :=
    { A := B
      commRing := inferInstance
      localRing := inferInstance
      algebra := inferInstance
      localHom := by
        -- The composite local map `R → S.A → B` is definitionally the ambient algebra map `R → B`.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using
          (inferInstance : IsLocalHom ((algebraMap S.A B).comp (algebraMap R S.A)))
      flat := by
        -- Flatness composes along the tower of local extensions.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using RingHom.Flat.comp S.flat hflatB
      map_maximalIdeal := by
        -- Push the maximal ideal through the old stage and then through the new local extension.
        calc
          Ideal.map (algebraMap R B) (maximalIdeal R)
              = Ideal.map ((algebraMap S.A B).comp (algebraMap R S.A)) (maximalIdeal R) := by
                  rw [IsScalarTower.algebraMap_eq R S.A B]
          _ = Ideal.map (algebraMap S.A B) (Ideal.map (algebraMap R S.A) (maximalIdeal R)) := by
                rw [Ideal.map_map]
          _ = Ideal.map (algebraMap S.A B) (maximalIdeal S.A) := by
                rw [S.map_maximalIdeal]
          _ = maximalIdeal B := hmapB
      residueEquiv := eB }
  refine ⟨T, ?_⟩
  refine ⟨{ toAlgHom := IsScalarTower.toAlgHom R S.A B, isLocalHom := ?_, residue_comm := ?_ }⟩
  · -- The canonical map in the tower is the given local ring map `S.A → B`.
    simpa using (inferInstance : IsLocalHom (algebraMap S.A B))
  -- The required residue-field square is exactly the compatibility hypothesis for the new stage.
  simpa [T, ResidueExtensionStage.residueToAmbient] using hcompat

/-- Helper for Lemma 10.159.1: package an explicit local extension on carrier `B` as the next
stage together with its canonical morphism from the previous stage. This keeps the successor-step
construction on the concrete ring `B` instead of asking elaboration to rediscover that carrier
through an existential witness. -/
theorem stage_and_hom_of_local_extension
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [Algebra R B]
    [IsScalarTower R S.A B] [IsLocalHom (algebraMap S.A B)]
    (hflatB : (algebraMap S.A B).Flat)
    (hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B)
    (eB : ResidueField B ≃+* Lx)
    (hcompat :
      (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
        S.residueToAmbient) :
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx,
      Nonempty (Hom hLLx S T) ∧ T.A = B := by
  let T : ResidueExtensionStage.{u, v, w} (R := R) K Lx :=
    { A := B
      commRing := inferInstance
      localRing := inferInstance
      algebra := inferInstance
      localHom := by
        -- The composite local map `R → S.A → B` is definitionally the ambient algebra map `R → B`.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using
          (inferInstance : IsLocalHom ((algebraMap S.A B).comp (algebraMap R S.A)))
      flat := by
        -- Flatness of the ambient map comes from composing the old stage with the new extension.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using RingHom.Flat.comp S.flat hflatB
      map_maximalIdeal := by
        -- Push the maximal ideal first through the old stage and then through the new local map.
        calc
          Ideal.map (algebraMap R B) (maximalIdeal R)
              = Ideal.map ((algebraMap S.A B).comp (algebraMap R S.A)) (maximalIdeal R) := by
                  rw [IsScalarTower.algebraMap_eq R S.A B]
          _ = Ideal.map (algebraMap S.A B) (Ideal.map (algebraMap R S.A) (maximalIdeal R)) := by
                rw [Ideal.map_map]
          _ = Ideal.map (algebraMap S.A B) (maximalIdeal S.A) := by
                rw [S.map_maximalIdeal]
          _ = maximalIdeal B := hmapB
      residueEquiv := eB }
  let f : Hom hLLx S T :=
    { toAlgHom := IsScalarTower.toAlgHom R S.A B
      isLocalHom := by
        -- The canonical map in the scalar tower is exactly the given local ring map `S.A → B`.
        simpa using (inferInstance : IsLocalHom (algebraMap S.A B))
      residue_comm := by
        -- The stored compatibility square already is the residue-field square required for `f`.
        simpa [T, ResidueExtensionStage.residueToAmbient] using hcompat }
  exact ⟨T, ⟨f⟩, rfl⟩

/-- Helper for Lemma 10.159.1: after transporting scalars along the residue-field identification
of a stage and then along an inclusion `L ≤ Lx`, the induced map into the ambient field `K` is
still the original residue-field comparison map of the stage. -/
theorem residueToAmbient_comp_algebraMap
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) = S.residueToAmbient := by
  -- Evaluate both maps on residue-field elements and unfold the chosen scalar tower.
  ext x
  rfl

/-- Helper for Lemma 10.159.1: evaluating the scalar-compatibility identity
`residueToAmbient_comp_algebraMap` on a residue-field element gives the pointwise formula used in
the transcendental successor branch. -/
theorem residueToAmbient_algebraMap_apply
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    ∀ x : ResidueField S.A,
      Lx.val.toRingHom (algebraMap (ResidueField S.A) Lx x) = S.residueToAmbient x := by
  intro x
  -- With the scalar tower fixed as above, both sides are definitionally the same map into `K`.
  rfl

/-- Helper for Lemma 10.159.1: the simple extension `L(x)` always contains the previous stage
field `L` after restricting scalars back to `ResidueField R`. This is the canonical inclusion
used in the source proof's successor step. -/
theorem le_restrictScalars_adjoin_singleton
    (L : IntermediateField (ResidueField R) K) (x : K) :
    L ≤ (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R) := by
  -- Elements already in `L` lie in the field generated by adjoining `x`.
  intro y hy
  change y ∈ IntermediateField.adjoin L ({x} : Set K)
  simpa using
    (IntermediateField.adjoin.algebraMap_mem (F := L) (S := ({x} : Set K)) ⟨y, hy⟩)

/-- Helper for Lemma 10.159.1: over a field, the negation of transcendence is exactly
integrality. This is the field-theoretic dichotomy used when the source proof passes from a
simple extension to its transcendental/algebraic cases. -/
theorem isIntegral_of_not_transcendental
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {x : E} (h : ¬ Transcendental F x) :
    IsIntegral F x := by
  -- Over a field, algebraicity and integrality coincide.
  have halg : IsAlgebraic F x := by
    simpa [Transcendental] using h
  exact halg.isIntegral

/-- Helper for Lemma 10.159.1: the simple algebraic generator equivalence respects coefficients
from the base residue field after transporting along the top-field identification. -/
theorem adjoinRootEquivAdjoin_topEquiv_apply_algebraMap
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    [Algebra (ResidueField S.A) L]
    [Algebra L Lx]
    [Algebra (ResidueField S.A) Lx]
    [IsScalarTower (ResidueField S.A) L Lx]
    (α : Lx)
    (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (hint : IsIntegral (ResidueField S.A) α)
    (x : ResidueField S.A) :
    let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
      (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
    eTop
        ((IntermediateField.adjoinRootEquivAdjoin (ResidueField S.A) hint)
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α)) x)) =
      algebraMap (ResidueField S.A) Lx x := by
  let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  calc
    eTop
        ((IntermediateField.adjoinRootEquivAdjoin (ResidueField S.A) hint)
          (algebraMap (ResidueField S.A)
            (AdjoinRoot (minpoly (ResidueField S.A) α)) x))
      =
        eTop
          (algebraMap (ResidueField S.A)
            (IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx)) x) := by
          rw [AlgEquiv.commutes]
    _ = algebraMap (ResidueField S.A) Lx x := by
          simpa using eTop.commutes x

/-- Helper for Lemma 10.159.1: the algebraic `AdjoinRoot` model carries the same map into the
ambient field `K` as the previous stage, once its residue field is identified with the simple
extension generated by `α`. -/
theorem algebraic_local_extension_compat
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    [Algebra (ResidueField S.A) L]
    [Algebra L Lx]
    [Algebra (ResidueField S.A) Lx]
    [IsScalarTower (ResidueField S.A) L Lx]
    (hambient :
      Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) = S.residueToAmbient)
    (α : Lx)
    (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (hint : IsIntegral (ResidueField S.A) α)
    (P : Polynomial (ResidueField S.A))
    (hP : P = minpoly (ResidueField S.A) α)
    (hPirred : Irreducible P)
    (f : Polynomial S.A)
    (hf : f.Monic)
    (hfmap : f.map (algebraMap S.A (ResidueField S.A)) = P) :
    letI : Fact (Irreducible P) := Fact.mk hPirred
    letI : IsLocalRing (AdjoinRoot f) :=
      adjoinRoot_isLocalRing_of_irreducible_reduction S.A f hf P hfmap
    letI : IsLocalHom (algebraMap S.A (AdjoinRoot f)) :=
      adjoinRoot_isLocalHom_of_irreducible_reduction S.A f P hfmap
    ∃ eB : ResidueField (AdjoinRoot f) ≃+* Lx,
      (Lx.val.toRingHom.comp eB.toRingHom).comp
          (ResidueField.map (algebraMap S.A (AdjoinRoot f))) =
        S.residueToAmbient := by
  -- Rewrite immediately to the canonical minimal polynomial so every later map sees the same
  -- simple algebraic extension.
  subst hP
  letI : Fact (Irreducible (minpoly (ResidueField S.A) α)) := Fact.mk hPirred
  letI : IsLocalRing (AdjoinRoot f) :=
    adjoinRoot_isLocalRing_of_irreducible_reduction
      S.A f hf (minpoly (ResidueField S.A) α) hfmap
  letI : IsLocalHom (algebraMap S.A (AdjoinRoot f)) :=
    adjoinRoot_isLocalHom_of_irreducible_reduction
      S.A f (minpoly (ResidueField S.A) α) hfmap
  let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  let eAdjoin :
      AdjoinRoot (minpoly (ResidueField S.A) α) ≃+* Lx :=
    ((IntermediateField.adjoinRootEquivAdjoin (ResidueField S.A) hint).trans eTop).toRingEquiv
  let eB : ResidueField (AdjoinRoot f) ≃+* Lx :=
    (adjoinRoot_residueField_equiv_of_irreducible_reduction
      S.A f (minpoly (ResidueField S.A) α) hfmap).trans eAdjoin
  refine ⟨eB, ?_⟩
  have hcoeff :
      (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α))) =
        S.residueToAmbient := by
    -- The algebraic generator identification sends coefficients to coefficients in `Lx`, and
    -- `hambient` identifies those with the old stage map into `K`.
    calc
      (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α)))
        = Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) := by
            ext x
            apply congrArg Subtype.val
            simpa [eAdjoin, eTop, RingHom.comp_apply] using
              (adjoinRootEquivAdjoin_topEquiv_apply_algebraMap
                (S := S) (Lx := Lx) α hgen hint x)
      _ = S.residueToAmbient := hambient
  have hres :
      (adjoinRoot_residueField_equiv_of_irreducible_reduction
          S.A f (minpoly (ResidueField S.A) α) hfmap).toRingHom.comp
          (ResidueField.map (algebraMap S.A (AdjoinRoot f))) =
        algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α)) := by
    -- The explicit `AdjoinRoot` residue-field equivalence already computes the coefficient map.
    simpa using
      (adjoinRoot_residueField_equiv_of_irreducible_reduction_comp_residueFieldMap
        S.A f (minpoly (ResidueField S.A) α) hfmap)
  -- Compose the coefficient computation for the explicit `AdjoinRoot` residue field with the
  -- simple-generator identification into `Lx`.
  calc
    (Lx.val.toRingHom.comp eB.toRingHom).comp
        (ResidueField.map (algebraMap S.A (AdjoinRoot f)))
      =
        (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          ((adjoinRoot_residueField_equiv_of_irreducible_reduction
            S.A f (minpoly (ResidueField S.A) α) hfmap).toRingHom.comp
            (ResidueField.map (algebraMap S.A (AdjoinRoot f)))) := by
              rfl
    _ =
        (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α))) := by
            rw [hres]
    _ = S.residueToAmbient := hcoeff

/-- Helper for Lemma 10.159.1: the canonical transcendental localization over a stage `S`
identifies its residue field with the simple transcendental extension generated by `α`, and this
identification preserves the ambient residue-field map into `K`. -/
theorem transcendental_local_extension_compat_canonical
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (α : Lx)
    (hgen :
      letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
      letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
      letI : Algebra (ResidueField S.A) Lx :=
        RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
      letI : IsScalarTower (ResidueField S.A) L Lx :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (htrans :
      letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
      letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
      letI : Algebra (ResidueField S.A) Lx :=
        RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
      letI : IsScalarTower (ResidueField S.A) L Lx :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      Transcendental (ResidueField S.A) α) :
    let J : Ideal (Polynomial S.A) := Ideal.map (Polynomial.C) (maximalIdeal S.A)
    let B : Type _ := Localization.AtPrime J
    ∃ eB : ResidueField B ≃+* Lx,
      ∀ a : S.A,
        Lx.val.toRingHom (eB (residue B (algebraMap S.A B a))) =
          S.residueToAmbient (residue S.A a) := by
  let J : Ideal (Polynomial S.A) := Ideal.map (Polynomial.C) (maximalIdeal S.A)
  let B : Type _ := Localization.AtPrime J
  letI : CommRing B := inferInstance
  letI : IsLocalRing B := inferInstance
  letI : Algebra S.A B := inferInstance
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eRat : RatFunc (ResidueField S.A) ≃+* Lx :=
    (ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans).toRingEquiv
  let eB : ResidueField B ≃+* Lx :=
    (localization_residueField_equiv S.A).trans (S.ratFunc_residueField_transport.trans eRat)
  refine ⟨eB, ?_⟩
  intro a
  -- Route correction: rewrite the canonical localization residue class through the residue-field
  -- model and only then evaluate the transported constant in `K`.
  calc
    Lx.val.toRingHom (eB (residue B (algebraMap S.A B a)))
        =
      Lx.val.toRingHom
        (eRat
          (S.ratFunc_residueField_transport
            (localization_residueField_equiv S.A
              (residue B (algebraMap S.A B a))))) := by
              rfl
    _ =
      Lx.val.toRingHom
        (eRat
          (S.ratFunc_residueField_transport
            (algebraMap (Polynomial ((maximalIdeal S.A).ResidueField))
              (RatFunc ((maximalIdeal S.A).ResidueField))
              (Polynomial.C (algebraMap S.A (maximalIdeal S.A).ResidueField a))))) := by
                rw [localization_residueField_equiv_apply_residue]
    _ =
      Lx.val.toRingHom
        (eRat
          (algebraMap (Polynomial (ResidueField S.A))
            (RatFunc (ResidueField S.A))
            (Polynomial.C
              (maximalIdealResidueFieldEquiv S.A
                (algebraMap S.A (maximalIdeal S.A).ResidueField a))))) := by
                  rw [ratFunc_residueField_transport_C]
    _ =
      Lx.val.toRingHom
        (algebraMap (ResidueField S.A) Lx
          (maximalIdealResidueFieldEquiv S.A
            (algebraMap S.A (maximalIdeal S.A).ResidueField a))) := by
              simpa [eRat] using
                congrArg Lx.val.toRingHom
                  (ratFunc_algEquiv_of_transcendental_generator_C
                    (S := S) hLLx α hgen htrans
                    (maximalIdealResidueFieldEquiv S.A
                      (algebraMap S.A (maximalIdeal S.A).ResidueField a)))
    _ =
      Lx.val.toRingHom (algebraMap (ResidueField S.A) Lx (residue S.A a)) := by
          rw [maximalIdealResidueFieldEquiv_apply_algebraMap]
    _ = S.residueToAmbient (residue S.A a) := by
          -- Finish by the pointwise scalar-compatibility formula just proved above.
          simpa using
            residueToAmbient_algebraMap_apply (S := S) (Lx := Lx) hLLx (residue S.A a)

/-- Helper for Lemma 10.159.1: a pointwise residue-class computation for a local extension over
`S.A` upgrades to the full residue-field square needed to package the next stage. -/
theorem transcendental_residue_class_bridge
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [IsLocalHom (algebraMap S.A B)]
    (eB : ResidueField B ≃+* Lx)
    (hclass :
      ∀ a : S.A,
        Lx.val.toRingHom (eB (residue B (algebraMap S.A B a))) =
          S.residueToAmbient (residue S.A a)) :
    (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
      S.residueToAmbient := by
  ext x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  -- Reduce the ring-hom equality to residue classes of elements of `S.A`.
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
  exact hclass a

/-- Helper for Lemma 10.159.1: adjoining one element `x : K` to the intermediate field realized
by a stage `S` produces the next source-faithful stage together with its canonical morphism from
`S`. This packages the algebraic/transcendental successor split from the source proof. -/
theorem extend_stage_by_element
    (S : ResidueExtensionStage.{u, v, w} (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx,
      Nonempty (Hom (le_restrictScalars_adjoin_singleton (R := R) L x) S T) := by
  let Lx : IntermediateField (ResidueField R) K :=
    (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
  let hLLx : L ≤ Lx := le_restrictScalars_adjoin_singleton (R := R) L x
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨α, hgen⟩ := stage_adjoin_singleton_top (S := S) x
  by_cases htrans : Transcendental (ResidueField S.A) α
  · let J : Ideal (Polynomial S.A) := Ideal.map (Polynomial.C) (maximalIdeal S.A)
    let B : Type w := Localization.AtPrime J
    letI : CommRing B := inferInstance
    letI : IsLocalRing B := inferInstance
    letI : Algebra S.A B := inferInstance
    letI : Algebra R B := inferInstance
    letI : IsScalarTower R S.A B := inferInstance
    letI : IsLocalHom (algebraMap S.A B) := localization_isLocalHom S.A
    have hflatB : (algebraMap S.A B).Flat := by
      -- The transcendental successor ring is a localization, hence flat over the previous stage.
      rw [RingHom.flat_algebraMap_iff]
      infer_instance
    have hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B :=
      localization_map_maximalIdeal_eq_maximalIdeal S.A
    obtain ⟨eB, hclass⟩ :=
      transcendental_local_extension_compat_canonical
        (S := S) (Lx := Lx) hLLx α hgen htrans
    have hcompat :
        (Lx.val.toRingHom.comp eB.toRingHom).comp
            (ResidueField.map (algebraMap S.A B)) =
          S.residueToAmbient :=
      transcendental_residue_class_bridge (S := S) (B := B) eB hclass
    -- Package the canonical localization branch as the next stage over the simple extension `L(x)`.
    simpa [Lx] using
      of_local_extension (S := S) (Lx := Lx) hLLx B hflatB hmapB eB hcompat
  · have hint : IsIntegral (ResidueField S.A) α :=
      isIntegral_of_not_transcendental htrans
    let P : Polynomial (ResidueField S.A) := minpoly (ResidueField S.A) α
    have hPirred : Irreducible P := minpoly.irreducible hint
    obtain ⟨f, hf, hfmap⟩ :=
      exists_monic_lift_of_residueField S.A P (minpoly.monic hint)
    let B : Type w := AdjoinRoot f
    letI : CommRing B := inferInstance
    letI : Algebra S.A B := inferInstance
    letI : Algebra R B := inferInstance
    letI : IsScalarTower R S.A B := inferInstance
    letI : Fact (Irreducible P) := Fact.mk hPirred
    letI : IsLocalRing B :=
      adjoinRoot_isLocalRing_of_irreducible_reduction S.A f hf P hfmap
    letI : IsLocalHom (algebraMap S.A B) :=
      adjoinRoot_isLocalHom_of_irreducible_reduction S.A f P hfmap
    letI : Module.Free S.A B := hf.free_adjoinRoot
    have hflatB : (algebraMap S.A B).Flat := by
      -- A monic `AdjoinRoot` algebra is free over the coefficient ring, hence flat.
      rw [RingHom.flat_algebraMap_iff]
      infer_instance
    have hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B :=
      adjoinRoot_map_maximalIdeal_eq_maximalIdeal_of_irreducible_reduction S.A f P hfmap
    have hambient :
        Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) =
          S.residueToAmbient :=
      residueToAmbient_comp_algebraMap (S := S) (Lx := Lx) hLLx
    obtain ⟨eB, hcompat⟩ :=
      algebraic_local_extension_compat
        (S := S) (Lx := Lx) hambient α hgen hint P rfl hPirred f hf hfmap
    -- Package the `AdjoinRoot` branch as the next stage over the same simple extension `L(x)`.
    simpa [Lx] using
      of_local_extension (S := S) (Lx := Lx) hLLx B hflatB hmapB eB hcompat

/-- Helper for Lemma 10.159.1: on a top stage, the ambient residue-field map is just the chosen
residue-field equivalence followed by the canonical identification with `K`. -/
theorem top_residueToAmbient_eq
    (T : ResidueExtensionStage (R := R) K (⊤ : IntermediateField (ResidueField R) K)) :
    T.residueToAmbient =
      IntermediateField.topEquiv.toRingHom.comp T.residueEquiv.toRingHom := by
  -- Unfolding the definition shows that the inclusion of the top intermediate field is the
  -- canonical equivalence to `K`.
  ext x
  rfl

end ResidueExtensionStage

end
