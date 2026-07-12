import StacksProject_2024.Chap10.Lemma_10_42_4.FrobeniusBaseChange
import StacksProject_2024.Chap10.Lemma_10_42_4.SeparableClosureDegreeDrop
import StacksProject_2024.Chap10.Lemma_10_42_4.TranscendenceBasisStage

section

open Algebra

universe u v

/-- Helper for Chap10 Lemma 10 42 4: an embedded copy of a purely inseparable finite
coefficient field is again purely inseparable over the original base. -/
lemma isPurelyInseparable_fieldRange_of_isPurelyInseparable
    {F : Type*} {B : Type*} {Ω : Type*}
    [Field F] [Field B] [Field Ω] [Algebra F B] [Algebra F Ω]
    [IsPurelyInseparable F B] (σ : B →ₐ[F] Ω) :
    IsPurelyInseparable F σ.fieldRange := by
  -- Transport pure inseparability across the canonical algebra equivalence with the field range.
  let e : B ≃ₐ[F] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  exact e.isPurelyInseparable

/-- Helper for Chap10 Lemma 10 42 4: in an algebraically closed characteristic-`p` ambient field,
each old transcendence-basis coordinate admits a chosen `p`th root. -/
lemma exists_pthRoots_algebraMap_of_isAlgClosed
    {F : Type*} {E : Type*} {Ω : Type*}
    [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω] [IsAlgClosed Ω]
    {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ} (x : Fin r → E) :
    ∃ y : Fin r → Ω, ∀ i, y i ^ p = algebraMap E Ω (x i) := by
  letI : CharP Ω p := charP_of_injective_algebraMap (algebraMap F Ω).injective p
  choose y hy using fun i : Fin r ↦
    surjective_frobenius Ω p (algebraMap E Ω (x i))
  refine ⟨y, ?_⟩
  intro i
  -- The chosen preimage under Frobenius is precisely a `p`th root of the old coordinate.
  simpa [frobenius_def] using hy i

/-- Helper for Chap10 Lemma 10 42 4: the finite purely inseparable coefficient field embeds into
an algebraic closure of the old top field, where all old coordinates admit `p`th roots. -/
lemma exists_embedded_pthRootStageData
    {F : Type u} {B : Type u} {E : Type v}
    [Field F] [Field B] [Field E] [Algebra F E] [Algebra F B]
    [FiniteDimensional F B] [IsPurelyInseparable F B]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {r : ℕ} (x : Fin r → E) :
    ∃ (Ω : Type v) (_ : Field Ω) (_ : Algebra F Ω) (_ : Algebra E Ω)
      (_ : IsScalarTower F E Ω) (_ : Algebra.IsAlgebraic E Ω)
      (σ : B →ₐ[F] Ω) (y : Fin r → Ω),
        FiniteDimensional F σ.fieldRange ∧ IsPurelyInseparable F σ.fieldRange ∧
          (∀ i, y i ^ p = algebraMap E Ω (x i)) := by
  let Ω := AlgebraicClosure E
  letI : Algebra F Ω := inferInstance
  letI : IsScalarTower F E Ω := inferInstance
  letI : Algebra.IsAlgebraic F B := Algebra.IsAlgebraic.of_finite F B
  let σ : B →ₐ[F] Ω := IsAlgClosed.lift (R := F) (S := B) (M := Ω)
  obtain ⟨y, hy⟩ :=
    exists_pthRoots_algebraMap_of_isAlgClosed
      (F := F) (E := E) (Ω := Ω) (p := p) x
  refine
    ⟨Ω, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, σ, y, ?_, ?_,
      hy⟩
  · -- Finite dimensionality is transported across the field-range equivalence of the embedding.
    exact finiteDimensional_fieldRange_of_finiteDimensional (F := F) (E := B) (L := Ω) σ
  · -- Pure inseparability is transported across the same field-range equivalence.
    exact isPurelyInseparable_fieldRange_of_isPurelyInseparable σ

/-- Helper for Chap10 Lemma 10 42 4: an element generated over `F` by a set `t` maps into the
field generated over the larger field `E` by the image of `t`. -/
lemma algHom_mem_adjoin_image_over_tower
    {F : Type u} {E : Type v} {B : Type u} {Ω : Type v}
    [Field F] [Field E] [Field B] [Field Ω]
    [Algebra F E] [Algebra F B] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω]
    (σ : B →ₐ[F] Ω) {t : Set B} {b : B}
    (hb : b ∈ IntermediateField.adjoin F t) :
    σ b ∈ IntermediateField.adjoin E (σ '' t : Set Ω) := by
  have hbase :
      IntermediateField.adjoin F (σ '' t : Set Ω) ≤
        (IntermediateField.adjoin E (σ '' t : Set Ω)).restrictScalars F := by
    -- The `E`-adjoin contains the same image generators, hence also their `F`-adjoin.
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin (F := E) (S := (σ '' t : Set Ω)) hz
  have hσbF : σ b ∈ IntermediateField.adjoin F (σ '' t : Set Ω) := by
    -- Mapping the old generated field computes as adjoining the image generators.
    have hmem_map : σ b ∈ (IntermediateField.adjoin F t).map σ := ⟨b, hb, rfl⟩
    rwa [IntermediateField.adjoin_map] at hmem_map
  exact hbase hσbF

/-- Helper for Chap10 Lemma 10 42 4: if a finite set generates `B / F`, then its image over
`E` contains the entire embedded coefficient field. -/
lemma fieldRange_subset_adjoin_image_of_adjoin_eq_top
    {F : Type u} {E : Type v} {B : Type u} {Ω : Type v}
    [Field F] [Field E] [Field B] [Field Ω]
    [Algebra F E] [Algebra F B] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω]
    (σ : B →ₐ[F] Ω) {t : Set B}
    (ht : IntermediateField.adjoin F t = ⊤) :
    (σ.fieldRange : Set Ω) ⊆ IntermediateField.adjoin E (σ '' t : Set Ω) := by
  intro z hz
  rcases hz with ⟨b, _hb, rfl⟩
  -- Reduce membership of an arbitrary embedded coefficient to the image-adjoin lemma.
  exact
    algHom_mem_adjoin_image_over_tower
      (F := F) (E := E) (B := B) (Ω := Ω) σ (t := t) (b := b)
      (by rw [ht]; trivial)

/-- Helper for Chap10 Lemma 10 42 4: adjoining an embedded finite purely inseparable coefficient
set together with chosen `p`th roots gives a purely inseparable extension of the old top field. -/
lemma isPurelyInseparable_adjoin_image_union_pthRoots
    {F : Type u} {B : Type u} {E : Type v} {Ω : Type v}
    [Field F] [Field B] [Field E] [Field Ω]
    [Algebra F B] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω]
    [IsPurelyInseparable F B]
    {p : ℕ} [Fact p.Prime] [CharP F p] [CharP E p]
    {r : ℕ} {x : Fin r → E} {y : Fin r → Ω}
    (σ : B →ₐ[F] Ω) (t : Set B) (hy : ∀ i, y i ^ p = algebraMap E Ω (x i)) :
    IsPurelyInseparable E
      (IntermediateField.adjoin E (σ '' t ∪ Set.range y : Set Ω)) := by
  rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem (F := E) (E := Ω) p]
  intro z hz
  rcases hz with hz | hz
  · rcases hz with ⟨b, _hb, rfl⟩
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F p b
    refine ⟨n, ⟨algebraMap F E a, ?_⟩⟩
    -- The embedded coefficient has a high `p`-power in the image of `E`.
    exact (calc
      σ b ^ p ^ n = σ (b ^ p ^ n) := by simp [map_pow]
      _ = σ (algebraMap F B a) := by rw [← ha]
      _ = algebraMap F Ω a := σ.commutes a
      _ = algebraMap E Ω (algebraMap F E a) := by
            rw [IsScalarTower.algebraMap_apply F E Ω]).symm
  · rcases hz with ⟨i, rfl⟩
    refine ⟨1, ⟨x i, ?_⟩⟩
    -- The chosen coordinate root has `p`th power equal to the old coordinate in `E`.
    have hyi : y i ^ p = algebraMap E Ω (x i) := hy i
    simpa using hyi.symm

/-- Helper for Chap10 Lemma 10 42 4: the embedded coefficients and chosen coordinate roots are
contained in one finite purely inseparable intermediate field over the old top field. -/
lemma exists_finite_purelyInseparable_adjoin_containing_fieldRange_and_pthRoots
    {F : Type u} {E : Type v} {B : Type u} {Ω : Type v}
    [Field F] [Field E] [Field B] [Field Ω]
    [Algebra F E] [Algebra F B] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω] [Algebra.IsAlgebraic E Ω]
    [FiniteDimensional F B] [IsPurelyInseparable F B]
    {p : ℕ} [Fact p.Prime] [CharP F p] [CharP E p]
    {r : ℕ} {x : Fin r → E} {y : Fin r → Ω}
    (σ : B →ₐ[F] Ω) (hy : ∀ i, y i ^ p = algebraMap E Ω (x i)) :
    ∃ S : Set Ω,
      S.Finite ∧
        S ⊆ (σ.fieldRange : Set Ω) ∪ Set.range y ∧
          (σ.fieldRange : Set Ω) ⊆ IntermediateField.adjoin E S ∧
            Set.range y ⊆ IntermediateField.adjoin E S ∧
              FiniteDimensional E (IntermediateField.adjoin E S) ∧
                IsPurelyInseparable E (IntermediateField.adjoin E S) := by
  obtain ⟨t, ht⟩ := IntermediateField.fg_top F B
  let S : Set Ω := σ '' (t : Set B) ∪ Set.range y
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A finite generating set for `B / F` plus finitely many roots gives a finite set in `Ω`.
    exact (t.finite_toSet.image σ).union (Set.finite_range y)
  · -- The chosen generators have no hidden elements: they are coefficients or coordinate roots.
    intro z hz
    rcases hz with hz | hz
    · rcases hz with ⟨b, _hb, rfl⟩
      exact Or.inl (show σ b ∈ σ.fieldRange from ⟨b, rfl⟩)
    · exact Or.inr hz
  · intro z hz
    have hz' : z ∈ IntermediateField.adjoin E (σ '' (t : Set B) : Set Ω) :=
      fieldRange_subset_adjoin_image_of_adjoin_eq_top
        (F := F) (E := E) (B := B) (Ω := Ω) σ (t := (t : Set B)) ht hz
    exact
      IntermediateField.adjoin.mono (F := E) (σ '' (t : Set B) : Set Ω) S
        (by intro z hz; exact Or.inl hz) hz'
  · intro z hz
    exact IntermediateField.subset_adjoin (F := E) (S := S) (Or.inr hz)
  · -- The selected generators are finite and algebraic over `E` inside the algebraic closure.
    exact
      IntermediateField.finiteDimensional_adjoin fun z _hz ↦
        (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  · -- Pure inseparability follows from the coefficient and coordinate root equations.
    exact
      isPurelyInseparable_adjoin_image_union_pthRoots
        (F := F) (B := B) (E := E) (Ω := Ω) (p := p) σ (t : Set B) hy

/-- Helper for Chap10 Lemma 10 42 4: the subtype cut out by an adjoin's generating set
generates that adjoined intermediate field over the old base. -/
lemma adjoin_preimage_generators_eq_top
    {E : Type v} {Ω : Type v} [Field E] [Field Ω] [Algebra E Ω] (S : Set Ω) :
    IntermediateField.adjoin E
        ({z : IntermediateField.adjoin E S | (z : Ω) ∈ S} :
          Set (IntermediateField.adjoin E S)) = ⊤ := by
  let L : IntermediateField E Ω := IntermediateField.adjoin E S
  let S_L : Set L := {z : L | (z : Ω) ∈ S}
  let U : IntermediateField E L := IntermediateField.adjoin E S_L
  refine eq_top_iff.2 ?_
  intro z _hz
  have hzΩ : (z : Ω) ∈ L := z.2
  -- Induct through the original adjoin in `Ω`; each generator becomes one of the subtype
  -- generators of `L`, and the field operations are preserved in the intermediate field `U`.
  have hmem :
      ∀ (w : Ω) (hw : w ∈ L), (⟨w, hw⟩ : L) ∈ U := by
    intro w hw
    refine IntermediateField.adjoin_induction (F := E) (E := Ω) (s := S)
      (p := fun a _ => ∀ haL : a ∈ L, (⟨a, haL⟩ : L) ∈ U) ?mem ?alg ?add ?inv ?mul hw hw
    · intro a haS haL
      exact IntermediateField.subset_adjoin (F := E) (S := S_L) haS
    · intro a haL
      simpa using U.algebraMap_mem a
    · intro a b haL hbL ha hb habL
      exact U.add_mem (ha haL) (hb hbL)
    · intro a haL ha hinvL
      exact U.inv_mem (ha haL)
    · intro a b haL hbL ha hb hmulL
      exact U.mul_mem (ha haL) (hb hbL)
  simpa [L, S_L, U] using hmem (z : Ω) hzΩ

/-- Helper for Chap10 Lemma 10 42 4: if an intermediate field contains the image of a
coefficient embedding `σ : B →ₐ[F] Ω`, then it inherits a compatible `B`-algebra structure. -/
lemma exists_algebra_of_fieldRange_subset_intermediateField
    {F : Type u} {B : Type u} {E : Type v} {Ω : Type v}
    [Field F] [Field B] [Field E] [Field Ω]
    [Algebra F B] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω]
    (σ : B →ₐ[F] Ω) (L : IntermediateField E Ω)
    (hσL : (σ.fieldRange : Set Ω) ⊆ L) :
    ∃ (_ : Algebra B L), IsScalarTower F B L ∧
      ∀ b : B, ((algebraMap B L b : L) : Ω) = σ b := by
  have hσ_mem : ∀ b : B, σ b ∈ L := by
    intro b
    -- Membership in `L` follows by viewing each embedded coefficient as an element of
    -- `σ.fieldRange`.
    exact hσL (show σ b ∈ σ.fieldRange from ⟨b, rfl⟩)
  let τ : B →+* L := σ.toRingHom.codRestrict L hσ_mem
  letI : Algebra B L := τ.toAlgebra
  have htower : IsScalarTower F B L := by
    -- The two `F`-algebra maps agree after coercion to the ambient field `Ω`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    change algebraMap F Ω a = σ (algebraMap F B a)
    rw [σ.commutes]
  have h_apply : ∀ b : B, ((algebraMap B L b : L) : Ω) = σ b := by
    intro b
    rfl
  exact ⟨inferInstance, htower, h_apply⟩

/-- Helper for Chap10 Lemma 10 42 4: if an intermediate field over `E` contains an intermediate
coefficient field over `F`, then the larger field inherits the coefficient algebra structure. -/
lemma exists_algebra_of_intermediateField_subset_intermediateField
    {F : Type u} {E : Type v} {Ω : Type v}
    [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω]
    (B₀ : IntermediateField F Ω) (L : IntermediateField E Ω)
    (hB₀L : (B₀ : Set Ω) ⊆ L) :
    ∃ (_ : Algebra B₀ L), IsScalarTower F B₀ L := by
  have hB₀_mem : ∀ b : B₀, (b : Ω) ∈ L := by
    intro b
    -- Membership is exactly the supplied containment, applied to the underlying element.
    exact hB₀L b.2
  let τ : B₀ →+* L := B₀.val.toRingHom.codRestrict L hB₀_mem
  letI : Algebra B₀ L := τ.toAlgebra
  have htower : IsScalarTower F B₀ L := by
    -- Both maps from `F` to `L` are the restrictions of the same map into `Ω`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    change algebraMap F Ω a = (algebraMap F Ω a)
    rfl
  exact ⟨inferInstance, htower⟩

/-- Helper for Chap10 Lemma 10 42 4: chosen ambient `p`th roots restrict to any intermediate
field that contains their range, preserving the `p`th-power equations over `E`. -/
lemma exists_pthRoots_in_intermediateField_of_range_subset
    {F : Type u} {E : Type v} {Ω : Type v}
    [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω]
    {p : ℕ} {r : ℕ} {x : Fin r → E} {yΩ : Fin r → Ω}
    (L : IntermediateField E Ω)
    (hyL : Set.range yΩ ⊆ L)
    (hyΩ : ∀ i, yΩ i ^ p = algebraMap E Ω (x i)) :
    ∃ y : Fin r → L,
      (∀ i, (y i : Ω) = yΩ i) ∧
        ∀ i, y i ^ p = algebraMap E L (x i) := by
  have hy_mem : ∀ i, yΩ i ∈ L := by
    intro i
    -- Each chosen root is in `L` because `L` contains the whole range of `yΩ`.
    exact hyL ⟨i, rfl⟩
  let y : Fin r → L := fun i ↦ ⟨yΩ i, hy_mem i⟩
  refine ⟨y, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    apply Subtype.ext
    -- Coercing to the ambient field reduces the restricted equation to the already chosen one.
    change yΩ i ^ p = algebraMap E Ω (x i)
    exact hyΩ i

/-- Helper for Chap10 Lemma 10 42 4: a finite top extension of an essentially finite type
stage remains essentially finite type after replacing the base by a compatible finite coefficient
field. -/
lemma essFiniteType_of_finiteDimensional_top_of_coeff_base
    {F : Type u} {B : Type*} {E : Type v} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F B] [Algebra F E] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    [Algebra.EssFiniteType F E] [FiniteDimensional E L] :
    Algebra.EssFiniteType B L := by
  -- First compose essential finite type along the finite top edge over `E`.
  have hFL : Algebra.EssFiniteType F L := by
    letI : Algebra.FiniteType E L := inferInstance
    exact Algebra.EssFiniteType.comp F E L
  -- Since `L` is already essentially finite type over `F`, it is so over any compatible
  -- intermediate coefficient base `B`.
  letI : Algebra.EssFiniteType F L := hFL
  exact Algebra.EssFiniteType.of_comp F B L

/-- Helper for Chap10 Lemma 10 42 4: evaluating a Frobenius-coefficient polynomial at `p`th
powers is the `p`th power of its original evaluation. -/
lemma aeval_map_frobenius_eq_aeval_pow
    {B : Type u} {L : Type v} [Field B] [Field L] [Algebra B L]
    {p : ℕ} [Fact p.Prime] [CharP B p]
    {ι : Type*} (P : MvPolynomial ι B) (y : ι → L) :
    MvPolynomial.aeval (fun i ↦ y i ^ p) (P.map (frobenius B p)) =
      (MvPolynomial.aeval y P) ^ p := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap B L).injective p
  have hfun : y ^ p = fun i : ι ↦ y i ^ p := by
    ext i
    rfl
  -- Normalize the coefficient Frobenius by moving through `expand`, whose variables evaluate to
  -- `p`th powers.
  calc
    MvPolynomial.aeval (fun i ↦ y i ^ p) (P.map (frobenius B p))
        = MvPolynomial.aeval y ((P.expand p).map (frobenius B p)) := by
            simp [hfun]
    _ = MvPolynomial.aeval y (P ^ p) := by
            rw [MvPolynomial.map_frobenius_expand]
    _ = (MvPolynomial.aeval y P) ^ p := by simp

/-- Helper for Chap10 Lemma 10 42 4: in characteristic `p`, pth roots of an algebraically
independent family are again algebraically independent. -/
lemma algebraicIndependent_of_pth_power_eq
    {B : Type u} {L : Type v} [Field B] [Field L] [Algebra B L]
    {p : ℕ} [Fact p.Prime] [CharP B p]
    {ι : Type*} {x y : ι → L}
    (hx : AlgebraicIndependent B x)
    (hy : ∀ i, y i ^ p = x i) :
    AlgebraicIndependent B y := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap B L).injective p
  rw [algebraicIndependent_iff]
  intro P hP
  have hmap_zero : P.map (frobenius B p) = 0 := by
    apply hx.eq_zero_of_aeval_eq_zero
    -- Raising the vanishing relation at `y` to the `p`th power gives a Frobenius-twisted
    -- polynomial relation at the known independent family `x`.
    calc
      MvPolynomial.aeval x (P.map (frobenius B p))
          = MvPolynomial.aeval (fun i ↦ y i ^ p) (P.map (frobenius B p)) := by
              congr 1
              ext i
              simp [hy i]
      _ = (MvPolynomial.aeval y P) ^ p := by
              exact aeval_map_frobenius_eq_aeval_pow (p := p) P y
      _ = 0 := by
              rw [hP]
              exact zero_pow (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hmap_zero' : P.map (frobenius B p) = (0 : MvPolynomial ι B).map (frobenius B p) := by
    simpa using hmap_zero
  -- Frobenius is injective on the coefficient field, so the original polynomial relation is zero.
  exact MvPolynomial.map_injective (f := frobenius B p) (frobenius B p).injective hmap_zero'

/-- Helper for Chap10 Lemma 10 42 4: a compatible pth-root lift of a transcendence basis across
algebraic base and top extensions is a transcendence basis over the new coefficient field. -/
lemma isTranscendenceBasis_of_pth_power_eq_algebraMap
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B] [Algebra.IsAlgebraic E L]
    {p : ℕ} [Fact p.Prime] [CharP B p]
    {ι : Type*} {x : ι → E} {y : ι → L}
    (hx : IsTranscendenceBasis F x)
    (hy : ∀ i, y i ^ p = algebraMap E L (x i)) :
    IsTranscendenceBasis B y := by
  let xL : ι → L := fun i ↦ algebraMap E L (x i)
  have hxF_L : IsTranscendenceBasis F xL := by
    -- Algebraic extension of the top field carries the original transcendence basis forward.
    simpa [xL, Function.comp_def] using
      (IsTranscendenceBasis.algebraMap_comp (A := L) hx)
  have hxB_L : IsTranscendenceBasis B xL := by
    -- Algebraic base change from `F` to `B` preserves the same lifted basis.
    exact
      (Algebra.IsAlgebraic.isTranscendenceBasis_iff
        (R := F) (S := B) (A := L) (x := xL)).mp hxF_L
  have hy_ind : AlgebraicIndependent B y :=
    algebraicIndependent_of_pth_power_eq (p := p) hxB_L.1 (x := xL) hy
  have hxy_le :
      IntermediateField.adjoin B (Set.range xL) ≤ IntermediateField.adjoin B (Set.range y) := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with ⟨i, rfl⟩
    have hyi : xL i = y i ^ p := (hy i).symm
    rw [hyi]
    exact pow_mem (IntermediateField.subset_adjoin (F := B) (S := Set.range y) ⟨i, rfl⟩) p
  have hy_alg_intermediate : Algebra.IsAlgebraic (IntermediateField.adjoin B (Set.range y)) L := by
    let F0 : IntermediateField B L := IntermediateField.adjoin B (Set.range xL)
    let F1 : IntermediateField B L := IntermediateField.adjoin B (Set.range y)
    have hF0F1 : F0 ≤ F1 := hxy_le
    letI : Algebra F0 F1 := (IntermediateField.inclusion hF0F1).toAlgebra
    letI : IsScalarTower F0 F1 L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hF0L : Algebra.IsAlgebraic F0 L := by
      simpa [F0, xL] using hxB_L.isAlgebraic_field
    -- Since `B(x)` is contained in `B(y)`, algebraicity over `B(x)` descends to the larger base.
    exact Algebra.IsAlgebraic.tower_top (K := F0) (A := L) F1
  have hy_alg : Algebra.IsAlgebraic (Algebra.adjoin B (Set.range y)) L :=
    (IntermediateField.isAlgebraic_adjoin_iff_top (F := B) (E := L)
      (S := L) (s := Set.range y)).mp hy_alg_intermediate
  exact hy_ind.isTranscendenceBasis_iff_isAlgebraic.mpr hy_alg

/-- Helper for Chap10 Lemma 10 42 4: the old transcendence-basis stage maps into the new
`p`th-root stage after the top-field base change. -/
lemma oldStage_map_le_pthRootStage
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {p : ℕ} {r : ℕ} {x : Fin r → E} {y : Fin r → L}
    (hy : ∀ i, y i ^ p = algebraMap E L (x i)) :
    ∀ z : IntermediateField.adjoin F (Set.range x),
      algebraMap E L (z : E) ∈ IntermediateField.adjoin B (Set.range y) := by
  let F1 : IntermediateField B L := IntermediateField.adjoin B (Set.range y)
  have hstage :
      IntermediateField.adjoin F ((IsScalarTower.toAlgHom F E L) '' Set.range x) ≤
        F1.restrictScalars F := by
    -- The new stage contains the image of every old generator because each is a `p`th power of a
    -- new generator; it also contains the base field through the scalar tower.
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with ⟨_, ⟨i, rfl⟩, rfl⟩
    have hyi_mem : y i ^ p ∈ F1 :=
      pow_mem (IntermediateField.subset_adjoin (F := B) (S := Set.range y) ⟨i, rfl⟩) p
    simpa [IsScalarTower.coe_toAlgHom', ← hy i] using hyi_mem
  intro z
  have hz_map :
      algebraMap E L (z : E) ∈
        (IntermediateField.adjoin F (Set.range x)).map
          (IsScalarTower.toAlgHom F E L) := by
    exact ⟨z, z.2, rfl⟩
  -- Mapping an adjoined field sends it to the field adjoined by the mapped generators, and that
  -- field is contained in the new `p`th-root stage by the previous paragraph.
  rw [IntermediateField.adjoin_map] at hz_map
  have hsets :
      (IsScalarTower.toAlgHom F E L) '' Set.range x =
        Set.range (fun i ↦ algebraMap E L (x i)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  exact hstage (by simpa [hsets] using hz_map)

/-- Helper for Chap10 Lemma 10 42 4: the old-to-new stage map is the codrestriction of the
top-field algebra map to `B(y)`. -/
lemma exists_oldStageToPthRootStageRingHom
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {p : ℕ} {r : ℕ} {x : Fin r → E} {y : Fin r → L}
    (hy : ∀ i, y i ^ p = algebraMap E L (x i)) :
    ∃ φ : IntermediateField.adjoin F (Set.range x) →+*
        IntermediateField.adjoin B (Set.range y),
      (IntermediateField.adjoin B (Set.range y)).val.toRingHom.comp φ =
        (algebraMap E L).comp (IntermediateField.adjoin F (Set.range x)).val.toRingHom := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  let F1 : IntermediateField B L := IntermediateField.adjoin B (Set.range y)
  have hmem : ∀ z : F0, algebraMap E L (z : E) ∈ F1 :=
    oldStage_map_le_pthRootStage
      (F := F) (B := B) (E := E) (L := L) (p := p) (r := r) (x := x) (y := y) hy
  let φ : F0 →+* F1 := ((algebraMap E L).comp F0.val.toRingHom).codRestrict F1 hmem
  refine ⟨φ, ?_⟩
  -- Both composites are the same map into `L`; codrestriction only records membership in `B(y)`.
  ext z
  rfl

/-- Helper for Chap10 Lemma 10 42 4: the old-to-new stage map sends each old coordinate to the
corresponding `p`th power in the new `p`th-root stage. -/
lemma oldStageToPthRootStageRingHom_apply_generator
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {p : ℕ} {r : ℕ} {x : Fin r → E} {y : Fin r → L}
    (hy : ∀ i, y i ^ p = algebraMap E L (x i))
    (φ : IntermediateField.adjoin F (Set.range x) →+*
        IntermediateField.adjoin B (Set.range y))
    (hφ : (IntermediateField.adjoin B (Set.range y)).val.toRingHom.comp φ =
        (algebraMap E L).comp (IntermediateField.adjoin F (Set.range x)).val.toRingHom)
    (i : Fin r) :
    (φ ⟨x i, IntermediateField.subset_adjoin (F := F) (S := Set.range x) ⟨i, rfl⟩⟩ : L) =
      y i ^ p := by
  -- Evaluate the composite identity on the old generator, then use the chosen root equation.
  have h := congrArg
    (fun ψ : IntermediateField.adjoin F (Set.range x) →+* L =>
      ψ ⟨x i, IntermediateField.subset_adjoin (F := F) (S := Set.range x) ⟨i, rfl⟩⟩) hφ
  simpa [RingHom.comp_apply, hy i] using h

/-- Helper for Chap10 Lemma 10 42 4: `reprField` sends an adjoined coordinate to the
corresponding rational-function variable. -/
lemma reprField_adjoin_generator
    {F : Type*} {E : Type*} {ι : Type*} [Field F] [Field E] [Algebra F E]
    {x : ι → E} (hx : AlgebraicIndependent F x) (i : ι) :
    hx.reprField ⟨x i, IntermediateField.subset_adjoin (F := F) (S := Set.range x) ⟨i, rfl⟩⟩ =
      algebraMap (MvPolynomial ι F) (FractionRing (MvPolynomial ι F)) (MvPolynomial.X i) := by
  -- Apply the inverse equivalence and compute the coordinate polynomial by evaluation.
  apply hx.aevalEquivField.injective
  apply Subtype.ext
  simpa [AlgebraicIndependent.reprField] using
    (AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe hx (MvPolynomial.X i)).symm

/-- Helper for Chap10 Lemma 10 42 4: after applying `aevalEquivField`, the rational-function
base-change map agrees with the old-to-new `p`th-root stage map on `F(x)`. -/
lemma oldStageToPthRootStage_aevalEquivField_comp_eq
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {p : ℕ} [Fact p.Prime] {r : ℕ} {x : Fin r → E} {y : Fin r → L}
    (hx : IsTranscendenceBasis F x) (hyBasis : IsTranscendenceBasis B y)
    (hy : ∀ i, y i ^ p = algebraMap E L (x i))
    (φ : IntermediateField.adjoin F (Set.range x) →+*
        IntermediateField.adjoin B (Set.range y))
    (hφ : (IntermediateField.adjoin B (Set.range y)).val.toRingHom.comp φ =
        (algebraMap E L).comp (IntermediateField.adjoin F (Set.range x)).val.toRingHom) :
    φ = hyBasis.1.aevalEquivField.toRingHom.comp
      ((ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)).comp
        hx.1.reprField.toRingHom) := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  let F1 : IntermediateField B L := IntermediateField.adjoin B (Set.range y)
  apply RingHom.ext
  intro z
  let ψ : F0 →+* F1 := hyBasis.1.aevalEquivField.toRingHom.comp
      ((ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)).comp
        hx.1.reprField.toRingHom)
  have hprop : ∀ (a : E) (ha : a ∈ F0), φ ⟨a, ha⟩ = ψ ⟨a, ha⟩ := by
    intro a ha
    -- The two maps out of the generated field agree on constants and on the coordinates, hence
    -- agree on the whole adjoin by the field-adjoin induction principle.
    refine IntermediateField.adjoin_induction (F := F) (E := E) (s := Set.range x)
      (p := fun a ha => φ ⟨a, ha⟩ = ψ ⟨a, ha⟩) ?mem ?alg ?add ?inv ?mul ha
    · intro a ha
      rcases ha with ⟨i, rfl⟩
      apply Subtype.ext
      have hφi := oldStageToPthRootStageRingHom_apply_generator
        (F := F) (B := B) (E := E) (L := L) (p := p) (r := r) (x := x) (y := y)
        hy φ hφ i
      have hreprX :
          hx.1.reprField.toRingHom
              ⟨x i, IntermediateField.subset_adjoin (F := F) (S := Set.range x) ⟨i, rfl⟩⟩ =
            algebraMap (MvPolynomial (Fin r) F) (FractionRing (MvPolynomial (Fin r) F))
              (MvPolynomial.X i) := by
        simpa using reprField_adjoin_generator hx.1 i
      have hratX :
          ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)
              (algebraMap (MvPolynomial (Fin r) F) (FractionRing (MvPolynomial (Fin r) F))
                (MvPolynomial.X i)) =
            algebraMap (MvPolynomial (Fin r) B) (FractionRing (MvPolynomial (Fin r) B))
              (MvPolynomial.X i ^ p) := by
        have h := congrArg
          (fun f : MvPolynomial (Fin r) F →+* FractionRing (MvPolynomial (Fin r) B) =>
            f (MvPolynomial.X i))
          (ratFunc_frobenius_baseChangeHom_comp_algebraMap
            (k := F) (k' := B) (r := r) (p := p))
        simpa [RingHom.comp_apply, MvPolynomial.expand_X] using h
      calc
        ((φ ⟨x i, IntermediateField.subset_adjoin (F := F) (S := Set.range x) ⟨i, rfl⟩⟩ :
              F1) : L)
            = y i ^ p := hφi
        _ = ((ψ ⟨x i, IntermediateField.subset_adjoin (F := F) (S := Set.range x) ⟨i, rfl⟩⟩ :
              F1) : L) := by
            unfold ψ
            rw [RingHom.comp_apply, RingHom.comp_apply, hreprX, hratX]
            simpa [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe,
              MvPolynomial.aeval_X, hy i]
    · intro c
      apply Subtype.ext
      have hcφ := congrArg (fun η : F0 →+* L => η (algebraMap F F0 c)) hφ
      have hreprC :
          hx.1.reprField.toRingHom (algebraMap F F0 c) =
            algebraMap F (FractionRing (MvPolynomial (Fin r) F)) c := by
        exact hx.1.reprField.commutes c
      have hratC :
          ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)
              (algebraMap F (FractionRing (MvPolynomial (Fin r) F)) c) =
            algebraMap B (FractionRing (MvPolynomial (Fin r) B)) (algebraMap F B c) := by
        have h := congrArg
          (fun f : MvPolynomial (Fin r) F →+* FractionRing (MvPolynomial (Fin r) B) =>
            f (MvPolynomial.C c))
          (ratFunc_frobenius_baseChangeHom_comp_algebraMap
            (k := F) (k' := B) (r := r) (p := p))
        simpa [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
          MvPolynomial.expand_C] using h
      calc
        ((φ (algebraMap F F0 c) : F1) : L)
            = algebraMap F L c := by
                simpa [RingHom.comp_apply, F0, IsScalarTower.algebraMap_apply F E L c] using hcφ
        _ = ((ψ (algebraMap F F0 c) : F1) : L) := by
            unfold ψ
            rw [RingHom.comp_apply, RingHom.comp_apply, hreprC, hratC]
            simpa using (IsScalarTower.algebraMap_apply F B L c)
    · intro a b ha hb hpa hpb
      have hadd : (⟨a + b, by exact add_mem ha hb⟩ : F0) = (⟨a, ha⟩ : F0) + ⟨b, hb⟩ :=
        Subtype.ext rfl
      rw [hadd, map_add, map_add, hpa, hpb]
    · intro a ha hpa
      have hinv : (⟨a⁻¹, by exact inv_mem ha⟩ : F0) = (⟨a, ha⟩ : F0)⁻¹ :=
        Subtype.ext rfl
      rw [hinv, map_inv₀, map_inv₀, hpa]
    · intro a b ha hb hpa hpb
      have hmul : (⟨a * b, by exact mul_mem ha hb⟩ : F0) = (⟨a, ha⟩ : F0) * ⟨b, hb⟩ :=
        Subtype.ext rfl
      rw [hmul, map_mul, map_mul, hpa, hpb]
  exact hprop z z.2

/-- Helper for Chap10 Lemma 10 42 4: the rational-function representation of the old-to-new
`p`th-root stage map is the source representation followed by Frobenius base change. -/
lemma oldStageToPthRootStage_reprField_comp_eq
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {p : ℕ} [Fact p.Prime] {r : ℕ} {x : Fin r → E} {y : Fin r → L}
    (hx : IsTranscendenceBasis F x) (hyBasis : IsTranscendenceBasis B y)
    (hy : ∀ i, y i ^ p = algebraMap E L (x i))
    (φ : IntermediateField.adjoin F (Set.range x) →+*
        IntermediateField.adjoin B (Set.range y))
    (hφ : (IntermediateField.adjoin B (Set.range y)).val.toRingHom.comp φ =
        (algebraMap E L).comp (IntermediateField.adjoin F (Set.range x)).val.toRingHom) :
    hyBasis.1.reprField.toRingHom.comp φ =
      (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)).comp
        hx.1.reprField.toRingHom := by
  have hafter := oldStageToPthRootStage_aevalEquivField_comp_eq
    (F := F) (B := B) (E := E) (L := L) (p := p) (r := r) (x := x) (y := y)
    hx hyBasis hy φ hφ
  apply RingHom.ext
  intro z
  -- Apply the rational-function equivalence over `B(y)`; the previous lemma computes the image.
  apply hyBasis.1.aevalEquivField.injective
  have hz := congrArg (fun f : IntermediateField.adjoin F (Set.range x) →+*
      IntermediateField.adjoin B (Set.range y) => f z) hafter
  calc
    hyBasis.1.aevalEquivField (hyBasis.1.reprField (φ z)) = φ z := by
      simp [AlgebraicIndependent.reprField]
    _ = hyBasis.1.aevalEquivField
        (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)
          (hx.1.reprField z)) := by
        simpa [RingHom.comp_apply] using hz

/-- Helper for Chap10 Lemma 10 42 4: mapping the old minimal polynomial through the `p`th-root
stage and then through `reprField` agrees with source rational-function Frobenius base change. -/
lemma oldStageToPthRootStage_minpoly_reprField_map_eq
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {p : ℕ} [Fact p.Prime] {r : ℕ} {x : Fin r → E} {y : Fin r → L}
    (hx : IsTranscendenceBasis F x) (hyBasis : IsTranscendenceBasis B y)
    (hy : ∀ i, y i ^ p = algebraMap E L (x i))
    (φ : IntermediateField.adjoin F (Set.range x) →+*
        IntermediateField.adjoin B (Set.range y))
    (hφ : (IntermediateField.adjoin B (Set.range y)).val.toRingHom.comp φ =
        (algebraMap E L).comp (IntermediateField.adjoin F (Set.range x)).val.toRingHom)
    (β : E) :
    (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map φ).map
        hyBasis.1.reprField.toRingHom) =
      (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
          hx.1.reprField.toRingHom).map
        (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p))) := by
  -- The ring-hom equality is lifted coefficientwise to the minimal polynomial.
  have hring := oldStageToPthRootStage_reprField_comp_eq
    (F := F) (B := B) (E := E) (L := L) (p := p) (r := r) (x := x) (y := y)
    hx hyBasis hy φ hφ
  rw [Polynomial.map_map, Polynomial.map_map, hring]

/-- Helper for Chap10 Lemma 10 42 4: Frobenius-range membership over the rational-function field
transports to the coefficient field `B(y)` of the restarted `p`th-root stage. -/
lemma minpoly_mem_frobenius_range_pthRootStage
    {F : Type u} {B : Type u} {E : Type v} {L : Type v}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {p : ℕ} [Fact p.Prime] [CharP B p] {r : ℕ} {x : Fin r → E} {y : Fin r → L}
    (hx : IsTranscendenceBasis F x) (hyBasis : IsTranscendenceBasis B y)
    (hy : ∀ i, y i ^ p = algebraMap E L (x i))
    (φ : IntermediateField.adjoin F (Set.range x) →+*
        IntermediateField.adjoin B (Set.range y))
    (hφ : (IntermediateField.adjoin B (Set.range y)).val.toRingHom.comp φ =
        (algebraMap E L).comp (IntermediateField.adjoin F (Set.range x)).val.toRingHom)
    {β : E}
    (hFrobRange :
      (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
          hx.1.aevalEquivField.symm.toRingHom).map
        (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p))) ∈
        Set.range
          (Polynomial.map
            (frobenius (FractionRing (MvPolynomial (Fin r) B)) p))) :
    ((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map φ) ∈
      Set.range
        (Polynomial.map
          (frobenius (IntermediateField.adjoin B (Set.range y)) p)) := by
  let F1 : IntermediateField B L := IntermediateField.adjoin B (Set.range y)
  letI : CharP F1 p := charP_of_injective_algebraMap (algebraMap B F1).injective p
  refine mem_frobenius_range_of_map_ringEquiv_symm
    (e := hyBasis.1.aevalEquivField.toRingEquiv) ?_
  have hpoly :
      (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map φ).map
          hyBasis.1.aevalEquivField.toRingEquiv.symm.toRingHom) =
        (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
            hx.1.aevalEquivField.symm.toRingHom).map
          (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p))) := by
    simpa [AlgebraicIndependent.reprField] using
      oldStageToPthRootStage_minpoly_reprField_map_eq
        (F := F) (B := B) (E := E) (L := L) (p := p) (r := r) (x := x) (y := y)
        hx hyBasis hy φ hφ β
  -- After the coefficient-map comparison, the normalized source Frobenius-range premise applies.
  rw [hpoly]
  exact hFrobRange

/-- Helper for Chap10 Lemma 10 42 4: a normalized Frobenius-range premise over the coefficient
extension is the remaining interface for constructing the restarted p-root absorption stage. -/
lemma exists_restarted_stage_absorbing_degree_p_step_of_frobenius_range
    {F : Type u} {B : Type u} {E : Type v}
    [Field F] [Field B] [Field E] [Algebra F E] [Algebra F B]
    [FiniteDimensional F B] [IsPurelyInseparable F B]
    {p : ℕ} [Fact p.Prime] [CharP F p] [CharP B p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    {β : E}
    (hβ_deg :
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p)
    (hβ_pow_mem : β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E)
    (hFrobRange :
      (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
          hx.1.aevalEquivField.symm.toRingHom).map
        (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p))) ∈
        Set.range
          (Polynomial.map
            (frobenius (FractionRing (MvPolynomial (Fin r) B)) p))) :
    ∃ (B' : Type u) (_ : Field B') (_ : Algebra F B')
      (_ : FiniteDimensional F B') (_ : IsPurelyInseparable F B')
      (L : Type v) (_ : Field L) (_ : Algebra F L) (_ : Algebra E L) (_ : Algebra B' L)
      (_ : IsScalarTower F E L) (_ : IsScalarTower F B' L)
      (_ : FiniteDimensional E L) (_ : IsPurelyInseparable E L)
      (_ : Algebra.EssFiniteType B' L)
      (y : Fin r → L),
          IsTranscendenceBasis B' y ∧
            Field.finInsepDegree (IntermediateField.adjoin B' (Set.range y)) L <
              Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
  -- Route correction: previous attempts kept rebuilding the coefficient-root witnesses at this
  -- stage.  The coefficient descent has already been compressed into `hFrobRange`; the remaining
  -- proof must build the p-root compositum stage, transport this Frobenius-range statement to its
  -- new transcendence-basis field, and apply an extension-aware degree drop.
  obtain ⟨Ω, hΩField, hFΩ, hEΩ, hFEΩ, hΩalg, σ, yΩ, hσfd, hσpi, hyΩ⟩ :=
    exists_embedded_pthRootStageData
      (F := F) (B := B) (E := E) (p := p) (r := r) x
  letI : Field Ω := hΩField
  letI : Algebra F Ω := hFΩ
  letI : Algebra E Ω := hEΩ
  letI : IsScalarTower F E Ω := hFEΩ
  letI : Algebra.IsAlgebraic E Ω := hΩalg
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap F E).injective p
  obtain ⟨S, hSfinite, hSsource, hσS, hyS, hSfd, hSpi⟩ :=
    exists_finite_purelyInseparable_adjoin_containing_fieldRange_and_pthRoots
      (F := F) (E := E) (B := B) (Ω := Ω) (p := p) (r := r) (x := x) σ hyΩ
  let L : IntermediateField E Ω := IntermediateField.adjoin E S
  obtain ⟨hBL, hFBL, hBL_apply⟩ :=
    exists_algebra_of_fieldRange_subset_intermediateField
      (F := F) (B := B) (E := E) (Ω := Ω) σ L hσS
  letI : Algebra B L := hBL
  letI : IsScalarTower F B L := hFBL
  obtain ⟨hRangeAlgL, hFRangeL⟩ :=
    exists_algebra_of_intermediateField_subset_intermediateField
      (F := F) (E := E) (Ω := Ω) σ.fieldRange L hσS
  letI : Algebra σ.fieldRange L := hRangeAlgL
  letI : IsScalarTower F σ.fieldRange L := hFRangeL
  obtain ⟨y, hy_val, hy⟩ :=
    exists_pthRoots_in_intermediateField_of_range_subset
      (F := F) (E := E) (Ω := Ω) (p := p) (r := r) (x := x) L hyS hyΩ
  letI : FiniteDimensional E L := by
    -- The top field is exactly the finite adjoin supplied by the generated-stage helper.
    simpa [L] using hSfd
  letI : IsPurelyInseparable E L := by
    -- Pure inseparability is inherited from the same finite adjoin.
    simpa [L] using hSpi
  letI : Algebra.EssFiniteType B L :=
    essFiniteType_of_finiteDimensional_top_of_coeff_base
      (F := F) (B := B) (E := E) (L := L)
  letI : Algebra.EssFiniteType σ.fieldRange L :=
    essFiniteType_of_finiteDimensional_top_of_coeff_base
      (F := F) (B := ↥σ.fieldRange) (E := E) (L := L)
  letI : FiniteDimensional F σ.fieldRange := hσfd
  letI : IsPurelyInseparable F σ.fieldRange := hσpi
  have hFL : Algebra.EssFiniteType F L := by
    -- The generated top field is finite over the old essentially finite type stage.
    letI : Algebra.FiniteType E L := inferInstance
    exact Algebra.EssFiniteType.comp F E L
  letI : Algebra.EssFiniteType F L := hFL
  letI : Algebra.IsAlgebraic F B := Algebra.IsAlgebraic.of_finite F B
  letI : Algebra.IsAlgebraic E L := Algebra.IsAlgebraic.of_finite E L
  have hyBasis : IsTranscendenceBasis B y :=
    isTranscendenceBasis_of_pth_power_eq_algebraMap
      (F := F) (B := B) (E := E) (L := L) (p := p) hx hy
  let F1 : IntermediateField B L := IntermediateField.adjoin B (Set.range y)
  let S_L : Set L := {z : L | (z : Ω) ∈ S}
  have hS_L_subset : S_L ⊆ F1 := by
    intro z hz
    rcases hSsource hz with hz_coeff | hz_root
    · rcases (RingHom.mem_fieldRange.mp hz_coeff) with ⟨b, hbz⟩
      have hz_eq : z = algebraMap B L b := by
        apply Subtype.val_injective
        rw [hBL_apply b]
        exact hbz.symm
      simpa [hz_eq] using F1.algebraMap_mem b
    · rcases hz_root with ⟨i, hzi⟩
      have hz_eq : z = y i := by
        exact Subtype.ext (by simpa [hy_val i] using hzi.symm)
      exact hz_eq.symm ▸
        IntermediateField.subset_adjoin (F := B) (S := Set.range y) ⟨i, rfl⟩
  have hL_generated_over_E : IntermediateField.adjoin E S_L = ⊤ := by
    -- The adjoin defining `L` is generated by the same elements after restricting them to `L`.
    simpa [L, S_L] using adjoin_preimage_generators_eq_top (E := E) (Ω := Ω) S
  have hGeneratedTop :
      IntermediateField.adjoin F1 (Set.range (algebraMap E L)) = ⊤ :=
    adjoin_range_eq_top_of_adjoin_eq_top_of_subset
      (B := B) (E := E) (L := L) F1 hS_L_subset hL_generated_over_E
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  obtain ⟨φ, hφ⟩ :=
    exists_oldStageToPthRootStageRingHom
      (F := F) (B := B) (E := E) (L := L) (p := p) (r := r) (x := x) (y := y) hy
  letI : Algebra F0 F1 := φ.toAlgebra
  letI : IsScalarTower F0 F1 L := by
    -- The old-stage map was defined as the codrestriction of `algebraMap E L`, so the route
    -- through `F1` agrees with the ambient `F0 → E → L` algebra structure.
    exact IsScalarTower.of_algebraMap_eq fun z ↦ by
      have hz := congrArg (fun ψ : F0 →+* L ↦ ψ z) hφ
      simpa [RingHom.comp_apply, F0] using hz.symm
  letI : IsScalarTower F0 E L := inferInstance
  letI : FiniteDimensional (separableClosure F0 E) E := by
    -- The source induction measure is finite over the old transcendence-basis stage.
    simpa [F0] using
      finiteDimensional_over_separableClosure_of_isTranscendenceBasis
        (k := F) (K := E) hx
  letI : Algebra.IsAlgebraic F0 F1 := by
    -- The old transcendence-basis stage is algebraic in `E`, and `L / E` is finite; hence every
    -- intermediate field of `L`, including `B(y)`, is algebraic over `F(x)`.
    have hF0E : Algebra.IsAlgebraic F0 E := by
      simpa [F0] using hx.isAlgebraic_field
    letI : Algebra.IsAlgebraic F0 E := hF0E
    letI : Algebra.IsAlgebraic F0 L := Algebra.IsAlgebraic.trans F0 E L
    exact Algebra.IsAlgebraic.tower_bot F0 F1 L
  have hβsep : algebraMap E L β ∈ separableClosure F1 L := by
    letI : CharP F1 p := charP_of_injective_algebraMap (algebraMap B F1).injective p
    have hFrobRange_F1 :
        ((minpoly F0 (β ^ p)).map φ) ∈
          Set.range (Polynomial.map (frobenius F1 p)) := by
      -- The generated-field bridge compares the coefficient map `φ` with the rational-function
      -- Frobenius base change, then transports Frobenius-range membership across `B(y)`.
      exact
        minpoly_mem_frobenius_range_pthRootStage
          (F := F) (B := B) (E := E) (L := L) (p := p) (r := r) (x := x) (y := y)
          hx hyBasis hy φ hφ hFrobRange
    have hφ_alg : (algebraMap F1 L).comp φ = algebraMap F0 L := by
      simpa using (IsScalarTower.algebraMap_eq F0 F1 L).symm
    have hβ_pow_mem_F0 : β ^ p ∈ separableClosure F0 E := by
      simpa [F0] using hβ_pow_mem
    -- With the Frobenius-range transport in the correct coefficient field, the existing
    -- separable-closure lemma pulls the mapped `p`th root into `separableClosure F1 L`.
    simpa [IsScalarTower.coe_toAlgHom'] using
      mapped_beta_mem_separableClosure_of_old_pow_mem_and_minpoly_frobenius_range
        (F := F0) (B := F1) (E := E) (L := L)
        (IsScalarTower.toAlgHom F0 E L) φ hφ_alg hβ_pow_mem_F0 hFrobRange_F1
  have hβ_deg_F0 :
      Module.finrank (separableClosure F0 E)
        (IntermediateField.adjoin (separableClosure F0 E) ({β} : Set E)) = p := by
    simpa [F0] using hβ_deg
  have hdrop : Field.finInsepDegree F1 L < Field.finInsepDegree F0 E :=
    finInsepDegree_drop_of_generated_top_absorbs_mapped_generator
      (F := F0) (B := F1) (E := E) (L := L) (β := β) (p := p)
      hGeneratedTop hβsep hβ_deg_F0
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, y, ?_⟩
  refine ⟨hyBasis, ?_⟩
  -- The generated-top degree-drop helper reduces the final inequality to the two transport
  -- facts isolated above.
  simpa [F0, F1] using hdrop

end
