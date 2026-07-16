import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_3_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_6_2.ShrinkTransport
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.FieldIndependence.CharacterRingFieldIndependence

/-!
# Serre's Theorem 24 over an abstract characteristic-`0` field (cyclotomic descent endgame)

This module proves `characterRing_eq_overlineCharacterRing_of_isSplittingField`, Serre's
Theorem 24 over an *arbitrary* characteristic-`0` field `k` containing enough roots of unity for
the exponent of `G`:
```
R[k](G) = R̄[k](G).
```

The `⊆` direction is `characterRingOverField_le_overlineCharacterRing`. For `⊇`, we run the
**cyclotomic descent**:

* Let `m := Monoid.exponent G`, `Q := CyclotomicField m ℚ` (a char-`0` field with enough `m`-th roots
  of unity, `cyclotomicField_exponent_hasEnoughRootsOfUnity`), `kbar := AlgebraicClosure k`,
  `Q̄ := AlgebraicClosure Q`.
* **Values land in `Q`.** Any `χ ∈ R̄[k](G)` has `extk χ ∈ R[kbar](G)`; its values are already in
  the (image of) `Q` because `Q` is sufficiently large
  (`character_value_mem_algebraMap_range_of_hasEnoughRoots_extension`). Since `Q ⊆ k`, the
  `k`-valued `χ` descends to a `Q`-valued `χ₀`.
* **Field independence.** `Q̄ ⊆ kbar` are algebraically closed and characteristic `0`, so the descent
  corollary `overlineCharacterRingInExtension_eq_characterRing_of_isAlgClosed` gives
  `overlineCharacterRingInExtension Q̄ kbar = R[Q̄](G)`. This places `extQ̄ χ₀` in `R[Q̄](G)`,
  i.e. `χ₀ ∈ R̄[Q](G)`.
* **Cyclotomic quasisplit.** Over `Q ↪ ℂ`, Serre's Theorem 24 holds
  (`characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_complexEmbedding`); transported
  along `Shrink.{0} G ≃* G` it gives `R[Q](G) = R̄[Q](G)`, so `χ₀ ∈ R[Q](G)`.
* **Ascend `Q → k`.** Mapping `R[Q](G)` along `Q → k` lands in `R[k](G)`
  (`map_mem_characterRingOverField_algHom`), recovering `χ = (algebraMap Q k) ∘ χ₀ ∈ R[k](G)`.

The embedding setup (a single coherent `Algebra Q kbar` with `IsScalarTower Q k kbar` and
`IsScalarTower Q Q̄ kbar`) is the fiddly part and is documented inline; it is reusable for any
"cyclotomic descent" argument over an abstract char-`0` base.
-/

noncomputable section

universe u v w

open scoped Representation

namespace Representation

open CategoryTheory

/-! ### Re-derived inputs from `Serre.Chap12.SplittingFieldOfEnoughRoots`

The file `Serre.Chap12.SplittingFieldOfEnoughRoots` cannot be imported here: it declares a bare
`local instance : Fintype G` whose auto-generated name `Representation.instFintype_serre` collides
with the identical declaration in `Serre.Chap12.Exercise_12_12_2_7` (a transitive import of
`Exercise_12_12_3_3`, which supplies the cyclotomic quasisplit input). To avoid editing those files,
the two facts needed below — the cyclotomic-field embedding of a sufficiently large char-`0` field,
and the value-landing statement for sufficiently large bases — are re-derived here verbatim under
private names. -/

section SplittingFieldInputs

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGEndgameInputs : Fintype G := Fintype.ofFinite G

/-- The cyclotomic field of the exponent of `G` contains enough exponent roots of unity. (Local copy
of `Representation.cyclotomicField_exponent_hasEnoughRootsOfUnity`.) -/
private instance cyclotomicField_exponent_hasEnoughRootsOfUnity_endgame :
    HasEnoughRootsOfUnity (CyclotomicField (Monoid.exponent G) ℚ) (Monoid.exponent G) where
  prim := by
    letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
    letI :
        IsCyclotomicExtension {Monoid.exponent G} ℚ
          (CyclotomicField (Monoid.exponent G) ℚ) :=
      CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
    simpa using
      (IsCyclotomicExtension.exists_isPrimitiveRoot
        (S := {Monoid.exponent G}) (A := ℚ)
        (B := CyclotomicField (Monoid.exponent G) ℚ)
        (n := Monoid.exponent G) (by simp)
        (show Monoid.exponent G ≠ 0 by exact NeZero.ne _))
  cyc := rootsOfUnity.isCyclic _ _

/-- A characteristic-zero field containing the exponent roots receives the exponent cyclotomic
field. (Local copy of `Representation.cyclotomicFieldExponentAlgHomOfHasEnoughRoots`.) -/
private noncomputable def cyclotomicFieldExponentAlgHom
    (K : Type u) [Field K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    CyclotomicField (Monoid.exponent G) ℚ →ₐ[ℚ] K := by
  classical
  let m := Monoid.exponent G
  let Lexp := CyclotomicField m ℚ
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {m} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := m) (K := ℚ)
  have hprim :
      ∀ n ∈ ({m} : Set ℕ), n ≠ 0 → ∃ r : K, IsPrimitiveRoot r n := by
    intro n hn _hn0
    rw [Set.mem_singleton_iff] at hn
    subst n
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K m
  let M : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ {x : K | ∃ n ∈ ({m} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
  let e : Lexp ≃ₐ[ℚ] M :=
    Classical.choice
      (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_exists_isPrimitiveRoot
        (S := {m}) ℚ Lexp K hprim)
  exact (IsScalarTower.toAlgHom ℚ M K).comp e.toAlgHom

/-- Over an algebraically closed extension field, character values of finite-group
representations are already in any sufficiently large base field. (Local copy of
`Representation.finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_algClosed`.) -/
private theorem finiteRep_character_value_mem_range_algClosed
    {F : Type v} [Field F]
    {Ω : Type u} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [HasEnoughRootsOfUnity F (Monoid.exponent G)]
    (ρ : Rep.{u} Ω G) [FiniteDimensional Ω ρ] (g : G) :
    ∃ x : F, algebraMap F Ω x = ρ.ρ.character g := by
  classical
  let m := Monoid.exponent G
  let b := Module.Free.chooseBasis Ω ρ
  let A :
      Matrix (Module.Free.ChooseBasisIndex Ω ρ)
        (Module.Free.ChooseBasisIndex Ω ρ) Ω :=
    LinearMap.toMatrix b b (ρ.ρ g)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F m
  let hprim : (primitiveRoots m F).Nonempty := by
    exact ⟨ζ, by
      rw [mem_primitiveRoots (Monoid.neZero_exponent_of_finite).pos]
      exact hζ⟩
  let e : rootsOfUnity m F ≃* rootsOfUnity m Ω :=
    rootsOfUnityEquivOfPrimitiveRoots
      (f := algebraMap F Ω)
      (algebraMap F Ω).injective hprim
  have hroot_preimage :
      ∀ μ ∈ A.charpoly.roots, ∃ x : F, algebraMap F Ω x = μ := by
    intro μ hμ
    have hμ_rep :
        μ ∈ (ρ.ρ g).charpoly.roots := by
      simpa [A] using hμ
    have hμ_order : μ ^ orderOf g = 1 :=
      Representation.charpoly_root_pow_orderOf_eq_one ρ.ρ g hμ_rep
    have hμ_exp : μ ^ m = 1 := by
      rcases Monoid.order_dvd_exponent g with ⟨d, hd⟩
      simp [m, hd, pow_mul, hμ_order]
    let μRoots : rootsOfUnity m Ω := rootsOfUnity.mkOfPowEq μ hμ_exp
    refine ⟨((e.symm μRoots : rootsOfUnity m F) : Fˣ), ?_⟩
    simpa [e, μRoots, rootsOfUnity.coe_mkOfPowEq] using
      rootsOfUnityEquivOfPrimitiveRoots_symm_apply
        (f := algebraMap F Ω)
        (n := m)
        (algebraMap F Ω).injective
        hprim
        μRoots
  have hsum_preimage :
      ∀ s : Multiset Ω,
        (∀ μ ∈ s, ∃ x : F, algebraMap F Ω x = μ) →
        ∃ x : F, algebraMap F Ω x = s.sum := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro _
      exact ⟨0, by simp⟩
    · intro μ s ih hs
      rcases hs μ (by simp) with ⟨xμ, hxμ⟩
      rcases ih (fun ν hν ↦ hs ν (by simp [hν])) with ⟨xs, hxs⟩
      refine ⟨xμ + xs, ?_⟩
      rw [map_add, hxμ, hxs]
      simp
  rcases hsum_preimage A.charpoly.roots hroot_preimage with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  calc
    algebraMap F Ω x = A.charpoly.roots.sum := hx
    _ = A.trace := by
          symm
          exact Matrix.trace_eq_sum_roots_charpoly A
    _ = ρ.ρ.character g := by
          symm
          simpa [A, Representation.character] using
            (LinearMap.trace_eq_matrix_trace Ω b (ρ.ρ g))

/-- Character values over any coefficient extension are in the sufficiently large base field.
(Local copy of `Representation.finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_extension`.) -/
private theorem finiteRep_character_value_mem_range_extension
    {F : Type v} [Field F]
    {E : Type u} [Field E] [Algebra F E]
    [HasEnoughRootsOfUnity F (Monoid.exponent G)]
    (ρ : Rep.{u} E G) [FiniteDimensional E ρ] (g : G) :
    ∃ x : F, algebraMap F E x = ρ.ρ.character g := by
  classical
  let Ω := AlgebraicClosure E
  let ρΩ : Rep.{u} Ω G := Rep.of (Representation.scalarExtension ρ.ρ)
  letI : FiniteDimensional Ω ρΩ := by
    dsimp [ρΩ]
    infer_instance
  obtain ⟨x, hx⟩ :=
    finiteRep_character_value_mem_range_algClosed
      (F := F) (Ω := Ω) (G := G) ρΩ g
  refine ⟨x, ?_⟩
  apply (algebraMap E Ω).injective
  calc
    algebraMap E Ω (algebraMap F E x) = algebraMap F Ω x := by
      simpa using (IsScalarTower.algebraMap_apply F E Ω x).symm
    _ = ρΩ.ρ.character g := hx
    _ = algebraMap E Ω (ρ.ρ.character g) := by
      simpa [ρΩ] using
        (congrFun
          (by
            ext h
            exact LinearMap.trace_baseChange (ρ.ρ h) Ω :
              (Representation.scalarExtension ρ.ρ).character =
                fun h ↦ algebraMap E Ω (ρ.ρ.character h))
          g)

/-- Over any coefficient extension, the value of a virtual character is already in a sufficiently
large base field. (Local copy of
`Representation.character_value_mem_algebraMap_range_of_hasEnoughRoots_extension`.) -/
private theorem character_value_mem_range_extension
    {F : Type v} [Field F]
    {E : Type u} [Field E] [Algebra F E]
    [HasEnoughRootsOfUnity F (Monoid.exponent G)]
    (χ : G → E) (hχ : χ ∈ R[E](G)) (g : G) :
    ∃ x : F, algebraMap F E x = χ g := by
  classical
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional E ρ := hρfd
    exact finiteRep_character_value_mem_range_extension
      (F := F) (E := E) (G := G) ρ g
  · intro n
    refine ⟨algebraMap ℤ F n, ?_⟩
    simp
  · intro φ ψ _ _ hφ hψ
    rcases hφ with ⟨xφ, hxφ⟩
    rcases hψ with ⟨xψ, hxψ⟩
    refine ⟨xφ + xψ, ?_⟩
    simp [map_add, hxφ, hxψ]
  · intro φ ψ _ _ hφ hψ
    rcases hφ with ⟨xφ, hxφ⟩
    rcases hψ with ⟨xψ, hxψ⟩
    refine ⟨xφ * xψ, ?_⟩
    simp [map_mul, hxφ, hxψ]

omit [Finite G] in
/-- Any finite-dimensional `E`-representation contributes an honest character-ring element even when
its carrier lives in a larger universe. (Local copy of the private universe bridge
`Representation.rep_character_mem_characterRingOverField_universe_bridge_local`.) -/
private theorem rep_character_mem_R_universe_bridge
    {E : Type u} [Field E]
    {V : Type w} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ρ : Representation E G V) :
    ρ.character ∈ R[E](G) := by
  -- Move to the coordinate model on `Fin n → E`, whose carrier lives in `Type u`; conjugation
  -- preserves the trace, so the character is unchanged.
  let e := (Module.finBasis E V).equivFun
  let ρfin : Representation E G (Fin (Module.finrank E V) → E) :=
    { toFun := fun h ↦ e.conj (ρ h)
      map_one' := by
        calc
          e.conj (ρ 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id e
      map_mul' := by
        intro g h
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let τ : Rep E G := Rep.of ρfin
  have hfin : ρ.character = ρfin.character := by
    ext h
    symm
    simpa [τ, ρfin, Representation.character] using
      (LinearMap.trace_conj' (ρ h) e)
  have hchar : ρ.character = τ.ρ.character := hfin
  exact hchar ▸ rep_character_mem_characterRingOverField (K := E) (G := G) τ

omit [Finite G] in
/-- Coefficientwise scalar extension along a fixed algebra structure preserves ordinary virtual
character rings: the image of `R[F](G)` under `F → E` lies in `R[E](G)`. (Adaptation of
`Representation.map_mem_characterRingOverField_algHom` using the ambient `Algebra F E`.) -/
private theorem map_mem_characterRingOverField_of_algebra
    {F : Type v} [Field F] {E : Type u} [Field E] [Algebra F E]
    (χ : G → F) (hχ : χ ∈ R[F](G)) :
    ((IsScalarTower.toAlgHom ℤ F E).compLeft G) χ ∈ R[E](G) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional F ρ := hρfd
    have hchar :
        ((IsScalarTower.toAlgHom ℤ F E).compLeft G) ρ.ρ.character =
          (Representation.scalarExtension (k := E) ρ.ρ).character := by
      ext g
      exact (LinearMap.trace_baseChange (ρ.ρ g) E).symm
    rw [hchar]
    -- The scalar extension's carrier lives in `max u v`; the universe-bridge helper places its
    -- character in `R[E](G)` regardless of the carrier universe.
    exact rep_character_mem_R_universe_bridge
      (E := E) (G := G) (ρ := Representation.scalarExtension (k := E) ρ.ρ)
  · intro n
    simpa using (R[E](G)).algebraMap_mem n
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](G)).add_mem hφ hψ
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](G)).mul_mem hφ hψ

end SplittingFieldInputs

section Endgame

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable [CharZero k] [HasEnoughRootsOfUnity k (Monoid.exponent G)]

/-! ### Step 3 (quasisplit over the cyclotomic field), via the `Shrink.{0}` universe transport. -/

/-- Transport of overline-ring membership along a multiplicative equivalence of finite groups. If
`χ : G → Q` lies in `R̄[Q](G)` (membership tested in `AlgebraicClosure Q`), then its precomposition
with `e : H ≃* G` lies in `R̄[Q](H)`. -/
private theorem mem_overlineCharacterRing_of_precomp_mulEquiv
    {Q : Type v} [Field Q] [CharZero Q]
    {H : Type w} [Group H] [Finite H] {GG : Type u} [Group GG] [Finite GG]
    (e : H ≃* GG) {χ : GG → Q} (hχ : χ ∈ R̄[Q](GG)) :
    (fun h : H ↦ χ (e h)) ∈ R̄[Q](H) := by
  -- Unfold both overline rings to membership in `R[Q̄](-)`, then transport the latter along `e`.
  rw [overlineCharacterRing, mem_overlineCharacterRingInExtension_iff] at hχ ⊢
  -- The goal is now (definitionally) `(fun h ↦ extQ̄(χ) (e h)) ∈ R[Q̄](H)`, the transport target.
  exact mem_characterRingOverField_of_precomp_mulEquiv_local
    (K := AlgebraicClosure Q) (G := GG) (H := H) e hχ

/-- **Quasisplit over a complex-embeddable cyclotomic-type field, in the source universe.** For any
characteristic-`0` field `F` that embeds into `ℂ` and contains enough roots of unity for the
exponent of `G`, Serre's Theorem 24 holds for `G : Type u`: `R[F](G) = R̄[F](G)`. This transports
the `Type 0` statement
`characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_complexEmbedding` along
`Shrink.{0} G ≃* G`. -/
private theorem quasisplit_of_complexEmbedding
    (F : Type v) [Field F] [CharZero F] [Algebra F ℂ]
    [HasEnoughRootsOfUnity F (Monoid.exponent G)] :
    R[F](G) = R̄[F](G) := by
  classical
  -- The `Type 0` copy of `G` and the group equivalence used to transport the statement.
  let H : Type 0 := Shrink.{0} G
  let e : H ≃* G := Shrink.mulEquiv
  haveI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  -- `F` has enough `(exponent H)`-th roots of unity, since `exponent H = exponent G`.
  have hexp : Monoid.exponent H = Monoid.exponent G := Monoid.exponent_eq_of_mulEquiv e
  haveI : HasEnoughRootsOfUnity F (Monoid.exponent H) := by rw [hexp]; infer_instance
  -- Theorem 24 over `F ↪ ℂ` for the `Type 0` group `H`.
  have hH : R[F](H) = R̄[F](H) :=
    characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_complexEmbedding
      (K := F) (G := H)
  -- Transport the equality back to `G` via the membership transports along `e`.
  apply le_antisymm
  · exact characterRingOverField_le_overlineCharacterRing F G
  · intro χ hχ
    -- `χ ∈ R̄[F](G)` ⟹ `χ ∘ e ∈ R̄[F](H)` ⟹ (quasisplit on `H`) `χ ∘ e ∈ R[F](H)`.
    have h1 : (fun h : H ↦ χ (e h)) ∈ R̄[F](H) :=
      mem_overlineCharacterRing_of_precomp_mulEquiv (Q := F) (H := H) (GG := G) e hχ
    rw [← hH] at h1
    -- ⟹ `(χ ∘ e) ∘ e.symm = χ ∈ R[F](G)`.
    have h2 : (fun g : G ↦ (fun h : H ↦ χ (e h)) (e.symm g)) ∈ R[F](G) :=
      mem_characterRingOverField_of_precomp_mulEquiv_local
        (K := F) (G := H) (H := G) e.symm h1
    simpa using h2

/-! ### The `Type u` cyclotomic subfield of `k`.

To run the (universe-monomorphic) field-independence corollary with both fields in universe `u`, we
realise the exponent cyclotomic field *inside* `k` as the intermediate field generated over `ℚ` by
the exponent roots of unity.  Its coercion `↥cyclotomicSubfield` is a genuine `Type u` subfield of
`k` with clean (non-`ULift`) instances — in particular no `ℤ`-scalar-tower diamond — and is
`ℚ`-isomorphic to `CyclotomicField (exponent G) ℚ`. -/

/-- The intermediate field of `k` generated over `ℚ` by the exponent roots of unity: a `Type u`
realisation of the exponent cyclotomic field. -/
private def cyclotomicSubfield : IntermediateField ℚ k :=
  IntermediateField.adjoin ℚ
    {x : k | ∃ n ∈ ({Monoid.exponent G} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}

/-- The `ℚ`-algebra equivalence between the exponent cyclotomic field and its `Type u` realisation
inside `k`. (Same construction as `cyclotomicFieldExponentAlgHom`, but kept as an equivalence.) -/
private noncomputable def cyclotomicSubfieldEquiv :
    CyclotomicField (Monoid.exponent G) ℚ ≃ₐ[ℚ] (cyclotomicSubfield (k := k) (G := G)) := by
  classical
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ (CyclotomicField (Monoid.exponent G) ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
  have hprim :
      ∀ n ∈ ({Monoid.exponent G} : Set ℕ), n ≠ 0 → ∃ r : k, IsPrimitiveRoot r n := by
    intro n hn _hn0
    rw [Set.mem_singleton_iff] at hn
    subst n
    exact HasEnoughRootsOfUnity.exists_primitiveRoot k (Monoid.exponent G)
  exact
    Classical.choice
      (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_exists_isPrimitiveRoot
        (S := {Monoid.exponent G}) ℚ (CyclotomicField (Monoid.exponent G) ℚ) k hprim)

/-- The `Type u` cyclotomic subfield of `k` is algebraic over `ℚ`. -/
private instance cyclotomicSubfield_isAlgebraic :
    Algebra.IsAlgebraic ℚ (cyclotomicSubfield (k := k) (G := G)) := by
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ (CyclotomicField (Monoid.exponent G) ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
  haveI : Algebra.IsAlgebraic ℚ (CyclotomicField (Monoid.exponent G) ℚ) := inferInstance
  exact (cyclotomicSubfieldEquiv (k := k) (G := G)).isAlgebraic

/-- The `Type u` cyclotomic subfield of `k` contains enough exponent roots of unity. -/
private theorem cyclotomicSubfield_hasEnoughRoots :
    HasEnoughRootsOfUnity (cyclotomicSubfield (k := k) (G := G)) (Monoid.exponent G) := by
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  haveI : HasEnoughRootsOfUnity (CyclotomicField (Monoid.exponent G) ℚ) (Monoid.exponent G) :=
    cyclotomicField_exponent_hasEnoughRootsOfUnity_endgame (G := G)
  exact MulEquiv.hasEnoughRootsOfUnity
    (((cyclotomicSubfieldEquiv (k := k) (G := G)).toRingEquiv.toMulEquiv).restrictRootsOfUnity
      (Monoid.exponent G))

/-! ### The main descent theorem. -/

/-- **Serre's Theorem 24 over a characteristic-`0` splitting field (cyclotomic-descent endgame).**
If `k` has characteristic `0` and contains enough roots of unity for the exponent of `G`, then
Serre's intrinsic character ring `R[k](G)` coincides with the ordinary character ring `R̄[k](G)`.
This is the worker proving the statement-level theorem
`Representation.characterRing_eq_overlineCharacterRing_of_isSplittingField` in
`Serre.Chap14.Remark_14_14_5_1`. -/
theorem characterRing_eq_overlineCharacterRing_of_isSplittingField_endgame :
    R[k](G) = R̄[k](G) := by
  classical
  haveI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  -- The `Type u` cyclotomic subfield `M ⊆ k`, its algebraic closure `Mbar : Type u`, and the
  -- algebraic closure `kbar : Type u` of `k`.  Working with `M : Type u` (rather than the `Type 0`
  -- cyclotomic field) keeps both fields fed to the universe-monomorphic field-independence
  -- corollary in universe `u`.
  set M := cyclotomicSubfield (k := k) (G := G) with hM
  set kbar := AlgebraicClosure k with hkbar
  set Mbar := AlgebraicClosure (M : Type u) with hMbar
  -- ### Instances on the `Type u` cyclotomic subfield `M`.
  haveI hRM : HasEnoughRootsOfUnity (M : Type u) (Monoid.exponent G) :=
    cyclotomicSubfield_hasEnoughRoots (k := k) (G := G)
  -- `Algebra M ℂ`: `M` is algebraic over `ℚ`, hence embeds into the algebraically closed `ℂ`.
  letI algMC : Algebra (M : Type u) ℂ :=
    (IsAlgClosed.lift (R := ℚ) (S := (M : Type u)) (M := ℂ)).toRingHom.toAlgebra
  -- ### Embedding setup `M ⊆ k ⊆ kbar` and `M ⊆ Mbar ⊆ kbar`.
  -- `M ⊆ k` is the native intermediate-field inclusion.  Mathlib then supplies `Algebra M kbar`
  -- (= `AlgebraicClosure.instAlgebra`) and the compatible `IsScalarTower M k kbar` automatically,
  -- so the triangle `M → k → kbar` already commutes.
  haveI towerMk : IsScalarTower (M : Type u) k kbar := inferInstance
  -- `Mbar → kbar` over `M` via `IsAlgClosed.lift`, giving the tower `IsScalarTower M Mbar kbar`.
  letI algMbarkbar : Algebra Mbar kbar :=
    (IsAlgClosed.lift (R := (M : Type u)) (S := Mbar) (M := kbar)).toRingHom.toAlgebra
  haveI towerMMbar : IsScalarTower (M : Type u) Mbar kbar :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      ((IsAlgClosed.lift (R := (M : Type u)) (S := Mbar) (M := kbar)).commutes x).symm
  -- The `ℤ`-tower through the custom `Algebra Mbar kbar` holds because `ℤ` is the initial ring.
  -- It is stated in the `Algebra.toSMul` form expected by `IsScalarTower.toAlgHom`, so that the
  -- (defeq but syntactically distinct) `zsmul` form does not block instance resolution on the
  -- algebraic closure `Mbar`.
  haveI towerZMbarkbar : @IsScalarTower ℤ Mbar kbar Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    ⟨fun (n : ℤ) (a : Mbar) (b : kbar) => by
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      congr 1
      exact DFunLike.congr_fun (RingHom.ext_int
        ((algebraMap Mbar kbar).comp (algebraMap ℤ Mbar)) (algebraMap ℤ kbar)) n⟩
  refine le_antisymm (characterRingOverField_le_overlineCharacterRing k G) ?_
  intro χ hχ
  -- `hχ : χ ∈ R̄[k](G)`, i.e. `extk χ ∈ R[kbar](G)`.
  have hχ_kbar :
      ((IsScalarTower.toAlgHom ℤ k kbar).compLeft G) χ ∈ R[kbar](G) :=
    (mem_overlineCharacterRingInExtension_iff k kbar χ).1 hχ
  -- #### Step 1: the values of `χ` already lie in `M`.
  -- Each value `algebraMap k kbar (χ g)` is in the range of `algebraMap M kbar`, hence (`M ⊆ k`,
  -- injectivity of `k → kbar`) `χ g ∈ range (algebraMap M k)`.
  have hvals : ∀ g : G, ∃ q : (M : Type u), algebraMap (M : Type u) k q = χ g := by
    intro g
    obtain ⟨q, hq⟩ :=
      character_value_mem_range_extension (F := (M : Type u)) (E := kbar)
        (((IsScalarTower.toAlgHom ℤ k kbar).compLeft G) χ) hχ_kbar g
    refine ⟨q, ?_⟩
    -- `algebraMap M kbar q = algebraMap k kbar (χ g)`; rewrite the LHS through the tower `M → k`.
    apply FaithfulSMul.algebraMap_injective k kbar
    rw [← IsScalarTower.algebraMap_apply (M : Type u) k kbar q]
    simpa using hq
  choose χ₀ hχ₀ using hvals
  -- #### Step 4 (recorded early): `χ = (algebraMap M k) ∘ χ₀`, the lift along `M → k`.
  have hχeq : ((IsScalarTower.toAlgHom ℤ (M : Type u) k).compLeft G) χ₀ = χ := by
    ext g; simpa using hχ₀ g
  -- #### Step 2: `χ₀ ∈ R̄[M](G)` (membership tested in `Mbar`), by field independence over `kbar`.
  have hχ₀_overlineM : χ₀ ∈ R̄[(M : Type u)](G) := by
    rw [overlineCharacterRing, mem_overlineCharacterRingInExtension_iff]
    -- Suffices: `extMbar χ₀ ∈ R[Mbar](G) = overlineCharacterRingInExtension Mbar kbar`.
    rw [← overlineCharacterRingInExtension_eq_characterRing_of_isAlgClosed (L := Mbar) (E := kbar)]
    rw [mem_overlineCharacterRingInExtension_iff]
    -- The double embedding `M → Mbar → kbar` of `χ₀` equals `extk χ` (single embedding `k → kbar`).
    have hbridge :
        ((IsScalarTower.toAlgHom ℤ Mbar kbar).compLeft G)
            (((IsScalarTower.toAlgHom ℤ (M : Type u) Mbar).compLeft G) χ₀) =
          ((IsScalarTower.toAlgHom ℤ k kbar).compLeft G) χ := by
      funext g
      change algebraMap Mbar kbar (algebraMap (M : Type u) Mbar (χ₀ g)) =
        algebraMap k kbar (χ g)
      rw [← IsScalarTower.algebraMap_apply (M : Type u) Mbar kbar (χ₀ g), ← hχ₀ g,
        ← IsScalarTower.algebraMap_apply (M : Type u) k kbar (χ₀ g)]
    exact hbridge ▸ hχ_kbar
  -- #### Step 3: cyclotomic quasisplit `R[M](G) = R̄[M](G)` gives `χ₀ ∈ R[M](G)`.
  have hχ₀_M : χ₀ ∈ R[(M : Type u)](G) := by
    rw [quasisplit_of_complexEmbedding (G := G) (M : Type u)]; exact hχ₀_overlineM
  -- #### Step 4: ascend `M → k`, recovering `χ ∈ R[k](G)`.
  have := map_mem_characterRingOverField_of_algebra (F := (M : Type u)) (E := k) (G := G) χ₀ hχ₀_M
  exact hχeq ▸ this

end Endgame

end Representation
