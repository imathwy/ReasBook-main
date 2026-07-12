import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.Chap10.Lemma_10_21_5
import StacksProject_2024.Chap10.Lemma_10_23_2
import StacksProject_2024.Chap15.Lemma_15_9_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {C : Type v}
variable [CommRing A] [CommRing C] [Algebra A C]

local notation:max "A[" f "]" => Localization.Away f
local notation:max "C[" f "]" => Localization.Away (algebraMap A C f)

noncomputable local instance localizedAwayAlgebra (f : A) : Algebra A[f] C[f] :=
  (Localization.awayMapₐ (Algebra.ofId A C) f).toAlgebra

/-- Helper for Lemma 15.109.3: the canonical localization algebra `A[f] → C[f]` is compatible
with the base map `A → A[f]`. Recording the scalar tower explicitly keeps later overlap
computations from stalling on tower synthesis. -/
local instance localizedAwayScalarTower (f : A) : IsScalarTower A A[f] C[f] :=
  IsScalarTower.of_algebraMap_eq' <|
    RingHom.ext fun a ↦ by
      simpa using ((Localization.awayMapₐ (Algebra.ofId A C) f).commutes a).symm

/-- Helper for Lemma 15.109.3: the common target overlap `C[x * y]` is the canonical
away-localization at the product of the two localized base elements. Making this instance explicit
keeps the later target-overlap maps from getting stuck on `map_mul` coercions. -/
local instance target_overlap_product_isLocalizationAway (x y : A) :
    IsLocalization.Away ((algebraMap A C x) * (algebraMap A C y)) C[x * y] := by
  -- Rewrite the localized product `x * y` through `map_mul`.
  simpa [map_mul] using
    (inferInstance : IsLocalization.Away (algebraMap A C (x * y)) C[x * y])

/-- Helper for Lemma 15.109.3: the common target overlap `C[x * y]` carries the canonical
`C[x]`-algebra structure induced by localizing the `x`-chart further at `y`. -/
noncomputable local instance target_overlap_right_algebra (x y : A) : Algebra C[x] C[x * y] :=
  (IsLocalization.Away.awayToAwayRight (algebraMap A C x) (algebraMap A C y)).toAlgebra

/-- Helper for Lemma 15.109.3: the common target overlap `C[x * y]` carries the canonical
`C[y]`-algebra structure induced by localizing the `y`-chart further at `x`. -/
noncomputable local instance target_overlap_left_algebra (x y : A) : Algebra C[y] C[x * y] :=
  (IsLocalization.Away.awayToAwayLeft (algebraMap A C y) (algebraMap A C x)).toAlgebra

/-- Helper for Lemma 15.109.3: the common overlap `A[x * y]` carries the canonical
`A[x]`-algebra structure induced by localizing the `x`-chart further at `y`. -/
noncomputable local instance overlap_right_algebra (x y : A) : Algebra A[x] A[x * y] :=
  (IsLocalization.Away.awayToAwayRight x y).toAlgebra

/-- Helper for Lemma 15.109.3: the common overlap `A[x * y]` carries the canonical
`A[y]`-algebra structure induced by localizing the `y`-chart further at `x`. -/
noncomputable local instance overlap_left_algebra (x y : A) : Algebra A[y] A[x * y] :=
  (IsLocalization.Away.awayToAwayLeft y x).toAlgebra

/-- Helper for Lemma 15.109.3: under the right-overlap algebra structure, base elements of `A`
map to their usual image in the common overlap ring. -/
lemma overlap_right_algebraMap_eq
    (x y a : A) :
    algebraMap A[x] A[x * y] (algebraMap A A[x] a) = algebraMap A A[x * y] a := by
  -- Normalize the right-overlap algebra map on a base element using the owner equality for
  -- `awayToAwayRight`.
  simpa using IsLocalization.Away.awayToAwayRight_eq (S := A[x]) x y a

/-- Helper for Lemma 15.109.3: under the left-overlap algebra structure, base elements of `A`
map to their usual image in the common overlap ring. -/
lemma overlap_left_algebraMap_eq
    (x y a : A) :
    algebraMap A[y] A[x * y] (algebraMap A A[y] a) = algebraMap A A[x * y] a := by
  -- Normalize the left-overlap algebra map on a base element using the owner equality for
  -- `awayToAwayLeft`.
  simpa using IsLocalization.Away.awayToAwayLeft_eq (S := A[y]) y x a

/-- Helper for Lemma 15.109.3: passing from the `i`-chart of `A` to the common overlap and then
to the target overlap agrees with first mapping to the target `i`-chart and then localizing
there. -/
lemma overlap_right_target_comp
    {r : ℕ} (g : Fin r → A) (i j : Fin r) :
    ((IsLocalization.Away.awayToAwayRight
          (algebraMap A C (g i)) (algebraMap A C (g j))) : C[g i] →+* C[g i * g j]).comp
        (algebraMap A[g i] C[g i]) =
      (algebraMap A[g i * g j] C[g i * g j]).comp
        (IsLocalization.Away.awayToAwayRight (g i) (g j) : A[g i] →+* A[g i * g j]) := by
  -- Proof comment: compare the two maps out of `A[g i]` by the localization extensionality
  -- principle. On base elements of `A`, both composites normalize to the same canonical image in
  -- `C[g i * g j]`.
  apply IsLocalization.ringHom_ext (Submonoid.powers (g i))
  ext a
  have hbase_source :
      algebraMap A[g i] C[g i] (algebraMap A A[g i] a) = algebraMap A C[g i] a := by
    simpa using (congrArg (fun φ : A →+* C[g i] ↦ φ a)
      (IsScalarTower.algebraMap_eq A A[g i] C[g i])).symm
  have hbase_source_C :
      algebraMap A C[g i] a = algebraMap C C[g i] (algebraMap A C a) := by
    simpa using congrArg (fun φ : A →+* C[g i] ↦ φ a)
      (IsScalarTower.algebraMap_eq A C C[g i])
  have hbase_target :
      algebraMap A[g i * g j] C[g i * g j] (algebraMap A A[g i * g j] a) =
        algebraMap A C[g i * g j] a := by
    simpa using (congrArg (fun φ : A →+* C[g i * g j] ↦ φ a)
      (IsScalarTower.algebraMap_eq A A[g i * g j] C[g i * g j])).symm
  have hbase_target_C :
      algebraMap A C[g i * g j] a =
        algebraMap C C[g i * g j] (algebraMap A C a) := by
    simpa using congrArg (fun φ : A →+* C[g i * g j] ↦ φ a)
      (IsScalarTower.algebraMap_eq A C C[g i * g j])
  have hsource_overlap :
      ((IsLocalization.Away.awayToAwayRight (g i) (g j) : A[g i] →+* A[g i * g j])
        (algebraMap A A[g i] a)) = algebraMap A A[g i * g j] a := by
    simpa using overlap_right_algebraMap_eq (x := g i) (y := g j) (a := a)
  -- Proof comment: both sides now rewrite to the canonical image of `a` in the common target
  -- overlap.
  simp only [RingHom.comp_apply]
  calc
    ((IsLocalization.Away.awayToAwayRight
          (algebraMap A C (g i)) (algebraMap A C (g j))) : C[g i] →+* C[g i * g j])
        (algebraMap A[g i] C[g i] (algebraMap A A[g i] a))
        = ((IsLocalization.Away.awayToAwayRight
            (algebraMap A C (g i)) (algebraMap A C (g j))) : C[g i] →+* C[g i * g j])
            (algebraMap A C[g i] a) := by rw [hbase_source]
    _ = ((IsLocalization.Away.awayToAwayRight
            (algebraMap A C (g i)) (algebraMap A C (g j))) : C[g i] →+* C[g i * g j])
            (algebraMap C C[g i] (algebraMap A C a)) := by rw [hbase_source_C]
    _ = algebraMap C C[g i * g j] (algebraMap A C a) := by
          simpa using IsLocalization.Away.awayToAwayRight_eq
            (S := C[g i]) (algebraMap A C (g i)) (algebraMap A C (g j)) (algebraMap A C a)
    _ = algebraMap A C[g i * g j] a := by rw [← hbase_target_C]
    _ = algebraMap A[g i * g j] C[g i * g j] (algebraMap A A[g i * g j] a) := by
          rw [← hbase_target]
    _ = algebraMap A[g i * g j] C[g i * g j]
          ((IsLocalization.Away.awayToAwayRight (g i) (g j) : A[g i] →+* A[g i * g j])
            (algebraMap A A[g i] a)) := by
          rw [← hsource_overlap]

/-- Helper for Lemma 15.109.3: passing from the `j`-chart of `A` to the common overlap and then
to the target overlap agrees with first mapping to the target `j`-chart and then localizing
there. -/
lemma overlap_left_target_comp
    {r : ℕ} (g : Fin r → A) (i j : Fin r) :
    ((IsLocalization.Away.awayToAwayLeft
          (algebraMap A C (g j)) (algebraMap A C (g i))) : C[g j] →+* C[g i * g j]).comp
        (algebraMap A[g j] C[g j]) =
      (algebraMap A[g i * g j] C[g i * g j]).comp
        (IsLocalization.Away.awayToAwayLeft (g j) (g i) : A[g j] →+* A[g i * g j]) := by
  -- Proof comment: the left-chart square is proved by the same localization-extensionality
  -- comparison as the right-chart square.
  apply IsLocalization.ringHom_ext (Submonoid.powers (g j))
  ext a
  have hbase_source :
      algebraMap A[g j] C[g j] (algebraMap A A[g j] a) = algebraMap A C[g j] a := by
    simpa using (congrArg (fun φ : A →+* C[g j] ↦ φ a)
      (IsScalarTower.algebraMap_eq A A[g j] C[g j])).symm
  have hbase_source_C :
      algebraMap A C[g j] a = algebraMap C C[g j] (algebraMap A C a) := by
    simpa using congrArg (fun φ : A →+* C[g j] ↦ φ a)
      (IsScalarTower.algebraMap_eq A C C[g j])
  have hbase_target :
      algebraMap A[g i * g j] C[g i * g j] (algebraMap A A[g i * g j] a) =
        algebraMap A C[g i * g j] a := by
    simpa using (congrArg (fun φ : A →+* C[g i * g j] ↦ φ a)
      (IsScalarTower.algebraMap_eq A A[g i * g j] C[g i * g j])).symm
  have hbase_target_C :
      algebraMap A C[g i * g j] a =
        algebraMap C C[g i * g j] (algebraMap A C a) := by
    simpa using congrArg (fun φ : A →+* C[g i * g j] ↦ φ a)
      (IsScalarTower.algebraMap_eq A C C[g i * g j])
  have hsource_overlap :
      ((IsLocalization.Away.awayToAwayLeft (g j) (g i) : A[g j] →+* A[g i * g j])
        (algebraMap A A[g j] a)) = algebraMap A A[g i * g j] a := by
    simpa using overlap_left_algebraMap_eq (x := g i) (y := g j) (a := a)
  -- Proof comment: after reducing both composites to base elements of `A`, the owner
  -- `awayToAwayLeft_eq` identity gives the common target image.
  simp only [RingHom.comp_apply]
  calc
    ((IsLocalization.Away.awayToAwayLeft
          (algebraMap A C (g j)) (algebraMap A C (g i))) : C[g j] →+* C[g i * g j])
        (algebraMap A[g j] C[g j] (algebraMap A A[g j] a))
        = ((IsLocalization.Away.awayToAwayLeft
            (algebraMap A C (g j)) (algebraMap A C (g i))) : C[g j] →+* C[g i * g j])
            (algebraMap A C[g j] a) := by rw [hbase_source]
    _ = ((IsLocalization.Away.awayToAwayLeft
            (algebraMap A C (g j)) (algebraMap A C (g i))) : C[g j] →+* C[g i * g j])
            (algebraMap C C[g j] (algebraMap A C a)) := by rw [hbase_source_C]
    _ = algebraMap C C[g i * g j] (algebraMap A C a) := by
          simpa using IsLocalization.Away.awayToAwayLeft_eq
            (S := C[g j]) (algebraMap A C (g j)) (algebraMap A C (g i)) (algebraMap A C a)
    _ = algebraMap A C[g i * g j] a := by rw [← hbase_target_C]
    _ = algebraMap A[g i * g j] C[g i * g j] (algebraMap A A[g i * g j] a) := by
          rw [← hbase_target]
    _ = algebraMap A[g i * g j] C[g i * g j]
          ((IsLocalization.Away.awayToAwayLeft (g j) (g i) : A[g j] →+* A[g i * g j])
            (algebraMap A A[g j] a)) := by
          rw [← hsource_overlap]

/-- Helper for Lemma 15.109.3: the common target overlap `C[g_i g_j]` is the canonical
away-localization of the target `i`-chart further at `g_j`. Writing this instance explicitly keeps
the later overlap comparisons away from `map_mul`-driven typeclass search. -/
lemma target_overlap_right_isLocalizationAway
    {r : ℕ} (g : Fin r → A) (i j : Fin r) :
    IsLocalization.Away ((algebraMap A C (g i)) * (algebraMap A C (g j))) C[g i * g j] := by
  -- Proof comment: the target overlap is by definition localized away from `g_i g_j`; rewrite the
  -- localized element using `map_mul`.
  simpa [map_mul] using
    (inferInstance : IsLocalization.Away (algebraMap A C (g i * g j)) C[g i * g j])

/-- Helper for Lemma 15.109.3: the common target overlap `C[g_i g_j]` is also the canonical
away-localization of the target `j`-chart further at `g_i`. This is the left-chart companion to
`target_overlap_right_isLocalizationAway`. -/
lemma target_overlap_left_isLocalizationAway
    {r : ℕ} (g : Fin r → A) (i j : Fin r) :
    IsLocalization.Away ((algebraMap A C (g j)) * (algebraMap A C (g i))) C[g i * g j] := by
  -- Proof comment: use the same target-overlap instance, but rewrite the product in the order
  -- expected by `awayToAwayLeft`.
  simpa [map_mul, mul_comm] using
    (inferInstance : IsLocalization.Away (algebraMap A C (g i * g j)) C[g i * g j])

/-- Helper for Lemma 15.109.3: the direct localization `R[x * y]` is also the localization of the
`y`-chart as an `R[y]`-algebra via the canonical left-overlap map. Recording this algebra
structure explicitly keeps the generic iterated-vs-direct comparison below from stalling on
instance search. -/
noncomputable local instance away_left_chart_algebra
    {R : Type*} [CommRing R] (x y : R) :
    Algebra (Localization.Away y) (Localization.Away (x * y)) :=
  (IsLocalization.Away.awayToAwayLeft
    (S := Localization.Away y)
    (P := Localization.Away (x * y))
    (x := y)
    x).toAlgebra

/-- Helper for Lemma 15.109.3: the direct product-localization realizes the expected scalar tower
`R → R[y] → R[xy]`. Making the tower explicit lets the generic comparison lemma below rewrite base
elements by `IsScalarTower.algebraMap_eq` instead of unfolding localization maps. -/
local instance away_left_chart_scalarTower
    {R : Type*} [CommRing R] (x y : R) :
    IsScalarTower R (Localization.Away y) (Localization.Away (x * y)) :=
  IsScalarTower.of_algebraMap_eq' <|
    RingHom.ext fun a ↦ by
      simpa using
        (IsLocalization.Away.awayToAwayLeft_eq
          (S := Localization.Away y)
          (x := y)
          (y := x)
          (P := Localization.Away (x * y))
          a).symm

/-- Helper for Lemma 15.109.3: the direct localization `R[x * y]` is also the localization of the
`y`-chart `R[y]` away from the image of `x`. This packages the standard comparison between a
single product-localization and an iterated away-localization into a reusable owner-facing form. -/
lemma away_left_chart_isLocalizationAway
    {R : Type*} [CommRing R] (x y : R) :
    IsLocalization.Away (algebraMap R (Localization.Away y) x) (Localization.Away (x * y)) := by
  let B := Localization.Away y
  let D := Localization.Away (algebraMap R B x)
  let φR :
      D ≃ₐ[R] Localization.Away (x * y) :=
    IsLocalization.algEquiv
      (Submonoid.powers (x * y))
      D
      (Localization.Away (x * y))
  let φB :
      D ≃ₐ[B] Localization.Away (x * y) :=
    { φR with
      commutes' := by
        -- Proof comment: compare the two `B`-algebra maps by localization extensionality on the
        -- `y`-chart and then reduce both sides to the canonical image of a base element of `R`.
        have hmaps :
            ((φR : D →+* Localization.Away (x * y)).comp (algebraMap B D)) =
              algebraMap B (Localization.Away (x * y)) := by
          apply IsLocalization.ringHom_ext (Submonoid.powers y)
          ext a
          have hbase_D :
              algebraMap B D (algebraMap R B a) = algebraMap R D a := by
            simpa [B] using congrArg (fun ψ : R →+* D ↦ ψ a)
              (IsScalarTower.algebraMap_eq R B D)
          have hbase_xy :
              algebraMap B (Localization.Away (x * y)) (algebraMap R B a) =
                algebraMap R (Localization.Away (x * y)) a := by
            simpa [B] using
              (congrArg (fun ψ : R →+* Localization.Away (x * y) ↦ ψ a)
                (IsScalarTower.algebraMap_eq R B (Localization.Away (x * y)))).symm
          simp only [RingHom.comp_apply]
          calc
            φR (algebraMap B D (algebraMap R B a))
                = φR (algebraMap R D a) := by rw [hbase_D]
            _ = algebraMap R (Localization.Away (x * y)) a := by
                  simpa using φR.commutes a
            _ = algebraMap B (Localization.Away (x * y)) (algebraMap R B a) := by
                  rw [hbase_xy]
        intro b
        exact congrArg (fun ψ : B →+* Localization.Away (x * y) ↦ ψ b) hmaps }
  -- Proof comment: transport the canonical iterated-localization structure across the
  -- `B`-algebra equivalence between `D` and the direct product-localization.
  simpa [B, D] using
    (IsLocalization.isLocalization_of_algEquiv
      (M := Submonoid.powers (algebraMap R B x))
      (S := D)
      (P := Localization.Away (x * y))
      φB)

/-- Helper for Lemma 15.109.3: for arbitrary commutative rings, an away-localization at an
idempotent has kernel equal to the complementary principal ideal. This owner-level form is the
stable input for the later overlap kernel comparisons. -/
lemma descended_localization_kernel_eq_span_one_sub
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {e : R}
    (he : IsIdempotentElem e)
    (hS : IsLocalization.Away e S) :
    RingHom.ker (algebraMap R S) = Ideal.span ({1 - e} : Set R) := by
  letI := hS
  letI : IsLocalization.Away e (R ⧸ Ideal.span ({1 - e} : Set R)) := by
    -- Repackage Lemma `10.21.5` with the complementary idempotent `1 - e`.
    simpa using
      (quotient_isLocalization_Away_one_sub_of_idempotent_generator
        (R := R) (I := Ideal.span ({1 - e} : Set R)) (e := 1 - e) he.one_sub
        (by simp : Ideal.span ({1 - e} : Set R) = R ∙ (1 - e)))
  let φ : (R ⧸ Ideal.span ({1 - e} : Set R)) ≃ₐ[R] S :=
    IsLocalization.algEquiv (Submonoid.powers e)
      (R ⧸ Ideal.span ({1 - e} : Set R)) S
  -- Compare kernel membership by transporting across the quotient-away equivalence.
  ext x
  constructor
  · intro hx
    have hcomm :
        φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = algebraMap R S x := by
      simpa using φ.commutes x
    have hx' : φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = 0 := by
      exact hcomm.trans (RingHom.mem_ker.mp hx)
    have hmk :
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x = 0 := by
      apply φ.injective
      simpa using hx'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · intro hx
    have hmk :
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hcomm :
        φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = algebraMap R S x := by
      simpa using φ.commutes x
    have hx' : φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = φ 0 :=
      congrArg φ hmk
    have hx0 : algebraMap R S x = 0 := by
      calc
        algebraMap R S x = φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) := hcomm.symm
        _ = φ 0 := hx'
        _ = 0 := by simp
    exact RingHom.mem_ker.mpr hx0

/-- Helper for Lemma 15.109.3: the canonical quotient by the complementary idempotent ideal is the
same away-localization as any given away-localization at the idempotent. -/
lemma idempotent_away_quotient_algEquiv_nonempty
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {e : R}
    (he : IsIdempotentElem e)
    (hS : IsLocalization.Away e S) :
    Nonempty ((R ⧸ Ideal.span ({1 - e} : Set R)) ≃ₐ[R] S) := by
  letI := hS
  letI : IsLocalization.Away e (R ⧸ Ideal.span ({1 - e} : Set R)) := by
    -- Repackage Lemma 10.21.5 with the complementary idempotent `1 - e`.
    simpa using
      (quotient_isLocalization_Away_one_sub_of_idempotent_generator
        (R := R) (I := Ideal.span ({1 - e} : Set R)) (e := 1 - e) he.one_sub
        (by simp : Ideal.span ({1 - e} : Set R) = R ∙ (1 - e)))
  -- Both rings now realize the same localization away from `e`.
  exact ⟨IsLocalization.algEquiv (Submonoid.powers e)
    (R ⧸ Ideal.span ({1 - e} : Set R)) S⟩

/-- Helper for Lemma 15.109.3: after localizing at `f`, an idempotent presentation of `C[f]`
splits `A[f]` as the product of `C[f]` and the quotient by the complementary idempotent ideal,
provided the kernel is exactly that complementary principal ideal. -/
lemma localized_idempotent_factor_exists
    {f : A} {e : A[f]}
    (he : IsIdempotentElem e)
    (hC : IsLocalization.Away e C[f])
    (hker : RingHom.ker (algebraMap A[f] C[f]) = Ideal.span ({1 - e} : Set A[f])) :
    Nonempty (A[f] ≃ₐ[A[f]] (C[f] × (A[f] ⧸ Ideal.span ({e} : Set A[f])))) := by
  letI := hC
  -- The localization away from an idempotent is a quotient by the complementary idempotent ideal.
  have hsurj : Function.Surjective (algebraMap A[f] C[f]) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  let quotientToLocalized :
      (A[f] ⧸ Ideal.span ({1 - e} : Set A[f])) ≃ₐ[A[f]] C[f] :=
    (Ideal.quotientEquivAlgOfEq (A[f]) hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (R₁ := A[f]) (f := Algebra.ofId A[f] C[f]) hsurj)
  -- The complementary idempotents `1 - e` and `e` give the standard product decomposition.
  let splitByIdempotent :
      A[f] ≃ₐ[A[f]]
        ((A[f] ⧸ Ideal.span ({1 - e} : Set A[f])) ×
          (A[f] ⧸ Ideal.span ({e} : Set A[f]))) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem (A[f]) he.one_sub he (by simp)
      (by simpa [sub_mul, he.eq])
  -- Replace the first quotient factor by the given localized algebra `C[f]`.
  exact ⟨splitByIdempotent.trans <|
    AlgEquiv.prodCongr quotientToLocalized
      (AlgEquiv.refl : (A[f] ⧸ Ideal.span ({e} : Set A[f])) ≃ₐ[A[f]]
        (A[f] ⧸ Ideal.span ({e} : Set A[f])))⟩

/-- Helper for Lemma 15.109.3: a localization away from an idempotent is the canonical quotient by
the complementary principal ideal. -/
lemma localized_away_kernel_eq_span_one_sub
    {f : A} {e : A[f]}
    (he : IsIdempotentElem e)
    (hC : IsLocalization.Away e C[f]) :
    RingHom.ker (algebraMap A[f] C[f]) = Ideal.span ({1 - e} : Set A[f]) := by
  -- Route correction: use the generic owner-level kernel computation for away-localizations at
  -- idempotents instead of duplicating the quotient comparison inside the chart-specific theorem.
  exact descended_localization_kernel_eq_span_one_sub (R := A[f]) (S := C[f]) he hC

/-- Helper for Lemma 15.109.3: associated generators define the same principal ideal even without
any domain hypothesis. This is the stable rewrite used to replace the overlap numerator by the
transported idempotent generator. -/
lemma ideal_span_singleton_eq_of_associated
    {R : Type*} [CommRing R] {x y : R}
    (hxy : Associated x y) :
    Ideal.span ({x} : Set R) = Ideal.span ({y} : Set R) := by
  apply le_antisymm
  · -- Rewrite the left singleton generator through the associated right-side generator.
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_
    rcases Associated.symm hxy with ⟨u, hu⟩
    exact Ideal.mem_span_singleton'.mpr ⟨↑u, by simpa [mul_comm] using hu⟩
  · -- The reverse inclusion is the same argument with the original association data.
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_
    rcases hxy with ⟨u, hu⟩
    exact Ideal.mem_span_singleton'.mpr ⟨↑u, by simpa [mul_comm] using hu⟩

/-- Helper for Lemma 15.109.3: mapping the `i`-chart complementary principal ideal to the common
overlap ring turns it into the principal ideal generated by the transported complementary
idempotent. -/
lemma overlap_right_map_span_one_sub
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (i j : Fin r) :
    Ideal.map (IsLocalization.Away.awayToAwayRight (g i) (g j))
        (Ideal.span ({1 - e i} : Set A[g i])) =
      Ideal.span
        ({1 - IsLocalization.Away.awayToAwayRight (g i) (g j) (e i)} :
          Set A[g i * g j]) := by
  -- Normalize the mapped singleton generator under the explicit overlap map.
  rw [Ideal.map_span]
  simp

/-- Helper for Lemma 15.109.3: mapping the `i`-chart idempotent principal ideal to the common
overlap ring turns it into the principal ideal generated by the transported idempotent. -/
lemma overlap_right_map_span
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (i j : Fin r) :
    Ideal.map (IsLocalization.Away.awayToAwayRight (g i) (g j))
        (Ideal.span ({e i} : Set A[g i])) =
      Ideal.span
        ({IsLocalization.Away.awayToAwayRight (g i) (g j) (e i)} :
          Set A[g i * g j]) := by
  -- Normalize the mapped singleton generator under the explicit overlap map.
  rw [Ideal.map_span]
  simp

/-- Helper for Lemma 15.109.3: mapping the `j`-chart complementary principal ideal to the common
overlap ring turns it into the principal ideal generated by the transported complementary
idempotent. -/
lemma overlap_left_map_span_one_sub
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (i j : Fin r) :
    Ideal.map (IsLocalization.Away.awayToAwayLeft (g j) (g i))
        (Ideal.span ({1 - e j} : Set A[g j])) =
      Ideal.span
        ({1 - IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)} :
          Set A[g i * g j]) := by
  -- The left-overlap map normalizes in the same way by direct image-of-span simplification.
  rw [Ideal.map_span]
  simp

/-- Helper for Lemma 15.109.3: mapping the `j`-chart idempotent principal ideal to the common
overlap ring turns it into the principal ideal generated by the transported idempotent. -/
lemma overlap_left_map_span
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (i j : Fin r) :
    Ideal.map (IsLocalization.Away.awayToAwayLeft (g j) (g i))
        (Ideal.span ({e j} : Set A[g j])) =
      Ideal.span
        ({IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)} :
          Set A[g i * g j]) := by
  -- The left-overlap map normalizes the idempotent generator by direct image-of-span
  -- simplification.
  rw [Ideal.map_span]
  simp

/-- Helper for Lemma 15.109.3: an idempotent is orthogonal to its complementary factor on the
right. -/
lemma idempotent_mul_one_sub_eq_zero
    {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) :
    e * (1 - e) = 0 := by
  calc
    e * (1 - e) = e - e * e := by rw [mul_sub, mul_one]
    _ = e - e := by rw [he.eq]
    _ = 0 := sub_self e

/-- Helper for Lemma 15.109.3: an idempotent is orthogonal to its complementary factor on the
left. -/
lemma one_sub_mul_idempotent_eq_zero
    {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) :
    (1 - e) * e = 0 := by
  simpa [mul_comm] using idempotent_mul_one_sub_eq_zero he

/-- Helper for Lemma 15.109.3: the annihilator of the complementary idempotent ideal is the
principal ideal generated by the idempotent. -/
lemma annihilator_span_one_sub_of_idempotent
    {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) :
    (Ideal.span ({1 - e} : Set R)).annihilator = Ideal.span ({e} : Set R) := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_annihilator] at hx
    have hkill : x * (1 - e) = 0 := by
      exact hx (1 - e) (Ideal.subset_span (by simp))
    -- Decompose `x` into the two complementary idempotent pieces and kill the second one.
    have hxsplit : x = x * e + x * (1 - e) := by
      calc
        x = x * 1 := by rw [mul_one]
        _ = x * (e + (1 - e)) := by simp
        _ = x * e + x * (1 - e) := by rw [mul_add]
    have hxeq : x = x * e := by
      calc
        x = x * e + x * (1 - e) := hxsplit
        _ = x * e + 0 := by rw [hkill]
        _ = x * e := by simp
    rw [hxeq]
    exact Ideal.mem_span_singleton.mpr ⟨x, by rw [mul_comm]⟩
  · intro x hx
    rw [Submodule.mem_annihilator]
    rcases Ideal.mem_span_singleton.mp (by simpa using hx) with ⟨y, rfl⟩
    intro z hz
    rcases Ideal.mem_span_singleton.mp (by simpa using hz) with ⟨w, rfl⟩
    -- Both generators multiply to zero, so every product of their multiples vanishes.
    calc
      (e * y) • ((1 - e) * w) = y * w * (e * (1 - e)) := by
        simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = y * w * 0 := by rw [idempotent_mul_one_sub_eq_zero he]
      _ = 0 := by simp

/-- Helper for Lemma 15.109.3: once the two transported complementary ideals on a common overlap
are identified with the same kernel, the transported idempotent ideals agree there as well. -/
lemma overlap_local_complement_span_eq_of_kernel_eq
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i])
    (he : ∀ i : Fin r, IsIdempotentElem (e i))
    (i j : Fin r)
    (hker_right :
      RingHom.ker (algebraMap A[g i * g j] C[g i * g j]) =
        Ideal.map
          (IsLocalization.Away.awayToAwayRight (g i) (g j) : A[g i] →+* A[g i * g j])
          (Ideal.span ({1 - e i} : Set A[g i])))
    (hker_left :
      RingHom.ker (algebraMap A[g i * g j] C[g i * g j]) =
        Ideal.map
          (IsLocalization.Away.awayToAwayLeft (g j) (g i) : A[g j] →+* A[g i * g j])
          (Ideal.span ({1 - e j} : Set A[g j]))) :
    Ideal.map
        (IsLocalization.Away.awayToAwayRight (g i) (g j) : A[g i] →+* A[g i * g j])
        (Ideal.span ({e i} : Set A[g i])) =
      Ideal.map
        (IsLocalization.Away.awayToAwayLeft (g j) (g i) : A[g j] →+* A[g i * g j])
        (Ideal.span ({e j} : Set A[g j])) := by
  let φright : A[g i] →+* A[g i * g j] :=
    IsLocalization.Away.awayToAwayRight (g i) (g j)
  let φleft : A[g j] →+* A[g i * g j] :=
    IsLocalization.Away.awayToAwayLeft (g j) (g i)
  have hright_idem :
      IsIdempotentElem (φright (e i)) :=
    (he i).map φright
  have hleft_idem :
      IsIdempotentElem (φleft (e j)) :=
    (he j).map φleft
  -- Proof comment: convert both transported idempotent ideals into annihilators of their
  -- complementary transported ideals, replace those complementary ideals by the common kernel, and
  -- then read the resulting annihilator equality back as equality of the idempotent ideals.
  calc
    Ideal.map φright (Ideal.span ({e i} : Set A[g i])) =
      Ideal.span ({φright (e i)} : Set A[g i * g j]) := by
      rw [overlap_right_map_span]
    _ =
        (Ideal.span ({1 - φright (e i)} : Set A[g i * g j])).annihilator := by
      symm
      exact annihilator_span_one_sub_of_idempotent hright_idem
    _ = (Ideal.map φright (Ideal.span ({1 - e i} : Set A[g i]))).annihilator := by
      rw [overlap_right_map_span_one_sub]
    _ = (RingHom.ker (algebraMap A[g i * g j] C[g i * g j])).annihilator := by
      rw [hker_right.symm]
    _ = (Ideal.map φleft (Ideal.span ({1 - e j} : Set A[g j]))).annihilator := by
      rw [hker_left]
    _ = (Ideal.span ({1 - φleft (e j)} : Set A[g i * g j])).annihilator := by
      rw [overlap_left_map_span_one_sub]
    _ = Ideal.span ({φleft (e j)} : Set A[g i * g j]) := by
      exact annihilator_span_one_sub_of_idempotent hleft_idem
    _ = Ideal.map φleft (Ideal.span ({e j} : Set A[g j])) := by
      rw [overlap_left_map_span]

/-- Helper for Lemma 15.109.3: if `f` lies in the ideal spanned by a family `g`, then after
localizing away from `f` the images of `g` already span the unit ideal. -/
lemma localized_family_spans_top_of_mem_span
    {ι : Type*} (g : ι → A) {f : A}
    (hf : f ∈ Ideal.span (Set.range g)) :
    Ideal.span (Set.range fun j : ι ↦ algebraMap A A[f] (g j)) = ⊤ := by
  let J : Ideal A[f] := Ideal.span (Set.range fun j : ι ↦ algebraMap A A[f] (g j))
  have hrange :
      (algebraMap A A[f]) '' Set.range g = Set.range fun j : ι ↦ algebraMap A A[f] (g j) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g i, ⟨i, rfl⟩, rfl⟩
  have hspan_image :
      J = Ideal.map (algebraMap A A[f]) (Ideal.span (Set.range g)) := by
    -- Rewrite the localized span as the image of the source span under the localization map.
    rw [Ideal.map_span, hrange]
  have hf_mem : algebraMap A A[f] f ∈ J := by
    -- Membership in the source span transports to membership in its localized image ideal.
    rw [hspan_image]
    exact Ideal.mem_map_of_mem (algebraMap A A[f]) hf
  have hf_unit : IsUnit (algebraMap A A[f] f) := by
    -- The localized image of the inverted element is a unit by construction.
    simpa using (IsLocalization.Away.algebraMap_isUnit f)
  exact J.eq_top_of_isUnit_mem hf_mem hf_unit

/-- Helper for Lemma 15.109.3: in the away-localization at one chosen generator, the images of the
whole generator family already span the unit ideal because the distinguished generator becomes a
unit. -/
lemma localized_generator_family_spans_top
    {r : ℕ} (g : Fin r → A) (i : Fin r) :
    Ideal.span (Set.range fun j : Fin r ↦ algebraMap A A[g i] (g j)) = ⊤ := by
  -- Apply the span-top criterion to the distinguished generator `g i`.
  exact localized_family_spans_top_of_mem_span (A := A) g
    (Ideal.subset_span (Set.mem_range_self i))

/-- Helper for Lemma 15.109.3: the infimum ideal chosen for the global complement is contained in
each of its defining local comaps. -/
lemma global_complement_ideal_le_local_comap
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (i : Fin r) :
    (⨅ k : Fin r, Ideal.comap (algebraMap A A[g k]) (Ideal.span ({e k} : Set A[g k]))) ≤
      Ideal.comap (algebraMap A A[g i]) (Ideal.span ({e i} : Set A[g i])) := by
  -- This is the direct `i`-th projection from the infimum defining the global ideal.
  exact iInf_le _ i

/-- Helper for Lemma 15.109.3: after mapping the descended global complement ideal to the `i`-th
generator localization, it is automatically contained in the local principal complement
`Ideal.span ({e i})`. -/
lemma map_global_complement_ideal_le_local_span
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (i : Fin r) :
    Ideal.map (algebraMap A A[g i])
        (⨅ k : Fin r, Ideal.comap (algebraMap A A[g k]) (Ideal.span ({e k} : Set A[g k]))) ≤
      Ideal.span ({e i} : Set A[g i]) := by
  -- Push the infimum ideal forward and keep only the defining `i`-th local constraint.
  refine Ideal.map_le_iff_le_comap.mpr ?_
  exact global_complement_ideal_le_local_comap (A := A) g e i

/-- Helper for Lemma 15.109.3: finite intersections of submodules commute with away-localization.
This isolates the recurring transport normalization needed for the descended ideal `J`. -/
lemma localized'_iInf_fin_away
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] {x : R} :
    ∀ {n : ℕ} (K : Fin n → Submodule R N),
      Submodule.localized'
          (Localization.Away x)
          (Submonoid.powers x)
          (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
          (⨅ i, K i) =
        ⨅ i,
          Submodule.localized'
            (Localization.Away x)
            (Submonoid.powers x)
            (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
            (K i) := by
  intro n
  induction n with
  | zero =>
      intro K
      rw [show (⨅ i : Fin 0, K i) = ⊤ by simp, Submodule.localized'_top]
      rw [show (⨅ i : Fin 0,
          Submodule.localized'
            (Localization.Away x)
            (Submonoid.powers x)
            (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
            (K i)) = ⊤ by simp]
  | succ n ih =>
      intro K
      have hiInf :
          (⨅ i : Fin (n + 1), K i) = K 0 ⊓ ⨅ i : Fin n, K i.succ := by
        ext y
        simp [Fin.forall_fin_succ]
      have hiInf' :
          (⨅ i : Fin (n + 1),
              Submodule.localized'
                (Localization.Away x)
                (Submonoid.powers x)
                (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
                (K i)) =
            Submodule.localized'
                (Localization.Away x)
                (Submonoid.powers x)
                (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
                (K 0) ⊓
              ⨅ i : Fin n,
                Submodule.localized'
                  (Localization.Away x)
                  (Submonoid.powers x)
                  (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
                  (K i.succ) := by
        ext y
        simp [Fin.forall_fin_succ]
      -- Proof comment: rewrite the finite intersection into head-plus-tail form, localize the
      -- binary infimum once, and then invoke the induction hypothesis on the tail.
      rw [hiInf, Submodule.localized'_inf, ih, hiInf']

/-- Helper for Lemma 15.109.3: membership in the away-localization of a finite intersection is
equivalent to simultaneous membership in the localized factors. This is the proposition-level form
used later to analyze localized descended denominators chartwise. -/
lemma mem_localized'_iInf_fin_away_iff
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] {x : R}
    {n : ℕ} (K : Fin n → Submodule R N) (y : LocalizedModule.Away x N) :
    y ∈ Submodule.localized'
        (Localization.Away x)
        (Submonoid.powers x)
        (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
        (⨅ i, K i) ↔
      ∀ i : Fin n,
        y ∈ Submodule.localized'
          (Localization.Away x)
          (Submonoid.powers x)
          (LocalizedModule.mkLinearMap (Submonoid.powers x) N)
          (K i) := by
  -- Proof comment: expand the previously proved finite-inf equality at the level of element
  -- membership; the right-hand side then unfolds to pointwise membership in each factor.
  simpa using congrArg
    (fun M : Submodule (Localization.Away x) (LocalizedModule.Away x N) ↦ y ∈ M)
    (localized'_iInf_fin_away (R := R) (N := N) (x := x) K)

/-- Helper for Lemma 15.109.3: if a quotient of a submodule by one of its submodules is
subsingleton, then that submodule is already the whole source. -/
lemma submodule_eq_top_of_subsingleton_quotient
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {P : Submodule R M} {Q : Submodule R P}
    (hsub : Subsingleton (P ⧸ Q)) :
    Q = ⊤ := by
  letI := hsub
  apply le_antisymm le_top
  intro x hx
  -- Every quotient class is zero in a subsingleton quotient, so the source element already lies
  -- in the denominator submodule.
  have hxzero : (Submodule.Quotient.mk x : P ⧸ Q) = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero Q).mp hxzero

/-- Helper for Lemma 15.109.3: once the quotient of a local ideal by the descended denominator is
subsingleton, the descended denominator must equal that local ideal. -/
lemma ideal_eq_of_subsingleton_submodule_quotient
    {R : Type*} [CommRing R] {I J : Ideal R}
    (hJI : J ≤ I)
    (hsub : Subsingleton (I ⧸ Submodule.comap I.subtype J)) :
    I = J := by
  have htop :
      Submodule.comap I.subtype J = ⊤ :=
    submodule_eq_top_of_subsingleton_quotient
      (P := I) (Q := Submodule.comap I.subtype J) hsub
  apply le_antisymm ?_ hJI
  intro x hx
  -- Read the equality `Submodule.comap I.subtype J = ⊤` back as membership of `x` in `J`.
  have htop_mem : (⟨x, hx⟩ : I) ∈ (⊤ : Submodule R I) := by
    simp
  have hxmem : (⟨x, hx⟩ : I) ∈ Submodule.comap I.subtype J := by
    rw [← htop] at htop_mem
    exact htop_mem
  simpa using hxmem

/-- Helper for Lemma 15.109.3: if, on a fixed generator chart `A[g i]`, the quotient of the
complementary principal ideal by the descended global denominator becomes trivial after localizing
at every image of the chosen generator family, then the descended denominator already equals that
principal ideal on the whole chart. -/
lemma map_global_complement_ideal_eq_local_span_of_localized_quotient_subsingleton
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (J : Ideal A) (i : Fin r)
    (hJ :
      Ideal.map (algebraMap A A[g i]) J ≤ Ideal.span ({e i} : Set A[g i]))
    (hlocal :
      ∀ j : Fin r,
        Subsingleton
          (LocalizedModule.Away (algebraMap A A[g i] (g j))
            (Ideal.span ({e i} : Set A[g i]) ⧸
              Submodule.comap (Ideal.span ({e i} : Set A[g i])).subtype
                (Ideal.map (algebraMap A A[g i]) J)))) :
    Ideal.map (algebraMap A A[g i]) J = Ideal.span ({e i} : Set A[g i]) := by
  classical
  -- Apply Lemma `10.23.2` on the `i`-th chart: the localized quotient is trivial on the
  -- generator cover, so the quotient itself is trivial.
  have hsub :
      Subsingleton
        (Ideal.span ({e i} : Set A[g i]) ⧸
          Submodule.comap (Ideal.span ({e i} : Set A[g i])).subtype
            (Ideal.map (algebraMap A A[g i]) J)) := by
    let sLocal : Finset A[g i] :=
      Finset.univ.image fun j : Fin r ↦ algebraMap A A[g i] (g j)
    apply module_subsingleton_of_localizationAway
      (R := A[g i])
      (M := Ideal.span ({e i} : Set A[g i]) ⧸
        Submodule.comap (Ideal.span ({e i} : Set A[g i])).subtype
          (Ideal.map (algebraMap A A[g i]) J))
      (s := sLocal)
    · -- The chosen generators still cover after localizing at `g i`.
      simpa [sLocal] using localized_generator_family_spans_top (A := A) g i
    · intro x
      have hx :
          x.1 ∈ Finset.univ.image fun j : Fin r ↦ algebraMap A A[g i] (g j) := by
        simpa [sLocal] using x.property
      rcases Finset.mem_image.mp hx with ⟨j, _, hjx⟩
      -- Each localized chart quotient is trivial by hypothesis.
      simpa [hjx] using hlocal j
  -- A subsingleton quotient of a submodule forces the denominator to equal the source ideal.
  symm
  exact ideal_eq_of_subsingleton_submodule_quotient
    (I := Ideal.span ({e i} : Set A[g i]))
    (J := Ideal.map (algebraMap A A[g i]) J) hJ hsub

/-- Helper for Lemma 15.109.3: if the localized denominator inside a quotient already fills the
localized source ideal, then the localized quotient is trivial. -/
lemma localized_ideal_quotient_subsingleton_of_localized_eq_top
    {R : Type*} [CommRing R] {x : R} {P Q : Ideal R}
    (hlocalized :
      Submodule.localized (p := Submonoid.powers x) (Submodule.comap P.subtype Q) = ⊤) :
    Subsingleton (LocalizedModule.Away x (P ⧸ Submodule.comap P.subtype Q)) := by
  let e :
      (LocalizedModule.Away x P ⧸
        Submodule.localized (p := Submonoid.powers x) (Submodule.comap P.subtype Q)) ≃ₗ[
          Localization.Away x] LocalizedModule.Away x (P ⧸ Submodule.comap P.subtype Q) :=
    localizedQuotientEquiv (Submonoid.powers x) (Submodule.comap P.subtype Q)
  have hquot :
      Subsingleton
        (LocalizedModule.Away x P ⧸
          Submodule.localized (p := Submonoid.powers x) (Submodule.comap P.subtype Q)) := by
    -- Once the localized denominator is all of the localized source ideal, the localized quotient
    -- is the quotient by `⊤`, hence subsingleton.
    rw [hlocalized]
    infer_instance
  -- Transport the quotient-by-`⊤` subsingleton structure across `localizedQuotientEquiv`.
  letI :
      Subsingleton
        (LocalizedModule.Away x P ⧸
          Submodule.localized (p := Submonoid.powers x) (Submodule.comap P.subtype Q)) := hquot
  exact e.symm.toEquiv.subsingleton

/-- Helper for Lemma 15.109.3: on a fixed generator chart, it suffices to show that every
localized descended denominator is already the whole localized complementary ideal. -/
lemma map_global_complement_ideal_eq_local_span_of_localized_eq_top
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) (J : Ideal A) (i : Fin r)
    (hJ :
      Ideal.map (algebraMap A A[g i]) J ≤ Ideal.span ({e i} : Set A[g i]))
    (hlocal :
      ∀ j : Fin r,
        Submodule.localized
            (p := Submonoid.powers (algebraMap A A[g i] (g j)))
            (Submodule.comap (Ideal.span ({e i} : Set A[g i])).subtype
              (Ideal.map (algebraMap A A[g i]) J)) = ⊤) :
    Ideal.map (algebraMap A A[g i]) J = Ideal.span ({e i} : Set A[g i]) := by
  -- Convert the localized `= ⊤` hypotheses into the quotient-subsingleton hypotheses expected by
  -- the previously established chartwise descent lemma.
  refine
    map_global_complement_ideal_eq_local_span_of_localized_quotient_subsingleton
      (A := A) g e J i hJ ?_
  intro j
  exact localized_ideal_quotient_subsingleton_of_localized_eq_top (hlocal j)

/-- Helper for Lemma 15.109.3: finitely many localized idempotents admit a common power-clearance
in the source ring. The resulting numerators satisfy both the expected localization identity and
the exact source-ring relation `a_i^2 = g_i^n a_i`. -/
lemma exists_common_power_idempotent_numerators
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i])
    (he : ∀ i : Fin r, IsIdempotentElem (e i)) :
    ∃ n : ℕ, ∃ a : Fin r → A,
      (∀ i : Fin r,
        algebraMap A A[g i] (a i) =
          (algebraMap A A[g i] (g i)) ^ n * e i) ∧
      (∀ i : Fin r, a i ^ 2 = g i ^ n * a i) := by
  classical
  have hsurj :
      ∀ i : Fin r, ∃ n : ℕ, ∃ b : A,
        algebraMap A A[g i] b = e i * (algebraMap A A[g i] (g i)) ^ n := by
    intro i
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (g i) (e i)
    exact ⟨n, b, hb.symm⟩
  choose n₀ b hb using hsurj
  have hclear :
      ∀ i : Fin r, ∃ m : ℕ,
        g i ^ m * (b i ^ 2 - g i ^ n₀ i * b i) = 0 := by
    intro i
    have hzero :
        algebraMap A A[g i] (b i ^ 2 - g i ^ n₀ i * b i) = 0 := by
      -- The chosen numerator represents an idempotent localization class, so its defect from the
      -- source relation vanishes after localizing away from `g i`.
      rw [map_sub, map_mul, map_pow, hb i]
      apply sub_eq_zero.mpr
      calc
        (e i * (algebraMap A A[g i] (g i)) ^ n₀ i) ^ 2
            = e i * (e i * ((algebraMap A A[g i] (g i)) ^ n₀ i *
                (algebraMap A A[g i] (g i)) ^ n₀ i)) := by
                  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        _ = e i * ((algebraMap A A[g i] (g i)) ^ n₀ i *
              (algebraMap A A[g i] (g i)) ^ n₀ i) := by
              simpa [mul_assoc] using congrArg
                (fun t ↦ t * ((algebraMap A A[g i] (g i)) ^ n₀ i *
                  (algebraMap A A[g i] (g i)) ^ n₀ i))
                (he i).eq
        _ = algebraMap A A[g i] (g i ^ n₀ i) *
              (e i * (algebraMap A A[g i] (g i)) ^ n₀ i) := by
              simp [map_pow, pow_two, mul_assoc, mul_left_comm, mul_comm]
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (g i)) A[g i]
        (b i ^ 2 - g i ^ n₀ i * b i)).mp hzero
    rcases s with ⟨s, hs_mem⟩
    rcases hs_mem with ⟨m, rfl⟩
    exact ⟨m, hs⟩
  choose m hm using hclear
  let N : Fin r → ℕ := fun i ↦ n₀ i + m i
  let n : ℕ := Finset.univ.sup N
  let a₀ : Fin r → A := fun i ↦ g i ^ m i * b i
  let a : Fin r → A := fun i ↦ g i ^ (n - N i) * a₀ i
  refine ⟨n, a, ?_, ?_⟩
  · intro i
    have hNi : N i ≤ n := Finset.le_sup (Finset.mem_univ i)
    have ha₀ :
        algebraMap A A[g i] (a₀ i) =
          (algebraMap A A[g i] (g i)) ^ N i * e i := by
      -- First clear the local denominator, then absorb the extra power into a single exponent.
      rw [show a₀ i = g i ^ m i * b i by rfl, map_mul, map_pow, hb i]
      simp [N, pow_add, mul_assoc, mul_left_comm, mul_comm]
    have hpow_local :
        (algebraMap A A[g i] (g i)) ^ N i *
            (algebraMap A A[g i] (g i)) ^ (n - N i) =
          (algebraMap A A[g i] (g i)) ^ n := by
      calc
        (algebraMap A A[g i] (g i)) ^ N i *
            (algebraMap A A[g i] (g i)) ^ (n - N i)
            = (algebraMap A A[g i] (g i)) ^ (N i + (n - N i)) := by
                rw [← pow_add]
        _ = (algebraMap A A[g i] (g i)) ^ n := by
              rw [Nat.add_sub_of_le hNi]
    calc
      algebraMap A A[g i] (a i)
          = (algebraMap A A[g i] (g i)) ^ (n - N i) * algebraMap A A[g i] (a₀ i) := by
              rw [show a i = g i ^ (n - N i) * a₀ i by rfl, map_mul, map_pow]
      _ = (algebraMap A A[g i] (g i)) ^ (n - N i) *
            ((algebraMap A A[g i] (g i)) ^ N i * e i) := by rw [ha₀]
      _ = (algebraMap A A[g i] (g i)) ^ n * e i := by
            calc
              (algebraMap A A[g i] (g i)) ^ (n - N i) *
                  ((algebraMap A A[g i] (g i)) ^ N i * e i)
                  = ((algebraMap A A[g i] (g i)) ^ N i *
                      (algebraMap A A[g i] (g i)) ^ (n - N i)) * e i := by
                        simp [mul_assoc, mul_left_comm, mul_comm]
              _ = (algebraMap A A[g i] (g i)) ^ n * e i := by rw [hpow_local]
  · intro i
    have hNi : N i ≤ n := Finset.le_sup (Finset.mem_univ i)
    have hpow_source :
        g i ^ N i * g i ^ (n - N i) = g i ^ n := by
      calc
        g i ^ N i * g i ^ (n - N i) = g i ^ (N i + (n - N i)) := by
          rw [← pow_add]
        _ = g i ^ n := by rw [Nat.add_sub_of_le hNi]
    have ha₀_sq :
        a₀ i ^ 2 = g i ^ N i * a₀ i := by
      have hm' : g i ^ m i * (b i ^ 2 - g i ^ n₀ i * b i) = 0 := hm i
      have hm'' : g i ^ m i * b i ^ 2 = g i ^ (m i + n₀ i) * b i := by
        apply sub_eq_zero.mp
        simpa [mul_sub, mul_assoc, pow_add, mul_left_comm, mul_comm] using hm'
      -- Rewrite the squared numerator using the exact source-ring denominator-clearing equation.
      calc
        a₀ i ^ 2 = (g i ^ m i * b i) * (g i ^ m i * b i) := by
          rw [show a₀ i = g i ^ m i * b i by rfl, pow_two]
        _ = (g i ^ m i * b i ^ 2) * g i ^ m i := by
              simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        _ = (g i ^ (m i + n₀ i) * b i) * g i ^ m i := by rw [hm'']
        _ = g i ^ N i * a₀ i := by
              simp [N, a₀, pow_add, mul_assoc, mul_left_comm, mul_comm]
    -- Inflate the chartwise relation to the global exponent `n`.
    calc
      a i ^ 2 = (g i ^ (n - N i) * a₀ i) * (g i ^ (n - N i) * a₀ i) := by
        rw [show a i = g i ^ (n - N i) * a₀ i by rfl, pow_two]
      _ = (g i ^ (n - N i) * a₀ i ^ 2) * g i ^ (n - N i) := by
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (g i ^ (n - N i) * (g i ^ N i * a₀ i)) * g i ^ (n - N i) := by rw [ha₀_sq]
      _ = g i ^ n * a i := by
            calc
              (g i ^ (n - N i) * (g i ^ N i * a₀ i)) * g i ^ (n - N i)
                  = ((g i ^ N i * g i ^ (n - N i)) * a₀ i) * g i ^ (n - N i) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
              _ = (g i ^ n * a₀ i) * g i ^ (n - N i) := by rw [hpow_source]
              _ = g i ^ n * a i := by
                    simp [a, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 15.109.3: once the source numerators satisfy
`a_i^2 = g_i^n a_i`, every higher power of `a_i` collapses to a corresponding power of `g_i`
times `a_i`. This is the source rewrite `a_i^(m + 1) = g_i^(nm) a_i`. -/
lemma numerator_pow_succ_eq_of_square_relation
    {r : ℕ} (g : Fin r → A) {n : ℕ} {a : Fin r → A}
    (ha_sq : ∀ i : Fin r, a i ^ 2 = g i ^ n * a i) :
    ∀ i : Fin r, ∀ m : ℕ, a i ^ (m + 1) = g i ^ (n * m) * a i := by
  intro i m
  induction m with
  | zero =>
      -- Proof comment: the base case is the tautological identity `a_i = g_i^0 a_i`.
      simp
  | succ m ih =>
      -- Proof comment: peel off one copy of `a_i`, use the induction hypothesis on the remaining
      -- factor, and then rewrite `a_i^2` through the idempotent numerator relation.
      calc
        a i ^ (m.succ + 1) = a i ^ (m + 1) * a i := by
          rw [pow_succ]
        _ = (g i ^ (n * m) * a i) * a i := by
          rw [ih]
        _ = g i ^ (n * m) * (a i ^ 2) := by
          rw [pow_two]
          ring_nf
        _ = g i ^ (n * m) * (g i ^ n * a i) := by
          rw [ha_sq i]
        _ = g i ^ (n * m.succ) * a i := by
          rw [Nat.mul_succ, pow_add]
          ring_nf

/-- Helper for Lemma 15.109.3: after transporting the cleared numerators to the common overlap,
the source overlap difference `g_j^n a_i - g_i^n a_j` already vanishes in the target overlap.
This is the exact overlap-zero step in the textbook argument before denominator clearing. -/
lemma overlap_cleared_numerator_difference_maps_to_zero
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i])
    {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i)
    (he : ∀ i : Fin r, IsIdempotentElem (e i))
    (hC : ∀ i : Fin r, IsLocalization.Away (e i) C[g i]) :
    ∀ i j : Fin r,
      algebraMap A[g i * g j] C[g i * g j]
        (algebraMap A A[g i * g j] (g j ^ n * a i - g i ^ n * a j)) = 0 := by
  -- TODO: transport the chartwise numerator identities to the common overlap and use
  -- `overlap_right_idempotent_maps_to_one` / `overlap_left_idempotent_maps_to_one` to rewrite both
  -- terms to the same mixed monomial in `g_i` and `g_j`.
  sorry

/-- Helper for Lemma 15.109.3: after the overlap-zero step and the second denominator-clearing
adjustment from the source proof, the cleared numerators already satisfy the pairwise divisibility
relation `g_i^n a_j ∈ (a_i)`. This is the packaged numerator layer needed by the main theorem. -/
lemma exists_common_power_idempotent_numerators_with_pairwise
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i])
    (he : ∀ i : Fin r, IsIdempotentElem (e i))
    (hC : ∀ i : Fin r, IsLocalization.Away (e i) C[g i]) :
    ∃ n : ℕ, ∃ a : Fin r → A,
      (∀ i : Fin r,
        algebraMap A A[g i] (a i) =
          (algebraMap A A[g i] (g i)) ^ n * e i) ∧
      (∀ i : Fin r, a i ^ 2 = g i ^ n * a i) ∧
      (∀ i j : Fin r, g i ^ n * a j ∈ Ideal.span ({a i} : Set A)) := by
  -- TODO: start from `exists_common_power_idempotent_numerators`, use
  -- `overlap_cleared_numerator_difference_maps_to_zero` plus two denominator-clearing steps on the
  -- common overlap, and package the final global adjustment so the returned numerators already
  -- satisfy the source proof's pairwise divisibility relation.
  sorry

/-- Helper for Lemma 15.109.3: the distinguished numerator `a i` already forces the local
idempotent ideal on the `i`-chart to lie in the localized numerator ideal. -/
lemma local_idempotent_span_le_map_numerator_ideal
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i) :
    ∀ i : Fin r,
      Ideal.span ({e i} : Set A[g i]) ≤
        Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a)) := by
  intro i
  have hai_mem :
      algebraMap A A[g i] (a i) ∈
        Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a)) := by
    -- The distinguished numerator belongs to the source numerator ideal by construction.
    exact Ideal.mem_map_of_mem (algebraMap A A[g i])
      (Ideal.subset_span (Set.mem_range_self i))
  have hspan_ai :
      Ideal.span ({algebraMap A A[g i] (a i)} : Set A[g i]) ≤
        Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a)) := by
    -- Passing from the generator to its principal ideal is the canonical singleton-span step.
    exact (Ideal.span_singleton_le_iff_mem _).2 hai_mem
  have he_mem :
      e i ∈ Ideal.span ({algebraMap A A[g i] (a i)} : Set A[g i]) := by
    -- The chosen numerator differs from `e i` by a unit power of the inverted generator `g i`.
    rw [ha i]
    have hu : IsUnit ((algebraMap A A[g i] (g i)) ^ n) := by
      simpa using (IsLocalization.Away.algebraMap_isUnit (g i)).pow n
    rcases hu with ⟨u, hu⟩
    rw [← hu]
    refine Ideal.mem_span_singleton.mpr ⟨↑u⁻¹, ?_⟩
    calc
      e i = (((↑u : A[g i]) * ↑u⁻¹) : A[g i]) * e i := by simp
      _ = ↑u * (↑u⁻¹ * e i) := by
        rw [mul_assoc]
      _ = ↑u * (e i * ↑u⁻¹) := by
        rw [mul_comm (↑u⁻¹) (e i)]
      _ = ↑u * e i * ↑u⁻¹ := by
        rw [mul_assoc]
  -- Push the idempotent generator through the distinguished numerator and then into the mapped
  -- global numerator ideal.
  exact ((Ideal.span_singleton_le_iff_mem _).2 he_mem).trans hspan_ai

/-- Helper for Lemma 15.109.3: if a unit multiple of an element lies in an ideal, then the
element itself already lies in that ideal. This is the basic local cancellation step used after
inverting one chosen generator. -/
lemma ideal_mem_of_isUnit_mul_mem
    {R : Type*} [CommRing R] {I : Ideal R} {u x : R}
    (hu : IsUnit u) (hx : u * x ∈ I) :
    x ∈ I := by
  rcases hu with ⟨u', rfl⟩
  -- Multiply by the inverse unit on the left to cancel the unit factor inside the ideal.
  have hx' : (↑(u'⁻¹) : R) * (↑u' * x) ∈ I := I.mul_mem_left _ hx
  simpa [mul_assoc] using hx'

/-- Helper for Lemma 15.109.3: once the source-style pairwise divisibility
`g_i^n a_j ∈ (a_i)` is known, localizing at `g i` collapses the whole numerator ideal to the
principal ideal generated by `a i`. -/
lemma localized_map_numerator_ideal_eq_span_numerator_of_pairwise
    {r : ℕ} (g : Fin r → A) {n : ℕ} {a : Fin r → A}
    (hpair :
      ∀ i j : Fin r, g i ^ n * a j ∈ Ideal.span ({a i} : Set A)) :
    ∀ i : Fin r,
      Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a)) =
        Ideal.span ({algebraMap A A[g i] (a i)} : Set A[g i]) := by
  intro i
  apply le_antisymm
  · rw [Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨y, ⟨j, rfl⟩, rfl⟩
    have hmap :
        algebraMap A A[g i] (g i ^ n * a j) ∈
          Ideal.map (algebraMap A A[g i]) (Ideal.span ({a i} : Set A)) := by
      -- Transport the source divisibility relation for `a j` into the localized chart.
      exact Ideal.mem_map_of_mem (algebraMap A A[g i]) (hpair i j)
    have hmap_span :
        Ideal.map (algebraMap A A[g i]) (Ideal.span ({a i} : Set A)) =
          Ideal.span ({algebraMap A A[g i] (a i)} : Set A[g i]) := by
      -- Normalize the image of the principal source ideal generated by `a i`.
      rw [Ideal.map_span]
      simp
    have hu :
        IsUnit (algebraMap A A[g i] (g i ^ n)) := by
      -- The inverted generator remains a unit after any power on the `i`-chart.
      simpa [map_pow] using (IsLocalization.Away.algebraMap_isUnit (g i)).pow n
    have hmul :
        algebraMap A A[g i] (g i ^ n) * algebraMap A A[g i] (a j) ∈
          Ideal.span ({algebraMap A A[g i] (a i)} : Set A[g i]) := by
      simpa [hmap_span, map_mul, map_pow] using hmap
    -- Cancel the unit power of `g i` to recover membership of `a j` itself.
    exact ideal_mem_of_isUnit_mul_mem hu hmul
  · have hai_mem :
        algebraMap A A[g i] (a i) ∈
          Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a)) := by
      -- The distinguished numerator is one of the global generators of `J`.
      exact Ideal.mem_map_of_mem (algebraMap A A[g i])
        (Ideal.subset_span (Set.mem_range_self i))
    exact (Ideal.span_singleton_le_iff_mem _).2 hai_mem

/-- Helper for Lemma 15.109.3: on the `i`-chart, the distinguished numerator `a i` and the local
idempotent `e i` generate the same principal ideal because they differ by a unit power of `g i`. -/
lemma local_numerator_span_eq_idempotent_span
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i) :
    ∀ i : Fin r,
      Ideal.span ({algebraMap A A[g i] (a i)} : Set A[g i]) =
        Ideal.span ({e i} : Set A[g i]) := by
  intro i
  have hu : IsUnit ((algebraMap A A[g i] (g i)) ^ n) := by
    -- The defining factor relating `a i` and `e i` is a unit on the localization chart.
    simpa using (IsLocalization.Away.algebraMap_isUnit (g i)).pow n
  rcases hu with ⟨u, hu⟩
  have hassoc :
      Associated (algebraMap A A[g i] (a i)) (e i) := by
    -- Rewrite the localized numerator as a unit multiple of the local idempotent.
    refine ⟨u⁻¹, ?_⟩
    calc
      algebraMap A A[g i] (a i) * ↑(u⁻¹)
          = (((algebraMap A A[g i] (g i)) ^ n) * e i) * ↑(u⁻¹) := by rw [ha i]
      _ = ((↑u : A[g i]) * e i) * ↑(u⁻¹) := by rw [hu]
      _ = ↑u * (↑(u⁻¹) * e i) := by simp [mul_assoc, mul_left_comm, mul_comm]
      _ = (↑u * ↑(u⁻¹) : A[g i]) * e i := by rw [mul_assoc]
      _ = e i := by simp
  exact ideal_span_singleton_eq_of_associated hassoc

/-- Helper for Lemma 15.109.3: after the source proof produces the pairwise divisibility
relations among the numerators, the localized image of the global numerator ideal is exactly the
idempotent ideal on each generator chart. -/
lemma local_numerator_ideal_eq_idempotent_span_of_pairwise
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i)
    (hpair :
      ∀ i j : Fin r, g i ^ n * a j ∈ Ideal.span ({a i} : Set A)) :
    ∀ i : Fin r,
      Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a)) =
        Ideal.span ({e i} : Set A[g i]) := by
  intro i
  -- First identify the localized global numerator ideal with the principal ideal of `a i`,
  -- then rewrite that generator to the local idempotent.
  calc
    Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a)) =
      Ideal.span ({algebraMap A A[g i] (a i)} : Set A[g i]) := by
        exact localized_map_numerator_ideal_eq_span_numerator_of_pairwise (A := A) g hpair i
    _ = Ideal.span ({e i} : Set A[g i]) := by
        exact local_numerator_span_eq_idempotent_span (A := A) g e ha i

/-- Helper for Lemma 15.109.3: on the common overlap `A[g_i g_j]`, the cleared numerator `a j`
is a unit multiple of the idempotent transported from the `j`-chart. -/
lemma overlap_numerator_eq_unit_mul_left_idempotent
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i) :
    ∀ i j : Fin r,
      ∃ u : Units A[g i * g j],
        algebraMap A A[g i * g j] (a j) =
          ↑u * IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j) := by
  intro i j
  let φleft : A[g j] →+* A[g i * g j] :=
    IsLocalization.Away.awayToAwayLeft (g j) (g i)
  have hgj_unit : IsUnit (φleft (algebraMap A A[g j] (g j))) := by
    -- The overlap map preserves the distinguished unit coming from the `j`-chart localization.
    exact (IsLocalization.Away.algebraMap_isUnit (g j)).map φleft
  rcases hgj_unit with ⟨u, hu⟩
  refine ⟨u ^ n, ?_⟩
  -- Proof comment: transport the defining identity for `a j` from the `j`-chart to the common
  -- overlap and then rewrite the `g j`-power as the chosen unit power.
  calc
    algebraMap A A[g i * g j] (a j)
        = φleft (algebraMap A A[g j] (a j)) := by
            simpa [φleft] using
              (overlap_left_algebraMap_eq (x := g i) (y := g j) (a := a j)).symm
    _ = φleft ((algebraMap A A[g j] (g j)) ^ n * e j) := by rw [ha j]
    _ = φleft (algebraMap A A[g j] (g j)) ^ n * φleft (e j) := by
          rw [map_mul, map_pow]
    _ = (↑u : A[g i * g j]) ^ n * φleft (e j) := by rw [hu]
    _ = ↑(u ^ n) * IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j) := by
          simp [φleft]

/-- Helper for Lemma 15.109.3: on the common overlap, the cleared numerator `a j` is associated to
the idempotent transported from the `j`-chart. This is the canonical denominator-change bridge
needed later for source-faithful overlap descent. -/
lemma overlap_numerator_associated_left_idempotent
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i) :
    ∀ i j : Fin r,
      Associated
        (algebraMap A A[g i * g j] (a j))
        (IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)) := by
  intro i j
  rcases overlap_numerator_eq_unit_mul_left_idempotent (A := A) g e ha i j with ⟨u, hu⟩
  -- Proof comment: the overlap numerator equals a unit multiple of the transported idempotent, so
  -- the two generators are associated.
  refine ⟨u⁻¹, ?_⟩
  calc
    algebraMap A A[g i * g j] (a j) * ↑(u⁻¹)
        = (↑u * IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)) * ↑(u⁻¹) := by
              rw [hu]
    _ = (↑u * ↑(u⁻¹)) *
          IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j) := by
          simp

/-- Helper for Lemma 15.109.3: transporting the `j`-chart away-localization across the common
overlap identifies `C[g_i g_j]` as the away-localization of `A[g_i g_j]` at the idempotent
coming from the `j`-chart. This is the exact owner-level overlap transport used by the source
proof before changing generators from the idempotent to the cleared numerator. -/
lemma overlap_transport_away_of_chart_idempotent
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i])
    (hC : ∀ i : Fin r, IsLocalization.Away (e i) C[g i]) :
    ∀ i j : Fin r,
      IsLocalization.Away
        (IsLocalization.Away.awayToAwayLeft (P := A[g i * g j]) (g j) (g i) (e j))
        C[g i * g j] := by
  -- TODO: instantiate the two iterated away-localization structures on the common overlap and
  -- apply `IsLocalization.Away.commutes` to the square
  -- `A[g_j] → A[g_i g_j]` and `A[g_j] → C[g_j]`.
  sorry

/-- Helper for Lemma 15.109.3: after transporting the `j`-chart idempotent to the common overlap,
that overlap target is already the away-localization at the cleared numerator `a j`. This is the
source proof's first structural bridge on `A[g_i g_j]`. -/
lemma overlap_target_isLocalizationAway_numerator
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i)
    (hC : ∀ i : Fin r, IsLocalization.Away (e i) C[g i]) :
    ∀ i j : Fin r,
      IsLocalization.Away (algebraMap A A[g i * g j] (a j)) C[g i * g j] := by
  -- TODO: combine `overlap_transport_away_of_chart_idempotent` with
  -- `overlap_numerator_associated_left_idempotent` to change the overlap localization generator
  -- from the transported idempotent to the cleared numerator `a_j`.
  sorry

/-- Helper for Lemma 15.109.3: after transporting the `i`-chart idempotent to the common overlap,
its image in the overlap target ring is `1`. -/
lemma overlap_right_idempotent_maps_to_one
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i])
    (he : ∀ i : Fin r, IsIdempotentElem (e i))
    (hC : ∀ i : Fin r, IsLocalization.Away (e i) C[g i]) :
    ∀ i j : Fin r,
      algebraMap A[g i * g j] C[g i * g j]
        (IsLocalization.Away.awayToAwayRight (g i) (g j) (e i)) = 1 := by
  intro i j
  have hchart_unit : IsUnit (algebraMap A[g i] C[g i] (e i)) := by
    -- The `i`-chart is away-localized at `e i`, so the image of `e i` is a unit there.
    letI := hC i
    exact IsLocalization.map_units C[g i]
      ⟨e i, show e i ∈ Submonoid.powers (e i) from ⟨1, by simp⟩⟩
  have hoverlap_unit :
      IsUnit
        (((IsLocalization.Away.awayToAwayRight
              (algebraMap A C (g i)) (algebraMap A C (g j))) : C[g i] →+* C[g i * g j])
          (algebraMap A[g i] C[g i] (e i))) := by
    -- Transport that unit across the explicit target overlap map.
    exact hchart_unit.map
      (IsLocalization.Away.awayToAwayRight
        (algebraMap A C (g i)) (algebraMap A C (g j)))
  have htransport :
      ((IsLocalization.Away.awayToAwayRight
            (algebraMap A C (g i)) (algebraMap A C (g j))) : C[g i] →+* C[g i * g j])
          (algebraMap A[g i] C[g i] (e i)) =
        algebraMap A[g i * g j] C[g i * g j]
          (IsLocalization.Away.awayToAwayRight (g i) (g j) (e i)) := by
    -- Normalize the transported target element with the previously proved compatibility square.
    simpa [RingHom.comp_apply] using
      congrArg (fun φ : A[g i] →+* C[g i * g j] ↦ φ (e i))
        (overlap_right_target_comp (A := A) (C := C) g i j)
  have htarget_unit :
      IsUnit
        (algebraMap A[g i * g j] C[g i * g j]
          (IsLocalization.Away.awayToAwayRight (g i) (g j) (e i))) := by
    simpa [← htransport] using hoverlap_unit
  have htarget_idem :
      IsIdempotentElem
        (algebraMap A[g i * g j] C[g i * g j]
          (IsLocalization.Away.awayToAwayRight (g i) (g j) (e i))) := by
    -- Idempotence survives transport first to the overlap source and then to the overlap target.
    exact ((he i).map (IsLocalization.Away.awayToAwayRight (g i) (g j))).map
      (algebraMap A[g i * g j] C[g i * g j])
  exact Algebra.eq_one_of_isUnit_of_isIdempotentElem htarget_idem htarget_unit

/-- Helper for Lemma 15.109.3: after transporting the `j`-chart idempotent to the common overlap,
its image in the overlap target ring is `1`. -/
lemma overlap_left_idempotent_maps_to_one
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i])
    (he : ∀ i : Fin r, IsIdempotentElem (e i))
    (hC : ∀ i : Fin r, IsLocalization.Away (e i) C[g i]) :
    ∀ i j : Fin r,
      algebraMap A[g i * g j] C[g i * g j]
        (IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)) = 1 := by
  intro i j
  have hchart_unit : IsUnit (algebraMap A[g j] C[g j] (e j)) := by
    -- The `j`-chart is away-localized at `e j`, so the image of `e j` is a unit there.
    letI := hC j
    exact IsLocalization.map_units C[g j]
      ⟨e j, show e j ∈ Submonoid.powers (e j) from ⟨1, by simp⟩⟩
  have hoverlap_unit :
      IsUnit
        (((IsLocalization.Away.awayToAwayLeft
              (algebraMap A C (g j)) (algebraMap A C (g i))) : C[g j] →+* C[g i * g j])
          (algebraMap A[g j] C[g j] (e j))) := by
    -- Transport that unit across the explicit target overlap map.
    exact hchart_unit.map
      (IsLocalization.Away.awayToAwayLeft
        (algebraMap A C (g j)) (algebraMap A C (g i)))
  have htransport :
      ((IsLocalization.Away.awayToAwayLeft
            (algebraMap A C (g j)) (algebraMap A C (g i))) : C[g j] →+* C[g i * g j])
          (algebraMap A[g j] C[g j] (e j)) =
        algebraMap A[g i * g j] C[g i * g j]
          (IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)) := by
    -- Normalize the transported target element with the previously proved compatibility square.
    simpa [RingHom.comp_apply] using
      congrArg (fun φ : A[g j] →+* C[g i * g j] ↦ φ (e j))
        (overlap_left_target_comp (A := A) (C := C) g i j)
  have htarget_unit :
      IsUnit
        (algebraMap A[g i * g j] C[g i * g j]
          (IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j))) := by
    simpa [← htransport] using hoverlap_unit
  have htarget_idem :
      IsIdempotentElem
        (algebraMap A[g i * g j] C[g i * g j]
          (IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j))) := by
    -- Idempotence survives transport first to the overlap source and then to the overlap target.
    exact ((he j).map (IsLocalization.Away.awayToAwayLeft (g j) (g i))).map
      (algebraMap A[g i * g j] C[g i * g j])
  exact Algebra.eq_one_of_isUnit_of_isIdempotentElem htarget_idem htarget_unit

/-- Helper for Lemma 15.109.3: the principal ideal generated by the overlap numerator `a j`
coincides with the principal ideal generated by the transported `j`-chart idempotent. -/
lemma overlap_numerator_span_eq_left_idempotent_span
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i) :
    ∀ i j : Fin r,
      Ideal.span ({algebraMap A A[g i * g j] (a j)} : Set A[g i * g j]) =
        Ideal.span
          ({IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)} :
            Set A[g i * g j]) := by
  intro i j
  -- Rewrite the numerator-generated principal ideal by the associated transported idempotent.
  exact ideal_span_singleton_eq_of_associated
    (overlap_numerator_associated_left_idempotent (A := A) g e ha i j)

/-- Helper for Lemma 15.109.3: on the common overlap, the cleared numerator `a j` already belongs
to the principal ideal generated by the transported idempotent from the `j`-chart. -/
lemma overlap_numerator_mem_left_idempotent_span
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i) :
    ∀ i j : Fin r,
      algebraMap A A[g i * g j] (a j) ∈
        Ideal.span
          ({IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)} :
            Set A[g i * g j]) := by
  intro i j
  rcases overlap_numerator_eq_unit_mul_left_idempotent (A := A) g e ha i j with ⟨u, hu⟩
  -- Proof comment: a unit multiple of the chosen generator lies in its singleton span.
  rw [hu]
  exact Ideal.mem_span_singleton.mpr ⟨↑u, by simpa [mul_comm] using hu.symm⟩

/-- Helper for Lemma 15.109.3: passing a global ideal first to the `i`-chart and then to the
common overlap is the same as mapping it directly from `A` to `A[g_i g_j]`. -/
lemma overlap_map_map_eq_direct
    {r : ℕ} (g : Fin r → A) (J : Ideal A) (i j : Fin r) :
    Ideal.map (IsLocalization.Away.awayToAwayRight (g i) (g j))
        (Ideal.map (algebraMap A A[g i]) J) =
      Ideal.map (algebraMap A A[g i * g j]) J := by
  have hcomp :
      (IsLocalization.Away.awayToAwayRight (g i) (g j) : A[g i] →+* A[g i * g j]).comp
          (algebraMap A A[g i]) =
        algebraMap A A[g i * g j] := by
    -- Proof comment: both maps are the canonical localization map out of `A`, so they agree on
    -- every base element.
    ext x
    simpa [RingHom.comp_apply] using
      (overlap_right_algebraMap_eq (x := g i) (y := g j) (a := x))
  -- Rewrite the iterated ideal image as the image under the composed overlap map.
  simpa [hcomp] using
    (Ideal.map_map
      (f := (algebraMap A A[g i] : A →+* A[g i]))
      (g := (IsLocalization.Away.awayToAwayRight (g i) (g j) : A[g i] →+* A[g i * g j]))
      (I := J))

/-- Helper for Lemma 15.109.3: on the common overlap, the global numerator ideal already contains
the idempotent transported from the `j`-chart. -/
lemma overlap_left_idempotent_span_le_map_numerator_ideal
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i)
    (i j : Fin r) :
    Ideal.span
        ({IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j)} :
          Set A[g i * g j]) ≤
      Ideal.map (algebraMap A A[g i * g j]) (Ideal.span (Set.range a)) := by
  have haj_mem :
      algebraMap A A[g i * g j] (a j) ∈
        Ideal.map (algebraMap A A[g i * g j]) (Ideal.span (Set.range a)) := by
    -- The generator `a j` lies in the source numerator ideal by definition.
    exact Ideal.mem_map_of_mem (algebraMap A A[g i * g j])
      (Ideal.subset_span (Set.mem_range_self j))
  have hspan_aj :
      Ideal.span ({algebraMap A A[g i * g j] (a j)} : Set A[g i * g j]) ≤
        Ideal.map (algebraMap A A[g i * g j]) (Ideal.span (Set.range a)) := by
    -- Passing from the element to its singleton span is the canonical ideal-containment step.
    exact (Ideal.span_singleton_le_iff_mem _).2 haj_mem
  have hej_mem :
      IsLocalization.Away.awayToAwayLeft (g j) (g i) (e j) ∈
        Ideal.span ({algebraMap A A[g i * g j] (a j)} : Set A[g i * g j]) := by
    rcases overlap_numerator_eq_unit_mul_left_idempotent (A := A) g e ha i j with ⟨u, hu⟩
    -- Proof comment: the transported idempotent differs from the localized numerator by a unit,
    -- so it already belongs to the principal ideal generated by that numerator.
    rw [hu]
    exact Ideal.mem_span_singleton.mpr ⟨↑(u⁻¹), by
      simp [mul_assoc, mul_left_comm, mul_comm]⟩
  exact (Ideal.span_singleton_le_iff_mem _).2 (hspan_aj hej_mem)

/-- Helper for Lemma 15.109.3: on the common overlap, the transported `i`-chart idempotent ideal
already lies in the direct image of the global numerator ideal. -/
lemma overlap_right_idempotent_span_le_map_numerator_ideal
    {r : ℕ} (g : Fin r → A) (e : ∀ i : Fin r, A[g i]) {n : ℕ} {a : Fin r → A}
    (ha : ∀ i : Fin r,
      algebraMap A A[g i] (a i) =
        (algebraMap A A[g i] (g i)) ^ n * e i)
    (i j : Fin r) :
    Ideal.map (IsLocalization.Away.awayToAwayRight (g i) (g j))
        (Ideal.span ({e i} : Set A[g i])) ≤
      Ideal.map (algebraMap A A[g i * g j]) (Ideal.span (Set.range a)) := by
  -- Proof comment: first use the chartwise numerator containment on `A[g i]`, then transport that
  -- containment to the overlap and collapse the iterated image to the direct image from `A`.
  calc
    Ideal.map (IsLocalization.Away.awayToAwayRight (g i) (g j))
        (Ideal.span ({e i} : Set A[g i])) ≤
      Ideal.map (IsLocalization.Away.awayToAwayRight (g i) (g j))
        (Ideal.map (algebraMap A A[g i]) (Ideal.span (Set.range a))) := by
          exact Ideal.map_mono
            (local_idempotent_span_le_map_numerator_ideal (A := A) g e ha i)
    _ = Ideal.map (algebraMap A A[g i * g j]) (Ideal.span (Set.range a)) := by
          simpa using
            overlap_map_map_eq_direct (A := A) g (Ideal.span (Set.range a)) i j

/-
Domain-style sampling for Lemma 15.109.3:
- primary domain: commutative algebra of local product decompositions detected on principal opens
  by idempotent localizations;
- sampled owner declarations:
  `exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation`,
  `Localization.awayMapₐ`,
  `RingHom.prod_bijective_of_isIdempotentElem`,
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator`;
- best owner abstraction: the public local comparison morphisms should stay at the canonical
  `Localization.awayMapₐ` surface; the local hypothesis is already the localized owner-level datum
  produced upstream by
  `exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation`, while the
  idempotent quotient/product decomposition and the finite-cover gluing argument are derived API
  rather than parallel owner declarations. The owner property on the comparison maps is still
  `Function.Bijective`; the local complementary splitting is supplied by
  `RingHom.prod_bijective_of_isIdempotentElem`, and the quotient-localization bridge by
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator`;
- primitive vs. derived:
  primitive data are the finitely generated ideal `I` and, for each `f ∈ I`, an idempotent in
  `A_f` whose associated away localization identifies `C_f`;
  derived API is the complementary quotient ideal `J`, with local bijectivity of the canonical
  away maps into `C × A ⧸ J`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below;
- `core/canonical`: `Localization.awayMapₐ` for the localized comparison maps and
  `RingHom.prod_bijective_of_isIdempotentElem` together with
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator` for the idempotent splitting and
  quotient-localization bridge, with target property `Function.Bijective`;
- `bridge/view`: quotient/product decompositions produced from the local idempotents. -/

-- Proof sketch: choose generators of `I`, write each localized algebra `C_f` as a localization of
-- `A_f` away from an idempotent, construct the complementary quotient ideal `J` from the
-- corresponding idempotent data, and then use the finite gluing criterion for local isomorphisms
-- on the cover by the chosen generators to extend the local product decomposition to every
-- `f ∈ I`.
/-- Lemma 15.109.3: if `I` is finitely generated and for each `f ∈ I` the localized map
`A_f → C_f` is localization away from an idempotent of `A_f`, then there exists a quotient ideal
`J ⊂ A` such that for every `f ∈ I` the localized map `A_f → (C × A ⧸ J)_f` is bijective. This
is the canonical quotient-algebra form of the source’s surjective complementary factor. -/
theorem exists_quotient_factor_of_localizationAway_idempotent_on_fg_ideal
    (I : Ideal A)
    (hI : I.FG)
    (hAway :
      ∀ ⦃f : A⦄, f ∈ I → ∃ e : A[f],
        IsIdempotentElem e ∧ IsLocalization.Away e C[f]) :
    ∃ J : Ideal A, ∀ ⦃f : A⦄, f ∈ I →
      Function.Bijective (Localization.awayMapₐ (Algebra.ofId A (C × A ⧸ J)) f) := by
  classical
  -- The source-proof route is to choose a finite generating family for `I`, clear the local
  -- idempotents by one common power, and take the global quotient from the resulting numerators.
  -- Route correction: the old proof kept the infimum-defined ideal in the foreground and got
  -- stuck on overlap transport for the wrong global object. The source-faithful route fixes the
  -- numerator ideal `J := (a_i)` first and postpones only the cross-chart containment.
  obtain ⟨s, hs⟩ := hI
  let g : Fin s.card → A := fun i ↦ (s.equivFin.symm i : A)
  have hg_span : Ideal.span (Set.range g) = I := by
    -- Rewrite the finite set of chosen generators as a `Fin`-indexed family.
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [g]⟩
  have hg_mem : ∀ i : Fin s.card, g i ∈ I := by
    intro i
    -- Each chosen generator belongs to the ideal it generates.
    simpa [hg_span] using
      (Ideal.subset_span (Set.mem_range_self i) : g i ∈ Ideal.span (Set.range g))
  let localData : ∀ i : Fin s.card, ∃ e : A[g i],
      IsIdempotentElem e ∧ IsLocalization.Away e C[g i] := fun i ↦
    hAway (hg_mem i)
  choose e he hC using localData
  obtain ⟨n, a, ha, ha_sq, hpair⟩ :=
    exists_common_power_idempotent_numerators_with_pairwise (A := A) (C := C) g e he hC
  let J : Ideal A := Ideal.span (Set.range a)
  refine ⟨J, ?_⟩
  intro f hf
  -- The main skeleton is now fixed:
  -- 1. the source ideal is now the numerator ideal `J := (a_i)`;
  -- 2. the diagonal identity `a i = g_i^n e_i` already gives
  --    `Ideal.span ({e i}) ≤ Ideal.map J` on each generator chart;
  -- 3. it remains to prove the reverse inclusion from the overlap argument, then finish by the
  --    local idempotent product decomposition and the finite cover criterion.
  have hg_cover_top : ∀ i : Fin s.card,
      Ideal.span (Set.range fun j : Fin s.card ↦ algebraMap A A[g i] (g j)) = ⊤ := by
    intro i
    -- This is the easy cover lemma needed later for the local-to-global descent on each `A[g i]`.
    simpa [g] using localized_generator_family_spans_top (A := A) g i
  have hf_cover_top :
      Ideal.span (Set.range fun j : Fin s.card ↦ algebraMap A A[f] (g j)) = ⊤ := by
    have hf_span : f ∈ Ideal.span (Set.range g) := by
      simpa [hg_span] using hf
    -- The same cover remains spanning after localizing at an arbitrary `f ∈ I`.
    simpa using localized_family_spans_top_of_mem_span (A := A) g hf_span
  have hlocal_ge : ∀ i : Fin s.card,
      Ideal.span ({e i} : Set A[g i]) ≤ Ideal.map (algebraMap A A[g i]) J := by
    intro i
    -- The diagonal numerator `a i = g_i^n e_i` already lands inside the mapped numerator ideal.
    simpa [J] using
      local_idempotent_span_le_map_numerator_ideal (A := A) g e ha i
  have hlocal_eq :
      ∀ i : Fin s.card,
        Ideal.map (algebraMap A A[g i]) J = Ideal.span ({e i} : Set A[g i]) := by
    intro i
    -- Proof comment: the strengthened numerator helper already packages the source proof's
    -- pairwise divisibility relation, so the chartwise ideal equality closes immediately.
    simpa [J] using
      local_numerator_ideal_eq_idempotent_span_of_pairwise
        (A := A) g e ha hpair i
  -- TODO: prove the source-faithful overlap step:
  -- 1. use the now-established chartwise identity `hlocal_eq` to rewrite the local quotient
  --    `(A[g_i] ⧸ Ideal.map J)` as `(A[g_i] ⧸ (e_i))`;
  -- 2. combine that rewrite with `localized_idempotent_factor_exists` to obtain bijectivity on
  --    each generator chart `g_i`;
  -- 3. pass from the generator charts to an arbitrary `f ∈ I` by localizing those generator-chart
  --    bijections further at `f` and applying `bijective_of_localized_span` to the cover
  --    `g_1, ..., g_r` of `A_f`.
  sorry

end
