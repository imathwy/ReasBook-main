import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Bezout
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain-style sampling:
- primary domain: elementary divisor domains and Smith normal form over commutative domains;
- sampled owner declarations:
  `IsBezout`,
  `Module.Basis.SmithNormalForm`,
  `Submodule.smithNormalForm`,
  `Submodule.exists_smith_normal_form_of_rank_eq`;
- source/core/bridge triage:
  `source-facing`: the ring property that every finite matrix over `R` admits an elementary-divisor
  diagonal form;
  `core/canonical`: mathlib's Smith-normal-form owner `Module.Basis.SmithNormalForm` for
  submodules of finite free modules over a PID, together with the canonical Bézout owner
  `IsBezout`;
  `bridge/view`: the explicit matrix predicate `Matrix.HasElementaryDivisorDiagonal` and the
  rectangular diagonal matrix `Matrix.smithNormalDiagonal`, which keep the source matrix language
  without introducing a second owner abstraction.
- primitive data: only the ring-level elementary-divisor property;
- derived API: the Bézout instance and the PID-to-elementary-divisor instance.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Definition 15.125.5 (1): a Bezout domain is the canonical mathlib property `IsBezout R`,
namely that every finitely generated ideal of `R` is principal. -/
#check IsBezout

end

namespace Matrix

variable {R : Type u}

/-- The rectangular diagonal matrix with diagonal entries `d` and all other entries equal to `0`.
-/
def smithNormalDiagonal [Zero R] {n m : ℕ} (d : Fin (Nat.min n m) → R) :
    Matrix (Fin n) (Fin m) R :=
  fun i j ↦ if hij : i.1 = j.1 ∧ i.1 < Nat.min n m then d ⟨i.1, hij.2⟩ else 0

/-- Helper for Definition 15.125.5: on `Fin 2`, the custom Smith diagonal is the expected
`2 × 2` diagonal matrix. -/
lemma smithNormalDiagonal_fin_two [CommRing R] (a b : R) :
    (smithNormalDiagonal ![a, b] : Matrix (Fin 2) (Fin 2) R) = !![a, 0; 0, b] := by
  -- Unfolding the custom diagonal on the two indices shows the familiar concrete matrix.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [smithNormalDiagonal]
  · rfl
  · rfl

/-- A matrix admits an elementary-divisor diagonal form if left and right multiplication by
invertible matrices turns it into a rectangular diagonal matrix whose diagonal entries form a
divisibility chain. -/
def HasElementaryDivisorDiagonal [CommRing R] {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) : Prop :=
  ∃ U : (Matrix (Fin n) (Fin n) R)ˣ, ∃ V : (Matrix (Fin m) (Fin m) R)ˣ,
    ∃ d : Fin (Nat.min n m) → R,
      (((U : Matrix (Fin n) (Fin n) R) * A) * (V : Matrix (Fin m) (Fin m) R)) =
        smithNormalDiagonal d ∧
      List.IsChain (· ∣ ·) (List.ofFn d)

/-- Helper for Definition 15.125.5: a matrix that is already a Smith diagonal with a divisibility
chain satisfies `HasElementaryDivisorDiagonal` without further row or column operations. -/
lemma hasElementaryDivisorDiagonal_of_smithNormalDiagonal [CommRing R] {n m : ℕ}
    (d : Fin (Nat.min n m) → R) (hchain : List.IsChain (· ∣ ·) (List.ofFn d)) :
    (smithNormalDiagonal d : Matrix (Fin n) (Fin m) R).HasElementaryDivisorDiagonal := by
  -- The source-facing predicate is witnessed by the identity matrices once the diagonal shape and
  -- divisibility chain are already present.
  refine ⟨1, 1, d, ?_, hchain⟩
  simp

/-- Helper for Definition 15.125.5: a two-term divisibility relation is exactly the chain
condition needed for the corresponding Smith diagonal. -/
lemma isChain_ofFn_vec2 [CommRing R] {a b : R} (hab : a ∣ b) :
    List.IsChain (· ∣ ·) (List.ofFn ![a, b]) := by
  -- On a list with two entries, `IsChain` reduces to the single divisibility relation.
  simpa using (List.isChain_pair : List.IsChain (· ∣ ·) [a, b] ↔ a ∣ b).2 hab

/-- Helper for Definition 15.125.5: a `2 × 2` Smith diagonal whose first entry divides the second
already satisfies the elementary-divisor condition. -/
lemma diagonal_pair_hasElementaryDivisorDiagonal_of_dvd [CommRing R] {a b : R} (hab : a ∣ b) :
    (smithNormalDiagonal ![a, b] : Matrix (Fin 2) (Fin 2) R).HasElementaryDivisorDiagonal := by
  -- The diagonal matrix is already in the required form, so the identity units witness it.
  refine ⟨1, 1, ![a, b], ?_, isChain_ofFn_vec2 hab⟩
  simp

end Matrix

section

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Definition 15.125.5: an elementary divisor domain is a domain such that every finite
rectangular matrix over `R` can be diagonalized by invertible left and right multipliers, with
diagonal entries forming a divisibility chain. -/
@[stacks 0ASR]
class IsElementaryDivisorDomain (R : Type u) [CommRing R] [IsDomain R] : Prop where
  hasElementaryDivisorDiagonal {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    A.HasElementaryDivisorDiagonal

-- Proof sketch: apply the elementary-divisor condition to the `1 × 2` matrix `[x y]`; the single
-- diagonal entry then generates the ideal `(x, y)`, showing that every two-generated ideal is
-- principal, hence `R` is Bézout by the standard mathlib characterization.
/-- An elementary divisor domain is a Bézout domain. -/
instance isBezout_of_isElementaryDivisorDomain [IsElementaryDivisorDomain R] : IsBezout R := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  let A : Matrix (Fin 1) (Fin 2) R := !![x, y]
  obtain ⟨U, V, d, hdiag, _⟩ := IsElementaryDivisorDomain.hasElementaryDivisorDiagonal (R := R) A
  let C : Matrix (Fin 1) (Fin 2) R := A * (V : Matrix (Fin 2) (Fin 2) R)
  let B : Matrix (Fin 1) (Fin 2) R :=
    ((U : Matrix (Fin 1) (Fin 1) R) * A) * (V : Matrix (Fin 2) (Fin 2) R)
  let u : R := (U : Matrix (Fin 1) (Fin 1) R) 0 0
  let uInv : R := ((↑(U⁻¹) : Matrix (Fin 1) (Fin 1) R) 0 0)
  let VInv : Matrix (Fin 2) (Fin 2) R := ↑(V⁻¹)
  let d0 : R := d ⟨0, by decide⟩
  -- Read off the two entries of the Smith-form row.
  have hB00 : B 0 0 = d0 := by
    have h := congrArg (fun M : Matrix (Fin 1) (Fin 2) R => M 0 0) hdiag
    simpa [B, d0, Matrix.smithNormalDiagonal] using h
  have hB01 : B 0 1 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 1) (Fin 2) R => M 0 1) hdiag
    simpa [B, Matrix.smithNormalDiagonal] using h
  -- The `1 × 1` change-of-basis matrix acts by multiplication with a unit scalar.
  have hu_mul : u * uInv = 1 := by
    have h :=
      congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0)
        (show ((U : Matrix (Fin 1) (Fin 1) R) * ↑(U⁻¹ : (Matrix (Fin 1) (Fin 1) R)ˣ)) = 1 from
          U.mul_inv)
    simpa [u, uInv, Matrix.mul_apply] using h
  have huInv_mul : uInv * u = 1 := by
    have h :=
      congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0)
        (show ((↑(U⁻¹ : (Matrix (Fin 1) (Fin 1) R)ˣ) : Matrix (Fin 1) (Fin 1) R) *
            (U : Matrix (Fin 1) (Fin 1) R)) = 1 from
          U.inv_mul)
    simpa [u, uInv, Matrix.mul_apply] using h
  have hVVInv00 :
      (V : Matrix (Fin 2) (Fin 2) R) 0 0 * VInv 0 0 +
        (V : Matrix (Fin 2) (Fin 2) R) 0 1 * VInv 1 0 = 1 := by
    have h :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0)
        (show (V : Matrix (Fin 2) (Fin 2) R) * VInv = (1 : Matrix (Fin 2) (Fin 2) R) from
          V.mul_inv)
    simpa [Matrix.mul_apply] using h
  have hVVInv10 :
      (V : Matrix (Fin 2) (Fin 2) R) 1 0 * VInv 0 0 +
        (V : Matrix (Fin 2) (Fin 2) R) 1 1 * VInv 1 0 = 0 := by
    have h :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0)
        (show (V : Matrix (Fin 2) (Fin 2) R) * VInv = (1 : Matrix (Fin 2) (Fin 2) R) from
          V.mul_inv)
    simpa [Matrix.mul_apply] using h
  have hVVInv01 :
      (V : Matrix (Fin 2) (Fin 2) R) 0 0 * VInv 0 1 +
        (V : Matrix (Fin 2) (Fin 2) R) 0 1 * VInv 1 1 = 0 := by
    have h :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1)
        (show (V : Matrix (Fin 2) (Fin 2) R) * VInv = (1 : Matrix (Fin 2) (Fin 2) R) from
          V.mul_inv)
    simpa [Matrix.mul_apply] using h
  have hVVInv11 :
      (V : Matrix (Fin 2) (Fin 2) R) 1 0 * VInv 0 1 +
        (V : Matrix (Fin 2) (Fin 2) R) 1 1 * VInv 1 1 = 1 := by
    have h :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1)
        (show (V : Matrix (Fin 2) (Fin 2) R) * VInv = (1 : Matrix (Fin 2) (Fin 2) R) from
          V.mul_inv)
    simpa [Matrix.mul_apply] using h
  have hB_scale00 : B 0 0 = u * C 0 0 := by
    calc
      B 0 0 =
          (U : Matrix (Fin 1) (Fin 1) R) 0 0 * A 0 0 * (V : Matrix (Fin 2) (Fin 2) R) 0 0 +
            (U : Matrix (Fin 1) (Fin 1) R) 0 0 * A 0 1 * (V : Matrix (Fin 2) (Fin 2) R) 1 0 := by
        simp [B, Matrix.mul_apply]
      _ = u * (A 0 0 * (V : Matrix (Fin 2) (Fin 2) R) 0 0 +
          A 0 1 * (V : Matrix (Fin 2) (Fin 2) R) 1 0) := by
        simp [u, mul_add, mul_assoc]
      _ = u * C 0 0 := by
        simp [C, Matrix.mul_apply]
  have hB_scale01 : B 0 1 = u * C 0 1 := by
    calc
      B 0 1 =
          (U : Matrix (Fin 1) (Fin 1) R) 0 0 * A 0 0 * (V : Matrix (Fin 2) (Fin 2) R) 0 1 +
            (U : Matrix (Fin 1) (Fin 1) R) 0 0 * A 0 1 * (V : Matrix (Fin 2) (Fin 2) R) 1 1 := by
        simp [B, Matrix.mul_apply]
      _ = u * (A 0 0 * (V : Matrix (Fin 2) (Fin 2) R) 0 1 +
          A 0 1 * (V : Matrix (Fin 2) (Fin 2) R) 1 1) := by
        simp [u, mul_add, mul_assoc]
      _ = u * C 0 1 := by
        simp [C, Matrix.mul_apply]
  -- Right multiplication by an invertible `2 × 2` matrix preserves the generated ideal of the row.
  have hC_span :
      Ideal.span ({C 0 0, C 0 1} : Set R) = Ideal.span ({x, y} : Set R) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · refine Ideal.mem_span_pair.mpr ?_
        refine ⟨(V : Matrix (Fin 2) (Fin 2) R) 0 0, (V : Matrix (Fin 2) (Fin 2) R) 1 0, ?_⟩
        simpa [C, A, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
          mul_comm, mul_left_comm, mul_assoc]
      · refine Ideal.mem_span_pair.mpr ?_
        refine ⟨(V : Matrix (Fin 2) (Fin 2) R) 0 1, (V : Matrix (Fin 2) (Fin 2) R) 1 1, ?_⟩
        simpa [C, A, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
          mul_comm, mul_left_comm, mul_assoc]
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · refine Ideal.mem_span_pair.mpr ?_
        refine ⟨VInv 0 0, VInv 1 0, ?_⟩
        have hx_mem :
            VInv 0 0 * C 0 0 + VInv 1 0 * C 0 1 = x := by
          calc
            VInv 0 0 * C 0 0 + VInv 1 0 * C 0 1 =
                x * ((V : Matrix (Fin 2) (Fin 2) R) 0 0 * VInv 0 0 +
                  (V : Matrix (Fin 2) (Fin 2) R) 0 1 * VInv 1 0) +
                y * ((V : Matrix (Fin 2) (Fin 2) R) 1 0 * VInv 0 0 +
                  (V : Matrix (Fin 2) (Fin 2) R) 1 1 * VInv 1 0) := by
              simp [C, A, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
                mul_add, add_mul, mul_comm, mul_assoc]
              ring
            _ = x := by
              rw [hVVInv00, hVVInv10]
              ring
        simpa [hz] using hx_mem
      · refine Ideal.mem_span_pair.mpr ?_
        refine ⟨VInv 0 1, VInv 1 1, ?_⟩
        have hy_mem :
            VInv 0 1 * C 0 0 + VInv 1 1 * C 0 1 = y := by
          calc
            VInv 0 1 * C 0 0 + VInv 1 1 * C 0 1 =
                x * ((V : Matrix (Fin 2) (Fin 2) R) 0 0 * VInv 0 1 +
                  (V : Matrix (Fin 2) (Fin 2) R) 0 1 * VInv 1 1) +
                y * ((V : Matrix (Fin 2) (Fin 2) R) 1 0 * VInv 0 1 +
                  (V : Matrix (Fin 2) (Fin 2) R) 1 1 * VInv 1 1) := by
              simp [C, A, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
                mul_add, add_mul, mul_comm, mul_assoc]
              ring
            _ = y := by
              rw [hVVInv01, hVVInv11]
              ring
        simpa [hz] using hy_mem
  -- Left multiplication by the invertible `1 × 1` matrix only rescales the row by a unit.
  have hB_span :
      Ideal.span ({B 0 0, B 0 1} : Set R) = Ideal.span ({C 0 0, C 0 1} : Set R) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · refine Ideal.mem_span_pair.mpr ?_
        simpa [hB_scale00] using ⟨u, 0, by simp⟩
      · refine Ideal.mem_span_pair.mpr ?_
        simpa [hB_scale01] using ⟨0, u, by simp⟩
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · refine Ideal.mem_span_pair.mpr ?_
        refine ⟨uInv, 0, ?_⟩
        calc
          uInv * B 0 0 + 0 * B 0 1 = uInv * (u * C 0 0) := by simp [hB_scale00]
          _ = (uInv * u) * C 0 0 := by ring
          _ = C 0 0 := by simp [huInv_mul]
      · refine Ideal.mem_span_pair.mpr ?_
        refine ⟨0, uInv, ?_⟩
        calc
          0 * B 0 0 + uInv * B 0 1 = uInv * (u * C 0 1) := by simp [hB_scale01]
          _ = (uInv * u) * C 0 1 := by ring
          _ = C 0 1 := by simp [huInv_mul]
  -- The Smith row is exactly `[d 0]`, so its span is principal.
  have hprincipal : (Ideal.span ({d0} : Set R)).IsPrincipal := by infer_instance
  have hdiag_span : Ideal.span ({B 0 0, B 0 1} : Set R) = Ideal.span ({d0} : Set R) := by
    rw [hB00, hB01]
    simp
  rw [← hC_span, ← hB_span, hdiag_span]
  exact hprincipal

/-- Helper for Definition 15.125.5: a single Bézout move on a `2 × 2` diagonal matrix produces a
new diagonal matrix whose first entry divides the second. -/
lemma diagonal_pair_refines_to_dvd [IsBezout R] (a b : R) :
    ∃ U : (Matrix (Fin 2) (Fin 2) R)ˣ, ∃ V : (Matrix (Fin 2) (Fin 2) R)ˣ,
      ∃ g h : R,
        (((U : Matrix (Fin 2) (Fin 2) R) * Matrix.smithNormalDiagonal ![a, b]) *
            (V : Matrix (Fin 2) (Fin 2) R)) =
          Matrix.smithNormalDiagonal ![g, h] ∧
        g ∣ h := by
  set g : R := IsBezout.gcd a b with hgdef
  obtain ⟨u, v, huv₀⟩ := IsBezout.gcd_eq_sum a b
  have huv : u * a + v * b = g := by
    simpa [hgdef] using huv₀
  obtain ⟨a₁, ha₁₀⟩ := IsBezout.gcd_dvd_left a b
  have ha₁ : a = g * a₁ := by
    simpa [hgdef] using ha₁₀
  obtain ⟨b₁, hb₁₀⟩ := IsBezout.gcd_dvd_right a b
  have hb₁ : b = g * b₁ := by
    simpa [hgdef] using hb₁₀
  by_cases hg : g = 0
  · -- If the gcd vanishes, then both entries are zero and the identity matrices already work.
    have ha : a = 0 := by
      simpa [hg] using ha₁
    have hb : b = 0 := by
      simpa [hg] using hb₁
    refine ⟨1, 1, 0, 0, ?_, dvd_rfl⟩
    simp [Matrix.smithNormalDiagonal_fin_two, ha, hb]
  · -- Otherwise divide out the gcd, build explicit unimodular row and column operations, and
    -- check entrywise that they produce the desired Smith diagonal.
    have hcoprime_mul : g * (u * a₁ + v * b₁) = g := by
      calc
        g * (u * a₁ + v * b₁) = u * a + v * b := by
          rw [ha₁, hb₁]
          ring
        _ = g := huv
    have hcoprime : u * a₁ + v * b₁ = 1 := by
      apply mul_left_cancel₀ hg
      simpa using hcoprime_mul
    let U₀ : Matrix (Fin 2) (Fin 2) R := !![u, v; -b₁, a₁]
    let V₀ : Matrix (Fin 2) (Fin 2) R := !![1, -(v * b₁); 1, u * a₁]
    have hU₀_det : U₀.det = 1 := by
      simp [U₀, Matrix.det_fin_two, hcoprime]
    have hV₀_det : V₀.det = 1 := by
      simp [V₀, Matrix.det_fin_two, hcoprime]
    have hU₀_unit : IsUnit U₀ :=
      (Matrix.isUnit_iff_isUnit_det U₀).2 (by
        simpa [hU₀_det] using (isUnit_one : IsUnit (1 : R)))
    have hV₀_unit : IsUnit V₀ :=
      (Matrix.isUnit_iff_isUnit_det V₀).2 (by
        simpa [hV₀_det] using (isUnit_one : IsUnit (1 : R)))
    obtain ⟨U, hU⟩ := hU₀_unit
    obtain ⟨V, hV⟩ := hV₀_unit
    refine ⟨U, V, g, g * a₁ * b₁, ?_, ⟨a₁ * b₁, by ring⟩⟩
    calc
      (((U : Matrix (Fin 2) (Fin 2) R) * Matrix.smithNormalDiagonal ![a, b]) *
            (V : Matrix (Fin 2) (Fin 2) R)) =
          ((U₀ * Matrix.smithNormalDiagonal ![a, b]) * V₀) := by
        simpa [hU, hV]
      _ = Matrix.smithNormalDiagonal ![g, g * a₁ * b₁] := by
        rw [Matrix.smithNormalDiagonal_fin_two, Matrix.smithNormalDiagonal_fin_two]
        ext i j
        fin_cases i <;> fin_cases j
        · -- The Bézout relation gives the new leading diagonal entry.
          simpa [Matrix.mul_apply, Fin.sum_univ_two, U₀, V₀] using huv
        · -- The upper-right entry vanishes after the compensating column operation.
          simp [Matrix.mul_apply, Fin.sum_univ_two, U₀, V₀, ha₁, hb₁]
          ring
        · -- The lower-left entry vanishes because both original entries share the gcd factor.
          simp [Matrix.mul_apply, Fin.sum_univ_two, U₀, V₀, ha₁, hb₁]
          ring
        · -- The lower-right entry records the remaining quotient factor.
          calc
            (((U₀ * !![a, 0; 0, b]) * V₀) 1 1) = g * a₁ * b₁ * (u * a₁ + v * b₁) := by
              simp [Matrix.mul_apply, Fin.sum_univ_two, U₀, V₀, ha₁, hb₁]
              ring
            _ = g * a₁ * b₁ := by
              rw [hcoprime]
              ring

/-- Helper for Definition 15.125.5: the range-restricted map onto its own range is surjective. -/
lemma rangeRestrict_range_eq_top {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    f.rangeRestrict.range = ⊤ := by
  -- Every element of `f.range` is tautologically hit by the range-restricted map.
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    rcases LinearMap.mem_range.mp y.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simpa using hx

/-- Helper for Definition 15.125.5: a right inverse makes the map
`(p, k) ↦ s p + k` bijective from `P × ker f` onto the source. -/
lemma section_add_ker_bijective_of_rightInverse {M P : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    Function.Bijective (fun x : P × ↥f.ker ↦ s x.1 + x.2) := by
  have hs_apply : ∀ p : P, f (s p) = p := by
    intro p
    have h := congrArg (fun g : P →ₗ[R] P => g p) hs
    simpa [LinearMap.comp_apply] using h
  constructor
  · intro x y hxy
    rcases x with ⟨px, kx⟩
    rcases y with ⟨py, ky⟩
    -- Applying `f` recovers the target coordinate because the kernel terms vanish.
    have hfst : px = py := by
      have h := congrArg f hxy
      simpa [hs_apply, LinearMap.mem_ker.mp kx.property, LinearMap.mem_ker.mp ky.property] using h
    subst hfst
    -- Once the first coordinates match, add-cancellation recovers the kernel component.
    have hsnd : (kx : M) = ky := by
      exact add_left_cancel hxy
    exact Prod.ext rfl (Subtype.ext hsnd)
  · intro x
    -- The inverse picks the image `f x` and the residual term `x - s (f x)` in the kernel.
    refine ⟨(f x, ⟨x - s (f x), ?_⟩), ?_⟩
    · rw [LinearMap.mem_ker]
      simp [LinearMap.map_sub, hs_apply]
    · simp [sub_eq_add_neg, add_left_comm]

/-- Helper for Definition 15.125.5: the range-restricted map has a linear right inverse over a
projective range. -/
lemma exists_rightInverse_rangeRestrict {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) [Module.Projective R ↥f.range] :
    ∃ s : ↥f.range →ₗ[R] M, f.rangeRestrict.comp s = LinearMap.id := by
  -- Projectivity upgrades surjectivity of the range-restricted map to a section.
  exact LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (rangeRestrict_range_eq_top (R := R) f)

/-- Helper for Definition 15.125.5: restricting a map to its own range does not change the
kernel. -/
lemma rangeRestrict_ker_eq_ker {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    f.rangeRestrict.ker = f.ker := by
  -- Both kernels consist exactly of those vectors sent to `0` by the underlying map.
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    exact Subtype.ext hx

/-- Helper for Definition 15.125.5: the kernel of `rangeRestrict` is canonically the ordinary
kernel of the original map. -/
noncomputable def rangeRestrict_ker_linearEquiv_ker {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    f.rangeRestrict.ker ≃ₗ[R] f.ker :=
  LinearEquiv.ofEq _ _ (rangeRestrict_ker_eq_ker (R := R) f)

/-- Helper for Definition 15.125.5: reindexing the chosen domain and codomain bases reindexes the
matrix of a linear map in the same rows and columns. -/
lemma linearMap_toMatrix_reindex_eq {ι ι' κ κ' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {M N : Type u} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (bdom : Module.Basis κ R M) (bcod : Module.Basis ι R N) (eDom : κ ≃ κ')
    (eCod : ι ≃ ι') (f : M →ₗ[R] N) :
    LinearMap.toMatrix (bdom.reindex eDom) (bcod.reindex eCod) f =
      Matrix.reindex eCod eDom (LinearMap.toMatrix bdom bcod f) := by
  -- Both sides compute the same coordinates after translating indices through the chosen
  -- equivalences.
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.reindex_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply]

/-- Helper for Definition 15.125.5: subtracting a section of `rangeRestrict` from a vector leaves
an element of `rangeRestrict.ker`. -/
lemma sub_section_mem_rangeRestrict_ker {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (s : ↥f.range →ₗ[R] M)
    (hs : f.rangeRestrict.comp s = LinearMap.id) (x : M) :
    x - s (f.rangeRestrict x) ∈ f.rangeRestrict.ker := by
  -- Applying `rangeRestrict` to the residual cancels the chosen section against the image term.
  rw [LinearMap.mem_ker]
  ext
  have hs_apply :
      f (s (f.rangeRestrict x)) = f x := by
    have h :=
      congrArg (fun g : ↥f.range →ₗ[R] ↥f.range => g (f.rangeRestrict x)) hs
    exact congrArg Subtype.val (by simpa [LinearMap.comp_apply] using h)
  simp [LinearMap.map_sub, hs_apply]

/-- Helper for Definition 15.125.5: the chosen codomain split equivalence sends the left block
back to the obvious `Sum.inl` coordinate. -/
lemma split_codomain_equiv_apply_castLE {n r : ℕ} (hro : r ≤ n) (j : Fin r) :
    ((finSumFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hro)))).symm)
      (Fin.castLE hro j) = Sum.inl j := by
  -- TODO: normalize `Fin.castLE hro j` to the cast of `Fin.castAdd (n - r) j`, then apply
  -- `finSumFinEquiv.symm` to read it as `Sum.inl j`.
  sorry

/-- Helper for Definition 15.125.5: the chosen codomain split equivalence sends the complementary
right block back to the obvious `Sum.inr` coordinate. -/
lemma split_codomain_equiv_apply_right {n r : ℕ} (hro : r ≤ n) (j : Fin (n - r)) :
    ((finSumFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hro)))).symm)
      ((Equiv.cast (congrArg Fin (Nat.add_sub_of_le hro))) (Fin.natAdd r j)) = Sum.inr j := by
  let e : Fin r ⊕ Fin (n - r) ≃ Fin n :=
    finSumFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hro)))
  -- Apply the forward equivalence and compare both sides in the ambient `Fin n`.
  apply e.injective
  rw [e.apply_symm_apply]
  ext
  rfl

/-- Helper for Definition 15.125.5: reindexing a block matrix whose only nonzero block is a
square Smith diagonal produces the padded rectangular Smith diagonal. -/
lemma smithNormalDiagonal_sum_reindex_eq [CommRing R] {k n m : ℕ} (a : Fin k → R) :
    Matrix.reindex (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n))
        (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k + m))
        (Matrix.fromBlocks
          (Matrix.smithNormalDiagonal (n := k) (m := k)
            (fun i ↦ a ⟨i.1, by simpa using i.2⟩))
          0 0 0) =
      Matrix.smithNormalDiagonal (n := k + n) (m := k + m)
        (fun i ↦ if hi : i.1 < k then a ⟨i.1, hi⟩ else 0) := by
  -- Compute in block coordinates first, then read the result back on `Fin (k + n)` and
  -- `Fin (k + m)` using the standard sum equivalences.
  ext i j
  refine Fin.addCases ?_ ?_ i
  · intro i'
    refine Fin.addCases ?_ ?_ j
    · intro j'
      -- In the active square block, both sides reduce to the same diagonal entry.
      by_cases hij : (i' : ℕ) = j'
      · have hik : (i' : ℕ) < k + Nat.min n m := by
          exact lt_of_lt_of_le i'.2 (Nat.le_add_right k (Nat.min n m))
        have hjk : (j' : ℕ) < k := by
          simpa [hij] using i'.2
        have hlt : ¬ k + Nat.min n m ≤ (j' : ℕ) := by
          exact Nat.not_le_of_lt (lt_of_lt_of_le hjk (Nat.le_add_right k (Nat.min n m)))
        simp [Matrix.reindex_apply, Matrix.smithNormalDiagonal, hij, hlt]
      · simp [Matrix.reindex_apply, Matrix.smithNormalDiagonal, hij]
    · intro j'
      -- The top-right block is zero, and the padded diagonal also vanishes off the diagonal.
      have hneq : ¬ (i' : ℕ) = k + j' := by
        intro hij
        have hk : k ≤ (i' : ℕ) := by
          simpa [hij] using Nat.le_add_right k (j' : ℕ)
        exact (Nat.not_lt_of_ge hk) i'.2
      simp [Matrix.reindex_apply, Matrix.smithNormalDiagonal, hneq]
  · intro i'
    refine Fin.addCases ?_ ?_ j
    · intro j'
      -- The bottom-left block is zero for the same reason.
      have hneq : ¬ k + i' = (j' : ℕ) := by
        intro hij
        have hk : k ≤ (j' : ℕ) := by
          simpa [hij] using Nat.le_add_right k (i' : ℕ)
        exact (Nat.not_lt_of_ge hk) j'.2
      simp [Matrix.reindex_apply, Matrix.smithNormalDiagonal, hneq]
    · intro j'
      -- In the bottom-right block, the padded coefficient function is already zero.
      have hnot : ¬ (k + i' : ℕ) < k := by
        exact Nat.not_lt_of_ge (Nat.le_add_right k (i' : ℕ))
      simp [Matrix.reindex_apply, Matrix.smithNormalDiagonal, hnot]

/-- Helper for Definition 15.125.5: the Smith basis on the range together with a basis of
`f.rangeRestrict.ker` gives a sum-indexed block matrix whose only nonzero block is the Smith
diagonal on the range. -/
lemma split_rangeRestrict_ker_basis_toMatrix_eq_fromBlocks [IsPrincipalIdealRing R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) :
    ∃ r k, ∃ hro : r ≤ n, ∃ hsum : r + k = m, ∃ a : Fin r → R,
      ∃ bcodSum : Module.Basis (Fin r ⊕ Fin (n - r)) R (Fin n → R),
      ∃ bdomSum : Module.Basis (Fin r ⊕ Fin k) R (Fin m → R),
        LinearMap.toMatrix bdomSum bcodSum
          (Matrix.toLin (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) A) =
            Matrix.fromBlocks
              (Matrix.smithNormalDiagonal (n := r) (m := r)
                (fun i ↦ a ⟨i.1, by simpa using i.2⟩))
              0 0 0 := by
  -- Route correction: build the split basis first, so the remaining proof is only the concrete
  -- block-matrix computation against those chosen bases.
  let f : (Fin m → R) →ₗ[R] (Fin n → R) :=
    Matrix.toLin (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) A
  obtain ⟨r, o, hro, btop, brange, a, hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_le (Pi.basisFun R (Fin n)) f.range ⊤ le_top
  have ho : o = n := by
    -- Compare the finite ranks of `⊤` and the ambient free module through their chosen bases.
    have hcard :
        Fintype.card (Fin o) = Fintype.card (Fin n) := by
      calc
        Fintype.card (Fin o) = Module.finrank R ↥(⊤ : Submodule R (Fin n → R)) := by
          symm
          exact Module.finrank_eq_card_basis btop
        _ = Module.finrank R (Fin n → R) := by
          simpa using (Submodule.finrank_top :
            Module.finrank R (⊤ : Submodule R (Fin n → R)) = Module.finrank R (Fin n → R))
        _ = Fintype.card (Fin n) := Module.finrank_eq_card_basis (Pi.basisFun R (Fin n))
    simpa using hcard
  subst o
  let bcod : Module.Basis (Fin n) R (Fin n → R) :=
    btop.map (LinearEquiv.ofTop (⊤ : Submodule R (Fin n → R)) rfl)
  obtain ⟨k, bker⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin m)) f.ker
  obtain ⟨s, hs⟩ := exists_rightInverse_rangeRestrict (R := R) f
  let bker' : Module.Basis (Fin k) R ↥f.rangeRestrict.ker :=
    bker.map (rangeRestrict_ker_linearEquiv_ker (R := R) f).symm
  let splitMap : (f.range × ↥f.rangeRestrict.ker) →ₗ[R] (Fin m → R) :=
    { toFun := fun x ↦ s x.1 + x.2
      map_add' := by
        intro x y
        simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c x
        simp [smul_add] }
  let splitEquiv : (f.range × ↥f.rangeRestrict.ker) ≃ₗ[R] (Fin m → R) :=
    LinearEquiv.ofBijective splitMap
      (section_add_ker_bijective_of_rightInverse (R := R) f.rangeRestrict s hs)
  let bdomSum : Module.Basis (Fin r ⊕ Fin k) R (Fin m → R) :=
    (brange.prod bker').map splitEquiv
  have hsum : r + k = m := by
    -- The split basis spans the whole domain, so its index cardinality matches `Fin m`.
    have hcard :
        Fintype.card (Fin r ⊕ Fin k) = Fintype.card (Fin m) := by
      calc
        Fintype.card (Fin r ⊕ Fin k) = Module.finrank R (Fin m → R) := by
          symm
          exact Module.finrank_eq_card_basis bdomSum
        _ = Fintype.card (Fin m) := Module.finrank_eq_card_basis (Pi.basisFun R (Fin m))
    simpa using hcard
  let eCod :
      Fin n ≃ Fin r ⊕ Fin (n - r) :=
    (finSumFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hro)))).symm
  let bcodSum : Module.Basis (Fin r ⊕ Fin (n - r)) R (Fin n → R) :=
    bcod.reindex eCod
  refine ⟨r, k, hro, hsum, a, bcodSum, bdomSum, ?_⟩
  have hs_apply : ∀ x : f.range, f (s x) = x := by
    -- Evaluating the right-inverse identity gives the ambient formula `f (s x) = x`.
    intro x
    have h :=
      congrArg (fun g : ↥f.range →ₗ[R] ↥f.range => g x) hs
    exact congrArg Subtype.val (by simpa [LinearMap.comp_apply] using h)
  have hsnf' : ∀ i, (brange i : Fin n → R) = a i • bcod (Fin.castLE hro i) := by
    -- Moving the top basis along `LinearEquiv.ofTop` only unwraps the subtype coercion.
    intro i
    simpa [bcod] using hsnf i
  have hbdom_inl : ∀ j, bdomSum (Sum.inl j) = s (brange j) := by
    -- The left summand of the product basis is sent through the chosen section.
    intro j
    simp [bdomSum, splitEquiv, splitMap]
  have hbdom_inr : ∀ j, bdomSum (Sum.inr j) = ((bker' j : f.rangeRestrict.ker) : Fin m → R) := by
    -- The right summand is exactly the transported kernel basis vector.
    intro j
    simp [bdomSum, splitEquiv, splitMap]
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          -- On the active Smith block, the chosen section lands back in `f.range`.
          rw [LinearMap.toMatrix_apply, hbdom_inl, hs_apply]
          rw [hsnf' j]
          by_cases hij : i = j
          · subst hij
            have hcoord :
                (bcodSum.repr (bcod (Fin.castLE hro i))) (Sum.inl i) = 1 := by
              simp [bcodSum, eCod, split_codomain_equiv_apply_castLE (hro := hro) i]
            simpa [hcoord, Matrix.fromBlocks, Matrix.smithNormalDiagonal]
          · have hcoord :
                (bcodSum.repr (bcod (Fin.castLE hro j))) (Sum.inl i) = 0 := by
              simp [bcodSum, eCod, split_codomain_equiv_apply_castLE (hro := hro) j, hij]
            have hneq : (i : ℕ) ≠ j := by
              exact fun h => hij (Fin.ext h)
            simp [Matrix.fromBlocks, Matrix.smithNormalDiagonal, hcoord, hneq]
      | inr j =>
          -- The transported kernel basis is killed by `f`, so the top-right block vanishes.
          rw [LinearMap.toMatrix_apply, hbdom_inr]
          have hker : f (((bker' j : f.rangeRestrict.ker) : Fin m → R)) = 0 := by
            exact congrArg Subtype.val (LinearMap.mem_ker.mp (bker' j).property)
          rw [hker]
          simp [Matrix.fromBlocks]
  | inr i =>
      cases j with
      | inl j =>
          -- The range basis has no coordinates on the complementary codomain block.
          rw [LinearMap.toMatrix_apply, hbdom_inl, hs_apply]
          rw [hsnf' j]
          have hcoord :
              (bcodSum.repr (bcod (Fin.castLE hro j))) (Sum.inr i) = 0 := by
            simp [bcodSum, eCod, split_codomain_equiv_apply_castLE (hro := hro) j]
          simp [Matrix.fromBlocks, hcoord]
      | inr j =>
          -- The bottom-right block is also zero because `f` kills the kernel summand.
          rw [LinearMap.toMatrix_apply, hbdom_inr]
          have hker : f (((bker' j : f.rangeRestrict.ker) : Fin m → R)) = 0 := by
            exact congrArg Subtype.val (LinearMap.mem_ker.mp (bker' j).property)
          rw [hker]
          simp [Matrix.fromBlocks]

/-- Helper for Definition 15.125.5: a basis of the top submodule over `Fin o` has the same
cardinality as the ambient basis over `Fin n`. -/
lemma top_basis_card_eq [IsPrincipalIdealRing R] {n o : ℕ}
    (btop : Module.Basis (Fin o) R ↥(⊤ : Submodule R (Fin n → R))) : o = n := by
  -- Compare finite ranks through the chosen basis on `⊤` and the standard basis on the ambient
  -- free module.
  have hcard :
      Fintype.card (Fin o) = Fintype.card (Fin n) := by
    calc
      Fintype.card (Fin o) = Module.finrank R ↥(⊤ : Submodule R (Fin n → R)) := by
        symm
        exact Module.finrank_eq_card_basis btop
      _ = Module.finrank R (Fin n → R) := by
        simpa using (Submodule.finrank_top : Module.finrank R (⊤ : Submodule R (Fin n → R)) =
          Module.finrank R (Fin n → R))
      _ = Fintype.card (Fin n) := Module.finrank_eq_card_basis (Pi.basisFun R (Fin n))
  simpa using hcard

/-- Helper for Definition 15.125.5: the source-faithful Smith-normal-form step first chooses
special bases on the codomain and domain for which the matrix itself is already diagonal. -/
lemma toMatrix_eq_smithNormalDiagonal_of_range_ker_split [IsPrincipalIdealRing R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) :
    ∃ bcod : Module.Basis (Fin n) R (Fin n → R),
      ∃ bdom : Module.Basis (Fin m) R (Fin m → R),
      ∃ d : Fin (Nat.min n m) → R,
        LinearMap.toMatrix bdom bcod
          (Matrix.toLin (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) A) =
            Matrix.smithNormalDiagonal d := by
  -- Route correction: isolate the range-plus-kernel decomposition as a basis-valued statement
  -- before converting those basis changes into explicit unit matrices.
  obtain ⟨r, k, hro, hsum, a, bcodSum, bdomSum, hblock⟩ :=
    split_rangeRestrict_ker_basis_toMatrix_eq_fromBlocks (R := R) A
  let eCod :
      Fin r ⊕ Fin (n - r) ≃ Fin n :=
    finSumFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hro)))
  let eDom : Fin r ⊕ Fin k ≃ Fin m :=
    finSumFinEquiv.trans (Equiv.cast (congrArg Fin hsum))
  let bcod : Module.Basis (Fin n) R (Fin n → R) :=
    bcodSum.reindex eCod
  let bdom : Module.Basis (Fin m) R (Fin m → R) :=
    bdomSum.reindex eDom
  let d : Fin (Nat.min n m) → R :=
    fun i ↦ if hi : i.1 < r then a ⟨i.1, hi⟩ else 0
  refine ⟨bcod, bdom, d, ?_⟩
  -- TODO: reindex the verified split-basis block matrix back to the ambient `Fin n`/`Fin m`
  -- coordinates using `linearMap_toMatrix_reindex_eq`, then close the goal with
  -- `smithNormalDiagonal_sum_reindex_cast_eq`.
  sorry

/-- Helper for Definition 15.125.5: over a principal ideal domain, every finite matrix is already
equivalent to some rectangular Smith diagonal before imposing the divisibility chain. -/
lemma matrix_has_smith_diagonal_of_isPrincipalIdealRing [IsPrincipalIdealRing R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) :
    ∃ U : (Matrix (Fin n) (Fin n) R)ˣ, ∃ V : (Matrix (Fin m) (Fin m) R)ˣ,
      ∃ d : Fin (Nat.min n m) → R,
        (((U : Matrix (Fin n) (Fin n) R) * A) * (V : Matrix (Fin m) (Fin m) R)) =
          Matrix.smithNormalDiagonal d := by
  obtain ⟨bcod, bdom, d, hdiag⟩ :=
    toMatrix_eq_smithNormalDiagonal_of_range_ker_split (R := R) A
  let U : (Matrix (Fin n) (Fin n) R)ˣ :=
    @unitOfInvertible _ _ (bcod.toMatrix (Pi.basisFun R (Fin n)))
      (Module.Basis.invertibleToMatrix bcod (Pi.basisFun R (Fin n)))
  let V : (Matrix (Fin m) (Fin m) R)ˣ :=
    @unitOfInvertible _ _ ((Pi.basisFun R (Fin m)).toMatrix bdom)
      (Module.Basis.invertibleToMatrix (Pi.basisFun R (Fin m)) bdom)
  refine ⟨U, V, d, ?_⟩
  -- Convert the diagonal matrix from the special Smith bases back to the standard coordinate
  -- bases by inserting the corresponding change-of-basis matrices.
  have hbase :
      ((Pi.basisFun R (Fin n)).toMatrix bcod *
          LinearMap.toMatrix bdom bcod
            (Matrix.toLin (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) A) *
          bdom.toMatrix (Pi.basisFun R (Fin m))) =
        A := by
    simpa using
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        (b := Pi.basisFun R (Fin m)) (b' := bdom) (c := Pi.basisFun R (Fin n)) (c' := bcod)
        (f := Matrix.toLin (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) A))
  -- The chosen units are inverse change-of-basis matrices, so associativity collapses the extra
  -- factors and leaves precisely the Smith diagonal.
  rw [← hbase, hdiag]
  calc
    ((↑U * ((Pi.basisFun R (Fin n)).toMatrix bcod * Matrix.smithNormalDiagonal d *
        bdom.toMatrix (Pi.basisFun R (Fin m)))) * ↑V) =
        bcod.toMatrix (Pi.basisFun R (Fin n)) *
          (((Pi.basisFun R (Fin n)).toMatrix bcod * Matrix.smithNormalDiagonal d) *
            (bdom.toMatrix (Pi.basisFun R (Fin m)) *
              (Pi.basisFun R (Fin m)).toMatrix bdom)) := by
      simp [U, V, Matrix.mul_assoc]
    _ = bcod.toMatrix (Pi.basisFun R (Fin n)) *
          ((Pi.basisFun R (Fin n)).toMatrix bcod * Matrix.smithNormalDiagonal d) := by
      rw [Module.Basis.toMatrix_mul_toMatrix_flip (b := bdom) (b' := Pi.basisFun R (Fin m))]
      simp
    _ = Matrix.smithNormalDiagonal d := by
      rw [← Matrix.mul_assoc,
        Module.Basis.toMatrix_mul_toMatrix_flip (b := bcod) (b' := Pi.basisFun R (Fin n))]
      simp

/-- Helper for Definition 15.125.5: a rectangular Smith diagonal can be refined to one whose
diagonal entries form a divisibility chain. -/
lemma smith_diagonal_refines_to_divisibility_chain [IsPrincipalIdealRing R] {n m : ℕ}
    (d : Fin (Nat.min n m) → R) :
    ∃ U : (Matrix (Fin n) (Fin n) R)ˣ, ∃ V : (Matrix (Fin m) (Fin m) R)ˣ,
      ∃ d' : Fin (Nat.min n m) → R,
        (((U : Matrix (Fin n) (Fin n) R) * Matrix.smithNormalDiagonal d) *
            (V : Matrix (Fin m) (Fin m) R)) =
          Matrix.smithNormalDiagonal d' ∧
        List.IsChain (· ∣ ·) (List.ofFn d') := by
  -- Route correction: after the structural diagonalization, the remaining source-faithful task is
  -- the recursive gcd-head sweep that refines successive diagonal pairs to a divisibility chain.
  -- TODO: normalize the active square block with `smithNormalDiagonal_sum_reindex_eq`, perform
  -- the block-lifted Bézout head sweep, recurse on the tail quotients, and then restore the
  -- rectangular padding.
  sorry

-- Proof sketch: over a principal ideal domain, Smith normal form supplies the required
-- diagonalization data, and its diagonal coefficients satisfy the standard divisibility chain.
/-- Every principal ideal domain is an elementary divisor domain. -/
instance isElementaryDivisorDomain_of_isPrincipalIdealRing
    [IsPrincipalIdealRing R] : IsElementaryDivisorDomain R := by
  constructor
  intro n m A
  obtain ⟨U₁, V₁, d, hdiag⟩ := matrix_has_smith_diagonal_of_isPrincipalIdealRing (R := R) A
  obtain ⟨U₂, V₂, d', hrefine, hchain⟩ :=
    smith_diagonal_refines_to_divisibility_chain (R := R) (n := n) (m := m) d
  refine ⟨U₂ * U₁, V₁ * V₂, d', ?_, hchain⟩
  -- The source-faithful proof has two stages, and they compose by associativity of matrix
  -- multiplication.
  calc
    ((((U₂ * U₁ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * A) *
          (((V₁ * V₂ : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R))) =
        (((U₂ : Matrix (Fin n) (Fin n) R) * Matrix.smithNormalDiagonal d) *
          (V₂ : Matrix (Fin m) (Fin m) R)) := by
      rw [← hdiag]
      simp [Matrix.mul_assoc]
    _ = Matrix.smithNormalDiagonal d' := hrefine

end
