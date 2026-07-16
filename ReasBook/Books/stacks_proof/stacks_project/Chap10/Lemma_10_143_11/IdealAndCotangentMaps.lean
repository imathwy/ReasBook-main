import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_143_10
import stacks_proof.stacks_project.Chap10.Proposition_10_138_13

-- Declarations moved out of `Lemma_10_143_11.lean` to keep the active proof file small.

open scoped TensorProduct

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- Helper for Lemma 10.143.11: a commuting comparison map sends the source kernel into the
target kernel. -/
lemma mapsTo_ker_of_comp_eq
    {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hcomp : qB.comp φ = qC) :
    Set.MapsTo φ (ker qC) (ker qB) := by
  intro x hx
  -- Evaluate the commuting square at `x` to transport the vanishing condition.
  have hx0 : qC x = 0 := by
    simpa [RingHom.mem_ker] using hx
  change qB (φ x) = 0
  have hpoint := congrArg (fun h : C →+* B₀ ↦ h x) hcomp
  simpa [RingHom.comp_apply, hx0] using hpoint

/-- Helper for Lemma 10.143.11: the induced map on kernels of a commuting square. -/
def kernel_restrict
    {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hcomp : qB.comp φ = qC) :
    ker qC → ker qB :=
  Subtype.map φ (mapsTo_ker_of_comp_eq (qC := qC) (qB := qB) (φ := φ) hcomp)

/-- Helper for Lemma 10.143.11: if `φ.comp f = g`, then `φ` sends the mapped ideal `f(I)` into the
mapped ideal `g(I)`. -/
lemma mapsTo_ideal_map_of_comp_eq
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {f : R →+* S} {g : R →+* T} {φ : S →+* T} (I : Ideal R)
    (hcomp : φ.comp f = g) :
    Set.MapsTo φ (Ideal.map f I) (Ideal.map g I) := by
  intro x hx
  -- Map first into `Ideal.map φ (Ideal.map f I)`, then rewrite the composite ideal map.
  have hx' : φ x ∈ Ideal.map φ (Ideal.map f I) := Ideal.mem_map_of_mem φ hx
  simpa [Ideal.map_map, hcomp] using hx'

/-- Helper for Lemma 10.143.11: the explicit comparison map on the textbook ideals `IC → J`. -/
def ideal_map_restrict
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    (f : R →+* S) (g : R →+* T) (φ : S →+* T) (I : Ideal R)
    (hcomp : φ.comp f = g) :
    Ideal.map f I → Ideal.map g I :=
  Subtype.map φ (mapsTo_ideal_map_of_comp_eq (I := I) hcomp)

/-- Helper for Lemma 10.143.11: the textbook ideal comparison `f(I) → g(I)` defines the expected
inclusion into the codomain ideal. -/
lemma ideal_map_le_comap_of_comp_eq
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    (f : R →+* S) (g : R →+* T) (φ : S →+* T) (I : Ideal R)
    (hcomp : φ.comp f = g) :
    Ideal.map f I ≤ Ideal.comap φ (Ideal.map g I) := by
  intro x hx
  -- The explicit ideal comparison lands in the target mapped ideal by construction.
  exact mapsTo_ideal_map_of_comp_eq (I := I) hcomp hx

/-- Helper for Lemma 10.143.11: injectivity of the cotangent map for the square-zero source ideal
forces injectivity of the textbook ideal comparison `f(I) → g(I)`. -/
lemma ideal_map_restrict_injective_of_mapCotangent_injective
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    [Algebra R S] [Algebra R T]
    {I : Ideal R} {φ : S →+* T}
    (hcomp : φ.comp (algebraMap R S) = algebraMap R T)
    (hSrcSq : (Ideal.map (algebraMap R S) I) ^ 2 = ⊥)
    (hCotInj :
        Function.Injective
          (Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I)
            { toRingHom := φ
              commutes' := fun x ↦ by
                -- The cotangent comparison is built from the same commuting square `φ ∘ f = g`.
                exact congrArg (fun h : R →+* T ↦ h x) hcomp }
            (ideal_map_le_comap_of_comp_eq (algebraMap R S) (algebraMap R T) φ I hcomp))) :
    Function.Injective (ideal_map_restrict (algebraMap R S) (algebraMap R T) φ I hcomp) := by
  intro x y hxy
  let φAlg : S →ₐ[R] T :=
    { toRingHom := φ
      commutes' := fun x ↦ by
        -- Read `φ` as the `R`-algebra map determined by the commuting square.
        exact congrArg (fun h : R →+* T ↦ h x) hcomp }
  have hle : Ideal.map (algebraMap R S) I ≤ Ideal.comap φAlg (Ideal.map (algebraMap R T) I) :=
    ideal_map_le_comap_of_comp_eq (algebraMap R S) (algebraMap R T) φ I hcomp
  have hcot_eq :
      Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I) φAlg hle
          ((Ideal.map (algebraMap R S) I).toCotangent x) =
        Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I) φAlg hle
          ((Ideal.map (algebraMap R S) I).toCotangent y) := by
    -- The cotangent map records exactly the same underlying image equality as `ideal_map_restrict`.
    simpa [φAlg, ideal_map_restrict] using
      congrArg (Ideal.toCotangent (Ideal.map (algebraMap R T) I)) hxy
  have hsrc_eq :
      (Ideal.map (algebraMap R S) I).toCotangent x =
        (Ideal.map (algebraMap R S) I).toCotangent y := hCotInj hcot_eq
  have hsub_mem : ((x : Ideal.map (algebraMap R S) I) : S) - y ∈ (Ideal.map (algebraMap R S) I) ^ 2 := by
    exact (Ideal.toCotangent_eq (Ideal.map (algebraMap R S) I)).mp hsrc_eq
  have hsub_zero : ((x : Ideal.map (algebraMap R S) I) : S) - y = 0 := by
    rw [hSrcSq] at hsub_mem
    simpa using hsub_mem
  -- Square-zero makes equality on cotangent classes equivalent to equality of ideal elements.
  apply Subtype.ext
  exact sub_eq_zero.mp hsub_zero

/-- Helper for Lemma 10.143.11: if `ker qB` is the image of the square-zero ideal `ker qA`, then
`ker qB` is square-zero as well. -/
lemma ker_square_zero_of_ker_eq_map
    (hSq : (ker qA) ^ 2 = ⊥)
    (hker : ker qB = (ker qA).map g) :
    (ker qB) ^ 2 = ⊥ := by
  -- The kernel comparison lets us transport the square-zero relation through `Ideal.map`.
  rw [hker]
  simpa [Ideal.map_pow] using congrArg (Ideal.map g) hSq

/-- Helper for Lemma 10.143.11: in a commuting square, every element killed by the comparison map
already lies in the source square-zero ideal once the source kernel is identified with `f(I)`. -/
lemma ker_le_ideal_map_of_comp_eq_of_ker_eq
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC)
    (hSrc : RingHom.ker qC = Ideal.map c I) :
    RingHom.ker φ ≤ Ideal.map c I := by
  intro x hx
  -- Apply the commuting relation at `x`; since `φ x = 0`, the image of `x` in the quotient also
  -- vanishes, so `x` belongs to the identified source kernel `Ideal.map c I`.
  have hxq : x ∈ RingHom.ker qC := by
    rw [RingHom.mem_ker] at hx ⊢
    have hpoint := congrArg (fun h : C →+* B₀ ↦ h x) hq
    simpa [RingHom.comp_apply, hx] using hpoint.symm
  simpa [hSrc] using hxq

/-- Helper for Lemma 10.143.11: once the source and target quotient kernels are identified with the
textbook ideals, the target ideal pulled back along the comparison map is exactly the source
ideal. -/
lemma ideal_comap_eq_of_comp_eq_of_ker_eq
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I) :
    Ideal.comap φ (Ideal.map g I) = Ideal.map c I := by
  ext x
  constructor
  · intro hx
    -- Rewrite membership in the pulled-back target ideal as vanishing in the target quotient.
    have hxker : φ x ∈ RingHom.ker qB := by
      simpa [hTgt] using hx
    have hpoint := congrArg (fun h : C →+* B₀ ↦ h x) hq
    have hx0 : qC x = 0 := by
      rw [RingHom.mem_ker] at hxker
      calc
        qC x = qB (φ x) := by simpa [RingHom.comp_apply] using hpoint.symm
        _ = 0 := hxker
    have : x ∈ RingHom.ker qC := by
      simpa [RingHom.mem_ker] using hx0
    simpa [hSrc] using this
  · intro hx
    have hxker : x ∈ RingHom.ker qC := by
      simpa [hSrc] using hx
    have hpoint := congrArg (fun h : C →+* B₀ ↦ h x) hq
    have hx0 : qB (φ x) = 0 := by
      rw [RingHom.mem_ker] at hxker
      calc
        qB (φ x) = qC x := by simpa [RingHom.comp_apply] using hpoint
        _ = 0 := hxker
    have : φ x ∈ RingHom.ker qB := by
      simpa [RingHom.mem_ker] using hx0
    simpa [hTgt] using this

/-- Helper for Lemma 10.143.11: if the comparison kernel already lies in the source textbook
ideal, then the pullback of the target textbook ideal has the kernel-sup form needed by the
surjective cotangent-kernel theorem. -/
lemma ideal_comap_eq_ker_sup_of_comp_eq_of_ker_eq
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (hkerφ_le : RingHom.ker φ ≤ Ideal.map c I) :
    Ideal.comap φ (Ideal.map g I) = RingHom.ker φ ⊔ Ideal.map c I := by
  -- The explicit pullback ideal is already the source ideal, so adjoining `ker φ` does nothing.
  calc
    Ideal.comap φ (Ideal.map g I) = Ideal.map c I :=
      ideal_comap_eq_of_comp_eq_of_ker_eq (I := I) (c := c) (g := g) hq hSrc hTgt
    _ = RingHom.ker φ ⊔ Ideal.map c I := by
      exact (sup_eq_right.mpr hkerφ_le).symm

/-- Helper for Lemma 10.143.11: an idempotent ideal contained in a square-zero ideal must be
zero. -/
lemma eq_bot_of_isIdempotentElem_of_le_square_zero
    {R : Type*} [CommRing R] {J K : Ideal R}
    (hJ : IsIdempotentElem J) (hJK : J ≤ K) (hK : K ^ 2 = ⊥) :
    J = ⊥ := by
  -- Replace the idempotent ideal by its square and compare it with the ambient square-zero ideal.
  apply le_antisymm
  · calc
      J = J ^ 2 := by simpa [pow_two] using hJ.symm
      _ ≤ K ^ 2 := by
            rw [pow_two, Ideal.mul_le]
            intro r hr s hs
            simpa [pow_two] using Ideal.mul_mem_mul (hJK hr) (hJK hs)
      _ = ⊥ := hK
  · exact bot_le

/-- Helper for Lemma 10.143.11: an ideal contained in a square-zero ideal is square-zero. -/
lemma square_zero_of_le_square_zero_ideal
    {R : Type*} [CommRing R] {J K : Ideal R}
    (hJK : J ≤ K) (hK : K ^ 2 = ⊥) :
    J ^ 2 = ⊥ := by
  -- Compare the square of the smaller ideal with the square-zero ambient ideal.
  apply le_antisymm
  · calc
      J ^ 2 ≤ K ^ 2 := by
            rw [pow_two, Ideal.mul_le]
            intro r hr s hs
            simpa [pow_two] using Ideal.mul_mem_mul (hJK hr) (hJK hs)
      _ = ⊥ := by simpa [pow_two] using hK
  · exact bot_le

/-- Helper for Lemma 10.143.11: when `I² = 0`, the canonical map `I → I / I²` is a linear
equivalence. -/
noncomputable def ideal_equiv_cotangent_of_square_zero
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥) :
    I ≃ₗ[R] I.Cotangent := by
  -- For a square-zero ideal, equality in the cotangent quotient already forces equality in `I`.
  refine LinearEquiv.ofBijective (Ideal.toCotangent I) ?_
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hsub : (x : R) - y ∈ I ^ 2 := (Ideal.toCotangent_eq I).mp hxy
    rw [hI] at hsub
    exact sub_eq_zero.mp (by simpa using hsub)
  · -- Surjectivity is the standard quotient presentation of `I / I²`.
    exact Ideal.toCotangent_surjective I

/-- Helper for Lemma 10.143.11: the inverse square-zero cotangent equivalence sends a cotangent
generator back to the original ideal element. -/
lemma ideal_equiv_cotangent_of_square_zero_symm_toCotangent
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥) (x : I) :
    (ideal_equiv_cotangent_of_square_zero I hI).symm (Ideal.toCotangent I x) = x := by
  -- The square-zero equivalence is built from `Ideal.toCotangent`, so its inverse recovers generators.
  simpa [ideal_equiv_cotangent_of_square_zero] using
    (ideal_equiv_cotangent_of_square_zero I hI).symm_apply_apply x

/-- Helper for Lemma 10.143.11: when we comap an intersection with the ambient ideal along the
ideal subtype, the ambient factor is automatic. -/
lemma submodule_comap_subtype_inf_eq_comap
    {R : Type*} [CommRing R] (J K : Ideal R) :
    Submodule.comap J.subtype (K ⊓ J) = Submodule.comap J.subtype K := by
  ext x
  constructor
  · intro hx
    -- Membership in the pulled-back intersection implies membership in the pulled-back ideal.
    exact (Ideal.mem_inf.mp (Submodule.mem_comap.mp hx)).1
  · intro hx
    -- The subtype already remembers that every element lies in the ambient ideal `J`.
    exact Submodule.mem_comap.mpr <| Ideal.mem_inf.mpr ⟨Submodule.mem_comap.mp hx, x.2⟩

/-- Helper for Lemma 10.143.11: if an `R`-algebra map has the same underlying ring map as the
chosen `A`-algebra structure on `B`, then the associated cotangent map is just the owner
`A`-linear cotangent map viewed by restriction of scalars. -/
lemma mapCotangent_restrictScalars_eq_of_toRingHom_eq
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    {I₁ : Ideal A} {I₂ : Ideal B} (f : A →ₐ[R] B)
    (hf : f.toRingHom = algebraMap A B)
    (hR : I₁ ≤ Ideal.comap f I₂) (hA : I₁ ≤ Ideal.comap (algebraMap A B) I₂) :
    Ideal.mapCotangent I₁ I₂ f hR =
      (Ideal.mapCotangent I₁ I₂ (Algebra.ofId A B) hA).restrictScalars R := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I₁ x
  -- Compare the two cotangent maps on generators, where both are determined by the same ring map.
  have hx :
      (⟨f x, hR x.2⟩ : I₂) = ⟨algebraMap A B x, hA x.2⟩ := by
    apply Subtype.ext
    exact congrArg (fun g : A →+* B ↦ g x) hf
  simpa [Ideal.mapCotangent_toCotangent, hx]

/-- Helper for Lemma 10.143.11: after identifying the square-zero target ideal with its cotangent
space, `Ideal.mapCotangent` on a source generator is the textbook ideal comparison `IC → J`. -/
lemma square_zero_symm_mapCotangent_toCotangent_eq_ideal_map_restrict
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    [Algebra R S] [Algebra R T]
    {I : Ideal R} {φ : S →+* T}
    (hcomp : φ.comp (algebraMap R S) = algebraMap R T)
    (hTgtSq : (Ideal.map (algebraMap R T) I) ^ 2 = ⊥)
    (x : Ideal.map (algebraMap R S) I) :
    (ideal_equiv_cotangent_of_square_zero (Ideal.map (algebraMap R T) I) hTgtSq).symm
      (Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I)
        { toRingHom := φ
          commutes' := fun r ↦ by
            -- The cotangent comparison uses the same algebra structure as the ideal comparison.
            exact congrArg (fun h : R →+* T ↦ h r) hcomp }
        (ideal_map_le_comap_of_comp_eq (algebraMap R S) (algebraMap R T) φ I hcomp)
        (Ideal.toCotangent (Ideal.map (algebraMap R S) I) x)) =
      ideal_map_restrict (algebraMap R S) (algebraMap R T) φ I hcomp x := by
  -- Expand `Ideal.mapCotangent` on generators and then invert the square-zero cotangent equivalence.
  rw [Ideal.mapCotangent_toCotangent]
  simpa [ideal_map_restrict] using
    ideal_equiv_cotangent_of_square_zero_symm_toCotangent
      (Ideal.map (algebraMap R T) I) hTgtSq
      (ideal_map_restrict (algebraMap R S) (algebraMap R T) φ I hcomp x)


end

end RingHom
