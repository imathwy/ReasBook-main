import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Subring

section AddIdeal

variable {R : Type u} [Ring R]

/-- Helper for Theorem 1.1.53: the element `0` belongs to the carrier of `H + N`. -/
theorem addIdeal_zero_mem (H : Subring R) (N : Ideal R) [N.IsTwoSided] :
    (0 : R) ∈ ({x | ∃ h ∈ H, ∃ n ∈ N, h + n = x} : Set R) := by
  -- The zero class is represented by `0 + 0`.
  have hsum : (0 : R) + 0 = 0 := by
    simp
  exact ⟨0, H.zero_mem, 0, N.zero_mem, hsum⟩

/-- Helper for Theorem 1.1.53: the element `1` belongs to the carrier of `H + N`. -/
theorem addIdeal_one_mem (H : Subring R) (N : Ideal R) [N.IsTwoSided] :
    (1 : R) ∈ ({x | ∃ h ∈ H, ∃ n ∈ N, h + n = x} : Set R) := by
  -- The unit class is represented by `1 + 0`.
  have hsum : (1 : R) + 0 = 1 := by
    simp
  exact ⟨1, H.one_mem, 0, N.zero_mem, hsum⟩

/-- Helper for Theorem 1.1.53: the carrier of `H + N` is closed under addition. -/
theorem addIdeal_add_mem (H : Subring R) (N : Ideal R) [N.IsTwoSided] {x y : R}
    (hx : x ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R))
    (hy : y ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R)) :
    x + y ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R) := by
  rcases hx with ⟨hx', hxH, nx, hxN, rfl⟩
  rcases hy with ⟨hy', hyH, ny, hyN, rfl⟩
  -- We add the subring parts and the ideal parts separately.
  refine ⟨hx' + hy', H.add_mem hxH hyH, nx + ny, N.add_mem hxN hyN, ?_⟩
  simp [add_left_comm, add_comm]

/-- Helper for Theorem 1.1.53: the carrier of `H + N` is closed under negation. -/
theorem addIdeal_neg_mem (H : Subring R) (N : Ideal R) [N.IsTwoSided] {x : R}
    (hx : x ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R)) :
    -x ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R) := by
  rcases hx with ⟨hx', hxH, nx, hxN, rfl⟩
  -- Negation preserves both the subring part and the ideal part.
  have hnegN : -nx ∈ N := by
    simpa using N.neg_mem hxN
  refine ⟨-hx', H.neg_mem hxH, -nx, hnegN, ?_⟩
  simp [add_comm]

/-- Helper for Theorem 1.1.53: the carrier of `H + N` is closed under multiplication. -/
theorem addIdeal_mul_mem (H : Subring R) (N : Ideal R) [N.IsTwoSided] {x y : R}
    (hx : x ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R))
    (hy : y ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R)) :
    x * y ∈ ({z | ∃ h ∈ H, ∃ n ∈ N, h + n = z} : Set R) := by
  rcases hx with ⟨hx', hxH, nx, hxN, rfl⟩
  rcases hy with ⟨hy', hyH, ny, hyN, rfl⟩
  -- Expand `(hx' + nx) * (hy' + ny)` and collect the ideal-valued terms.
  have hideal :
      hx' * ny + nx * hy' + nx * ny ∈ N := by
    exact N.add_mem
      (N.add_mem (N.mul_mem_left hx' hyN) (N.mul_mem_right hy' hxN))
      (N.mul_mem_right ny hxN)
  refine ⟨hx' * hy', H.mul_mem hxH hyH, hx' * ny + nx * hy' + nx * ny, hideal, ?_⟩
  calc
    hx' * hy' + (hx' * ny + nx * hy' + nx * ny) = hx' * hy' + hx' * ny + (nx * hy' + nx * ny) := by
      simp [add_assoc]
    _ = (hx' + nx) * (hy' + ny) := by
      simp [add_mul, mul_add, add_assoc, add_left_comm]

/-- The subring `H + N` of sums `h + n` with `h ∈ H` and `n ∈ N`. -/
def addIdeal (H : Subring R) (N : Ideal R) [N.IsTwoSided] : Subring R where
  carrier := {x | ∃ h ∈ H, ∃ n ∈ N, h + n = x}
  zero_mem' := addIdeal_zero_mem H N
  one_mem' := addIdeal_one_mem H N
  add_mem' := addIdeal_add_mem H N
  neg_mem' := addIdeal_neg_mem H N
  mul_mem' := addIdeal_mul_mem H N

scoped[SubringIdeal] notation:65 H:65 " + " N:66 => Subring.addIdeal H N

open scoped SubringIdeal

@[simp] theorem mem_addIdeal {H : Subring R} {N : Ideal R} [N.IsTwoSided] {x : R} :
    x ∈ H + N ↔ ∃ h ∈ H, ∃ n ∈ N, h + n = x :=
  Iff.rfl

@[simp] theorem le_addIdeal {H : Subring R} {N : Ideal R} [N.IsTwoSided] : H ≤ H + N := by
  intro x hx
  -- Elements of `H` are represented as `x + 0`.
  have hsum : x + 0 = x := by
    simp
  exact ⟨x, hx, 0, N.zero_mem, hsum⟩

@[simp] theorem mem_addIdeal_of_mem_ideal {H : Subring R} {N : Ideal R} [N.IsTwoSided] {x : R}
    (hx : x ∈ N) : x ∈ H + N := by
  -- Elements of `N` are represented as `0 + x`.
  have hsum : (0 : R) + x = x := by
    simp
  exact ⟨0, H.zero_mem, x, hx, hsum⟩

end AddIdeal

end Subring

open scoped SubringIdeal

section SubringCorrespondence

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (φ : R →+* S)

/- Theorem 1.1.53 (1): for a surjective ring homomorphism, pulling back a subring of the target
along the homomorphism and then mapping it forward recovers the original subring. -/
#check Subring.map_comap_eq_self_of_surjective

-- Proof sketch: use `Subring.comap_map_eq_self` and the hypothesis that the kernel lies in `H`.
/- Theorem 1.1.53 (2): if a subring contains the kernel, then mapping it forward and pulling it
back recovers the original subring. -/
recall Subring.comap_map_eq_self {R : Type u} {S : Type v} [NonAssocRing R] [NonAssocRing S]
    {f : R →+* S} {s : Subring R} (h : f ⁻¹' {0} ⊆ s) : (s.map f).comap f = s

/- Theorem 1.1.53 (3): under a surjective ring homomorphism, extension and contraction induce the
canonical correspondence between ideals of the target and ideals of the source containing
`ker φ`. -/
#check Ideal.relIsoOfSurjective

end SubringCorrespondence

section IdealQuotients

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (φ : R →+* S)
variable (H : Ideal R) [H.IsTwoSided]

-- Proof sketch: the induced quotient map is always the canonical map
-- `Ideal.quotientMap (Ideal.map φ H) φ Ideal.le_comap_map`; surjectivity comes from
-- `Ideal.quotientMap_surjective`, and injectivity follows from
-- `Ideal.comap_map_of_surjective φ φ.surjective = H ⊔ RingHom.ker φ` together with
-- `RingHom.ker φ ≤ H`.
/-- Theorem 1.1.53 (4): if `H` contains `ker φ`, then the canonical map
`R ⧸ H →+* S ⧸ Ideal.map φ H` is bijective. -/
theorem quotientMap_bijective_of_surjective [RingHomSurjective φ] (hH : RingHom.ker φ ≤ H) :
    Function.Bijective (Ideal.quotientMap (Ideal.map φ H) φ Ideal.le_comap_map) := by
  constructor
  · refine Ideal.quotientMap_injective' ?_
    rw [Ideal.comap_map_of_surjective φ φ.surjective]
    exact sup_le le_rfl hH
  · exact Ideal.quotientMap_surjective φ.surjective

end IdealQuotients

section SubringSecondIsomorphism

variable {R : Type u} [Ring R]
variable (H : Subring R) (N : Ideal R) [N.IsTwoSided]

-- Proof sketch: the kernel of `H → R ⧸ N` is the preimage of `N` under the subtype map
-- `H ↪ R`, which is exactly the ideal-theoretic intersection `H ∩ N`.
/-- Theorem 1.1.53 (5): for a subring `H` and an ideal `N`, the kernel of the composite
`H →+* R →+* R ⧸ N` is the ideal `H ∩ N`, represented in Lean as `Ideal.comap H.subtype N`. -/
theorem ker_subringToQuotient_eq_comap :
    RingHom.ker (((Ideal.Quotient.mk N).comp H.subtype) : H →+* R ⧸ N) =
      Ideal.comap H.subtype N := by
  -- The kernel of the quotient map is `N`, so pulling it back along `H ↪ R` gives `H ∩ N`.
  simpa [Ideal.mk_ker] using (RingHom.comap_ker (Ideal.Quotient.mk N) H.subtype).symm

/-- Helper for Theorem 1.1.53: the canonical inclusion of `H` into `H + N`. -/
def subringToAddIdeal : H →+* (H + N) :=
  Subring.inclusion (Subring.le_addIdeal (H := H) (N := N))

/-- Helper for Theorem 1.1.53: the canonical map from `H` to `(H + N) / N`. -/
def subringToAddIdealQuotient :
    H →+* (H + N) ⧸ Ideal.comap (H + N).subtype N :=
  (Ideal.Quotient.mk (Ideal.comap (H + N).subtype N)).comp (subringToAddIdeal H N)

/-- Helper for Theorem 1.1.53: every class in `(H + N) / N` has a representative from `H`. -/
theorem subring_to_addIdeal_quotient_surjective :
    Function.Surjective (subringToAddIdealQuotient H N) := by
  intro z
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
  rcases x.2 with ⟨h, hh, n, hn, hxn⟩
  refine ⟨⟨h, hh⟩, ?_⟩
  -- Replace the quotient representative `x` by the textbook decomposition `h + n`.
  have hmem : h + n ∈ H + N := by
    exact ⟨h, hh, n, hn, rfl⟩
  have hx : x = ⟨h + n, hmem⟩ := by
    ext
    exact hxn.symm
  rw [hx]
  dsimp [subringToAddIdealQuotient]
  refine (Ideal.Quotient.eq (I := Ideal.comap (H + N).subtype N)
    (x := (subringToAddIdeal H N ⟨h, hh⟩))
    (y := ⟨h + n, hmem⟩)).2 ?_
  -- The difference is `-n`, which lies in `N`.
  change (h - (h + n) : R) ∈ N
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using N.neg_mem hn

/-- Helper for Theorem 1.1.53: the kernel of `H → (H + N) / N` is `H ∩ N`. -/
theorem ker_subringToAddIdealQuotient_eq_comap :
    RingHom.ker (subringToAddIdealQuotient H N) = Ideal.comap H.subtype N := by
  -- The quotient kernel is pulled back first along `H ↪ H + N` and then along `(H + N) ↪ R`.
  dsimp [subringToAddIdealQuotient, subringToAddIdeal]
  rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_comap]
  rfl

/-- Helper for Theorem 1.1.53: the second isomorphism theorem follows from the surjective
map `H → (H + N) / N` and its kernel computation. -/
noncomputable def quotientInfEquivAddIdealQuotientAux :
    H ⧸ Ideal.comap H.subtype N ≃+* (H + N) ⧸ Ideal.comap (H + N).subtype N :=
  -- Route correction: keep the exported `def` proof-free.
  -- Package the quotient argument once as a term-level equivalence.
  (Ideal.quotEquivOfEq (ker_subringToAddIdealQuotient_eq_comap (H := H) (N := N)).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (subring_to_addIdeal_quotient_surjective (H := H) (N := N))
    )

/-- Theorem 1.1.53 (6): the second isomorphism theorem for a subring `H` and an ideal `N`,
stated as the canonical ring isomorphism `H / (H ∩ N) ≃ (H + N) / N`. -/
noncomputable def quotientInfEquivAddIdealQuotient :
    H ⧸ Ideal.comap H.subtype N ≃+* (H + N) ⧸ Ideal.comap (H + N).subtype N :=
  quotientInfEquivAddIdealQuotientAux H N

end SubringSecondIsomorphism
