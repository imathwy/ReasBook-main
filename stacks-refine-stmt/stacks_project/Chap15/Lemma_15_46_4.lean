import stacks_project.Chap15.Definition_15_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open KaehlerDifferential
open scoped FrobeniusSubfield

universe u v w

section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]

local instance : Algebra (ZMod p) K := ZMod.algebra K p

variable {A : Type v} (Kα : A → Subfield K)

private instance instSMulSubfield (k : Subfield K) : SMul (ZMod p) k :=
  (inferInstance : Algebra (ZMod p) k).toSMul

private theorem coe_algebraMap_zmod_subfield (k : Subfield K) (x : ZMod p) :
    (((algebraMap (ZMod p) k) x : k) : K) = algebraMap (ZMod p) K x :=
  congrArg (fun f : ZMod p →+* K ↦ f x)
    (RingHom.ext_zmod ((algebraMap k K).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) K))

private theorem coe_zmod_smul_subfield (k : Subfield K) (x : ZMod p) (y : k) :
    ((x • y : k) : K) = x • (y : K) := by
  simpa [Algebra.smul_def] using
    congrArg (fun z : K ↦ z * (y : K)) (coe_algebraMap_zmod_subfield k x)

private instance instIsScalarTowerSubfield (k : Subfield K) : IsScalarTower (ZMod p) k K where
  smul_assoc x y z := by
    change (((x • y : k) : K) * z) = x • y • z
    rw [coe_zmod_smul_subfield k x y]
    exact smul_mul_assoc x (y : K) z

local notation "kaehlerDifferentialMapTo" α =>
  @KaehlerDifferential.map (ZMod p) (Kα α) _ _
    (inferInstance : Algebra (ZMod p) (Kα α)) K K _ _
    (inferInstance : Algebra (ZMod p) K) (inferInstance : Algebra K K)
    (inferInstance : Algebra (Kα α) K) (inferInstance : Algebra (ZMod p) K)
    (inferInstance : IsScalarTower (ZMod p) K K) (instIsScalarTowerSubfield (Kα α))
    (inferInstance : SMulCommClass (Kα α) K K)

/-
Domain triage:
* primary domain: fields of characteristic `p`, Frobenius subfields, and the canonical
  Kähler-differential maps induced by `𝔽_p ⊆ K_α ⊆ K`, together with the chapter owner
  `pPowerCompositum` for the compositum `L^p K_α`;
* sampled owner declarations:
  - `frobeniusSubfield`,
  - `pPowerCompositum`,
  - `KaehlerDifferential.map`,
  - `Subfield.map`,
  - `Subfield.mem_iInf`;
* best owner abstraction: the primitive owner data are the family of subfields `Kα` and the
  canonical owner map `KaehlerDifferential.map (ZMod p) k K K`; the
  intersection-of-kernels and
  Frobenius-compositum statements are derived API, with the latter expressed through
  `pPowerCompositum` rather than a parallel raw `⊔`/`Subfield.map` spelling;
* layer triage:
  - `source-facing`: the two clauses of Lemma `15.46.4`;
  - `core/canonical`: `K^[p]`, `pPowerCompositum`, `KaehlerDifferential.map`, and the
    lattice operations on subfields;
  - `bridge/view`: no extra bridge owner is needed beyond the reusable comparison-map owner
  above; the source-facing statements use it together with `pPowerCompositum`.
-/

-- Proof sketch: choose a `p`-basis of `K` over `𝔽_p` using Lemma `15.46.2`, identify an element of
-- the intersection of all kernels with a finite linear relation over every `K_α`, and apply the
-- directed-intersection criterion of Lemma `15.46.3` to force the coefficients into `K^p`, where
-- Lemma `15.46.2` rules out any nontrivial relation.
/-- Lemma 15.46.4 (1): if the subfields `K_α` intersect in `K^p` and are downward directed as a
nonempty family, then the intersection of the kernels of the canonical maps
`Ω[K⁄𝔽_p] → Ω[K⁄K_α]` is zero. -/
theorem iInf_ker_kaehlerDifferentialMap_eq_bot
    (h_nonempty : Nonempty A) (h_inter : K^[p] = ⨅ α, Kα α) (h_directed : Directed (· ≥ ·) Kα) :
    (⨅ α, LinearMap.ker (kaehlerDifferentialMapTo α)) = ⊥ := by
  sorry

-- Proof sketch: reduce along intermediate fields to the primitive-extension case, then treat the
-- separable and purely inseparable degree-`p` cases separately. In each case, a basis of `L` over
-- `K` adapted to a primitive generator shows that intersecting the composita `L^p K_α` recovers
-- exactly `L^p` because the coefficients intersect back to `K^p`.
section FiniteExtension

variable {L : Type w} [Field L] [Algebra K L] [FiniteDimensional K L] [CharP L p]

/-- Lemma 15.46.4 (2): for every finite extension `L / K` over a field `K` of characteristic `p`,
the `p`-th-power subfield `L^p` is the
intersection of the composita `L^p K_α` inside `L` for a downward directed family `(K_α)` with
intersection `K^p`. -/
theorem frobeniusSubfield_eq_iInf_pPowerCompositum_of_finiteExtension
    (h_inter : K^[p] = ⨅ α, Kα α) (h_directed : Directed (· ≥ ·) Kα) :
    L^[p] = ⨅ α, (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
  sorry

end FiniteExtension

end
