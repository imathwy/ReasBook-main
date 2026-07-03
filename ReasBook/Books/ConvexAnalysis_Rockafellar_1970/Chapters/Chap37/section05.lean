

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_37_5_1 (from Chap07) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable {YU : Type*} {YV : Type*}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 37.5.1 says that for a closed proper concave-convex saddle-function
  `K`, the graph of its saddle subdifferential `dK` is closed and is homeomorphic to the ambient
  product space under the map `(u, v, u⋆, v⋆) ↦ (u - u⋆, v + v⋆)`.
- `core/canonical`: graph-valued multivalued mappings in the project are organized as `SetRel`,
  while the saddle subdifferential owner itself is already `Bifunction.subdifferentialAt` from
  Chapter 35.
- `bridge/view`: this file therefore adds a pairing-level graph owner
  `Bifunction.subdifferentialGraphPairing K : SetRel (U × V) (YU × YV)` and its notation surface
  `gphd[YU, YV](K)`, and states the corollary directly on that owner layer instead of
  introducing a second packaged saddle-mapping wrapper.

Domain-style sampling used here:
- `Bifunction.subdifferentialAt` and `Bifunction.mem_subdifferentialAt` from
  `Chap07.Text_35_6_3`;
- `Function.subdifferentialGraph` from `Chap05.Definition_5_24_3`, which fixes `SetRel` as the
  canonical graph owner layer for subdifferentials;
- `Function.isClosed_subdifferentialGraph` from `Chap05.Theorem_5_24_7`, the upstream closed-graph
  owner theorem in the pure convex setting;
- `SaddleFunction.IsConcaveConvex`, `SaddleFunction.IsClosed`, and
  `SaddleFunction.IsProper`, which are the chapter's primitive owner-level hypotheses at codomain
  layer `WithTopBot`.

Primitive data vs derived API:
- primitive owner reused from upstream: `Bifunction.subdifferentialAt K u v`;
- derived bridge API introduced here: the graph relation
  `Bifunction.subdifferentialGraphPairing K`, its pointwise membership lemma, and the explicit
  Minty map on the self-pairing specialization `gphd[U, V](K)`;
- derived source-facing conclusions: graph closedness and the homeomorphism theorem for the
  textbook Minty-style coordinate map.

Layer target: `bridge/view`.

Ambient-assumption minimization:
- the graph relation and its pointwise membership theorem live exactly at the ambient layer of the
  existing owner `Bifunction.subdifferentialAt`, so they stay on the intrinsic pairing-based
  layer;
- the self-pairing specialization `gphd[U, V](K)` and the explicit Minty map below stay at the
  same pairing-level scalar layer as `subdifferentialGraphPairing`;
- the closed-graph clause is first stated on the pairing-level owner
  `subdifferentialGraphPairing` and only then specialized to the self-pairing specialization
  `gphd[U, V](K)`, while the Minty-homeomorphism clause remains on the explicit self-pairing map
  where subtraction/addition is intrinsically typed.
-/

/-- The graph of the saddle subdifferential, expressed on the chapter's canonical `SetRel`
owner layer for multivalued mappings. -/
abbrev subdifferentialGraphPairing (K : U → V → WithTopBot 𝕜) : SetRel (U × V) (YU × YV) :=
  {p | p.2 ∈ d(K ; p.1.1, p.1.2)}

scoped[Rockafellar] notation "gphd[" YU ", " YV "](" K ")" =>
  Bifunction.subdifferentialGraphPairing (YU := YU) (YV := YV) K

/-- Pointwise membership in the graph of the saddle subdifferential is exactly membership of the
second pair in `d(K ; u, v)`. -/
@[simp] theorem mem_subdifferentialGraphPairing
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : YU} {vStar : YV} :
    (u, v) ~[gphd[YU, YV](K)] (uStar, vStar) ↔
      (uStar, vStar) ∈ d(K ; u, v) :=
  Iff.rfl

end

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]

/-- Pointwise membership in the self-pairing saddle-subdifferential graph. -/
@[simp] theorem mem_subdifferentialGraph
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : U} {vStar : V} :
    (u, v) ~[gphd[U, V](K)] (uStar, vStar) ↔
      (uStar, vStar) ∈ d(K ; u, v) :=
  Iff.rfl

variable [Add V]

/-- The textbook Minty map on the graph of the saddle subdifferential. -/
def subdifferentialGraphMintyMap
    (K : U → V → WithTopBot 𝕜) :
    (gphd[U, V](K) : SetRel (U × V) (U × V)) → U × V
  | ⟨((u, v), (uStar, vStar)), _⟩ => (u - uStar, v + vStar)

@[simp] theorem subdifferentialGraphMintyMap_apply
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : U} {vStar : V}
    (hp : (u, v) ~[gphd[U, V](K)] (uStar, vStar)) :
    subdifferentialGraphMintyMap K ⟨((u, v), (uStar, vStar)), hp⟩ = (u - uStar, v + vStar) :=
  rfl

end

section

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable {YU : Type*} {YV : Type*}
variable [TopologicalSpace YU] [TopologicalSpace YV]
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]

/-- Corollary 37.5.1, closed-graph clause on the pairing-level graph owner of the saddle
subdifferential. -/
theorem isClosed_subdifferentialGraphPairing
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K) :
    IsClosed (gphd[YU, YV](K)) := by
  let _ := hK_shape
  let _ := hK_closed
  sorry

end

section

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]

/-- Corollary 37.5.1, self-pairing specialization of
`isClosed_subdifferentialGraphPairing`. -/
theorem isClosed_subdifferentialGraph
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K) :
    IsClosed (gphd[U, V](K) : SetRel (U × V) (U × V)) := by
  simpa using
    (isClosed_subdifferentialGraphPairing (K := K) hK_shape hK_closed)

end

section

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]
variable {K : U → V → WithTopBot 𝕜}

/-- Corollary 37.5.1, homeomorphism clause: for a closed proper concave-convex saddle-function,
the explicit Minty map on the graph of the saddle subdifferential is a homeomorphism onto the
ambient product space. -/
theorem isHomeomorph_subdifferentialGraphMintyMap
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K) :
    IsHomeomorph (subdifferentialGraphMintyMap K) := by
  let _ := hK_shape
  let _ := hK_closed
  let _ := hK_proper
  sorry

end

end Bifunction

/-! ### Corollary_37_5_2 (from Chap07) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable {YU : Type*} {YV : Type*}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]
variable [Neg YU]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 37.5.2 gives monotonicity (and later maximal monotonicity) for the
  saddle-subdifferential after the standard sign flip on the first dual coordinate.
- `core/canonical`: the underlying graph owner is already
  `subdifferentialGraphPairing : SetRel (U × V) (YU × YV)` from Corollary 37.5.1, and monotonicity
  is owned by `SetRel.Monotone`.
- `bridge/view`: this file introduces the dedicated sign-flip graph owner
  `subdifferentialGraphPairingSignFlip` with source-facing notation
  `gphdsf[YU, YV](K)`, i.e. the canonical pullback view of `gphd[YU, YV](K)` under the
  first-dual-coordinate sign map.

Domain-style sampling used here:
- `Bifunction.subdifferentialGraphPairing` and
  `Bifunction.mem_subdifferentialGraphPairing` from `Chap07.Corollary_37_5_1`;
- `SetRel.Monotone` from `Chap05.Definition_5_24_7`.

Primitive data vs derived API:
- primitive source data: `K` and `subdifferentialGraphPairing K`;
- primitive bridge map: `(u⋆, v⋆) ↦ (-u⋆, v⋆)`;
- derived API: the sign-flip graph owner and notation `gphdsf[_, _](·)`, plus pointwise membership
  and monotonicity.

Layer target: `bridge/view`.

Abstraction boundary notes:
- the scalar/codomain layer is upstream-owned in `subdifferentialAt` and
  `subdifferentialGraphPairing` (Text 35.6.4 and Corollary 37.5.1), so this file normalizes the
  relation owner surface without introducing a second codomain owner.
-/

/-- Corollary 37.5.2 sign-flip graph owner on the intrinsic pairing layer:
pull `subdifferentialGraphPairing K` back along the first-dual-coordinate sign map. -/
abbrev subdifferentialGraphPairingSignFlip
    (K : U → V → WithTopBot 𝕜) : SetRel (U × V) (YU × YV) :=
  (Prod.map id (fun q : YU × YV ↦ (-q.1, q.2))) ⁻¹'
    gphd[YU, YV](K)

scoped[Rockafellar] notation "gphdsf[" YU ", " YV "](" K ")" =>
  Bifunction.subdifferentialGraphPairingSignFlip (YU := YU) (YV := YV) K

/-- Pointwise membership in the Corollary 37.5.2 sign-flipped graph view. -/
@[simp] theorem mem_subdifferentialGraphPairing_signFlip
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : YU} {vStar : YV} :
    (u, v) ~[gphdsf[YU, YV](K)] (uStar, vStar) ↔
      (u, v) ~[gphd[YU, YV](K)] (-uStar, vStar) := by
  simp

end

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]
variable [Neg U]

/-- Pointwise membership in the self-pairing sign-flipped saddle-subdifferential graph. -/
@[simp] theorem mem_subdifferentialGraph_signFlip
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : U} {vStar : V} :
    (u, v) ~[gphdsf[U, V](K)] (uStar, vStar) ↔
      (u, v) ~[gphd[U, V](K)] (-uStar, vStar) := by
  simpa using
    (mem_subdifferentialGraphPairing_signFlip
      (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
      (YU := U) (YV := V))

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {V : Type v}
variable [AddCommMonoid U] [SMul 𝕜 U] [Sub U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {YU : Type*} {YV : Type*}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]
variable [Neg YU] [Sub YU] [Sub YV]

/-- Corollary 37.5.2, monotonicity clause: for a concave-convex saddle-function,
the sign-flipped saddle-subdifferential graph relation is monotone on the intrinsic pairing layer
`(U × V) ↔ (YU × YV)`. -/
theorem monotone_subdifferentialGraphPairing_signFlip
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K) :
    Mon[𝕜](gphdsf[YU, YV](K)) := by
  let _ := hK_shape
  sorry

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]

/-!
For maximal monotonicity, this file follows the self-pairing owner used upstream by the Minty-map
homeomorphism theorem in Corollary 37.5.1 (`gphd[U, V](K) : SetRel (U × V) (U × V)`). This
clause therefore stays on the same scalar-parametric self-pairing abstraction layer as
Corollary 37.5.1, rather than specializing to Euclidean finite-dimensional models.
-/

/-- Corollary 37.5.2, maximal clause: for a closed proper concave-convex saddle-function,
the sign-flipped saddle-subdifferential graph relation is maximal monotone on the self-pairing
pairing owner layer. -/
theorem maximal_monotone_subdifferentialGraph_signFlip
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K) :
    Maximal (·.Monotone 𝕜) (gphdsf[U, V](K)) := by
  let _ := hK_shape
  let _ := hK_closed
  let _ := hK_proper
  sorry

end

end Bifunction

/-! ### Corollary_37_5_3 (from Chap07) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v

namespace Bifunction

section

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 37.5.3 identifies `∂KStar(0, 0)` with the saddle-points of `K`, and
  extracts the existence criterion `0 ∈ dom ∂ₛ KStar`.
- `core/canonical`: the relevant owners already exist upstream as
  `Bifunction.IsSaddlePoint`, the intrinsic strong-dual domain notation `dom∂ₛ`, and
  `SaddleFunction.dom`.
- `bridge/view`: this file therefore keeps only the zero-fiber and intrinsic-domain bridge
  theorems,
  with no local redefinition of the saddle subdifferential, graph relation, effective domain, or
  saddle-point set.

Primary mathematical domain:
- saddle-point existence via the conjugate saddle subdifferential.

Domain-style sampling used here:
- `Bifunction.mem_subdifferentialAt_iff_mem_subdifferentialAt_of_equivalent_lowerConjugate` from
  `Chap07.Theorem_37_5`;
- `Bifunction.mem_subdifferentialDomDual` from `Chap07.Definition_37_3_1`;
- `Bifunction.isSaddlePoint_iff_zero_mem_subdifferentialAt` from
  `Chap07.Proposition_36_5_2`;
- `Bifunction.subdifferentialGraphPairing` / notation `gphd[YU, YV](K)` from
  `Chap07.Corollary_37_5_1`;
- `Bifunction.ri_dom_subset_subdifferentialDomDual_of_isClosedProperConcaveConvex`
  from `Chap07.Theorem_37_4`.

Primitive data vs derived API:
- primitive source data: a saddle kernel `K` and a conjugate-side representative
  `KStar ∼ lowerConjugate K`;
- primitive owner data reused from upstream: `d(KStar ; 0, 0)`, `IsSaddlePoint K u v`,
  `dom∂ₛ KStar`, and `SaddleFunction.dom KStar`;
- derived API: the zero-fiber/saddle-point equivalence, the intrinsic-domain existence criterion,
  and
  the relative-interior existence consequence.

Layer target: `source-facing`, stated directly on the existing owners.
-/

-- Proof sketch: specialize Theorem 37.5 at the dual base point `(0, 0)`, then rewrite the
-- primal-side zero-subgradient clause by Proposition 36.5.2.
/-- Corollary 37.5.3, zero-fiber clause: if `KStar` is a conjugate saddle representative of `K`,
then membership in `∂KStar(0, 0)` is exactly the saddle-point condition for `K`. -/
theorem mem_subdifferentialAt_zero_iff_isSaddlePoint_of_equivalent_lowerConjugate
    {K KStar : U → V → EReal}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K)
    {u : U} {v : V} :
    (u, v) ∈ d(KStar ; (0 : U), (0 : V) | U, V) ↔ IsSaddlePoint K u v := by
  sorry

-- Proof sketch: use `mem_subdifferentialDomDual` to rewrite `0 ∈ dom∂ₛ KStar` as nonemptiness of
-- `d(KStar ; 0, 0)`, then use the previous zero-fiber theorem to identify those witnesses with
-- saddle-points of `K`.
/-- Corollary 37.5.3, existence criterion: `K` has a saddle-point exactly when the origin lies in
the intrinsic strong-dual domain `dom∂ₛ KStar` of a conjugate saddle representative `KStar`. -/
theorem exists_isSaddlePoint_iff_zero_mem_subdifferentialDomDual_of_equivalent_lowerConjugate
    {K KStar : U → V → EReal}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K) :
    (∃ p : U × V, IsSaddlePoint K p.1 p.2) ↔
      (0 : U × V) ∈ dom∂ₛ KStar := by
  sorry

-- Proof sketch: Theorem 37.4 places `ri (dom KStar)` inside the domain of the saddle
-- subdifferential of `KStar`; the previous theorem then converts `0 ∈ dom∂ₛ KStar` into
-- existence of a saddle-point of `K`.
/-- Corollary 37.5.3, relative-interior consequence: if the origin lies in the relative interior
of the product domain of a closed proper concave-convex conjugate representative `KStar`, then
the original saddle kernel `K` has a saddle-point. -/
theorem exists_isSaddlePoint_of_zero_mem_ri_dom_of_equivalent_lowerConjugate
    {K KStar : U → V → EReal}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K)
    (hKStar_shape : SaddleFunction.IsConcaveConvex ℝ KStar)
    (hKStar_closed : SaddleFunction.IsClosed KStar)
    (hKStar_proper : SaddleFunction.IsProper KStar)
    (hzero_ri : (0 : U × V) ∈ ri[ℝ](SaddleFunction.dom KStar)) :
    ∃ p : U × V, IsSaddlePoint K p.1 p.2 := by
  sorry

end

end Bifunction

/-! ### Theorem_37_5 (from Chap07) -/
noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type v} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {V : Type v}
variable {YU : Type u} {YV : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [HasPairing U YU 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V] [HasPairing V YV 𝕜]
variable [NormedAddCommGroup YU] [NormedSpace 𝕜 YU]
variable [NormedAddCommGroup YV] [NormedSpace 𝕜 YV]

local instance : HasPairing YU U 𝕜 := HasPairing.swap
local instance : HasPairing YV V 𝕜 := HasPairing.swap

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 37.5 is the saddle-function analogue of Fenchel subgradient inversion:
  for a closed proper concave-convex `K`, any conjugate saddle representative `KStar`, the
  saddle-subgradient relation for `K` is equivalent both to the reversed saddle-subgradient
  relation for `KStar` and to the usual convex subgradient relation of the graph function of the
  closed proper convex generator `F`.
- `core/canonical`: the owner abstractions already present in the project are
  `Bifunction.lowerConjugate`, the Chapter 34 class owner `omegaAdjoint`, the Chapter 34 equivalence
  relation `K ∼ L`, the Chapter 34 closed-convex owner `Bifunction.IsClosedConvex`, the saddle
  subdifferential owner `Bifunction.subdifferentialAt`, the Chapter 23 vector-subdifferential
  owner `_root_.subdifferentialAt` / `∂[·](·)(·)` on `Function.uncurry F`, and the Chapter 6/7
  adjoint notation surface `F⋆`.
- `bridge/view`: the source theorem's fourth displayed equality is a Fenchel-Young equality
  companion relating the same owner data through `adjoint`; it is kept inside the TFAE
  theorem below rather than promoted to a second owner.

Primary mathematical domain:
- conjugate saddle-functions, saddle subdifferentials, and graph-function Fenchel duality.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `Bifunction.lowerConjugate` from `Chap07.Definition_37_1_1`;
- `Bifunction.subdifferentialAt` and the notation `d(K ; u, v)` from `Chap07.Text_35_6_3`;
- `Bifunction.adjoint` / `F⋆` from `Chap06.Definition_6_30_14`;
- `Bifunction.mem_omegaAdjoint_iff` and the Chapter 34 owner `omegaAdjoint` from
  `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive source data for the full four-clause theorem: a closed-convex generator owner
  `hF : IsClosedConvex F`, graph properness of `Function.uncurry F`, a representative
  `K ∈ omegaAdjoint V YU F`, and a conjugate-side representative `KStar ∼ lowerConjugate K`;
- primitive owner data reused from upstream: `d(K ; u, v)`, `d(KStar ; uStar, vStar)`,
  the graph-function owner `Function.uncurry F`,
  the pairing-level subdifferential owner
  `∂[YU × V](Function.uncurry F)(·)`, and `(F⋆)`;
- derived saddle-side data: `SaddleFunction.IsProper K`, obtained from
  `Bifunction.isProper_of_mem_omega_of_uncurry_isConvex_of_uncurry_isProper`;
- derived API: the four-way `List.TFAE` formulation matching Rockafellar's theorem, and the
  shorter inversion lemma used directly by Corollary 37.5.3 and the graph corollaries.

Layer target:
- the theorem `conjugate_subdifferentialAt_tfae_of_mem_omega_and_equivalent_lowerConjugate` is
  `source-facing`;
- the theorem
  `mem_subdifferentialAt_iff_mem_subdifferentialAt_of_equivalent_lowerConjugate`
  is the `core/canonical` owner-level consequence for downstream use, but it remains on the same
  pairing-level normed ambient layer as the source-facing theorem because its only justification
  in the current chapter graph is extraction of the first two clauses of that TFAE statement.
-/

-- Proof sketch: first derive `SaddleFunction.IsProper K` from the Chapter 34 properness bridge
-- attached to `hK : K ∈ omegaAdjoint V YU F`, then use the Chapter 34 closed-convex owner `hF`
-- for the generator `F`, identify the graph-function conjugate relation by the convex theorem
-- `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff`, and translate the
-- saddle-side clauses through the Chapter 37 conjugate owner `lowerConjugate K`. Corollary 37.4.1
-- then allows replacement of `lowerConjugate K` by any equivalent conjugate representative
-- `KStar`.
variable {F : U → YV → WithBotTop 𝕜}
variable {K : U → V → WithBotTop 𝕜}
variable {KStar : YU → YV → WithBotTop 𝕜}

local notation "F⋆" => (adjoint V YU F : V → YU → WithBotTop 𝕜)

/-- Theorem 37.5, source-facing owner form: for `K ∈ omegaAdjoint V YU F` and a conjugate saddle
representative
`KStar ∼ lowerConjugate K`, the saddle-subgradient clause for `K`, the reversed
saddle-subgradient clause for `KStar`, the graph-function subgradient clause for
`Function.uncurry F` through the pairing-level subgradient notation `∂[YU × V](·)(·)`, and the
associated Fenchel-Young equality written with `(F⋆)` all
belong to one four-condition equivalence class. Properness of `K` is derived internally from the
Chapter 34 owner hypotheses. -/
theorem conjugate_subdifferentialAt_tfae_of_mem_omega_and_equivalent_lowerConjugate
    (hF : IsClosedConvex F)
    (hF_proper : (Function.uncurry F).IsProper)
    (hK : K ∈ omegaAdjoint V YU F)
    (hKStar : KStar ∼ lowerConjugate K)
    {u : U} {uStar : YU} {v : V} {vStar : YV} :
    List.TFAE
      [ (uStar, vStar) ∈ d(K ; u, v | YU, YV),
        (u, v) ∈ d(KStar ; uStar, vStar | U, V),
        (-uStar, v) ∈ ∂[YU × V]Function.uncurry F((u, vStar)),
        F u vStar - ⟪v, vStar⟫ₚ =
          F⋆ v uStar - ⟪u, uStar⟫ₚ ] := by
  sorry

-- This owner-level inversion statement is only obtained in this file by specializing the
-- preceding TFAE theorem to its first two clauses, so it stays on the same
-- pairing-level normed ambient layer rather than being promoted to a weaker theorem unsupported
-- by the current chapter graph.
-- Proof sketch: specialize the preceding TFAE theorem to the first two clauses and read off the
-- `0 ↔ 1` equivalence.
/-- Core owner consequence of Theorem 37.5: the saddle subdifferential of a closed proper
concave-convex kernel is inverted by any conjugate saddle representative in the Chapter 37 sense
`KStar ∼ lowerConjugate K`. -/
theorem mem_subdifferentialAt_iff_mem_subdifferentialAt_of_equivalent_lowerConjugate
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K)
    {u : U} {uStar : YU} {v : V} {vStar : YV} :
    (uStar, vStar) ∈ d(K ; u, v | YU, YV) ↔
      (u, v) ∈ d(KStar ; uStar, vStar | U, V) := by
  sorry

end

end Bifunction
