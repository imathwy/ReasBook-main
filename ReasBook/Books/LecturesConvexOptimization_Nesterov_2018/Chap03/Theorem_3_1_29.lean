import Mathlib
import Nesterov.Chap03.Definition_3_1_1_5
import Nesterov.Chap03.PointwiseSupremumOn

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommMonoid U] [Module ℝ U]

/- This item lies in the chapter's parametric minimax / saddle-value domain.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/PointwiseSupremumOn`, the chapter owner for faithful upper
  envelopes of a kernel;
- `ClosedConvexOn` in `Chap03/Definition_3_1_1_5`, the chapter owner for primal slice geometry;
- `IsSaddlePointOn` in `Mathlib/Order/SaddlePoint`, the canonical owner for saddle inequalities;
- `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer` in
  `Chap03/Lemma_3_22`, the nearby minimax owner theorem behind the present unique-minimizer
  consequence.

Best owner abstraction:
- source-facing: the minimax equality between the attained primal minimum and attained dual
  maximum;
- core/canonical: `IsSaddlePointOn`, `pointwiseSupremumOn`, `IsMinOn`, `IsMaxOn`, and `IsLeast`;
- bridge/view: the chosen minimizer family `x`, which realizes the diagonal values.

Primitive data:
- the feasible sets `P` and `S`;
- the kernel `Ψ`;
- the real-valued upper objective `f`, bridged to `pointwiseSupremumOn` on `P`;
- the closed-convexity of the primal slices and the concavity of the dual slices;
- the chosen slice minimizers `x u` on `P` and their uniqueness;
- an attained maximizer `uStar ∈ S` of the lower-value function
  `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`.

Derived API:
- the actual minimax equality for the primal and dual value sets;
- the canonical saddle predicate at `(x uStar, uStar)`;
- the primal-minimizer and value companions derived from that saddle relation.
-/

section

variable {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {f : X → ℝ}
variable (x : U → X)
variable {uStar : U}

/-- Theorem 3.1.29: if every primal slice `x ↦ Ψ x u` with `u ∈ S` attains the unique minimizer
`x u` on `P`, and if the lower-value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` attains its
maximum on `S`, then the primal minimum of `f` on `P` equals the dual maximum of that lower-value
function on `S`. -/
-- Proof sketch: first use the unique-minimizer hypothesis together with Theorem 3.1.4 and
-- Lemma 3.1.22 to show that `(x uStar, uStar)` is a saddle point of `Ψ` on `P × S`. The saddle
-- inequalities imply that `x uStar` minimizes `f` on `P` and that
-- `f (x uStar) = sInf ((fun x ↦ Ψ x uStar) '' P)`. Finally combine that identity with the
-- maximizing property `huStar_max` to identify the primal infimum `sInf (f '' P)` with the dual
-- supremum `sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S)`.
theorem minimax_eq_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    sInf (f '' P) = sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := sorry

/-- The distinguished pair `(x uStar, uStar)` is a saddle point of `Ψ` on `P × S` under the
unique-slice-minimizer and dual-maximizer hypotheses. -/
-- Proof sketch: apply Theorem 3.1.4 to each closed-convex slice `x ↦ Ψ x u` to recover bounded
-- sublevel sets from uniqueness of `x u`. Then Lemma 3.1.22 applied at `uStar` forces the two
-- inequalities `Ψ (x uStar) u ≤ Ψ (x uStar) uStar ≤ Ψ x uStar` for all `u ∈ S` and `x ∈ P`,
-- which is exactly the saddle relation.
theorem isSaddlePointOn_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsSaddlePointOn P S Ψ (x uStar) uStar := sorry

/-- Companion consequence of Theorem 3.1.29: the distinguished primal point `x uStar` minimizes
the real-valued upper objective `f` on `P`. -/
-- Proof sketch: combine the saddle inequalities at `(x uStar, uStar)` with the bridge
-- `hf_eq` identifying `f` on `P` with the faithful upper envelope `pointwiseSupremumOn S Ψ`.
-- This gives `f (x uStar) ≤ f x` for every feasible `x`.
theorem isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsMinOn f P (x uStar) := sorry

/-- Companion value identity from Theorem 3.1.29. -/
-- Proof sketch: once `x uStar` is known to minimize `f` on `P`, the right-hand saddle inequality
-- identifies its objective value with the slice minimum
-- `sInf ((fun x ↦ Ψ x uStar) '' P)`.
theorem objective_eq_valueFunction_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    f (x uStar) = sInf ((fun x ↦ Ψ x uStar) '' P) := sorry

/-- Order-theoretic companion of Theorem 3.1.29: the upper-envelope value attained at `x uStar`
is the least element of the feasible value image. -/
-- Proof sketch: reformulate `isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max`
-- as the statement that `f (x uStar)` is a lower bound on `f '' P`, and use `hx_mem huStar` to
-- record that the bound is itself attained in the image.
theorem primal_min_isLeast_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsLeast (f '' P) (f (x uStar)) := by
  refine ⟨⟨x uStar, hx_mem huStar, rfl⟩, ?_⟩
  rintro _ ⟨p, hpP, rfl⟩
  have hmin : IsMinOn f P (x uStar) :=
    isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max
      x hΨ_closedConvex hΨ_concave hf_eq hx_mem hx_min hx_unique huStar huStar_max
  exact hmin hpP

end

end
