/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Gegenbauer polynomials of index `3/2`

The Gegenbauer (ultraspherical) polynomials `Cₙ = Cₙ^{(3/2)} : ℝ[X]` of index `3/2` are defined by
their three-term recurrence

  `C₀ = 1`, `C₁ = 3X`, `(n + 2) Cₙ₊₂ = (2n + 5) X Cₙ₊₁ - (n + 3) Cₙ`,

and this file develops their algebraic theory, their differential equation, and their
orthogonality on `[-1, 1]` with respect to the weight `1 - x²`. They are the polynomials in which
the leading-twist light-cone distribution amplitude of a pseudoscalar meson is expanded: written
in the light-cone fraction `u` through `x = 2u - 1`, the weighted polynomials
`u (1 - u) Cₙ (2u - 1)` are the eigenfunctions of the Efremov–Radyushkin–Brodsky–Lepage evolution
kernel, and the weight `1 - x²` here is `4 u (1 - u)`.

Only the index `3/2` is defined. The index-`1/2` and index-`1` families are the Legendre and
Chebyshev (second kind) polynomials, with the weights `1` and `√(1 - x²)`; the index-`3/2`
family is the one whose weight `1 - x²` is, up to normalisation, the asymptotic distribution
amplitude `6 u (1 - u)`.

## Main definitions

* `EpsilonEridani.Polynomial.gegenbauer n`: the Gegenbauer polynomial `Cₙ^{(3/2)}`.

## Main statements

* `gegenbauer_add_two`: the three-term recurrence;
* `natDegree_gegenbauer`, `leadingCoeff_gegenbauer`: `Cₙ` has degree `n` and leading coefficient
  `(2n + 1) (2n choose n) / 2ⁿ`;
* `gegenbauer_comp_neg_X`: the parity relation `Cₙ (-X) = (-1)ⁿ Cₙ`;
* `gegenbauer_eval_one`, `gegenbauer_eval_neg_one`: `Cₙ (1) = (n + 1)(n + 2) / 2` and
  `Cₙ (-1) = (-1)ⁿ (n + 1)(n + 2) / 2`;
* `derivative_gegenbauer_succ`, `X_mul_derivative_gegenbauer_succ`,
  `one_sub_X_sq_mul_derivative_gegenbauer_succ`: the ladder relations for the derivatives;
* `one_sub_X_sq_mul_derivative_derivative_gegenbauer`: the Gegenbauer differential equation
  `(1 - X²) Cₙ'' = 4 X Cₙ' - n (n + 3) Cₙ`, and
  `derivative_one_sub_X_sq_sq_mul_derivative_gegenbauer`, its Sturm–Liouville form
  `((1 - X²)² Cₙ')' = -n (n + 3) (1 - X²) Cₙ`;
* `integral_gegenbauer_mul_gegenbauer`: the orthogonality relation
  `∫₋₁¹ (1 - x²) Cₘ Cₙ = if m = n then 2 (n + 1)(n + 2) / (2n + 3) else 0`.

Orthogonality of distinct members is proved by the Sturm–Liouville argument: the operator
`p ↦ ((1 - X²)² p')'` is symmetric on `[-1, 1]` because its boundary term carries `(1 - X²)²`
(`integral_derivative_one_sub_X_sq_sq_mul_derivative_mul`), and `Cₘ`, `Cₙ` are eigenvectors, for
the weight `1 - X²`, with the distinct eigenvalues `-m (m + 3)`, `-n (n + 3)`. The normalisation
then follows from the recurrence. The squared norm `2 (n + 1)(n + 2) / (2n + 3)` is the value at
`λ = 3/2` of the general Gegenbauer norm `π 2^{1 - 2λ} Γ(n + 2λ) / (n! (n + λ) Γ(λ)²)`.

## References

* [G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, ch. IV]
* NIST Digital Library of Mathematical Functions, §18.3, §18.5, §18.8, §18.9,
  <https://dlmf.nist.gov/18>
-/

public section

namespace EpsilonEridani

namespace Polynomial

open _root_.Polynomial

/-- The **Gegenbauer polynomial** `Cₙ = Cₙ^{(3/2)}` of index `3/2`, defined by `C₀ = 1`,
`C₁ = 3X` and the recurrence `(n + 2) Cₙ₊₂ = (2n + 5) X Cₙ₊₁ - (n + 3) Cₙ`
(see `gegenbauer_add_two`). -/
noncomputable def gegenbauer : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 * X
  | n + 2 => C ((n + 2 : ℝ)⁻¹) *
      ((2 * n + 5 : ℝ[X]) * X * gegenbauer (n + 1) - (n + 3 : ℝ[X]) * gegenbauer n)

/-- `C₀ = 1`. -/
@[simp] theorem gegenbauer_zero : gegenbauer 0 = 1 := by rw [gegenbauer]

/-- `C₁ = 3X`. -/
@[simp] theorem gegenbauer_one : gegenbauer 1 = 3 * X := by rw [gegenbauer]

private theorem natCast_add_two_ne_zero (n : ℕ) : (n + 2 : ℝ[X]) ≠ 0 := by
  exact_mod_cast (show n + 2 ≠ 0 by omega)

/-- The **three-term recurrence** `(n + 2) Cₙ₊₂ = (2n + 5) X Cₙ₊₁ - (n + 3) Cₙ`, the defining
relation of the Gegenbauer polynomials of index `3/2`. -/
theorem gegenbauer_add_two (n : ℕ) : (n + 2 : ℝ[X]) * gegenbauer (n + 2) =
    (2 * n + 5 : ℝ[X]) * X * gegenbauer (n + 1) - (n + 3 : ℝ[X]) * gegenbauer n := by
  rw [gegenbauer, ← mul_assoc]
  convert one_mul _
  rw [← (by rw [map_add, C_eq_natCast, C_ofNat] : C (n + 2 : ℝ) = (n + 2 : ℝ[X])), ← C_mul,
    mul_inv_cancel₀ (by positivity), C_1]

/-- The three-term recurrence evaluated at a point. -/
theorem gegenbauer_eval_add_two (n : ℕ) (x : ℝ) : (n + 2) * (gegenbauer (n + 2)).eval x =
    (2 * n + 5) * x * (gegenbauer (n + 1)).eval x - (n + 3) * (gegenbauer n).eval x := by
  simpa using congrArg (eval x) (gegenbauer_add_two n)

/-- `C₂ = (3/2) (5X² - 1)`. -/
theorem gegenbauer_two : gegenbauer 2 = C (3 / 2) * (5 * X ^ 2 - 1) := by
  refine funext fun x => ?_
  have h := gegenbauer_eval_add_two 0 x
  norm_num at h
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_one, eval_ofNat]
  linear_combination h / 2

/-- `C₃ = (5/2) (7X³ - 3X)`. -/
theorem gegenbauer_three : gegenbauer 3 = C (5 / 2) * (7 * X ^ 3 - 3 * X) := by
  refine funext fun x => ?_
  have h := gegenbauer_eval_add_two 1 x
  norm_num [gegenbauer_two] at h
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_ofNat]
  linear_combination h / 3

/-- `Cₙ (1) = (n + 1)(n + 2) / 2`. -/
@[simp] theorem gegenbauer_eval_one (n : ℕ) :
    (gegenbauer n).eval 1 = (n + 1) * (n + 2) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n h₀ h₁ =>
    have h := gegenbauer_eval_add_two n 1
    rw [h₀, h₁] at h
    push_cast at h ⊢
    exact mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) (by linear_combination h)

/-- **Parity** of the Gegenbauer polynomials: `Cₙ (-X) = (-1)ⁿ Cₙ`. -/
theorem gegenbauer_comp_neg_X (n : ℕ) :
    (gegenbauer n).comp (-X) = (-1) ^ n * gegenbauer n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    refine mul_left_cancel₀ (natCast_add_two_ne_zero n) ?_
    have h := congrArg (·.comp (-X)) (gegenbauer_add_two n)
    simp only [mul_comp, sub_comp, add_comp, natCast_comp, ofNat_comp, X_comp, h₀, h₁] at h
    linear_combination h - (-1) ^ n * gegenbauer_add_two n

/-- Parity of the Gegenbauer polynomials, evaluated at a point. -/
theorem gegenbauer_eval_neg (n : ℕ) (x : ℝ) :
    (gegenbauer n).eval (-x) = (-1) ^ n * (gegenbauer n).eval x := by
  simpa using congrArg (eval x) (gegenbauer_comp_neg_X n)

/-- `Cₙ (-1) = (-1)ⁿ (n + 1)(n + 2) / 2`. -/
@[simp] theorem gegenbauer_eval_neg_one (n : ℕ) :
    (gegenbauer n).eval (-1) = (-1) ^ n * ((n + 1) * (n + 2) / 2) := by
  rw [gegenbauer_eval_neg, gegenbauer_eval_one]

/-- The three-term recurrence read off on coefficients. -/
private theorem coeff_gegenbauer_add_two (n k : ℕ) :
    (n + 2) * (gegenbauer (n + 2)).coeff (k + 1) =
      (2 * n + 5) * (gegenbauer (n + 1)).coeff k - (n + 3) * (gegenbauer n).coeff (k + 1) := by
  have h := congrArg (coeff · (k + 1)) (gegenbauer_add_two n)
  simpa [add_mul, sub_mul, mul_assoc, coeff_X_mul] using h

/-- `Cₙ` has no coefficient above degree `n`. -/
theorem coeff_gegenbauer_of_lt {n k : ℕ} (h : n < k) : (gegenbauer n).coeff k = 0 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [coeff_one, h.ne']
  | one => simp [coeff_X, h.ne]
  | more n h₀ h₁ =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h' := coeff_gegenbauer_add_two n k
    rw [h₀ (by omega), h₁ (by omega)] at h'
    exact (mul_eq_zero.mp (h'.trans (by ring))).resolve_left (by positivity)

/-- The coefficient of `Xⁿ` in `Cₙ`, which is its leading coefficient, is
`(2n + 1) (2n choose n) / 2ⁿ`. -/
theorem coeff_gegenbauer_self (n : ℕ) :
    (gegenbauer n).coeff n = (2 * n + 1) * n.centralBinom / 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num [Nat.centralBinom]
  | more n _ h₁ =>
    have h := coeff_gegenbauer_add_two n (n + 1)
    rw [h₁, coeff_gegenbauer_of_lt (n := n) (k := n + 1 + 1) (by omega)] at h
    have hc : ((n + 2 : ℕ) : ℝ) * (n + 2).centralBinom = 2 * (2 * (n + 1 : ℕ) + 1) *
        (n + 1).centralBinom := by exact_mod_cast Nat.succ_mul_centralBinom_succ (n + 1)
    push_cast at hc h ⊢
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    rw [h, mul_zero, sub_zero, pow_succ _ (n + 1)]
    field_simp
    linear_combination -(2 * n + 5) * hc

private theorem coeff_gegenbauer_self_ne_zero (n : ℕ) : (gegenbauer n).coeff n ≠ 0 := by
  rw [coeff_gegenbauer_self]
  exact div_ne_zero (mul_ne_zero (by positivity) (by exact_mod_cast n.centralBinom_ne_zero))
    (by positivity)

/-- No Gegenbauer polynomial vanishes. -/
theorem gegenbauer_ne_zero (n : ℕ) : gegenbauer n ≠ 0 := fun h =>
  coeff_gegenbauer_self_ne_zero n (by rw [h, coeff_zero])

/-- `Cₙ` has degree exactly `n`. -/
@[simp] theorem natDegree_gegenbauer (n : ℕ) : (gegenbauer n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun _ h => coeff_gegenbauer_of_lt (by exact_mod_cast h))
    (coeff_gegenbauer_self_ne_zero n)

/-- `Cₙ` has degree exactly `n`. -/
@[simp] theorem degree_gegenbauer (n : ℕ) : (gegenbauer n).degree = n :=
  (degree_eq_iff_natDegree_eq (gegenbauer_ne_zero n)).mpr (natDegree_gegenbauer n)

/-- The leading coefficient of `Cₙ` is `(2n + 1) (2n choose n) / 2ⁿ`. -/
@[simp] theorem leadingCoeff_gegenbauer (n : ℕ) :
    (gegenbauer n).leadingCoeff = (2 * n + 1) * n.centralBinom / 2 ^ n := by
  rw [leadingCoeff, natDegree_gegenbauer, coeff_gegenbauer_self]

/-- One rung of the derivative ladder: the lowering relation at `n` gives the raising relation at
`n + 1`, through the derivative of the three-term recurrence. -/
private theorem derivative_gegenbauer_add_two_of {n : ℕ}
    (h : X * derivative (gegenbauer (n + 1)) =
      derivative (gegenbauer n) + (n + 1 : ℝ[X]) * gegenbauer (n + 1)) :
    derivative (gegenbauer (n + 2)) =
      X * derivative (gegenbauer (n + 1)) + (n + 4 : ℝ[X]) * gegenbauer (n + 1) := by
  have hd := congrArg derivative (gegenbauer_add_two n)
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_natCast, derivative_ofNat,
    derivative_X, zero_mul, zero_add, add_zero, mul_one] at hd
  refine mul_left_cancel₀ (natCast_add_two_ne_zero n) ?_
  linear_combination hd + (n + 3) * h

private theorem derivative_gegenbauer_ladder (n : ℕ) :
    X * derivative (gegenbauer (n + 1)) =
        derivative (gegenbauer n) + (n + 1 : ℝ[X]) * gegenbauer (n + 1) ∧
      (1 - X ^ 2) * derivative (gegenbauer (n + 1)) =
        (n + 3 : ℝ[X]) * gegenbauer n - (n + 1 : ℝ[X]) * X * gegenbauer (n + 1) := by
  induction n with
  | zero =>
    constructor <;> norm_num <;> ring
  | succ n ih =>
    have hb := derivative_gegenbauer_add_two_of ih.1
    have hr := gegenbauer_add_two n
    push_cast
    constructor
    · linear_combination X * hb - ih.2 - hr
    · linear_combination (1 - X ^ 2) * hb + X * ih.2 + X * hr

/-- The raising relation `C'ₙ₊₁ = X C'ₙ + (n + 3) Cₙ`. -/
theorem derivative_gegenbauer_succ (n : ℕ) :
    derivative (gegenbauer (n + 1)) =
      X * derivative (gegenbauer n) + (n + 3 : ℝ[X]) * gegenbauer n := by
  cases n with
  | zero => simp
  | succ n =>
    convert derivative_gegenbauer_add_two_of (derivative_gegenbauer_ladder n).1 using 3
    push_cast
    ring

/-- The lowering relation `X C'ₙ₊₁ = C'ₙ + (n + 1) Cₙ₊₁`. -/
theorem X_mul_derivative_gegenbauer_succ (n : ℕ) :
    X * derivative (gegenbauer (n + 1)) =
      derivative (gegenbauer n) + (n + 1 : ℝ[X]) * gegenbauer (n + 1) :=
  (derivative_gegenbauer_ladder n).1

/-- The relation `(1 - X²) C'ₙ₊₁ = (n + 3) Cₙ - (n + 1) X Cₙ₊₁`, which expresses the derivative
through the family itself. -/
theorem one_sub_X_sq_mul_derivative_gegenbauer_succ (n : ℕ) :
    (1 - X ^ 2) * derivative (gegenbauer (n + 1)) =
      (n + 3 : ℝ[X]) * gegenbauer n - (n + 1 : ℝ[X]) * X * gegenbauer (n + 1) :=
  (derivative_gegenbauer_ladder n).2

/-- The **Gegenbauer differential equation** of index `3/2`:
`(1 - X²) C''ₙ = 4 X C'ₙ - n (n + 3) Cₙ`. -/
theorem one_sub_X_sq_mul_derivative_derivative_gegenbauer (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (gegenbauer n)) =
      4 * X * derivative (gegenbauer n) - (n : ℝ[X]) * ((n : ℝ[X]) + 3) * gegenbauer n := by
  cases n with
  | zero => simp
  | succ n =>
    have hd := congrArg derivative (one_sub_X_sq_mul_derivative_gegenbauer_succ n)
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast, derivative_one,
      derivative_ofNat, derivative_X_sq, derivative_X, zero_mul, zero_add, zero_sub, mul_one,
      add_zero, C_ofNat] at hd
    push_cast
    linear_combination hd - (n + 3 : ℝ[X]) * X_mul_derivative_gegenbauer_succ n

/-- The **Gegenbauer differential equation** of index `3/2` in Sturm–Liouville form:
`((1 - X²)² C'ₙ)' = -n (n + 3) (1 - X²) Cₙ`. -/
theorem derivative_one_sub_X_sq_sq_mul_derivative_gegenbauer (n : ℕ) :
    derivative ((1 - X ^ 2) ^ 2 * derivative (gegenbauer n)) =
      -((n : ℝ[X]) * ((n : ℝ[X]) + 3)) * (1 - X ^ 2) * gegenbauer n := by
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_one, derivative_X,
    Nat.cast_ofNat, C_ofNat]
  push_cast
  linear_combination (1 - X ^ 2) * one_sub_X_sq_mul_derivative_derivative_gegenbauer n

section Orthogonality

open MeasureTheory intervalIntegral

/-- The **symmetry of the Gegenbauer operator** `p ↦ ((1 - X²)² p')'` on `[-1, 1]`: the boundary
term of the integration by parts carries the factor `(1 - X²)²` and vanishes at both endpoints. -/
theorem integral_derivative_one_sub_X_sq_sq_mul_derivative_mul (p q : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, (derivative ((1 - X ^ 2) ^ 2 * derivative p) * q).eval x =
      ∫ x in (-1 : ℝ)..1, (p * derivative ((1 - X ^ 2) ^ 2 * derivative q)).eval x := by
  have key : derivative ((1 - X ^ 2) ^ 2 * derivative p) * q -
      p * derivative ((1 - X ^ 2) ^ 2 * derivative q) =
        derivative ((1 - X ^ 2) ^ 2 * (derivative p * q - p * derivative q)) := by
    simp only [derivative_mul, derivative_sub]
    ring
  rw [← sub_eq_zero, ← integral_sub ((_root_.Polynomial.continuous _).intervalIntegrable _ _)
    ((_root_.Polynomial.continuous _).intervalIntegrable _ _)]
  simp_rw [← eval_sub, key]
  rw [integral_deriv_eq_sub' _ (funext fun x => _root_.Polynomial.deriv _)
    (fun x _ => _root_.Polynomial.differentiableAt _) (_root_.Polynomial.continuous _).continuousOn]
  simp

/-- **Orthogonality of the Gegenbauer polynomials** of index `3/2` on `[-1, 1]`: distinct members
are orthogonal with respect to the weight `1 - x²`. -/
theorem integral_gegenbauer_mul_gegenbauer_of_ne {m n : ℕ} (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (gegenbauer m).eval x * (gegenbauer n).eval x = 0 := by
  have hs := integral_derivative_one_sub_X_sq_sq_mul_derivative_mul (gegenbauer m) (gegenbauer n)
  rw [derivative_one_sub_X_sq_sq_mul_derivative_gegenbauer,
    derivative_one_sub_X_sq_sq_mul_derivative_gegenbauer] at hs
  have e₁ : ∀ x : ℝ, eval x (-((m : ℝ[X]) * ((m : ℝ[X]) + 3)) * (1 - X ^ 2) * gegenbauer m *
      gegenbauer n) =
      -((m : ℝ) * (m + 3)) * ((1 - x ^ 2) * (gegenbauer m).eval x * (gegenbauer n).eval x) :=
    fun x => by simp only [eval_mul, eval_neg, eval_add, eval_sub, eval_natCast, eval_ofNat,
      eval_one, eval_pow, eval_X]; ring
  have e₂ : ∀ x : ℝ, eval x (gegenbauer m * (-((n : ℝ[X]) * ((n : ℝ[X]) + 3)) * (1 - X ^ 2) *
      gegenbauer n)) =
      -((n : ℝ) * (n + 3)) * ((1 - x ^ 2) * (gegenbauer m).eval x * (gegenbauer n).eval x) :=
    fun x => by simp only [eval_mul, eval_neg, eval_add, eval_sub, eval_natCast, eval_ofNat,
      eval_one, eval_pow, eval_X]; ring
  simp_rw [e₁, e₂, intervalIntegral.integral_const_mul] at hs
  have hmn : (m : ℝ) * (m + 3) ≠ n * (n + 3) := by
    intro he
    have : m * (m + 3) = n * (n + 3) := by exact_mod_cast he
    rcases Nat.lt_or_gt_of_ne h with hlt | hlt
    · exact (Nat.mul_lt_mul'' hlt (by omega : m + 3 < n + 3)).ne this
    · exact (Nat.mul_lt_mul'' hlt (by omega : n + 3 < m + 3)).ne' this
  exact (mul_eq_zero.mp (by linear_combination hs : ((n : ℝ) * (n + 3) - m * (m + 3)) *
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (gegenbauer m).eval x * (gegenbauer n).eval x = 0))
    |>.resolve_left (sub_ne_zero.mpr hmn.symm)

/-- The three-term recurrence for `Cₙ₊₂`, paired with a polynomial `q` against the weight
`1 - x²` on `[-1, 1]`. -/
private theorem integral_gegenbauer_add_two_mul (n : ℕ) (q : ℝ[X]) :
    (n + 2 : ℝ) * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (gegenbauer (n + 2)).eval x * q.eval x =
      (2 * n + 5 : ℝ) *
          (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * x * (gegenbauer (n + 1)).eval x * q.eval x) -
        (n + 3 : ℝ) * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (gegenbauer n).eval x * q.eval x := by
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  exact integral_congr fun x _ => by
    linear_combination (1 - x ^ 2) * q.eval x * gegenbauer_eval_add_two n x

/-- **Normalisation of the Gegenbauer polynomials** of index `3/2`:
`∫₋₁¹ (1 - x²) Cₙ² = 2 (n + 1)(n + 2) / (2n + 3)`. -/
theorem integral_gegenbauer_mul_self (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (gegenbauer n).eval x * (gegenbauer n).eval x =
      (2 * (n + 1) * (n + 2) / (2 * n + 3) : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [gegenbauer_zero, eval_one, mul_one]
    rw [integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_pow 2),
      integral_pow]
    norm_num
  | one =>
    have e : ∀ x : ℝ, (1 - x ^ 2) * (gegenbauer 1).eval x * (gegenbauer 1).eval x =
        9 * x ^ 2 - 9 * x ^ 4 := fun x => by
      simp only [gegenbauer_one, eval_mul, eval_ofNat, eval_X]; ring
    simp_rw [e]
    rw [integral_sub ((intervalIntegral.intervalIntegrable_pow 2).const_mul _)
      ((intervalIntegral.intervalIntegrable_pow 4).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
      integral_pow]
    norm_num
  | more n _ h₁ =>
    -- pair the recurrence for `Cₙ₊₂` with `Cₙ₊₂`, and the one for `Cₙ₊₃` with `Cₙ₊₁`;
    -- both produce the mixed integral `K = ∫ (1 - x²) x Cₙ₊₁ Cₙ₊₂`
    have hA := integral_gegenbauer_add_two_mul n (gegenbauer (n + 2))
    have hB := integral_gegenbauer_add_two_mul (n + 1) (gegenbauer (n + 1))
    rw [integral_gegenbauer_mul_gegenbauer_of_ne (by omega : n ≠ n + 2), mul_zero,
      sub_zero] at hA
    rw [integral_gegenbauer_mul_gegenbauer_of_ne (by omega : n + 1 + 2 ≠ n + 1), h₁,
      mul_zero] at hB
    have hK : ∫ x in (-1 : ℝ)..1,
        (1 - x ^ 2) * x * (gegenbauer (n + 1 + 1)).eval x * (gegenbauer (n + 1)).eval x =
        ∫ x in (-1 : ℝ)..1,
          (1 - x ^ 2) * x * (gegenbauer (n + 1)).eval x * (gegenbauer (n + 2)).eval x :=
      integral_congr fun x _ => by ring
    rw [hK] at hB
    set K := ∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) * x * (gegenbauer (n + 1)).eval x * (gegenbauer (n + 2)).eval x
    have h3 : (2 * n + 5 : ℝ) * (2 * (n + 2) * (n + 3) / (2 * n + 5)) =
        2 * (n + 2) * (n + 3) := by
      field_simp
    push_cast at hB ⊢
    rw [eq_div_iff (by positivity)]
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    linear_combination (2 * n + 7) * hA - (2 * n + 5) * hB + (n + 4) * h3

/-- **The orthogonality relation** for the Gegenbauer polynomials of index `3/2`:
`∫₋₁¹ (1 - x²) Cₘ Cₙ = if m = n then 2 (n + 1)(n + 2) / (2n + 3) else 0`. -/
theorem integral_gegenbauer_mul_gegenbauer (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (gegenbauer m).eval x * (gegenbauer n).eval x =
      if m = n then (2 * (n + 1) * (n + 2) / (2 * n + 3) : ℝ) else 0 := by
  split_ifs with h
  · subst h
    exact integral_gegenbauer_mul_self m
  · exact integral_gegenbauer_mul_gegenbauer_of_ne h

end Orthogonality

end Polynomial

end EpsilonEridani
