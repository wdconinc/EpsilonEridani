/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.PauliMatrices.Basic
public import EpsilonEridani.Mathematics.DataStructures.Matrix.PosSemidef

/-!
# The spin density matrix of a spin-one target

The spin state of a target of spin `s` is a positive semidefinite, unit-trace density matrix `ρ`
on the `2s + 1`-dimensional spin space. Given spin matrices `S₀, S₁, S₂` on that space, the
*vector polarization* and the *tensor polarization* of `ρ` are the expectation values

* `Pₖ = tr (ρ Sₖ)`,
* `Pᵢⱼ = tr (ρ Σᵢⱼ)`, where `Σᵢⱼ = (3/2) (Sᵢ Sⱼ + Sⱼ Sᵢ) - δᵢⱼ ∑ₖ Sₖ Sₖ`

is the symmetric traceless rank-two *tensor operator*. For an irreducible spin the Casimir
`∑ₖ Sₖ Sₖ` is `s (s + 1)`, so `Σᵢⱼ` is the usual `(3/2) {Sᵢ, Sⱼ} - s (s + 1) δᵢⱼ`; for spin one
`P₂₂ = tr (ρ (3 S₂² - 2))` is the tensor polarization `P_zz = n₊ + n₋ - 2 n₀` along the
quantization axis, in terms of the populations `n_m` of the magnetic substates.

This file develops the two spins that matter for light nuclei.

* **Spin one** (the deuteron), in the Cartesian basis, where `(Sₖ)ₐᵦ = -i εₖₐᵦ` (`spinOne`).
  The matrices `1`, `Sₖ`, `Σᵢⱼ` span all `3 × 3` matrices, and the three families are mutually
  orthogonal for the trace form: every `ρ` is
  `ρ = (tr ρ / 3) 1 + (1/2) ∑ₖ Pₖ Sₖ + (1/9) ∑ᵢⱼ Pᵢⱼ Σᵢⱼ`
  (`spinOne_decomposition`), and the three pieces are the trace part, the antisymmetric part
  `(ρ - ρᵀ) / 2` and the symmetric traceless part `(ρ + ρᵀ) / 2 - (tr ρ / 3) 1` of `ρ`. In the
  language of representations these are the components of degree zero, one and two of a
  spin-one density matrix (scalar, vector polarization, tensor polarization); this file
  identifies them concretely and does not develop the rotation action.
* **Spin one half** (the nucleon), with `Sₖ = σₖ / 2` (`spinHalf`). Here the tensor operator
  vanishes identically (`tensorOperator_spinHalf`), because `{σᵢ, σⱼ} = 2 δᵢⱼ`: a spin-one-half
  target carries no tensor polarization (`tensorPolarization_spinHalf`). This is the structural
  reason why the tensor structure functions of a spin-one target have no spin-one-half analogue.

Positive semidefiniteness of a unit-trace `ρ` bounds the spin-one polarizations:
`-2 ≤ Pᵢᵢ ≤ 1` and `3 |Pₖ| ≤ 2 + Pₖₖ` (so `|Pₖ| ≤ 1`). Both bounds on `Pₖₖ` are attained by
pure states: the state of zero spin projection along axis `k`, which has vanishing vector
polarization and the extreme tensor polarization `Pₖₖ = -2`, and a state of zero spin
projection along a perpendicular axis, which has `Pₖₖ = 1`.

## Main definitions

* `EpsilonEridani.Spin.tensorOperator`: the tensor operator `Σᵢⱼ` built from spin matrices.
* `EpsilonEridani.Spin.vectorPolarization`, `EpsilonEridani.Spin.tensorPolarization`: `Pₖ`, `Pᵢⱼ`.
* `EpsilonEridani.Spin.spinOne`, `EpsilonEridani.Spin.spinHalf`: the spin matrices of spin one
  and spin one half.

## Main results

* `EpsilonEridani.Spin.spinOne_commutator_zero_one` (and its cyclic partners) and
  `EpsilonEridani.Spin.sum_spinOne_mul_self`: `spinOne` is a spin-one representation.
* `EpsilonEridani.Spin.spinOne_decomposition`: completeness of the decomposition.
* `EpsilonEridani.Spin.trace_spinOne_mul_spinOne`,
  `EpsilonEridani.Spin.trace_spinOne_mul_tensorOperator`,
  `EpsilonEridani.Spin.trace_tensorOperator_mul_tensorOperator`: its orthogonality.
* `EpsilonEridani.Spin.tensorPolarization_spinHalf`: a spin-one-half state has no tensor
  polarization.
* `EpsilonEridani.Spin.neg_two_le_re_tensorPolarization_spinOne`,
  `EpsilonEridani.Spin.re_tensorPolarization_spinOne_le_one`,
  `EpsilonEridani.Spin.three_mul_norm_vectorPolarization_spinOne_le`: the positivity bounds.

## References

* P. Hoodbhoy, R. L. Jaffe and A. Manohar, *Novel effects in deep inelastic scattering from
  spin-one hadrons*, Nucl. Phys. B312 (1989) 571.
* E. Leader, *Spin in Particle Physics*, Cambridge University Press (2001), §3.1.
* A. Airapetian et al. (HERMES), *First measurement of the tensor structure function `b₁` of the
  deuteron*, Phys. Rev. Lett. 95 (2005) 242001 (the convention `P_zz = n₊ + n₋ - 2 n₀`).
-/

public section

noncomputable section

namespace EpsilonEridani.Spin

open Matrix Complex

/-! ### The tensor operator and the polarizations -/

section General

variable {n : Type*} [Fintype n]

/-- The **tensor operator** `Σᵢⱼ = (3/2) (Sᵢ Sⱼ + Sⱼ Sᵢ) - δᵢⱼ ∑ₖ Sₖ Sₖ` of a triple of spin
matrices `S`: the symmetric traceless rank-two combination of the spin matrices. For an
irreducible spin `s`, where `∑ₖ Sₖ Sₖ = s (s + 1)`, it is `(3/2) {Sᵢ, Sⱼ} - s (s + 1) δᵢⱼ`. -/
def tensorOperator (S : Fin 3 → Matrix n n ℂ) (i j : Fin 3) : Matrix n n ℂ :=
  (3 / 2 : ℂ) • (S i * S j + S j * S i) - if i = j then ∑ k, S k * S k else 0

/-- The **vector polarization** `Pₖ = tr (ρ Sₖ)` of a spin density matrix `ρ`: the expectation
value of the spin component `Sₖ`. This is the conventional polarization vector for spin one; for
a general spin `s` the conventional polarization vector is `Pₖ / s`. -/
def vectorPolarization (S : Fin 3 → Matrix n n ℂ) (ρ : Matrix n n ℂ) (k : Fin 3) : ℂ :=
  (ρ * S k).trace

/-- The **tensor polarization** `Pᵢⱼ = tr (ρ Σᵢⱼ)` of a spin density matrix `ρ`: the expectation
value of the tensor operator `Σᵢⱼ`. -/
def tensorPolarization (S : Fin 3 → Matrix n n ℂ) (ρ : Matrix n n ℂ) (i j : Fin 3) : ℂ :=
  (ρ * tensorOperator S i j).trace

variable (S : Fin 3 → Matrix n n ℂ)

lemma tensorOperator_def (i j : Fin 3) :
    tensorOperator S i j =
      (3 / 2 : ℂ) • (S i * S j + S j * S i) - if i = j then ∑ k, S k * S k else 0 := (rfl)

lemma vectorPolarization_def (ρ : Matrix n n ℂ) (k : Fin 3) :
    vectorPolarization S ρ k = (ρ * S k).trace := (rfl)

lemma tensorPolarization_def (ρ : Matrix n n ℂ) (i j : Fin 3) :
    tensorPolarization S ρ i j = (ρ * tensorOperator S i j).trace := (rfl)

/-- The tensor operator is symmetric in its two indices. -/
lemma tensorOperator_comm (i j : Fin 3) : tensorOperator S i j = tensorOperator S j i := by
  simp only [tensorOperator_def, add_comm (S i * S j), eq_comm (a := i)]

/-- The tensor operator is traceless as a rank-two tensor: `∑ᵢ Σᵢᵢ = 0`. -/
@[simp]
lemma sum_tensorOperator_self : ∑ i, tensorOperator S i i = 0 := by
  simp only [tensorOperator_def, ite_true, Finset.sum_sub_distrib, ← Finset.smul_sum,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

/-- The tensor polarization is symmetric in its two indices. -/
lemma tensorPolarization_comm (ρ : Matrix n n ℂ) (i j : Fin 3) :
    tensorPolarization S ρ i j = tensorPolarization S ρ j i := by
  rw [tensorPolarization_def, tensorOperator_comm, tensorPolarization_def]

/-- The tensor polarization is traceless: `∑ᵢ Pᵢᵢ = 0`. -/
@[simp]
lemma sum_tensorPolarization_self (ρ : Matrix n n ℂ) : ∑ i, tensorPolarization S ρ i i = 0 := by
  simp only [tensorPolarization_def, ← trace_sum, ← Matrix.mul_sum, sum_tensorOperator_self,
    Matrix.mul_zero, trace_zero]

end General

/-! ### Spin one -/

/-- The **spin-one matrices** in the Cartesian basis, `(Sₖ)ₐᵦ = -i εₖₐᵦ`: the generators of
rotations acting on three-vectors, which is the spin-one representation. -/
def spinOne : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, 0, 0; 0, 0, -I; 0, I, 0], !![0, 0, I; 0, 0, 0; -I, 0, 0],
    !![0, -I, 0; I, 0, 0; 0, 0, 0]]

/-- The product of two spin-one matrices: `(Sᵢ Sⱼ)ₐᵦ = δᵢⱼ δₐᵦ - δᵢᵦ δⱼₐ`, the contraction
identity `εᵢₐₖ εⱼᵦₖ = δᵢⱼ δₐᵦ - δᵢᵦ δₐⱼ`. -/
lemma spinOne_mul_spinOne_apply (i j a b : Fin 3) :
    (spinOne i * spinOne j) a b =
      (if i = j ∧ a = b then 1 else 0) - (if i = b ∧ j = a then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [spinOne, Matrix.mul_apply, Fin.sum_univ_three]

/-- The entries of a spin-one matrix are antisymmetric: `(Sₖ)ᵦₐ = -(Sₖ)ₐᵦ`. -/
lemma spinOne_apply_swap (k a b : Fin 3) : spinOne k b a = -spinOne k a b := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [spinOne]

/-- The diagonal entries of a spin-one matrix vanish. -/
@[simp]
lemma spinOne_apply_self (k a : Fin 3) : spinOne k a a = 0 := by
  fin_cases k <;> fin_cases a <;> simp [spinOne]

/-- The spin-one matrices are hermitian. -/
lemma isHermitian_spinOne (k : Fin 3) : (spinOne k).IsHermitian := by
  ext a b
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [spinOne]

/-- The spin-one matrices obey the angular-momentum algebra: `[S₀, S₁] = i S₂`. -/
lemma spinOne_commutator_zero_one :
    spinOne 0 * spinOne 1 - spinOne 1 * spinOne 0 = I • spinOne 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [spinOne]

/-- The spin-one matrices obey the angular-momentum algebra: `[S₁, S₂] = i S₀`. -/
lemma spinOne_commutator_one_two :
    spinOne 1 * spinOne 2 - spinOne 2 * spinOne 1 = I • spinOne 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [spinOne]

/-- The spin-one matrices obey the angular-momentum algebra: `[S₂, S₀] = i S₁`. -/
lemma spinOne_commutator_two_zero :
    spinOne 2 * spinOne 0 - spinOne 0 * spinOne 2 = I • spinOne 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [spinOne]

/-- The Casimir of the spin-one matrices is `s (s + 1) = 2`. -/
lemma sum_spinOne_mul_self : ∑ k, spinOne k * spinOne k = (2 : ℂ) • 1 := by
  ext a b
  simp only [Matrix.sum_apply, spinOne_mul_spinOne_apply, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> norm_num

/-- The spin-one matrices are traceless. -/
@[simp]
lemma trace_spinOne (k : Fin 3) : (spinOne k).trace = 0 := by
  simp [trace_fin_three]

/-- The spin-one matrices are orthogonal for the trace form: `tr (Sᵢ Sⱼ) = 2 δᵢⱼ`. -/
lemma trace_spinOne_mul_spinOne (i j : Fin 3) :
    (spinOne i * spinOne j).trace = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [trace_fin_three, spinOne_mul_spinOne_apply] <;> norm_num

/-- The entries of the spin-one tensor operator:
`(Σᵢⱼ)ₐᵦ = δᵢⱼ δₐᵦ - (3/2) (δᵢₐ δⱼᵦ + δᵢᵦ δⱼₐ)`. -/
lemma tensorOperator_spinOne_apply (i j a b : Fin 3) :
    tensorOperator spinOne i j a b =
      (if i = j ∧ a = b then 1 else 0) -
        (3 / 2 : ℂ) * ((if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0)) := by
  rw [tensorOperator_def, sum_spinOne_mul_self]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [spinOne_mul_spinOne_apply] <;> norm_num

/-- The spin-one tensor operator is traceless. -/
@[simp]
lemma trace_tensorOperator_spinOne (i j : Fin 3) : (tensorOperator spinOne i j).trace = 0 := by
  fin_cases i <;> fin_cases j <;> simp [trace_fin_three, tensorOperator_spinOne_apply] <;> norm_num

/-- The vector polarization of a spin-one state along the first axis:
`P₀ = i (ρ₁₂ - ρ₂₁)`. -/
lemma vectorPolarization_spinOne_zero (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    vectorPolarization spinOne ρ 0 = I * (ρ 1 2 - ρ 2 1) := by
  simp [vectorPolarization_def, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, spinOne]
  ring

/-- The vector polarization of a spin-one state along the second axis:
`P₁ = i (ρ₂₀ - ρ₀₂)`. -/
lemma vectorPolarization_spinOne_one (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    vectorPolarization spinOne ρ 1 = I * (ρ 2 0 - ρ 0 2) := by
  simp [vectorPolarization_def, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, spinOne]
  ring

/-- The vector polarization of a spin-one state along the third axis:
`P₂ = i (ρ₀₁ - ρ₁₀)`. -/
lemma vectorPolarization_spinOne_two (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    vectorPolarization spinOne ρ 2 = I * (ρ 0 1 - ρ 1 0) := by
  simp [vectorPolarization_def, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, spinOne]
  ring

/-- The tensor polarization of a spin-one state in terms of the entries of its density matrix:
`Pᵢⱼ = δᵢⱼ tr ρ - (3/2) (ρᵢⱼ + ρⱼᵢ)`. -/
lemma tensorPolarization_spinOne (ρ : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    tensorPolarization spinOne ρ i j =
      (if i = j then ρ.trace else 0) - (3 / 2 : ℂ) * (ρ i j + ρ j i) := by
  rw [tensorPolarization_def, trace_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, tensorOperator_spinOne_apply, trace_fin_three] <;>
    ring

/-- The diagonal tensor polarization of a spin-one state: `Pᵢᵢ = tr ρ - 3 ρᵢᵢ`. -/
lemma tensorPolarization_spinOne_self (ρ : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) :
    tensorPolarization spinOne ρ i i = ρ.trace - 3 * ρ i i := by
  rw [tensorPolarization_spinOne, ite_eq_left rfl]
  ring

/-- The spin-one matrices are orthogonal to the tensor operators for the trace form. -/
@[simp]
lemma trace_spinOne_mul_tensorOperator (k i j : Fin 3) :
    (spinOne k * tensorOperator spinOne i j).trace = 0 := by
  rw [← tensorPolarization_def, tensorPolarization_spinOne, spinOne_apply_swap]
  simp

/-- The Gram matrix of the spin-one tensor operators for the trace form:
`tr (Σᵢⱼ Σₖₗ) = (9/2) (δᵢₖ δⱼₗ + δᵢₗ δⱼₖ) - 3 δᵢⱼ δₖₗ`. -/
lemma trace_tensorOperator_mul_tensorOperator (i j k l : Fin 3) :
    (tensorOperator spinOne i j * tensorOperator spinOne k l).trace =
      (9 / 2 : ℂ) * ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) -
        3 * (if i = j ∧ k = l then 1 else 0) := by
  rw [← tensorPolarization_def, tensorPolarization_spinOne, trace_tensorOperator_spinOne,
    tensorOperator_spinOne_apply, tensorOperator_spinOne_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp <;> norm_num

/-- The vector-polarization part of a spin-one density matrix is its antisymmetric part:
`∑ₖ Pₖ Sₖ = ρ - ρᵀ`. -/
lemma sum_vectorPolarization_smul_spinOne (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ k, vectorPolarization spinOne ρ k • spinOne k = ρ - ρᵀ := by
  ext a b
  simp only [Matrix.sum_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
    vectorPolarization_spinOne_zero, vectorPolarization_spinOne_one,
    vectorPolarization_spinOne_two, Matrix.sub_apply, Matrix.transpose_apply]
  fin_cases a <;> fin_cases b <;> simp [spinOne] <;> ring_nf <;> simp [I_sq] <;> ring

/-- The tensor-polarization part of a spin-one density matrix is its symmetric traceless part:
`∑ᵢⱼ Pᵢⱼ Σᵢⱼ = (9/2) (ρ + ρᵀ) - 3 (tr ρ) 1`. -/
lemma sum_tensorPolarization_smul_tensorOperator (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ i, ∑ j, tensorPolarization spinOne ρ i j • tensorOperator spinOne i j =
      (9 / 2 : ℂ) • (ρ + ρᵀ) - (3 * ρ.trace) • 1 := by
  ext a b
  simp only [Matrix.sum_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
    tensorPolarization_spinOne, tensorOperator_spinOne_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.one_apply, trace_fin_three]
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-- **Completeness of the spin-one decomposition.** Every `3 × 3` matrix, in particular every
spin-one density matrix, is recovered from its trace, its vector polarization and its tensor
polarization:
`ρ = (tr ρ / 3) 1 + (1/2) ∑ₖ Pₖ Sₖ + (1/9) ∑ᵢⱼ Pᵢⱼ Σᵢⱼ`.
The three terms are the trace part, the antisymmetric part and the symmetric traceless part of
`ρ` (`sum_vectorPolarization_smul_spinOne`, `sum_tensorPolarization_smul_tensorOperator`). -/
theorem spinOne_decomposition (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    ρ = (ρ.trace / 3) • 1 + (1 / 2 : ℂ) • ∑ k, vectorPolarization spinOne ρ k • spinOne k +
      (1 / 9 : ℂ) • ∑ i, ∑ j, tensorPolarization spinOne ρ i j • tensorOperator spinOne i j := by
  rw [sum_vectorPolarization_smul_spinOne, sum_tensorPolarization_smul_tensorOperator]
  module

/-! ### Positivity bounds for spin one -/

section Bounds

open scoped ComplexOrder

variable {ρ : Matrix (Fin 3) (Fin 3) ℂ}

/-- The tensor polarization of a spin-one state is at most one: `Pᵢᵢ ≤ 1`. -/
theorem re_tensorPolarization_spinOne_le_one (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (i : Fin 3) : (tensorPolarization spinOne ρ i i).re ≤ 1 := by
  have := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := i))).1
  simp only [tensorPolarization_spinOne_self, htr, sub_re, one_re, mul_re, re_ofNat, im_ofNat,
    zero_mul, sub_zero]
  linarith

/-- The tensor polarization of a spin-one state is at least minus two: `-2 ≤ Pᵢᵢ`. -/
theorem neg_two_le_re_tensorPolarization_spinOne (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (i : Fin 3) : -2 ≤ (tensorPolarization spinOne ρ i i).re := by
  have h0 := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := 0))).1
  have h1 := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := 1))).1
  have h2 := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := 2))).1
  have : (ρ 0 0).re + (ρ 1 1).re + (ρ 2 2).re = 1 := by
    simpa [trace_fin_three] using congrArg re htr
  simp only [tensorPolarization_spinOne_self, htr, sub_re, one_re, mul_re, re_ofNat, im_ofNat,
    zero_mul, sub_zero]
  fin_cases i <;> simp <;> linarith

/-- **The vector polarization of a spin-one state is bounded by its tensor polarization**:
`3 |Pₖ| ≤ 2 + Pₖₖ`. Since `Pₖₖ ≤ 1`, this gives `|Pₖ| ≤ 1`; and a state with the extreme
tensor polarization `Pₖₖ = -2` has no vector polarization along `k`. -/
theorem three_mul_norm_vectorPolarization_spinOne_le (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (k : Fin 3) :
    3 * ‖vectorPolarization spinOne ρ k‖ ≤ 2 + (tensorPolarization spinOne ρ k k).re := by
  have key (a b : Fin 3) : ‖I * (ρ a b - ρ b a)‖ ≤ (ρ a a).re + (ρ b b).re := by
    rw [norm_mul, norm_I, one_mul]
    have hab := hρ.two_mul_norm_apply_le a b
    have hba := hρ.two_mul_norm_apply_le b a
    simp only [RCLike.re_to_complex] at hab hba
    linarith [norm_sub_le (ρ a b) (ρ b a)]
  have : (ρ 0 0).re + (ρ 1 1).re + (ρ 2 2).re = 1 := by
    simpa [trace_fin_three] using congrArg re htr
  simp only [tensorPolarization_spinOne_self, htr, sub_re, one_re, mul_re, re_ofNat, im_ofNat,
    zero_mul, sub_zero]
  fin_cases k
  · have := key 1 2
    simp only [Fin.zero_eta, vectorPolarization_spinOne_zero]
    linarith
  · have := key 2 0
    simp only [Fin.mk_one, vectorPolarization_spinOne_one]
    linarith
  · have := key 0 1
    simp only [Fin.reduceFinMk, vectorPolarization_spinOne_two]
    linarith

/-- The pure state of zero spin projection along axis `k`, the projector onto the `k`-th
Cartesian basis vector, has no vector polarization. -/
@[simp]
lemma vectorPolarization_spinOne_single_self (k l : Fin 3) :
    vectorPolarization spinOne (single k k 1) l = 0 := by
  simp [vectorPolarization_def, trace_single_mul]

/-- The pure state of zero spin projection along axis `k` has the extreme tensor polarization
`Pₖₖ = -2`, so the bound `neg_two_le_re_tensorPolarization_spinOne` is sharp. -/
lemma tensorPolarization_spinOne_single_self (k : Fin 3) :
    tensorPolarization spinOne (single k k 1) k k = -2 := by
  rw [tensorPolarization_spinOne_self, trace_single_eq_same, single_apply_same]
  norm_num

/-- The pure state of zero spin projection along an axis `l` perpendicular to `k` has tensor
polarization `Pₖₖ = 1`, so the bound `re_tensorPolarization_spinOne_le_one` is sharp. -/
lemma tensorPolarization_spinOne_single_of_ne {k l : Fin 3} (h : l ≠ k) :
    tensorPolarization spinOne (single l l 1) k k = 1 := by
  rw [tensorPolarization_spinOne_self, trace_single_eq_same]
  simp [h]

end Bounds

/-! ### Spin one half -/

/-- The **spin-one-half matrices** `Sₖ = σₖ / 2`. -/
def spinHalf (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • PauliMatrix.pauliMatrix (Sum.inr k)

/-- The Casimir of the spin-one-half matrices is `s (s + 1) = 3/4`. -/
lemma sum_spinHalf_mul_self : ∑ k, spinHalf k * spinHalf k = (3 / 4 : ℂ) • 1 := by
  simp only [spinHalf, smul_mul_smul_comm, PauliMatrix.pauliMatrix_mul_self, Fin.sum_univ_three]
  module

/-- **The tensor operator vanishes for spin one half**: `(3/2) {Sᵢ, Sⱼ} = (3/4) δᵢⱼ`, which is
exactly the Casimir term. -/
@[simp]
theorem tensorOperator_spinHalf (i j : Fin 3) : tensorOperator spinHalf i j = 0 := by
  have h : spinHalf i * spinHalf j + spinHalf j * spinHalf i =
      (1 / 4 : ℂ) • (PauliMatrix.pauliMatrix (Sum.inr i) * PauliMatrix.pauliMatrix (Sum.inr j) +
        PauliMatrix.pauliMatrix (Sum.inr j) * PauliMatrix.pauliMatrix (Sum.inr i)) := by
    simp only [spinHalf, smul_mul_smul_comm, smul_add]
    norm_num
  rw [tensorOperator_def, h, PauliMatrix.pauliMatrix_anticommutator, sum_spinHalf_mul_self]
  by_cases hij : i = j
  · subst hij
    simp [KroneckerDelta.kroneckerDelta, smul_smul]
    norm_num
  · simp [hij, KroneckerDelta.kroneckerDelta]

/-- **A spin-one-half target has no tensor polarization.** -/
@[simp]
theorem tensorPolarization_spinHalf (ρ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 3) :
    tensorPolarization spinHalf ρ i j = 0 := by
  simp [tensorPolarization_def]

end EpsilonEridani.Spin
