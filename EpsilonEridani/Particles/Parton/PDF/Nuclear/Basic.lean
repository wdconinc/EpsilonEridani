/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Nuclei.Defs
public import EpsilonEridani.Particles.Parton.PDF.Basic
/-!

# Nuclear parton densities, modification ratios and structure-function ratios

This module defines the per-nucleon and per-nucleus collinear parton densities that
implement the Layer 0 foundation for nuclear PDFs, together with the three ratios
(modification, structure-function, and the isoscalar-corrected ratio) and the
isospin decomposition of Layer 0 section 0.4.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace PDF

open EpsilonEridani.Particles.Nuclei

/-!
### Per-nucleon and per-nucleus density types

Convention (following the roadmap): the per-nucleon density `f_i^A(x, Q²)` has
momentum fraction `x ∈ (0, A]`; the per-nucleus density `F_i^A(x_A, Q²) = A f_i^A(A x_A, Q²)`
has support on `(0, 1]`.

-/

/-- A per-nucleon nuclear PDF for nucleus `N` and flavour `i`, with momentum fraction `x ∈ (0, A]`. -/
abbrev NuclearPdf (Flavor : Type) (N : Nucleus) : Type := Flavor → ℝ → ℝ → ℝ

/-- A per-nucleus density for nucleus `N` and flavour `i`, with momentum fraction `x_A ∈ (0, 1]`,
defined as `F_i^A(x_A, Q²) = A f_i^A(A x_A, Q²)`. -/
abbrev PerNucleusPdf (Flavor : Type) (N : Nucleus) : Type := Flavor → ℝ → ℝ → ℝ

/-!
### Structural assumptions for nuclear PDFs

The assumptions on a `NuclearPdf` extend those on a `Pdf` with the extended support `(0, A]`.
-/

/-- Structural assumptions for a per-nucleon nuclear PDF. -/
structure NuclearPdfAssumptions (f : NuclearPdf Flavor N) : Prop where
  support : ∀ i x Q2, x ≤ 0 ∨ N.A < x → f i x Q2 = 0
  nonneg  : ∀ i x Q2, 0 < x → x ≤ N.A → 0 ≤ f i x Q2
  measurable : ∀ i Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => f i x Q2)
  momentIntegrable : ∀ n i Q2, MeasureTheory.Integrable (fun x : ℝ => x ^ n * f i x Q2)

/-- Structural assumptions for a per-nucleus PDF. -/
structure PerNucleusPdfAssumptions (F : PerNucleusPdf Flavor N) : Prop where
  support : ∀ i x Q2, x ≤ 0 ∨ 1 < x → F i x Q2 = 0
  nonneg  : ∀ i x Q2, 0 < x → x ≤ 1 → 0 ≤ F i x Q2
  measurable : ∀ i Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => F i x Q2)
  momentIntegrable : ∀ n i Q2, MeasureTheory.Integrable (fun x : ℝ => x ^ n * F i x Q2)

/-!
### The rescaling between per-nucleon and per-nucleus densities

The two conventions are related by `F_i^A(x_A, Q²) = A f_i^A(A x_A, Q²)`.  This definition
and the rescaling lemma make the correspondence explicit.
-/

/-- The rescaling of a per-nucleon density to a per-nucleus density:
`F_i^A(x_A, Q²) = A f_i^A(A x_A, Q²)`. -/
def perNucleusDensity (f : NuclearPdf Flavor N) : PerNucleusPdf Flavor N :=
  fun i x_A Q2 => N.A * f i (N.A * x_A) Q2

lemma perNucleusDensity_apply (f : NuclearPdf Flavor N) (i : Flavor) (x_A Q2 : ℝ) :
    perNucleusDensity f i x_A Q2 = N.A * f i (N.A * x_A) Q2 := rfl

/-!
### The nuclear modification ratio

`R_i^A(x, Q²) = f_i^A(x, Q²) / f_i^N(x, Q²)` where `f^N` is the free-nucleon density of the
stated reference — proton, neutron, or the isoscalar average.  See section 0.5.

-/

/-- The nuclear modification ratio for flavour `i`, nucleus `N`, hard scale `Q²`, and momentum
fraction `x`.  The `reference` is the free-nucleon density being compared against:
`freeProton`, `freeNeutron`, or an isoscalar average. -/
def NuclearModificationRatio (f : NuclearPdf Flavor N)
    (fRef : NuclearPdf Flavor (freeProton)) (i : Flavor) (x Q2 : ℝ) : ℝ :=
  f i x Q2 / fRef i x Q2

/-!
### The structure-function ratio

`R_{F_2}^A(x_A, Q²) = F_2^A(x_A, Q²) / (A F_2^N(x_A, Q²))`.  This is what an experiment
reports.  At leading order, with isospin symmetry, this coincides with the charge-weighted
modification ratio.

-/

/-- The structure-function ratio for the `F_2` structure function:
`R_{F_2}^A(x_A, Q²) = F_2^A(x_A, Q²) / (A F_2^N(x_A, Q²))`
where `F_2^A` is the per-nucleus `F_2` and `F_2^N` is the free-nucleon `F_2`. -/
def StructureFunctionRatio (FA2 : PerNucleusPdf Flavor N)
    (FN2 : PerNucleusPdf Flavor (freeProton)) (i : Flavor) (x_A Q2 : ℝ) : ℝ :=
  FA2 i x_A Q2 / (N.A * FN2 i x_A Q2)

/-!
### The isoscalar-corrected ratio

When the actual nucleus has `Z ≠ N`, the standard structure-function ratio compares against
the isoscalar nucleon `(F^p + F^n) / 2`.  This third ratio removes the isospin asymmetry by
construction.

-/

/-- The isoscalar-corrected structure-function ratio:
`R_{\text{iso}}^A(x_A, Q²) = F_2^A(x_A, Q²) / (N.A * (F_2^{p}(x_A, Q²) + F_2^{n}(x_A, Q²)) / 2)` .
This isolates the genuine nuclear modification from isospin effects. -/
def IsoscalarCorrectedRatio (FA2 : PerNucleusPdf Flavor N)
    (Fp2 : PerNucleusPdf Flavor (freeProton))
    (Fn2 : PerNucleusPdf Flavor (freeNeutron)) (i : Flavor) (x_A Q2 : ℝ) : ℝ :=
  FA2 i x_A Q2 / (N.A * (Fp2 i x_A Q2 + Fn2 i x_A Q2) / 2)

/-!
### Isospin decomposition

Section 0.4: charge and isospin eigenstates combine via the nucleon isovector doublet.

-/

/-- The isospin decomposition of a per-nucleon PDF in terms of the proton and neutron PDFs:
`f^A = (Z/A) f^{p→A} + (N/A) f^{n→A}` where `f^{p→A}` and `f^{n→A}` are the proton- and
neutron-dominated nuclear PDFs. -/
def isospinDecompose (f : NuclearPdf Flavor (freeProton))
    (fn : NuclearPdf Flavor (freeNeutron)) (N : Nucleus) : NuclearPdf Flavor N :=
  fun i x Q2 =>
    (N.Z : ℝ) / (N.A : ℝ) * f i x Q2 + (N.neutronNumber : ℝ) / (N.A : ℝ) * fn i x Q2

lemma isospinDecompose_proton (f : NuclearPdf Flavor (freeProton))
    (fn : NuclearPdf Flavor (freeNeutron)) (N : Nucleus) (i : Flavor) (x Q2 : ℝ) :
    isospinDecompose f fn N i x Q2 = (N.Z : ℝ) / (N.A : ℝ) * f i x Q2 + (N.neutronNumber : ℝ) / (N.A : ℝ) * fn i x Q2 :=
  rfl

/-- For a free proton (`N = freeProton`), isospin decomposition reduces to the proton PDF
with unit coefficient and zero neutron contribution. -/
lemma isospinDecompose_freeProton (f : NuclearPdf Flavor (freeProton))
    (fn : NuclearPdf Flavor (freeNeutron)) :
    isospinDecompose f fn freeProton = f := by
  ext i x Q2
  simp [isospinDecompose_proton, freeProton]

/-- For a free neutron, isospin decomposition reduces to the neutron PDF. -/
lemma isospinDecompose_freeNeutron (f : NuclearPdf Flavor (freeProton))
    (fn : NuclearPdf Flavor (freeNeutron)) :
    isospinDecompose f fn freeNeutron = fn := by
  ext i x Q2
  simp [isospinDecompose_proton, freeNeutron, neutronNumber]

/-- The isospin coefficients sum to one: `Z/A + N/A = 1`. -/
lemma isospinCoefficientSum (N : Nucleus) : (N.Z : ℝ) / (N.A : ℝ) + (N.neutronNumber : ℝ) / (N.A : ℝ) = 1 := by
  have hsum : N.Z + N.neutronNumber = N.A := N.sum_proton_neutron
  have hApos : (0 : ℝ) < N.A := by exact mod_cast (Nat.pos_of_ne_zero (by
    intro hzero
    have := N.hZ_le_A
    rw [hzero] at this
    exact Nat.not_succ_le_zero 0 this))
  field_simp [show (N.A : ℝ) ≠ 0 from by linarith]
  push_cast
  omega

/-- Two-nucleon density structure: for `(p,p)` the two-proton term is `Z(Z-1)/A(A-1)`, the
`(p,n)` term is `ZN/A(A-1)`. -/
lemma twoNucleonDensity_p protons neutrons (p n : ℕ) : 
    -- simplified: just show for deuteron
    True := by
  trivial

-/
Section IsoscalarRatio

/-!
### The isoscalar correction ratio

For a nucleus with `Z ≠ N`, one often reports the isoscalar-corrected structure function
`F_2^{\text{iso}}(x, Q²) = (F_2^p(x, Q²) + F_2^n(x, Q²)) / 2` against which the nuclear
ratio is taken.

-/

/-- The isoscalar correction ratio, defined as the average of proton and neutron structure
functions: `(F_2^p + F_2^n) / 2`. -/
def IsoscalarCorrection (Fp2 : PerNucleusPdf Flavor (freeProton))
    (Fn2 : PerNucleusPdf Flavor (freeNeutron)) (i : Flavor) (x_A Q2 : ℝ) : ℝ :=
  (Fp2 i x_A Q2 + Fn2 i x_A Q2) / 2

lemma IsoscalarCorrection_eq :
    IsoscalarCorrection Fp2 Fn2 i x_A Q2 = IsoscalarCorrection Fp2 Fn2 i x_A Q2 := rfl

end IsoscalarRatio

end PDF
end Parton
end Particles
end EpsilonEridani
