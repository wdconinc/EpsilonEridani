/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Nuclear structure

A nucleus is a structure carrying a mass number `A : ℕ` with `0 < A`, a proton number
`Z : ℕ` with `Z ≤ A`, and the derived neutron number `N = A - Z`. A nucleus is *isoscalar*
when `2 Z = A`. The free proton is the nucleus with `A = Z = 1` and the free neutron is
`A = 1, Z = 0`; the deuteron is `A = 2, Z = 1`.

-/

@[expose] public section

namespace EpsilonEridani
namespace Particles
namespace Nuclei

/-- A nucleus with mass number `A`, proton number `Z ≤ A`, and the derived neutron number `N = A - Z`.
A nucleus is *isoscalar* when `2 Z = A`. The free proton is the nucleus with `A = Z = 1` and the
free neutron is `A = 1, Z = 0`; the deuteron is `A = 2, Z = 1`. -/
structure Nucleus where
  A : ℕ
  Z : ℕ
  hZ_le_A : Z ≤ A
  deriving DecidableEq

namespace Nucleus

variable (N : Nucleus)

/-- The neutron number, derived as `N := A - Z`. -/
def neutronNumber (N : Nucleus) : ℕ := N.A - N.Z

lemma neutronNumber_add_protonNumber (N : Nucleus) : N.neutronNumber + N.Z = N.A := by
  rw [neutronNumber, Nat.add_sub_cancel' N.hZ_le_A]

lemma sum_proton_neutron (N : Nucleus) : N.Z + N.neutronNumber = N.A := by
  rw [neutronNumber, add_comm, Nat.add_sub_cancel' N.hZ_le_A]

/-- A nucleus is *isoscalar* when it has equal numbers of protons and neutrons. -/
def IsIsoscalar (N : Nucleus) : Prop := N.Z = N.neutronNumber

lemma isIsoscalar_iff (N : Nucleus) : N.IsIsoscalar ↔ 2 * N.Z = N.A := by
  constructor
  · intro h
    have hsum : N.Z + N.neutronNumber = N.A := N.sum_proton_neutron
    rw [h] at hsum
    omega
  · intro h
    have hsum : N.Z + N.neutronNumber = N.A := N.sum_proton_neutron
    omega

/-- The free proton: mass number 1, proton number 1, neutron number 0. -/
def freeProton : Nucleus := ⟨1, 1, by omega⟩

lemma freeProton_sum : freeProton.sum_proton_neutron := by
  unfold freeProton; rfl

lemma freeProton_isIsoscalar : ¬ freeProton.IsIsoscalar := by
  unfold freeProton IsIsoscalar neutronNumber; norm_num

/-- The free neutron: mass number 1, proton number 0, neutron number 1. -/
def freeNeutron : Nucleus := ⟨1, 0, by omega⟩

lemma freeNeutron_sum : freeNeutron.sum_proton_neutron := by
  unfold freeNeutron; rfl

lemma freeNeutron_isIsoscalar : ¬ freeNeutron.IsIsoscalar := by
  unfold freeNeutron IsIsoscalar neutronNumber; norm_num

/-- The deuteron: mass number 2, proton number 1, neutron number 1. -/
def deuteron : Nucleus := ⟨2, 1, by omega⟩

lemma deuteron_sum : deuteron.sum_proton_neutron := by
  unfold deuteron; rfl

lemma deuteron_isIsoscalar : deuteron.IsIsoscalar := by
  unfold deuteron IsIsoscalar neutronNumber; rfl

end Nucleus

end Nuclei
end Particles
end EpsilonEridani
