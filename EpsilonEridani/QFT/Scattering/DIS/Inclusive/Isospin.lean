/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.Particles.Parton.PDF.Basic
public import EpsilonEridani.QFT.Scattering.DIS.CrossSection

/-!
# Isospin, the neutron, and the proton-neutron difference of `F₂`

In the quark-parton model the neutral-current structure function of a target is
`F₂ = x Σ_f e_f² (q_f + qbar_f)` (`DIS.f2LO`), where `q_f + qbar_f` is the target's quark plus
antiquark density of flavour `f`. Exact isospin symmetry relates the neutron to the proton: the
neutron's densities are the proton's with up and down exchanged, `q^n_f = q^p_{τ f}` with
`τ = Equiv.swap u d` the isospin involution, which fixes every other flavour. The neutron density
is therefore the pullback `PDF.comap τ q^p`; that the two nucleons are related this way is the
assumption of exact isospin symmetry, and its violation is not modelled here. Since `F₂` sees only
the combination `q_f + qbar_f`, relabelling the flavours of that combination is all the neutron
needs.

Relabelling the flavours of a density is the same as relabelling the charges the other way
(`f2LO_comap`), so the neutron is the proton with the up and down charges exchanged. Every flavour
other than up and down then drops out of the difference:

  `F₂^p - F₂^n = x (e_u² - e_d²) ((u + ubar) - (d + dbar))`  (`f2LO_sub_f2LO_comap_swap`),

which for the light flavours, `e_u = 2/3` and `e_d = e_s = -1/3`, is the identity
`F₂^p - F₂^n = (x / 3) (u + ubar - d - dbar)` (`f2LO_charge_sub_f2LO_charge_comap_swap`) whose
`dx / x` integral is the Gottfried sum.

The ratio `F₂^p / F₂^n` at large `x` is not fixed by isospin. It is fixed by the limits of the
density ratios: if every `q_f + qbar_f` is asymptotically `ρ_f` times a common reference function,
the ratio tends to `Σ e_f² ρ_f / Σ e_{τ f}² ρ_f` (`tendsto_f2LO_div_f2LO_comap_swap`). For the light
flavours with `d/u → r` and `s/u → t` that is `(4 + r + t) / (1 + 4 r + t)`
(`tendsto_f2LO_charge_div_f2LO_charge_comap_swap`), and the familiar value `4` as `x → 1` is the
conditional statement that the down and strange densities are negligible against the up density
there (`tendsto_f2LO_charge_div_f2LO_charge_comap_swap_nhdsLT_one`). Whether they are is an open
experimental question, which is why the hypothesis is stated rather than assumed.

## Main results

* `f2LO_comap`: `F₂` of a density with relabelled flavours is `F₂` with the inverse relabelling
  of the charges.
* `f2LO_sub_f2LO_comap_swap`: the proton-neutron difference `x (e_u² - e_d²) (q_u - q_d)`.
* `f2LO_charge_sub_f2LO_charge_comap_swap`: the light-flavour difference `(x / 3) (q_u - q_d)`.
* `tendsto_f2LO_div_f2LO_comap_swap`: the limit of `F₂^p / F₂^n` in terms of the limits of the
  density ratios.
* `tendsto_f2LO_charge_div_f2LO_charge_comap_swap_nhdsLT_one`: `F₂^p / F₂^n → 4` as `x → 1⁻`
  when the down and strange densities are negligible against the up density.

## References

* K. Gottfried, *Sum rule for high-energy electron-proton scattering*,
  Phys. Rev. Lett. **18** (1967) 1174.
* R. Devenish and A. Cooper-Sarkar, *Deep Inelastic Scattering*, Oxford University Press (2004),
  ch. 5.
* F. Halzen and A. D. Martin, *Quarks and Leptons*, Wiley (1984), ch. 9.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Inclusive

open Filter Topology
open Particles.Parton.PDF (Pdf comap comap_apply)
open Particles.Meson (LightFlavor)

/-!
## Relabelling flavours, and the proton-neutron difference
-/

section General

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- **Relabelling the flavours of a density is relabelling the charges the other way.** For a
bijection `σ` of flavour types, the leading-order `F₂` of the density `q ∘ σ` with charges `e` is
the `F₂` of `q` with charges `e ∘ σ⁻¹`. -/
theorem f2LO_comap (σ : κ ≃ ι) (e : κ → ℝ) (q : Pdf ι) (x Q2 : ℝ) :
    f2LO e (comap σ q) x Q2 = f2LO (e ∘ σ.symm) q x Q2 := by
  simp only [f2LO, comap_apply, Function.comp_apply]
  rw [← σ.sum_comp fun i => e (σ.symm i) ^ 2 * q i x Q2]
  simp

variable [DecidableEq ι]

/-- **The proton-neutron difference of `F₂`.** Under the isospin involution `τ = swap u d` every
flavour other than `u` and `d` drops out of `F₂^p - F₂^n`, which is
`x (e_u² - e_d²) (q_u - q_d)`. -/
theorem f2LO_sub_f2LO_comap_swap (e : ι → ℝ) (q : Pdf ι) (u d : ι) (x Q2 : ℝ) :
    f2LO e q x Q2 - f2LO e (comap (Equiv.swap u d) q) x Q2
      = x * (e u ^ 2 - e d ^ 2) * (q u x Q2 - q d x Q2) := by
  rw [f2LO_comap, Equiv.symm_swap]
  simp only [f2LO, Function.comp_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rcases eq_or_ne u d with rfl | hud
  · simp
  rw [Fintype.sum_eq_add u d hud fun i hi => by
    rw [Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, sub_self]]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- **The limiting ratio of the proton and neutron `F₂`.** If every density `q i` is
asymptotically `ρ i` times a common reference function `w` along a filter `l`, then
`F₂^p / F₂^n` tends to `Σ e_i² ρ_i / Σ e_{τ i}² ρ_i`, where `τ = swap u d` is the isospin
involution, provided the limiting denominator does not vanish. -/
theorem tendsto_f2LO_div_f2LO_comap_swap {e : ι → ℝ} {q : Pdf ι} {u d : ι} {Q2 : ℝ}
    {l : Filter ℝ} {w : ℝ → ℝ} {ρ : ι → ℝ} (hx : ∀ᶠ x in l, x ≠ 0) (hw : ∀ᶠ x in l, w x ≠ 0)
    (hq : ∀ i, Tendsto (fun x => q i x Q2 / w x) l (𝓝 (ρ i)))
    (hρ : ∑ i, e (Equiv.swap u d i) ^ 2 * ρ i ≠ 0) :
    Tendsto (fun x => f2LO e q x Q2 / f2LO e (comap (Equiv.swap u d) q) x Q2) l
      (𝓝 ((∑ i, e i ^ 2 * ρ i) / ∑ i, e (Equiv.swap u d i) ^ 2 * ρ i)) := by
  have hlim (c : ι → ℝ) :
      Tendsto (fun x => ∑ i, c i * (q i x Q2 / w x)) l (𝓝 (∑ i, c i * ρ i)) :=
    tendsto_finsetSum _ fun i _ => (hq i).const_mul (c i)
  refine ((hlim _).div (hlim _) hρ).congr' ?_
  filter_upwards [hx, hw] with x hx hw
  rw [Pi.div_apply]
  have h (c : ι → ℝ) :
      x * ∑ i, c i * q i x Q2 = x * w x * ∑ i, c i * (q i x Q2 / w x) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [f2LO_comap, Equiv.symm_swap]
  simp only [f2LO, Function.comp_apply]
  rw [h, h, mul_div_mul_left _ _ (mul_ne_zero hx hw)]

end General

/-!
## The light flavours
-/

section LightFlavor

open EpsilonEridani.Particles.Meson.LightFlavor

/-- **The light-flavour proton-neutron difference of `F₂`.** With the light-quark charges,
`F₂^p - F₂^n = (x / 3) (q_u - q_d)`: for `q_f` the quark plus antiquark density this is
`(x / 3) (u + ubar - d - dbar)`, the integrand of the Gottfried sum after division by `x`. -/
theorem f2LO_charge_sub_f2LO_charge_comap_swap (q : Pdf LightFlavor) (x Q2 : ℝ) :
    f2LO charge q x Q2 - f2LO charge (comap (Equiv.swap u d) q) x Q2
      = x / 3 * (q u x Q2 - q d x Q2) := by
  rw [f2LO_sub_f2LO_comap_swap, charge_u, charge_d]
  ring

/-- **The light-flavour ratio `F₂^p / F₂^n` in terms of `d / u` and `s / u`.** If, along a filter
avoiding `x = 0`, the down and strange densities are asymptotically `r` and `t` times the up
density, then `F₂^p / F₂^n → (4 + r + t) / (1 + 4 r + t)`. -/
theorem tendsto_f2LO_charge_div_f2LO_charge_comap_swap {q : Pdf LightFlavor} {Q2 : ℝ}
    {l : Filter ℝ} {r t : ℝ} (hx : ∀ᶠ x in l, x ≠ 0) (hu : ∀ᶠ x in l, q u x Q2 ≠ 0)
    (hd : Tendsto (fun x => q d x Q2 / q u x Q2) l (𝓝 r))
    (hs : Tendsto (fun x => q s x Q2 / q u x Q2) l (𝓝 t)) (hrt : 1 + 4 * r + t ≠ 0) :
    Tendsto (fun x => f2LO charge q x Q2 / f2LO charge (comap (Equiv.swap u d) q) x Q2) l
      (𝓝 ((4 + r + t) / (1 + 4 * r + t))) := by
  have hu' : Tendsto (fun x => q u x Q2 / q u x Q2) l (𝓝 1) :=
    tendsto_const_nhds.congr' <| hu.mono fun x hx => (div_self hx).symm
  let ρ : LightFlavor → ℝ := fun | .u => 1 | .d => r | .s => t
  have hq : ∀ i, Tendsto (fun x => q i x Q2 / q u x Q2) l (𝓝 (ρ i)) := by
    rintro (_ | _ | _)
    exacts [hu', hd, hs]
  have hρ : ∑ i, charge (Equiv.swap u d i) ^ 2 * ρ i ≠ 0 := by
    simp only [LightFlavor.sum_univ, Equiv.swap_apply_left, Equiv.swap_apply_right, ρ]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    norm_num
    intro h
    apply hrt
    linarith
  convert tendsto_f2LO_div_f2LO_comap_swap hx hu hq hρ using 2
  simp only [LightFlavor.sum_univ, Equiv.swap_apply_left, Equiv.swap_apply_right, ρ]
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  norm_num
  field_simp

/-- **`F₂^p / F₂^n → 4` as `x → 1`, conditionally.** If, as `x → 1` from below, the up density is
eventually non-zero and the down and strange densities are negligible against it, the
proton-neutron ratio of `F₂` tends to `e_u² / e_d² = 4`. -/
theorem tendsto_f2LO_charge_div_f2LO_charge_comap_swap_nhdsLT_one {q : Pdf LightFlavor}
    {Q2 : ℝ} (hu : ∀ᶠ x in 𝓝[<] 1, q u x Q2 ≠ 0)
    (hd : Tendsto (fun x => q d x Q2 / q u x Q2) (𝓝[<] 1) (𝓝 0))
    (hs : Tendsto (fun x => q s x Q2 / q u x Q2) (𝓝[<] 1) (𝓝 0)) :
    Tendsto (fun x => f2LO charge q x Q2 / f2LO charge (comap (Equiv.swap u d) q) x Q2)
      (𝓝[<] 1) (𝓝 4) := by
  have hx : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds one_ne_zero)
  simpa using tendsto_f2LO_charge_div_f2LO_charge_comap_swap hx hu hd hs (by norm_num)

end LightFlavor

end Inclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
