module

public import ArtinMatthews.SpectralGamma0FourierEnergy
public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative
public import ArtinMatthews.SpectralCuspWeightedLocalIntegrability
public import ArtinMatthews.SpectralGamma0FourierWeakDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of a smooth local Fourier representative with the
actual completed vertical-energy derivative, using compact weak tests. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology MatrixGroups

namespace ArtinMatthews

theorem spectral_integrable_local_test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set ℝ} {f : ℝ → E} (hf : LocallyIntegrableOn f S volume)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ S) :
    Integrable (fun x => ρ x • f x) volume := by
  have hfi : Integrable ((tsupport ρ).indicator f) volume :=
    (integrable_indicator_iff (isClosed_tsupport ρ).measurableSet).mpr
      (hf.integrableOn_compact_subset hρs hρc)
  have h := hfi.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hρ hρc
  apply h.congr
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport ρ
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, smul_zero, image_eq_zero_of_notMem_tsupport hx, zero_smul]

theorem spectral_local_classical_weak_derivative (Y : ℝ) (C D : ℝ → ℂ)
    (hC : ContinuousOn C (Ioi Y)) (hD : ContinuousOn D (Ioi Y))
    (hCD : ∀ y, Y < y → HasDerivAt C (D y) y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ y, deriv ρ y • C y) = -(∫ y, ρ y • D y) := by
  have hCl : LocallyIntegrableOn C (Ioi Y) volume := hC.locallyIntegrableOn measurableSet_Ioi
  have hDl : LocallyIntegrableOn D (Ioi Y) volume := hD.locallyIntegrableOn measurableSet_Ioi
  have hi := spectral_integrable_local_test hDl hρ.continuous hρc hρs
  have hi' := spectral_integrable_local_test hCl (hρ.continuous_deriv (by simp)) hρc.deriv
    (tsupport_deriv_subset.trans hρs)
  have hi0 := spectral_integrable_local_test hCl hρ.continuous hρc hρs
  have H := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (fun y _ => (hρ.differentiable (by simp) y).hasDerivAt)
    (fun y hy => hCD y (hρs hy)) hi hi' hi0
  change (∫ y, ρ y • D y) = -(∫ y, deriv ρ y • C y) at H
  rw [H, neg_neg]

theorem spectral_local_weak_derivative_identification (Y : ℝ) (f g C D : ℝ → ℂ)
    (hg : LocallyIntegrableOn g (Ioi Y) volume)
    (hC : ContinuousOn C (Ioi Y)) (hD : ContinuousOn D (Ioi Y))
    (hCD : ∀ y, Y < y → HasDerivAt C (D y) y)
    (hfC : f =ᵐ[volume.restrict (Ioi Y)] C)
    (hweak : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi Y → (∫ y in Ioi Y, deriv ρ y • f y) = -(∫ y in Ioi Y, ρ y • g y)) :
    g =ᵐ[volume.restrict (Ioi Y)] D := by
  have hDl : LocallyIntegrableOn D (Ioi Y) volume := hD.locallyIntegrableOn measurableSet_Ioi
  have htest (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
      (hρs : tsupport ρ ⊆ Ioi Y) : (∫ y, ρ y • (g y - D y)) = 0 := by
    have hgint := spectral_integrable_local_test hg hρ.continuous hρc hρs
    have hDint := spectral_integrable_local_test hDl hρ.continuous hρc hρs
    have hc := spectral_local_classical_weak_derivative Y C D hC hD hCD ρ hρ hρc hρs
    have hw := hweak ρ hρ hρc hρs
    have hleft : (∫ y in Ioi Y, deriv ρ y • f y) = ∫ y in Ioi Y, deriv ρ y • C y := by
      apply integral_congr_ae
      exact hfC.mono fun y hy => by dsimp only; rw [hy]
    rw [hleft, spectralTest_setIntegral_eq_integral (deriv ρ) (Ioi Y)
      (tsupport_deriv_subset.trans hρs), spectralTest_setIntegral_eq_integral ρ (Ioi Y) hρs] at hw
    have he : (∫ y, ρ y • g y) = ∫ y, ρ y • D y := neg_injective (hw.symm.trans hc)
    simp_rw [smul_sub]
    rw [integral_sub hgint hDint, he, sub_self]
  have hz := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg.sub hDl) htest
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioi] with y hy hyS
  exact sub_eq_zero.mp (hy hyS)

theorem gamma0CuspFourierDerivative_locallyIntegrable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (u : gamma0EnergySpace N) :
    LocallyIntegrableOn (gamma0CuspFourierDerivative N r Y hY n u) (Ioi Y) volume := by
  have h := cuspVerticalL2_locallyIntegrableOn (N : ℝ) Y
    (Nat.cast_pos.mpr (NeZero.pos N)) hY (gamma0CuspFourierScaledDerivative N r Y hY n u)
  exact h.continuousOn_smul isOpen_Ioi.isLocallyClosed
    (continuousOn_id.inv₀ fun y hy => (hY.trans hy).ne')

theorem gamma0CuspFourierDerivative_ae_classical (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (u : gamma0EnergySpace N)
    (C D : ℝ → ℂ) (hC : ContinuousOn C (Ioi Y)) (hD : ContinuousOn D (Ioi Y))
    (hCD : ∀ y, Y < y → HasDerivAt C (D y) y)
    (hfC : gamma0CuspFourierCoefficient N r Y hY n (gamma0EnergyInclusion N u)
      =ᵐ[volume.restrict (Ioi Y)] C) :
    gamma0CuspFourierDerivative N r Y hY n u =ᵐ[volume.restrict (Ioi Y)] D :=
  spectral_local_weak_derivative_identification Y _ _ C D
    (gamma0CuspFourierDerivative_locallyIntegrable N r Y hY n u) hC hD hCD hfC
    (fun ρ hρ hρc hρs => gamma0CuspFourier_weak_derivative N r Y hY n ρ hρ hρc hρs u)

theorem gamma0CuspFourier_classical_integrable_energy (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (u : gamma0EnergySpace N)
    (C D : ℝ → ℂ) (hC : ContinuousOn C (Ioi Y)) (hD : ContinuousOn D (Ioi Y))
    (hCD : ∀ y, Y < y → HasDerivAt C (D y) y)
    (hfC : gamma0CuspFourierCoefficient N r Y hY n (gamma0EnergyInclusion N u)
      =ᵐ[volume.restrict (Ioi Y)] C) :
    IntegrableOn (fun y => ‖C y‖ ^ 2 / y ^ 2) (Ioi Y) volume ∧
      IntegrableOn (fun y => ‖D y‖ ^ 2) (Ioi Y) volume := by
  constructor
  · apply (gamma0CuspFourierCoefficient_integrable_mass N r Y hY n (gamma0EnergyInclusion N u)).congr
    exact hfC.mono fun y hy => by dsimp only; rw [hy]
  · apply (gamma0CuspFourierDerivative_integrable_energy N r Y hY n u).congr
    exact (gamma0CuspFourierDerivative_ae_classical N r Y hY n u C D hC hD hCD hfC).mono
      fun y hy => by dsimp only; rw [hy]

end ArtinMatthews
