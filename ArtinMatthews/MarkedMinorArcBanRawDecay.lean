module

public import ArtinMatthews.MarkedMinorArcBanRawSchur
public import ArtinMatthews.MarkedMinorArcBanDecay
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
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

/-! Uniform every-logarithm ban saving for the actual source slot count. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

def markedRawBanErrorRate (K : ℕ) (H A W A₀ x : ℝ) : ℝ :=
  markedRawBanErrorBound K ⌊(Real.log x)^(1/100:ℝ)⌋₊ H A W ((Real.log x)^A₀) x

theorem markedRawBanErrorRate_eq_envelope (K : ℕ) (H A W A₀ x : ℝ) :
    markedRawBanErrorRate K H A W A₀ x =
      markedBanEnvelope (H^2*markedBanErrorConstant K A W) A₀ x := by
  unfold markedRawBanErrorRate markedRawBanErrorBound markedBanEnvelope markedPadSlots
  push_cast
  ring

theorem markedRawBanErrorRate_log_saving (K : ℕ) (H A W A₀ B : ℝ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) :
    Tendsto (fun x : ℝ => (Real.log x)^B*markedRawBanErrorRate K H A W A₀ x) atTop (nhds 0) := by
  simp_rw [markedRawBanErrorRate_eq_envelope]
  apply markedBanEnvelope_log_saving
  unfold markedBanErrorConstant
  positivity

/-- The actual raw clean ban error has every logarithmic operator saving,
uniformly in the background, memory cutoff, positions and endpoint tests.
The geometric premises are the literal source-box tau conditions. -/
theorem markedRawBanErrorKernel_uniform_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H A W A₀ Bsave : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hW : 0 ≤ W) (hA₀ : 0 ≤ A₀)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (hsupp : ∀ t, ψ t ≠ 0 → |t| ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ (B : ℕ) (Z : Finset (ℤ × ℤ)) (q r : ℝ)
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (d₀ Y ρ : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z → ℂ),
      0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 → (∀ s, ‖χ s‖ ≤ 1) →
      (∀ z : Z, markedMinorIntegerTau r z.1 ≠ 0) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      1 ≤ Y → ∀ bg : MarkedRawBackground (markedRawActualPrimeBand e x)
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ B,
      ‖markedWeightedCountingMatrix
        (fun u : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z =>
          markedRawLastMass (markedRawActualPrimeAtom e q x) u.2)
        (markedRawBanErrorKernel hZ ψ η d₀ Y ((Real.log x)^A₀) ρ χ bg)‖ ≤
          (Real.log x)^(-Bsave) := by
  classical
  have hn := (markedRawBanErrorRate_log_saving (Fintype.card J) H A W A₀ Bsave hA hW).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [markedRawBanErrorKernel_actual_schur_eventually e he hinj,hn,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hs hn hlog
  intro B Z q r hZ d₀ Y ρ χ hq0 hq1 hρ0 hρ1 hχ hz hgeo hY bg
  let complement : Z → ℤ × ℤ := fun z => Classical.choose (markedPrimitivePosition_completion z.1 (hZ _ z.2))
  have hd : ∀ z : Z, markedMinorIntegerDet z.1 (complement z)=1 :=
    fun z => Classical.choose_spec (markedPrimitivePosition_completion z.1 (hZ _ z.2))
  have hh := hs ⌊(Real.log x)^(1/100:ℝ)⌋₊ B Z q r hZ complement ψ η d₀ Y ((Real.log x)^A₀) ρ H A W χ
    hq0 hq1 hρ0 hρ1 hH hη hχ hd hz hgeo (Real.one_le_rpow hlog hA₀) hY hA hW hψ hsupp bg
  apply hh.trans
  have hL : 0 < Real.log x := by linarith
  have hp : 0 < (Real.log x)^Bsave := Real.rpow_pos_of_pos hL _
  rw [Real.rpow_neg hL.le,← one_div]
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm,markedRawBanErrorRate] using hn.le)

end ArtinMatthews
