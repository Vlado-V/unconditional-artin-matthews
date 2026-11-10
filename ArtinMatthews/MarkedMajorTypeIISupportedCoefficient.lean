module

public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedMajorTypeIICoefficients
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! The actual scalar alpha coefficient, zero off its original interval.
The norm exponent is independent of the number of prime bands and marks. -/
namespace ArtinMatthews
open Filter Finset
noncomputable section

 def markedMajorRestrictedCoefficient (W modulation : ℝ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if n ∈ S then markedMajorCenteredCoefficient W modulation n else 0

 theorem markedMajorRestrictedCoefficient_nonzero (W modulation : ℝ) (S : Finset ℕ) (n : ℕ) :
    markedMajorRestrictedCoefficient W modulation S n ≠ 0 ↔
      n ∈ S ∧ markedMajorCenteredCoefficient W modulation n ≠ 0 := by
  classical
  simp only [markedMajorRestrictedCoefficient,ite_ne_right_iff]

 theorem markedMajorRestrictedCoefficient_eq_zero (W modulation : ℝ) (S : Finset ℕ) (n : ℕ)
    (hn : n ∉ S) : markedMajorRestrictedCoefficient W modulation S n = 0 := by
  simp only [markedMajorRestrictedCoefficient,ite_eq_right hn]

 theorem markedMajorTypeII_supported_alpha (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ) (modulation : ℝ),
      (∀ n ∈ S, Real.exp (δ*L) ≤ (n:ℝ)) →
      (∀ n, ‖markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation S n‖ ≤ L^2) ∧
      (∀ n, markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation S n ≠ 0 →
        ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) := by
  filter_upwards [markedMajorTypeII_alpha_bound δ hδ,markedMajorTypeII_alpha_rough δ hδ] with L hb hr
  intro S modulation hS
  constructor
  · intro n
    by_cases hn : n ∈ S
    · simpa only [markedMajorRestrictedCoefficient,ite_eq_left hn] using hb n modulation (hS n hn)
    · simp only [markedMajorRestrictedCoefficient,ite_eq_right hn,norm_zero]
      exact sq_nonneg L
  · intro n hn
    obtain ⟨hnS,hnα⟩ := (markedMajorRestrictedCoefficient_nonzero _ _ _ _).mp hn
    exact hr n modulation (hS n hnS) hnα

 theorem markedMajorTypeII_interval_alpha (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (M N : ℕ) (modulation : ℝ), Real.exp (δ*L) ≤ (M:ℝ) →
      (∀ n, ‖markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation (Icc M N) n‖ ≤ L^2) ∧
      (∀ n, markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation (Icc M N) n ≠ 0 →
        ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) := by
  filter_upwards [markedMajorTypeII_supported_alpha δ hδ] with L hL
  intro M N modulation hM
  exact hL (Icc M N) modulation (fun n hn => hM.trans (by exact_mod_cast (mem_Icc.mp hn).1))

 theorem markedMajorTypeII_supported_alpha_band_rough {I : Type*} [Fintype I]
    (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ) (modulation : ℝ),
      (∀ n ∈ S, Real.exp (δ*L) ≤ (n:ℝ)) →
      ∀ n, markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation S n ≠ 0 →
        ∀ i p,p ∈ markedLogPowerBand (e i) (Real.exp L) → ¬p∣n := by
  filter_upwards [markedMajorTypeII_supported_alpha δ hδ,
    markedMajorTypeII_bands_below_rough e hinj he] with L hα hband
  intro S modulation hS n hn i p hp
  exact (hα S modulation hS).2 n hn p (hband i p hp)

 theorem markedMajorTypeII_interval_alpha_log (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (M N : ℕ) (modulation : ℝ), x^δ ≤ (M:ℝ) →
      (∀ n, ‖markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ)))
        modulation (Icc M N) n‖ ≤ (Real.log x)^2) ∧
      (∀ n, markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ)))
        modulation (Icc M N) n ≠ 0 →
        ∀ p ∈ Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,¬p∣n) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (markedMajorTypeII_interval_alpha δ hδ),
    eventually_gt_atTop (0:ℝ)] with x hx hxpos
  have heq : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos hxpos,mul_comm]
  simpa only [heq] using hx

 theorem markedMajorTypeII_supported_alpha_band_rough_log {I : Type*} [Fintype I]
    (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset ℕ) (modulation : ℝ),
      (∀ n ∈ S, x^δ ≤ (n:ℝ)) →
      ∀ n, markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation S n ≠ 0 →
        ∀ i p,p ∈ markedLogPowerBand (e i) x → ¬p∣n := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (markedMajorTypeII_supported_alpha_band_rough e hinj he δ hδ),
    eventually_gt_atTop (0:ℝ)] with x hx hxpos
  have heq : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos hxpos,mul_comm]
  simpa only [heq,Real.exp_log hxpos] using hx

end
end ArtinMatthews
