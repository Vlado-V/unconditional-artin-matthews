module

public import ArtinMatthews.MarkedMajorMellinConstructed
public import ArtinMatthews.MarkedMajorMellinLabelEnergyData
public import ArtinMatthews.MarkedMajorMellinLabelEnergy
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal unit logarithmic phase from normalized endpoint separation
preserves every saving, without differentiating that phase. -/
namespace ArtinMatthews
open Filter MeasureTheory Set
open scoped ContDiff

theorem markedMajorMellinLabelEnergy_phase_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsupp : Function.support cutoff ⊆ Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ (X : ℝ), 1 ≤ X → ∀ hX : 0 < X,
      X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      ∀ {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
      (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X)
      (θ : ℝ), |θ| ≤ cfg.Kθ*L^cfg.A₀ → ∀ logScale : ℝ,
      ‖∫ p : ℝ × ℝ, Complex.exp (-Complex.I*(p.2:ℂ)*(logScale:ℂ))*
        (markedMajorConstructedCoefficient ψ ha hab hψ hX θ (p.1/X,p.2)*
        (z.endpoint cutoff p.1*z'.conjugateEndpoint cutoff (p.2-p.1)))‖ ≤ L^(-P) := by
  filter_upwards [markedMajorMellinLabelEnergy_all_log cfg σ Kx hσ cutoff hcutoff hnorm
    hlo hhi hsupp ψ ha hab hψ P hP] with L henergy
  intro X hX1 hX hupper hcomp J J' _ _ _ _ z z' θ hθ logScale
  have hphase (p : ℝ × ℝ) : ‖Complex.exp (-Complex.I*(p.2:ℂ)*(logScale:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖Complex.exp (-Complex.I*(p.2:ℂ)*(logScale:ℂ))*
        (markedMajorConstructedCoefficient ψ ha hab hψ hX θ (p.1/X,p.2)*
          (z.endpoint cutoff p.1*z'.conjugateEndpoint cutoff (p.2-p.1)))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ p : ℝ × ℝ, ‖markedMajorConstructedCoefficient ψ ha hab hψ hX θ (p.1/X,p.2)*
          (z.endpoint cutoff p.1*z'.conjugateEndpoint cutoff (p.2-p.1))‖ := by
      simp only [norm_mul,hphase,one_mul]
    _ ≤ _ := henergy X hX1 hX hupper hcomp z z' θ hθ

end ArtinMatthews
