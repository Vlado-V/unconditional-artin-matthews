module

public import ArtinMatthews.MarkedMajorMellinConstructed
public import ArtinMatthews.MarkedMajorMellinLabelEnergyData
public import ArtinMatthews.MarkedMajorComparableMean
public import ArtinMatthews.MarkedMajorMellinEnergyAssembly
public import ArtinMatthews.MarkedMajorMellinLabelEnergyCentral
public import ArtinMatthews.MarkedMajorMellinLabelEnergyLog
public import ArtinMatthews.MarkedMajorMellinLabelEnergyMean
public import ArtinMatthews.MarkedMajorMellinLabelEnergyParameters
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Arbitrary logarithmic saving for the full actual two-endpoint major
Mellin integral. The endpoint records carry only literal arithmetic data;
all central cancellation and weighted means are proved inputs. -/
namespace ArtinMatthews
open Filter MeasureTheory Set
open scoped ContDiff

theorem markedMajorMellinLabelEnergy_comparable_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsupp : Function.support cutoff ⊆ Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ (X X' : ℝ), 1 ≤ X → 1 ≤ X' → ∀ hX : 0 < X,
      X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      X' ≤ Real.exp (σ*L) → X' ≤ Kx*Real.exp L → X ≤ 2*X' →
      ∀ {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
      (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X')
      (θ : ℝ), |θ| ≤ cfg.Kθ*L^cfg.A₀ →
      (∫ p : ℝ × ℝ, ‖markedMajorConstructedCoefficient ψ ha hab hψ hX θ (p.1/X,p.2)*
        (z.endpoint cutoff p.1*z'.conjugateEndpoint cutoff (p.2-p.1))‖) ≤ L^(-P) := by
  obtain ⟨n,hn⟩ := exists_nat_ge (P+2*cfg.A₀+2*cfg.D+9)
  obtain ⟨CF,hCF,hkernel⟩ := markedMajor_constructed_endpoint_L1_energy ψ ha hab hψ n
  obtain ⟨CM,hCM,hmean⟩ := markedMajorLabelEnergy_weighted cfg σ hi hσ hhi cutoff hnorm
    (fun y hy => (hsupp hy).2)
  have hcentral := markedMajorLabelEnergy_central cfg cutoff hcutoff hlo hhi hsupp
    σ Kx (cfg.A₀+3) (cfg.A₀+2+P+2) hσ (by linarith [cfg.hA₀]) (by linarith [cfg.hA₀])
  filter_upwards [hcentral,hmean,
    markedMajorLabelEnergy_log_budget cfg.A₀ cfg.D P cfg.Kθ CF (2*CM) markedMajorFourierWeightMass
      hCF.le (by positivity) markedMajorFourierWeightMass_nonneg n hn,
    eventually_ge_atTop (2:ℝ)] with L hc hm hbudget hL
  intro X X' hX1 hX'1 hX hupper hcomp hupper' hcomp' hXX' J J' _ _ _ _ z z' θ hθ
  have hXp' : 0 < X' := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hcent := hc X hX1 hupper hcomp z
  have hcent' := hc X' hX'1 hupper' hcomp' z'
  have hr : 2*X*L^(cfg.A₀+2) ≤ 2*X*L^(cfg.A₀+3) := by
    convert markedMajorComparable_central_radius hL hX.le (by linarith : X ≤ 2*X) (B := cfg.A₀+2) using 1
    congr 2
    ring
  have hr' : 2*X*L^(cfg.A₀+2) ≤ 2*X'*L^(cfg.A₀+3) := by
    convert markedMajorComparable_central_radius hL hXp'.le hXX' (B := cfg.A₀+2) using 1
    congr 2
    ring
  have he := (markedMajorLocalMean_mono_radius _ (z.endpoint_continuous cutoff) hr).trans hcent.1
  have he' := (markedMajorLocalMean_mono_radius _ (z'.conjugateEndpoint_continuous cutoff) hr').trans hcent'.2
  have hW : 1 ≤ 1+|θ| := le_add_of_nonneg_right (abs_nonneg θ)
  have hWp : 0 < 1+|θ| := by positivity
  have hscaled (c : ℝ) :
      (∫ t, markedMajorFourierWeight ((1+|θ|)*X) 2 (t-c)*‖z.endpoint cutoff t‖^2) ≤
        (2*CM)*(1+|θ|)*L^(2*cfg.D+5) := by
    have H := (hm X hX1 hupper z (1+|θ|) c hW).1
    exact H.trans (by nlinarith [(mul_nonneg (mul_nonneg hCM.le hWp.le)
      (Real.rpow_nonneg (by linarith : 0 ≤ L) (2*cfg.D+5)))])
  have hscaled' (c : ℝ) :
      (∫ t, markedMajorFourierWeight ((1+|θ|)*X) 2 (t-c)*‖z'.conjugateEndpoint cutoff t‖^2) ≤
        (2*CM)*(1+|θ|)*L^(2*cfg.D+5) := by
    have hs : (1+|θ|)*X ≤ (2*(1+|θ|))*X' := by nlinarith
    have H := (markedMajorLocalMean_mono_scale _ (z'.conjugateEndpoint_continuous cutoff)
      (z'.conjugateEndpoint_bounded cutoff) (mul_pos hWp hX) hs c).trans
        (hm X' hX'1 hupper' z' (2*(1+|θ|)) c (by linarith)).2
    convert H using 1
    ring
  have henergy := hkernel X hX1 hX θ (L^(cfg.A₀+2)) (L^(-(cfg.A₀+2+P+2)))
    ((2*CM)*(1+|θ|)*L^(2*cfg.D+5)) (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
    (z.endpoint cutoff) (z'.conjugateEndpoint cutoff)
    (z.endpoint_continuous cutoff) (z'.conjugateEndpoint_continuous cutoff)
    (z.endpoint_bounded cutoff) (z'.conjugateEndpoint_bounded cutoff)
    he he' hscaled hscaled'
  exact henergy.trans (hbudget (1+|θ|) hW (markedMajorLabelEnergy_theta_scale hL1 cfg.hA₀ hθ))

end ArtinMatthews
