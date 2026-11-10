module

public import ArtinMatthews.SourceLocalAnnularMellin
public import ArtinMatthews.SourceLocalBallMellin
public import ArtinMatthews.StandardLocalHaarScaling
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The actual finite Fourier Mellin factor is holomorphic on the right
half-plane. Its absolute integrals are uniformly bounded on positive
vertical bands, including the precise weighted norm used on a sheet. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set
open scoped NumberField
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "k" => P.adicCompletion K
local notation "q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "μ" => sourceLocalMulMeasure K P
local notation "c" => Measure.real (sourceLocalSelfDual K P) (sourceLocalBall K P 0)
local notation "d" => sourceDifferentExponent K P

theorem sourceLocalAnnularMellinIntegrand_norm (z : ℂ) (u : kˣ) :
    ‖sourceLocalAnnularMellinIntegrand K P z u‖ =
      ‖sourceLocalFourier K P (sourceLocalUnitTest K P) (u : k)‖ * ‖(u : k)‖ ^ z.re := by
  rw [sourceLocalAnnularMellinIntegrand, norm_mul, sourceLocalMellinWeight,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr u.ne_zero)]

theorem sourceLocalAnnularWeightedNorm_integrable (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun u : kˣ => ‖sourceLocalFourier K P (sourceLocalUnitTest K P) (u : k)‖ *
      ‖(u : k)‖ ^ σ) μ := by
  have h := (sourceLocalAnnularMellin_integrable K P (σ : ℂ) (by simpa using hσ)).norm
  simpa only [sourceLocalAnnularMellinIntegrand_norm, Complex.ofReal_re] using h

def sourceLocalAnnularMellinBandBound (a b : ℝ) : ℝ :=
  c * (sourceLocalMellinShellMass K P * q ^ ((d : ℝ) * b) / (1 - q ^ (-a))) +
    (c / q) * (sourceLocalMellinShellMass K P * q ^ (((d : ℝ) + 1) * b) / (1 - q ^ (-a)))

theorem sourceLocalAnnularMellin_norm_integral_le_band (a b : ℝ) (ha : 0 < a)
    (z : ℂ) (hl : a ≤ z.re) (hh : z.re ≤ b) :
    (∫ u, ‖sourceLocalAnnularMellinIntegrand K P z u‖ ∂μ) ≤
      sourceLocalAnnularMellinBandBound K P a b := by
  let g (n : ℤ) (u : kˣ) := ‖(sourceLocalMulBall K P n).indicator (sourceLocalMellinWeight K P z) u‖
  have hi (n : ℤ) : Integrable (g n) μ :=
    (sourceLocalMellinWeight_integrable_indicator K P n z (ha.trans_le hl)).norm
  have hc := (sourceLocalBall_volume_pos K P 0).le
  have hcq := div_nonneg hc (sourceLocalNorm_pos K P).le
  have hB (n : ℤ) (hn : 0 ≤ n) :
      (∫ u, g n u ∂μ) ≤ sourceLocalMellinShellMass K P * q ^ ((n : ℝ) * b) / (1 - q ^ (-a)) := by
    unfold g
    simp_rw [norm_indicator_eq_indicator_norm]
    rw [integral_indicator (sourceLocalMulBall_measurable K P n)]
    exact sourceLocalMellinWeight_norm_integral_ball_le K P n hn a b ha z hl hh
  calc
    _ ≤ ∫ u, c * g (d : ℤ) u + (c / q) * g ((d : ℤ) + 1) u ∂μ := by
      apply integral_mono (sourceLocalAnnularMellin_integrable K P z (ha.trans_le hl)).norm
        (((hi (d : ℤ)).const_mul c).add ((hi ((d : ℤ) + 1)).const_mul (c / q)))
      intro u
      change ‖sourceLocalAnnularMellinIntegrand K P z u‖ ≤ c * g (d : ℤ) u + (c / q) * g ((d : ℤ) + 1) u
      rw [sourceLocalAnnularMellinIntegrand_eq]
      apply (norm_sub_le _ _).trans_eq
      simp only [g, norm_mul, Complex.norm_of_nonneg hc, Complex.norm_of_nonneg hcq]
    _ = c * (∫ u, g (d : ℤ) u ∂μ) + (c / q) * (∫ u, g ((d : ℤ) + 1) u ∂μ) := by
      rw [integral_add ((hi (d : ℤ)).const_mul c) ((hi ((d : ℤ) + 1)).const_mul (c / q)),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      unfold sourceLocalAnnularMellinBandBound
      have h0 := hB (d : ℤ) (Int.natCast_nonneg _)
      have h1 := hB ((d : ℤ) + 1) (add_nonneg (Int.natCast_nonneg _) zero_le_one)
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] at h0 h1
      exact add_le_add (mul_le_mul_of_nonneg_left h0 hc) (mul_le_mul_of_nonneg_left h1 hcq)

theorem sourceLocalAnnularMellin_norm_le_band (a b : ℝ) (ha : 0 < a)
    (z : ℂ) (hl : a ≤ z.re) (hh : z.re ≤ b) :
    ‖sourceLocalAnnularMellin K P z‖ ≤ sourceLocalAnnularMellinBandBound K P a b :=
  (norm_integral_le_integral_norm _).trans
    (sourceLocalAnnularMellin_norm_integral_le_band K P a b ha z hl hh)

theorem sourceLocalAnnularMellin_differentiableOn :
    DifferentiableOn ℂ (sourceLocalAnnularMellin K P) {z : ℂ | 0 < z.re} := by
  let : NeZero (q : ℂ) := ⟨Complex.ofReal_ne_zero.mpr (sourceLocalNorm_pos K P).ne'⟩
  let f (z : ℂ) := (c : ℂ) * (sourceLocalMellinShellMass K P : ℂ) *
    (q : ℂ) ^ ((d : ℂ) * z) * (1 - (q : ℂ) ^ (z - 1)) / (1 - (q : ℂ) ^ (-z))
  have hp := differentiable_const_cpow_of_neZero (q : ℂ)
  have h1 : Differentiable ℂ (fun z : ℂ => (q : ℂ) ^ ((d : ℂ) * z)) :=
    hp.comp ((differentiable_const (d : ℂ)).mul differentiable_id)
  have h2 : Differentiable ℂ (fun z : ℂ => 1 - (q : ℂ) ^ (z - 1)) :=
    (differentiable_const (1 : ℂ)).sub (hp.comp (differentiable_id.sub (differentiable_const (1 : ℂ))))
  have h3 : Differentiable ℂ (fun z : ℂ => 1 - (q : ℂ) ^ (-z)) :=
    (differentiable_const (1 : ℂ)).sub (hp.comp differentiable_id.neg)
  have hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re} := by
    apply ((((differentiable_const ((c : ℂ) * (sourceLocalMellinShellMass K P : ℂ))).mul h1).mul
      h2).differentiableOn).div h3.differentiableOn
    intro z hz hn
    have h : ‖(q : ℂ) ^ (-z)‖ < 1 := sourceLocalMellinRatio_norm_lt_one K P z hz
    have he : (q : ℂ) ^ (-z) = 1 := (sub_eq_zero.mp hn).symm
    rw [he, norm_one] at h
    exact lt_irrefl _ h
  exact hf.congr (fun z hz => sourceLocalAnnularMellin_eq K P z hz)

end
end ArtinMatthews.SourcePhysical
