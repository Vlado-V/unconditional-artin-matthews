module

public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralKLAnalysisProductWeight
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual absolute modulus/spectral interchange for compact-test Weyl
multipliers.  Gaussian damping p > 1/4 absorbs the proved modulus growth,
and the actual KL measure absorbs the spectral edge. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralWeylGaussianSpectralIntegrand (M : ℝ → ℝ → ℂ) (p : ℝ)
    (F G : ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  Complex.exp (-(p : ℂ)*(q.1 : ℂ)^2)*(q.1 : ℂ)*M q.2 q.1*F q.2*star (G q.2)

theorem spectralWeylGaussianSpectralIntegrand_measurable (M : ℝ → ℝ → ℂ) (p : ℝ)
    (F G : ℝ → ℂ) (hM : Measurable (fun q : ℝ × ℝ => M q.1 q.2))
    (hF : Measurable F) (hG : Measurable G) :
    Measurable (spectralWeylGaussianSpectralIntegrand M p F G) := by
  have hMs := hM.comp measurable_swap
  unfold spectralWeylGaussianSpectralIntegrand
  exact ((((by fun_prop : Measurable (fun q : ℝ × ℝ =>
    Complex.exp (-(p : ℂ)*(q.1 : ℂ)^2))).mul (by fun_prop)).mul hMs).mul
      (hF.comp measurable_snd)).mul ((continuous_star.measurable.comp hG).comp measurable_snd)

theorem spectralWeylGaussianSpectralIntegrand_bound (M : ℝ → ℝ → ℂ) (p C : ℝ)
    (F G : ℝ → ℂ) {X r : ℝ}
    (hM : ‖(X : ℂ)*M r X‖ ≤ 4*Real.pi*Real.exp (X^2/4)*(1+C/r)) :
    ‖spectralWeylGaussianSpectralIntegrand M p F G (X,r)‖ ≤
      (4*Real.pi*Real.exp (-(p-1/4)*X^2))*(‖F r‖*‖G r‖*(1+C/r)) := by
  have he : ‖Complex.exp (-(p : ℂ)*(X : ℂ)^2)‖ = Real.exp (-p*X^2) := by
    rw [show -(p : ℂ)*(X : ℂ)^2 = ((-p*X^2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  have hi : spectralWeylGaussianSpectralIntegrand M p F G (X,r) =
      Complex.exp (-(p : ℂ)*(X : ℂ)^2)*((X : ℂ)*M r X)*F r*star (G r) := by
    unfold spectralWeylGaussianSpectralIntegrand
    ring_nf
  rw [hi,norm_mul,norm_mul,norm_mul,norm_star,he]
  calc
    _ ≤ (Real.exp (-p*X^2)*(4*Real.pi*Real.exp (X^2/4)*(1+C/r)))*‖F r‖*‖G r‖ := by
      gcongr
    _ = _ := by
      rw [show Real.exp (-p*X^2)*(4*Real.pi*Real.exp (X^2/4)*(1+C/r)) =
        (4*Real.pi*(1+C/r))*(Real.exp (-p*X^2)*Real.exp (X^2/4)) by ring,
        ← Real.exp_add,show -p*X^2+X^2/4 = -(p-1/4)*X^2 by ring]
      ring_nf

theorem spectralWeylGaussianSpectralIntegrand_integrable (M : ℝ → ℝ → ℂ) {p : ℝ}
    (hp : 1/4 < p) (C : ℝ) (F G : ℝ → ℂ)
    (hM : Measurable (fun q : ℝ × ℝ => M q.1 q.2))
    (hMb : ∀ r X : ℝ, 0 < r → 0 < X →
      ‖(X : ℂ)*M r X‖ ≤ 4*Real.pi*Real.exp (X^2/4)*(1+C/r))
    (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    Integrable (spectralWeylGaussianSpectralIntegrand M p F G)
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure) := by
  have hX : Integrable (fun X : ℝ => 4*Real.pi*Real.exp (-(p-1/4)*X^2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrable_exp_neg_mul_sq (sub_pos.mpr hp)).const_mul (4*Real.pi)).restrict
  have hr := spectralKL_continuous_L2_product_order_weight_integrable F G hcF hcG hF hG C
  have hb := hX.mul_prod hr
  apply hb.mono' (spectralWeylGaussianSpectralIntegrand_measurable M p F G hM
    hcF.measurable hcG.measurable).aestronglyMeasurable
  have hpos : ∀ᵐ q ∂((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure),
      0 < q.1 ∧ 0 < q.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
    exact ⟨hX,hr⟩
  filter_upwards [hpos] with q hq
  exact spectralWeylGaussianSpectralIntegrand_bound M p C F G (hMb q.2 q.1 hq.2 hq.1)

theorem spectralWeylJGaussianSpectralIntegrand_integrable {p : ℝ} (hp : 1/4 < p)
    (F G : ℝ → ℂ) (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    Integrable (spectralWeylGaussianSpectralIntegrand spectralWeylJMultiplier p F G)
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure) :=
  spectralWeylGaussianSpectralIntegrand_integrable _ hp _ F G spectralWeylJMultiplier_measurable
    (fun _ _ hr hX => spectralWeylJMultiplier_order_bound hr hX) hcF hcG hF hG

theorem spectralWeylKGaussianSpectralIntegrand_integrable {p : ℝ} (hp : 1/4 < p)
    (F G : ℝ → ℂ) (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    Integrable (spectralWeylGaussianSpectralIntegrand spectralWeylKMultiplier p F G)
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure) :=
  spectralWeylGaussianSpectralIntegrand_integrable _ hp _ F G spectralWeylKMultiplier_measurable
    (fun _ _ hr hX => spectralWeylKMultiplier_order_bound hr hX) hcF hcG hF hG

end ArtinMatthews
