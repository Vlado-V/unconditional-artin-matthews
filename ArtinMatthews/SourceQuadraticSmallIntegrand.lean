module

public import ArtinMatthews.SourceQuadraticSmallContourIntegral
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

namespace ArtinMatthews
open NumberField Complex MeasureTheory Set VaryingKummerAnalytic
open OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical ContDiff BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem quadraticSmallContourIntegrand_integrable (m : Ideal (𝓞 F))
    (w : ℝ → ℂ) (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0)
    (hs : ContDiff ℝ ∞ w) {σ X : ℝ} (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4)
    (hσone : σ ≠ 1) (hX : 0 < X) :
    Integrable (fun t : ℝ => quadraticSmallContourKernel F w σ t *
      (X : ℂ) ^ quadraticPoissonLine σ t * quadraticSmallEuler F m (quadraticPoissonLine σ t)) := by
  apply (quadraticPoissonLine_cpow_integrable _
    (quadraticSmallContourKernel_continuous F w hc hp hs hσone)
    (quadraticSmallContourKernel_integrable F w hc hp hs hσ hσtop hσone) σ hX).mul_bdd
  · exact ((quadraticSmallEuler_continuous F m).comp (by
      unfold quadraticPoissonLine
      fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun t => quadraticSmallEuler_norm_le F m
      (by rw [quadraticPoissonLine_re]; exact hσ.le))

theorem quadraticSmall_sqrt_ratio_cpow {M Q : ℝ} (hM : 0 < M) (hQ : 0 < Q) (s : ℂ) :
    (Real.sqrt (M / Q) : ℂ) ^ s = (M : ℂ) ^ (s / 2) * (Q : ℂ) ^ (-(s / 2)) := by
  rw [quadraticPoisson_sqrt_cpow (div_pos hM hQ).le, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hM.le hQ.le, Complex.cpow_neg, div_eq_mul_inv]

end
end ArtinMatthews
