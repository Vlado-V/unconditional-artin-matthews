module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import ArtinMatthews.VaryingKummerAnalyticLogarithmicResidue
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaOrders
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
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

/-! Actual residues of the smoothed prime-ideal Mellin integrand. The
contribution at one is positive, nontrivial zeros retain their multiplicities,
and the contribution at zero is exactly -(r₁+r₂−1)Φ(0). -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Literal Mellin integrand of the negative logarithmic derivative. -/
def mixedExplicitFormulaIntegrand (f : ℝ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  -(mellin f s * (x : ℂ)^s) * logDeriv (mixedDedekindZeta K) s

variable (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
  (hpositive : tsupport f ⊆ Ioi 0) (hcontinuous : Continuous f)
  {x : ℝ} (hx : 0 < x)
include hcompact hpositive hcontinuous hx

theorem mixedExplicitFormulaIntegrand_residue {ρ : ℂ} {n : ℤ}
    (ho : meromorphicOrderAt (mixedDedekindZeta K) ρ = n) :
    Tendsto (fun s => (s-ρ)*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] ρ)
      (𝓝 (-(mellin f ρ*(x : ℂ)^ρ)*(n : ℂ))) := by
  have hw : ContinuousAt (fun s : ℂ => -(mellin f s*(x : ℂ)^s)) ρ :=
    (((smoothMellin_entire f hcompact hpositive hcontinuous ρ).mul
      (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))).neg).continuousAt
  exact meromorphic_weighted_logDeriv_residue (mixedDedekindZeta_meromorphic K ρ) ho hw

theorem mixedExplicitFormulaIntegrand_residue_one :
    Tendsto (fun s => (s-1)*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] 1)
      (𝓝 ((x : ℂ)*mellin f 1)) := by
  have H := mixedExplicitFormulaIntegrand_residue K f hcompact hpositive hcontinuous hx
    (mixedDedekindZeta_order_one K)
  simpa only [cpow_one,Int.cast_neg,Int.cast_one,neg_mul_neg,mul_one,one_mul,mul_comm] using H

theorem mixedExplicitFormulaIntegrand_residue_zero :
    Tendsto (fun s => s*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] 0)
      (𝓝 (-(((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*
        mellin f 0)) := by
  have H := mixedExplicitFormulaIntegrand_residue K f hcompact hpositive hcontinuous hx
    (mixedDedekindZeta_meromorphicOrder_zero K)
  simpa only [sub_zero,cpow_zero,mul_one,neg_mul,mul_neg,mul_comm] using H

theorem mixedExplicitFormulaIntegrand_residue_nontrivial {ρ : ℂ}
    (hρ : mixedCompletedDedekindXi K ρ = 0) :
    Tendsto (fun s => (s-ρ)*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] ρ)
      (𝓝 (-((zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
        mellin f ρ*(x : ℂ)^ρ))) := by
  have H := mixedExplicitFormulaIntegrand_residue K f hcompact hpositive hcontinuous hx
    (mixedDedekindZeta_order_at_xi_zero K hρ)
  convert H using 1
  congr 1
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
