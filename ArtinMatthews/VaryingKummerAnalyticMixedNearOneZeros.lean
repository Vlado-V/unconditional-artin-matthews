module

public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import ArtinMatthews.VaryingKummerAnalyticZeroSeparation
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaLogDerivBound
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import ArtinMatthews.VaryingKummerAnalyticMixedXiReality
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroBaseBound
public import ArtinMatthews.VaryingKummerAnalyticSeparatedPoleBound
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Unconditional field-uniform near-one zero structure for the genuine mixed
Dedekind completion. The only possible zero in the explicit padded box is real,
simple, and unique; the separated zero-pole error has an explicit bound. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical ComplexConjugate
noncomputable section
universe u
variable (K : Type u) [Field K] [NumberField K]

theorem mixedCompletedDedekindXi_nearOne_unique {C : ℝ} (hC : 0 ≤ C)
    (hGamma : ∀ σ : ℝ, σ ∈ Icc (1:ℝ) 2 →
      ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤ C*(Module.finrank ℚ K : ℝ))
    {ρ : ℂ} (hρ : mixedCompletedDedekindXi K ρ = 0)
    (hbox : InNearOneBox (mixedZeroScale K C) ρ) :
    zeroMultiplicity (mixedCompletedDedekindXi K) ρ = 1 ∧ ρ.im = 0 ∧
      ∀ τ, mixedCompletedDedekindXi K τ = 0 →
        InNearOneBox (mixedZeroScale K C) τ → τ = ρ := by
  exact nearOneBox_real_simple_unique (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K) (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (mixedCompletedDedekindXi_conj K)
    (fun z hz => (mixedCompletedDedekindXi_zeros_in_strip K z hz).2)
    (mixedZeroScale_pos K hC) (A := 0) (by simpa using mixedZeroScale_pos K hC)
    (by simpa using mixedCompletedDedekindXi_logDeriv_at_zeroScale K hC hGamma) hρ hbox

theorem mixedCompletedDedekindXi_nearOne_error {C : ℝ} (hC : 0 ≤ C)
    (hGamma : ∀ σ : ℝ, σ ∈ Icc (1:ℝ) 2 →
      ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤ C*(Module.finrank ℚ K : ℝ))
    {h : ℝ} (hh : 0 < h) (hh4 : h ≤ 4/mixedZeroScale K C) :
    |(logDeriv (mixedCompletedDedekindXi K) ((1+h : ℝ) : ℂ)).re -
      ∑' ρ, nearOneZeroPole (mixedCompletedDedekindXi K) (mixedZeroScale K C) (1+h) ρ| ≤
        1014*mixedZeroScale K C := by
  have H := logDeriv_re_nearOne_error_le (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K) (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun z hz => (mixedCompletedDedekindXi_zeros_in_strip K z hz).2)
    (mixedZeroScale_pos K hC) hh hh4
    (mixedCompletedDedekindXi_logDeriv_at_zeroScale K hC hGamma)
  convert H using 1
  ring

/-- One universal constant works for every number field and every signature. -/
theorem exists_uniform_mixedDedekind_nearOne :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      (∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 →
        InNearOneBox (mixedZeroScale K C) ρ →
        zeroMultiplicity (mixedCompletedDedekindXi K) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, mixedCompletedDedekindXi K τ = 0 →
            InNearOneBox (mixedZeroScale K C) τ → τ = ρ) ∧
      (∀ h : ℝ, 0 < h → h ≤ 4/mixedZeroScale K C →
        |(logDeriv (mixedCompletedDedekindXi K) ((1+h : ℝ) : ℂ)).re -
          ∑' ρ, nearOneZeroPole (mixedCompletedDedekindXi K) (mixedZeroScale K C) (1+h) ρ| ≤
            1014*mixedZeroScale K C) := by
  obtain ⟨C,hC,hΓ⟩ := exists_mixedGammaFactor_logDeriv_bound.{u}
  refine ⟨C,hC,fun K _ _ => ⟨?_, ?_⟩⟩
  · exact fun _ hρ hbox => mixedCompletedDedekindXi_nearOne_unique K hC.le (hΓ K) hρ hbox
  · exact fun _ hh hh4 => mixedCompletedDedekindXi_nearOne_error K hC.le (hΓ K) hh hh4

end
end ArtinMatthews.VaryingKummerAnalytic
