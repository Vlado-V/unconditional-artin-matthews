module

public import ArtinMatthews.VaryingKummerAnalyticMixedContourZeros
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinZeroUniform
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import ArtinMatthews.VaryingKummerAnalyticZeroSumLimit
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The zero sum in the actual finite residue rectangle converges to the
absolutely convergent sum over all genuine completed-Dedekind zeros. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Topology ContDiff BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedContourZeros_sum_tendsto {Φ : ℂ → ℂ}
    (hΦ : Summable (fun ρ => (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*Φ ρ))
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop) :
    Tendsto (fun i => ∑ ρ ∈ mixedContourZeros K (T i),
      (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*Φ ρ) l
        (𝓝 (∑' ρ, (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*Φ ρ)) := by
  apply complex_summable_tendsto_finset_sum hΦ
  intro ρ hρ
  have hm : zeroMultiplicity (mixedCompletedDedekindXi K) ρ ≠ 0 := by
    intro H
    simp only [H,Int.cast_zero,zero_mul,ne_eq,not_true_eq_false] at hρ
  have hz := (zeroMultiplicity_ne_zero_iff (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K) ρ).mp hm
  filter_upwards [hT.eventually_ge_atTop |ρ.im|] with i hi
  exact (mem_mixedContourZeros K (T i) ρ).mpr ⟨hz,hi⟩

theorem mixedMellin_zero_sum_tendsto
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f)
    {x : ℝ} (hx : 0 < x) {ι : Type*} {l : Filter ι} {T : ι → ℝ}
    (hT : Tendsto T l atTop) :
    Tendsto (fun i => ∑ ρ ∈ mixedContourZeros K (T i),
      (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ) l
        (𝓝 (∑' ρ, (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
          mellin f ρ*(x : ℂ)^ρ)) := by
  obtain ⟨C,hC,H⟩ := mixedCompletedDedekindXi_mellin_power_zero_uniform f hcompact hpositive hsmooth
  have HS := (H K x hx).1
  have HT := mixedContourZeros_sum_tendsto K (Φ := fun ρ => mellin f ρ*(x : ℂ)^ρ)
    (by simpa only [mul_assoc] using HS) hT
  simpa only [mul_assoc] using HT

end
end ArtinMatthews.VaryingKummerAnalytic
