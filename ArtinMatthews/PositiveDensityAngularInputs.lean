module

public import ArtinMatthews.KummerAngularSourceBounds
public import ArtinMatthews.CubicGaloisFourier
public import ArtinMatthews.PositiveDensityCubicRamification
public import ArtinMatthews.RealDensity
public import ArtinMatthews.PositiveDensitySmoothAnalyticInputs
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

/-! The positive-density branch from the literal ordinary and cubic smooth
mean laws and the source angular bounds. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory VaryingKummerAnalytic
open scoped BigOperators Topology ContDiff

theorem positive_density_of_smooth_mean_laws_and_angular_sources
    {S : Finset ℤ} (hS : AdmissibleBases S) (hA : ¬ ObstructionA S) (hB : ¬ ObstructionB S)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε < 1 / 1000000)
    (Φ : ℝ → ℝ) (hΦsmooth : ContDiff ℝ ∞ Φ) (hΦcompact : HasCompactSupport Φ)
    (hΦsupport : tsupport Φ ⊆ Set.Ioo (1 : ℝ) 2)
    (hΦrange : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) (hΦnonzero : ∃ t, Φ t ≠ 0)
    (hsource : ∀ (q : ℕ) [NeZero q], q.Prime → 2 < q → TwelfthAngularSourceBounds q)
    (hordinary : ∀ T : ℝ, 1 < T → T < 2 → Function.support Φ ⊆ Set.Ioo 1 T →
      ∀ (M : ℕ) [NeZero M] (U : Finset (ZMod M)ˣ),
        Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
          giantUncenteredPrimeTest U ε Φ T x) atTop
          (𝓝 (((U.card : ℝ) / Nat.totient M *
            (giantPrimeConstant ε * ∫ t : ℝ, Φ t) : ℝ) : ℂ)))
    (hcubic : ∀ T : ℝ, 1 < T → T < 2 → Function.support Φ ⊆ Set.Ioo 1 T →
      ∀ (M : ℕ) [NeZero M] (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ),
        (∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1) →
        Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
          giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x) atTop
          (𝓝 (((U.card : ℝ) / Nat.totient M *
            (cubicConditionDensity S * (giantPrimeConstant ε * ∫ t : ℝ, Φ t)) : ℝ) : ℂ))) :
    PositiveDyadicLowerBound S ∧ PositiveLowerRelativePrimeDensity S ∧
      PositiveRealLowerRelativePrimeDensity S := by
  have hzero : ∀ a ∈ S, ∀ q : ℕ, q.Prime → 2 < q → a.natAbs ≤ q →
      ∀ ρ : ℂ, mixedCompletedDedekindXi (primeKummerField q a) ρ = 0 →
        ρ.re ≤ 1 - 1 / 1000000 := by
    intro a ha q hq hq₂ haq
    let : NeZero a := ⟨(hS.2 a ha).1⟩
    let : NeZero q := ⟨hq.ne_zero⟩
    exact primeKummer_zero_region_of_angular_source_bounds q a hq hq₂ haq (hsource q hq hq₂)
  have hεq : ε < 1 / 4 := hεδ.trans (by norm_num)
  have hdyadic := positiveDyadicLowerBound_of_smooth_mean_laws_and_zero_region hS hA hB
    (δ := (1 / 1000000 : ℝ)) (by norm_num) hεδ hε hεq Φ hΦsmooth hΦcompact
    hΦsupport hΦrange hΦnonzero hzero hordinary hcubic
  exact ⟨hdyadic, hdyadic.positiveLowerRelativePrimeDensity,
    hdyadic.positiveRealLowerRelativePrimeDensity⟩

end ArtinMatthews
