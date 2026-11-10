module

public import ArtinMatthews.CubicGaloisFourier
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.PositiveDensityCubicRamification
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.PositiveDensityCubicProgression
public import ArtinMatthews.PositiveDensityCubicStatistic
public import ArtinMatthews.PositiveDensityEnlargedAssembly
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

/-! The arithmetic positive-density assembly with the ordinary and cubic
mean laws and the actual growing-prime Kummer zero region as inputs. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory VaryingKummerAnalytic
open scoped BigOperators Topology ContDiff

theorem positiveDyadicLowerBound_of_smooth_mean_laws_and_zero_region
    {S : Finset ℤ} (hS : AdmissibleBases S) (hA : ¬ ObstructionA S) (hB : ¬ ObstructionB S)
    {δ ε : ℝ} (hδ : δ ≤ 1) (hεδ : ε < δ) (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦsmooth : ContDiff ℝ ∞ Φ) (hΦcompact : HasCompactSupport Φ)
    (hΦsupport : tsupport Φ ⊆ Set.Ioo (1 : ℝ) 2)
    (hΦrange : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) (hΦnonzero : ∃ t, Φ t ≠ 0)
    (hzero : ∀ a ∈ S, ∀ q : ℕ, q.Prime → 2 < q → a.natAbs ≤ q →
      ∀ ρ : ℂ, mixedCompletedDedekindXi (primeKummerField q a) ρ = 0 → ρ.re ≤ 1 - δ)
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
    PositiveDyadicLowerBound S := by
  obtain ⟨T, hT₁, hT₂, hs⟩ := giantSieve_support_lt_two Φ hΦcompact hΦsupport
  obtain ⟨t, ht⟩ := hΦnonzero
  have hI : 0 < ∫ y : ℝ, Φ y :=
    hΦsmooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hΦcompact (fun y => (hΦrange y).1) ht
  let κ := giantPrimeConstant ε * ∫ y : ℝ, Φ y
  have hκ : 0 < κ := mul_pos (giantPrimeConstant_pos hε (by linarith)) hI
  rcases exists_quadratic_progression_dichotomy (fun a ha => (hS.2 a ha).1) hA with
    ⟨u, hprog⟩ | ⟨hrel, u, hprog⟩
  · apply positiveDyadicLowerBound_of_enlarged_mean hS hδ hεδ hε hεq hzero hprog
      (fun _ => True) (fun _ _ => Or.inl rfl) Φ hΦrange hT₁ hT₂ hs hκ
    intro Y _hY _habs
    let M := enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)
    let : NeZero M := ⟨(giantSieveEnlargedModulus_pos S Y).ne'⟩
    simpa only [giantSelectedPrimeTest_all, κ] using
      hordinary T hT₁ hT₂ hs M (giantSieveEnlargedUnits hprog Y)
  · have hcpos := cubicConditionDensity_pos hB hrel
    apply positiveDyadicLowerBound_of_enlarged_mean hS hδ hεδ hε hεq hzero hprog
      (giantCubicSieveSelection S (giantCubicRamifiedPrimes S))
      (fun _ hp => Or.inr hp.2) Φ hΦrange hT₁ hT₂ hs (mul_pos hcpos hκ)
    intro Y _hY _habs
    let M := enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)
    let U := giantSieveEnlargedUnits hprog Y
    let : NeZero M := ⟨(giantSieveEnlargedModulus_pos S Y).ne'⟩
    have h₃ : 3 ∣ M := giantSieve_three_dvd_enlargedModulus S Y
    have hclass : ∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1 := by
      intro v hv
      simpa only [Nat.cast_one] using giantSieve_enlarged_unit_mod_three hprog Y hv
    apply (hcubic T hT₁ hT₂ hs M h₃ U hclass).congr'
    filter_upwards [giantSelectedPrimeTest_cubic_frobenius_eventually hS hprog Y ε Φ
      hΦrange hT₁ hT₂ hs] with x hx
    exact congrArg (fun z : ℂ => ((Real.log x / x : ℝ) : ℂ) * z) hx.symm

end ArtinMatthews
