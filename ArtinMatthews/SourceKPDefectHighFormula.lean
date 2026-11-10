module

public import ArtinMatthews.SourceKPAdelicDefectRadialFormula
public import ArtinMatthews.SourceKPAutomorphicCompactDefect
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceKPAdelicCuspBand
public import ArtinMatthews.SourceKPAdelicCutoffSupport
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

/-! The actual cutoff defect vanishes below its height threshold and is
unipotent invariant on the high cusp. -/

namespace ArtinMatthews
open NumberField Matrix Set
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCutoffCasimirDefect_zero_of_orbit_le {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : sourceKPAdelicOrbitHeight K hζ q ≤ T / 2) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s q = 0 := by
  have hz (c : SourceKPRationalBorelCoset K) :
      sourceKPAdelicDefectTerm K hζ T s q c = 0 := by
    have hc : sourceKPAdelicRationalHeight K hζ q c ≤ T / 2 := by
      induction c using Quotient.inductionOn with
      | _ γ =>
        exact (le_csSup (sourceKPAdelicOrbitHeight_range_bddAbove K hζ q)
          (Set.mem_range_self γ)).trans hq
    rw [sourceKPAdelicDefectTerm, sourceKPAdelicDefectCoefficient_zero hT hc, zero_mul]
  simp only [sourceKPAdelicCutoffCasimirDefect_radial_sum K hζ hT s q, hz, tsum_zero, mul_zero]

/-- At high cover height the actual rational defect sum contains just the
identity coset. -/
theorem sourceKPAdelicCutoffCasimirDefect_high_formula {T : ℝ} (hT : 2 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : T / 2 < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s q =
      (InfinitePlace.nrComplexPlaces K : ℂ) *
        (sourceKPAdelicDefectCoefficient T s (sourceKPAdelicCoverHeight K hζ q) *
          sourceKPAdelicCompactScalar K hζ s q) := by
  let c₀ := sourceKPRationalBorelCosetMk K (1 : PGL(2, K))
  have h₀ : sourceKPAdelicRationalHeight K hζ q c₀ = sourceKPAdelicCoverHeight K hζ q := by
    change sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ 1 * q) = _
    rw [map_one, one_mul]
  have hc₀ : 1 < sourceKPAdelicRationalHeight K hζ q c₀ := by rw [h₀]; linarith
  have hz (c : SourceKPRationalBorelCoset K) (hc : c ≠ c₀) :
      sourceKPAdelicDefectTerm K hζ T s q c = 0 := by
    have hle : sourceKPAdelicRationalHeight K hζ q c ≤ 1 := by
      apply le_of_not_gt
      intro h
      exact hc (sourceKPAdelicRationalHeight_high_subsingleton K hζ q h hc₀)
    rw [sourceKPAdelicDefectTerm,
      sourceKPAdelicDefectCoefficient_zero (by linarith : 0 < T) (hle.trans (by linarith)), zero_mul]
  rw [sourceKPAdelicCutoffCasimirDefect_radial_sum K hζ (by linarith : 0 < T),
    tsum_eq_single c₀ hz, sourceKPAdelicDefectTerm, h₀]
  change _ * (_ * (sourceKPAdelicPrincipalSeriesScalar K hζ s
    (sourceKPAdelicCompactSection K hζ s)).val (sourceKPAdelicProjectiveRationalLift K hζ 1 * q)) = _
  rw [map_one, one_mul]
  rfl

theorem sourceKPAdelicCutoffCasimirDefect_high_upper {T : ℝ} (hT : 2 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : T / 2 < sourceKPAdelicCoverHeight K hζ q)
    (y : 𝔸[K]) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s (sourceKPAdelicUpperLift K hζ y * q) =
      sourceKPAdelicCutoffCasimirDefect K hζ T s q := by
  have hH := sourceKPAdelicCoverHeight_left_upper K hζ y q
  have hqy : T / 2 < sourceKPAdelicCoverHeight K hζ (sourceKPAdelicUpperLift K hζ y * q) := by
    rwa [hH]
  have hu := sourceKPAdelicPrincipalSeriesScalar_upper K hζ s
    (sourceKPAdelicCompactSection K hζ s) y q
  change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicUpperLift K hζ y * q) =
    sourceKPAdelicCompactScalar K hζ s q at hu
  rw [sourceKPAdelicCutoffCasimirDefect_high_formula K hζ hT s _ hqy,
    sourceKPAdelicCutoffCasimirDefect_high_formula K hζ hT s q hq, hH, hu]

theorem sourceKPAutomorphicCompactCutoffDefect_zero_of_orbit_le {T : ℝ} (hT : 0 < T) (s : ℂ)
    (x : SourceKPAutomorphicCompactLevel K hζ)
    (hx : sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ T / 2) :
    sourceKPAutomorphicCompactCutoffDefect K hζ hT s x = 0 := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q, rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    change sourceKPAutomorphicCompactOrbitHeight K hζ
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) ≤ T / 2 at hx
    rw [sourceKPAutomorphicCompactOrbitHeight_mk, sourceKPAutomorphicOrbitHeight_mk] at hx
    change sourceKPAutomorphicCompactCutoffDefect K hζ hT s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) = 0
    rw [sourceKPAutomorphicCompactCutoffDefect_adelic]
    exact sourceKPAdelicCutoffCasimirDefect_zero_of_orbit_le K hζ hT s q hx

end
end ArtinMatthews
