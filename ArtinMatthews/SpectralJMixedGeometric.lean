module

public import ArtinMatthews.SpectralABLOppositeModulus
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralJForwardWeylNormalization
public import ArtinMatthews.SpectralJOddSynthesis
public import ArtinMatthews.SpectralJForwardBareFibre
public import ArtinMatthews.SpectralMixedCuspBesselFibre
public import ArtinMatthews.SpectralMixedJRegularizationTannery
public import ArtinMatthews.SpectralTrueWidthCompactSeries
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews
open MeasureTheory Set
open scoped ContDiff MatrixGroups
noncomputable section

-- The existing geometric modulus term is independent of the spectral branch.
theorem gamma0TrueWidthBareFibre_forwardJ_normalized
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (q : Ioi (0 : ℕ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    gamma0TrueWidthBareFibre N r s q m n (spectralJForwardSpectralWeight f) =
      gamma0ABLOppositeGeometricTerm N r s q m n f -
        gamma0ABLOppositeGeometricTerm N r s q m n (spectralJOddSynthesis f) := by
  letI : NeZero q.val := ⟨q.property.ne'⟩
  have he := gamma0TrueWidthBareFibre_forwardJ N r s q m n hm hn hmn f hf hc hp
  dsimp only at he
  have harg := spectral_mixed_weyl_argument (gamma0TrueWidthModulus N r s (q.val : ℝ)) n m
  rw [harg] at he
  unfold gamma0ABLOppositeGeometricTerm
  dsimp only
  rw [he]
  ring

theorem gamma0MixedJ_geometric_reconstruction
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    Summable (fun q : Ioi (0 : ℕ) =>
      ‖gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f‖) ∧
    Summable (fun q : Ioi (0 : ℕ) =>
      ‖gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
        (spectralJOddSynthesis f)‖) ∧
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f) =
      (∑' q : Ioi (0 : ℕ),
        gamma0TrueWidthBareFibre (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJForwardSpectralWeight f)) +
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis f)) := by
  let G (q : Ioi (0 : ℕ)) :=
    gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f
  let B (q : Ioi (0 : ℕ)) :=
    gamma0TrueWidthBareFibre (r * s) (gamma0CuspOneOver s) 1 q n m
      (spectralJForwardSpectralWeight f)
  let O (q : Ioi (0 : ℕ)) :=
    gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
      (spectralJOddSynthesis f)
  have hB : Summable (fun q => ‖B q‖) :=
    (gamma0MixedJRegularizedBareSeries_tendsto f hf hc hp r s hcop m n hmn).1
  have hG : Summable (fun q => ‖G q‖) := by
    simpa only [G, gamma0ABLOppositeGeometricTerm] using
      (gamma0TrueWidth_compactTest_summable (r * s) (gamma0CuspOneOver s) 1 n m
        (4 * Real.pi * Real.sqrt (|(n : ℝ) * (m : ℝ)|)) f hc hp).2.2
  have hpoint (q : Ioi (0 : ℕ)) : B q = G q - O q :=
    gamma0TrueWidthBareFibre_forwardJ_normalized (r * s) (gamma0CuspOneOver s) 1 q
      n m hn hm (by simpa only [mul_comm n m] using hmn) f hf hc hp
  have hOpoint (q : Ioi (0 : ℕ)) : O q = G q - B q := by
    rw [hpoint]
    ring
  have hO : Summable (fun q => ‖O q‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hG.add hB)
    intro q
    rw [hOpoint]
    exact norm_sub_le _ _
  refine ⟨hG, hO, ?_⟩
  change (∑' q, G q) = (∑' q, B q) + ∑' q, O q
  have hsum : (∑' q, B q) = (∑' q, G q) - ∑' q, O q := by
    simp_rw [hpoint]
    exact hG.of_norm.tsum_sub hO.of_norm
  rw [hsum]
  ring

end
end ArtinMatthews
