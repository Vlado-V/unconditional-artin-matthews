module

public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceKPAdelicOrbitHeight
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceKPAdelicCuspOverlap
public import ArtinMatthews.SourceKPAdelicCutoffSupport
public import ArtinMatthews.SourceKPAdelicHeightAction
public import ArtinMatthews.SourceKPAdelicSectionBound
public import ArtinMatthews.SourceKPAdelicUpperProjection
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

/-! Exact cutoff values on the high adelic cusp, including the transition band. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCoverHeight_left_upper (y : 𝔸[K])
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCoverHeight K hζ (sourceKPAdelicUpperLift K hζ y * q) =
      sourceKPAdelicCoverHeight K hζ q := by
  unfold sourceKPAdelicCoverHeight
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  rw [map_mul, sourceKPAdelicUpperLift_projection, ← hg, ← map_mul,
    sourceKPAdelicHeightOnProjective_mk, sourceKPAdelicHeightOnProjective_mk,
    sourceKPAdelicHeight_left_borel K hζ _ _ (sourceKPRingNormalizedBorel_upper 𝔸[K] y)]
  have hdet : GeneralLinearGroup.det (sourceKPUpperMatrix 𝔸[K] y) = 1 := by
    simpa only [map_one, mul_one] using sourceKPUpperDiagonal_det y (1 : (𝔸[K])ˣ)
  rw [hdet, map_one, one_mul]

theorem sourceKPAdelicOrbitHeight_eq_cover_of_high
    (q : SourceKPAdelicProjective K hζ) (hq : 1 < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicOrbitHeight K hζ q = sourceKPAdelicCoverHeight K hζ q := by
  refine le_antisymm ?_ (sourceKPAdelicCoverHeight_le_orbit K hζ q)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨γ, rfl⟩
  by_cases hγ : γ ∈ sourceKPRationalBorel K
  · exact (sourceKPAdelicCoverHeight_left_rationalBorel K hζ γ hγ q).le
  · have hle := le_of_not_gt (fun ht => hγ (sourceKPAdelicCoverHeight_high_overlap K hζ q γ hq ht))
    exact hle.trans hq.le

theorem sourceKPAdelicCutoffEisenstein_eq_cutoffSeed_of_high {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : 1 < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicCutoffEisenstein K hζ T s q =
      (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ q) : ℂ) *
        sourceKPAdelicCompactScalar K hζ s q := by
  let c₀ := sourceKPRationalBorelCosetMk K (1 : PGL(2,K))
  have h₀ : sourceKPAdelicRationalHeight K hζ q c₀ = sourceKPAdelicCoverHeight K hζ q := by
    change sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ 1 * q) = _
    rw [map_one, one_mul]
  have hhigh : 1 < sourceKPAdelicRationalHeight K hζ q c₀ := h₀ ▸ hq
  have hz (c : SourceKPRationalBorelCoset K) (hc : c ≠ c₀) :
      sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c = 0 := by
    apply sourceKPAdelicCutoffSummand_zero K hζ (zero_lt_one.trans_le hT) s q c
    refine (le_of_not_gt fun hh => hc ?_).trans hT
    exact sourceKPAdelicRationalHeight_high_subsingleton K hζ q hh hhigh
  change (∑' c, sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c) = _
  rw [tsum_eq_single c₀ hz]
  change (sourceKPAdelicCutoffSeed K hζ T s).val (sourceKPAdelicProjectiveRationalLift K hζ 1 * q) =
    (sourceKPAdelicCutoffSeed K hζ T s).val q
  rw [map_one, one_mul]

theorem sourceKPAdelicCompactScalar_left_upper (s : ℂ) (y : 𝔸[K])
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicUpperLift K hζ y * q) =
      sourceKPAdelicCompactScalar K hζ s q :=
  sourceKPAdelicPrincipalSeriesScalar_upper K hζ s (sourceKPAdelicCompactSection K hζ s) y q

theorem sourceKPAdelicCutoffEisenstein_left_upper_of_high {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (y : 𝔸[K]) (q : SourceKPAdelicProjective K hζ) (hq : 1 < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicCutoffEisenstein K hζ T s (sourceKPAdelicUpperLift K hζ y * q) =
      sourceKPAdelicCutoffEisenstein K hζ T s q := by
  have hH := sourceKPAdelicCoverHeight_left_upper K hζ y q
  rw [sourceKPAdelicCutoffEisenstein_eq_cutoffSeed_of_high K hζ hT s _ (hH.symm ▸ hq),
    sourceKPAdelicCutoffEisenstein_eq_cutoffSeed_of_high K hζ hT s q hq,
    hH, sourceKPAdelicCompactScalar_left_upper]

end
end ArtinMatthews
