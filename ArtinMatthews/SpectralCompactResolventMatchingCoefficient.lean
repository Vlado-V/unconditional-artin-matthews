module

public import ArtinMatthews.SpectralCompactResolventHeightMatrix
public import ArtinMatthews.SpectralEisensteinRegularMatching
public import ArtinMatthews.SpectralMeromorphicFormMaps
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

/-! The meromorphic finite matching coefficient is the exact genuine
outgoing coefficient whenever the determinant is regular on the
actual off-cut resolvent domain. -/
noncomputable section
open Set Filter Topology Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0HeightMatchingRegular (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (s : ℂ) : Prop :=
  s*(1-s)∉(gamma0TruncatedFormData N Y hY).exceptional ∧
    (gamma0HeightMatchingMatrix N Y hY s).det≠0

def gamma0HeightMatchingCoefficient (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (s : ℂ) (F : Gamma0RegionL2 N) : Gamma0EisensteinCuspClasses N → ℂ :=
  (gamma0HeightMatchingMatrix N Y hY s).det⁻¹ •
    (gamma0HeightMatchingMatrix N Y hY s).cramer (gamma0HeightMatchingRhs N Y hY s F)

theorem gamma0HeightMatchingCoefficient_mulVec (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (s : ℂ) (F : Gamma0RegionL2 N)
    (hs : (gamma0HeightMatchingMatrix N Y hY s).det≠0) :
    (gamma0HeightMatchingMatrix N Y hY s).mulVec (gamma0HeightMatchingCoefficient N Y hY s F)=
      gamma0HeightMatchingRhs N Y hY s F := by
  rw [gamma0HeightMatchingCoefficient,Matrix.mulVec_smul,Matrix.mulVec_cramer,
    smul_smul,inv_mul_cancel₀ hs,one_smul]

theorem gamma0HeightMatchingRhs_meromorphicAt (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (F : ℂ → Gamma0RegionL2 N) (s : ℂ)
    (hF : AnalyticAt ℂ F s) (i : Gamma0EisensteinCuspClasses N) :
    MeromorphicAt (fun w => gamma0HeightMatchingRhs N Y hY w (F w) i) s :=
  spectralMeromorphicAt_comp_clm (innerSL ℂ (gamma0HeightOutgoingDefect N Y hY 2 i))
    (gamma0HeightMatchingDefect_apply_meromorphicAt N Y hY F s hF)

theorem gamma0HeightMatchingRhs_analyticAt (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (F : ℂ → Gamma0RegionL2 N) (s : ℂ)
    (hs : s*(1-s)∉(gamma0TruncatedFormData N Y hY).exceptional)
    (hF : AnalyticAt ℂ F s) (i : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0HeightMatchingRhs N Y hY w (F w) i) s :=
  ((innerSL ℂ (gamma0HeightOutgoingDefect N Y hY 2 i)).analyticAt _).comp
    (gamma0HeightMatchingDefect_apply_analyticAt N Y hY F s hs hF)

theorem gamma0HeightMatchingCoefficient_meromorphicAt (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (F : ℂ → Gamma0RegionL2 N) (s : ℂ)
    (hF : AnalyticAt ℂ F s) (i : Gamma0EisensteinCuspClasses N) :
    MeromorphicAt (fun w => gamma0HeightMatchingCoefficient N Y hY w (F w) i) s := by
  have hcol : MeromorphicAt (fun w => ((gamma0HeightMatchingMatrix N Y hY w).updateCol i
      (gamma0HeightMatchingRhs N Y hY w (F w))).det) s := by
    apply spectralMatrixDet_meromorphicAt
    intro j k
    by_cases h : k=i
    · simpa only [Matrix.updateCol_apply,ite_eq_left h] using gamma0HeightMatchingRhs_meromorphicAt N Y hY F s hF j
    · simpa only [Matrix.updateCol_apply,ite_eq_right h] using
        gamma0HeightMatchingMatrix_entry_meromorphic N Y hY j k s
  simpa only [gamma0HeightMatchingCoefficient,Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,Pi.inv_apply] using
    (gamma0HeightMatchingMatrix_det_meromorphic N Y hY s).inv.fun_mul hcol

theorem gamma0HeightMatchingCoefficient_analyticAt (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (F : ℂ → Gamma0RegionL2 N) (s : ℂ)
    (hs : gamma0HeightMatchingRegular N Y hY s)
    (hF : AnalyticAt ℂ F s) (i : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0HeightMatchingCoefficient N Y hY w (F w) i) s := by
  have hcol : AnalyticAt ℂ (fun w => ((gamma0HeightMatchingMatrix N Y hY w).updateCol i
      (gamma0HeightMatchingRhs N Y hY w (F w))).det) s := by
    apply spectralMatrixDet_analyticAt
    intro j k
    by_cases h : k=i
    · simpa only [Matrix.updateCol_apply,ite_eq_left h] using gamma0HeightMatchingRhs_analyticAt N Y hY F s hs.1 hF j
    · simpa only [Matrix.updateCol_apply,ite_eq_right h] using
        gamma0HeightMatchingMatrix_entry_analyticAt N Y hY s hs.1 j k
  simpa only [gamma0HeightMatchingCoefficient,Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,Pi.inv_apply] using
    ((gamma0HeightMatchingMatrix_det_analyticAt N Y hY s hs.1).inv hs.2).fun_mul hcol

theorem gamma0CompactForcingResolventTrueCoefficient_mulVec (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    (gamma0HeightMatchingMatrix N A.height A.pos s).mulVec (gamma0CompactForcingResolventTrueCoefficient N ψ A s hs)=
      gamma0HeightMatchingRhs N A.height A.pos s (gamma0SmoothSeedMass N ψ) := by
  funext i
  let L := innerSL ℂ (gamma0HeightOutgoingDefect N A.height A.pos 2 i)
  let b := gamma0CompactForcingResolventTrueCoefficient N ψ A s hs
  let D := gamma0HeightMatchingDefect N A.height A.pos s
  have h := congrArg L (gamma0CompactForcingResolventActualDefect_zero N ψ A s hs)
  change L (D (gamma0CompactForcingCorrectedMass N ψ s b))=L 0 at h
  simp only [gamma0CompactForcingCorrectedMass,map_sub,map_sum,map_smul,map_zero,smul_eq_mul] at h
  change (∑ j,L (D (gamma0CuspChannelForcing N (1-s) j))*b j)=L (D (gamma0SmoothSeedMass N ψ))
  simp_rw [mul_comm (L (D (gamma0CuspChannelForcing N (1-s) _)))]
  exact (sub_eq_zero.mp h).symm

theorem gamma0CompactForcingResolventMatchingCoefficient_eq_true (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain)
    (hd : (gamma0HeightMatchingMatrix N A.height A.pos s).det≠0) :
    gamma0HeightMatchingCoefficient N A.height A.pos s (gamma0SmoothSeedMass N ψ)=
      gamma0CompactForcingResolventTrueCoefficient N ψ A s hs := by
  let M := gamma0HeightMatchingMatrix N A.height A.pos s
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  exact (gamma0HeightMatchingCoefficient_mulVec N A.height A.pos s (gamma0SmoothSeedMass N ψ) hd).trans
    (gamma0CompactForcingResolventTrueCoefficient_mulVec N ψ A s hs).symm

end ArtinMatthews
