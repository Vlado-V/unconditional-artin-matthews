module

public import ArtinMatthews.VaryingKummerAnalyticSplitPrimeComparison
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! One actual fixed nonnegative compact smooth majorant for the dyadic
prime interval, independent of every field, prime q and scale x. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

def splitPrimeBump : ContDiffBump (3/2 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def splitPrimeWeight (y : ℝ) : ℂ := (splitPrimeBump y : ℂ)

theorem splitPrimeWeight_compact : HasCompactSupport splitPrimeWeight :=
  splitPrimeBump.hasCompactSupport.comp_left Complex.ofReal_zero

theorem splitPrimeWeight_smooth : ContDiff ℝ ∞ splitPrimeWeight :=
  Complex.ofRealCLM.contDiff.comp splitPrimeBump.contDiff

theorem splitPrimeWeight_nonneg (y : ℝ) : 0 ≤ (splitPrimeWeight y).re :=
  splitPrimeBump.nonneg

theorem splitPrimeWeight_positive_support : tsupport splitPrimeWeight ⊆ Ioi 0 := by
  have ht : tsupport splitPrimeWeight ⊆ tsupport splitPrimeBump :=
    tsupport_comp_subset Complex.ofReal_zero _
  rw [splitPrimeBump.tsupport_eq] at ht
  intro y hy
  have h := ht hy
  rw [Metric.mem_closedBall,Real.dist_eq] at h
  change |y-3/2| ≤ 1 at h
  have H := (abs_le.mp h).1
  change 0 < y
  linarith

theorem splitPrimeWeight_eq_one (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) :
    splitPrimeWeight y = 1 := by
  have h : y ∈ Metric.closedBall (3/2 : ℝ) splitPrimeBump.rIn := by
    rw [Metric.mem_closedBall,Real.dist_eq]
    change |y-3/2| ≤ 1/2
    exact abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  simp only [splitPrimeWeight,splitPrimeBump.one_of_mem_closedBall h,Complex.ofReal_one]

theorem splitPrimeWeight_majorant (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) :
    1 ≤ (splitPrimeWeight y).re := by rw [splitPrimeWeight_eq_one y hy]; norm_num

end
end ArtinMatthews.VaryingKummerAnalytic
