module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import ArtinMatthews.VaryingKummerAnalyticMixedXiConjugateLog
public import ArtinMatthews.VaryingKummerAnalyticMixedXiGoodHeightBound
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaHighStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Actual symmetric contour heights, with a polynomial majorant adequate
for rapid Mellin decay. The field is fixed only after uniform analytic
bounds have supplied the constants. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open scoped Topology
noncomputable section
universe u

private theorem height_mass_le_linear (K : Type u) [Field K] [NumberField K]
    (n : ℕ) {u : ℝ} (hu : |u| ≤ (n : ℝ)+3) :
    Real.log |(discr K : ℝ)| + (Module.finrank ℚ K : ℝ)*Real.log (|u|+2) ≤
      (Real.log |(discr K : ℝ)|+2*(Module.finrank ℚ K : ℝ))*((n : ℝ)+3) := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < |u|+2 by positivity)
  have hD := discr_log_nonneg K
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hd : 0 ≤ (Module.finrank ℚ K : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left (show Real.log (|u|+2) ≤ 2*((n : ℝ)+3) by linarith) hd
  nlinarith [mul_nonneg hD hn]

theorem exists_mixedDedekindZeta_good_sequence
    (K : Type u) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℕ → ℝ,
      (∀ n : ℕ, t n ∈ Icc ((n : ℝ)+2) ((n : ℝ)+3)) ∧
      Tendsto t atTop atTop ∧
      (∀ (n : ℕ) (ρ : ℂ), mixedCompletedDedekindXi K ρ = 0 → |ρ.im| ≠ t n) ∧
      ∀ (n : ℕ) (σ : ℝ), -(1/2 : ℝ) ≤ σ → σ ≤ 2 →
        ‖logDeriv (mixedDedekindZeta K) (⟨σ,t n⟩ : ℂ)‖ ≤ C*((n : ℝ)+3)^2 ∧
        ‖logDeriv (mixedDedekindZeta K) (⟨σ,-t n⟩ : ℂ)‖ ≤ C*((n : ℝ)+3)^2 := by
  obtain ⟨B,hB,hxi⟩ := exists_mixedCompletedDedekindXi_good_height_norm_bound.{u}
  obtain ⟨E,hE,hzeta⟩ := exists_mixedDedekindZeta_high_strip_logDeriv_bound.{u}
  have hx (n : ℕ) := hxi K ((n : ℝ)+2)
  choose t ht ha hb using hx
  have ht' (n : ℕ) : t n ∈ Icc ((n : ℝ)+2) ((n : ℝ)+3) := by
    simpa only [add_assoc, show (2 : ℝ)+1=3 by norm_num] using ht n
  have htpos (n : ℕ) : 0 < t n := by linarith [(ht' n).1,Nat.cast_nonneg (α := ℝ) n]
  have htone (n : ℕ) : 1 ≤ |t n| := by rw [abs_of_pos (htpos n)]; linarith [(ht' n).1,Nat.cast_nonneg (α := ℝ) n]
  have havoid (n : ℕ) := mixedCompletedDedekindXi_symmetric_height_avoids K (ha n)
  let L := Real.log |(discr K : ℝ)|+2*(Module.finrank ℚ K : ℝ)
  have hL : 0 < L := by
    have hD := discr_log_nonneg K
    have hd : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    dsimp [L]
    linarith
  refine ⟨B*L^2+E*L,by positivity,t,ht',?_,havoid,?_⟩
  · exact tendsto_atTop_mono (fun n => (ht' n).1)
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  intro n σ hσ hσ'
  have hN : 1 ≤ (n : ℝ)+3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hmid : |(n : ℝ)+2+1/2| ≤ (n : ℝ)+3 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hm := height_mass_le_linear K n hmid
  have hm0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).le.trans
    (mixedDedekind_height_scale_ge_log_two K ((n : ℝ)+2+1/2))
  have hxib : ‖logDeriv (mixedCompletedDedekindXi K) (⟨σ,t n⟩ : ℂ)‖ ≤
      B*L^2*((n : ℝ)+3)^2 := by
    calc
      _ ≤ B*(Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ)*Real.log (|(n : ℝ)+2+1/2|+2))^2 := hb n σ hσ hσ'
      _ ≤ B*(L*((n : ℝ)+3))^2 := by gcongr
      _ = _ := by ring
  have hmass : Real.log |(discr K : ℝ)| + (Module.finrank ℚ K : ℝ)*Real.log (|t n|+2) ≤
      L*((n : ℝ)+3) := height_mass_le_linear K n (by rw [abs_of_pos (htpos n)]; exact (ht' n).2)
  have hgeneral (s : ℂ) (hs : s.re = σ) (hi : |s.im| = |t n|)
      (hxb : ‖logDeriv (mixedCompletedDedekindXi K) s‖ ≤ B*L^2*((n : ℝ)+3)^2) :
      ‖logDeriv (mixedDedekindZeta K) s‖ ≤ (B*L^2+E*L)*((n : ℝ)+3)^2 := by
    have hnz : mixedCompletedDedekindXi K s ≠ 0 := by
      intro hz
      apply havoid n s hz
      rw [hi,abs_of_pos (htpos n)]
    have h := hzeta K s (by rw [hs]; exact hσ) (by rw [hs]; exact hσ')
      (by rw [hi]; exact htone n) hnz
    rw [hi] at h
    have hem := mul_le_mul_of_nonneg_left hmass hE.le
    have hel : 0 ≤ E*L := mul_nonneg hE.le hL.le
    nlinarith [mul_nonneg hel (show 0 ≤ ((n : ℝ)+3)^2-((n : ℝ)+3) by nlinarith)]
  constructor
  · exact hgeneral ⟨σ,t n⟩ rfl rfl hxib
  · exact hgeneral ⟨σ,-t n⟩ rfl (by simp) (by
      rw [mixedCompletedDedekindXi_logDeriv_norm_neg_height]
      exact hxib)

end
end ArtinMatthews.VaryingKummerAnalytic
