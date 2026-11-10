module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedGoodHeight
public import ArtinMatthews.VaryingKummerAnalyticMixedXiContourBound
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
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

/-! The genuine zero-avoiding heights carry a field-uniform full norm bound
throughout the horizontal contour strip. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
noncomputable section
universe u

theorem log_height_le_twice_midpoint {T t : ℝ} (ht : t ∈ Icc T (T+1)) :
    Real.log (|t|+2) ≤ 2*Real.log (|T+1/2|+2) := by
  have habs : |t| ≤ |T+1/2|+1 := by
    apply abs_le.mpr
    constructor
    · linarith [ht.1, neg_abs_le (T+1/2)]
    · linarith [ht.2, le_abs_self (T+1/2)]
  have harg : |t|+2 ≤ 2*(|T+1/2|+2) := by linarith [abs_nonneg (T+1/2)]
  have hlog2 : Real.log 2 ≤ Real.log (|T+1/2|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg (T+1/2)])
  calc
    _ ≤ Real.log (2*(|T+1/2|+2)) := Real.log_le_log (by positivity) harg
    _ = Real.log 2 + Real.log (|T+1/2|+2) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ _ := by linarith

theorem mixedDedekind_height_scale_ge_log_two
    (K : Type u) [Field K] [NumberField K] (T : ℝ) :
    Real.log 2 ≤ Real.log |(discr K : ℝ)| +
      (Module.finrank ℚ K : ℝ)*Real.log (|T|+2) := by
  have hn : 1 ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hD := discr_log_nonneg K
  have hl : Real.log 2 ≤ Real.log (|T|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  have hl0 : 0 ≤ Real.log (|T|+2) := Real.log_nonneg (by linarith [abs_nonneg T])
  nlinarith

theorem exists_mixedCompletedDedekindXi_good_height_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ T : ℝ,
      ∃ t ∈ Icc T (T+1),
        (∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 → 0 < |t-ρ.im|) ∧
        ∀ σ : ℝ, -(1/2 : ℝ) ≤ σ → σ ≤ 2 →
          ‖logDeriv (mixedCompletedDedekindXi K) (⟨σ,t⟩ : ℂ)‖ ≤
            C*(Real.log |(discr K : ℝ)| +
              (Module.finrank ℚ K : ℝ)*Real.log (|T+1/2|+2))^2 := by
  obtain ⟨B,hB,hbase⟩ := exists_mixedCompletedDedekindXi_horizontal_norm_bound.{u}
  obtain ⟨H,hH,hheight⟩ := exists_mixedDedekind_good_height.{u}
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨44*B/Real.log 2 + 36*B*H,by positivity,?_⟩
  intro K _ _ T
  let L := Real.log |(discr K : ℝ)| +
    (Module.finrank ℚ K : ℝ)*Real.log (|T+1/2|+2)
  have hLmin : Real.log 2 ≤ L := mixedDedekind_height_scale_ge_log_two K (T+1/2)
  have hL : 0 < L := hl2.trans_le hLmin
  let δ := 1/(2*(H*L+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨t,ht,havoid⟩ := hheight K T
  change ∀ ρ, mixedCompletedDedekindXi K ρ = 0 → δ ≤ |t-ρ.im| at havoid
  refine ⟨t,ht,fun ρ hρ => hδ.trans_le (havoid ρ hρ),?_⟩
  intro σ hσ hσ'
  have h := hbase K t σ δ hσ hσ' hδ havoid
  have hscale : Real.log |(discr K : ℝ)| +
      (Module.finrank ℚ K : ℝ)*Real.log (|t|+2) ≤ 2*L := by
    have hlog := mul_le_mul_of_nonneg_left (log_height_le_twice_midpoint ht)
      (show 0 ≤ (Module.finrank ℚ K : ℝ) by positivity)
    have hD := discr_log_nonneg K
    dsimp [L]
    linarith
  have hδinv : 1/δ = 2*(H*L+1) := by dsimp [δ]; simp
  have hsmall : L ≤ L^2/Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith [mul_le_mul_of_nonneg_left hLmin hL.le]
  calc
    _ ≤ B*(4+9/δ)*(2*L) := h.trans
      (mul_le_mul_of_nonneg_left hscale (by positivity))
    _ = 44*B*L + 36*B*H*L^2 := by
      have he : 9/δ = 9*(1/δ) := by ring
      rw [he,hδinv]
      ring
    _ ≤ (44*B/Real.log 2 + 36*B*H)*L^2 := by
      have hm := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 44*B by positivity)
      calc
        _ ≤ 44*B*(L^2/Real.log 2) + 36*B*H*L^2 := by linarith
        _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
