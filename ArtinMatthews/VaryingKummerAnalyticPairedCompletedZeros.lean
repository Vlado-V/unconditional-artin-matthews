module

public import ArtinMatthews.VaryingKummerAnalyticPairedCompleted
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow
public import ArtinMatthews.VaryingKummerAnalyticComplexZeroPole
public import ArtinMatthews.VaryingKummerAnalyticComplexZeroCount
public import ArtinMatthews.VaryingKummerAnalyticWeightedZeroSum
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Positive pole sums, exact multiplicity counts and weighted zero sums
for the genuine inverse-character product. Its value at zero is an explicit
input: right-half-plane nonvanishing does not supply that boundary fact. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open ArtinMatthews.ReusedGrowth OAI.PrimeDegreePackets.AnalyticGrowth
open Complex
open scoped BigOperators
noncomputable section
variable {F G : ℂ → ℂ} {W : ℂ}
variable (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
variable (h0 : pairedCompleted F G 0 ≠ 0)
variable (hgF : HasSubquadraticGrowth F) (hgG : HasSubquadraticGrowth G)
variable (hfe : ∀ s, F s = W * G (1-s))
variable (hFr : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
variable (hGr : ∀ s : ℂ, 1 < s.re → G s ≠ 0)
include hF hG h0 hgF hgG hfe hFr hGr

theorem pairedCompleted_hasSum_complexZeroPole {s : ℂ} (hs : 1 < s.re) :
    HasSum (complexZeroPole (pairedCompleted F G) s)
      (logDeriv (pairedCompleted F G) s).re :=
  hasSum_complexZeroPole (pairedCompleted_entire hF hG) h0
    (pairedCompleted_hasSubquadraticGrowth hgF hgG)
    (pairedCompleted_functionalEquation hfe)
    (fun _ hρ => (pairedCompleted_zero_strip hfe hFr hGr hρ).2) hs

theorem pairedCompleted_finite_zero_height_window_bound
    (S : Finset ℂ) (T : ℝ) (hT : ∀ ρ ∈ S, |T-ρ.im| ≤ 1) :
    (∑ ρ ∈ S, (zeroMultiplicity (pairedCompleted F G) ρ : ℝ)) ≤
      5*(logDeriv (pairedCompleted F G) (⟨2,T⟩ : ℂ)).re :=
  finite_zero_height_window_bound (pairedCompleted_entire hF hG) h0
    (pairedCompleted_hasSubquadraticGrowth hgF hgG)
    (pairedCompleted_functionalEquation hfe)
    (fun _ hρ => (pairedCompleted_zero_strip hfe hFr hGr hρ).2) S T hT

theorem pairedCompleted_zeroHeightCount_le_logDeriv (T : ℝ) :
    zeroHeightCount (pairedCompleted F G) T ≤
      5*(logDeriv (pairedCompleted F G) (⟨2,T⟩ : ℂ)).re :=
  zeroHeightCount_le_logDeriv (pairedCompleted_entire hF hG) h0
    (pairedCompleted_hasSubquadraticGrowth hgF hgG)
    (pairedCompleted_functionalEquation hfe)
    (fun _ hρ => (pairedCompleted_zero_strip hfe hFr hGr hρ).2) T

theorem pairedCompleted_finite_zero_height_window_bound_of_logDeriv_bounds
    (S : Finset ℂ) (T : ℝ) (hT : ∀ ρ ∈ S, |T-ρ.im| ≤ 1) {B C : ℝ}
    (hB : ‖logDeriv F (⟨2,T⟩ : ℂ)‖ ≤ B)
    (hC : ‖logDeriv G (⟨2,T⟩ : ℂ)‖ ≤ C) :
    (∑ ρ ∈ S, (zeroMultiplicity (pairedCompleted F G) ρ : ℝ)) ≤ 5*(B+C) := by
  have hs : 1 < (⟨2,T⟩ : ℂ).re := by norm_num
  have hp := (Complex.re_le_norm _).trans
    (pairedCompleted_logDeriv_norm_le hF hG (hFr _ hs) (hGr _ hs) hB hC)
  exact (pairedCompleted_finite_zero_height_window_bound hF hG h0 hgF hgG hfe hFr hGr
    S T hT).trans (mul_le_mul_of_nonneg_left hp (by norm_num))

theorem pairedCompleted_factor_multiplicity_height_window_bound
    (S : Finset ℂ) (T : ℝ) (hT : ∀ ρ ∈ S, |T-ρ.im| ≤ 1) {B C : ℝ}
    (hB : ‖logDeriv F (⟨2,T⟩ : ℂ)‖ ≤ B)
    (hC : ‖logDeriv G (⟨2,T⟩ : ℂ)‖ ≤ C) :
    (∑ ρ ∈ S, ((zeroMultiplicity F ρ : ℝ) + (zeroMultiplicity G ρ : ℝ))) ≤
      5*(B+C) := by
  simpa only [pairedCompleted_zeroMultiplicity hF hG h0, Int.cast_add] using
    pairedCompleted_finite_zero_height_window_bound_of_logDeriv_bounds
      hF hG h0 hgF hgG hfe hFr hGr S T hT hB hC

theorem pairedCompleted_zeroHeightCount_le_of_logDeriv_bound (T : ℝ) {B : ℝ}
    (hB : (logDeriv (pairedCompleted F G) (⟨2,T⟩ : ℂ)).re ≤ B) :
    zeroHeightCount (pairedCompleted F G) T ≤ 5*B :=
  (pairedCompleted_zeroHeightCount_le_logDeriv hF hG h0 hgF hgG hfe hFr hGr T).trans
    (mul_le_mul_of_nonneg_left hB (by norm_num))

theorem pairedCompleted_zeroHeightCount_le_of_factor_logDeriv_bounds (T : ℝ) {B C : ℝ}
    (hB : ‖logDeriv F (⟨2,T⟩ : ℂ)‖ ≤ B)
    (hC : ‖logDeriv G (⟨2,T⟩ : ℂ)‖ ≤ C) :
    zeroHeightCount (pairedCompleted F G) T ≤ 5*(B+C) := by
  have hs : 1 < (⟨2,T⟩ : ℂ).re := by norm_num
  apply pairedCompleted_zeroHeightCount_le_of_logDeriv_bound hF hG h0 hgF hgG hfe hFr hGr T
  exact (Complex.re_le_norm _).trans
    (pairedCompleted_logDeriv_norm_le hF hG (hFr _ hs) (hGr _ hs) hB hC)

omit hgF hgG in
theorem pairedCompleted_mem_zeroHeightWindow_iff (T : ℝ) (ρ : ℂ) :
    ρ ∈ zeroHeightWindow (pairedCompleted F G) T ↔
      (F ρ = 0 ∨ G ρ = 0) ∧ |T-ρ.im| ≤ 1 := by
  rw [mem_zeroHeightWindow_iff (pairedCompleted_entire hF hG) h0
    (pairedCompleted_functionalEquation hfe)
    (fun _ hρ => (pairedCompleted_zero_strip hfe hFr hGr hρ).2), pairedCompleted_zero_iff]

theorem pairedCompleted_weighted_zero_summable_and_bound {Φ : ℂ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hΦ : ∀ ρ, pairedCompleted F G ρ = 0 → ‖Φ ρ‖ ≤ C/(1+|ρ.im|)^2) :
    Summable (fun ρ => (zeroMultiplicity (pairedCompleted F G) ρ : ℂ)*Φ ρ) ∧
      (∑' ρ, ‖(zeroMultiplicity (pairedCompleted F G) ρ : ℂ)*Φ ρ‖) ≤
        4*C*(logDeriv (pairedCompleted F G) 2).re :=
  weighted_zero_summable_and_bound (pairedCompleted_entire hF hG) h0
    (pairedCompleted_hasSubquadraticGrowth hgF hgG)
    (pairedCompleted_functionalEquation hfe) hC (fun _ => pairedCompleted_zero_strip hfe hFr hGr) hΦ

theorem pairedCompleted_weighted_zero_summable_and_bound_of_logDeriv_bounds
    {Φ : ℂ → ℂ} {C B D : ℝ} (hC : 0 ≤ C)
    (hΦ : ∀ ρ, pairedCompleted F G ρ = 0 → ‖Φ ρ‖ ≤ C/(1+|ρ.im|)^2)
    (hB : ‖logDeriv F 2‖ ≤ B) (hD : ‖logDeriv G 2‖ ≤ D) :
    Summable (fun ρ => (zeroMultiplicity (pairedCompleted F G) ρ : ℂ)*Φ ρ) ∧
      (∑' ρ, ‖(zeroMultiplicity (pairedCompleted F G) ρ : ℂ)*Φ ρ‖) ≤ 4*C*(B+D) := by
  obtain ⟨hS,hbound⟩ := pairedCompleted_weighted_zero_summable_and_bound
    hF hG h0 hgF hgG hfe hFr hGr hC hΦ
  refine ⟨hS,hbound.trans ?_⟩
  have hs : 1 < (2 : ℂ).re := by norm_num
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4*C)
  exact (Complex.re_le_norm _).trans
    (pairedCompleted_logDeriv_norm_le hF hG (hFr _ hs) (hGr _ hs) hB hD)

end
end ArtinMatthews.VaryingKummerAnalytic
