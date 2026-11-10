module

public import ArtinMatthews.VaryingKummerAnalyticZeroGrowth
public import ArtinMatthews.VaryingKummerAnalyticComplexZeroCount
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

/-! A concrete finite set containing exactly the zeros in a unit height
window, and the corresponding multiplicity count. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth

open ArtinMatthews.ReusedGrowth
open Complex
open scoped BigOperators
noncomputable section

/-- All zeros whose imaginary part is within one of T. The disk is large
enough for the entire critical strip in this height window. -/
def zeroHeightWindow (f : ℂ → ℂ) (T : ℝ) : Finset ℂ :=
  (zeroDiskFinset f (|T|+2)).filter (fun ρ => |T-ρ.im| ≤ 1)

lemma zero_in_height_window_norm_le {ρ : ℂ} {T : ℝ}
    (hρ₀ : 0 ≤ ρ.re) (hρ₁ : ρ.re ≤ 1) (hT : |T-ρ.im| ≤ 1) :
    ‖ρ‖ ≤ |T|+2 := by
  have him : |ρ.im| ≤ |T|+1 := by
    have H := abs_le.mp hT
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self T, neg_le_abs T]
  have H := Complex.norm_le_abs_re_add_abs_im ρ
  rw [abs_of_nonneg hρ₀] at H
  linarith

lemma mem_zeroHeightWindow_iff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) (ρ : ℂ) :
    ρ ∈ zeroHeightWindow f T ↔ f ρ = 0 ∧ |T-ρ.im| ≤ 1 := by
  classical
  rw [zeroHeightWindow,Finset.mem_filter]
  constructor
  · rintro ⟨hm,hT⟩
    refine ⟨?_,hT⟩
    apply (zeroMultiplicity_ne_zero_iff hf h0 ρ).mp
    have H := (mem_zeroDiskFinset f (|T|+2) ρ).mp hm
    rwa [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hm)] at H
  · rintro ⟨hz,hT⟩
    refine ⟨?_,hT⟩
    have hr := hstrip ρ hz
    have hl := hstrip (1-ρ) (by rwa [hfe])
    have hρ₀ : 0 ≤ ρ.re := by
      simp only [Complex.sub_re,Complex.one_re] at hl
      linarith
    rw [mem_zeroDiskFinset,divisor_closedBall_eq_multiplicity hf
      (zero_in_height_window_norm_le hρ₀ hr hT)]
    exact (zeroMultiplicity_ne_zero_iff hf h0 ρ).mpr hz

/-- Multiplicity is retained, including repeated zeros. -/
def zeroHeightCount (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  ∑ ρ ∈ zeroHeightWindow f T, (zeroMultiplicity f ρ : ℝ)

theorem zeroHeightCount_le_logDeriv {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) :
    zeroHeightCount f T ≤ 5*(logDeriv f (⟨2,T⟩ : ℂ)).re := by
  apply finite_zero_height_window_bound hf h0 hg hfe hstrip
  intro ρ hρ
  exact (Finset.mem_filter.mp hρ).2

end
end OAI.PrimeDegreePackets.AnalyticGrowth
