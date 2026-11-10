module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import ArtinMatthews.MarkedMajorArcCharacterPhase
public import ArtinMatthews.MarkedMajorArcDivisorReindex
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform genuine oscillation for the individual divisor terms of a
rough-number inclusion-exclusion expansion. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_divisor_character_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧ 0 < U₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t H : ℝ)
        (d M N : ℕ), 0 < d → U₀ ≤ H/d →
        1 ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ (H/d)^B →
        H ≤ (M:ℝ)+1 → (N:ℝ) ≤ 2*H →
        ‖∑ n ∈ Ioc M N, if d ∣ n then
          χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I) else 0‖ ≤
        (q:ℝ)*A*((H/d)/Real.sqrt |t/(2*Real.pi)|+(H/d)^(1-δ)) := by
  obtain ⟨A,δ,hA,hδ,hhalf,he⟩ := marked_character_log_phase_uniform B hB
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp he
  refine ⟨A,δ,max U₀ 1,hA,hδ,hhalf,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro q _ χ t H d M N hd hscale ht htB hM hN
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hL : H/d ≤ ((M/d+1:ℕ):ℝ) := by
    apply (div_le_iff₀ hdR).2
    have hm : M < (M/d+1)*d := (Nat.div_lt_iff_lt_mul hd).1 (by omega)
    have hmR : (M:ℝ)+1 ≤ ((M/d+1:ℕ):ℝ)*(d:ℝ) := by exact_mod_cast hm
    exact hM.trans hmR
  have hR : ((N/d:ℕ):ℝ) ≤ 2*(H/d) := by
    calc
      _ ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
      _ ≤ (2*H)/(d:ℝ) := div_le_div_of_nonneg_right hN hdR.le
      _ = _ := by ring
  have hb := hU₀ (H/d) ((le_max_left _ _).trans hscale) q χ t
    (M/d+1) (N/d) ht htB hL hR
  have hi : Ioc (M/d) (N/d) = Icc (M/d+1) (N/d) := by ext n; simp
  rw [marked_divisor_character_sum_eq q χ t hd, norm_mul, hi]
  calc
    _ ≤ 1*‖∑ m ∈ Icc (M/d+1) (N/d), χ (m:ZMod q)*(m:ℂ)^((t:ℂ)*Complex.I)‖ :=
      mul_le_mul_of_nonneg_right (marked_character_imaginary_power_norm_le q χ t hd) (norm_nonneg _)
    _ ≤ _ := by simpa using hb

 theorem marked_scaled_power_reciprocal_bound {H d S δ : ℝ}
    (hH : 0 < H) (hd : 0 < d) (hS : 0 < S) (hscale : S ≤ H/d)
    (hδ : 0 ≤ δ) :
    (H/d)^(1-δ) ≤ (H/d)*S^(-δ) := by
  rw [sub_eq_add_neg,Real.rpow_add (div_pos hH hd), Real.rpow_one]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hS hscale (neg_nonpos.mpr hδ))
    (div_nonneg hH.le hd.le)

end ArtinMatthews
