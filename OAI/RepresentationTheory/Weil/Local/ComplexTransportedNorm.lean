module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.RepresentationTheory.Weil.Local.ArchimedeanNorm


set_option backward.privateInPublic true
@[expose] public section

/-! # Complex Transported Norm -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexTransportedNorm.Construction

noncomputable section

/-! The transported complex norm is a positive power of the usual complex modulus. -/

theorem continuous_complex_embedding_circle_norm
    {k : Type} [NormedField k] (e : ℂ →+* k) (he : Continuous e) (u : Circle) :
    ‖e (u : ℂ)‖ = 1 := by
  have hcont : Continuous (fun v : Circle => ‖e (v : ℂ)‖) := (he.comp continuous_subtype_val).norm
  obtain ⟨B, hB⟩ := (isCompact_range hcont).bddAbove
  have hle (v : Circle) : ‖e (v : ℂ)‖ ≤ 1 := by
    by_contra! hv
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt B hv
    have hb := hB (Set.mem_range_self (v ^ m))
    simp only [Circle.coe_pow, map_pow, norm_pow] at hb
    exact not_lt_of_ge hb hm
  have hprod : ‖e (u : ℂ)‖ * ‖e ((u⁻¹ : Circle) : ℂ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, map_one, norm_one]
  apply le_antisymm (hle u)
  calc
    1 = ‖e (u : ℂ)‖ * ‖e ((u⁻¹ : Circle) : ℂ)‖ := hprod.symm
    _ ≤ ‖e (u : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left (hle u⁻¹) (norm_nonneg _)
    _ = ‖e (u : ℂ)‖ := mul_one _

theorem continuous_complex_embedding_norm_power
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) (e : ℂ →+* k) (he : Continuous e) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ z : ℂ, ‖e z‖ = ‖z‖ ^ s := by
  obtain ⟨s, hs, hs1, hR⟩ := ArchimedeanNorm.Construction.continuous_real_embedding_norm_power h (e.comp Complex.ofRealHom)
    (he.comp Complex.continuous_ofReal)
  refine ⟨s, hs, hs1, fun z => ?_⟩
  by_cases hz : z = 0
  · simp [hz, hs.ne']
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnC : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let u : Circle := ⟨z / (‖z‖ : ℂ), by
    change z / (‖z‖ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self hn]⟩
  have hpolar : z = (‖z‖ : ℂ) * (u : ℂ) := by
    change z = (‖z‖ : ℂ) * (z / (‖z‖ : ℂ))
    field_simp
  calc
    ‖e z‖ = ‖e (‖z‖ : ℂ)‖ * ‖e (u : ℂ)‖ := by rw [← norm_mul, ← map_mul, ← hpolar]
    _ = ‖z‖ ^ s := by
      rw [continuous_complex_embedding_circle_norm e he u, mul_one]
      simpa only [RingHom.comp_apply, abs_of_nonneg (norm_nonneg _)] using! hR ‖z‖

end

end OAI.RepresentationTheory.Weil.Local.ComplexTransportedNorm.Construction
