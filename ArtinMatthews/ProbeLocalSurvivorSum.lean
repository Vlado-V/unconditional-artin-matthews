module

public import ArtinMatthews.ProbePrimeRawWeights
public import ArtinMatthews.ProbeEulerLocalAlgebra
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute geometric summation of the explicit local survivor index. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open scoped BigOperators Classical
noncomputable section

theorem probe_local_geometric_product (E V : ℂ) (hE : ‖E‖ < 1) (hV : ‖V‖ < 1) :
    HasSum (fun ds : ℕ × ℕ => E ^ ds.1 * V ^ ds.2)
      ((1 - E)⁻¹ * (1 - V)⁻¹) := by
  have he : Summable (fun d : ℕ => ‖E ^ d‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg E) hE
  have hv : Summable (fun r : ℕ => ‖V ^ r‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg V) hV
  exact (hasSum_geometric_of_norm_lt_one hE).mul
    (hasSum_geometric_of_norm_lt_one hV) (summable_mul_of_summable_norm he hv)

theorem probeLocalSurvivor_hasSum (q R W D V : ℂ) (hq : q ≠ 0)
    (hV : ‖V‖ < 1) (hW : ‖W‖ < 1) (hE : ‖R * V‖ < 1) :
    HasSum (probeLocalSurvivorValue q R W D V)
      (ArtinMatthews.probeGoodLocalFactor q V W D (R * V)) := by
  let E := R * V
  have hg := probe_local_geometric_product E V hE hV
  have h0 := hasSum_geometric_of_norm_lt_one hV
  have h1 : HasSum (fun k : ℕ => W ^ (k + 1)) (W * (1 - W)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hW).mul_left W using 1
    funext k
    rw [pow_succ']
  have h2 : HasSum (fun ds : ℕ × ℕ =>
      R ^ (ds.1 + 1) * (1 - q⁻¹) * V ^ (ds.1 + 1 + ds.2))
      (((1 - q⁻¹) * E) * ((1 - E)⁻¹ * (1 - V)⁻¹)) := by
    convert hg.mul_left ((1 - q⁻¹) * E) using 1
    funext ds
    change R ^ (ds.1 + 1) * (1 - q⁻¹) * V ^ (ds.1 + 1 + ds.2) =
      (1 - q⁻¹) * (R * V) * ((R * V) ^ ds.1 * V ^ ds.2)
    simp only [pow_add, pow_one, mul_pow]
    ring
  have h3 : HasSum (fun d : ℕ => R ^ (d + 1) * W * V ^ (d + 1))
      ((W * E) * (1 - E)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hE).mul_left (W * E) using 1
    funext d
    change R ^ (d + 1) * W * V ^ (d + 1) = (W * (R * V)) * (R * V) ^ d
    simp only [pow_add, pow_one, mul_pow]
    ring
  have h4 : HasSum (fun d : ℕ => -D * R ^ d * V ^ d) (-D * (1 - E)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hE).mul_left (-D) using 1
    funext d
    change -D * R ^ d * V ^ d = -D * (R * V) ^ d
    rw [mul_pow]
    ring
  have h5 : HasSum (fun ds : ℕ × ℕ =>
      -D * W * R ^ ds.1 * (q - 1) * V ^ (ds.1 + 1 + ds.2))
      ((-D * W * (q - 1) * V) * ((1 - E)⁻¹ * (1 - V)⁻¹)) := by
    convert hg.mul_left (-D * W * (q - 1) * V) using 1
    funext ds
    change -D * W * R ^ ds.1 * (q - 1) * V ^ (ds.1 + 1 + ds.2) =
      (-D * W * (q - 1) * V) * ((R * V) ^ ds.1 * V ^ ds.2)
    simp only [pow_add, pow_one, mul_pow]
    ring
  have hs : HasSum (probeLocalSurvivorValue q R W D V)
      ((1 - V)⁻¹ + (W * (1 - W)⁻¹ +
        (((1 - q⁻¹) * E) * ((1 - E)⁻¹ * (1 - V)⁻¹) +
          ((W * E) * (1 - E)⁻¹ +
            (-D * (1 - E)⁻¹ +
              ((-D * W * (q - 1) * V) * ((1 - E)⁻¹ * (1 - V)⁻¹))))))) := by
    apply HasSum.sum
    · exact h0
    · apply HasSum.sum
      · exact h1
      · apply HasSum.sum
        · exact h2
        · apply HasSum.sum
          · exact h3
          · apply HasSum.sum
            · exact h4
            · exact h5
  have hv : 1 - V ≠ 0 := by
    intro h
    have he : V = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hV
    exact lt_irrefl _ hV
  have hw : 1 - W ≠ 0 := by
    intro h
    have he : W = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hW
    exact lt_irrefl _ hW
  have he : 1 - E ≠ 0 := by
    intro h
    have he : R * V = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hE
    exact lt_irrefl _ hE
  convert hs using 1
  unfold ArtinMatthews.probeGoodLocalFactor
  dsimp only [E] at he ⊢
  field_simp
  ring

end

end ArtinMatthews.VaryingKummerAnalytic
