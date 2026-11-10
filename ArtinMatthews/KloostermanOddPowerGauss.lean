module

public import ArtinMatthews.KloostermanOddPowerArithmetic
public import ArtinMatthews.KloostermanCubicStationary
public import ArtinMatthews.KloostermanOddPowerPhase
public import ArtinMatthews.QuadraticAffineGaussNorm
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


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine square-root cancellation in every actual stationary second-order orbit. -/
noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

attribute [local instance] Classical.decEq

theorem oddPower_shiftGauss_norm (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (a b : OddPowerRing p m) (ha : oddPowerReduction p m a ≠ 0) (u : (OddPowerRing p m)ˣ)
    (hu : u∈stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b) :
    ‖∑ z : ZMod p, ZMod.stdAddChar
      ((((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))*(a-b*(↑u⁻¹:OddPowerRing p m)^2)+
        (((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))^2*(b*(↑u⁻¹:OddPowerRing p m)^3))‖ =
      Real.sqrt p := by
  simp_rw [oddPower_phase_reduction p m a b u hu]
  have hF : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  have h2 : (2:ZMod p)≠0 := by
    intro h
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hp2'
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hp2 hp2'
  have hψ : (ZMod.stdAddChar : AddChar (ZMod p) ℂ)≠1 := by
    simpa using (ZMod.isPrimitive_stdAddChar p) (a := 1) one_ne_zero
  simpa only [ZMod.card] using quadraticAffineGauss_norm hF h2 ZMod.stdAddChar hψ
    (oddPower_stationary_quadratic_ne_zero p m hm a b ha u hu)
    ((((a-b*(↑u⁻¹:OddPowerRing p m)^2).val/p^m:ℕ):ZMod p))

theorem oddPower_averaged_norm (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (a b : OddPowerRing p m) (ha : oddPowerReduction p m a ≠ 0) :
    (p:ℝ)*‖sum ZMod.stdAddChar a b‖ ≤
      ((stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b).card:ℝ)*Real.sqrt p := by
  have havg := kloosterman_cubic_stationary_average (Z := ZMod p)
    (R := OddPowerRing p m) ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar _)
    ((p^(m+1):ℕ):OddPowerRing p m) ((p^m:ℕ):OddPowerRing p m) a b
    (oddPower_outer_square_zero p m) (oddPower_inner_cube_zero p m hm)
    (oddPower_outer_mul_inner_zero p m) (fun z => (z.val:OddPowerRing p m))
  simp only [ZMod.card] at havg
  calc
    _ = ‖(p:ℂ)*sum ZMod.stdAddChar a b‖ := by simp
    _ = _ := congrArg norm havg
    _ ≤ ∑ u ∈ stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b,
        ‖ZMod.stdAddChar (a*(u:OddPowerRing p m)+b*(↑u⁻¹:OddPowerRing p m))*
          ∑ z : ZMod p, ZMod.stdAddChar
            ((((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))*(a-b*(↑u⁻¹:OddPowerRing p m)^2)+
              (((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))^2*(b*(↑u⁻¹:OddPowerRing p m)^3))‖ :=
      norm_sum_le _ _
    _ = ∑ _u ∈ stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b, Real.sqrt p := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_mul,AddChar.norm_apply,one_mul,oddPower_shiftGauss_norm p m hm hp2 a b ha u hu]
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end ArtinMatthews.PrimePowerWeil
