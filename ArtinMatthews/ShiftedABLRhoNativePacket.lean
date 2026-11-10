module

public import ArtinMatthews.SpectralMixedSourcePacketTrace
public import ArtinMatthews.ShiftedABLRhoSourcePacket
public import ArtinMatthews.ShiftedABLSourceBudget
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.ShiftedABLRhoCommonTransforms
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

/-! The actual signed source block, with its common spatial test, is
the finite input of the native mixed-cusp forward traces. -/

noncomputable section
open Set OAI
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedABLSourceRhoIndex_ne_zero {m3 m4 : ℕ} {d : ℕ × ℕ} {i : ℕ × Bool}
    (ρ : shiftedABLSourceRhoIndex m3 m4 d i) : ρ.val ≠ 0 :=
  (shiftedABLRhoSignedBlock_band ρ.property).1

theorem shiftedABLSourceRhoIndex_magnitude_injective {m3 m4 : ℕ} {d : ℕ × ℕ} {i : ℕ × Bool} :
    Function.Injective (fun ρ : shiftedABLSourceRhoIndex m3 m4 d i =>
      sourceJHolomorphicIndexMagnitude ρ.val (shiftedABLSourceRhoIndex_ne_zero ρ)) := by
  intro ρ σ h
  have hm : ρ.val.natAbs = σ.val.natAbs := congrArg (fun j : ℕ+ => j.val) h
  have hd (x : shiftedABLSourceRhoIndex m3 m4 d i) : decide (x.val < 0) = i.2 :=
    congrArg Prod.snd (Finset.mem_filter.mp x.property).2
  have he := (hd ρ).trans (hd σ).symm
  rw [decide_eq_decide] at he
  apply Subtype.ext
  by_cases hρ : ρ.val < 0
  · have hσ := he.mp hρ
    have hc := congrArg (fun x : ℕ => (x : ℤ)) hm
    rw [Int.ofNat_natAbs_of_nonpos hρ.le,Int.ofNat_natAbs_of_nonpos hσ.le] at hc
    exact neg_injective hc
  · have hσ : ¬σ.val < 0 := fun hh => hρ (he.mpr hh)
    have hc := congrArg (fun x : ℕ => (x : ℤ)) hm
    rwa [Int.natAbs_of_nonneg (le_of_not_gt hρ),Int.natAbs_of_nonneg (le_of_not_gt hσ)] at hc

theorem gamma0MixedSourceCompensation_norm (r s : ℕ) (b n : ℤ) :
    ‖gamma0MixedSourceCompensation r s b n‖ = (s : ℝ)*Real.sqrt (r : ℝ) := by
  rw [gamma0MixedSourceCompensation,norm_mul,atkinPhase_norm,mul_one,
    Complex.norm_real,Real.norm_of_nonneg (by positivity)]

theorem shiftedABLFullSeparatedSignedSum_eq_nativePacket
    (χ : SevenEighths.HeckeFamily.Character) (D m3 m4 F L : ℕ) [NeZero F]
    (hr : (m3*m4).Coprime F) (hL : 0 < L) (hm3 : 0 < m3) (hm4 : 0 < m4) (hne : m3 ≠ m4)
    (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (t : ℝ) :
    let r := m3*m4
    let n := (m3 : ℤ)-(m4 : ℤ)
    let X := ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) ((2 : ℝ)^i.1)
      (shiftedABLFirstIndex m3 m4) r F
    let f := shiftedABLRhoCommonTest (4*Real.pi*X) (t+shiftedABLRhoHeight z)
    let U := shiftedABLSourceRhoIndex m3 m4 d i
    shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t =
      gamma0MixedSourcePacketSum f r F hr n U.attach
        (shiftedABLSourceRhoPacketCoefficient χ D m3 m4 d i z t) (fun ρ => ρ.val) := by
  have hh := shiftedABLFullSeparatedSignedSum_eq_source_tsum χ D m3 m4 F L hr hL hm3 hm4 hne d i z t
  dsimp only at hh ⊢
  rw [shiftedABLRhoBlockScale_eq_abl (NeZero.pos F)] at hh
  exact hh

end ArtinMatthews
