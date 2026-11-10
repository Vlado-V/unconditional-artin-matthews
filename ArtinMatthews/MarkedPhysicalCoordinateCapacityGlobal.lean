module

public import ArtinMatthews.MarkedPhysicalCoordinateLineTerms
public import ArtinMatthews.MarkedPhysicalMomentTube
public import ArtinMatthews.MarkedPhysicalCapacityCostAbsorption
public import ArtinMatthews.MarkedPhysicalCoordinateCapacityEnvelope
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual finite summation of the omitted-cap error, including the
original physical mass and the full fixed-coordinate good volume. The
source small-B estimate absorbs the proved carrier/coefficient costs. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalMomentTubeRadius_ge_one (n : ℕ) {K H : ℝ}
    (hK : 0≤K) (hH : 0≤H) : 1 ≤ markedPhysicalMomentTubeRadius n K H := by
  have hh := Nat.le_ceil (16+512*(n:ℝ)*K*H)
  have hm : 0≤512*(n:ℝ)*K*H := by positivity
  have h : (1:ℝ)≤(markedPhysicalMomentTubeRadius n K H:ℝ) := by
    unfold markedPhysicalMomentTubeRadius
    linarith
  exact_mod_cast h

def markedPhysicalCoordinateCapacityGlobal {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U W : ℝ) (B : ℕ) (hB : 1≤B) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B,
      markedPhysicalCoordinateCapacityTerm e x
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hB q U W
        (markedDirtyMemoryCutoff x)

theorem markedPhysicalCoordinateCapacityGlobal_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,(1/10:ℝ)≤e j) (he1 : ∀ j,e j≤(1/5:ℝ))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp G : ℝ)
    (hK : 0≤K) (hHexp : 0≤Hexp) (heta : 0≤etaBound) (hpsi : 0≤psiBound)
    (hQexp : 0≤Qexp) (hη : ∀ t,‖η t‖≤etaBound) (hψ : ∀ t,‖ψ t‖≤psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0≤d₀) (hY : 1≤Y),
      d₀*Y≤Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) → ∀ (q U W : ℝ),0≤q → q≤1 →
      ‖markedPhysicalCoordinateCapacityGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W
        (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
        (markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀ (zero_le_one.trans hY)))‖≤
          (Real.log x)^(-G) := by
  filter_upwards [markedPhysicalCoordinateCapacityTerm_envelope e he0,
    markedPhysicalCoordinateCapacity_actual_log_saving e he0 he1 ψ η K Hexp etaBound psiBound Qexp (G+1)
      hK hHexp heta hpsi hQexp hη hψ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (15:ℝ))] with x hterm htotal hlog
  intro d₀ Y hd₀ hY hscale q U W hq0 hq1
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  let B := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hB : 1≤B := markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀ (zero_le_one.trans hY))
  let coeff := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp)
      (n := markedMemoryMomentLength x) (B := B)
  have hs : (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) B,
      ‖markedPhysicalCoordinateCapacityTerm e x V ψ η d₀ Y ((Real.log x)^Qexp) i hB q U W
        (markedDirtyMemoryCutoff x)‖)≤
      15*markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x*(∑ i,‖coeff i‖) := by
    calc
      _ ≤ ∑ i,15*markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x*‖coeff i‖ :=
        Finset.sum_le_sum (fun i _ => hterm V ψ η d₀ Y ((Real.log x)^Qexp) q U W hq0 hq1 B hB i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hV : ∀ j,0≤V j := by
    intro j
    unfold V bandReciprocalMass
    positivity
  have hm : 0 ≤ markedPhysicalMass V (markedPadSlots x) := markedPhysicalMass_nonneg V _ hV
  have hh := htotal d₀ Y hd₀ hY hscale
  change (markedPhysicalMass V (markedPadSlots x)*(∑ i,‖coeff i‖))*
    markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x≤(Real.log x)^(-(G+1)) at hh
  have hbound : ‖markedPhysicalCoordinateCapacityGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W B hB‖≤
      15*(Real.log x)^(-(G+1)) := by
    unfold markedPhysicalCoordinateCapacityGlobal
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
    apply ((mul_le_mul_of_nonneg_left (norm_sum_le _ _) hm).trans
      (mul_le_mul_of_nonneg_left hs hm)).trans
    calc
      _ = 15*((markedPhysicalMass V (markedPadSlots x)*(∑ i,‖coeff i‖))*
          markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  apply hbound.trans
  have hL : 0<Real.log x := by linarith
  calc
    15*(Real.log x)^(-(G+1)) ≤ Real.log x*(Real.log x)^(-(G+1)) :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hL.le _)
    _ = (Real.log x)^(1:ℝ)*(Real.log x)^(-(G+1)) := by rw [Real.rpow_one]
    _ = (Real.log x)^(-G) := by rw [← Real.rpow_add hL]; congr 1; ring

end
end ArtinMatthews
