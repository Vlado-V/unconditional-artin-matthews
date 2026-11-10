module

public import ArtinMatthews.MarkedPhysicalSourceBad
public import ArtinMatthews.MarkedPhysicalPairingCoordinates
public import ArtinMatthews.MarkedPhysicalCanonicalWindow
public import ArtinMatthews.MarkedPhysicalEndpointNorm
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

/-! The original source-bad physical coefficient in the exact canonical
integer coordinates. All source/target labels and the copied divisor are
the literal products of the original union marking. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedPhysical_source_bad_canonical_norm_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z) = 1)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H F G : ℝ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hG : 0 ≤ G) (hη : ∀ t, ‖η t‖ ≤ H)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ F) (hg : ∀ s, ‖g s‖ ≤ G)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    [NeZero (markedPhysicalMarkingProduct u)]
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D) (z : ℤ × ℤ)
    (s t : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z)
    (hs : s.1.2 = markedPhysicalEdgeSource u) (ht : t.1.2 = markedPhysicalEdgeTarget u)
    (hspos : s.1.1.1 = markedPhysicalCanonicalRootPosition r)
    (htpos : t.1.1.1 = (markedPhysicalCanonicalTargetEquiv hA hC r).symm z) :
    ‖markedPhysicalEdgeCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V
      ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1 s t *
      star (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f s) * g t‖ ≤
      markedPhysicalMass V (markedPadSlots x+1) * H^2 * F * G *
        (if markedPhysicalActualEdgeCopiedDivisor e x u ∣ z.2 then
          ‖markedBanEdgeKernel ψ Q Y (markedPhysicalActualEdgeSourceProduct e x u)
            (markedPhysicalActualEdgeTargetProduct e x u)
            (z.2/markedPhysicalActualEdgeCopiedDivisor e x u)‖ else 0) *
        (if ((((markedPhysicalCanonicalCompletion r).1 : ℝ)/
            ((markedPhysicalCanonicalRootPosition r).1 : ℝ)) : AddCircle (1 : ℝ)) ∈
          markedRawBadRootSet e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) then 1 else 0) := by
  let P := fun j => markedLogPowerBand (e j) x
  let hP := fun j p (hp : p ∈ P j) => (mem_markedLogPowerBand.mp hp).1
  have hsraw : (markedPhysicalStateToRaw P hP (markedPadSlots x) Z s).2.1 =
      markedPhysicalActualEdgeRawSource e x u := by
    change (markedPhysicalMarkingEquiv P hP (markedPadSlots x)).symm s.1.2 = _
    rw [hs]
    rfl
  have htraw : (markedPhysicalStateToRaw P hP (markedPadSlots x) Z t).2.1 =
      (markedPhysicalMarkingEquiv P hP (markedPadSlots x)).symm (markedPhysicalEdgeTarget u) := by
    change (markedPhysicalMarkingEquiv P hP (markedPadSlots x)).symm t.1.2 = _
    rw [ht]
  have hdet : markedMinorIntegerDet s.1.1.1 t.1.1.1 = z.2 := by
    rw [hspos, htpos]
    have hh := congrArg Prod.snd (Equiv.apply_symm_apply (markedPhysicalCanonicalTargetEquiv hA hC r) z)
    exact hh
  have hc : markedMinorIntegerDet s.1.1.1 (markedPhysicalCanonicalCompletion r) = 1 := by
    rw [hspos]
    exact markedPhysicalCanonicalCompletion_det hA hC r
  have hh := markedPhysical_source_bad_coefficient_norm_le e x d₀ Y Q V hV Z hZ w hw
    ψ η H F G hH hF hG hη f g hf hg s t (markedPhysicalCanonicalCompletion r) hc
  dsimp only at hh
  rw [hsraw, htraw, hdet, hspos, markedPhysicalActualEdgeTargetProduct_eq e x u] at hh
  exact hh

def markedPhysicalCanonicalBadWeight
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y Q : ℝ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    {A B C D : ℝ} (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D)
    (z : ℤ × ℤ) (ψ : SchwartzMap ℝ ℂ) : ℝ :=
  ‖markedBanEdgeKernel ψ Q Y (markedPhysicalActualEdgeSourceProduct e x u)
    (markedPhysicalActualEdgeTargetProduct e x u) (z.2/markedPhysicalActualEdgeCopiedDivisor e x u)‖ *
    (if |markedMinorIntegerTau (((markedPhysicalCanonicalCompletion r).1 : ℝ)/
        ((markedPhysicalCanonicalRootPosition r).1 : ℝ)) z| ≤ 16 then
      markedRawBadRootArcMajorant e x d₀ Y (markedPhysicalActualEdgeRawSource e x u)
        ((((markedPhysicalCanonicalCompletion r).1 : ℝ)/
          ((markedPhysicalCanonicalRootPosition r).1 : ℝ)) : AddCircle (1 : ℝ)) else 0)

set_option backward.isDefEq.respectTransparency false in
theorem markedPhysical_source_bad_position_norm_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z) = 1)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H F G R : ℝ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hG : 0 ≤ G) (hη : ∀ t, ‖η t‖ ≤ H)
    (hY : 0 < Y) (hsupp : ∀ v, ψ v ≠ 0 → |v| ≤ R)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ F) (hg : ∀ s, ‖g s‖ ≤ G)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    [NeZero (markedPhysicalMarkingProduct u)]
    {A B C D U : ℝ} (hA : 1 < A) (hC : 1 < C) (hU : 0 < U) (hUA : U ≤ A) (hBU : B ≤ 16*U)
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D)
    (z : ℤ × ℤ) (hz : z ∈ markedPhysicalCanonicalTargets hA hC r Z)
    (hcover : ∀ θ : AddCircle (1 : ℝ),
      (if θ ∈ markedRawBadRootSet e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) then (1 : ℝ) else 0) ≤
        markedRawBadRootArcMajorant e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) θ) :
    ‖markedPhysicalEdgePositionTerm (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V
      ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1
      (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f) g
      (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
      (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z)‖ ≤
      (markedPhysicalMass V (markedPadSlots x+1)*H^2*F*G) *
        (if z ∈ markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y then
          markedPhysicalCanonicalBadWeight e x d₀ Y Q u r z ψ else 0) := by
  let c := markedPhysicalMass V (markedPadSlots x+1)*H^2*F*G
  let θ : AddCircle (1 : ℝ) := (((markedPhysicalCanonicalCompletion r).1 : ℝ)/
    ((markedPhysicalCanonicalRootPosition r).1 : ℝ) : ℝ)
  let k := ‖markedBanEdgeKernel ψ Q Y (markedPhysicalActualEdgeSourceProduct e x u)
    (markedPhysicalActualEdgeTargetProduct e x u) (z.2/markedPhysicalActualEdgeCopiedDivisor e x u)‖
  let b : ℝ := if θ ∈ markedRawBadRootSet e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) then 1 else 0
  let m := markedRawBadRootArcMajorant e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) θ
  let I : ℝ := if markedPhysicalActualEdgeCopiedDivisor e x u ∣ z.2 then k else 0
  have hc0 : 0 ≤ c := by
    have hm := markedPhysicalMass_nonneg V (markedPadSlots x+1) hV
    dsimp only [c]
    positivity
  have hk0 : 0 ≤ k := norm_nonneg _
  have hb0 : 0 ≤ b := by dsimp only [b]; split_ifs <;> norm_num
  have hbm : b ≤ m := hcover θ
  have hm0 : 0 ≤ m := hb0.trans hbm
  have hs := markedPhysicalCanonicalTarget_strip hA hC hU hUA hBU r Z hbox z hz
  have hweight : markedPhysicalCanonicalBadWeight e x d₀ Y Q u r z ψ = k*m := by
    simp only [markedPhysicalCanonicalBadWeight, hs, ite_true]
    rfl
  generalize hT : (if z ∈ markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y then
    markedPhysicalCanonicalBadWeight e x d₀ Y Q u r z ψ else 0) = T
  have hT0 : 0 ≤ T := by
    rw [← hT]
    split_ifs
    · rw [hweight]
      exact mul_nonneg hk0 hm0
    · exact le_rfl
  have hct0 : 0 ≤ c*T := mul_nonneg hc0 hT0
  change _ ≤ c*T
  unfold markedPhysicalEdgePositionTerm markedPhysicalEdgePairTerm markedPhysicalStateExtend
  split_ifs with hsr htr hsp htp
  all_goals try simp only [norm_zero]
  all_goals try exact hct0
  let s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z :=
    ⟨(⟨markedPhysicalCanonicalRootPosition r,hsr⟩,markedPhysicalEdgeSource u),hsp⟩
  let t : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z :=
    ⟨(⟨(markedPhysicalCanonicalTargetEquiv hA hC r).symm z,htr⟩,markedPhysicalEdgeTarget u),htp⟩
  have hbase := markedPhysical_source_bad_canonical_norm_le e x d₀ Y Q V hV Z hZ w hw
    ψ η H F G hH hF hG hη f g hf hg u hA hC r z s t rfl rfl rfl rfl
  change _ ≤ c*I*b at hbase
  by_cases hzW : z ∈ markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y
  · rw [← hT, ite_eq_left hzW, hweight]
    apply hbase.trans
    have hIk : I ≤ k := by dsimp only [I]; split_ifs <;> first | exact le_rfl | exact hk0
    calc
      c*I*b = c*(I*b) := by ring
      _ ≤ c*(k*m) := mul_le_mul_of_nonneg_left (mul_le_mul hIk hbm hb0 hk0) hc0
  · rw [← hT, ite_eq_right hzW, mul_zero]
    have hI : I = 0 := by
      dsimp only [I]
      split_ifs with hd
      · have hk : markedBanEdgeKernel ψ Q Y (markedPhysicalActualEdgeSourceProduct e x u)
            (markedPhysicalActualEdgeTargetProduct e x u) (z.2/markedPhysicalActualEdgeCopiedDivisor e x u) = 0 := by
          by_contra hk
          exact hzW (markedPhysicalCanonicalTarget_window hA hC hU hUA hBU r Z hbox z hz
            _ _ _ R Q Y ψ hY hsupp hd hk)
        dsimp only [k]
        rw [hk, norm_zero]
      · rfl
    simpa only [hI, mul_zero, zero_mul] using hbase

end ArtinMatthews
