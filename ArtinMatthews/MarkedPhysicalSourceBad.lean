module

public import ArtinMatthews.MarkedPhysicalActualLineMain
public import ArtinMatthews.MarkedMinorArcDirtyGoodCutoff
public import ArtinMatthews.MarkedPhysicalGoodPairing
public import ArtinMatthews.MarkedPhysicalCompletionGood
public import ArtinMatthews.MarkedPhysicalEdgeNorm
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! The literal physical first/second-bad source projection and its
pointwise coefficient bound at the canonical source ratio. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def MarkedPhysicalActualGood {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z) : Prop :=
  MarkedRawDirtyGood e x 0 d₀ Y w
    (markedPhysicalStateToRaw (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x) Z s)

theorem markedPhysicalActualGood_canonical_completion
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z)
    (completion : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1.1 (w s.1.1) = 1)
    (hc : markedMinorIntegerDet s.1.1.1 completion = 1) :
    MarkedPhysicalActualGood e x d₀ Y w s ↔
      (((completion.1 : ℝ)/(s.1.1.1.1 : ℝ)) : AddCircle (1 : ℝ)) ∉
        markedRawBadRootSet e x d₀ Y
          ((markedPhysicalStateToRaw (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x) Z s).2.1) :=
  markedRawDirtyGood_zero_canonical_completion e x d₀ Y w _ completion hw hc

theorem markedPhysicalActualEdgeTargetProduct_eq
    {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1)) :
    (markedRawLastProduct
      ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊)
        ((markedPhysicalMarkingEquiv (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x)).symm
            (markedPhysicalEdgeTarget u))).2 : ℤ) =
      markedPhysicalActualEdgeTargetProduct e x u := by
  let P := fun j => markedLogPowerBand (e j) x
  let hP := fun j p (hp : p ∈ P j) => (mem_markedLogPowerBand.mp hp).1
  let ar := (markedPhysicalMarkingEquiv P hP (markedPadSlots x)).symm (markedPhysicalEdgeTarget u)
  have hv (j : J) : ((ar j (Fin.last ⌊(Real.log x)^(1/100 : ℝ)⌋₊)).1 : ℕ) =
      (u j (Fin.last (markedPadSlots x)) : ℕ) := by
    have hh := markedPhysicalMarkingEquiv_apply P hP (markedPadSlots x) ar j
      (Fin.last ⌊(Real.log x)^(1/100 : ℝ)⌋₊)
    have hea : markedPhysicalMarkingEquiv P hP (markedPadSlots x) ar =
        markedPhysicalEdgeTarget u := Equiv.apply_symm_apply _ _
    rw [hea] at hh
    have he : ((ar j (Fin.last ⌊(Real.log x)^(1/100 : ℝ)⌋₊)).1 : ℕ) =
        (markedPhysicalEdgeTarget u j (Fin.last ⌊(Real.log x)^(1/100 : ℝ)⌋₊) : ℕ) := by
      exact hh.symm
    exact he.trans (congrArg Subtype.val (markedPhysicalEdgeTarget_last u j))
  have hp : markedRawLastProduct ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) ar).2 =
      ∏ j, (u j (Fin.last (markedPadSlots x)) : ℕ) := by
    unfold markedRawLastProduct
    apply Finset.prod_congr rfl
    intro j _
    exact hv j
  exact congrArg (fun n : ℕ => (n : ℤ)) hp

theorem markedPhysical_source_bad_coefficient_norm_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z) = 1)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H F G : ℝ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (_hG : 0 ≤ G) (hη : ∀ t, ‖η t‖ ≤ H)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ F) (hg : ∀ s, ‖g s‖ ≤ G)
    (s t : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z)
    (completion : ℤ × ℤ) (hc : markedMinorIntegerDet s.1.1.1 completion = 1) :
    let P := fun j => markedLogPowerBand (e j) x
    let hP := fun j p (hp : p ∈ P j) => (mem_markedLogPowerBand.mp hp).1
    let sr := markedPhysicalStateToRaw P hP (markedPadSlots x) Z s
    let tr := markedPhysicalStateToRaw P hP (markedPadSlots x) Z t
    let n := ⌊(Real.log x)^(1/100 : ℝ)⌋₊
    let b := ((markedRawActiveSplit n) sr.2.1).2
    let a := ((markedRawActiveSplit n) tr.2.1).2
    let D := markedRawCopiedProduct ((markedRawActiveSplit n) sr.2.1).1
    ‖markedPhysicalEdgeCoefficient P hP V n Z hZ ψ η d₀ Y Q 1 s t *
      star (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f s) * g t‖ ≤
      markedPhysicalMass V (markedPadSlots x+1) * H^2 * F * G *
        (if (D : ℤ) ∣ markedMinorIntegerDet s.1.1.1 t.1.1.1 then
          ‖markedBanEdgeKernel ψ Q Y (markedRawLastProduct b) (markedRawLastProduct a)
            (markedMinorIntegerDet s.1.1.1 t.1.1.1/(D : ℤ))‖ else 0) *
        (if (((completion.1 : ℝ)/(s.1.1.1.1 : ℝ)) : AddCircle (1 : ℝ)) ∈
          markedRawBadRootSet e x d₀ Y sr.2.1 then 1 else 0) := by
  dsimp only
  have hgood := markedPhysicalActualGood_canonical_completion e x d₀ Y w s completion (hw s.1.1) hc
  by_cases hb : (((completion.1 : ℝ)/(s.1.1.1.1 : ℝ)) : AddCircle (1 : ℝ)) ∈
      markedRawBadRootSet e x d₀ Y
        (markedPhysicalStateToRaw (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x) Z s).2.1
  · have hng : ¬MarkedPhysicalActualGood e x d₀ Y w s := fun hs => (hgood.mp hs) hb
    simp only [ite_eq_left hb, mul_one, markedPhysicalBadVector, ite_eq_right hng, norm_mul, norm_star]
    have hcoef := markedPhysicalEdgeCoefficient_one_norm_le
      (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      V hV ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η H hH hη d₀ Y Q s t
    have hmass : markedPhysicalMass V (⌊(Real.log x)^(1/100 : ℝ)⌋₊+2) =
        markedPhysicalMass V (markedPadSlots x+1) := rfl
    dsimp only at hcoef
    rw [hmass] at hcoef
    have hσ := markedPhysicalMass_nonneg V (markedPadSlots x+1) hV
    let sr := markedPhysicalStateToRaw (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x) Z s
    let tr := markedPhysicalStateToRaw (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x) Z t
    let K : ℝ := if (markedRawCopiedProduct ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) sr.2.1).1 : ℤ) ∣
        markedMinorIntegerDet s.1.1.1 t.1.1.1 then
      ‖markedBanEdgeKernel ψ Q Y
        (markedRawLastProduct ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) sr.2.1).2)
        (markedRawLastProduct ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) tr.2.1).2)
        (markedMinorIntegerDet s.1.1.1 t.1.1.1/
          (markedRawCopiedProduct ((markedRawActiveSplit ⌊(Real.log x)^(1/100 : ℝ)⌋₊) sr.2.1).1 : ℤ))‖ else 0
    have hK : 0 ≤ K := by dsimp only [K]; split_ifs <;> positivity
    change ‖markedPhysicalEdgeCoefficient _ _ V _ Z hZ ψ η d₀ Y Q 1 s t‖ ≤
      markedPhysicalMass V (markedPadSlots x+1)*H^2*K at hcoef
    change ‖markedPhysicalEdgeCoefficient _ _ V _ Z hZ ψ η d₀ Y Q 1 s t‖ * ‖f s‖ * ‖g t‖ ≤
      markedPhysicalMass V (markedPadSlots x+1)*H^2*F*G*K
    apply (mul_le_mul
      (mul_le_mul hcoef (hf s) (norm_nonneg _) (by positivity)) (hg t)
      (norm_nonneg _) (by positivity)).trans_eq
    ring
  · have hgs : MarkedPhysicalActualGood e x d₀ Y w s := hgood.mpr hb
    simp only [ite_eq_right hb, mul_zero, markedPhysicalBadVector, ite_eq_left hgs,
      star_zero, mul_zero, zero_mul, norm_zero, le_refl]

end ArtinMatthews
