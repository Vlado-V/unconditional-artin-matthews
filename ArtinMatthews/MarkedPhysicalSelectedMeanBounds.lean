module

public import ArtinMatthews.MarkedPhysicalCoordinateRootPolynomial
public import ArtinMatthews.MarkedPhysicalPathBonferroni
public import ArtinMatthews.MarkedPhysicalResidueMonomialBounds
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

/-! Positivity and domination of the actual guarded selected means.
These retain the original residue scalar and compare it to the genuine
unguarded Bonferroni tail mean, rather than estimating a signed sum. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalSelectedGuardedMonomialMean_bounds
    {J : Type*} [Fintype J] {P : J → Finset ℕ} {M N : ℕ}
    (hP : ∀ j p,p ∈ P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (r : Fin (N+1) → ℝ)
    (hr : ∀ v,0 ≤ r v ∧ r v ≤ 1)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (T : Finset ℕ) (hT : T ⊆ markedPhysicalBandPrimes P) :
    0 ≤ markedPhysicalSelectedGuardedMonomialMean hP a r z hz T hT ∧
      markedPhysicalSelectedGuardedMonomialMean hP a r z hz T hT ≤
        markedPhysicalSelectedMonomialMean hP Finset.univ a r z hz T := by
  let S := markedPhysicalBonferroniModulus Finset.univ a T
  let : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos hP Finset.univ a hT).ne'⟩
  have hm (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :=
    (markedPhysicalResidueBonferroniMonomial_mem_unitInterval
      (markedPhysicalBonferroniModulus_squarefree hP Finset.univ a hT) g
      Finset.univ a r (fun v _ => hr v) z hz T).1
  unfold markedPhysicalSelectedGuardedMonomialMean markedPhysicalSelectedMonomialMean
  rw [dite_eq_left hT]
  dsimp only
  constructor
  · apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro g _
    split_ifs
    · exact hm g
    · exact le_rfl
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro g _
    split_ifs
    · exact le_rfl
    · exact hm g

theorem markedPhysicalCoordinateSelectedAverage_norm_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q : ℝ) {R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) R) (hR : 1 ≤ R)
    (q U Vr : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hUV : 0 ≤ U*Vr)
    (T : Finset ℕ) (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x)) :
    ‖markedPhysicalCoordinateSelectedAverage e x V ψ η d₀ Y Q i hR q U Vr T‖ ≤
      (U*Vr/(riemannZeta 2).re)*
        (‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
          V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖*
          markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR*
          markedPhysicalSelectedMonomialMean (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            Finset.univ i.1 (markedMemoryVisitQ q (markedMemoryMomentLength x))
            (markedPhysicalCoordinateIndexPath i.2.1)
            (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) T) := by
  let C := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  let v := markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR
  let a := markedPhysicalSelectedGuardedMonomialMean
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i.1
    (markedMemoryVisitQ q (markedMemoryMomentLength x))
    (markedPhysicalCoordinateIndexPath i.2.1)
    (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) T hT
  let b := markedPhysicalSelectedMonomialMean (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    Finset.univ i.1 (markedMemoryVisitQ q (markedMemoryMomentLength x))
    (markedPhysicalCoordinateIndexPath i.2.1)
    (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) T
  have hab : 0 ≤ a ∧ a ≤ b := markedPhysicalSelectedGuardedMonomialMean_bounds _ i.1 _
    (fun v => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 _ v) _ _ T hT
  have hv : 0 ≤ v := (markedPhysicalCoordinateIndexGoodVolume_bounds e x d₀ Y U Vr i hR).1
  have hd : 0 ≤ U*Vr/(riemannZeta 2).re := div_nonneg hUV markedRoot_zeta_two_pos.le
  rw [markedPhysicalCoordinateSelectedAverage_eq]
  change ‖(U*Vr/(riemannZeta 2).re) • (v • ((a:ℂ)*C))‖ ≤
    (U*Vr/(riemannZeta 2).re)*(‖C‖*v*b)
  calc
    _ = (U*Vr/(riemannZeta 2).re)*(‖C‖*v*a) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,abs_of_nonneg hv,
        norm_mul,Complex.norm_real,abs_of_nonneg hab.1]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hab.2 (mul_nonneg (norm_nonneg C) hv)) hd

end
end ArtinMatthews
