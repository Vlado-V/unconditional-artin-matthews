module

public import ArtinMatthews.MarkedPhysicalRootHaarMain
public import ArtinMatthews.MarkedPhysicalRootLineMass
public import ArtinMatthews.FixedURootMassShift
public import ArtinMatthews.MarkedPhysicalRootHaarBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The residue-class sum is performed inside the positive strip main
term. This retains the one-prime line charge while allowing the required
target line to vary with the actual integer target coordinate. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRootStripMain_nonneg {S : ℕ} (hS : Squarefree S)
    {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D) (α β : ℝ) (z : ℤ × ℤ) :
    0 ≤ markedPhysicalRootStripMain S A B α β C D z := by
  unfold markedPhysicalRootStripMain
  split_ifs with h
  · rw [div_eq_mul_inv]
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr h.2))
        (sub_nonneg.mpr hCD)
    · simpa only [one_div] using (fixedURoot_normalized_density_bounds hS).1
  · exact le_rfl

def markedPhysicalRootIncidenceMain {ι : Type*} (I : Finset ι)
    (S : ℕ) [NeZero S] (A B C D : ℝ) (α β c : ι → ℝ)
    (d b a : ℤ) (R Y Q : ℝ) (ψ : ℝ → ℂ)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop) : ℝ :=
  ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
    ∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
      if E g iz.2 then
        c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
          markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2
      else 0

theorem markedPhysicalRootIncidenceMain_le_count {ι : Type*} (I : Finset ι)
    {S : ℕ} [NeZero S] (hS : Squarefree S)
    (A B C D : ℝ) (hAB : A ≤ B) (hCD : C ≤ D) (α β c : ι → ℝ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (d b a : ℤ) (R Y Q : ℝ) (ψ : ℝ → ℂ)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop)
    (ℓ : (ℤ × ℤ) → MarkedRootLineTuple S)
    (hE : ∀ z ∈ markedPhysicalRootTargetWindow d R Y,
      ∀ g, E g z → markedRootKernelTuple hS g = ℓ z) :
    markedPhysicalRootIncidenceMain I S A B C D α β c d b a R Y Q ψ E ≤
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) *
        markedPhysicalRootLineMass S *
        markedPhysicalRootPositiveMain I S A B C D α β c d b a R Y Q ψ := by
  let w := fun iz : ι × (ℤ × ℤ) =>
    c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
      markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2
  have hw : ∀ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y), 0 ≤ w iz := by
    intro iz hiz
    exact mul_nonneg (mul_nonneg (hc iz.1 (Finset.mem_product.mp hiz).1) (norm_nonneg _))
      (markedPhysicalRootStripMain_nonneg hS hAB hCD _ _ _)
  have h := markedPhysicalRoot_forced_line_weighted_sum_le
    (I.product (markedPhysicalRootTargetWindow d R Y)) hS
    (fun g iz => E g iz.2) (fun iz => ℓ iz.2) w hw
    (fun iz hiz => hE iz.2 (Finset.mem_product.mp hiz).2)
  have hN : 0 < (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) := by
    exact_mod_cast (show 0 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) from Nat.card_pos)
  have hh := (div_le_iff₀ hN).mp h
  simpa only [markedPhysicalRootIncidenceMain, markedPhysicalRootPositiveMain,
    w, mul_ite, mul_one, mul_zero, mul_comm, mul_left_comm, mul_assoc] using hh

theorem markedPhysicalRoot_zeta_two_pos : 0 < (riemannZeta 2).re := by
  have hz : (riemannZeta 2).re = Real.pi^2/6 := by
    rw [riemannZeta_two, ← Complex.ofReal_pow]
    norm_num [pow_two, Complex.mul_re]
  rw [hz]
  positivity

theorem markedPhysicalRootIncidenceMain_le {ι : Type*} (I : Finset ι)
    {S : ℕ} [NeZero S] (hS : Squarefree S)
    (A B C D : ℝ) (hAB : A ≤ B) (hCD : C ≤ D) (α β c : ι → ℝ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (d b a : ℤ) {R Y Q W : ℝ} (ψ : ℝ → ℂ)
    (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ R)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop)
    (ℓ : (ℤ × ℤ) → MarkedRootLineTuple S)
    (hE : ∀ z ∈ markedPhysicalRootTargetWindow d R Y,
      ∀ g, E g z → markedRootKernelTuple hS g = ℓ z) :
    markedPhysicalRootIncidenceMain I S A B C D α β c d b a R Y Q ψ E ≤
      ((B-A)*(D-C)/(riemannZeta 2).re) * markedPhysicalRootLineMass S *
        ((33*W*(8*R+5))*Q^3) * ∫ r : ℝ, markedPhysicalIntervalMajorant I α β c r := by
  have hmass : 0 ≤ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) *
      markedPhysicalRootLineMass S := mul_nonneg (Nat.cast_nonneg _) (markedPhysicalRootLineMass_nonneg S)
  have hN : (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) ≠ 0 := by
    exact_mod_cast (show Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) ≠ 0 from Nat.card_pos.ne')
  apply (markedPhysicalRootIncidenceMain_le_count I hS A B C D hAB hCD α β c hc
    d b a R Y Q ψ E ℓ hE).trans
  apply (mul_le_mul_of_nonneg_left
    (markedPhysicalRootPositiveMain_le I hS A B C D hAB hCD α β c hc d b a ψ
      hQ hY hR hW hψ hsupp) hmass).trans_eq
  field_simp [hN, markedPhysicalRoot_zeta_two_pos.ne']

end ArtinMatthews
