module

public import ArtinMatthews.MarkedPhysicalRootHaarMain
public import ArtinMatthews.FixedURootMassShift
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Integrating the actual target row against a positive bad-root cover.
The estimate uses the cover mass, not its pointwise size or a projection
norm. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRootMain_integrand_eq {ι : Type*} (I : Finset ι)
    (α β c : ι → ℝ) (d b a : ℤ) (R Y Q : ℝ) (ψ : ℝ → ℂ) (r : ℝ) :
    (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
      c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
        markedPhysicalStripArcIndicator iz.2 (α iz.1) (β iz.1) r) =
      markedPhysicalIntervalMajorant I α β c r *
        ∑ z ∈ (markedPhysicalRootTargetWindow d R Y).filter
          (fun z => |markedMinorIntegerTau r z| ≤ 16),
          ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ := by
  rw [Finset.product_eq_sprod, Finset.sum_product]
  unfold markedPhysicalIntervalMajorant
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hi : r ∈ Set.Icc (α i) (β i) <;>
    by_cases hz : |markedMinorIntegerTau r z| ≤ 16 <;>
    simp [markedPhysicalStripArcIndicator, hi, hz]

theorem markedPhysicalRootPositiveMain_le {ι : Type*} (I : Finset ι)
    {S : ℕ} (hS : Squarefree S) (A B C D : ℝ) (hAB : A ≤ B) (hCD : C ≤ D)
    (α β c : ι → ℝ) (hc : ∀ i ∈ I, 0 ≤ c i)
    (d b a : ℤ) {R Y Q W : ℝ} (ψ : ℝ → ℂ)
    (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ R) :
    markedPhysicalRootPositiveMain I S A B C D α β c d b a R Y Q ψ ≤
      ((B-A)*(D-C)/((riemannZeta 2).re*
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
      ((33*W*(8*R+5))*Q^3) * ∫ r : ℝ, markedPhysicalIntervalMajorant I α β c r := by
  have hd : 0 ≤ (B-A)*(D-C)/((riemannZeta 2).re*
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hCD))
      (by simpa only [one_div] using (fixedURoot_normalized_density_bounds hS).1)
  have hM (r : ℝ) : 0 ≤ markedPhysicalIntervalMajorant I α β c r := by
    unfold markedPhysicalIntervalMajorant
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact hc i hi
    · exact le_rfl
  have hpoint (r : ℝ) := markedPhysicalRootTargetWindow_kernel_bound d b a r ψ
    hQ hY hR hW hψ hsupp (fun _ => (1 : ℂ)) (by intro z _; simp)
  simp only [one_mul] at hpoint
  have hi := integral_mono
    (integrable_finsetSum (I.product (markedPhysicalRootTargetWindow d R Y)) (fun iz _ =>
      (markedPhysicalStripArcIndicator_integrable iz.2 (α iz.1) (β iz.1)).const_mul
        (c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖)))
    ((markedPhysicalIntervalMajorant_integrable I α β c).mul_const ((33*W*(8*R+5))*Q^3))
    (fun r => by
      rw [markedPhysicalRootMain_integrand_eq]
      exact mul_le_mul_of_nonneg_left (hpoint r) (hM r))
  rw [integral_mul_const] at hi
  rw [markedPhysicalRootPositiveMain_integral]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hi hd
    _ = _ := by ring

theorem markedPhysicalIntervalMajorant_integral_eq_haar {ι : Type*} (I : Finset ι)
    (α β c : ι → ℝ) (hα : ∀ i ∈ I, 0 ≤ α i) (hβ : ∀ i ∈ I, β i ≤ 1)
    (F : AddCircle (1 : ℝ) → ℝ)
    (hF : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      markedPhysicalIntervalMajorant I α β c r = F (r : AddCircle (1 : ℝ))) :
    (∫ r : ℝ, markedPhysicalIntervalMajorant I α β c r) = ∫ θ, F θ := by
  have hz (r : ℝ) (hr : r ∉ Set.Icc (0 : ℝ) 1) :
      markedPhysicalIntervalMajorant I α β c r = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hri : r ∉ Set.Icc (α i) (β i) := by
      intro hm
      exact hr ⟨(hα i hi).trans hm.1, hm.2.trans (hβ i hi)⟩
    exact ite_eq_right hri
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ = ∫ r in Set.Icc (0 : ℝ) 1, F (r : AddCircle (1 : ℝ)) := by
      exact setIntegral_congr_fun measurableSet_Icc hF
    _ = ∫ r in Set.Ioc (0 : ℝ) 1, F (r : AddCircle (1 : ℝ)) := integral_Icc_eq_integral_Ioc
    _ = _ := by simpa only [zero_add] using AddCircle.integral_preimage (1 : ℝ) 0 F

end ArtinMatthews
