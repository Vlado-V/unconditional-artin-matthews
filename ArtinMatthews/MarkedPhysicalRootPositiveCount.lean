module

public import ArtinMatthews.MarkedPhysicalRootStripCount
public import ArtinMatthews.MarkedPhysicalRootTargetWindow
public import ArtinMatthews.MarkedPhysicalRootKernelCount
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

/-! The positive absolute-kernel version of the actual strip replacement.
It retains the real interval coefficients and the exact root main term. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def markedPhysicalRootPositiveDiscrepancy {ι : Type*} (I : Finset ι)
    {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V A B C D : ℝ) (α β c : ι → ℝ)
    (d b a : ℤ) (R Y Q : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
    c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
      (((markedPhysicalRootStripPoints g₀ A B (α iz.1) (β iz.1) C D iz.2).card : ℝ) -
        markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2)) / (U*V)

theorem markedPhysicalRootPositiveDiscrepancy_bound {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type*} (I : Finset ι) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D : ℝ) (α β c : ι → ℝ)
        (d b a : ℤ) (R Y Q W : ℝ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        (∀ i ∈ I, 0 ≤ α i ∧ β i ≤ 1) →
        1 ≤ Q → 1 ≤ Y → 0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) →
        |markedPhysicalRootPositiveDiscrepancy I g₀ U V A B C D α β c d b a R Y Q ψ| ≤
          (5*E*W)*x^(-δ/1000)*Q^3*
            ((markedPhysicalRootTargetWindow d R Y).card : ℝ)*(∑ i ∈ I, |c i|) := by
  obtain ⟨E,hE,hcount⟩ := markedPhysicalRootStrip_sum_error hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro ι I S g₀ U V A B C D α β c d b a R Y Q W ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hα hQ hY hW hψ
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hh := hx (I.product (markedPhysicalRootTargetWindow d R Y)) S g₀ U V A B C D
    (fun iz => α iz.1) (fun iz => β iz.1) Prod.snd
    (fun iz => ((c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ : ℝ) : ℂ))
    hU hV hS hSr hUA hAB hB hVC hCD hD
    (fun iz hiz => hα iz.1 (Finset.mem_product.mp hiz).1)
  have hcoeff : (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
      ‖((c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ : ℝ) : ℂ)‖) ≤
      5*W*Q^3*((markedPhysicalRootTargetWindow d R Y).card : ℝ)*(∑ i ∈ I, |c i|) := by
    calc
      _ ≤ ∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y), |c iz.1| * (5*W*Q^3) := by
        apply Finset.sum_le_sum
        intro iz _
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_left (markedBanEdgeKernel_norm_le_five ψ hQ hY hW hψ b a _)
          (abs_nonneg _)
      _ = _ := by
        rw [Finset.product_eq_sprod, Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have heq : (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
      ((c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ : ℝ) : ℂ) *
        (((markedPhysicalRootStripPoints g₀ A B (α iz.1) (β iz.1) C D iz.2).card : ℂ) -
          (markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2 : ℂ))) =
      ((∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
        c iz.1*‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
          (((markedPhysicalRootStripPoints g₀ A B (α iz.1) (β iz.1) C D iz.2).card : ℝ) -
            markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2)) : ℝ) := by
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_eq_abs] at hh
  unfold markedPhysicalRootPositiveDiscrepancy
  rw [abs_div, abs_of_pos (mul_pos hUp hVp)]
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left hcoeff (by positivity : 0 ≤ E*x^(-δ/1000))).trans_eq
  ring

end ArtinMatthews
