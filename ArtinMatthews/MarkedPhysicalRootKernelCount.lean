module

public import ArtinMatthews.MarkedPhysicalRootStripCount
public import ArtinMatthews.MarkedPhysicalRootTargetWindow
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

/-! Weighted replacement of the literal strip-root counts. The target
window, raw-minus-major kernel and finite interval coefficient mass remain
explicit. No estimate on a physical pairing is assumed. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedBanEdgeKernel_norm_le_five (ψ : ℝ → ℂ) {Q Y W : ℝ}
    (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hW : 0 ≤ W) (hψ : ∀ u, ‖ψ u‖ ≤ W)
    (b a l : ℤ) : ‖markedBanEdgeKernel ψ Q Y b a l‖ ≤ 5*W*Q^3 := by
  have hq₀ : 0 ≤ Q := zero_le_one.trans hQ
  have hy₀ : 0 < Y := zero_lt_one.trans_le hY
  have hq3 : 1 ≤ Q^3 := one_le_pow₀ hQ
  have hi : (if l=b-a then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hdiv : 4*Q^3/Y ≤ 4*Q^3 := (div_le_self (by positivity) hY)
  calc
    _ ≤ W*((if l=b-a then (1:ℝ) else 0)+4*Q^3/Y) :=
      markedBanEdgeKernel_norm_le ψ hq₀ hy₀ hW hψ b a l
    _ ≤ W*(Q^3+4*Q^3) :=
      mul_le_mul_of_nonneg_left (add_le_add (hi.trans hq3) hdiv) hW
    _ = _ := by ring

def markedPhysicalRootKernelDiscrepancy {ι : Type*} (I : Finset ι)
    {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V A B C D : ℝ) (α β : ι → ℝ) (c : ι → ℂ)
    (d b a : ℤ) (R Y Q : ℝ) (ψ : ℝ → ℂ) (test : (ℤ × ℤ) → ℂ) : ℂ :=
  (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
    c iz.1 * test iz.2 * markedBanEdgeKernel ψ Q Y b a (iz.2.2/d) *
      (((markedPhysicalRootStripPoints g₀ A B (α iz.1) (β iz.1) C D iz.2).card : ℂ) -
        (markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2 : ℂ))) /
    (U*V : ℝ)

theorem markedPhysicalRootKernelDiscrepancy_bound {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type*} (I : Finset ι) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D : ℝ) (α β : ι → ℝ) (c : ι → ℂ)
        (d b a : ℤ) (R Y Q W : ℝ) (ψ : ℝ → ℂ) (test : (ℤ × ℤ) → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        (∀ i ∈ I, 0 ≤ α i ∧ β i ≤ 1) →
        1 ≤ Q → 1 ≤ Y → 0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) →
        (∀ z ∈ markedPhysicalRootTargetWindow d R Y, ‖test z‖ ≤ 1) →
        ‖markedPhysicalRootKernelDiscrepancy I g₀ U V A B C D α β c d b a R Y Q ψ test‖ ≤
          (5*E*W)*x^(-δ/1000)*Q^3*
            ((markedPhysicalRootTargetWindow d R Y).card : ℝ)*(∑ i ∈ I, ‖c i‖) := by
  obtain ⟨E,hE,hcount⟩ := markedPhysicalRootStrip_sum_error hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro ι I S g₀ U V A B C D α β c d b a R Y Q W ψ test hU hV hS hSr
    hUA hAB hB hVC hCD hD hα hQ hY hW hψ htest
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hh := hx (I.product (markedPhysicalRootTargetWindow d R Y)) S g₀ U V A B C D
    (fun iz => α iz.1) (fun iz => β iz.1) Prod.snd
    (fun iz => c iz.1*test iz.2*markedBanEdgeKernel ψ Q Y b a (iz.2.2/d))
    hU hV hS hSr hUA hAB hB hVC hCD hD
    (fun iz hiz => hα iz.1 (Finset.mem_product.mp hiz).1)
  have hcoeff : (∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
      ‖c iz.1*test iz.2*markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖) ≤
      5*W*Q^3*((markedPhysicalRootTargetWindow d R Y).card : ℝ)*(∑ i ∈ I, ‖c i‖) := by
    calc
      _ ≤ ∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y), ‖c iz.1‖*(5*W*Q^3) := by
        apply Finset.sum_le_sum
        intro iz hiz
        rw [norm_mul, norm_mul]
        calc
          _ ≤ (‖c iz.1‖*1)*(5*W*Q^3) := mul_le_mul
            (mul_le_mul_of_nonneg_left (htest iz.2 (Finset.mem_product.mp hiz).2) (norm_nonneg _))
            (markedBanEdgeKernel_norm_le_five ψ hQ hY hW hψ b a _) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ = _ := by
        rw [Finset.product_eq_sprod, Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have hnonneg : 0 ≤ E*x^(-δ/1000) := by positivity
  unfold markedPhysicalRootKernelDiscrepancy
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hUp hVp)]
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left hcoeff hnonneg).trans_eq
  ring

end ArtinMatthews
