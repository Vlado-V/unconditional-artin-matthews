module

public import ArtinMatthews.MarkedPhysicalBadRootReplacement
public import ArtinMatthews.FixedURootMassShift
public import ArtinMatthews.MarkedPhysicalBadRootMain
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

/-! A complete scalar estimate for the actual positive one-edge bad-root
sum. Both the Haar main term and the arithmetic replacement error are
proved here; no small projection or unproved row estimate is assumed. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRoot_normalized_area_le {U V A B C D : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hUA : U ≤ A) (_hAB : A ≤ B) (hB : B ≤ 16*U)
    (hVC : V ≤ C) (hCD : C ≤ D) (hD : D ≤ 2*V) :
    (B-A)*(D-C)/(U*V) ≤ 16 := by
  apply (div_le_iff₀ (mul_pos hU hV)).mpr
  have hm := mul_le_mul (show B-A ≤ 16*U by linarith)
    (show D-C ≤ V by linarith) (sub_nonneg.mpr hCD) (by positivity : 0 ≤ 16*U)
  nlinarith

theorem markedPhysicalBadRootKernelSum_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (β H R T : ℝ) (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β)
    (hβhi : β+(1/100 : ℝ) < 1) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (o : J → Fin (markedPadSlots x)) (d₀ Y Q : ℝ)
        (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D W : ℝ) (b a : ℤ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
        0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) → (∀ u, ψ u ≠ 0 → |u| ≤ R) →
        markedPhysicalBadRootKernelSum e x source d₀ Y g₀ A B C D
          (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ / (U*V) ≤
          (16/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) +
            (5*E*W)*x^(-δ/2000) := by
  obtain ⟨E,hE,hcount⟩ := markedPhysicalBadRootKernel_power_saving e he β H R
    hβ heβ hβhi hH hR hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, markedPhysicalBadRootKernelMain_log_saving e he hinj T,
    eventually_gt_atTop (1 : ℝ)] with x hx hmain hx1
  intro source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYhi hYlo hW hψ hsupp
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have herr := hx source o d₀ Y Q S g₀ U V A B C D W b a ψ hU hV hS hSr
    hUA hAB hB hVC hCD hD hQ hQhi hY hYlo hYhi hW hψ
  have hm := hmain d₀ Y hYlo source S hS A B C D hAB hCD
    (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q W ψ
    hQ hY hR hW hψ hsupp
  have hden : 0 ≤ 1/((riemannZeta 2).re*
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) :=
    (fixedURoot_normalized_density_bounds hS).1
  have harea := markedPhysicalRoot_normalized_area_le hUp hVp hUA hAB hB hVC hCD hD
  have hscale : 0 ≤ ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
    have hlog : 0 ≤ Real.log x := (Real.log_pos hx1).le
    positivity
  have hmnorm : markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D
      (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ / (U*V) ≤
      (16/((riemannZeta 2).re*
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
        ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
    apply (div_le_div_of_nonneg_right hm (mul_pos hUp hVp).le).trans
    calc
      _ = ((B-A)*(D-C)/(U*V)) *
          (1/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
          (((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T)) := by ring
      _ ≤ 16 * (1/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
          (((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right harea hden) hscale
      _ = _ := by ring
  calc
    _ = (markedPhysicalBadRootKernelSum e x source d₀ Y g₀ A B C D
        (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ -
        markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D
        (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ)/(U*V) +
        markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D
        (markedSourceCopiedProduct (markedRawNumericActive source) o) b a R Q ψ/(U*V) := by ring
    _ ≤ (5*E*W)*x^(-δ/2000) +
        (16/((riemannZeta 2).re*
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
          ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) :=
      add_le_add ((le_abs_self _).trans herr) hmnorm
    _ = _ := by ring

end ArtinMatthews
