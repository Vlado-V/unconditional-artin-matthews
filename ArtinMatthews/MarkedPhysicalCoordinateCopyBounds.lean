module

public import ArtinMatthews.MarkedPhysicalCoordinateCopies
public import ArtinMatthews.MarkedPhysicalCoordinateNorm
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

/-! Actual coordinate-copy product budgets. Slot-average coefficients
are retained and bounded by one; no path-length factor is hidden. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalCoordinateEdgeBound {J : Type*} [Fintype J] (V : J → ℝ) (H W : ℝ) : ℝ :=
  5*|∏ j,(V j)⁻¹| * H^2*W

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ))
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q H W : ℝ)

theorem markedPhysicalCoordinateCopy_norm_le (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (j : ℕ) (s t : MarkedPhysicalState P (pads+1) Z)
    (c : (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1)))) (z z' : ℤ × ℤ) :
    ‖markedPhysicalCoordinateCopy P hP V pads Z ψ η d₀ Y Q j s t c z z'‖ ≤
      markedPhysicalCoordinateEdgeBound V H W*Q^3 := by
  have hcard : 1 ≤ (Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℝ) := by
    exact_mod_cast (show 1 ≤ Fintype.card (J → Equiv.Perm (Fin (pads+1))) from Fintype.card_pos)
  have hc : ‖((Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)⁻¹)^2‖ ≤ 1 := by
    rw [norm_pow,norm_inv]
    have hn : ‖(Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)‖ =
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℝ) := by simp
    rw [hn]
    exact pow_le_one₀ (inv_nonneg.mpr (zero_le_one.trans hcard)) (inv_le_one_of_one_le₀ hcard)
  have hb : 1+4*Q^3/Y ≤ 5*Q^3 := by
    have hh : 4*Q^3/Y ≤ 4*Q^3 := div_le_self (by positivity) hY
    nlinarith [show (1:ℝ) ≤ Q^3 from one_le_pow₀ hQ]
  have hk (f : SchwartzMap ℝ ℂ) (g : ℝ → ℂ)
      (hf : ∀ u,‖f u‖ ≤ W) (hg : ∀ u,‖g u‖ ≤ H) :
      ‖markedPhysicalCoordinateKernel V pads f g d₀ Y Q
        (markedPhysicalStateToRaw P hP (pads+1) Z (markedPhysicalSlotEquiv P (pads+1) Z c.1 s)).2.1
        (markedPhysicalStateToRaw P hP (pads+1) Z (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)).2.1 z z'‖ ≤
        markedPhysicalCoordinateEdgeBound V H W*Q^3 := by
    apply (markedPhysicalCoordinateKernel_norm_le V pads f g d₀ Y Q H W
      (lt_of_lt_of_le zero_lt_one hY) (zero_le_one.trans hQ) hH hW hg hf _ _ z z').trans
    calc
      _ ≤ |∏ k,(V k)⁻¹| * H^2*W*(5*Q^3) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by unfold markedPhysicalCoordinateEdgeBound; ring
  unfold markedPhysicalCoordinateCopy
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
  split_ifs
  · exact hk ψ η hψ hη
  · exact hk (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
      (fun u => by simpa only [markedRawEdgeAdjointCutoff_apply,norm_star] using hψ (-u))
      (fun u => by simpa only [norm_star] using hη u)

def markedPhysicalCoordinatePathKernel (n : ℕ)
    (path : Fin (n+1) → MarkedPhysicalState P (pads+1) Z)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z : Fin (n+1) → ℤ × ℤ) : ℂ :=
  ∏ v : Fin n,markedPhysicalCoordinateCopy P hP V pads Z ψ η d₀ Y Q v.val
    (path v.castSucc) (path v.succ) (copies v) (z v.castSucc) (z v.succ)

theorem markedPhysicalCoordinatePathKernel_norm_le (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (n : ℕ) (path : Fin (n+1) → MarkedPhysicalState P (pads+1) Z)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z : Fin (n+1) → ℤ × ℤ) :
    ‖markedPhysicalCoordinatePathKernel P hP V pads Z ψ η d₀ Y Q n path copies z‖ ≤
      (markedPhysicalCoordinateEdgeBound V H W*Q^3)^n := by
  rw [markedPhysicalCoordinatePathKernel,norm_prod]
  calc
    _ ≤ ∏ _v : Fin n,markedPhysicalCoordinateEdgeBound V H W*Q^3 :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ =>
        markedPhysicalCoordinateCopy_norm_le P hP V pads Z ψ η d₀ Y Q H W hY hQ hH hW hη hψ _ _ _ _ _ _)
    _ = _ := by simp

end ArtinMatthews
