module

public import ArtinMatthews.MarkedPhysicalCoordinateIndex
public import ArtinMatthews.MarkedPhysicalCoordinateLabelCopies
public import ArtinMatthews.MarkedPhysicalCoordinateCopyBounds
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

/-! The literal complex coefficient on the full finite relative-path
carrier. Its norm bound holds even for labels that admit no physical
lift; all original slot-average factors remain in the coefficient. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalCoordinateIndexPath {n B : ℕ}
    (tail : Fin n → ↥(markedPrimitiveCoordinateTube B)) : Fin (n+1) → ℤ × ℤ :=
  Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) (1,0) (fun v => (tail v).1)

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (pads : ℕ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

def markedPhysicalCoordinateLabelKernel (n : ℕ)
    (a : MarkedPhysicalLabelPath P (pads+1) n) (z : Fin (n+1) → ℤ × ℤ)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1)))) : ℂ :=
  ∏ v : Fin n,markedPhysicalCoordinateLabelCopy P hP V pads ψ η d₀ Y Q v.val
    (a v.castSucc) (a v.succ) (copies v) (z v.castSucc) (z v.succ)

def markedPhysicalCoordinateIndexCoefficient {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n B) : ℂ :=
  markedPhysicalCoordinateLabelKernel P hP V pads ψ η d₀ Y Q n i.1
    (markedPhysicalCoordinateIndexPath i.2.1) i.2.2

theorem markedPhysicalCoordinateLabelCopy_norm_le (H W : ℝ)
    (hY : 1≤Y) (hQ : 1≤Q) (hH : 0≤H) (hW : 0≤W)
    (hη : ∀ t,‖η t‖≤H) (hψ : ∀ t,‖ψ t‖≤W)
    (j : ℕ) (a b : MarkedPhysicalMarking P (pads+1))
    (c : (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z z' : ℤ × ℤ) :
    ‖markedPhysicalCoordinateLabelCopy P hP V pads ψ η d₀ Y Q j a b c z z'‖≤
      markedPhysicalCoordinateEdgeBound V H W*Q^3 := by
  have hcard : 1≤(Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℝ) := by
    exact_mod_cast (show 1≤Fintype.card (J → Equiv.Perm (Fin (pads+1))) from Fintype.card_pos)
  have hc : ‖((Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)⁻¹)^2‖≤1 := by
    rw [norm_pow,norm_inv]
    have hn : ‖(Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)‖=
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℝ) := by simp
    rw [hn]
    exact pow_le_one₀ (inv_nonneg.mpr (zero_le_one.trans hcard)) (inv_le_one_of_one_le₀ hcard)
  have hb : 1+4*Q^3/Y≤5*Q^3 := by
    have hh : 4*Q^3/Y≤4*Q^3 := div_le_self (by positivity) hY
    nlinarith [show (1:ℝ)≤Q^3 from one_le_pow₀ hQ]
  have hk (f : SchwartzMap ℝ ℂ) (g : ℝ → ℂ)
      (hf : ∀ t,‖f t‖≤W) (hg : ∀ t,‖g t‖≤H) :
      ‖markedPhysicalCoordinateKernel V pads f g d₀ Y Q
        ((markedPhysicalMarkingEquiv P hP (pads+1)).symm (fun i k => a i (c.1 i k)))
        ((markedPhysicalMarkingEquiv P hP (pads+1)).symm (fun i k => b i (c.2 i k))) z z'‖≤
        markedPhysicalCoordinateEdgeBound V H W*Q^3 := by
    apply (markedPhysicalCoordinateKernel_norm_le V pads f g d₀ Y Q H W
      (lt_of_lt_of_le zero_lt_one hY) (zero_le_one.trans hQ) hH hW hg hf _ _ z z').trans
    calc
      _ ≤ |∏ k,(V k)⁻¹| * H^2*W*(5*Q^3) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by unfold markedPhysicalCoordinateEdgeBound; ring
  unfold markedPhysicalCoordinateLabelCopy
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
  split_ifs
  · exact hk ψ η hψ hη
  · exact hk (markedRawEdgeAdjointCutoff ψ) (fun t => star (η t))
      (fun t => by simpa only [markedRawEdgeAdjointCutoff_apply,norm_star] using hψ (-t))
      (fun t => by simpa only [norm_star] using hη t)

theorem markedPhysicalCoordinateLabelKernel_norm_le (H W : ℝ)
    (hY : 1≤Y) (hQ : 1≤Q) (hH : 0≤H) (hW : 0≤W)
    (hη : ∀ t,‖η t‖≤H) (hψ : ∀ t,‖ψ t‖≤W)
    (n : ℕ) (a : MarkedPhysicalLabelPath P (pads+1) n) (z : Fin (n+1) → ℤ × ℤ)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1)))) :
    ‖markedPhysicalCoordinateLabelKernel P hP V pads ψ η d₀ Y Q n a z copies‖≤
      (markedPhysicalCoordinateEdgeBound V H W*Q^3)^n := by
  rw [markedPhysicalCoordinateLabelKernel,norm_prod]
  calc
    _ ≤ ∏ _v : Fin n,markedPhysicalCoordinateEdgeBound V H W*Q^3 :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ =>
        markedPhysicalCoordinateLabelCopy_norm_le P hP V pads ψ η d₀ Y Q H W
          hY hQ hH hW hη hψ _ _ _ _ _ _)
    _ = _ := by simp

theorem markedPhysicalCoordinateIndexCoefficient_norm_le (H W : ℝ)
    (hY : 1≤Y) (hQ : 1≤Q) (hH : 0≤H) (hW : 0≤W)
    (hη : ∀ t,‖η t‖≤H) (hψ : ∀ t,‖ψ t‖≤W) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n B) :
    ‖markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i‖≤
      (markedPhysicalCoordinateEdgeBound V H W*Q^3)^n :=
  markedPhysicalCoordinateLabelKernel_norm_le P hP V pads ψ η d₀ Y Q H W
    hY hQ hH hW hη hψ n _ _ _

theorem markedPhysicalCoordinateIndexCoefficient_absolute_sum (H W : ℝ)
    (hY : 1≤Y) (hQ : 1≤Q) (hH : 0≤H) (hW : 0≤W)
    (hη : ∀ t,‖η t‖≤H) (hψ : ∀ t,‖ψ t‖≤W) (n B : ℕ) :
    (∑ i : MarkedPhysicalCoordinateIndex P (pads+1) n B,
      ‖markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i‖)≤
      Fintype.card (MarkedPhysicalCoordinateIndex P (pads+1) n B)*
        (markedPhysicalCoordinateEdgeBound V H W*Q^3)^n := by
  calc
    _ ≤ ∑ _i : MarkedPhysicalCoordinateIndex P (pads+1) n B,
        (markedPhysicalCoordinateEdgeBound V H W*Q^3)^n :=
      Finset.sum_le_sum (fun i _ => markedPhysicalCoordinateIndexCoefficient_norm_le
        P hP V pads ψ η d₀ Y Q H W hY hQ hH hW hη hψ i)
    _ = _ := by simp

end
end ArtinMatthews
