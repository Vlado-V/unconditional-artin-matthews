module

public import ArtinMatthews.MarkedMinorArcBanMajor
public import ArtinMatthews.MarkedMinorArcCellGeometry
public import ArtinMatthews.MarkedMinorArcBanNeighbors
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite target enumeration for the raw-minus-major comparison kernel. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedBanNormalizedDet (z : ℤ × ℤ) (D : ℤ) (v : ℤ × ℤ) : ℤ :=
  markedMinorIntegerDet z v / D

def markedBanEdgeKernel (ψ : ℝ → ℂ) (Q Y : ℝ) (b a l : ℤ) : ℂ :=
  ψ ((l:ℝ)/Y)*((if l=b-a then 1 else 0)-markedBanMajorKernel Q Y (l-b+a))

theorem markedBan_normalized_fiber_card_le (r : ℝ) (z w : ℤ × ℤ) (D l : ℤ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (V : Finset (ℤ × ℤ))
    (hV : ∀ v ∈ V, D ∣ markedMinorIntegerDet z v ∧
      |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) :
    (V.filter (fun v => markedBanNormalizedDet z D v=l)).card ≤ 33 := by
  apply markedBan_targets_card_le r z w (D*l) hd hz
  intro v hv
  obtain ⟨hmem,hl⟩ := Finset.mem_filter.mp hv
  refine ⟨?_,(hV v hmem).2⟩
  calc
    _ = (markedMinorIntegerDet z v / D)*D := (Int.ediv_mul_cancel (hV v hmem).1).symm
    _ = _ := by rw [show markedMinorIntegerDet z v / D=l from hl]; ring

theorem markedBanEdgeKernel_norm_le (ψ : ℝ → ℂ) {Q Y W : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) (hW : 0 ≤ W) (hψ : ∀ u, ‖ψ u‖ ≤ W) (b a l : ℤ) :
    ‖markedBanEdgeKernel ψ Q Y b a l‖ ≤
      W*((if l=b-a then (1:ℝ) else 0)+4*Q^3/Y) := by
  have hi : ‖(if l=b-a then (1:ℂ) else 0)‖ = if l=b-a then (1:ℝ) else 0 := by
    split_ifs <;> simp
  calc
    _ ≤ ‖ψ ((l:ℝ)/Y)‖*(‖(if l=b-a then (1:ℂ) else 0)‖+‖markedBanMajorKernel Q Y (l-b+a)‖) := by
      rw [markedBanEdgeKernel,norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ W*((if l=b-a then (1:ℝ) else 0)+4*Q^3/Y) :=
      mul_le_mul (hψ _) (add_le_add (le_of_eq hi) (markedBanMajorKernel_norm_le hQ hY _))
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) hW

theorem markedBan_kernel_row_bound (r : ℝ) (z w : ℤ × ℤ) (D b a : ℤ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (V : Finset (ℤ × ℤ))
    (hV : ∀ v ∈ V, D ∣ markedMinorIntegerDet z v ∧
      |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    (ψ : ℝ → ℂ) {Q Y A W : ℝ} (hQ : 0 ≤ Q) (hY : 0 < Y) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ A)
    (test : (ℤ × ℤ) → ℂ) (htest : ∀ v ∈ V, ‖test v‖ ≤ 1) :
    (∑ v ∈ V, ‖test v*markedBanEdgeKernel ψ Q Y b a (markedBanNormalizedDet z D v)‖) ≤
      33*W*(1+(2*A*Y+1)*(4*Q^3/Y)) := by
  classical
  let S := V.filter (fun v => ψ ((markedBanNormalizedDet z D v:ℝ)/Y) ≠ 0)
  let L := markedBanIntegerWindow 0 (A*Y)
  have hSV : S ⊆ V := Finset.filter_subset _ _
  have hlegal : ∀ v ∈ S, D ∣ markedMinorIntegerDet z v ∧
      |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16 := fun v hv => hV v (hSV hv)
  have hmaps : (S : Set (ℤ × ℤ)).MapsTo (markedBanNormalizedDet z D) L := by
    intro v hv
    apply mem_markedBanIntegerWindow.mpr
    have hh := hsupp _ (Finset.mem_filter.mp hv).2
    rw [abs_div,abs_of_pos hY] at hh
    have hm := (div_le_iff₀ hY).mp hh
    simpa only [add_zero] using hm
  have hcard : S.card ≤ 33*L.card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      _ ≤ ∑ _l ∈ L, 33 := Finset.sum_le_sum (fun l _ =>
        markedBan_normalized_fiber_card_le r z w D l hd hz S hlegal)
      _ = _ := by simp [Nat.mul_comm]
  have hcardR : (S.card:ℝ) ≤ 33*(2*A*Y+1) := by
    have hL := markedBanIntegerWindow_card_le 0 (mul_nonneg hA hY.le)
    have hc : (S.card:ℝ) ≤ 33*(L.card:ℝ) := by exact_mod_cast hcard
    exact hc.trans (by nlinarith [hL])
  have hraw : ((S.filter (fun v => markedBanNormalizedDet z D v=b-a)).card:ℝ) ≤ 33 := by
    exact_mod_cast markedBan_normalized_fiber_card_le r z w D (b-a) hd hz S hlegal
  have heq : (∑ v ∈ S, ‖test v*markedBanEdgeKernel ψ Q Y b a (markedBanNormalizedDet z D v)‖) =
      ∑ v ∈ V, ‖test v*markedBanEdgeKernel ψ Q Y b a (markedBanNormalizedDet z D v)‖ := by
    apply Finset.sum_subset hSV
    intro v hv hn
    have hzero : ψ ((markedBanNormalizedDet z D v:ℝ)/Y)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hv,hh⟩)
    simp only [markedBanEdgeKernel,hzero,zero_mul,mul_zero,norm_zero]
  rw [← heq]
  calc
    _ ≤ ∑ v ∈ S, W*((if markedBanNormalizedDet z D v=b-a then (1:ℝ) else 0)+4*Q^3/Y) := by
      apply Finset.sum_le_sum
      intro v hv
      calc
        _ ≤ ‖markedBanEdgeKernel ψ Q Y b a (markedBanNormalizedDet z D v)‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (htest v (hSV hv))
        _ ≤ _ := markedBanEdgeKernel_norm_le ψ hQ hY hW hψ b a _
    _ = W*(((S.filter (fun v => markedBanNormalizedDet z D v=b-a)).card:ℝ)+(S.card:ℝ)*(4*Q^3/Y)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
      simp only [Finset.sum_boole,Finset.sum_const,nsmul_eq_mul]
    _ ≤ W*(33+(33*(2*A*Y+1))*(4*Q^3/Y)) :=
      mul_le_mul_of_nonneg_left (add_le_add hraw
        (mul_le_mul_of_nonneg_right hcardR (by positivity))) hW
    _ = _ := by ring

theorem markedBan_kernel_row_bound_polynomial (r : ℝ) (z w : ℤ × ℤ) (D b a : ℤ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (V : Finset (ℤ × ℤ))
    (hV : ∀ v ∈ V, D ∣ markedMinorIntegerDet z v ∧
      |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    (ψ : ℝ → ℂ) {Q Y A W : ℝ} (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ A)
    (test : (ℤ × ℤ) → ℂ) (htest : ∀ v ∈ V, ‖test v‖ ≤ 1) :
    (∑ v ∈ V, ‖test v*markedBanEdgeKernel ψ Q Y b a (markedBanNormalizedDet z D v)‖) ≤
      (33*W*(8*A+5))*Q^3 := by
  have hYpos : 0 < Y := by linarith
  have hq3 : 1 ≤ Q^3 := one_le_pow₀ hQ
  have hi : 1/Y ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hY
  apply (markedBan_kernel_row_bound r z w D b a hd hz V hV ψ
    (by linarith) hYpos hA hW hψ hsupp test htest).trans
  calc
    _ = 33*W*(1+(8*A+4*(1/Y))*Q^3) := by field_simp [hYpos.ne']; ring
    _ ≤ 33*W*(Q^3+(8*A+4)*Q^3) :=
      mul_le_mul_of_nonneg_left (add_le_add hq3
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (by positivity)
    _ = _ := by ring

end ArtinMatthews
