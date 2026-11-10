module

public import ArtinMatthews.MarkedMinorArcCircle
public import ArtinMatthews.MarkedMinorArcBanMajor
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact real representatives of the original closed major arcs. The finite
cover is used as a cover, without any disjointness or omitted endpoints. -/
namespace ArtinMatthews
open Set Metric

 theorem markedMajor_circle_closedBall_lift (x r : ℝ) (ξ : AddCircle (1:ℝ))
    (hξ : ξ ∈ closedBall (x:AddCircle (1:ℝ)) r) :
    ∃ t : ℝ, |t| ≤ r ∧ ((x+t:ℝ):AddCircle (1:ℝ)) = ξ := by
  obtain ⟨y,hy⟩ := Quot.exists_rep ξ
  change ((y:ℝ):AddCircle (1:ℝ))=ξ at hy
  have hpre : y ∈ ((fun t : ℝ => (t:AddCircle (1:ℝ))) ⁻¹' closedBall (x:AddCircle (1:ℝ)) r) := by
    simpa only [mem_preimage,hy] using hξ
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hpre
  obtain ⟨n,hn⟩ := mem_iUnion.mp hpre
  have hb : |y-(x+(n:ℝ))| ≤ r := by
    simpa only [mem_closedBall,Real.dist_eq,zsmul_eq_mul,mul_one] using hn
  refine ⟨y-(x+(n:ℝ)),hb,?_⟩
  have he : x+(y-(x+(n:ℝ)))=y-(n:ℝ) := by ring
  rw [he,AddCircle.coe_sub,markedBan_integer_circle_zero,sub_zero,hy]

 theorem markedMajor_circle_major_lift {Q Y : ℝ} (hQ : 0 ≤ Q) (hY : 0 < Y)
    (ξ : AddCircle (1:ℝ)) (hξ : ξ ∈ markedMinorCircleMajor Q Y) :
    ∃ (q h : ℕ) (θ : ℝ), 0 < q ∧ (q:ℝ) ≤ Q ∧ h < ⌊Q⌋₊ ∧ |θ| ≤ 2*Q ∧
      ((((h:ℝ)/(q:ℝ)+θ/Y):ℝ):AddCircle (1:ℝ))=ξ := by
  have hc := markedBan_major_cover hQ hξ
  obtain ⟨q,hq,hh⟩ := mem_iUnion₂.mp hc
  obtain ⟨h,hh,hball⟩ := mem_iUnion₂.mp hh
  obtain ⟨t,ht,he⟩ := markedMajor_circle_closedBall_lift ((h:ℝ)/(q:ℝ)) (2*Q/Y) ξ hball
  have hqmem := Finset.mem_Icc.mp hq
  refine ⟨q,h,Y*t,hqmem.1,?_,Finset.mem_range.mp hh,?_,?_⟩
  · exact (show (q:ℝ) ≤ ⌊Q⌋₊ by exact_mod_cast hqmem.2).trans (Nat.floor_le hQ)
  · rw [abs_mul,abs_of_pos hY]
    have hm := mul_le_mul_of_nonneg_left ht hY.le
    have hid : Y*(2*Q/Y)=2*Q := by field_simp
    rwa [hid] at hm
  · convert he using 2
    field_simp

end ArtinMatthews
