module

public import ArtinMatthews.MarkedPhysicalSlopeSeparation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Telescoping the actual slopes of a finite physical path. Zero
determinants and repeated positions are permitted throughout. -/
namespace ArtinMatthews
noncomputable section

theorem markedFiniteRealPath_distance (n : ℕ) (f : Fin (n+1) → ℝ) (D : ℝ)
    (hstep : ∀ k : Fin n,|f k.succ-f k.castSucc|≤D) (v : Fin (n+1)) :
    |f v-f 0|≤(v.val:ℝ)*D := by
  refine Fin.induction ?_ ?_ v
  · simp
  · intro k ih
    have ht : |f k.succ-f 0|≤|f k.succ-f k.castSucc|+|f k.castSucc-f 0| := by
      simpa only [sub_add_sub_cancel] using abs_add_le (f k.succ-f k.castSucc) (f k.castSucc-f 0)
    calc
      _ ≤ |f k.succ-f k.castSucc|+|f k.castSucc-f 0| := ht
      _ ≤ D+(k.val:ℝ)*D := add_le_add (hstep k) ih
      _ = (k.succ.val:ℝ)*D := by simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]; ring

theorem markedFiniteRealPath_distance_le (n : ℕ) (f : Fin (n+1) → ℝ) (D : ℝ) (hD : 0≤D)
    (hstep : ∀ k : Fin n,|f k.succ-f k.castSucc|≤D) (v : Fin (n+1)) :
    |f v-f 0|≤(n:ℝ)*D :=
  (markedFiniteRealPath_distance n f D hstep v).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ v.isLt) hD)

theorem markedPhysicalPath_slope_step (n : ℕ) (p : Fin (n+1) → ℤ × ℤ)
    (U C : ℝ) (hU : 0<U) (hC : 0≤C)
    (hfirst : ∀ v,U≤((p v).1:ℝ))
    (hdet : ∀ k : Fin n,|(markedMinorIntegerDet (p k.castSucc) (p k.succ):ℝ)|≤C) :
    ∀ k : Fin n,|markedPhysicalSlope (p k.succ)-markedPhysicalSlope (p k.castSucc)|≤C/U^2 := by
  intro k
  have hs : 0<((p k.castSucc).1:ℝ) := hU.trans_le (hfirst _)
  have ht : 0<((p k.succ).1:ℝ) := hU.trans_le (hfirst _)
  rw [markedPhysicalSlope_difference _ _ (by exact_mod_cast hs.ne') (by exact_mod_cast ht.ne'),
    abs_div,abs_of_pos (mul_pos hs ht)]
  apply (div_le_div_iff₀ (mul_pos hs ht) (sq_pos_of_pos hU)).mpr
  have hden : U^2≤((p k.castSucc).1:ℝ)*((p k.succ).1:ℝ) := by
    nlinarith [hfirst k.castSucc,hfirst k.succ]
  exact (mul_le_mul_of_nonneg_right (hdet k) (sq_nonneg U)).trans
    (mul_le_mul_of_nonneg_left hden hC)

theorem markedPhysicalPath_root_det_bound (n : ℕ) (p : Fin (n+1) → ℤ × ℤ)
    (U C : ℝ) (hU : 0<U) (hC : 0≤C)
    (hbox : ∀ v,U≤((p v).1:ℝ) ∧ ((p v).1:ℝ)≤16*U)
    (hdet : ∀ k : Fin n,|(markedMinorIntegerDet (p k.castSucc) (p k.succ):ℝ)|≤C)
    (v : Fin (n+1)) : |(markedMinorIntegerDet (p 0) (p v):ℝ)|≤256*(n:ℝ)*C := by
  have hstep := markedPhysicalPath_slope_step n p U C hU hC (fun v => (hbox v).1) hdet
  have hslope := markedFiniteRealPath_distance_le n (fun v => markedPhysicalSlope (p v))
    (C/U^2) (div_nonneg hC (sq_nonneg U)) hstep v
  have hs : 0<((p 0).1:ℝ) := hU.trans_le (hbox 0).1
  have ht : 0<((p v).1:ℝ) := hU.trans_le (hbox v).1
  rw [markedPhysicalSlope_difference _ _ (by exact_mod_cast hs.ne') (by exact_mod_cast ht.ne'),
    abs_div,abs_of_pos (mul_pos hs ht)] at hslope
  have hb := (div_le_iff₀ (mul_pos hs ht)).mp hslope
  have hden : ((p 0).1:ℝ)*((p v).1:ℝ)≤(16*U)^2 := by
    nlinarith [(hbox 0).2,(hbox v).2]
  calc
    _ ≤ ((n:ℝ)*(C/U^2))*(((p 0).1:ℝ)*((p v).1:ℝ)) := hb
    _ ≤ ((n:ℝ)*(C/U^2))*(16*U)^2 :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 256*(n:ℝ)*C := by field_simp [hU.ne']; ring

end
end ArtinMatthews
