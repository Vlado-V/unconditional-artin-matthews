module

public import ArtinMatthews.MarkedPhysicalRootCoordinates
public import ArtinMatthews.MarkedPhysicalPathSlopeBounds
public import ArtinMatthews.MarkedRawGoodRootTransport
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact coordinates, pole exclusion, and tube bounds for physical
paths. No pairwise-distinct or nonzero-determinant condition is imposed. -/
namespace ArtinMatthews
noncomputable section

def markedPhysicalPathCoordinates {n : ℕ} (root completion : ℤ × ℤ)
    (p : Fin (n+1) → ℤ × ℤ) : Fin (n+1) → ℤ × ℤ :=
  fun v => markedPhysicalRootCoordinates root completion (p v)

theorem markedPhysicalPathCoordinates_lift {n : ℕ} (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) (p : Fin (n+1) → ℤ × ℤ) (v : Fin (n+1)) :
    markedPhysicalRootLift root completion (markedPhysicalPathCoordinates root completion p v)=p v :=
  markedPhysicalRootLift_coordinates root completion (p v) hdet

theorem markedPhysicalPathCoordinates_initial {n : ℕ} (completion : ℤ × ℤ)
    (p : Fin (n+1) → ℤ × ℤ) (hdet : markedMinorIntegerDet (p 0) completion=1) :
    markedPhysicalPathCoordinates (p 0) completion p 0=(1,0) :=
  markedPhysicalRootCoordinates_source (p 0) completion hdet

theorem markedPhysicalPathCoordinates_terminal {n : ℕ} (completion : ℤ × ℤ)
    (p : Fin (n+1) → ℤ × ℤ) (hdet : markedMinorIntegerDet (p 0) completion=1)
    (hloop : p (Fin.last n)=p 0) :
    markedPhysicalPathCoordinates (p 0) completion p (Fin.last n)=(1,0) := by
  unfold markedPhysicalPathCoordinates
  rw [hloop,markedPhysicalRootCoordinates_source _ _ hdet]

theorem markedPhysicalPathCoordinates_eq_iff {n : ℕ} (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) (p : Fin (n+1) → ℤ × ℤ)
    (v w : Fin (n+1)) :
    markedPhysicalPathCoordinates root completion p v=markedPhysicalPathCoordinates root completion p w ↔ p v=p w :=
  (markedPhysicalRootEquiv root completion hdet).injective.eq_iff

theorem markedPhysicalPathCoordinates_det {n : ℕ} (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) (p : Fin (n+1) → ℤ × ℤ)
    (v w : Fin (n+1)) :
    markedMinorIntegerDet (markedPhysicalPathCoordinates root completion p v)
      (markedPhysicalPathCoordinates root completion p w)=markedMinorIntegerDet (p v) (p w) := by
  have h := markedPhysicalRootLift_det root completion
    (markedPhysicalPathCoordinates root completion p v) (markedPhysicalPathCoordinates root completion p w) hdet
  rw [markedPhysicalPathCoordinates_lift _ _ hdet,markedPhysicalPathCoordinates_lift _ _ hdet] at h
  exact h.symm

theorem markedPhysicalPathCoordinates_tau_box {n : ℕ} (completion : ℤ × ℤ)
    (p : Fin (n+1) → ℤ × ℤ) (hdet : markedMinorIntegerDet (p 0) completion=1)
    (U : ℝ) (hU : 0<U) (hbox : ∀ v,U≤((p v).1:ℝ) ∧ ((p v).1:ℝ)≤16*U)
    (v : Fin (n+1)) :
    (1/16:ℝ) ≤ markedMinorIntegerTau ((completion.1:ℝ)/(p 0).1)
      (markedPhysicalPathCoordinates (p 0) completion p v) ∧
      markedMinorIntegerTau ((completion.1:ℝ)/(p 0).1)
        (markedPhysicalPathCoordinates (p 0) completion p v)≤16 := by
  have hp : 0<((p 0).1:ℝ) := hU.trans_le (hbox 0).1
  rw [markedPhysicalPathCoordinates,markedPhysicalRootCoordinates_tau _ _ _ hdet (by exact_mod_cast hp.ne')]
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [(hbox 0).2,(hbox v).1]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [(hbox 0).1,(hbox v).2]

theorem markedPhysicalPathCoordinates_no_pole {n : ℕ} (completion : ℤ × ℤ)
    (p : Fin (n+1) → ℤ × ℤ) (hdet : markedMinorIntegerDet (p 0) completion=1)
    (U : ℝ) (hU : 0<U) (hbox : ∀ v,U≤((p v).1:ℝ) ∧ ((p v).1:ℝ)≤16*U)
    (v : Fin (n+1)) :
    markedMinorIntegerTau ((completion.1:ℝ)/(p 0).1)
      (markedPhysicalPathCoordinates (p 0) completion p v)≠0 := by
  have h := (markedPhysicalPathCoordinates_tau_box completion p hdet U hU hbox v).1
  linarith

theorem markedPhysicalPathCoordinates_tube {n : ℕ} (completion : ℤ × ℤ)
    (p : Fin (n+1) → ℤ × ℤ) (hdet : markedMinorIntegerDet (p 0) completion=1)
    (U C : ℝ) (hU : 0<U) (hC : 0≤C)
    (hbox : ∀ v,U≤((p v).1:ℝ) ∧ ((p v).1:ℝ)≤16*U)
    (hstep : ∀ k : Fin n,|(markedMinorIntegerDet (p k.castSucc) (p k.succ):ℝ)|≤C)
    (hr : ((completion.1:ℝ)/(p 0).1)∈Set.Icc (0:ℝ) 1) (v : Fin (n+1)) :
    |((markedPhysicalPathCoordinates (p 0) completion p v).1:ℝ)|≤16+256*(n:ℝ)*C ∧
      |((markedPhysicalPathCoordinates (p 0) completion p v).2:ℝ)|≤256*(n:ℝ)*C := by
  let z := markedPhysicalPathCoordinates (p 0) completion p v
  let r := (completion.1:ℝ)/(p 0).1
  have hz₂ : |(z.2:ℝ)|≤256*(n:ℝ)*C := markedPhysicalPath_root_det_bound n p U C hU hC hbox hstep v
  have ht := markedPhysicalPathCoordinates_tau_box completion p hdet U hU hbox v
  have hta : |markedMinorIntegerTau r z|≤16 := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  have hra : |r|≤1 := by
    rw [abs_of_nonneg (show 0≤r from hr.1)]
    exact hr.2
  have he : (z.1:ℝ)=markedMinorIntegerTau r z-r*(z.2:ℝ) := by unfold markedMinorIntegerTau; ring
  refine ⟨?_,hz₂⟩
  change |(z.1:ℝ)|≤_
  rw [he]
  calc
    _ ≤ |markedMinorIntegerTau r z|+|r*(z.2:ℝ)| := by
      simpa only [sub_zero,zero_sub,abs_neg] using
        abs_sub_le (markedMinorIntegerTau r z) 0 (r*(z.2:ℝ))
    _ = |markedMinorIntegerTau r z|+|r| * |(z.2:ℝ)| := by rw [abs_mul]
    _ ≤ 16+1*(256*(n:ℝ)*C) :=
      add_le_add hta (mul_le_mul hra hz₂ (abs_nonneg _) (by norm_num : (0:ℝ)≤1))
    _ = _ := by ring

end
end ArtinMatthews
