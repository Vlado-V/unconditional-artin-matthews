module

public import ArtinMatthews.MarkedTypeIIGoodSecond
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual second good-state test forces at most one distinct numeric
omission/promoted product in the dirty anchor interval. -/
namespace ArtinMatthews

/-- The source second-test complement gives the literal pair separation. -/
theorem markedMinorPairGood_separation (Q : Finset ℤ) (T : ℤ) (ε : ℝ)
    (r : AddCircle (1:ℝ)) (hg : r ∉ markedPairBadRoots Q T ε)
    {u v : ℤ} (hu : u ∈ Q) (hv : v ∈ Q) (hne : u ≠ v) :
    ε < ‖((u-v)*T) • r‖ := by
  by_contra h
  apply hg
  apply Set.mem_iUnion.mpr
  refine ⟨u,Set.mem_iUnion.mpr ⟨hu,Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,?_⟩⟩⟩⟩
  rw [ite_eq_right hne]
  exact le_of_not_gt h

/-- Literal distinct numeric trial values satisfying the source anchor interval. -/
noncomputable def markedMinorDirtyAnchorTrials (Q : Finset ℤ) (T : ℤ)
    (r A : AddCircle (1:ℝ)) (p : ℕ) : Finset ℤ := by
  classical
  exact Q.filter (fun u => ‖(u*T) • r-A‖ ≤ 16/(p : ℝ))

/-- The source separation100ε is strictly larger than the anchor diameter
32/p. At most one distinct integer DZ can survive. -/
theorem markedMinorDirtyAnchorTrials_card_le_one (Q : Finset ℤ) (T : ℤ)
    (r A : AddCircle (1:ℝ)) {p : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hp : 1/(p : ℝ) ≤ ε) (hg : r ∉ markedPairBadRoots Q T (100*ε)) :
    (markedMinorDirtyAnchorTrials Q T r A p).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hu' := Finset.mem_filter.mp hu
  have hv' := Finset.mem_filter.mp hv
  by_contra hne
  have hsep := markedMinorPairGood_separation Q T (100*ε) r hg hu'.1 hv'.1 hne
  have he : ((u-v)*T) • r=(u*T) • r-(v*T) • r := by
    rw [sub_mul,sub_smul]
  rw [he] at hsep
  have htri : ‖(u*T) • r-(v*T) • r‖ ≤ 16/(p : ℝ)+16/(p : ℝ) := by
    calc
      _ ≤ ‖(u*T) • r-A‖+‖(v*T) • r-A‖ := by
        simpa only [dist_eq_norm,norm_sub_rev A ((v*T) • r)] using
          dist_triangle ((u*T) • r) A ((v*T) • r)
      _ ≤ _ := add_le_add hu'.2 hv'.2
  have hb : 16/(p : ℝ)+16/(p : ℝ) ≤ 32*ε := by
    calc
      _ = 32*(1/(p : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  linarith

/-- Actual band-prime scale p≥exp(L^a) discharges the anchor-diameter
comparison, with no asymptotic separation premise substituted. -/
theorem markedMinorDirtyAnchorTrials_card_le_one_exp (Q : Finset ℤ) (T : ℤ)
    (r A : AddCircle (1:ℝ)) (p : ℕ) (L a : ℝ)
    (hp : Real.exp (L^a) ≤ (p : ℝ))
    (hg : r ∉ markedPairBadRoots Q T (100*Real.exp (-(L^a)))) :
    (markedMinorDirtyAnchorTrials Q T r A p).card ≤ 1 := by
  apply markedMinorDirtyAnchorTrials_card_le_one Q T r A (Real.exp_pos _)
  · calc
      _ ≤ 1/Real.exp (L^a) := one_div_le_one_div_of_le (Real.exp_pos _) hp
      _ = _ := by rw [one_div,Real.exp_neg]
  · exact hg

end ArtinMatthews
