module

public import ArtinMatthews.MarkedMinorArcCellBandwidth
public import ArtinMatthews.MarkedMinorArcRawCleanKernel
public import ArtinMatthews.MarkedMinorArcRawCleanSupport
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal raw kernel is a finite sum of actual line-and-cell shifted
kernels. The shift set comes from the genuine cutoff, independently of the
number of position cells, root lines, active slots, or pending particles. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators

/-- Actual projective line and literal source position cell. -/
noncomputable def markedRawPositionKey {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ) (z : Z) :
    MarkedRootLineTuple D × ℤ :=
  (markedRawPositionLineTuple D z.1 (hZ _ z.2),markedMinorPositionCell r d₀ Y z.1)

/-- One actual cell shift, retaining the actual projective line gate. -/
noncomputable def markedRawCleanShiftKernel {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (r d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) (shift : ℤ) :
    Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ := by
  classical
  exact fun u v => if
    (markedRawPositionKey hZ r d₀ Y (markedRawCopiedProduct b.1) u.1).1=
      (markedRawPositionKey hZ r d₀ Y (markedRawCopiedProduct b.1) v.1).1 ∧
    markedMinorPositionCell r d₀ Y v.1.1-markedMinorPositionCell r d₀ Y u.1.1=shift
    then markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v else 0

/-- Every nonzero actual raw edge already has the stated projective line. -/
theorem markedRawCleanKernel_ne_zero_line {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z)
    (h : markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v ≠ 0) :
    markedRawPositionLineTuple (markedRawCopiedProduct b.1) u.1.1 (hZ _ u.1.2)=
      markedRawPositionLineTuple (markedRawCopiedProduct b.1) v.1.1 (hZ _ v.1.2) := by
  exact (markedRawCleanKernel_line_gate hZ b
    (markedRawCleanKernel_ne_zero_squarefree hP hZ ψ η d₀ Y Q ρ χ b u v h) u v).mp
      (markedRawCleanKernel_ne_zero_support hZ ψ η d₀ Y Q ρ χ b u v h).2.1

/-- Exact finite decomposition into the actual root-line-preserving cell
shifts, with the shift bound derived from the literal raw determinant cutoff. -/
theorem markedRawCleanKernel_eq_sum_shifts {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    {d₀ Y c K : ℝ} (hd₀ : 0 < d₀) (hY : 0 < Y) (hc : 0 < c) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (r Q ρ : ℝ)
    (hτ : ∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z|)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (b : MarkedRawBackground P pads B) :
    markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b=
      ∑ shift ∈ Finset.Icc (-(⌈2*K/c^2+1⌉₊ : ℤ)) (⌈2*K/c^2+1⌉₊ : ℤ),
        markedRawCleanShiftKernel hZ ψ η r d₀ Y Q ρ χ b shift := by
  classical
  funext u v
  simp only [Matrix.sum_apply]
  by_cases hz : markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v=0
  · simp only [markedRawCleanShiftKernel,hz,ite_self,Finset.sum_const_zero]
  · have hline := markedRawCleanKernel_ne_zero_line hP hZ ψ η d₀ Y Q ρ χ b u v hz
    have hshift := markedRawCleanKernel_ne_zero_shift hZ ψ η hd₀ hY hc hK hψ r Q ρ hτ χ b u v hz
    symm
    calc
      _ = markedRawCleanShiftKernel hZ ψ η r d₀ Y Q ρ χ b
          (markedMinorPositionCell r d₀ Y v.1.1-markedMinorPositionCell r d₀ Y u.1.1) u v := by
        apply Finset.sum_eq_single
        · intro shift _ hne
          simp only [markedRawCleanShiftKernel,markedRawPositionKey,hline,true_and,
            ite_eq_right (Ne.symm hne)]
        · exact fun hn => False.elim (hn hshift)
      _ = _ := by simp only [markedRawCleanShiftKernel,markedRawPositionKey,hline,and_self,ite_true]

/-- Actual floor cells give the required geometric width for any fixed
source-to-target shift; the bound is independent of the source cell index. -/
theorem markedMinorPositionCell_distance_of_shift (r : ℝ) {d₀ Y : ℝ}
    (hd₀ : 0 < d₀) (hY : 0 < Y) (z v : ℤ × ℤ) (shift : ℤ)
    (hshift : markedMinorPositionCell r d₀ Y v-markedMinorPositionCell r d₀ Y z=shift) :
    |(v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z| ≤
      ((|shift| : ℤ) : ℝ)*(d₀*Y)+d₀*Y := by
  have hw : 0 < d₀*Y := mul_pos hd₀ hY
  have hz₁ := Int.floor_le (((z.2 : ℝ)/markedMinorIntegerTau r z)/(d₀*Y))
  have hz₂ := Int.lt_floor_add_one (((z.2 : ℝ)/markedMinorIntegerTau r z)/(d₀*Y))
  have hv₁ := Int.floor_le (((v.2 : ℝ)/markedMinorIntegerTau r v)/(d₀*Y))
  have hv₂ := Int.lt_floor_add_one (((v.2 : ℝ)/markedMinorIntegerTau r v)/(d₀*Y))
  have hs : ((markedMinorPositionCell r d₀ Y v : ℤ) : ℝ)-
      ((markedMinorPositionCell r d₀ Y z : ℤ) : ℝ)=(shift : ℝ) := by exact_mod_cast hshift
  change ((markedMinorPositionCell r d₀ Y z : ℤ) : ℝ) ≤ _ at hz₁
  change _ < ((markedMinorPositionCell r d₀ Y z : ℤ) : ℝ)+1 at hz₂
  change ((markedMinorPositionCell r d₀ Y v : ℤ) : ℝ) ≤ _ at hv₁
  change _ < ((markedMinorPositionCell r d₀ Y v : ℤ) : ℝ)+1 at hv₂
  have hz₁' := (le_div_iff₀ hw).mp hz₁
  have hz₂' := (div_lt_iff₀ hw).mp hz₂
  have hv₁' := (le_div_iff₀ hw).mp hv₁
  have hv₂' := (div_lt_iff₀ hw).mp hv₂
  have habs₁ : -(↑(|shift|) : ℝ) ≤ (shift : ℝ) := by exact_mod_cast neg_abs_le shift
  have habs₂ : (shift : ℝ) ≤ (↑(|shift|) : ℝ) := by exact_mod_cast le_abs_self shift
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right habs₁ hw.le,mul_le_mul_of_nonneg_right habs₂ hw.le]

end ArtinMatthews
