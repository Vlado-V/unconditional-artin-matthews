module

public import ArtinMatthews.MarkedMinorArcOperator
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
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The dimension-sharp absolute bound for the actual determinant matrix.
This bounds its complementary Fourier tail without losing a power of Y. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The actual integer rectangle has exactly `M*N` points. -/
theorem markedMinorBox_card (L T : ℤ) (M N : ℕ) :
    (markedMinorBox L T M N).card = M*N := by
  simp only [markedMinorBox,Finset.product_eq_sprod,Finset.card_product,Int.card_Ico,
    add_sub_cancel_left,Int.toNat_natCast]

/-- The elementary Hilbert-space matrix bound from an entry bound. -/
theorem markedMinorMatrix_norm_le_card_mul_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {B : ℝ} (hB : 0 ≤ B) (hentry : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A‖ ≤ B*(Fintype.card ι : ℝ) := by
  classical
  apply markedMinorMatrix_norm_le_of_energy A (mul_nonneg hB (Nat.cast_nonneg _))
  intro f
  have hCS : (∑ j, ‖f j‖)^2 ≤ (Fintype.card ι : ℝ)*(∑ j, ‖f j‖^2) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun _ => (1:ℝ)) (fun j => ‖f j‖)
  have hpoint (i : ι) : ‖(A *ᵥ f) i‖^2 ≤ B^2*(Fintype.card ι : ℝ)*(∑ j, ‖f j‖^2) := by
    calc
      _ ≤ (∑ j, ‖A i j‖*‖f j‖)^2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [mulVec,dotProduct,norm_mul] using norm_sum_le Finset.univ (fun j => A i j*f j)
      _ ≤ (B*∑ j, ‖f j‖)^2 := by
        apply pow_le_pow_left₀ (by positivity)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _))
      _ = B^2*(∑ j, ‖f j‖)^2 := mul_pow _ _ _
      _ ≤ B^2*((Fintype.card ι : ℝ)*(∑ j, ‖f j‖^2)) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg B)
      _ = _ := by ring
  calc
    _ ≤ ∑ _i : ι, B^2*(Fintype.card ι : ℝ)*(∑ j, ‖f j‖^2) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp; ring

/-- The actual normalized determinant matrix has absolute norm at most its
rectangle area divided by Y, for every frequency including all resonances. -/
theorem markedMinorDeterminantMatrix_norm_le_area (L T : ℤ) (M N : ℕ)
    {Y : ℝ} (hY : 0 < Y) (θ : ℝ) :
    ‖markedMinorDeterminantMatrix L T M N Y θ‖ ≤ ((M : ℝ)*(N : ℝ))/Y := by
  classical
  have hh := markedMinorMatrix_norm_le_card_mul_entry
    (markedMinorDeterminantMatrix L T M N Y θ) (B := 1/Y) (by positivity) (fun i j => by
      simp only [markedMinorDeterminantMatrix,norm_mul,norm_inv,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hY,OAI.Problem337.RealPhase.norm_phase,mul_one,one_div]
      exact le_rfl)
  have hcard : (Fintype.card (MarkedMinorBoxIndex L T M N) : ℝ) = (M : ℝ)*(N : ℝ) := by
    rw [Fintype.card_coe,markedMinorBox_card,Nat.cast_mul]
  rw [hcard] at hh
  convert hh using 1; ring

/-- Thus the actual source lattice-area condition gives an absolute
frequency-uniform bound, needed for the Fourier cutoff tail. -/
theorem markedMinorDeterminantMatrix_norm_le (L T : ℤ) (M N : ℕ) {Y C : ℝ}
    (hY : 0 < Y) (hMN : (M : ℝ)*(N : ℝ) ≤ C*Y) (θ : ℝ) :
    ‖markedMinorDeterminantMatrix L T M N Y θ‖ ≤ C :=
  (markedMinorDeterminantMatrix_norm_le_area L T M N hY θ).trans
    ((div_le_iff₀ hY).mpr hMN)

end ArtinMatthews
