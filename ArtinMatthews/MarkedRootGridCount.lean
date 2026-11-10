module

public import ArtinMatthews.MarkedRootUniformGrid
public import ArtinMatthews.MarkedRootGridBudget
public import ArtinMatthews.FixedURootPrescribedMatrix
public import ArtinMatthews.FixedURootFullPowerSaving
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The literal finite grid pays the proved three-dimensional root error
once per cell. The source's c/8 choice retains its power number of cells. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def markedRootGridRootSet {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V : ℝ) (N : ℕ) (i : MarkedRootGridIndex N) : Finset (Σ _u : ℤ,ℤ × ℤ) :=
  fixedURootMatrixBoxPoints g₀
    (U*(1+(i.2.1:ℝ)/N)) (U*(1+((i.2.1:ℝ)+1)/N))
    ((i.1:ℝ)/N) (((i.1:ℝ)+1)/N)
    (V*(1+(i.2.2:ℝ)/N)) (V*(1+((i.2.2:ℝ)+1)/N)) true true true true true true

def markedRootGridCountError {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V : ℝ) (N : ℕ) (i : MarkedRootGridIndex N) : ℝ :=
  |((markedRootGridRootSet g₀ U V N i).card : ℝ)-
    ((U*V)/(N:ℝ)^3)/((riemannZeta 2).re*
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))|

theorem markedRootGrid_interval_endpoints (N k i : ℕ) (hN : 0 < N) (hi : i < k*N) :
    0 ≤ (i:ℝ)/N ∧ (i:ℝ)/N ≤ ((i:ℝ)+1)/N ∧ ((i:ℝ)+1)/N ≤ (k:ℝ) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  refine ⟨div_nonneg (Nat.cast_nonneg i) hn.le,?_,?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hn.le
  · apply (div_le_iff₀ hn).mpr
    exact_mod_cast (show i+1 ≤ k*N by omega)

theorem markedRootGridCountError_bound {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ,0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ) (N : ℕ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S:ℝ) ≤ Real.exp (M*(Real.log x)^(49/50:ℝ)) → 0 < N →
        ∀ i : MarkedRootGridIndex N,markedRootGridCountError g₀ U V N i ≤ E*U*V*x^(-δ/1000) := by
  obtain ⟨E,hE,hroot⟩ := fixedURootMatrixBox_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hroot,eventually_gt_atTop (0:ℝ)] with x hx hx0
  intro S g₀ U V N hU hV hS hSr hN i
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hr := markedRootGrid_interval_endpoints N 1 i.1 hN (by simpa only [one_mul] using i.1.isLt)
  have ha := markedRootGrid_interval_endpoints N 15 i.2.1 hN i.2.1.isLt
  have hb := markedRootGrid_interval_endpoints N 1 i.2.2 hN (by simpa only [one_mul] using i.2.2.isLt)
  have hh := hx S g₀ U V
    (U*(1+(i.2.1:ℝ)/N)) (U*(1+((i.2.1:ℝ)+1)/N))
    ((i.1:ℝ)/N) (((i.1:ℝ)+1)/N)
    (V*(1+(i.2.2:ℝ)/N)) (V*(1+((i.2.2:ℝ)+1)/N))
    true true true true true true hU hV hS hSr
    (by nlinarith [ha.1]) (mul_le_mul_of_nonneg_left (by linarith [ha.2.1]) hUp.le)
    (by nlinarith [ha.2.2]) hr.1 hr.2.1 (by simpa only [Nat.cast_one] using hr.2.2)
    (by nlinarith [hb.1]) (mul_le_mul_of_nonneg_left (by linarith [hb.2.1]) hVp.le)
    (by nlinarith [hb.2.2])
  convert hh using 1
  unfold markedRootGridCountError markedRootGridRootSet
  congr 1
  congr 1
  field_simp [hNr]
  ring

theorem markedRootGridCountError_sum_bound {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ,0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S:ℝ) ≤ Real.exp (M*(Real.log x)^(49/50:ℝ)) →
        (∑ i : MarkedRootGridIndex (markedRootGridSize (δ/1000) x),
          markedRootGridCountError g₀ U V (markedRootGridSize (δ/1000) x) i)/(U*V) ≤
            120*E*x^(-5*(δ/1000)/8) := by
  obtain ⟨E,hE,hroot⟩ := markedRootGridCountError_bound hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hroot,eventually_ge_atTop (1:ℝ)] with x hx hx1
  intro S g₀ U V hU hV hS hSr
  have hc : 0 < δ/1000 := by positivity
  have hUp : 0 < U := (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hx1) δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hx1) δ).trans_le hV
  have hN := (markedRootGridSize_bounds hc hx1).1
  have hs : (∑ i : MarkedRootGridIndex (markedRootGridSize (δ/1000) x),
      markedRootGridCountError g₀ U V (markedRootGridSize (δ/1000) x) i) ≤
      (15*(markedRootGridSize (δ/1000) x : ℝ)^3)*(E*U*V*x^(-δ/1000)) := by
    calc
      _ ≤ ∑ _i : MarkedRootGridIndex (markedRootGridSize (δ/1000) x),E*U*V*x^(-δ/1000) :=
        Finset.sum_le_sum (fun i _ => hx S g₀ U V _ hU hV hS hSr hN i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,markedRootGridIndex_card,
          Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,nsmul_eq_mul]
  apply (div_le_iff₀ (mul_pos hUp hVp)).mpr
  apply hs.trans
  have hg := mul_le_mul_of_nonneg_left (markedRootGridSize_discrepancy hc hx1) hE.le
  calc
    _ = (E*(15*(markedRootGridSize (δ/1000) x : ℝ)^3*x^(-(δ/1000))))*(U*V) := by
      rw [show -δ/1000=-(δ/1000) by ring]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hg (mul_pos hUp hVp).le

end ArtinMatthews
