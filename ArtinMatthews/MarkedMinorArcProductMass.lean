module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal PD04 baseline, tilted prime measure, and product-mass bound. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedMemoryVisitQ (q : ℝ) (N : ℕ) (j : Fin (N+1)) : ℝ :=
  if j.val = 0 ∨ j.val = N then Real.sqrt q else q

def markedMemoryEta (q : ℝ) (N : ℕ) (j : Fin (N+1)) : ℝ :=
  1-markedMemoryVisitQ q N j

def markedMemoryBaseline (q : ℝ) (N p : ℕ) : ℝ :=
  1-(∑ j : Fin (N+1), markedMemoryEta q N j)/((p:ℝ)+1)

def markedMemoryPrimeAtom (V q : ℝ) (N p : ℕ) : ℝ :=
  1/(V*((p:ℝ)+1)*markedMemoryBaseline q N p)

theorem markedMemoryEta_mem_unitInterval {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (N : ℕ) (j : Fin (N+1)) : 0 ≤ markedMemoryEta q N j ∧ markedMemoryEta q N j ≤ 1 := by
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq0
  have hs1 : Real.sqrt q ≤ 1 := by nlinarith
  unfold markedMemoryEta markedMemoryVisitQ
  split_ifs <;> constructor <;> linarith

theorem markedMemoryEta_sum_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    0 ≤ (∑ j : Fin (N+1), markedMemoryEta q N j) ∧
      (∑ j : Fin (N+1), markedMemoryEta q N j) ≤ (N:ℝ)+1 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => (markedMemoryEta_mem_unitInterval hq0 hq1 N j).1)
  · calc
      _ ≤ ∑ _j : Fin (N+1), (1:ℝ) :=
        Finset.sum_le_sum (fun j _ => (markedMemoryEta_mem_unitInterval hq0 hq1 N j).2)
      _ = _ := by simp

/-- The actual source baseline is uniformly separated from zero as soon as
the prime is twice the number of path visits. -/
theorem markedMemoryBaseline_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {N p : ℕ} (hlarge : 2*(N+1) ≤ p+1) :
    (1/2:ℝ) ≤ markedMemoryBaseline q N p ∧ markedMemoryBaseline q N p ≤ 1 := by
  obtain ⟨hs0,hs1⟩ := markedMemoryEta_sum_bounds hq0 hq1 N
  have hp : 0 < (p:ℝ)+1 := by positivity
  have hsize : 2*((N:ℝ)+1) ≤ (p:ℝ)+1 := by exact_mod_cast hlarge
  have hf : (∑ j : Fin (N+1), markedMemoryEta q N j)/((p:ℝ)+1) ≤ 1/2 :=
    (div_le_iff₀ hp).mpr (by linarith)
  have hf0 := div_nonneg hs0 hp.le
  unfold markedMemoryBaseline
  constructor <;> linarith

theorem markedMemoryPrimeAtom_pos {V q : ℝ} (hV : 0 < V) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {N p : ℕ} (hlarge : 2*(N+1) ≤ p+1) : 0 < markedMemoryPrimeAtom V q N p := by
  have hb : 0 < markedMemoryBaseline q N p := by
    linarith [(markedMemoryBaseline_bounds hq0 hq1 hlarge).1]
  exact one_div_pos.mpr (mul_pos (mul_pos hV (by positivity)) hb)

theorem markedMemoryPrimeAtom_mul_prime_le {V q : ℝ} (hV : 0 < V)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N p : ℕ} (hlarge : 2*(N+1) ≤ p+1) :
    markedMemoryPrimeAtom V q N p * (p:ℝ) ≤ 2/V := by
  have hb := (markedMemoryBaseline_bounds hq0 hq1 hlarge).1
  have hb0 : 0 < markedMemoryBaseline q N p := by linarith
  have hp : 0 < (p:ℝ)+1 := by positivity
  have hd : 0 < V*((p:ℝ)+1)*markedMemoryBaseline q N p := mul_pos (mul_pos hV hp) hb0
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hV.le hp.le)
  apply (le_div_iff₀ hV).mpr
  calc
    _ = ((p:ℝ)*V)/(V*((p:ℝ)+1)*markedMemoryBaseline q N p) := by
      unfold markedMemoryPrimeAtom
      ring
    _ ≤ 2 := (div_le_iff₀ hd).mpr (by nlinarith)

def markedMemoryProductMass {J : Type*} [Fintype J] (V : J → ℝ)
    (q : ℝ) (N : ℕ) (p : J → ℕ) : ℝ :=
  ∏ j, markedMemoryPrimeAtom (V j) q N (p j)

theorem markedMemoryProductMass_le_reciprocal {J : Type*} [Fintype J]
    {V : J → ℝ} {v q : ℝ} (hv : 0 < v) (hV : ∀ j, v ≤ V j)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N : ℕ} (p : J → ℕ)
    (hp : ∀ j, 0 < p j) (hlarge : ∀ j, 2*(N+1) ≤ p j+1) :
    markedMemoryProductMass V q N p ≤ (2/v)^(Fintype.card J)/(∏ j, p j : ℕ) := by
  have hb : 0 < (∏ j, p j : ℕ) := Finset.prod_pos (fun j _ => hp j)
  have hbR : 0 < ((∏ j, p j : ℕ):ℝ) := by exact_mod_cast hb
  apply (le_div_iff₀ hbR).mpr
  calc
    _ = ∏ j, markedMemoryPrimeAtom (V j) q N (p j)*(p j:ℝ) := by
      rw [Nat.cast_prod, Finset.prod_mul_distrib]
      rfl
    _ ≤ ∏ _j : J, (2/v) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact mul_nonneg (markedMemoryPrimeAtom_pos (hv.trans_le (hV j)) hq0 hq1 (hlarge j)).le
          (Nat.cast_nonneg _)
      · intro j _
        exact (markedMemoryPrimeAtom_mul_prime_le (hv.trans_le (hV j)) hq0 hq1 (hlarge j)).trans
          (div_le_div_of_nonneg_left (by norm_num) hv (hV j))
    _ = _ := by simp [div_pow]

/-- The actual dyadic support [1,4] in PD03 turns the reciprocal-product
bound into the endpoint mass C_K/Y used in PD04. -/
theorem markedMemoryProductMass_le_of_cutoff {J : Type*} [Fintype J]
    {V : J → ℝ} {v q Y : ℝ} (hv : 0 < v) (hV : ∀ j, v ≤ V j)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {N : ℕ} (p : J → ℕ)
    (hp : ∀ j, 0 < p j) (hlarge : ∀ j, 2*(N+1) ≤ p j+1)
    (hY : 0 < Y) (η : ℝ → ℂ) (hη : Function.support η ⊆ Set.Icc 1 4)
    (hcut : η (((∏ j, p j : ℕ):ℝ)/Y) ≠ 0) :
    markedMemoryProductMass V q N p ≤ (2/v)^(Fintype.card J)/Y := by
  have hb : Y ≤ ((∏ j, p j : ℕ):ℝ) := by
    have hh : 1 ≤ ((∏ j, p j : ℕ):ℝ)/Y := (hη hcut).1
    simpa only [one_mul] using (le_div_iff₀ hY).mp hh
  exact (markedMemoryProductMass_le_reciprocal hv hV hq0 hq1 p hp hlarge).trans
    (div_le_div_of_nonneg_left (by positivity) hY hb)

end ArtinMatthews
