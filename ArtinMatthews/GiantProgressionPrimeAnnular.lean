module

public import ArtinMatthews.GiantProgressionPrimeMass
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Literal rational prime annuli for fixed unit-residue sets, and their
logarithmic mass. Every congruence is tested at the original prime. -/
namespace ArtinMatthews
noncomputable section
open Filter ArithmeticFunction MeasureTheory
open scoped BigOperators Topology

theorem giantUnitPrimeLogCoeff_eq {M : ℕ} (U : Finset (ZMod M)ˣ) (n : ℕ) :
    giantUnitPrimeLogCoeff U n =
      if n.Prime ∧ (n : ZMod M) ∈ U.image (fun a : (ZMod M)ˣ => (a : ZMod M))
      then Real.log n else 0 := by
  classical
  unfold giantUnitPrimeLogCoeff
  by_cases hp : n.Prime
  · simp only [hp, ite_true, true_and]
    by_cases hU : (n : ZMod M) ∈ U.image (fun a : (ZMod M)ˣ => (a : ZMod M))
    · rw [ite_eq_left hU]
      obtain ⟨a,ha,haz⟩ := Finset.mem_image.mp hU
      rw [Finset.sum_eq_single a]
      · simp [vonMangoldt.residueClass, haz.symm, vonMangoldt_apply_prime hp]
      · intro b _ hba
        have hnb : (n : ZMod M) ≠ (b : ZMod M) := by
          intro h
          exact hba (Units.ext (haz.trans h)).symm
        simp [vonMangoldt.residueClass,hnb]
      · intro h
        exact (h ha).elim
    · rw [ite_eq_right hU]
      apply Finset.sum_eq_zero
      intro a ha
      have hna : (n : ZMod M) ≠ (a : ZMod M) := by
        intro h
        exact hU (Finset.mem_image.mpr ⟨a,ha,h.symm⟩)
      simp [vonMangoldt.residueClass,hna]
  · simp [hp]

def giantUnitAnnularPrimes {M : ℕ} (U : Finset (ZMod M)ˣ) (a b x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc ⌊x*a⌋₊ ⌊x*b⌋₊).filter (fun n => n.Prime ∧
    (n : ZMod M) ∈ U.image (fun u : (ZMod M)ˣ => (u : ZMod M)))

def giantUnitPrimeAnnular {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ p ∈ giantUnitAnnularPrimes U a b x, Φ (p/x)

theorem giantUnitPrimeLogAnnular_eq {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (a b x : ℝ) :
    giantUnitPrimeLogAnnular U Φ a b x =
      ∑ p ∈ giantUnitAnnularPrimes U a b x, Real.log p * Φ (p/x) := by
  classical
  simp only [giantUnitPrimeLogAnnular, OAI.SevenEighths.PNT.AnnularPrimeMass.annularSum,
    giantUnitPrimeLogCoeff_eq, giantUnitAnnularPrimes, Finset.sum_filter, ite_mul, zero_mul]

theorem giantUnitAnnularPrimes_bounds {M : ℕ} (U : Finset (ZMod M)ˣ)
    {a b x : ℝ} (ha : 0≤a) (hab : a≤b) (hx : 0<x) {p : ℕ}
    (hp : p ∈ giantUnitAnnularPrimes U a b x) :
    x*a < (p : ℝ) ∧ (p : ℝ) ≤ x*b := by
  have h := (Finset.mem_filter.mp hp).1
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp (Finset.mem_Ioc.mp h).1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp (Finset.mem_Ioc.mp h).2⟩

theorem giantUnitAnnularPrimes_ratio {M : ℕ} (U : Finset (ZMod M)ˣ)
    {a b x : ℝ} (ha : 0≤a) (hab : a≤b) (hx : 0<x) {p : ℕ}
    (hp : p ∈ giantUnitAnnularPrimes U a b x) : (p : ℝ)/x ∈ Set.Icc a b := by
  have h := giantUnitAnnularPrimes_bounds U ha hab hx hp
  exact ⟨(le_div_iff₀ hx).mpr (by linarith [h.1]),
    (div_le_iff₀ hx).mpr (by linarith [h.2])⟩

theorem giantUnitAnnularPrimes_card_bound {M : ℕ} (U : Finset (ZMod M)ˣ)
    {C a b x : ℝ} (hC : 0≤C)
    (hbound : ∀ N : ℕ, cumsum (giantUnitPrimeLogCoeff U) N ≤ C*N)
    (ha : 0<a) (hab : a≤b) (hx : 1≤x) (hxa : 1<x*a) :
    ((giantUnitAnnularPrimes U a b x).card : ℝ)/x ≤ C*(b+1)/Real.log (x*a) := by
  have hx0 : 0<x := zero_lt_one.trans_le hx
  have hlog : 0<Real.log (x*a) := Real.log_pos hxa
  have hlo : Real.log (x*a)*(giantUnitAnnularPrimes U a b x).card ≤
      ∑ p ∈ giantUnitAnnularPrimes U a b x, Real.log p := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    exact Real.log_le_log (mul_pos hx0 ha) (giantUnitAnnularPrimes_bounds U ha.le hab hx0 hp).1.le
  have hhi : (∑ p ∈ giantUnitAnnularPrimes U a b x, Real.log p) ≤
      cumsum (giantUnitPrimeLogCoeff U) (⌊x*b⌋₊+1) := by
    have he := giantUnitPrimeLogAnnular_eq U (fun _ => 1) a b x
    simp only [mul_one] at he
    rw [← he]
    unfold giantUnitPrimeLogAnnular OAI.SevenEighths.PNT.AnnularPrimeMass.annularSum cumsum
    simp only [mul_one]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      exact Finset.mem_range.mpr (by omega)
    · intro n _ _
      exact giantUnitPrimeLogCoeff_nonneg U n
  have hcum := OAI.SevenEighths.PNT.AnnularPrimeMass.scaledCumulative_bound
    (giantUnitPrimeLogCoeff_nonneg U) hC hbound hx (ha.le.trans hab) (le_refl b)
  have hcum' : cumsum (giantUnitPrimeLogCoeff U) (⌊x*b⌋₊+1)/x ≤ C*(b+1) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,
      OAI.SevenEighths.PNT.AnnularPrimeMass.scaledCumulative,
      OAI.SevenEighths.PNT.AnnularPrimeMass.cumulative] using hcum)
  apply (le_div_iff₀ hlog).mpr
  calc
    _ = (Real.log (x*a)*(giantUnitAnnularPrimes U a b x).card)/x := by ring
    _ ≤ (∑ p ∈ giantUnitAnnularPrimes U a b x, Real.log p)/x := div_le_div_of_nonneg_right hlo hx0.le
    _ ≤ cumsum (giantUnitPrimeLogCoeff U) (⌊x*b⌋₊+1)/x := div_le_div_of_nonneg_right hhi hx0.le
    _ ≤ _ := hcum'

end
end ArtinMatthews
