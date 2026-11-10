module

public import ArtinMatthews.ShiftedPairCount
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-(d,D) pair count in the original, unscaled variables. -/
namespace ArtinMatthews

/-- This superset contains every pair with actual gcd d and actual common
prime part D, retaining only the divisibilities needed for the bound. -/
def shiftedDivisiblePairs (B d D : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
    (fun p => p.1≠p.2 ∧ d∣p.1 ∧ d∣p.2 ∧ Nat.ModEq D p.1 p.2)

theorem shiftedDivisiblePairs_card_le (B d D : ℕ)
    (hd : 0<d) (hD : 0<D) (hdD : d∣D) :
    (shiftedDivisiblePairs B d D).card ≤ 2*((B/d)*(B/D)) := by
  let f : ℕ×ℕ → ℕ×ℕ := fun p => (p.1/d,p.2/d)
  have hf : Set.MapsTo f (shiftedDivisiblePairs B d D)
      (shiftedOffDiagonalPairs (B/d) (D/d)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hne,hp1,hp2,hmod⟩
    rcases Finset.mem_product.mp hp with ⟨h1,h2⟩
    rw [Finset.mem_Icc] at h1 h2
    change f p ∈ shiftedOffDiagonalPairs (B/d) (D/d)
    simp only [shiftedOffDiagonalPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, f]
    refine ⟨⟨⟨Nat.div_pos (Nat.le_of_dvd h1.1 hp1) hd, Nat.div_le_div_right h1.2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd h2.1 hp2) hd, Nat.div_le_div_right h2.2⟩⟩,?_,?_⟩
    · intro he
      apply hne
      calc
        p.1 = d*(p.1/d) := (Nat.mul_div_cancel' hp1).symm
        _ = d*(p.2/d) := by rw [he]
        _ = p.2 := Nat.mul_div_cancel' hp2
    · apply Nat.ModEq.mul_left_cancel' hd.ne'
      simpa only [Nat.mul_div_cancel' hdD, Nat.mul_div_cancel' hp1,
        Nat.mul_div_cancel' hp2] using hmod
  have hi : Set.InjOn f (shiftedDivisiblePairs B d D) := by
    intro p hp q hq he
    rcases (Finset.mem_filter.mp hp).2 with ⟨_,hp1,hp2,_⟩
    rcases (Finset.mem_filter.mp hq).2 with ⟨_,hq1,hq2,_⟩
    have hx : p.1/d=q.1/d := congrArg Prod.fst he
    have hy : p.2/d=q.2/d := congrArg Prod.snd he
    apply Prod.ext
    · simpa only [Nat.mul_div_cancel' hp1,Nat.mul_div_cancel' hq1] using
        congrArg (fun n => d*n) hx
    · simpa only [Nat.mul_div_cancel' hp2,Nat.mul_div_cancel' hq2] using
        congrArg (fun n => d*n) hy
  have hbound := (Finset.card_le_card_of_injOn f hf hi).trans
    (shiftedOffDiagonalPairs_card_le (B/d) (D/d)
      (Nat.div_pos (Nat.le_of_dvd hD hdD) hd))
  simpa only [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hdD] using hbound

/-- The full M²/(dD) saving; using B=2M only changes the numerical constant. -/
theorem shiftedDivisiblePairs_card_real (B d D : ℕ)
    (hd : 0<d) (hD : 0<D) (hdD : d∣D) :
    ((shiftedDivisiblePairs B d D).card : ℝ) ≤ 2*(B : ℝ)^2/((d : ℝ)*(D : ℝ)) := by
  have hdr : (0 : ℝ)<d := by exact_mod_cast hd
  have hDr : (0 : ℝ)<D := by exact_mod_cast hD
  have hdivd : ((B/d : ℕ) : ℝ) ≤ (B : ℝ)/(d : ℝ) := by
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast Nat.div_mul_le_self B d
  have hdivD : ((B/D : ℕ) : ℝ) ≤ (B : ℝ)/(D : ℝ) := by
    apply (le_div_iff₀ hDr).mpr
    exact_mod_cast Nat.div_mul_le_self B D
  have hc : ((shiftedDivisiblePairs B d D).card : ℝ) ≤
      2*((B/d : ℕ) : ℝ)*((B/D : ℕ) : ℝ) := by
    have hh := shiftedDivisiblePairs_card_le B d D hd hD hdD
    exact_mod_cast (show (shiftedDivisiblePairs B d D).card ≤ 2*(B/d)*(B/D) by simpa only [mul_assoc] using hh)
  calc
    _ ≤ 2*((B/d : ℕ) : ℝ)*((B/D : ℕ) : ℝ) := hc
    _ ≤ 2*((B : ℝ)/(d : ℝ))*((B : ℝ)/(D : ℝ)) := by gcongr
    _ = _ := by ring

end ArtinMatthews
