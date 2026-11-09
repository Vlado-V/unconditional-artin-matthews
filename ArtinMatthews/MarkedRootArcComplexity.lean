module

public import ArtinMatthews.MarkedRootArcClipped
public import ArtinMatthews.MarkedRawBadRootArcMajorant


set_option backward.privateInPublic true
@[expose] public section

/-! The literal interval coefficient mass of the positive first/beta
arc majorants. Each nonzero frequency q costs |q|+1 closed intervals. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPairRootArcComplexity (Q : Finset ℤ) (T : ℤ) : ℝ :=
  ∑ p : Q × Q,if p.1.1=p.2.1 then 0 else (((p.1.1-p.2.1)*T).natAbs:ℝ)+1

def markedFirstRootArcComplexity {I : Type*} [Fintype I] (D : I → ℕ) (L : ℕ) : ℝ :=
  Finset.univ.sum (fun p : I × ↥(Finset.Icc 1 L) => (((D p.1*p.2.1:ℕ):ℤ).natAbs:ℝ)+1)

theorem markedPairRootArcComplexity_nonneg (Q : Finset ℤ) (T : ℤ) :
    0 ≤ markedPairRootArcComplexity Q T := by
  unfold markedPairRootArcComplexity
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem markedPairRootArcComplexity_le (Q : Finset ℤ) (T : ℤ) {R : ℝ}
    (hR : 1 ≤ R) (hcard : (Q.card:ℝ) ≤ R)
    (hQ : ∀ u ∈ Q,|(u:ℝ)| ≤ R) (hT : |(T:ℝ)| ≤ R) :
    markedPairRootArcComplexity Q T ≤ 3*R^4 := by
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hterm (p : Q × Q) :
      (if p.1.1=p.2.1 then (0:ℝ) else (((p.1.1-p.2.1)*T).natAbs:ℝ)+1) ≤ 3*R^2 := by
    split_ifs
    · positivity
    · have hu := hQ p.1.1 p.1.2
      have hv := hQ p.2.1 p.2.2
      have hd : |(p.1.1:ℝ)-(p.2.1:ℝ)| ≤ 2*R := (abs_sub _ _).trans (by linarith)
      have hp := mul_le_mul hd hT (abs_nonneg _) (by positivity : 0 ≤ 2*R)
      simp only [Nat.cast_natAbs,Int.cast_abs,Int.cast_mul,Int.cast_sub,abs_mul]
      nlinarith [sq_nonneg (R-1)]
  calc
    _ ≤ ∑ _p : Q × Q,3*R^2 := Finset.sum_le_sum (fun p _ => hterm p)
    _ = (Q.card:ℝ)^2*(3*R^2) := by simp [Fintype.card_prod,Fintype.card_coe,pow_two]
    _ ≤ R^2*(3*R^2) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (by positivity)
    _ = _ := by ring

theorem markedFirstRootArcComplexity_le {I : Type*} [Fintype I]
    (D : I → ℕ) (L : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hcard : (Fintype.card I:ℝ) ≤ R) (hL : (L:ℝ) ≤ R) (hD : ∀ i,(D i:ℝ) ≤ R) :
    markedFirstRootArcComplexity D L ≤ 2*R^4 := by
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hterm (p : I × ↥(Finset.Icc 1 L)) :
      ((((D p.1*p.2.1:ℕ):ℤ).natAbs:ℝ)+1) ≤ 2*R^2 := by
    have hl : (p.2.1:ℝ) ≤ R := (Nat.cast_le.mpr (Finset.mem_Icc.mp p.2.2).2).trans hL
    have hp := mul_le_mul (hD p.1) hl (Nat.cast_nonneg _) hR₀
    simp only [Int.natAbs_mul,Int.natAbs_natCast,Nat.cast_mul]
    nlinarith [sq_nonneg (R-1)]
  unfold markedFirstRootArcComplexity
  calc
    _ ≤ ∑ _p : I × ↥(Finset.Icc 1 L),2*R^2 := Finset.sum_le_sum (fun p _ => hterm p)
    _ = (Fintype.card I:ℝ)*L*(2*R^2) := by simp [Fintype.card_prod,Fintype.card_coe]
    _ ≤ (R*R)*(2*R^2) := mul_le_mul_of_nonneg_right
      (mul_le_mul hcard hL (Nat.cast_nonneg _) hR₀) (by positivity)
    _ = _ := by ring

def markedRawFirstRootArcComplexity {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ) : ℝ :=
  markedFirstRootArcComplexity
    (fun o : markedRawDyadicOmissions a d₀ => markedSourceCopiedProduct (markedRawNumericActive a) o.1)
    ⌊Y^(1/5:ℝ)⌋₊

def markedRawBetaRootArcComplexity {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) : ℝ :=
  ∑ p : Finset J × J,
    if p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2) then
      (∑ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x,
        markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t *
          markedPairRootArcComplexity (markedRawDirtyFullTrials e x a (p.1.erase p.2))
            (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t)) /
        Real.exp (-((Real.log x)^(e p.2))/4)
    else 0

def markedRawBadRootArcComplexity {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) : ℝ :=
  markedRawFirstRootArcComplexity a d₀ Y+markedRawBetaRootArcComplexity e x a

end
end ArtinMatthews
