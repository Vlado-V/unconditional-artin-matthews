module

public import ArtinMatthews.GiantCandidatePrimeStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The exact total removed logarithm is expressed by factorial
valuations. Its bound sums over all integers in the interval. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateRemovedLog_eq_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    giantCandidateRemovedLog P m =
      ∑ p ∈ P, (m.factorization p:ℝ)*Real.log (p:ℝ) := by
  classical
  let d : ℕ := ∏ p ∈ P,p
  let f := m.factorization.filter (fun p => p ∣ d)
  have he : (giantCandidatePrimePart P m).factorization = f :=
    factorization_commonPrimePart m d
  have hs : f.support ⊆ P := by
    intro p hp
    have hne := Finsupp.mem_support_iff.mp hp
    have hd : p ∣ d := by
      by_contra hd
      exact hne (by simp [f,hd])
    have hmp : m.factorization p ≠ 0 := by
      simpa only [f,Finsupp.filter_apply,ite_eq_left hd] using hne
    have hprime : p.Prime := by
      by_contra h
      exact hmp (Nat.factorization_eq_zero_of_not_prime m h)
    obtain ⟨q,hq,hpq⟩ := (hprime.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hd
    have h : p = q := (Nat.dvd_prime (hP q hq)).mp hpq |>.resolve_left hprime.ne_one
    simpa only [h] using hq
  unfold giantCandidateRemovedLog
  rw [Real.log_nat_eq_sum_factorization,he,Finsupp.sum_of_support_subset f hs _ (by simp)]
  apply sum_congr rfl
  intro p hp
  have hd : p ∣ d := dvd_prod_of_mem (fun q : ℕ => q) hp
  simp [f,hd]

theorem giantCandidateRemovedLog_sum_eq_factorial (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ m ∈ Ioc 0 N, giantCandidateRemovedLog P m) =
      ∑ p ∈ P, (N.factorial.factorization p:ℝ)*Real.log (p:ℝ) := by
  classical
  simp_rw [giantCandidateRemovedLog_eq_sum P hP]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [← sum_mul,← Nat.cast_sum]
  have hi : Ioc (0:ℕ) N = Ico 1 (N+1) := by
    ext m
    simp only [mem_Ioc,mem_Ico]
    omega
  rw [hi,← Nat.factorization_prod_apply (fun m hm =>
    Nat.ne_of_gt (zero_lt_one.trans_le (mem_Ico.mp hm).1)),prod_Ico_id_eq_factorial]

theorem giantCandidateRemovedLog_sum_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ m ∈ Ioc 0 N, giantCandidateRemovedLog P m) ≤
      (N:ℝ)*∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ)-1) := by
  rw [giantCandidateRemovedLog_sum_eq_factorial P hP,mul_sum]
  apply sum_le_sum
  intro p hp
  have hval : (N.factorial.factorization p:ℝ) ≤ (N:ℝ)/((p:ℝ)-1) := by
    have hb : (N.factorial.factorization p:ℝ) ≤ ((N/(p-1):ℕ):ℝ) :=
      Nat.cast_le.mpr (Nat.factorization_factorial_le_div_pred (hP p hp) N)
    exact hb.trans (by simpa only [Nat.cast_sub (hP p hp).one_le,Nat.cast_one] using
      (Nat.cast_div_le (α := ℝ) (m := N) (n := p-1)))
  calc
    _ ≤ ((N:ℝ)/((p:ℝ)-1))*Real.log (p:ℝ) :=
      mul_le_mul_of_nonneg_right hval (Real.log_natCast_nonneg _)
    _ = _ := by ring

private theorem factorial_factorization_div_le {p N : ℕ} (hp : p.Prime) :
    N/p ≤ N.factorial.factorization p := by
  let b := Nat.log p N + 2
  have h : Nat.log p N < b := by dsimp [b]; omega
  rw [Nat.factorization_factorial hp h]
  have hb : 1 ∈ Ico 1 b := by
    apply mem_Ico.mpr
    dsimp [b]
    omega
  simpa only [pow_one] using (single_le_sum
    (f := fun i => N/p^i) (fun _ _ => Nat.zero_le _) hb)

theorem giant_candidate_prime_log_reciprocal_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hN : 0 < N)
    (hPtop : ∀ p ∈ P, p ≤ N) :
    (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ)-1)) ≤ 4*Real.log (N:ℝ) := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  apply (mul_le_mul_iff_right₀ hNR).mp
  rw [mul_sum]
  calc
    _ ≤ ∑ p ∈ P, 4*(N.factorial.factorization p:ℝ)*Real.log (p:ℝ) := by
      apply sum_le_sum
      intro p hp
      have hpP := hP p hp
      have hdiv : 0 < N/p := Nat.div_pos (hPtop p hp) hpP.pos
      have htwice : N ≤ 2*p*(N/p) := by
        have hmod := Nat.mod_lt N hpP.pos
        have hadd := Nat.mod_add_div N p
        have hone : p ≤ p*(N/p) := by
          simpa only [mul_one] using Nat.mul_le_mul_left p (show 1 ≤ N/p from hdiv)
        nlinarith
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpP.two_le
      have hpR : (1:ℝ) < p := by linarith
      have hmulR : (N:ℝ) ≤ 4*((p:ℝ)-1)*(N.factorial.factorization p:ℝ) := calc
        _ ≤ 2*(p:ℝ)*((N/p:ℕ):ℝ) := by exact_mod_cast htwice
        _ ≤ 4*((p:ℝ)-1)*((N/p:ℕ):ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (factorial_factorization_div_le hpP))
          (by positivity)
      have hdivR : (N:ℝ)/((p:ℝ)-1) ≤ 4*(N.factorial.factorization p:ℝ) :=
        (div_le_iff₀ (sub_pos.mpr hpR)).mpr (by linarith only [hmulR])
      calc
        _ = ((N:ℝ)/((p:ℝ)-1))*Real.log (p:ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hdivR (Real.log_natCast_nonneg _)
    _ = 4*(∑ m ∈ Ioc 0 N, giantCandidateRemovedLog P m) := by
      rw [giantCandidateRemovedLog_sum_eq_factorial P hP,mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ (N:ℝ)*(4*Real.log (N:ℝ)) := by
      have hsum : (∑ m ∈ Ioc 0 N, giantCandidateRemovedLog P m) ≤ (N:ℝ)*Real.log (N:ℝ) := by
        calc
          _ ≤ ∑ _m ∈ Ioc 0 N, Real.log (N:ℝ) := by
            apply sum_le_sum
            intro m hm
            exact (giantCandidateRemovedLog_le P (mem_Ioc.mp hm).1).trans
              (Real.log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hm).1)
                (Nat.cast_le.mpr (mem_Ioc.mp hm).2))
          _ = _ := by simp [Nat.card_Ioc]
      linarith only [hsum]

theorem giant_candidate_removed_log_actual_bound {L : ℝ} (hL : 0 ≤ L) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hPtop : ∀ p ∈ P, (p:ℝ) ≤ Real.exp (L^(9/20:ℝ))) (N : ℕ) :
    (∑ m ∈ Ioc 0 N, giantCandidateRemovedLog P m) ≤ 4*(N:ℝ)*L^(9/20:ℝ) := by
  let X := ⌊Real.exp (L^(9/20:ℝ))⌋₊
  have hY : 1 ≤ Real.exp (L^(9/20:ℝ)) :=
    Real.one_le_exp_iff.mpr (Real.rpow_nonneg hL _)
  have hX : 0 < X := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa only [Nat.cast_one] using hY)
  have hlogX : Real.log (X:ℝ) ≤ L^(9/20:ℝ) := by
    rw [← Real.log_exp (L^(9/20:ℝ))]
    exact Real.log_le_log (Nat.cast_pos.mpr hX) (Nat.floor_le (Real.exp_pos _).le)
  have htop : ∀ p ∈ P, p ≤ X := fun p hp =>
    (Nat.le_floor_iff (Real.exp_pos _).le).mpr (hPtop p hp)
  calc
    _ ≤ (N:ℝ)*(4*Real.log (X:ℝ)) :=
      (giantCandidateRemovedLog_sum_le P hP N).trans
        (mul_le_mul_of_nonneg_left (giant_candidate_prime_log_reciprocal_le P hP hX htop)
          (Nat.cast_nonneg N))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hlogX (show (0:ℝ) ≤ 4*(N:ℝ) by positivity)]

end
end ArtinMatthews
