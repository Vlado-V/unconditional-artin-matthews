module

public import ArtinMatthews.GiantPrimeShift
public import ArtinMatthews.ExceptionalAsymptotic
public import ArtinMatthews.GiantPrimeNormalization
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite candidates of Section 10.3. The selection predicate
records the literal extra prime condition, such as the cubic condition with
its ramification exclusions. The giant-prime window and shifted smooth test
are the existing ones from (1.2). -/

namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology

def giantSieveWeight (Φ : ℝ → ℝ) (x : ℝ) (p : ℕ) : ℝ :=
  Φ (((p : ℝ)-1)/x)

def giantSieveCandidates {M : ℕ} (U : Finset (ZMod M)ˣ)
    (select : ℕ → Prop) (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : Finset ℕ := by
  classical
  exact (giantPrimeMeanRange T x).filter fun p =>
    (∃ u ∈ U, (u : ZMod M) = (p : ZMod M)) ∧ select p ∧
      giantSieveWeight Φ x p ≠ 0 ∧ (giantPrimeFactors (p-1) x ε).Nonempty

theorem mem_giantSieveCandidates {M : ℕ} {U : Finset (ZMod M)ˣ}
    {select : ℕ → Prop} {ε T x : ℝ} {Φ : ℝ → ℝ} {p : ℕ} :
    p ∈ giantSieveCandidates U select ε Φ T x ↔
      p ∈ giantPrimeMeanRange T x ∧ (∃ u ∈ U, (u : ZMod M) = (p : ZMod M)) ∧
        select p ∧ giantSieveWeight Φ x p ≠ 0 ∧ (giantPrimeFactors (p-1) x ε).Nonempty := by
  classical
  simp only [giantSieveCandidates, Finset.mem_filter]

theorem giantSieveCandidate_prime {M : ℕ} {U : Finset (ZMod M)ˣ}
    {select : ℕ → Prop} {ε T x : ℝ} {Φ : ℝ → ℝ} {p : ℕ}
    (hp : p ∈ giantSieveCandidates U select ε Φ T x) : p.Prime :=
  (Finset.mem_filter.mp (mem_giantSieveCandidates.mp hp).1).2

theorem giantPrimeMeanRange_predecessor_le {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x)
    {p : ℕ} (hp : p ∈ giantPrimeMeanRange T x) : ((p-1 : ℕ):ℝ) ≤ T*x := by
  have hp' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hpred : p-1 ≤ ⌊T*x⌋₊ := by omega
  exact (Nat.cast_le.mpr hpred).trans (Nat.floor_le (mul_nonneg hT hx))

theorem giantSieveCandidate_factor {M : ℕ} {U : Finset (ZMod M)ˣ}
    {select : ℕ → Prop} {ε T x : ℝ} {Φ : ℝ → ℝ} {p : ℕ}
    (hT : 0 ≤ T) (hT₂ : T ≤ 2) (hx : 0 < x)
    (hp : p ∈ giantSieveCandidates U select ε Φ T x) :
    ∃ k Q : ℕ, Q ∈ giantPrimeWindow x ε ∧ p-1 = k*Q ∧ k ≤ exceptionalExponentCutoff ε x := by
  have hpr := giantSieveCandidate_prime hp
  have hn : p-1 ≠ 0 := by have := hpr.two_le; omega
  obtain ⟨Q,hQ⟩ := (mem_giantSieveCandidates.mp hp).2.2.2.2
  rw [giantPrimeFactors_eq_window_filter hn hx.le] at hQ
  obtain ⟨hwindow,hdiv⟩ := Finset.mem_filter.mp hQ
  obtain ⟨k,hpk⟩ := hdiv
  have heq : p-1 = k*Q := by simpa only [Nat.mul_comm] using hpk
  refine ⟨k,Q,hwindow,heq,?_⟩
  have hQlo := (mem_giantPrimeWindow hx.le).mp hwindow |>.2.1
  have hn₂ : ((p-1 : ℕ):ℝ) ≤ 2*x :=
    (giantPrimeMeanRange_predecessor_le hT hx.le (mem_giantSieveCandidates.mp hp).1).trans
      (mul_le_mul_of_nonneg_right hT₂ hx.le)
  have hrpow : (2*x^ε)*x^(1-ε) = 2*x := by
    rw [mul_assoc, ← Real.rpow_add hx, show ε+(1-ε)=1 by ring, Real.rpow_one]
  have hk : (k:ℝ)*x^(1-ε) ≤ (2*x^ε)*x^(1-ε) := by
    calc
      _ ≤ (k:ℝ)*(Q:ℝ) := mul_le_mul_of_nonneg_left hQlo.le (Nat.cast_nonneg _)
      _ = ((p-1 : ℕ):ℝ) := by exact_mod_cast heq.symm
      _ ≤ 2*x := hn₂
      _ = _ := hrpow.symm
  have hk' : (k:ℝ) ≤ 2*x^ε := by
    by_contra! hlt
    exact (not_lt_of_ge hk) (mul_lt_mul_of_pos_right hlt (Real.rpow_pos_of_pos hx _))
  exact Nat.le_floor hk'

theorem giantSieve_support_lt_two (Φ : ℝ → ℝ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ Set.Ioo (1:ℝ) 2) :
    ∃ T : ℝ, 1 < T ∧ T < 2 ∧ Function.support Φ ⊆ Set.Ioo 1 T := by
  by_cases hne : (tsupport Φ).Nonempty
  · have hsup := hs (hc.sSup_mem hne)
    let T := (sSup (tsupport Φ)+2)/2
    have h1 : 1 < T := by dsimp [T]; linarith [hsup.1]
    have h2 : T < 2 := by dsimp [T]; linarith [hsup.2]
    have hT : sSup (tsupport Φ) < T := by dsimp [T]; linarith [hsup.2]
    refine ⟨T,h1,h2,?_⟩
    intro t ht
    have hts := subset_tsupport Φ ht
    exact ⟨(hs hts).1, (le_csSup hc.bddAbove hts).trans_lt hT⟩
  · refine ⟨3/2,by norm_num,by norm_num,?_⟩
    intro t ht
    exact False.elim (hne ⟨t,subset_tsupport Φ ht⟩)

theorem giantSieveCandidates_interval_eventually {M : ℕ} (U : Finset (ZMod M)ˣ)
    (select : ℕ → Prop) (ε : ℝ) (Φ : ℝ → ℝ) {T : ℝ} (hT : T < 2)
    (hs : Function.support Φ ⊆ Set.Ioo 1 T) :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ giantSieveCandidates U select ε Φ T x,
      x < (p:ℝ) ∧ (p:ℝ) ≤ 2*x := by
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (1/(2-T))] with x hx hthresh
  intro p hp
  have hpΦ := (mem_giantSieveCandidates.mp hp).2.2.2.1
  have hsup := hs (show ((p:ℝ)-1)/x ∈ Function.support Φ from hpΦ)
  have hlo := (lt_div_iff₀ hx).mp hsup.1
  have hhi := (div_lt_iff₀ hx).mp hsup.2
  have hmargin := (div_le_iff₀ (sub_pos.mpr hT)).mp hthresh
  exact ⟨by linarith,by nlinarith⟩

theorem giantSieveCandidates_structural_eventually {S : Finset ℤ} (hS : AdmissibleBases S)
    {M : ℕ} (U : Finset (ZMod M)ˣ) (select : ℕ → Prop) (ε : ℝ) (Φ : ℝ → ℝ)
    (hΦ : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) {T : ℝ} (hT₁ : 1 < T) (hT₂ : T < 2)
    (hs : Function.support Φ ⊆ Set.Ioo 1 T) :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ giantSieveCandidates U select ε Φ T x,
      p.Prime ∧ (x < (p:ℝ) ∧ (p:ℝ) ≤ 2*x) ∧
        (∀ a ∈ S, (a : ZMod p) ≠ 0) ∧
        (∃ k Q : ℕ, Q.Prime ∧ p-1 = k*Q ∧ k ≤ exceptionalExponentCutoff ε x) ∧
        (0 ≤ giantSieveWeight Φ x p ∧ giantSieveWeight Φ x p ≤ 1) := by
  let H := ∑ a ∈ S, a.natAbs
  filter_upwards [giantSieveCandidates_interval_eventually U select ε Φ hT₂ hs,
    eventually_ge_atTop (H:ℝ), eventually_gt_atTop (0:ℝ)] with x hinterval hH hx
  intro p hp
  have hpi := hinterval p hp
  obtain ⟨k,Q,hQ,hpk,hkm⟩ := giantSieveCandidate_factor
    (by linarith) hT₂.le hx hp
  refine ⟨giantSieveCandidate_prime hp,hpi,?_,
    ⟨k,Q,(mem_giantPrimeWindow hx.le).mp hQ |>.1,hpk,hkm⟩,hΦ _⟩
  intro a ha hz
  have haH : a.natAbs ≤ H := Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
  have hlt : a.natAbs < p := by
    exact_mod_cast ((Nat.cast_le.mpr haH : (a.natAbs:ℝ) ≤ H).trans hH).trans_lt hpi.1
  have hd : p ∣ a.natAbs := Int.natCast_dvd_natCast.mp
    (Int.dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz))
  exact (not_le_of_gt hlt) (Nat.le_of_dvd (Int.natAbs_pos.mpr (hS.2 a ha).1) hd)

end
end ArtinMatthews
