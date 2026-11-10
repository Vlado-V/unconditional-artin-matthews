module

public import ArtinMatthews.GiantMarkedBilinearFinite
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Damping at the actual common quotient after selecting one prime in each
band. The selected labels and original reciprocal normalizers are retained. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def giantMarkedQuotientDamping {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (h : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (∑ j, bandCount (P j) h) * markedMajorLabelMass P

def giantMarkedQuotientDampedSum {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M N : Finset ℕ) (α β F : ℕ → ℂ) : ℂ :=
  ∑ a ∈ markedMajorLabelSet P, ∑ m ∈ M, ∑ n ∈ N,
    if a ∣ m * n - 1 then
      α m * β n * F ((m * n - 1) / a) *
        (1 / 2 : ℂ) ^ (∑ j, bandCount (P j) ((m * n - 1) / a)) *
        (markedMajorLabelMass P : ℂ)
    else 0

def giantMarkedQuotientWeight {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (u : ℕ) : ℝ :=
  ∑ a ∈ markedMajorLabelSet P,
    if a ∣ u then giantMarkedQuotientDamping P (u / a) else 0

theorem giantMarkedSelectedDivisors_mul {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (t : (j : J) → ↥(P j)) (h : ℕ) (j : J) :
    activeDivisors (P j) (markedPrimeBandProduct P t * h) =
      insert (t j : ℕ) (activeDivisors (P j) h) := by
  classical
  ext p
  simp only [activeDivisors, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hd⟩
    rcases (hP j p hp).dvd_mul.mp hd with hd | hd
    · obtain ⟨i, _, hpi⟩ := ((hP j p hp).prime.dvd_finsetProd_iff
          (fun i => (t i : ℕ))).mp hd
      have heq := ((hP i _ (t i).2).dvd_iff_eq (hP j p hp).ne_one).mp hpi
      have hji : j = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdis hne) hp (heq ▸ (t i).2)
      subst i
      exact Or.inl heq.symm
    · exact Or.inr ⟨hp, hd⟩
  · rintro (rfl | ⟨hp, hd⟩)
    · exact ⟨(t j).2, dvd_mul_of_dvd_left
        (Finset.dvd_prod_of_mem (fun i => (t i : ℕ)) (Finset.mem_univ j)) h⟩
    · exact ⟨hp, dvd_mul_of_dvd_right hd _⟩

theorem giantMarkedSelectedBandCount_sub_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (t : (j : J) → ↥(P j)) (h : ℕ) (j : J) :
    bandCount (P j) (markedPrimeBandProduct P t * h) - 1 ≤ bandCount (P j) h := by
  rw [bandCount, giantMarkedSelectedDivisors_mul P hP hdis t]
  have hc := Finset.card_insert_le (a := (t j : ℕ)) (s := activeDivisors (P j) h)
  change _ ≤ (activeDivisors (P j) h).card
  omega

theorem giantMarkedSelectedBandCount_sub_eq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (t : (j : J) → ↥(P j)) (h : ℕ) (j : J)
    (hsq : ¬(t j : ℕ) ^ 2 ∣ markedPrimeBandProduct P t * h) :
    bandCount (P j) (markedPrimeBandProduct P t * h) - 1 = bandCount (P j) h := by
  have hn : (t j : ℕ) ∉ activeDivisors (P j) h := by
    intro hj
    have hh := (Finset.mem_filter.mp hj).2
    apply hsq
    rw [pow_two]
    exact mul_dvd_mul
      (Finset.dvd_prod_of_mem (fun i => (t i : ℕ)) (Finset.mem_univ j)) hh
  simp only [bandCount, giantMarkedSelectedDivisors_mul P hP hdis t h j,
    Finset.card_insert_of_notMem hn, Nat.add_sub_cancel]

theorem giantMarkedLabelDamping_eq_real {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (u : ℕ) :
    giantMarkedLabelDamping P (fun j => bandReciprocalMass (P j)) u =
      (((1 / 2 : ℝ) ^ (∑ j, (bandCount (P j) u - 1)) * markedMajorLabelMass P : ℝ) : ℂ) := by
  rw [giantMarkedLabelDamping, markedMajorLabelMass]
  push_cast
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem giantMarkedQuotientDampedSum_eq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M N : Finset ℕ) (α β F : ℕ → ℂ)
    (hF : ∀ j p, p ∈ P j → ∀ h, F (p * h) = F h) :
    giantMarkedQuotientDampedSum P M N α β F =
      ∑ m ∈ M, ∑ n ∈ N, α m * β n * F (m * n - 1) *
        (giantMarkedQuotientWeight P (m * n - 1) : ℂ) := by
  classical
  unfold giantMarkedQuotientDampedSum giantMarkedQuotientWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  let u := m * n - 1
  change (if a ∣ u then _ else 0) = α m * β n * F u *
    ((if a ∣ u then giantMarkedQuotientDamping P (u / a) else 0 : ℝ) : ℂ)
  by_cases hd : a ∣ u
  · have heq : F u = F (u / a) := by
      calc
        F u = F (a * (u / a)) := congrArg F (Nat.mul_div_cancel' hd).symm
        _ = F (u / a) := ?_
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
      by_cases hzero : u / markedPrimeBandProduct P t = 0
      · simp only [hzero, mul_zero]
      · exact marked_invariant_finset_product Finset.univ (fun j => (t j : ℕ)) F
          (fun j _ => (hP j _ (t j).2).pos)
          (fun j _ k _ => hF j _ (t j).2 k) (Nat.pos_of_ne_zero hzero)
    simp only [hd, ite_true, heq, giantMarkedQuotientDamping]
    push_cast
    ring
  · simp only [hd, ite_false, Complex.ofReal_zero, mul_zero]

end ArtinMatthews
