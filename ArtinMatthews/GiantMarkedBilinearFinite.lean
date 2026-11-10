module

public import ArtinMatthews.MarkedTypeIIFinite
public import ArtinMatthews.MarkedMajorLabelPolynomial
public import ArtinMatthews.MarkedMajorLabelSplit
public import ArtinMatthews.MarkedTypeIIArithmetic
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

/-! Exact finite passage from the literal marking weight to the determinant
square. The selected prime products, damping, normalizers and collision term
are retained. No determinant saving or graph transference is assumed here. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators ComplexConjugate

def giantMarkedLabelDamping {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (u : ℕ) : ℂ :=
  ∏ j, (1 / 2 : ℂ) ^ (bandCount (P j) u - 1) / (V j : ℂ)

theorem giantMarkedBandProduct_dvd_iff {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (t : (j : J) → ↥(P j)) (u : ℕ) :
    markedPrimeBandProduct P t ∣ u ↔ ∀ j, (t j : ℕ) ∣ u := by
  constructor
  · intro hd j
    exact (Finset.dvd_prod_of_mem (fun i => (t i : ℕ)) (Finset.mem_univ j)).trans hd
  · intro hd
    apply Fintype.prod_dvd_of_isRelPrime
    · intro i j hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (Nat.coprime_primes (hP i _ (t i).2) (hP j _ (t j).2)).mpr
      intro heq
      exact Finset.disjoint_left.mp (hdis hij) (t i).2 (heq ▸ (t j).2)
    · exact hd

theorem giantMarkedBandWeight_selected (P : Finset ℕ) (V : ℝ) (u : ℕ) :
    (bandWeight P V u : ℂ) =
      ∑ p : ↥P, if (p : ℕ) ∣ u then
        (1 / 2 : ℂ) ^ (bandCount P u - 1) / (V : ℂ) else 0 := by
  classical
  have h := congrArg (fun x : ℝ => (x : ℂ)) (bandWeight_eq_selected_sum P V u)
  push_cast at h
  calc
    _ = ∑ p ∈ P, if p ∣ u then
        (1 / 2 : ℂ) ^ (bandCount P u - 1) / (V : ℂ) else 0 := by
      simpa only [activeDivisors, Finset.sum_filter] using h
    _ = _ := (Finset.sum_coe_sort P (fun p : ℕ => if p ∣ u then
      (1 / 2 : ℂ) ^ (bandCount P u - 1) / (V : ℂ) else 0)).symm

/-- The actual single-array weight is a sum over numeric selected labels.
The common damping still depends on the original predecessor. -/
theorem giantMarkedWeight_label_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (V : J → ℝ) (u : ℕ) :
    (divisorWeight Finset.univ P V u : ℂ) =
      ∑ a ∈ markedMajorLabelSet P,
        if a ∣ u then giantMarkedLabelDamping P V u else 0 := by
  classical
  rw [markedMajorLabelSet_sum P hP hdis]
  calc
    _ = ∏ j, ∑ p : ↥(P j), if (p : ℕ) ∣ u then
        (1 / 2 : ℂ) ^ (bandCount (P j) u - 1) / (V j : ℂ) else 0 := by
      push_cast [divisorWeight]
      exact Finset.prod_congr rfl (fun j _ => giantMarkedBandWeight_selected (P j) (V j) u)
    _ = ∑ t : (j : J) → ↥(P j), ∏ j, if (t j : ℕ) ∣ u then
        (1 / 2 : ℂ) ^ (bandCount (P j) u - 1) / (V j : ℂ) else 0 :=
      Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [Fintype.prod_ite_zero, ← giantMarkedBandProduct_dvd_iff P hP hdis,
        giantMarkedLabelDamping]

def giantMarkedEndpoint (a m n : ℕ) : MarkedTypeIIEndpoint := ⟨a, m, n⟩

def giantMarkedEndpoints {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M N : Finset ℕ) : Finset MarkedTypeIIEndpoint := by
  classical
  exact (markedMajorLabelSet P ×ˢ (M ×ˢ N)).image
    (fun t => giantMarkedEndpoint t.1 t.2.1 t.2.2)

theorem giantMarkedEndpoints_sum {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M N : Finset ℕ) (c : MarkedTypeIIEndpoint → ℂ) :
    (∑ e ∈ giantMarkedEndpoints P M N, c e) =
      ∑ a ∈ markedMajorLabelSet P, ∑ m ∈ M, ∑ n ∈ N,
        c (giantMarkedEndpoint a m n) := by
  classical
  rw [giantMarkedEndpoints, Finset.sum_image]
  · simp only [Finset.sum_product]
  · intro a _ b _ hab
    cases a with
    | mk a mn =>
      cases mn with
      | mk m n =>
        cases b with
        | mk b rs =>
          cases rs with
          | mk r s =>
            cases hab
            rfl

def giantMarkedEndpointCoefficient {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (α β : ℕ → ℂ)
    (e : MarkedTypeIIEndpoint) : ℂ :=
  α e.leftFactor * β e.rightFactor * giantMarkedLabelDamping P V (e.value - 1)

/-- Exact elimination of the positive label divisor in the linear sum.
The endpoint function is evaluated at the common quotient only by its stated
invariance. Zero quotients and the endpoint `value = 1` are included. -/
theorem giant_marked_endpoint_quotient (E : Finset MarkedTypeIIEndpoint)
    (B : ℕ) (c : MarkedTypeIIEndpoint → ℂ) (F : ℕ → ℂ)
    (he : ∀ e ∈ E, 0 < e.label ∧ 1 ≤ e.value ∧ e.value ≤ e.label * B)
    (hF : ∀ e ∈ E, ∀ h, F (e.label * h) = F h) :
    (∑ e ∈ E, if e.label ∣ e.value - 1 then F (e.value - 1) * c e else 0) =
      ∑ h ∈ Finset.range B, F h * markedTypeIIEndpointSum E c h := by
  classical
  simp only [markedTypeIIEndpointSum, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e heE
  by_cases hd : e.label ∣ e.value - 1
  · rw [ite_eq_left hd]
    let q := (e.value - 1) / e.label
    have hsub : e.value - 1 = e.label * q := (Nat.mul_div_cancel' hd).symm
    have hrep : e.represents q := by
      unfold MarkedTypeIIEndpoint.represents
      have hv := (he e heE).2.1
      omega
    have hq : q ∈ Finset.range B :=
      marked_quotient_mem_range_of_mul_bound hrep (he e heE).2.2
    rw [Finset.sum_eq_single q]
    · rw [ite_eq_left hrep, hsub, hF e heE]
    · intro h _ hhq
      rw [ite_eq_right]
      intro hh
      exact hhq (marked_common_quotient_unique (he e heE).1 hh hrep)
    · exact fun h => (h hq).elim
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro h _
    rw [ite_eq_right]
    intro hh
    apply hd
    exact ⟨h, by
      change e.value = 1 + e.label * h at hh
      omega⟩

theorem giant_marked_bilinear_selected {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (V : J → ℝ) (M N : Finset ℕ) (α β F : ℕ → ℂ) :
    (∑ m ∈ M, ∑ n ∈ N, α m * β n * F (m*n-1) *
      (divisorWeight Finset.univ P V (m*n-1) : ℂ)) =
      ∑ e ∈ giantMarkedEndpoints P M N,
        if e.label ∣ e.value - 1 then
          F (e.value - 1) * giantMarkedEndpointCoefficient P V α β e else 0 := by
  classical
  rw [giantMarkedEndpoints_sum]
  simp_rw [giantMarkedWeight_label_sum P hP hdis, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := N) (t := markedMajorLabelSet P)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  change α m * β n * F (m*n-1) *
      (if a ∣ m*n-1 then giantMarkedLabelDamping P V (m*n-1) else 0) =
    if a ∣ m*n-1 then
      F (m*n-1) * (α m * β n * giantMarkedLabelDamping P V (m*n-1)) else 0
  by_cases hd : a ∣ m*n-1
  · simp only [hd, ite_true]
    ring
  · simp only [hd, ite_false, mul_zero]

theorem giantMarkedEndpoints_bounds {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M N : Finset ℕ) (B : ℕ) (hM : ∀ m ∈ M, 0 < m)
    (hN : ∀ n ∈ N, 0 < n)
    (hMN : ∀ a ∈ markedMajorLabelSet P, ∀ m ∈ M, ∀ n ∈ N, m*n ≤ a*B) :
    ∀ e ∈ giantMarkedEndpoints P M N,
      0 < e.label ∧ 1 ≤ e.value ∧ e.value ≤ e.label * B := by
  classical
  intro e he
  obtain ⟨⟨a,m,n⟩, ht, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨ha, hm, hn⟩ := by
    simpa only [Finset.mem_product] using ht
  have ha0 := markedMajorLabelSet_pos P hP ha
  refine ⟨ha0, Nat.mul_pos (hM m hm) (hN n hn), ?_⟩
  change m*n ≤ a*B
  exact hMN a ha m hm n hn

/-- The actual marked bilinear sum before Cauchy, with its bounded function
on the common quotient and no change of array normalization. -/
theorem giant_marked_bilinear_quotient {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (V : J → ℝ) (M N : Finset ℕ) (B : ℕ) (α β F : ℕ → ℂ)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n)
    (hMN : ∀ a ∈ markedMajorLabelSet P, ∀ m ∈ M, ∀ n ∈ N, m*n ≤ a*B)
    (hF : ∀ j p, p ∈ P j → ∀ h, F (p*h) = F h) :
    (∑ m ∈ M, ∑ n ∈ N, α m * β n * F (m*n-1) *
      (divisorWeight Finset.univ P V (m*n-1) : ℂ)) =
      ∑ h ∈ Finset.range B, F h * markedTypeIIEndpointSum
        (giantMarkedEndpoints P M N) (giantMarkedEndpointCoefficient P V α β) h := by
  classical
  rw [giant_marked_bilinear_selected P hP hdis]
  apply giant_marked_endpoint_quotient
    (giantMarkedEndpoints P M N) B (giantMarkedEndpointCoefficient P V α β) F
    (giantMarkedEndpoints_bounds P hP M N B hM hN hMN)
  intro e he h
  obtain ⟨⟨a,m,n⟩, ht, rfl⟩ := Finset.mem_image.mp he
  have ha : a ∈ markedMajorLabelSet P := (Finset.mem_product.mp ht).1
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
  change F ((∏ j, (t j : ℕ))*h) = F h
  by_cases hh : h = 0
  · simp only [hh, mul_zero]
  · exact marked_invariant_finset_product Finset.univ (fun j => (t j : ℕ)) F
      (fun j _ => (hP j _ (t j).2).pos)
      (fun j _ k _ => hF j _ (t j).2 k) (Nat.pos_of_ne_zero hh)

/-- Literal marked Cauchy square, with the sharp quotient range supplied by
`m*n ≤ a*B` for the actual selected label `a`. -/
theorem giant_marked_bilinear_square {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (V : J → ℝ) (M N : Finset ℕ) (B : ℕ) (α β F : ℕ → ℂ)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n)
    (hMN : ∀ a ∈ markedMajorLabelSet P, ∀ m ∈ M, ∀ n ∈ N, m*n ≤ a*B)
    (hF : ∀ j p, p ∈ P j → ∀ h, F (p*h) = F h)
    (hFnorm : ∀ h ∈ Finset.range B, ‖F h‖ ≤ 1) :
    ‖∑ m ∈ M, ∑ n ∈ N, α m * β n * F (m*n-1) *
      (divisorWeight Finset.univ P V (m*n-1) : ℂ)‖ ^ 2 ≤
      (B : ℝ) * (markedTypeIIDeterminantSum (giantMarkedEndpoints P M N)
          (giantMarkedEndpointCoefficient P V α β) +
        markedTypeIICollisionSum (giantMarkedEndpoints P M N) (Finset.range B)
          (giantMarkedEndpointCoefficient P V α β)).re := by
  rw [giant_marked_bilinear_quotient P hP hdis V M N B α β F hM hN hMN hF]
  have hc := marked_typeII_cauchy (giantMarkedEndpoints P M N) (Finset.range B)
    (giantMarkedEndpointCoefficient P V α β) F hFnorm
  rw [marked_typeII_square_eq_determinant_add_collisions_of_mul_bound _ _ _
    (giantMarkedEndpoints_bounds P hP M N B hM hN hMN)] at hc
  simpa only [Finset.card_range] using hc

/-- A genuine determinant-and-collision input bounds the original marked
bilinear sum; the input is not a hypothesis about the desired prime sum. -/
theorem giant_marked_bilinear_norm_sq_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (V : J → ℝ) (M N : Finset ℕ) (B : ℕ) (α β F : ℕ → ℂ)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n)
    (hMN : ∀ a ∈ markedMajorLabelSet P, ∀ m ∈ M, ∀ n ∈ N, m*n ≤ a*B)
    (hF : ∀ j p, p ∈ P j → ∀ h, F (p*h) = F h)
    (hFnorm : ∀ h ∈ Finset.range B, ‖F h‖ ≤ 1)
    {D C : ℝ}
    (hD : ‖markedTypeIIDeterminantSum (giantMarkedEndpoints P M N)
      (giantMarkedEndpointCoefficient P V α β)‖ ≤ D)
    (hC : ‖markedTypeIICollisionSum (giantMarkedEndpoints P M N) (Finset.range B)
      (giantMarkedEndpointCoefficient P V α β)‖ ≤ C) :
    ‖∑ m ∈ M, ∑ n ∈ N, α m * β n * F (m*n-1) *
      (divisorWeight Finset.univ P V (m*n-1) : ℂ)‖ ^ 2 ≤ (B : ℝ) * (D+C) := by
  apply (giant_marked_bilinear_square P hP hdis V M N B α β F hM hN hMN hF hFnorm).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  exact (Complex.re_le_norm _).trans ((norm_add_le _ _).trans (add_le_add hD hC))

end ArtinMatthews
