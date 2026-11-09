module

public import ArtinMatthews.SourceComparisonMarkWeight
public import ArtinMatthews.CubicSamplingArrayTruncation


set_option backward.privateInPublic true
@[expose] public section

/-! The ordinary comparison divisor model retains the ordered list and
its disjoint residual subset as the coefficient index. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

abbrev SourceComparisonDivisorIndex (t : G → ℕ) :=
  Σ _ : ((g : G) → Fin (t g) → ℕ), MarkedWeightedIndex

def sourceComparisonDivisorIndices (P : G → Finset ℕ) (t : G → ℕ) (k : ℕ) :
    Finset (SourceComparisonDivisorIndex t) :=
  (sourceComparisonMarkChoices P t).sigma (fun l =>
    markedWeightedIndices (univ.biUnion P) (representedArraySelected l) k)

def sourceComparisonDivisor {t : G → ℕ} (i : SourceComparisonDivisorIndex t) : ℕ :=
  markedWeightedDivisor (representedArraySelected i.1) i.2

def sourceComparisonDivisorCoefficient (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (i : SourceComparisonDivisorIndex t) : ℂ :=
  sourceComparisonMarkCoefficient P t b i.1 *
    (markedWeightedCoefficient (sourceComparisonMarkResidualDamping P q) i.2 : ℂ)

def sourceComparisonDivisorModel (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (k n : ℕ) : ℂ :=
  ∑ i ∈ sourceComparisonDivisorIndices P t k,
    if sourceComparisonDivisor i ∣ n then sourceComparisonDivisorCoefficient P t q b i else 0

theorem sourceComparisonDivisorModel_eq_truncation (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (k n : ℕ) :
    sourceComparisonDivisorModel P t q b k n =
      ∑ l ∈ sourceComparisonMarkChoices P t, sourceComparisonMarkCoefficient P t b l *
        (markedWeightedTruncation (univ.biUnion P) (representedArraySelected l)
          (sourceComparisonMarkResidualDamping P q) k n : ℂ) := by
  classical
  unfold sourceComparisonDivisorModel sourceComparisonDivisorIndices
  rw [sum_sigma]
  apply sum_congr rfl
  intro l _
  rw [markedWeightedTruncation_eq_polynomial, markedIndexedDivisorPolynomial,
    Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases hd : sourceComparisonDivisor ⟨l, i⟩ ∣ n
  · have hd' : markedWeightedDivisor (representedArraySelected l) i ∣ n := hd
    rw [ite_eq_left hd, ite_eq_left hd']
    rfl
  · have hd' : ¬ markedWeightedDivisor (representedArraySelected l) i ∣ n := hd
    rw [ite_eq_right hd, ite_eq_right hd', Complex.ofReal_zero, mul_zero]

theorem sourceComparisonDivisor_prime_set_subset (P : G → Finset ℕ) (t : G → ℕ) (k : ℕ)
    {i : SourceComparisonDivisorIndex t} (hi : i ∈ sourceComparisonDivisorIndices P t k) :
    representedArraySelected i.1 ∪ i.2.2 ⊆ univ.biUnion P := by
  classical
  obtain ⟨hl, hT⟩ := mem_sigma.mp hi
  have ht := (mem_powersetCard.mp (mem_sigma.mp hT).2).1
  exact union_subset (sourceComparisonMarkChoices_selected_subset P t hl)
    (ht.trans sdiff_subset)

theorem sourceComparisonDivisor_pos (P : G → Finset ℕ) (t : G → ℕ) (k : ℕ)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime)
    {i : SourceComparisonDivisorIndex t} (hi : i ∈ sourceComparisonDivisorIndices P t k) :
    0 < sourceComparisonDivisor i := by
  unfold sourceComparisonDivisor markedWeightedDivisor
  exact prod_pos (fun p hp => (hP p (sourceComparisonDivisor_prime_set_subset P t k hi hp)).pos)

theorem sourceComparisonDivisor_prime_dvd_mem (P : G → Finset ℕ) (t : G → ℕ) (k : ℕ)
    {i : SourceComparisonDivisorIndex t} (hi : i ∈ sourceComparisonDivisorIndices P t k)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ sourceComparisonDivisor i)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime) : p ∈ univ.biUnion P := by
  classical
  unfold sourceComparisonDivisor markedWeightedDivisor at hd
  obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  have hr' := sourceComparisonDivisor_prime_set_subset P t k hi hr
  exact ((Nat.prime_dvd_prime_iff_eq hp (hP r hr')).mp hpr) ▸ hr'

theorem sourceComparisonDivisor_bound (P : G → Finset ℕ) (t : G → ℕ) (k : ℕ)
    {Z : ℝ} (hZ : 1 ≤ Z) (hpZ : ∀ p ∈ univ.biUnion P, (p : ℝ) ≤ Z)
    {i : SourceComparisonDivisorIndex t} (hi : i ∈ sourceComparisonDivisorIndices P t k) :
    (sourceComparisonDivisor i : ℝ) ≤ Z ^ ((∑ g, t g) + k) := by
  classical
  let A := representedArraySelected i.1 ∪ i.2.2
  have hT := (mem_sigma.mp (mem_sigma.mp hi).2)
  have hcardT : i.2.2.card ≤ k := (mem_powersetCard.mp hT.2).2.trans_le
    (Nat.le_of_lt_succ (mem_range.mp hT.1))
  have hcard : A.card ≤ (∑ g, t g) + k :=
    (card_union_le _ _).trans (Nat.add_le_add (cubicSampling_selected_card_le i.1) hcardT)
  change ((∏ p ∈ A, p : ℕ) : ℝ) ≤ _
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _p ∈ A, Z := prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      (fun p hp => hpZ p (sourceComparisonDivisor_prime_set_subset P t k hi hp))
    _ = Z ^ A.card := prod_const _
    _ ≤ _ := pow_le_pow_right₀ hZ hcard

theorem sourceComparisonDivisorModel_pointwise_error (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (k n : ℕ) :
    ‖sourceComparisonMarkWeight P t q b n - sourceComparisonDivisorModel P t q b k n‖ ≤
      ∑ l ∈ sourceComparisonMarkChoices P t, ‖sourceComparisonMarkCoefficient P t b l‖ *
        markedWeightedTail (univ.biUnion P) (representedArraySelected l)
          (sourceComparisonMarkResidualDamping P q) (k + 1) n := by
  rw [sourceComparisonMarkWeight_eq_residual P t q hdis,
    sourceComparisonDivisorModel_eq_truncation, ← sum_sub_distrib]
  simp_rw [← mul_sub, ← Complex.ofReal_sub]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro l hl
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact cubicSampling_weightedTruncation_abs_error _ _ hP
    (sourceComparisonMarkChoices_selected_subset P t hl) _
    (fun _ hp => sourceComparisonMarkResidualDamping_bounds P q hdis hq hp) k n

end
end ArtinMatthews
