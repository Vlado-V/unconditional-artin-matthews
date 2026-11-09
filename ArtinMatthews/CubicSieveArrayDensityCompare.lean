module

public import ArtinMatthews.CubicSieveFirstArrayTail
public import ArtinMatthews.CubicSieveRestrictedDensityBudget
public import ArtinMatthews.CubicSieveBernoulliPrimeBand


set_option backward.privateInPublic true
@[expose] public section

/-! The retained first-array model has the true independent mean, up to
the explicit truncation and restricted local-density errors. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_firstArrayFullModel_eq_independentMean {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (V : J → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    cubicSieveFirstArrayFullModel P V (fun p => 1 / (p : ℝ)) = independentArrayMean P V := by
  rw [cubicSieve_firstArrayFullModel_eq_bandMeans P V _ hdis, independentArrayMean_eq]

theorem cubicSieve_firstArray_restricted_value_error {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {v y M : ℝ} (hv : 0 < v) (hy : 0 < y) (hM : 0 ≤ M)
    (hV : ∀ j, v ≤ bandReciprocalMass (P j))
    (hmin : ∀ j p, p ∈ P j → y ≤ (p : ℝ))
    (hmass : (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) ≤ M)
    {r : ℕ} (hr : 0 < r) (k : ℕ) :
    |cubicSieveFirstArrayTruncationModel P (fun j => bandReciprocalMass (P j))
        (fun p => cubicSieveRestrictedMarkingDensity r p 1) k -
      independentArrayMean P (fun j => bandReciprocalMass (P j))| ≤
      2 * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k +
        (1 / v + 1 / 2) * (M / y + Real.log (r : ℝ) / (Real.log (3 / 2 : ℝ) * y)) := by
  let U := univ.biUnion P
  let g (p : ℕ) := cubicSieveRestrictedMarkingDensity r p 1
  let V (j : J) := bandReciprocalMass (P j)
  have hPU (p : ℕ) (hp : p ∈ U) : p.Prime := by
    obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
    exact hP j p hp
  have hminU (p : ℕ) (hp : p ∈ U) : y ≤ (p : ℝ) := by
    obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
    exact hmin j p hp
  have hg (p : ℕ) (hp : p ∈ U) : 0 ≤ g p ∧ g p ≤ 1 / (p : ℝ) :=
    cubicSieve_restrictedMarkingDensity_bounds r (hPU p hp)
  have hmg : (∑ p ∈ U, g p) ≤ M := (sum_le_sum (fun p hp => (hg p hp).2)).trans hmass
  have htail := cubicSieve_firstArrayTruncation_tail P hdis (fun j => hv.trans_le (hV j)) g hg hM hmg k
  have hmeans := bernoulliPrimeBandMean_prod_abs_sub_le univ P (fun _ => g) (fun _ p => 1 / (p : ℝ))
    (fun j _ => hP j) hv (fun j _ => hV j)
    (fun j _ p hp => cubicSieve_restrictedMarkingDensity_bounds r (hP j p hp))
    (fun _ _ _ _ => ⟨by positivity, le_rfl⟩)
  have hpair : ((Finset.univ : Finset J) : Set J).PairwiseDisjoint P := fun _ _ _ _ hij => hdis hij
  rw [← sum_biUnion hpair] at hmeans
  rw [← cubicSieve_firstArrayFullModel_eq_bandMeans P V g hdis,
    ← independentArrayMean_eq] at hmeans
  exact (abs_sub_le _ (cubicSieveFirstArrayFullModel P V g) _).trans
    (add_le_add htail (hmeans.trans
      (mul_le_mul_of_nonneg_left (cubicSieve_restrictedDensity_total_distance U hPU hr hy hminU hmass)
        (by positivity))))

theorem cubicSieve_firstArray_restricted_tangent_error {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {v y Z M : ℝ} (hv : 0 < v) (hy : 0 < y) (hZ : 1 ≤ Z) (hM : 0 ≤ M)
    (hV : ∀ j, v ≤ bandReciprocalMass (P j))
    (hmin : ∀ j p, p ∈ P j → y ≤ (p : ℝ)) (hmax : ∀ j p, p ∈ P j → (p : ℝ) ≤ Z)
    (hmass : (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) ≤ M) (r k : ℕ) :
    |cubicSieveFirstArrayTruncationTangent P (fun j => bandReciprocalMass (P j))
      (fun p => cubicSieveRestrictedMarkingDensity r p 1) (cubicSieveRestrictedMarkingTangent r) k| ≤
      2 * (4 * Real.log Z / y) * ((Fintype.card J : ℝ) + 1) * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k +
        (1 / v + 1 / 2) * (2 * Real.log Z * M / y) := by
  let U := univ.biUnion P
  let g (p : ℕ) := cubicSieveRestrictedMarkingDensity r p 1
  let g' := cubicSieveRestrictedMarkingTangent r
  let V (j : J) := bandReciprocalMass (P j)
  have hPU (p : ℕ) (hp : p ∈ U) : p.Prime := by
    obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
    exact hP j p hp
  have hminU (p : ℕ) (hp : p ∈ U) : y ≤ (p : ℝ) := by
    obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
    exact hmin j p hp
  have hmaxU (p : ℕ) (hp : p ∈ U) : (p : ℝ) ≤ Z := by
    obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
    exact hmax j p hp
  have hg (p : ℕ) (hp : p ∈ U) : 0 ≤ g p ∧ g p ≤ 1 / (p : ℝ) :=
    cubicSieve_restrictedMarkingDensity_bounds r (hPU p hp)
  have hmg : (∑ p ∈ U, g p) ≤ M := (sum_le_sum (fun p hp => (hg p hp).2)).trans hmass
  have htail := cubicSieve_firstArrayTruncationTangent_tail P hdis (fun j => hv.trans_le (hV j)) g g'
    hg hM (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hZ)) hy.le)
    (fun p hp => cubicSieve_restrictedMarkingTangent_interval r (hPU p hp) hy (hminU p hp) (hmaxU p hp))
    hmg k
  have hfull := cubicSieve_firstArrayFullModel_hasDerivAt P V
    (fun p s => cubicSieveRestrictedMarkingDensity r p s) g' 1
    (fun p hp => cubicSieve_restrictedMarkingDensity_hasDerivAt_one r (hPU p hp).one_lt)
  have hmeans := bernoulliPrimeBandMean_prod_deriv_abs_le univ P
    (fun _ p s => cubicSieveRestrictedMarkingDensity r p s) (fun _ => g')
    (fun j _ => hP j) hv (fun j _ => hV j)
    (fun j _ p hp => cubicSieve_restrictedMarkingDensity_hasDerivAt_one r (hP j p hp).one_lt)
    (fun j _ p hp => cubicSieve_restrictedMarkingDensity_bounds r (hP j p hp))
  have hfun : (fun s => cubicSieveFirstArrayFullModel P V (fun p => cubicSieveRestrictedMarkingDensity r p s)) =
      (fun s => ∏ j, bernoulliBandMean (P j) (fun p => cubicSieveRestrictedMarkingDensity r p s) (V j)) :=
    funext (fun _ => cubicSieve_firstArrayFullModel_eq_bandMeans P V _ hdis)
  rw [← hfun, hfull.deriv] at hmeans
  have hpair : ((Finset.univ : Finset J) : Set J).PairwiseDisjoint P := fun _ _ _ _ hij => hdis hij
  rw [← sum_biUnion hpair] at hmeans
  have hbound := hmeans.trans (mul_le_mul_of_nonneg_left
    (cubicSieve_restrictedDensity_total_tangent U hPU r hy hZ hminU hmaxU hmass) (by positivity))
  have hsplit := abs_sub_le
    (cubicSieveFirstArrayTruncationTangent P V g g' k) (cubicSieveFirstArrayFullTangent P V g g') 0
  simp only [sub_zero] at hsplit
  exact hsplit.trans (add_le_add htail hbound)

end ArtinMatthews
