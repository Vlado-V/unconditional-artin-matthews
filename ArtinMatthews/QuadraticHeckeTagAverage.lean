module

public import ArtinMatthews.QuadraticHeckeTagLift


set_option backward.privateInPublic true
@[expose] public section

/-! Averaging the translated quadratic form over disjoint tags. Each
row or column is excluded at most as many times as it has prime factors. -/
namespace ArtinMatthews.QuadraticScale

open scoped BigOperators

noncomputable section
variable {P : Type*} [DecidableEq P]

def tagOverlapCount (pool : Finset (Finset P)) (r : Finset P) : ℕ :=
  (pool.filter (fun t => ¬ Disjoint t r)).card

theorem tagOverlapCount_le (pool : Finset (Finset P))
    (hpool : (↑pool : Set (Finset P)).PairwiseDisjoint id) (r : Finset P) :
    tagOverlapCount pool r ≤ r.card := by
  let bad := pool.filter (fun t => ¬ Disjoint t r)
  have hw (t : bad) : ∃ p : P, p ∈ t.val ∧ p ∈ r :=
    Finset.not_disjoint_iff.mp (Finset.mem_filter.mp t.property).2
  let pick : bad → r := fun t => ⟨(hw t).choose, (hw t).choose_spec.2⟩
  have hinj : Function.Injective pick := by
    intro t u h
    apply Subtype.ext
    by_contra hn
    have ht := (Finset.mem_filter.mp t.property).1
    have hu := (Finset.mem_filter.mp u.property).1
    have he : (hw t).choose = (hw u).choose := congrArg Subtype.val h
    exact Finset.disjoint_left.mp (hpool ht hu hn) (hw t).choose_spec.1 (by
      change (hw t).choose ∈ u.val
      rw [he]
      exact (hw u).choose_spec.1)
  simpa [tagOverlapCount, bad] using Fintype.card_le_of_injective pick hinj

private theorem sum_tagOverlap (pool carrier : Finset (Finset P)) (f : Finset P → ℝ) :
    (∑ t ∈ pool, ∑ r ∈ carrier, if Disjoint t r then 0 else f r) =
      ∑ r ∈ carrier, (tagOverlapCount pool r : ℝ) * f r := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [tagOverlapCount, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : Disjoint t r <;> simp [h]

theorem isEnergyBound_tag_average
    (rows cols pool : Finset (Finset P)) (K : Finset P → Finset P → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hp : pool.Nonempty)
    (hK : ∀ r ∈ rows, ∀ c ∈ cols, ‖K r c‖ ≤ 1)
    (hLift : ∀ t ∈ pool, IsEnergyBound (tagRows rows t) cols K B)
    (hmul : ∀ t ∈ pool, ∀ r ∈ rows, ∀ c ∈ cols, Disjoint t r → Disjoint t c →
      K (t ∪ r) c = K t c * K r c)
    (hunit : ∀ t ∈ pool, ∀ c ∈ cols, Disjoint t c → ‖K t c‖ = 1)
    (hrow : ∀ r ∈ rows, (tagOverlapCount pool r : ℝ) ≤ pool.card / 4)
    (hcol : ∀ c ∈ cols, (tagOverlapCount pool c : ℝ) ≤ pool.card / 4) :
    IsEnergyBound rows cols K (8 * B) := by
  let E := bestEnergyBound rows cols K
  have hE : 0 ≤ E ∧ IsEnergyBound rows cols K E :=
    bestEnergyBound_spec rows cols K
      ⟨_, by positivity, isEnergyBound_card rows cols K hK⟩
  have hpc : (0 : ℝ) < pool.card := by exact_mod_cast Finset.Nonempty.card_pos hp
  have hbound (a : Finset P → ℂ) :
      finiteEnergy rows cols K a ≤ (2 * B + 3 / 4 * E) * coeffMass cols a := by
    let m := coeffMass cols a
    let e := finiteEnergy rows cols K a
    have hrowLoss :
        (∑ t ∈ pool, finiteEnergy (rows.filter (fun r => ¬ Disjoint t r)) cols K a) ≤
          pool.card / 4 * e := by
      simp only [finiteEnergy, Finset.sum_filter, ite_not]
      rw [sum_tagOverlap]
      change _ ≤ pool.card / 4 * (∑ r ∈ rows, ‖rowValue cols K a r‖ ^ 2)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right (hrow r hr) (sq_nonneg _))
    have hcolLoss :
        (∑ t ∈ pool, coeffMass cols (tagBadCoeff t a)) ≤ pool.card / 4 * m := by
      simp only [tagBadCoeff_mass]
      rw [sum_tagOverlap]
      change _ ≤ pool.card / 4 * (∑ c ∈ cols, ‖a c‖ ^ 2)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_right (hcol c hc) (sq_nonneg _))
    have hsum :
        (pool.card : ℝ) * e ≤
          (∑ t ∈ pool, finiteEnergy (rows.filter (fun r => ¬ Disjoint t r)) cols K a) +
          (pool.card : ℝ) * (2 * B * m) +
          (2 * E) * ∑ t ∈ pool, coeffMass cols (tagBadCoeff t a) := by
      have h := Finset.sum_le_sum (s := pool) (fun t ht =>
        (finiteEnergy_tag_lift rows cols K t hB (hLift t ht) (hmul t ht) (hunit t ht) a).trans
          (add_le_add_right (mul_le_mul_of_nonneg_left (hE.2 (tagBadCoeff t a))
            (by norm_num : (0 : ℝ) ≤ 2)) _))
      simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        ← Finset.mul_sum] using h
    have havg :
        (pool.card : ℝ) * e ≤ pool.card / 4 * e + pool.card * (2 * B * m) +
          (2 * E) * (pool.card / 4 * m) :=
      hsum.trans (add_le_add (add_le_add_left hrowLoss _)
        (mul_le_mul_of_nonneg_left hcolLoss (by positivity [hE.1])))
    apply (le_of_mul_le_mul_left _ hpc)
    calc
      (pool.card : ℝ) * e ≤ pool.card / 4 * e + pool.card * (2 * B * m) +
          (2 * E) * (pool.card / 4 * m) := havg
      _ ≤ pool.card / 4 * (E * m) + pool.card * (2 * B * m) +
          (2 * E) * (pool.card / 4 * m) := by
        exact add_le_add_left
          (add_le_add_left (mul_le_mul_of_nonneg_left (hE.2 a) (by positivity)) _) _
      _ = _ := by ring
  have hmin : E ≤ 2 * B + 3 / 4 * E :=
    bestEnergyBound_le rows cols K (by positivity [hE.1]) hbound
  intro a
  exact (hE.2 a).trans (mul_le_mul_of_nonneg_right
    (by linarith : E ≤ 8 * B) (coeffMass_nonneg cols a))

end
end ArtinMatthews.QuadraticScale
