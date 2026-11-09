module

public import ArtinMatthews.QuadraticHeckeFiniteEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! A disjoint prime tag moves the good rows injectively, with an exact
unitary twist on the columns avoiding the tag. The discarded columns
remain a separate squared-energy term. -/
namespace ArtinMatthews.QuadraticScale

open scoped BigOperators ComplexConjugate

noncomputable section
variable {P : Type*} [DecidableEq P]

def tagRows (rows : Finset (Finset P)) (tag : Finset P) : Finset (Finset P) :=
  (rows.filter (Disjoint tag)).image (tag ∪ ·)

def tagBadCoeff (tag : Finset P) (a : Finset P → ℂ) (c : Finset P) : ℂ :=
  if Disjoint tag c then 0 else a c

theorem tagBadCoeff_mass (cols : Finset (Finset P)) (tag : Finset P) (a : Finset P → ℂ) :
    coeffMass cols (tagBadCoeff tag a) =
      ∑ c ∈ cols, if Disjoint tag c then 0 else ‖a c‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Disjoint tag c <;> simp [tagBadCoeff, hc]

private theorem norm_add_sq_bound (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  calc
    _ ≤ (‖z‖ + ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

theorem finiteEnergy_tag_lift (rows cols : Finset (Finset P)) (K : Finset P → Finset P → ℂ)
    (tag : Finset P) {B : ℝ} (hB : 0 ≤ B)
    (hLift : IsEnergyBound (tagRows rows tag) cols K B)
    (hmul : ∀ r ∈ rows, ∀ c ∈ cols, Disjoint tag r → Disjoint tag c →
      K (tag ∪ r) c = K tag c * K r c)
    (hunit : ∀ c ∈ cols, Disjoint tag c → ‖K tag c‖ = 1)
    (a : Finset P → ℂ) :
    finiteEnergy rows cols K a ≤
      finiteEnergy (rows.filter (fun r => ¬ Disjoint tag r)) cols K a +
      2 * B * coeffMass cols a + 2 * finiteEnergy rows cols K (tagBadCoeff tag a) := by
  let R := rows.filter (Disjoint tag)
  let good : Finset P → ℂ := fun c => if Disjoint tag c then a c else 0
  let twist : Finset P → ℂ := fun c => conj (K tag c) * good c
  have hmass : coeffMass cols twist ≤ coeffMass cols a := by
    apply Finset.sum_le_sum
    intro c hc
    by_cases h : Disjoint tag c
    · simp [twist, good, h, hunit c hc h]
    · simp [twist, good, h]
  have hrow (r : Finset P) (hr : r ∈ R) : rowValue cols K good r = rowValue cols K twist (tag ∪ r) := by
    obtain ⟨hr', hd⟩ := Finset.mem_filter.mp hr
    apply Finset.sum_congr rfl
    intro c hc
    by_cases h : Disjoint tag c
    · have hK : K tag c * conj (K tag c) = 1 := by
        rw [Complex.mul_conj', hunit c hc h]
        norm_num
      simp only [twist, good, ite_eq_left h, hmul r hr' c hc hd h]
      calc
        _ = (K tag c * conj (K tag c)) * (K r c * a c) := by rw [hK, one_mul]
        _ = _ := by ac_rfl
    · simp [twist, good, h]
  have hinj : Set.InjOn (fun r : Finset P => tag ∪ r) ↑R := by
    intro r hr s hs he
    have hd := (Finset.mem_filter.mp (show r ∈ R from hr)).2
    have hd' := (Finset.mem_filter.mp (show s ∈ R from hs)).2
    simpa only [Finset.union_sdiff_cancel_left hd, Finset.union_sdiff_cancel_left hd'] using
      congrArg (fun w : Finset P => w \ tag) he
  have hgood : finiteEnergy R cols K good ≤ B * coeffMass cols a := by
    calc
      _ = finiteEnergy (tagRows rows tag) cols K twist := by
        change (∑ r ∈ R, ‖rowValue cols K good r‖ ^ 2) =
          ∑ r ∈ R.image (tag ∪ ·), ‖rowValue cols K twist r‖ ^ 2
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl (fun r hr => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow r hr))
      _ ≤ B * coeffMass cols twist := hLift twist
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hB
  have hsplit (r : Finset P) :
      rowValue cols K a r = rowValue cols K good r + rowValue cols K (tagBadCoeff tag a) r := by
    unfold rowValue
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : Disjoint tag c <;> simp [good, tagBadCoeff, h]
  have hlocal : finiteEnergy R cols K a ≤
      2 * finiteEnergy R cols K good + 2 * finiteEnergy R cols K (tagBadCoeff tag a) := by
    unfold finiteEnergy
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun r _ => by rw [hsplit r]; exact norm_add_sq_bound _ _)
  have hpartition : finiteEnergy rows cols K a =
      finiteEnergy (rows.filter (fun r => ¬ Disjoint tag r)) cols K a + finiteEnergy R cols K a := by
    unfold finiteEnergy
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not rows (Disjoint tag) _).symm
  calc
    _ = _ := hpartition
    _ ≤ finiteEnergy (rows.filter (fun r => ¬ Disjoint tag r)) cols K a +
        (2 * finiteEnergy R cols K good + 2 * finiteEnergy R cols K (tagBadCoeff tag a)) :=
      add_le_add_right hlocal _
    _ ≤ _ := by
      have hbad := finiteEnergy_le_of_subset R rows (Finset.filter_subset _ _) cols K (tagBadCoeff tag a)
      linarith

end
end ArtinMatthews.QuadraticScale
