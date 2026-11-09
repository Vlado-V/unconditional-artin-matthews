module

public import Mathlib


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Filter Topology
noncomputable section

/-- A decaying shell recurrence improves every available geometric mass bound. -/
theorem shell_recurrence_improve
    (a : ℕ → ℝ) (r D q C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hr : 0 < r) (hD : 0 ≤ D) (hq : 0 < q) (hC : 0 < C)
    (hbound : ∀ n, a n ≤ C * q ^ n)
    (hrec : ∀ n, a (n + 1) ≤ D * r ^ (n + 1) * (a n + a (n + 1) + a (n + 2))) :
    ∃ C' > 0, ∀ n, a n ≤ C' * (q * r) ^ n := by
  let K := D * C * (q⁻¹ + 1 + q)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C' := max (a 0) K + 1
  have hC' : 0 < C' := by dsimp [C']; linarith [le_max_right (a 0) K]
  refine ⟨C',hC',?_⟩
  intro n
  cases n with
  | zero => simpa [C'] using (le_max_left (a 0) K).trans (le_add_of_nonneg_right zero_le_one)
  | succ n =>
    have hsum : a n + a (n + 1) + a (n + 2) ≤
        C * q ^ n + C * q ^ (n + 1) + C * q ^ (n + 2) := by
      linarith [hbound n,hbound (n+1),hbound (n+2)]
    have hfactor : D * r ^ (n + 1) *
        (C * q ^ n + C * q ^ (n + 1) + C * q ^ (n + 2)) =
        K * (q * r) ^ (n + 1) := by
      dsimp [K]
      simp only [mul_pow,pow_add,pow_one,pow_two]
      field_simp
      <;> ring
    calc
      a (n + 1) ≤ D * r ^ (n + 1) * (a n + a (n + 1) + a (n + 2)) := hrec n
      _ ≤ D * r ^ (n + 1) *
          (C * q ^ n + C * q ^ (n + 1) + C * q ^ (n + 2)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hD (pow_nonneg hr.le _))
      _ = K * (q * r) ^ (n + 1) := hfactor
      _ ≤ C' * (q * r) ^ (n + 1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_pos hq hr).le _)
        dsimp [C']
        linarith [le_max_right (a 0) K]

/-- The shell recurrence upgrades one geometric bound to every positive geometric rate. -/
theorem shell_recurrence_arbitrary_rate
    (a : ℕ → ℝ) (r D q C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hr : 0 < r) (hr1 : r < 1) (hD : 0 ≤ D) (hq : 0 < q) (hC : 0 < C)
    (hbound : ∀ n, a n ≤ C * q ^ n)
    (hrec : ∀ n, a (n + 1) ≤ D * r ^ (n + 1) * (a n + a (n + 1) + a (n + 2)))
    (t : ℝ) (ht : 0 < t) :
    ∃ C' > 0, ∀ n, a n ≤ C' * t ^ n := by
  have himprove : ∀ k : ℕ, ∃ C' > 0, ∀ n, a n ≤ C' * (q * r ^ k) ^ n := by
    intro k
    induction k with
    | zero => exact ⟨C,hC,by simpa using hbound⟩
    | succ k ih =>
      obtain ⟨C',hC',hb⟩ := ih
      obtain ⟨C'',hC'',hb'⟩ := shell_recurrence_improve a r D (q*r^k) C' ha hr hD
        (mul_pos hq (pow_pos hr _)) hC' hb hrec
      refine ⟨C'',hC'',?_⟩
      simpa [pow_succ,mul_assoc] using hb'
  have hlim : Tendsto (fun k : ℕ => q * r ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).const_mul q
  obtain ⟨k,hk⟩ := (hlim.eventually (gt_mem_nhds ht)).exists
  obtain ⟨C',hC',hb⟩ := himprove k
  refine ⟨C',hC',fun n => (hb n).trans ?_⟩
  gcongr

/-- In particular, the nonnegative shell masses have finite total mass. -/
theorem shell_recurrence_summable
    (a : ℕ → ℝ) (r D q C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hr : 0 < r) (hr1 : r < 1) (hD : 0 ≤ D) (hq : 0 < q) (hC : 0 < C)
    (hbound : ∀ n, a n ≤ C * q ^ n)
    (hrec : ∀ n, a (n + 1) ≤ D * r ^ (n + 1) * (a n + a (n + 1) + a (n + 2))) :
    Summable a := by
  obtain ⟨C',hC',hb⟩ := shell_recurrence_arbitrary_rate a r D q C ha hr hr1 hD hq hC
    hbound hrec (1/2) (by norm_num)
  exact Summable.of_nonneg_of_le ha hb
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left C')

end
end ArtinMatthews
