module

public import ArtinMatthews.IdealHarmonicSourceWindow


set_option backward.privateInPublic true
@[expose] public section

/-! A log-cell restriction of a genuine prime interval is again a prime
interval, including both ends of its finite hull. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def IdealPrimeInterval (P : Finset ℕ) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ p : ℕ, p.Prime → a ≤ p → p ≤ b → p ∈ P

def idealPrimeCellIndex (h : ℝ) (r p : ℕ) : ℤ :=
  ⌊Real.log (r*p : ℕ) / h⌋

def idealPrimeCellSet (P : Finset ℕ) (h : ℝ) (r : ℕ) (j : ℤ) : Finset ℕ :=
  P.filter fun p => idealPrimeCellIndex h r p = j

theorem idealPrimeCellIndex_mono {h : ℝ} (hh : 0 < h) {r m n : ℕ}
    (hr : 0 < r) (hm : 0 < m) (hmn : m ≤ n) :
    idealPrimeCellIndex h r m ≤ idealPrimeCellIndex h r n := by
  apply Int.floor_mono
  apply div_le_div_of_nonneg_right _ hh.le
  apply Real.log_le_log
  · exact_mod_cast Nat.mul_pos hr hm
  · exact_mod_cast Nat.mul_le_mul_left r hmn

theorem idealPrimeCellSet_hull (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hinterval : IdealPrimeInterval P) {h : ℝ} (hh : 0 < h)
    {r : ℕ} (hr : 0 < r) (j : ℤ) (hne : (idealPrimeCellSet P h r j).Nonempty) :
    idealPrimeCellSet P h r j =
      (Icc ((idealPrimeCellSet P h r j).min' hne)
        ((idealPrimeCellSet P h r j).max' hne)).filter Nat.Prime := by
  let S := idealPrimeCellSet P h r j
  have hmin := min'_mem S hne
  have hmax := max'_mem S hne
  have hminP : S.min' hne ∈ P := (mem_filter.mp hmin).1
  have hmaxP : S.max' hne ∈ P := (mem_filter.mp hmax).1
  have hminj : idealPrimeCellIndex h r (S.min' hne) = j := (mem_filter.mp hmin).2
  have hmaxj : idealPrimeCellIndex h r (S.max' hne) = j := (mem_filter.mp hmax).2
  ext p
  constructor
  · intro hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨min'_le S p hp, le_max' S p hp⟩,
      hP p (mem_filter.mp hp).1⟩
  · intro hp
    obtain ⟨hpn, hpp⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hpn
    have hpP : p ∈ P := hinterval _ hminP _ hmaxP p hpp hlo hhi
    refine mem_filter.mpr ⟨hpP, ?_⟩
    have hl := idealPrimeCellIndex_mono hh hr (hP _ hminP).pos hlo
    have hu := idealPrimeCellIndex_mono hh hr hpp.pos hhi
    rw [hminj] at hl
    rw [hmaxj] at hu
    exact le_antisymm hu hl

def idealHarmonicPrimeClosed {q : ℕ} (χ : DirichletCharacter ℂ q) (m n : ℕ) : ℂ :=
  ∑ p ∈ (Icc m n).filter Nat.Prime, (p : ℂ)⁻¹*χ (p : ZMod q)

theorem idealHarmonicPrimeClosed_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {m n : ℕ} (hmn : m ≤ n) :
    idealHarmonicPrimeClosed χ m n =
      (if m.Prime then (m : ℂ)⁻¹*χ (m : ZMod q) else 0) +
        idealHarmonicPrimeInterval χ m n := by
  simp only [idealHarmonicPrimeClosed, idealHarmonicPrimeInterval,
    Nat.floor_natCast, sum_filter]
  rw [Icc_eq_cons_Ioc hmn, sum_cons]

theorem idealHarmonicPrimeClosed_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ‖idealHarmonicPrimeClosed χ m n‖ ≤
      ‖idealHarmonicPrimeInterval χ m n‖ + (m : ℝ)⁻¹ := by
  rw [idealHarmonicPrimeClosed_eq χ hmn]
  have hb : ‖if m.Prime then (m : ℂ)⁻¹*χ (m : ZMod q) else 0‖ ≤ (m : ℝ)⁻¹ := by
    split_ifs
    · rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_of_le_one_right (by positivity) (χ.norm_le_one _)
    · simp only [norm_zero]
      positivity
  exact (norm_add_le _ _).trans (by linarith)

end
end ArtinMatthews
