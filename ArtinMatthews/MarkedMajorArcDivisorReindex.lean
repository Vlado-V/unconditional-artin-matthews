module

public import ArtinMatthews.MarkedMajorArcCharacterPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact divisor reindexing for the oscillatory rough-number expansion.
The finite bijection follows the genuine `sum_Icc_dvd_reindex` proof in
OAI/NumberTheory/JointDickman/Arithmetic/PrimePresencePhase.lean, extended
here to arbitrary half-open natural intervals. -/
namespace ArtinMatthews
open Finset

 theorem marked_sum_Ioc_dvd_reindex {E : Type*} [AddCommMonoid E]
    {d : ℕ} (hd : 0 < d) (M N : ℕ) (F : ℕ → E) :
    (∑ n ∈ Ioc M N, if d ∣ n then F n else 0) =
      ∑ m ∈ Ioc (M/d) (N/d), F (d*m) := by
  classical
  rw [← sum_filter]
  apply sum_bij (fun n _ => n/d)
  · intro n hn
    obtain ⟨hn,hdn⟩ := mem_filter.mp hn
    refine mem_Ioc.mpr ⟨?_, Nat.div_le_div_right (mem_Ioc.mp hn).2⟩
    apply (Nat.div_lt_iff_lt_mul hd).2
    simpa [Nat.mul_div_cancel' hdn, mul_comm] using (mem_Ioc.mp hn).1
  · intro n hn m hm he
    have hdn := (mem_filter.mp hn).2
    have hdm := (mem_filter.mp hm).2
    simpa only [Nat.mul_div_cancel' hdn,Nat.mul_div_cancel' hdm] using congrArg (d*·) he
  · intro m hm
    obtain ⟨hm1,hmN⟩ := mem_Ioc.mp hm
    refine ⟨d*m,mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩,
      dvd_mul_right d m⟩,Nat.mul_div_cancel_left m hd⟩
    · simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hd).1 hm1
    · simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmN
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

 theorem marked_character_imaginary_power_mul (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (d m : ℕ) :
    χ ((d*m:ℕ):ZMod q)*((d*m:ℕ):ℂ)^((t:ℂ)*Complex.I) =
      (χ (d:ZMod q)*(d:ℂ)^((t:ℂ)*Complex.I))*
        (χ (m:ZMod q)*(m:ℂ)^((t:ℂ)*Complex.I)) := by
  simp only [Nat.cast_mul,map_mul,Complex.natCast_mul_natCast_cpow]
  ring

 theorem marked_character_imaginary_power_norm_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) {d : ℕ} (hd : 0 < d) :
    ‖χ (d:ZMod q)*(d:ℂ)^((t:ℂ)*Complex.I)‖ ≤ 1 := by
  rw [norm_mul]
  have hp : ‖(d:ℂ)^((t:ℂ)*Complex.I)‖ = 1 := by
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hn := Complex.norm_cpow_eq_rpow_re_of_pos hdR ((t:ℂ)*Complex.I)
    simpa using hn
  rw [hp,mul_one]
  exact χ.norm_le_one _

 theorem marked_divisor_character_sum_eq (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) {d : ℕ} (hd : 0 < d) (M N : ℕ) :
    (∑ n ∈ Ioc M N, if d ∣ n then
      χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I) else 0) =
    (χ (d:ZMod q)*(d:ℂ)^((t:ℂ)*Complex.I))*
      ∑ m ∈ Ioc (M/d) (N/d), χ (m:ZMod q)*(m:ℂ)^((t:ℂ)*Complex.I) := by
  rw [marked_sum_Ioc_dvd_reindex hd, mul_sum]
  apply sum_congr rfl
  intro m _
  exact marked_character_imaginary_power_mul q χ t d m

end ArtinMatthews
