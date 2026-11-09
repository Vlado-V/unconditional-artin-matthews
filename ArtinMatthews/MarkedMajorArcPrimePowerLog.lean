module

public import ArtinMatthews.MarkedMajorArcRoughCharacter
public import ArtinMatthews.MarkedMajorArcPrimeNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! Removal of the actual higher prime powers after logarithmic weighting. -/
namespace ArtinMatthews
open Finset ArithmeticFunction

noncomputable def markedMajorLogMangoldtSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t H u v : ℝ) : ℂ :=
  (H:ℂ)⁻¹*∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
    (vonMangoldt n:ℂ)*(((Real.log n)⁻¹:ℝ)*(χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)))

 theorem marked_major_log_prime_power_error {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t H : ℝ) {u v : ℝ}
    (hH : 0 < H) (hu : 0 < u) (hlog : 1 ≤ Real.log u) (huv : u ≤ v) :
    ‖markedMajorLogMangoldtSum χ t H u v-markedMajorNormalizedPrimeSum χ t H u v‖ ≤
      2*Real.sqrt v*Real.log v/H := by
  classical
  let f : ℕ → ℂ := fun n => (vonMangoldt n:ℂ)*
    (((Real.log n)⁻¹:ℝ)*(χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)))
  let S := Ioc ⌊u⌋₊ ⌊v⌋₊
  have hu1 : 1 ≤ u := by
    by_contra hn
    have hh : Real.log u < Real.log 1 := Real.log_lt_log hu (by linarith)
    simp only [Real.log_one] at hh
    linarith
  have hv1 : 1 ≤ v := hu1.trans huv
  have he (n : ℕ) (hn : n.Prime) : f n = χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I) := by
    have hnp : (1:ℝ) < n := by exact_mod_cast hn.one_lt
    have hln : (Real.log n:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hnp).ne'
    dsimp [f]
    rw [vonMangoldt_apply_prime hn,Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀ hln,one_mul]
  have heq : markedMajorLogMangoldtSum χ t H u v-markedMajorNormalizedPrimeSum χ t H u v =
      (H:ℂ)⁻¹*∑ n ∈ S.filter (fun n => ¬n.Prime), f n := by
    have hfilter : (∑ n ∈ S.filter Nat.Prime, f n) =
        ∑ n ∈ S.filter Nat.Prime, χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I) := by
      apply sum_congr rfl
      intro n hn
      exact he n (mem_filter.mp hn).2
    have hs := sum_filter_add_sum_filter_not S Nat.Prime f
    rw [markedMajorLogMangoldtSum,markedMajorNormalizedPrimeSum,one_div,← mul_sub]
    congr 1
    change (∑ n ∈ S,f n)-(∑ n ∈ S.filter Nat.Prime,_) = _
    rw [← hfilter]
    linear_combination -hs
  have hnorm (n : ℕ) (hn : n ∈ S) : ‖f n‖ ≤ vonMangoldt n := by
    dsimp [f]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg
      (marked_log_character_weight_norm_le χ t u hu hlog n (mem_Ioc.mp hn).1)
  have hsub : S.filter (fun n => ¬n.Prime) ⊆ (Ioc 0 ⌊v⌋₊).filter (fun n => ¬n.Prime) := by
    intro n hn
    obtain ⟨hnS,hnP⟩ := mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hnS
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hhi⟩,hnP⟩
  rw [heq,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
  have hs : ‖∑ n ∈ S.filter (fun n => ¬n.Prime), f n‖ ≤ 2*Real.sqrt v*Real.log v := by
    calc
      _ ≤ ∑ n ∈ S.filter (fun n => ¬n.Prime), ‖f n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S.filter (fun n => ¬n.Prime), vonMangoldt n :=
        sum_le_sum (fun n hn => hnorm n (mem_filter.mp hn).1)
      _ ≤ ∑ n ∈ (Ioc 0 ⌊v⌋₊).filter (fun n => ¬n.Prime), vonMangoldt n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
      _ = Chebyshev.psi v-Chebyshev.theta v := by rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      _ ≤ _ := Chebyshev.psi_sub_theta_le hv1
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hH.le)

end ArtinMatthews
