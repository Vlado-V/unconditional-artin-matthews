module

public import ArtinMatthews.MarkedMajorArcDivisorPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The actual complex divisor polynomial and its oscillatory reciprocal-mass
bound. This keeps the logarithmic saving of inclusion-exclusion rather than
replacing reciprocal divisor mass by the number of summands. -/
namespace ArtinMatthews
open Finset

noncomputable def markedMajorDivisorPolynomial {ι : Type*} (J : Finset ι)
    (d : ι → ℕ) (c : ι → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ i ∈ J, if d i ∣ n then c i else 0

 theorem marked_divisor_polynomial_phase_eq {ι : Type*} (J : Finset ι)
    (d : ι → ℕ) (c : ι → ℂ) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (M N : ℕ) :
    (∑ n ∈ Ioc M N, markedMajorDivisorPolynomial J d c n *
      (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))) =
    ∑ i ∈ J, c i * ∑ n ∈ Ioc M N,
      if d i ∣ n then χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I) else 0 := by
  classical
  simp only [markedMajorDivisorPolynomial,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

 theorem marked_divisor_polynomial_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧ 0 < U₀ ∧
      ∀ {ι : Type*} (J : Finset ι) (d : ι → ℕ) (c : ι → ℂ)
        (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t H S : ℝ)
        (M N : ℕ), 0 < H → U₀ ≤ S →
        (∀ i ∈ J, 0 < d i ∧ S ≤ H/d i ∧ |t/(2*Real.pi)| ≤ (H/d i)^B) →
        1 ≤ |t/(2*Real.pi)| → H ≤ (M:ℝ)+1 → (N:ℝ) ≤ 2*H →
        ‖∑ n ∈ Ioc M N, markedMajorDivisorPolynomial J d c n *
          (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))‖ ≤
        (q:ℝ)*A*H*(∑ i ∈ J, ‖c i‖/(d i:ℝ))*
          (1/Real.sqrt |t/(2*Real.pi)|+S^(-δ)) := by
  classical
  obtain ⟨A,δ,U₀,hA,hδ,hhalf,hU₀,hbound⟩ := marked_divisor_character_phase_uniform B hB
  refine ⟨A,δ,U₀,hA,hδ,hhalf,hU₀,?_⟩
  intro ι J d c q _ χ t H S M N hH hUS hi ht hM hN
  have hS : 0 < S := hU₀.trans_le hUS
  rw [marked_divisor_polynomial_phase_eq]
  calc
    _ ≤ ∑ i ∈ J, ‖c i * ∑ n ∈ Ioc M N,
        if d i ∣ n then χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ J, (q:ℝ)*A*H*(‖c i‖/(d i:ℝ))*
        (1/Real.sqrt |t/(2*Real.pi)|+S^(-δ)) := by
      apply sum_le_sum
      intro i hiJ
      obtain ⟨hd,hs,hfreq⟩ := hi i hiJ
      have hdR : (0:ℝ) < d i := by exact_mod_cast hd
      have hb := hbound q χ t H (d i) M N hd (hUS.trans hs) ht hfreq hM hN
      have hp := marked_scaled_power_reciprocal_bound hH hdR hS hs hδ.le
      rw [norm_mul]
      calc
        _ ≤ ‖c i‖*((q:ℝ)*A*((H/d i)/Real.sqrt |t/(2*Real.pi)|+(H/d i)^(1-δ))) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ ≤ ‖c i‖*((q:ℝ)*A*((H/d i)/Real.sqrt |t/(2*Real.pi)|+(H/d i)*S^(-δ))) := by
          gcongr
        _ = _ := by ring
    _ = _ := by rw [← sum_mul, ← mul_sum]

end ArtinMatthews
