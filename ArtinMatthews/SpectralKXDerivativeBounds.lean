module

public import ArtinMatthews.SpectralKXDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform physical derivative envelopes for the actual K kernel.
The finite adjacent-order recurrence bounds each norm by an average of
shifted-kernel norms. The normalized order-strip bound controls each order. -/

noncomputable section
open Set
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKXDerivative_norm_le (n : ℕ) (B M t x : ℝ)
    (hK : ∀ σ : ℝ, |σ| ≤ B → ‖schlafliBesselK ((σ : ℂ)+(t : ℂ)*Complex.I) x‖ ≤ M)
    (δ : ℝ) (hδ : |δ|+(n : ℝ) ≤ B) :
    ‖spectralKXDerivative n ((δ : ℂ)+(t : ℂ)*Complex.I) x‖ ≤ M := by
  induction n generalizing δ with
  | zero =>
    simpa only [spectralKXDerivative_zero] using hK δ (by simpa only [Nat.cast_zero,add_zero] using hδ)
  | succ n ih =>
    have hm : |δ-1|+(n : ℝ) ≤ B := by
      have ht := abs_sub δ (1 : ℝ)
      norm_num at ht
      push_cast at hδ
      linarith
    have hp : |δ+1|+(n : ℝ) ≤ B := by
      have ht := abs_add_le δ (1 : ℝ)
      norm_num at ht
      push_cast at hδ
      linarith
    have hem : ((δ : ℂ)+(t : ℂ)*Complex.I)-1 = ((δ-1 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by push_cast;ring
    have hep : ((δ : ℂ)+(t : ℂ)*Complex.I)+1 = ((δ+1 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by push_cast;ring
    rw [spectralKXDerivative_succ,hem,hep,norm_mul]
    calc
      _ ≤ ‖(-(1/2) : ℂ)‖*(‖spectralKXDerivative n (((δ-1 : ℝ) : ℂ)+(t : ℂ)*Complex.I) x‖+
          ‖spectralKXDerivative n (((δ+1 : ℝ) : ℂ)+(t : ℂ)*Complex.I) x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ ≤ ‖(-(1/2) : ℂ)‖*(M+M) :=
        mul_le_mul_of_nonneg_left (add_le_add (ih (δ-1) hm) (ih (δ+1) hp)) (norm_nonneg _)
      _ = M := by norm_num;ring

theorem spectralKXDerivative_closed_strip_bound (n k : ℕ) (B a : ℝ) (hB : 0 ≤ B)
    (hBk : B+(n : ℝ)+1 < (k : ℝ)+1/2) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t x : ℝ, |δ| ≤ B → a ≤ x →
      Real.exp (Real.pi*|t|/2)*‖spectralKXDerivative n ((δ : ℂ)+(t : ℂ)*Complex.I) x‖ ≤
        C*(1+|t|)^k/x^k := by
  obtain ⟨C,hC,hK⟩ := schlafliBesselK_closed_strip_polynomial_bound k (B+(n : ℝ)) a
    (by positivity) hBk ha
  refine ⟨C,hC,?_⟩
  intro δ t x hδ hx
  let E := C*(1+|t|)^k/x^k
  let L := Real.exp (Real.pi*|t|/2)
  have hL : 0 < L := Real.exp_pos _
  have hb : ∀ σ : ℝ, |σ| ≤ B+(n : ℝ) →
      ‖schlafliBesselK ((σ : ℂ)+(t : ℂ)*Complex.I) x‖ ≤ E/L := by
    intro σ hσ
    apply (le_div_iff₀ hL).mpr
    simpa only [mul_comm] using hK σ t x hσ hx
  have hd := spectralKXDerivative_norm_le n (B+(n : ℝ)) (E/L) t x hb δ (by linarith)
  have he := (le_div_iff₀ hL).mp hd
  simpa only [mul_comm] using he

theorem schlafliBesselK_iteratedDeriv_closed_strip_bound (n k : ℕ) (B a : ℝ) (hB : 0 ≤ B)
    (hBk : B+(n : ℝ)+1 < (k : ℝ)+1/2) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t x : ℝ, |δ| ≤ B → a ≤ x →
      Real.exp (Real.pi*|t|/2)*‖iteratedDeriv n (schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I)) x‖ ≤
        C*(1+|t|)^k/x^k := by
  obtain ⟨C,hC,hbound⟩ := spectralKXDerivative_closed_strip_bound n k B a hB hBk ha
  refine ⟨C,hC,?_⟩
  intro δ t x hδ hx
  rw [schlafliBesselK_iteratedDeriv_eq n _ x (ha.trans_le hx)]
  exact hbound δ t x hδ hx

theorem schlafliBesselK_iteratedDeriv_compact_bound (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t x : ℝ, a ≤ x →
      Real.exp (Real.pi*|t|/2)*‖iteratedDeriv n (schlafliBesselK ((t : ℂ)*Complex.I)) x‖ ≤
        C*(1+|t|)^(n+2) := by
  obtain ⟨C,hC,hbound⟩ := schlafliBesselK_iteratedDeriv_closed_strip_bound n (n+2) 0 a
    le_rfl (by push_cast;linarith) ha
  refine ⟨C/a^(n+2),by positivity,?_⟩
  intro t x hx
  have hp : a^(n+2) ≤ x^(n+2) := pow_le_pow_left₀ ha.le hx _
  have he := hbound 0 t x (by simp) hx
  simp only [Complex.ofReal_zero,zero_add] at he
  apply he.trans
  calc
    _ ≤ C*(1+|t|)^(n+2)/a^(n+2) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos ha _) hp
    _ = _ := by ring

theorem spectralKXDerivative_compact_bound (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t x : ℝ, a ≤ x →
      Real.exp (Real.pi*|t|/2)*‖spectralKXDerivative n ((t : ℂ)*Complex.I) x‖ ≤
        C*(1+|t|)^(n+2) := by
  obtain ⟨C,hC,hbound⟩ := schlafliBesselK_iteratedDeriv_compact_bound n a ha
  refine ⟨C,hC,?_⟩
  intro t x hx
  rw [← schlafliBesselK_iteratedDeriv_eq n _ x (ha.trans_le hx)]
  exact hbound t x hx

theorem schlafliBesselK_iteratedDeriv_three_quarter_decay (n N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t x : ℝ, |δ| ≤ 3/4 → 1 ≤ x →
      Real.exp (Real.pi*|t|/2)*‖iteratedDeriv n (schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I)) x‖ ≤
        C*(1+|t|)^(N+n+2)/x^N := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  obtain ⟨C,hC,hbound⟩ := schlafliBesselK_iteratedDeriv_closed_strip_bound n (N+n+2) (3/4) 1
    (by norm_num) (by push_cast;linarith) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro δ t x hδ hx
  apply (hbound δ t x hδ hx).trans
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : x^N ≤ x^(N+n+2) := pow_le_pow_right₀ hx (by omega)
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 N) hp

end ArtinMatthews
