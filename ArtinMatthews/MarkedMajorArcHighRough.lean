module

public import ArtinMatthews.MarkedMajorArcRoughTruncation
public import ArtinMatthews.MarkedMajorArcRoughParameters
public import ArtinMatthews.MarkedRoughBonferroniBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine high-frequency cancellation of the fully normalized rough-number
coefficient, with the actual moving cutoff and arbitrary logarithmic saving. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_major_high_rough_cancellation (a τ P : ℝ)
    (ha : 0 ≤ a) (hτ : 0 < τ) (hP : 0 ≤ P) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t H u v : ℝ),
        (q:ℝ) ≤ L^a → L^T ≤ |t| → |t| ≤ Real.exp (2*L) →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H →
        ‖markedRoughCharacterSum χ (Real.exp (L^(6/25:ℝ))) t H u v‖ ≤ L^(-P) := by
  classical
  let B := 4/τ+1
  have hB : 1/2 ≤ B := by
    have hh : 0 ≤ 4/τ := by positivity
    dsimp [B]
    linarith
  have hBr : 4/τ ≤ B := by dsimp [B]; linarith
  obtain ⟨A,δ,U₀,hA,hδ,_,hU₀,hphase⟩ := marked_rough_character_explicit_uniform B hB
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  obtain ⟨D,hD,herror⟩ := marked_rough_bonferroni_uniform_power E (6/25) τ (6/25) P (1/2)
    (by norm_num) hP hτ (by norm_num) (by norm_num)
  obtain ⟨T,hT,hmain⟩ := marked_rough_character_uniform_power A (E^2) (a+2*(6/25))
    (τ/2) δ P (1/2) hA.le (by linarith) hP (half_pos hτ) hδ (by norm_num)
  have hSlarge := ((Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (half_pos hτ))).eventually (eventually_ge_atTop U₀))
  have hfreqlo := (tendsto_rpow_atTop hT).eventually (eventually_ge_atTop (2*Real.pi))
  refine ⟨T,hT,?_⟩
  filter_upwards [herror,hmain,marked_rough_density_inverse_cutoff (6/25) (by norm_num),
    marked_rough_prime_reciprocal_cutoff_le (6/25) (by norm_num) (by norm_num),
    marked_rough_modulus_density_budget a (6/25) (by norm_num),
    marked_rough_actual_depth_support D τ hD.le hτ,hSlarge,hfreqlo,
    eventually_ge_atTop (max 1 (1/τ))] with L herror hmain hVbound hsum hmod hsupport hU hfL hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hτL : 1 ≤ τ*L := by
    have hh := (div_le_iff₀ hτ).mp ((le_max_right _ _).trans hL)
    nlinarith
  intro q _ χ t H u v hq htlo hthi hH hHu huv hvH
  let W := Real.exp (L^(6/25:ℝ))
  let V := markedSieveEulerProduct W
  let S := Real.exp (τ*L/2)
  let r := ⌊D*Real.log L⌋₊
  let C := ∑ p ∈ Nat.primesLE ⌊W⌋₊, 1/(p:ℝ)
  have hWp : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hLp.le _)
  have hVp : 0 < V := markedSieveEulerProduct_pos W
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hup : 0 < u := hHp.trans_le hHu
  have hvp : 0 < v := hup.trans_le huv
  have hlog : 1 ≤ Real.log u := hτL.trans
    ((Real.le_log_iff_exp_le hup).mpr (hH.trans hHu))
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  have hUC : U₀ ≤ S := by simpa only [S,Function.comp_apply,id_eq,div_mul_eq_mul_div] using hU
  have htf : 1 ≤ |t/(2*Real.pi)| := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
    exact (one_le_div (by positivity)).mpr (hfL.trans htlo)
  have hds (J : Finset ℕ) (hJ : J ∈ roughTruncationSubsets (Nat.primesLE ⌊W⌋₊) r) :
      S ≤ H/(roughSubsetDivisor J:ℝ) ∧
        |t/(2*Real.pi)| ≤ (H/(roughSubsetDivisor J:ℝ))^B := by
    obtain ⟨hd,hdW⟩ := marked_rough_truncation_divisor_support hW1 r J hJ
    have hdR : (0:ℝ) < roughSubsetDivisor J := by exact_mod_cast hd
    have hdhi : (roughSubsetDivisor J:ℝ) ≤ Real.exp (τ*L/2) := hdW.trans hsupport
    exact ⟨marked_rough_divisor_length hdR hdhi hH,
      marked_rough_frequency_range hτ hLp.le hdR hdhi hH hthi hBr⟩
  have hb := hphase q χ W t H S u v r hHp hUC hds htf hHu huv hvH hlog
  have hnum := hmain (q:ℝ) V⁻¹ V S t (Nat.cast_nonneg _) (inv_nonneg.mpr hVp.le) hVp
    (hmod (q:ℝ) (Nat.cast_nonneg _) hq)
    (by dsimp [S]; rw [div_mul_eq_mul_div]) htlo
  have hfirst : 3*(q:ℝ)*A/V^2*(1/Real.sqrt |t/(2*Real.pi)|+S^(-δ)) ≤ (1/2)*L^(-P) := by
    calc
      _ = 3*(q:ℝ)*A*V⁻¹/V*(1/Real.sqrt |t/(2*Real.pi)|+S^(-δ)) := by ring
      _ ≤ _ := hnum
  have htail := herror C V H hC hsum hVp (by simpa only [one_div] using hVbound) hH
  have hsecond : markedRoughTruncationError W r ⌊u⌋₊ ⌊v⌋₊/(H*V) ≤ (1/2)*L^(-P) :=
    (marked_rough_truncation_error_bound W C H u v r hWp.le hC hHp hvp.le hvH le_rfl).trans htail
  exact hb.trans (by linarith)

end ArtinMatthews
