module

public import ArtinMatthews.ShiftedABLRhoScale
public import ArtinMatthews.ShiftedABLMellinCircle


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Fourier separation of the original signed circle sum. -/

noncomputable section
open Set MeasureTheory OAI
open scoped BigOperators
namespace ArtinMatthews

def shiftedABLRhoBlockPhase (R t : ℝ) (ρ : ℤ) : ℂ :=
  FourierBridge.logPhase t (-shiftedABLRhoLogShift R (ρ.natAbs : ℝ))

theorem shiftedABLRhoBlockPhase_norm (R t : ℝ) (ρ : ℤ) :
    ‖shiftedABLRhoBlockPhase R t ρ‖ = 1 := norm_shifted_logPhase _ _

theorem shiftedABLRhoBlockPhase_square_norm (u : Finset ℤ) (α : ℤ → ℂ) (R t : ℝ) :
    (∑ ρ ∈ u, ‖α ρ*shiftedABLRhoBlockPhase R t ρ‖^2) = ∑ ρ ∈ u, ‖α ρ‖^2 := by
  simp only [norm_mul,shiftedABLRhoBlockPhase_norm,mul_one]

def shiftedABLSeparatedSignedSum (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 F r L : ℕ) (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (t : ℝ) : ℂ :=
  let R := (2 : ℝ)^i.1
  let n := shiftedABLFirstIndex m3 m4
  let u := t+shiftedABLRhoHeight z
  ∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ = i),
    (shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z*shiftedABLRhoBlockPhase R u ρ)*
      ∑ c ∈ shiftedABLMellinModuli F r L,
        shiftedABLMellinKloosterman (F*c) m3 m4 ρ/(c : ℂ)*
          shiftedABLRhoCommonTest (shiftedABLRhoBlockScale L n r R) u (shiftedABLRhoOrbitalArgument F n r ρ c)

theorem shiftedABLRhoFourierTest_integrable (a b x u : ℝ) :
    Integrable (fun t : ℝ => shiftedABLRhoFourierDensity t*FourierBridge.logPhase (t+u) (-b)*
      shiftedABLRhoCommonTest a (t+u) x) := by
  have hP (v : ℝ) : Continuous (fun t : ℝ => FourierBridge.logPhase (t+u) v) := by
    change Continuous (fun t : ℝ => Complex.exp
      (Complex.ofRealCLM (2*Real.pi*(t+u)*v)*Complex.I))
    fun_prop
  have hF : Continuous (fun t : ℝ => shiftedABLRhoCommonTest a (t+u) x) := by
    by_cases hx : 0 < x
    · simp only [shiftedABLRhoCommonTest,ite_eq_left hx]
      exact continuous_const.mul (hP _)
    · simp only [shiftedABLRhoCommonTest,ite_eq_right hx]
      exact continuous_const
  have hm := (shiftedABLRhoFourierDensity.continuous.mul (hP (-b))).mul hF
  apply shiftedABLRhoFourierDensity.integrable.norm.mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    change ‖shiftedABLRhoFourierDensity t*FourierBridge.logPhase (t+u) (-b)*
      shiftedABLRhoCommonTest a (t+u) x‖ ≤ ‖shiftedABLRhoFourierDensity t‖
    rw [norm_mul,norm_mul,norm_shifted_logPhase,mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (shiftedABLRhoCommonTest_norm_le a (t+u) x))

theorem shiftedABLRhoSignedBlock_band {m3 m4 : ℕ} {d : ℕ × ℕ} {i : ℕ × Bool} {ρ : ℤ}
    (hρ : ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ = i)) :
    ρ ≠ 0 ∧ (2 : ℝ)^i.1 ≤ (ρ.natAbs : ℝ) ∧ (ρ.natAbs : ℝ) ≤ 2*(2 : ℝ)^i.1 := by
  obtain ⟨hu,hi⟩ := Finset.mem_filter.mp hρ
  have hnz := (shiftedABLDualFrequencies_witness hu).1
  have hindex : i.1 = Nat.log 2 ρ.natAbs := (congrArg Prod.fst hi).symm
  obtain ⟨hl,hh⟩ := shiftedABLFrequency_dyadic hnz
  refine ⟨hnz,?_,?_⟩
  · rw [hindex]
    exact_mod_cast hl
  · rw [hindex,← mul_comm ((2 : ℝ)^(Nat.log 2 ρ.natAbs)),← pow_succ]
    exact_mod_cast hh.le

theorem shiftedABLMellinSignedSum_rho_separation (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 F r L : ℕ) (hne : m3 ≠ m4) (hF : 0 < F) (hr : 0 < r) (hL : 0 < L)
    (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) :
    Integrable (fun t : ℝ => shiftedABLRhoFourierDensity t*
      shiftedABLSeparatedSignedSum χ D m3 m4 F r L d i z t) ∧
    shiftedABLMellinSignedSum χ D m3 m4 F r L d i z =
      ∫ t : ℝ, shiftedABLRhoFourierDensity t*shiftedABLSeparatedSignedSum χ D m3 m4 F r L d i z t := by
  let U := (shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ = i)
  let C := shiftedABLMellinModuli F r L
  let R := (2 : ℝ)^i.1
  let n := shiftedABLFirstIndex m3 m4
  let a := shiftedABLRhoBlockScale L n r R
  let x (ρ : ℤ) (c : ℕ) := shiftedABLRhoOrbitalArgument F n r ρ c
  let α (ρ : ℤ) := shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z
  let S (ρ : ℤ) (c : ℕ) := shiftedABLMellinKloosterman (F*c) m3 m4 ρ/(c : ℂ)
  let V (ρ : ℤ) (c : ℕ) (t : ℝ) :=
    shiftedABLRhoFourierDensity t*shiftedABLRhoBlockPhase R (t+shiftedABLRhoHeight z) ρ*
      shiftedABLRhoCommonTest a (t+shiftedABLRhoHeight z) (x ρ c)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hn : 0 < n := Int.natAbs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  have hV (ρ : ℤ) (c : ℕ) : Integrable (V ρ c) :=
    shiftedABLRhoFourierTest_integrable a (shiftedABLRhoLogShift R (ρ.natAbs : ℝ)) (x ρ c)
      (shiftedABLRhoHeight z)
  have hEq (ρ : ℤ) (hρu : ρ ∈ U) (c : ℕ) (hc : c ∈ C) :
      shiftedABLMellinModulusWeight F L z c = ∫ t : ℝ, V ρ c t := by
    have hL₀ : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
    have hF₀ : 0 < (F : ℝ) := Nat.cast_pos.mpr hF
    have hc₀ : 0 < (c : ℝ) := (by positivity : 0 < 3*(L : ℝ)/(F : ℝ)).trans_le
      (shiftedABLMellinModuli_bounds hF hc).1
    obtain ⟨hnz,hlo,hhi⟩ := shiftedABLRhoSignedBlock_band hρu
    exact shiftedABLMellinModulusWeight_rho_separation hF hL hn hr z hR hnz hlo hhi hc₀
  have hfun : (fun t : ℝ => shiftedABLRhoFourierDensity t*
      shiftedABLSeparatedSignedSum χ D m3 m4 F r L d i z t) =
      fun t => ∑ ρ ∈ U, ∑ c ∈ C, (α ρ*S ρ c)*V ρ c t := by
    funext t
    unfold shiftedABLSeparatedSignedSum
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [← mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [α,S,V,x,a,n,R]
    ring
  rw [hfun]
  have hI (ρ : ℤ) (c : ℕ) : Integrable (fun t => (α ρ*S ρ c)*V ρ c t) :=
    (hV ρ c).const_mul _
  refine ⟨integrable_finsetSum U (fun ρ _ => integrable_finsetSum C (fun c _ => hI ρ c)),?_⟩
  rw [integral_finsetSum U (fun ρ _ => integrable_finsetSum C (fun c _ => hI ρ c))]
  unfold shiftedABLMellinSignedSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρu
  rw [integral_finsetSum C (fun c _ => hI ρ c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [integral_const_mul,← hEq ρ hρu c hc]
  dsimp only [α,S]
  ring

end ArtinMatthews
