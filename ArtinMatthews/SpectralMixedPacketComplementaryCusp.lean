module

public import ArtinMatthews.SpectralMixedPacketTerms
public import ArtinMatthews.SpectralInfinityComplementaryCross


set_option backward.privateInPublic true
@[expose] public section

/-! Actual complementary cusp packet bounds at the true mixed chart. -/

noncomputable section
open Set OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0MixedPacketExceptionalWeight (N : ℕ) (n : ℤ) (a ε : ℝ) : ℝ :=
  ((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
    (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a))

def gamma0MixedPacketExceptionalSize (N : ℕ) (B : ℝ) (n : ℤ) (a ε S : ℝ) : ℝ :=
  Real.sqrt (S*(1+B/(N : ℝ)))*Real.sqrt (1+gamma0MixedPacketExceptionalWeight N n a ε)

theorem gamma0MixedPacketExceptionalWeight_nonneg (N : ℕ) (n : ℤ) {a ε : ℝ} (ha : 0 < a) :
    0 ≤ gamma0MixedPacketExceptionalWeight N n a ε := by
  unfold gamma0MixedPacketExceptionalWeight
  positivity

theorem gamma0MixedCusp_exceptional_cosine_moment_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ E : ℝ, 0 < E ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (U : Finset (Gamma0AllHeightSpectralIndex (r*s))) (n : ℤ) (hn : n ≠ 0)
        {a Y : ℝ}, 0 < a → a ≤ 1 → ∀ hY : 0 < Y,
      Y < (a^2/2)/(|cuspFourierFrequency 1 n|/
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ i ∈ U, gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4) →
      gamma0CuspCosineExceptionalMoment (r*s) U (gamma0CuspOneOver s) Y hY n hn a ≤
        E*(1+gamma0MixedPacketExceptionalWeight (r*s) n a ε) := by
  obtain ⟨D,hD,hRight⟩ := gamma0MixedCusp_exceptional_compact_density_le hε
  let c := Real.exp (-Real.exp 1)/16
  let e := Real.cos (Real.pi/4)
  have he : 0 < e := by dsimp only [e]; rw [Real.cos_pi_div_four]; positivity
  have hc : 0 < c^2*e := by dsimp only [c]; positivity
  let E := (1+8*D)/(c^2*e)
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨E,hE,?_⟩
  intro r s ir is hcop U n hn a Y ha ha₁ hY hYR hSpec
  let N := r*s
  let b := gamma0CuspOneOver s
  let W := gamma0MixedPacketExceptionalWeight N n a ε
  let V := gamma0CuspCosineExceptionalMoment N U b Y hY n hn a
  have hW : 0 ≤ W := gamma0MixedPacketExceptionalWeight_nonneg N n ha
  have hR := hRight r s hcop U n hn ha ha₁ hY hYR hSpec
  rw [mul_assoc D] at hR
  change c^2*(e*V) ≤ 1+8*(D*W) at hR
  have hRv : V ≤ E*(1+W) := by
    have hM : c^2*e*V ≤ (1+8*D)*(1+W) := by
      rw [mul_assoc]
      exact hR.trans (by nlinarith only [mul_nonneg hD.le hW,hW,hD.le])
    calc
      _ ≤ ((1+8*D)*(1+W))/(c^2*e) := (le_div_iff₀ hc).mpr (by rw [mul_comm]; exact hM)
      _ = _ := by dsimp only [E]; ring
  exact hRv

theorem gamma0MixedPacket_complementary_cusp_bound_of_moments
    {ι : Type*} (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (h : SpectralEnergyTest)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    {B a H ε C E : ℝ} (ha : 0 < a) (hH : 0 ≤ H) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hSym : ∀ l : Ici (0 : ℝ), 3/16 ≤ (l : ℝ) → (l : ℝ) ≤ 1/4 →
      ‖h l‖ ≤ H*a^(-2*Real.sqrt (1/4-(l : ℝ)))/
        Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ))))
    (hL : (∑ i ∈ gamma0HeatComplementaryCuspidalIndices N,
        ‖gamma0InfinityCuspPacketAmplitude N i v α m hm Y hY‖^2/
          Real.cos (Real.pi*Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i))) ≤
      C*(1+B/(N : ℝ))*(∑ j ∈ v, ‖α j‖^2))
    (hRv : gamma0CuspCosineExceptionalMoment N (gamma0HeatComplementaryCuspidalIndices N)
      b Y hY n hn a ≤ E*(1+gamma0MixedPacketExceptionalWeight N n a ε)) :
    (∑ i ∈ gamma0HeatComplementaryCuspidalIndices N,
      ‖gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm i‖) ≤
      (Real.sqrt C*Real.sqrt E/4)*H*
        gamma0MixedPacketExceptionalSize N B n a ε (∑ j ∈ v, ‖α j‖^2) := by
  let U := gamma0HeatComplementaryCuspidalIndices N
  let S := ∑ j ∈ v, ‖α j‖^2
  let W := gamma0MixedPacketExceptionalWeight N n a ε
  have hcross := gamma0Infinity_complementary_cusp_cross_bound N v α m hm b Y hY n hn h ha hH hSym
  change (∑ i ∈ U, ‖gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm i‖) ≤ _
  refine hcross.trans ?_
  calc
    _ ≤ (H/4)*Real.sqrt (C*(1+B/(N : ℝ))*S)*Real.sqrt (E*(1+W)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL) (by positivity))
        (Real.sqrt_le_sqrt hRv) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      unfold gamma0MixedPacketExceptionalSize
      rw [show C*(1+B/(N : ℝ))*S = C*(S*(1+B/(N : ℝ))) by ring,
        Real.sqrt_mul hC,Real.sqrt_mul hE]
      dsimp only [W]
      ring

theorem gamma0MixedPacket_complementary_cusp_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (h : SpectralEnergyTest) (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ)
        (hm : ∀ j, m j ≠ 0), Function.Injective m →
      ∀ (n : ℤ) (hn : n ≠ 0) {B a H Y : ℝ},
      0 < B → 0 < a → a ≤ 1 → 0 ≤ H → ∀ hY : 0 < Y,
      Y < (1/4)/B →
      Y < (a^2/2)/(|cuspFourierFrequency 1 n|/
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ j, |cuspFourierFrequency 1 (m j)| ≤ B) →
      (∀ l : Ici (0 : ℝ), 3/16 ≤ (l : ℝ) → (l : ℝ) ≤ 1/4 →
        ‖h l‖ ≤ H*a^(-2*Real.sqrt (1/4-(l : ℝ)))/
          Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ)))) →
      let N := r*s
      (∑ i ∈ gamma0HeatComplementaryCuspidalIndices N,
        ‖gamma0MixedPacketCuspidalTerm N h (gamma0CuspOneOver s) Y hY n hn v α m hm i‖) ≤
        C*H*gamma0MixedPacketExceptionalSize N B n a ε (∑ j ∈ v, ‖α j‖^2) := by
  obtain ⟨C,hC,hLeft⟩ := gamma0Infinity_complementary_packet_orbit_bessel
  obtain ⟨E,hE,hRight⟩ := gamma0MixedCusp_exceptional_cosine_moment_bound hε
  refine ⟨Real.sqrt C*Real.sqrt E/4,by positivity,?_⟩
  intro ι r s ir is hcop h v α m hm hinj n hn B a H Y hB ha ha₁ hH hY hYL hYR hfreq hSym
  have hSpec (i : Gamma0AllHeightSpectralIndex (r*s))
      (hi : i ∈ gamma0HeatComplementaryCuspidalIndices (r*s)) :
      gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4 :=
    ((mem_gamma0HeatComplementaryCuspidalIndices (r*s) i).mp hi).le
  have hL := hLeft (r*s) (gamma0HeatComplementaryCuspidalIndices (r*s))
    v α m hinj hm hB hY hYL hfreq hSpec
  have hRv := @hRight r s ir is hcop (gamma0HeatComplementaryCuspidalIndices (r*s))
    n hn a Y ha ha₁ hY hYR hSpec
  exact gamma0MixedPacket_complementary_cusp_bound_of_moments
    (r*s) (gamma0CuspOneOver s) h v α m hm n hn Y hY
    (B := B) (a := a) (H := H) (ε := ε) (C := C) (E := E)
    ha hH hC.le hE.le hSym hL hRv

end ArtinMatthews
