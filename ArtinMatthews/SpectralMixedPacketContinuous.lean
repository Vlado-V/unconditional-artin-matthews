module

public import ArtinMatthews.SpectralMixedPacketPrincipalCore
public import ArtinMatthews.SpectralInfinityContinuousCutoff
public import ArtinMatthews.SpectralMixedCuspContinuousCutoff
public import ArtinMatthews.SpectralPrincipalWeightedCrossIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive-frequency packet is controlled in its own
measure by the two genuine continuous cutoff bounds. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

private theorem cutoff_eq_preimage (R : ℝ) :
    spectralPrincipalCutoff (fun t : ℝ => t) R = (fun t : ℝ => 1+|t|) ⁻¹' Icc 1 R := by
  ext t
  change (1+|t| ≤ R) ↔ (1 ≤ 1+|t| ∧ 1+|t| ≤ R)
  exact ⟨fun h => ⟨le_add_of_nonneg_right (abs_nonneg _),h⟩,And.right⟩

private theorem aemeasurable_from_cutoffs (μ : Measure ℝ) (f : ℝ → ℝ)
    (h : ∀ R : ℝ, 1 ≤ R → IntegrableOn f (spectralPrincipalCutoff (fun t : ℝ => t) R) μ) :
    AEMeasurable f μ := by
  let U (k : ℕ) := spectralPrincipalCutoff (fun t : ℝ => t) ((k : ℝ)+1)
  have hCover : (⋃ k, U k) = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨k,hk⟩ := exists_nat_ge |t|
    exact mem_iUnion.mpr ⟨k,by change 1+|t| ≤ (k : ℝ)+1; linarith⟩
  have ha := aemeasurable_iUnion_iff.mpr
    (fun k : ℕ => (h ((k : ℝ)+1) (le_add_of_nonneg_left (Nat.cast_nonneg k))).aestronglyMeasurable.aemeasurable)
  change AEMeasurable f (μ.restrict (⋃ k, U k)) at ha
  rwa [hCover,Measure.restrict_univ] at ha

private theorem packet_continuous_aemeasurable {ι : Type*} (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0) :
    AEMeasurable (gamma0MixedPacketContinuousIntegrand N h b Y hY n hn v α m hm)
      gamma0EisensteinSpectralMeasure := by
  let I := gamma0MixedPacketContinuousIntegrand N h b Y hY n hn v α m hm
  let G (j : ι) := gamma0BareContinuousRhoIntegrand N h b 1 Y hY n (m j) hn (hm j)
  have hπ : ((2*Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hI : I = fun t => ((2*Real.pi : ℝ) : ℂ)*(∑ j ∈ v, α j*G j t) := by
    funext t
    exact ((div_eq_iff hπ).mp
      (gamma0MixedPacketContinuousIntegrand_eq_sum N h b Y hY n hn v α m hm t)).trans (mul_comm _ _)
  change AEMeasurable I gamma0EisensteinSpectralMeasure
  rw [hI]
  have hG (j : ι) : AEStronglyMeasurable (fun t => α j*G j t) (volume.restrict (Ioi (0 : ℝ))) :=
    (gamma0BareContinuousRhoIntegrand_aestronglyMeasurable N h b 1 Y hY n (m j) hn (hm j)).const_mul _
  exact (((v.aestronglyMeasurable_fun_sum (fun j _ => hG j)).const_mul
    ((2*Real.pi : ℝ) : ℂ)).smul_measure _).aemeasurable

private theorem channel_cross_bound {κ : Type*} [Fintype κ] (A D : κ → ℂ)
    (z : ℂ) (W H d : ℝ) (hW : 0 < W) (hz : ‖z‖ ≤ H*d/W) :
    ‖(z*∑ i, D i*star (A i))/4‖ ≤ (H/4)*d*
      Real.sqrt ((∑ i, ‖A i‖^2)/W)*Real.sqrt ((∑ i, ‖D i‖^2)/W) := by
  have hA : 0 ≤ ∑ i, ‖A i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ ∑ i, ‖D i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : ‖∑ i, D i*star (A i)‖ ≤ Real.sqrt (∑ i, ‖A i‖^2)*Real.sqrt (∑ i, ‖D i‖^2) := by
    calc
      _ ≤ ∑ i, ‖D i*star (A i)‖ := norm_sum_le _ _
      _ = ∑ i, ‖A i‖*‖D i‖ := by simp only [norm_mul,norm_star,mul_comm]
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖A i‖) (fun i => ‖D i‖)
  have hHd : 0 ≤ H*d/W := (norm_nonneg _).trans hz
  rw [norm_div,norm_mul,show ‖(4 : ℂ)‖ = 4 from Complex.norm_natCast 4]
  calc
    _ ≤ (H*d/W*(Real.sqrt (∑ i, ‖A i‖^2)*Real.sqrt (∑ i, ‖D i‖^2)))/4 :=
      div_le_div_of_nonneg_right (mul_le_mul hz hsum (norm_nonneg _) hHd) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_div hA,Real.sqrt_div hD]
      have he : (Real.sqrt (∑ i, ‖A i‖^2)/Real.sqrt W)*
          (Real.sqrt (∑ i, ‖D i‖^2)/Real.sqrt W) =
          (Real.sqrt (∑ i, ‖A i‖^2)*Real.sqrt (∑ i, ‖D i‖^2))/W := by
        rw [div_mul_div_comm,← pow_two,Real.sq_sqrt hW.le]
      rw [mul_assoc ((H/4)*d),he]
      ring

theorem gamma0MixedPacket_principal_continuous_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (h : SpectralEnergyTest) (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ)
        (hm : ∀ j, m j ≠ 0), Function.Injective m →
      ∀ (n : ℤ) (hn : n ≠ 0) {B Z H Y : ℝ},
      0 < B → 1 ≤ Z → 0 ≤ H → ∀ hY : 0 < Y,
      Y < (1/16)/B →
      Y < (1/16)/(|cuspFourierFrequency 1 n|/
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ j, |cuspFourierFrequency 1 (m j)| ≤ B) →
      (∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ ≤
        H*spectralPrincipalDecayWeight Z t/Real.cosh (Real.pi*t)) →
      let N := r*s
      let F := gamma0MixedPacketContinuousIntegrand N h (gamma0CuspOneOver s) Y hY n hn v α m hm
      Integrable F gamma0EisensteinSpectralMeasure ∧
        (∫ t, ‖F t‖ ∂gamma0EisensteinSpectralMeasure) ≤
          C*H*gamma0MixedPacketPrincipalSize N B |cuspFourierFrequency 1 n| Z
            (∑ j ∈ v, ‖α j‖^2) := by
  obtain ⟨C₁,hC₁,hLeft⟩ := gamma0Infinity_continuous_packet_cutoff_bound
  obtain ⟨C₂,hC₂,hRight⟩ := gamma0MixedCusp_continuous_cutoff_orbit_bound
  refine ⟨Real.sqrt (8*C₁)*Real.sqrt (8*C₂)/4,by positivity,?_⟩
  intro ι r s ir is hcop h v α m hm hinj n hn B Z H Y hB hZ hH hY hYL hYR hfreq hSym
  let N := r*s
  let b := gamma0CuspOneOver s
  let q := |cuspFourierFrequency 1 n|
  let S := ∑ j ∈ v, ‖α j‖^2
  let μ := gamma0EisensteinSpectralMeasure
  let f := gamma0InfinityContinuousPacketDensity N v α m hm Y hY
  let g := gamma0ContinuousPrincipalDensity N b Y hY n hn
  let F := gamma0MixedPacketContinuousIntegrand N h b Y hY n hn v α m hm
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hf (t : ℝ) : 0 ≤ f t := div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Real.cosh_pos _).le
  have hg (t : ℝ) : 0 ≤ g t := div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Real.cosh_pos _).le
  have hcutL (R : ℝ) (hR : 1 ≤ R) :
      IntegrableOn f (spectralPrincipalCutoff (fun t : ℝ => t) R) μ ∧
        (∫ t in spectralPrincipalCutoff (fun t : ℝ => t) R, f t ∂μ) ≤
          (C₁*S)*(R^2+(B/(N : ℝ))*R) := by
    have hh := hLeft N v α m hinj hm hR hB hY hYL hfreq
    rw [cutoff_eq_preimage]
    exact ⟨hh.1,hh.2.trans_eq (by ring)⟩
  have hcutR (R : ℝ) (hR : 1 ≤ R) :
      IntegrableOn g (spectralPrincipalCutoff (fun t : ℝ => t) R) μ ∧
        (∫ t in spectralPrincipalCutoff (fun t : ℝ => t) R, g t ∂μ) ≤
          C₂*(R^2+(q/(N : ℝ))*R) := by
    have hh := hRight r s hcop n hn hR hY hYR
    rw [cutoff_eq_preimage]
    exact ⟨hh.1,hh.2.trans_eq (by ring)⟩
  have hfm := aemeasurable_from_cutoffs μ f (fun R hR => (hcutL R hR).1)
  have hgm := aemeasurable_from_cutoffs μ g (fun R hR => (hcutR R hR).1)
  have hFm : AEMeasurable F μ := packet_continuous_aemeasurable N h b Y hY n hn v α m hm
  have hDom : ∀ᵐ t ∂μ, ‖F t‖ ≤ (H/4)*spectralPrincipalDecayWeight Z t*Real.sqrt (f t)*Real.sqrt (g t) :=
    ae_of_all _ (fun t => channel_cross_bound (gamma0InfinityContinuousPacketFourier N v α m hm Y hY · t)
      (fun a => gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N a)
        b Y hY n hn (eisensteinCriticalPoint t)) (spectralContinuousTestSymbol h t)
      (Real.cosh (Real.pi*t)) H (spectralPrincipalDecayWeight Z t) (Real.cosh_pos _) (hSym t))
  have hB₁ : 0 ≤ B/(N : ℝ) := by positivity
  have hB₂ : 0 ≤ q/(N : ℝ) := by dsimp only [q]; positivity
  obtain ⟨hI,hcross⟩ := spectralPrincipal_cross_integral μ (fun t : ℝ => t) f g F measurable_id
    hfm hgm hFm hf hg (div_nonneg hH (by norm_num)) hZ hB₁ hB₂ (mul_nonneg hC₁.le hS) hC₂.le
    hDom hcutL hcutR
  refine ⟨hI,hcross.trans_eq ?_⟩
  unfold gamma0MixedPacketPrincipalSize
  have hL : 8*(C₁*S)*(Z^2+(B/(N : ℝ))*Z) = (8*C₁)*(S*(Z^2+B*Z/(N : ℝ))) := by ring
  have hR : 8*C₂*(Z^2+(q/(N : ℝ))*Z) = (8*C₂)*(Z^2+q*Z/(N : ℝ)) := by ring
  rw [hL,hR,Real.sqrt_mul (by positivity : 0 ≤ 8*C₁),Real.sqrt_mul (by positivity : 0 ≤ 8*C₂)]
  ring

end ArtinMatthews
