module

public import ArtinMatthews.SpectralPeterssonCutReproducing
public import ArtinMatthews.SpectralPeterssonPairingUnfold


set_option backward.privateInPublic true
@[expose] public section

/-! Exact unfolding of the literal height-cut Poincare series. Its finite
row support removes the weight-two summation obstruction. -/
noncomputable section
open Set MeasureTheory Matrix UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

theorem gamma0PeterssonTruncatedInner_unfold (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (A : ℝ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (hI : Integrable (fun z => UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed n A)
      (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F) z)) :
    gamma0PeterssonInner N k (gamma0PeterssonTruncatedPoincare N a k n A) F =
      ∫ z, UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed n A)
        (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F) z := by
  let σ := gamma0TrueCuspScaling N a
  let P := spectralPeterssonStripCutSeed n A
  let G (z : UpperHalfPlane) := UpperHalfPlane.petersson (k : ℤ) P (spectralHolomorphicSlash k σ F) z
  let U (z : UpperHalfPlane) := G (σ⁻¹ • z)
  have hpres : MeasurePreserving (fun z : UpperHalfPlane => σ⁻¹ • z) volume volume := by
    change MeasurePreserving (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ σ⁻¹ • z) _ _
    exact measurePreserving_smul _ _
  have hemb : MeasurableEmbedding (fun z : UpperHalfPlane => σ⁻¹ • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ σ⁻¹ • z)
    exact measurableEmbedding_const_smul _
  have hG : Integrable G := by simpa only [G,P,σ] using! hI
  have hU : Integrable U := by
    simpa only [U,Function.comp_def] using! hpres.integrable_comp_of_integrable (g := G) hG
  have hi : (∫ z, U z) = ∫ z, G z := hpres.integral_comp hemb G
  have hterm (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
      U (γ.val • z) = UpperHalfPlane.petersson (k : ℤ)
        (spectralHolomorphicSlash k (σ⁻¹*atkinRealMap γ.val) P) F z := by
    let H := σ⁻¹*atkinRealMap γ.val
    have hb : spectralHolomorphicSlash k H (spectralHolomorphicSlash k σ F) = F := by
      rw [← spectralHolomorphicSlash_mul,show σ*H = atkinRealMap γ.val by dsimp only [H]; group]
      exact hF γ
    have hp := spectralHolomorphicPetersson_slash k H P (spectralHolomorphicSlash k σ F) z
    rw [hb] at hp
    have he : H • z = σ⁻¹ • (γ.val • z) := by
      dsimp only [H]
      rw [mul_smul,atkinRealMap_smul]
    rw [he] at hp
    exact hp.symm
  have hpoint (z : UpperHalfPlane) :
      (∑' γ : CongruenceSubgroup.Gamma0 N, U (γ.val⁻¹ • z)) =
        (2 : ℂ)*UpperHalfPlane.petersson (k : ℤ) (gamma0PeterssonTruncatedPoincare N a k n A) F z := by
    have hsum : (∑' γ : CongruenceSubgroup.Gamma0 N,
        spectralHolomorphicSlash k (σ⁻¹*atkinRealMap γ.val) P z) =
        (2 : ℂ)*gamma0PeterssonTruncatedPoincare N a k n A z := by
      rw [gamma0PeterssonTruncatedPoincare_periodization]
      dsimp only [P,σ]
      ring
    calc
      _ = ∑' γ : CongruenceSubgroup.Gamma0 N, U (γ.val • z) := by
        simpa only [Equiv.inv_apply,Subgroup.coe_inv] using
          (Equiv.inv (CongruenceSubgroup.Gamma0 N)).tsum_eq (fun γ => U (γ.val • z))
      _ = ∑' γ : CongruenceSubgroup.Gamma0 N, UpperHalfPlane.petersson (k : ℤ)
          (spectralHolomorphicSlash k (σ⁻¹*atkinRealMap γ.val) P) F z :=
        tsum_congr (fun γ => hterm γ z)
      _ = _ := by
        simp only [UpperHalfPlane.petersson]
        rw [tsum_mul_right,tsum_mul_right,← Complex.conj_tsum,hsum,map_mul]
        norm_num only [map_ofNat]
        ring
  have h := gamma0PeterssonRegion_integral_unfold N U hU
  have he : (∫ z in gamma0InteriorRegion N, ∑' γ : CongruenceSubgroup.Gamma0 N, U (γ.val⁻¹ • z)) =
      (2 : ℂ)*gamma0PeterssonInner N k (gamma0PeterssonTruncatedPoincare N a k n A) F := by
    simp_rw [hpoint]
    exact integral_const_mul _ _
  rw [he,hi] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

theorem gamma0PeterssonTruncatedInner_reproduce (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ+) (A : ℝ) (hA : 0 < A) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (hCont : Continuous (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)) (M : ℝ)
    (hbd : ∀ z, ‖spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F z‖*z.im^((k : ℝ)/2) ≤ M)
    (b : ℂ) (hb : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight
      (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F) n y hy = b) :
    gamma0PeterssonInner N k (gamma0PeterssonTruncatedPoincare N a k n A) F =
      (spectralPeterssonTruncatedMass k n A : ℂ)*b := by
  rw [gamma0PeterssonTruncatedInner_unfold N a k n A F hF
    (spectralPeterssonCutStrip_integrable k hk n A hA _ hCont M hbd)]
  exact spectralPeterssonCutStrip_reproduce k hk n A hA _ hCont M hbd b hb

end ArtinMatthews
