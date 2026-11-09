module

public import ArtinMatthews.SpectralOrbitalCompactSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Removing the target horizontal window by the literal period-N partition. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

def cuspPartialOrbitalIntegrand (N : ℕ) (ψ : h2SmoothCompactSeeds)
    (n : ℤ) (η : ℝ → ℝ) (R : SL(2, ℤ)) (k : ℤ) (z : UpperHalfPlane) : ℂ :=
  inner ℂ (ψ.val z) (cuspFourierWave N n η
    (R • (integerTranslation ((N : ℤ)*k) • z)))

theorem cuspPartialOrbitalIntegrand_finsum (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℤ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hpη : tsupport η ⊆ Ioi (0 : ℝ)) (R : SL(2, ℤ)) (k : ℤ) (z : UpperHalfPlane) :
    cuspPartialOrbitalIntegrand N ψ n η R k z =
      ∑ᶠ l : ℤ, cuspOrbitalIntegrand N ψ
        (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη) R (k,l) z := by
  unfold cuspPartialOrbitalIntegrand
  rw [← cuspFourierTestSeed_parabolic_finsum N n η hη hcη hpη
    (R • (integerTranslation ((N : ℤ)*k) • z))]
  simp only [RCLike.inner_apply]
  rw [finsum_mul]
  congr 1
  funext l
  simp only [cuspOrbitalIntegrand,cuspOrbitalMatrix,RCLike.inner_apply,mul_smul]

theorem cuspPartialOrbitalIntegrand_hasFiniteSupport (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℤ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hpη : tsupport η ⊆ Ioi (0 : ℝ)) (R : SL(2, ℤ)) (hR : R 1 0 ≠ 0) :
    Function.HasFiniteSupport (cuspPartialOrbitalIntegrand N ψ n η R) := by
  let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη
  have h := finiteFunctionSupport_fibre_sum (cuspOrbitalIntegrand N ψ φ R)
    (cuspOrbitalIntegrand_hasFiniteSupport N ψ φ R hR)
  have he : (fun k z => ∑ᶠ l : ℤ, cuspOrbitalIntegrand N ψ φ R (k,l) z) =
      cuspPartialOrbitalIntegrand N ψ n η R := by
    funext k z
    exact (cuspPartialOrbitalIntegrand_finsum N ψ n η hη hcη hpη R k z).symm
  rwa [he] at h

theorem cuspPartialOrbitalIntegrand_integrable (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℤ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hpη : tsupport η ⊆ Ioi (0 : ℝ)) (R : SL(2, ℤ)) (hR : R 1 0 ≠ 0) (k : ℤ) :
    Integrable (cuspPartialOrbitalIntegrand N ψ n η R k) := by
  let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη
  have hF := cuspOrbitalIntegrand_hasFiniteSupport N ψ φ R hR
  have h := finiteFunctionSupport_integrable volume
    (fun l => cuspOrbitalIntegrand N ψ φ R (k,l))
    (finiteFunctionSupport_fibre _ hF k)
    (fun l => cuspOrbitalIntegrand_integrable N ψ φ R (k,l))
  apply h.congr
  exact Eventually.of_forall fun z =>
    (cuspPartialOrbitalIntegrand_finsum N ψ n η hη hcη hpη R k z).symm

def cuspTranslatedOrbitalIntegrand (N : ℕ) (ψ : h2SmoothCompactSeeds)
    (n : ℤ) (η : ℝ → ℝ) (R : SL(2, ℤ)) (k : ℤ) (z : UpperHalfPlane) : ℂ :=
  inner ℂ (ψ.val (integerTranslation (-((N : ℤ)*k)) • z)) (cuspFourierWave N n η (R • z))

theorem cuspPartialOrbitalIntegrand_translate (N : ℕ) (ψ : h2SmoothCompactSeeds)
    (n : ℤ) (η : ℝ → ℝ) (R : SL(2, ℤ)) (k : ℤ) (z : UpperHalfPlane) :
    cuspPartialOrbitalIntegrand N ψ n η R k (integerTranslation (-((N : ℤ)*k)) • z) =
      cuspTranslatedOrbitalIntegrand N ψ n η R k z := by
  unfold cuspPartialOrbitalIntegrand cuspTranslatedOrbitalIntegrand
  rw [← mul_smul (integerTranslation ((N : ℤ)*k)), integerTranslation_neg,
    mul_inv_cancel,one_smul]

theorem cuspTranslatedOrbitalIntegrand_hasFiniteSupport (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℤ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hpη : tsupport η ⊆ Ioi (0 : ℝ)) (R : SL(2, ℤ)) (hR : R 1 0 ≠ 0) :
    Function.HasFiniteSupport (cuspTranslatedOrbitalIntegrand N ψ n η R) := by
  apply (cuspPartialOrbitalIntegrand_hasFiniteSupport N ψ n η hη hcη hpη R hR).subset
  intro k hk hzero
  apply hk
  funext z
  rw [← cuspPartialOrbitalIntegrand_translate]
  exact congrFun hzero _

theorem cuspTranslatedOrbitalIntegrand_integrable (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℤ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hpη : tsupport η ⊆ Ioi (0 : ℝ)) (R : SL(2, ℤ)) (hR : R 1 0 ≠ 0) (k : ℤ) :
    Integrable (cuspTranslatedOrbitalIntegrand N ψ n η R k) := by
  have hmp := h2_integer_measurePreserving (integerTranslation (-((N : ℤ)*k)))
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => integerTranslation (-((N : ℤ)*k)) • z) :=
    measurableEmbedding_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ (integerTranslation (-((N : ℤ)*k))))
  have h : Integrable (fun z : UpperHalfPlane => cuspPartialOrbitalIntegrand N ψ n η R k
      (integerTranslation (-((N : ℤ)*k)) • z)) :=
    (hmp.integrable_comp_emb hme (g := cuspPartialOrbitalIntegrand N ψ n η R k)).mpr
      (cuspPartialOrbitalIntegrand_integrable N ψ n η hη hcη hpη R hR k)
  apply h.congr
  exact Eventually.of_forall (cuspPartialOrbitalIntegrand_translate N ψ n η R k)

theorem cuspPartialOrbitalIntegral_translate (N : ℕ) (ψ : h2SmoothCompactSeeds)
    (n : ℤ) (η : ℝ → ℝ) (R : SL(2, ℤ)) (k : ℤ) :
    (∫ z, cuspPartialOrbitalIntegrand N ψ n η R k z) =
      ∫ z, cuspTranslatedOrbitalIntegrand N ψ n η R k z := by
  have h := (h2_integer_measurePreserving (integerTranslation (-((N : ℤ)*k)))).integral_comp
    (show MeasurableEmbedding (fun z : UpperHalfPlane => integerTranslation (-((N : ℤ)*k)) • z) from
      measurableEmbedding_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ (integerTranslation (-((N : ℤ)*k)))))
    (cuspPartialOrbitalIntegrand N ψ n η R k)
  rw [← h]
  apply integral_congr_ae
  exact Eventually.of_forall (cuspPartialOrbitalIntegrand_translate N ψ n η R k)

end ArtinMatthews
