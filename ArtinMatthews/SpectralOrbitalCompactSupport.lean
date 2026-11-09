module

public import ArtinMatthews.SpectralFiniteFunctionIntegrals


set_option backward.privateInPublic true
@[expose] public section

/-! The two translation parameters have finite support as entire compact-test
integrands, not just after integration and not merely at each point. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace Pointwise

namespace ArtinMatthews

theorem compactPoincareIntegrand_hasFiniteSupport (ψ φ : h2SmoothCompactSeeds) :
    Function.HasFiniteSupport (fun M : SL(2, ℤ) =>
      fun z : UpperHalfPlane => inner ℂ (ψ.val z) (φ.val (M • z))) := by
  apply (integer_compact_translates_finite ψ.val.hasCompactSupport φ.val.hasCompactSupport).subset
  intro M hM
  by_contra hnot
  apply hM
  funext z
  by_cases hψ : ψ.val z = 0
  · simp only [hψ,inner_zero_left,Pi.zero_apply]
  have hφ : φ.val (M • z) = 0 := by
    by_contra hφ
    exact hnot ⟨M • z,⟨⟨z,subset_tsupport _ hψ,rfl⟩,subset_tsupport _ hφ⟩⟩
  simp only [hφ,inner_zero_right,Pi.zero_apply]

def cuspOrbitalMatrix (N : ℕ) (R : SL(2, ℤ)) (p : ℤ × ℤ) : SL(2, ℤ) :=
  integerTranslation ((N : ℤ) * p.2) * R * integerTranslation ((N : ℤ) * p.1)

theorem cuspOrbitalMatrix_injective (N : ℕ) [NeZero N] (R : SL(2, ℤ))
    (hR : R 1 0 ≠ 0) : Function.Injective (cuspOrbitalMatrix N R) := by
  rintro ⟨k,l⟩ ⟨a,b⟩ h
  have hA := congrArg (fun M : SL(2, ℤ) => M 0 0) h
  have hD := congrArg (fun M : SL(2, ℤ) => M 1 1) h
  change (integerTranslation ((N : ℤ) * l) * R * integerTranslation ((N : ℤ) * k)) 0 0 =
    (integerTranslation ((N : ℤ) * b) * R * integerTranslation ((N : ℤ) * a)) 0 0 at hA
  change (integerTranslation ((N : ℤ) * l) * R * integerTranslation ((N : ℤ) * k)) 1 1 =
    (integerTranslation ((N : ℤ) * b) * R * integerTranslation ((N : ℤ) * a)) 1 1 at hD
  rw [(integerTranslation_entries _ _ _).1,(integerTranslation_entries _ _ _).1] at hA
  rw [(integerTranslation_entries _ _ _).2.2,(integerTranslation_entries _ _ _).2.2] at hD
  have hNc : (N : ℤ) * R 1 0 ≠ 0 := mul_ne_zero (by exact_mod_cast NeZero.ne N) hR
  apply Prod.ext
  · apply mul_left_cancel₀ hNc
    nlinarith [hD]
  · apply mul_left_cancel₀ hNc
    nlinarith [hA]

def cuspOrbitalIntegrand (N : ℕ) (ψ φ : h2SmoothCompactSeeds) (R : SL(2, ℤ))
    (p : ℤ × ℤ) (z : UpperHalfPlane) : ℂ :=
  inner ℂ (ψ.val z) (φ.val (cuspOrbitalMatrix N R p • z))

theorem cuspOrbitalIntegrand_hasFiniteSupport (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (R : SL(2, ℤ)) (hR : R 1 0 ≠ 0) :
    Function.HasFiniteSupport (cuspOrbitalIntegrand N ψ φ R) :=
  Function.HasFiniteSupport.fun_comp_of_injective
    (f := fun M : SL(2, ℤ) => fun z : UpperHalfPlane => inner ℂ (ψ.val z) (φ.val (M • z)))
    (g := cuspOrbitalMatrix N R)
    (cuspOrbitalMatrix_injective N R hR) (compactPoincareIntegrand_hasFiniteSupport ψ φ)

theorem cuspOrbitalIntegrand_integrable (N : ℕ) (ψ φ : h2SmoothCompactSeeds)
    (R : SL(2, ℤ)) (p : ℤ × ℤ) : Integrable (cuspOrbitalIntegrand N ψ φ R p) :=
  compactPoincareGeometricKernel_integrable ψ φ _

end ArtinMatthews
