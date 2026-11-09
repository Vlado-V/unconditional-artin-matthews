module

public import ArtinMatthews.SpectralStoneEisensteinPair


set_option backward.privateInPublic true
@[expose] public section

/-! Exact sesquilinearity of the actual continuum pairing on compact
automorphic seeds. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0StoneEisensteinPairIntegrand_add_right (N : ℕ) [NeZero N]
    (ψ ξ ζ : h2SmoothCompactSeeds) (t : ℝ) :
    gamma0StoneEisensteinPairIntegrand N ψ (ξ+ζ) t=
      gamma0StoneEisensteinPairIntegrand N ψ ξ t+gamma0StoneEisensteinPairIntegrand N ψ ζ t := by
  simp only [gamma0StoneEisensteinPairIntegrand,gamma0StoneEisensteinAmplitude,
    gamma0CuspEisensteinMeromorphicTest_add_seed,map_add,mul_add,Finset.sum_add_distrib,add_div]

theorem gamma0StoneEisensteinPairIntegrand_smul_right (N : ℕ) [NeZero N]
    (c : ℂ) (ψ ξ : h2SmoothCompactSeeds) (t : ℝ) :
    gamma0StoneEisensteinPairIntegrand N ψ (c • ξ) t=
      c*gamma0StoneEisensteinPairIntegrand N ψ ξ t := by
  rw [gamma0StoneEisensteinPairIntegrand,gamma0StoneEisensteinPairIntegrand,
    ← mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h : gamma0StoneEisensteinAmplitude N (c • ξ) i t=
      (starRingEnd ℂ) c*gamma0StoneEisensteinAmplitude N ξ i t :=
    gamma0CuspEisensteinMeromorphicTest_smul_seed N (gamma0EisensteinCuspClassRepresentative N i)
      c ξ (eisensteinCriticalPoint t)
  rw [h,map_mul,show (starRingEnd ℂ) ((starRingEnd ℂ) c)=c from star_star c]
  ring

theorem gamma0StoneEisensteinPairIntegrand_conj (N : ℕ) [NeZero N]
    (ψ ξ : h2SmoothCompactSeeds) (t : ℝ) :
    (starRingEnd ℂ) (gamma0StoneEisensteinPairIntegrand N ψ ξ t)=
      gamma0StoneEisensteinPairIntegrand N ξ ψ t := by
  have h (a : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) a)=a := star_star a
  let a (i : Gamma0EisensteinCuspClasses N) := gamma0StoneEisensteinAmplitude N ψ i t
  let b (i : Gamma0EisensteinCuspClasses N) := gamma0StoneEisensteinAmplitude N ξ i t
  let q : ℂ := ((2*Real.pi:ℝ):ℂ)
  change (starRingEnd ℂ) ((∑ i,a i*(starRingEnd ℂ) (b i))/q)=
    (∑ i,b i*(starRingEnd ℂ) (a i))/q
  rw [map_div₀,show (starRingEnd ℂ) q=q from Complex.conj_ofReal _,map_sum]
  apply congrArg (fun z : ℂ => z/q)
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,h,mul_comm]

def gamma0StoneEisensteinPair (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) : ℂ :=
  ∫ t in Ioi 0,gamma0StoneEisensteinPairIntegrand N ψ ξ t

theorem gamma0StoneEisensteinPair_add_right (N : ℕ) [NeZero N] (ψ ξ ζ : h2SmoothCompactSeeds) :
    gamma0StoneEisensteinPair N ψ (ξ+ζ)=gamma0StoneEisensteinPair N ψ ξ+gamma0StoneEisensteinPair N ψ ζ := by
  simp only [gamma0StoneEisensteinPair,gamma0StoneEisensteinPairIntegrand_add_right]
  exact integral_add (gamma0StoneEisensteinPairIntegrand_integrableOn N ψ ξ)
    (gamma0StoneEisensteinPairIntegrand_integrableOn N ψ ζ)

theorem gamma0StoneEisensteinPair_smul_right (N : ℕ) [NeZero N]
    (c : ℂ) (ψ ξ : h2SmoothCompactSeeds) :
    gamma0StoneEisensteinPair N ψ (c • ξ)=c*gamma0StoneEisensteinPair N ψ ξ := by
  simp only [gamma0StoneEisensteinPair,gamma0StoneEisensteinPairIntegrand_smul_right]
  exact integral_const_mul _ _

theorem gamma0StoneEisensteinPair_conj (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    (starRingEnd ℂ) (gamma0StoneEisensteinPair N ψ ξ)=gamma0StoneEisensteinPair N ξ ψ := by
  have h : (∫ t in Ioi 0,(starRingEnd ℂ) (gamma0StoneEisensteinPairIntegrand N ψ ξ t))=
      (starRingEnd ℂ) (∫ t in Ioi 0,gamma0StoneEisensteinPairIntegrand N ψ ξ t) := integral_conj
  simp only [gamma0StoneEisensteinPairIntegrand_conj] at h
  exact h.symm

theorem gamma0StoneEisensteinPair_diagonal (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0StoneEisensteinPair N ψ ψ=((∫ t in Ioi 0,gamma0StoneFrequencyDensity N ψ t):ℝ) := by
  simp only [gamma0StoneEisensteinPair,gamma0StoneEisensteinPairIntegrand_diagonal]
  exact integral_ofReal

end ArtinMatthews
