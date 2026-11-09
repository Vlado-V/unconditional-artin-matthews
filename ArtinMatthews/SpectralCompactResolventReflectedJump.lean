module

public import ArtinMatthews.SpectralCompactResolventHeightScattering


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual reflected compact-forcing resolvents differ by the
actual Eisenstein family with their reflected outgoing coefficients. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem spectralMatchedJump_sum {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (M : Matrix ι ι ℂ) (a b : ι → ℂ) (hab : a= -(M.mulVec b)) (u v : ι → V) :
    (∑ i,a i • v i)-(∑ i,b i • u i)= -(∑ i,b i • (u i+∑ j,M j i • v j)) := by
  rw [hab]
  simp only [Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,smul_add,Finset.sum_add_distrib,
    spectralSum_smul_matrix_mulVec M b v]
  abel

theorem gamma0CompactForcingMatchedEnergy_reflected_jump (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s)
    (hYs : gamma0HeightMatchingRegular N A.height A.pos s)
    (hYq : gamma0HeightMatchingRegular N A.height A.pos (1-s)) :
    gamma0CompactForcingMatchedEnergy N ψ A s-gamma0CompactForcingMatchedEnergy N ψ A (1-s)=
      -(∑ i,gamma0CompactForcingMatchedCoefficient N ψ A (1-s) i •
        gamma0CuspEisensteinMatchedTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N i) s) := by
  let R := gamma0HeightMatchingResponse N A.height A.pos s
  let F := gamma0SmoothSeedMass N ψ
  let M := gamma0CuspScatteringMatrix N s
  let a := gamma0CompactForcingMatchedCoefficient N ψ A s
  let b := gamma0CompactForcingMatchedCoefficient N ψ A (1-s)
  let u (i : Gamma0EisensteinCuspClasses N) := -R (gamma0CuspChannelForcing N s i)
  let v (i : Gamma0EisensteinCuspClasses N) := -R (gamma0CuspChannelForcing N (1-s) i)
  have hE (i : Gamma0EisensteinCuspClasses N) :
      gamma0CuspEisensteinMatchedTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N i) s =
        u i+∑ j,M j i • v j := by
    rw [gamma0CuspEisensteinMatchedTruncatedEnergy_eq_atHeight_response N A.height A.pos A.matching_le _ s hs hYs]
    change R (-gamma0CuspChannelForcing N s i-∑ j,M j i • gamma0CuspChannelForcing N (1-s) j)=_
    rw [map_sub,map_neg,map_sum]
    simp only [u,v,map_smul,smul_neg,Finset.sum_neg_distrib,sub_eq_add_neg]
  rw [gamma0CompactForcingMatchedEnergy_expand N ψ A s,
    gamma0CompactForcingMatchedEnergy_expand N ψ A (1-s),
    gamma0HeightMatchingResponse_reflect,show (1:ℂ)-(1-s)=s from eisensteinParameterReflect_involutive s]
  simp_rw [hE]
  have hj := spectralMatchedJump_sum M a b
    (gamma0CompactForcingMatchedCoefficient_reflection_regular N ψ A s hs hYs hYq) u v
  calc
    (R F-∑ i,a i • R (gamma0CuspChannelForcing N (1-s) i))-
        (R F-∑ i,b i • R (gamma0CuspChannelForcing N s i)) =
        (∑ i,a i • v i)-(∑ i,b i • u i) := by
      simp only [u,v,smul_neg,Finset.sum_neg_distrib]
      abel
    _ = _ := hj

theorem gamma0CompactForcingMatchedTest_reflected_jump (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s)
    (hYs : gamma0HeightMatchingRegular N A.height A.pos s)
    (hYq : gamma0HeightMatchingRegular N A.height A.pos (1-s)) :
    gamma0CompactForcingMatchedTest N ψ φ A s-gamma0CompactForcingMatchedTest N ψ φ A (1-s)=
      -(∑ i,gamma0CompactForcingMatchedCoefficient N ψ A (1-s) i *
        gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) φ s) := by
  let L := (innerSL ℂ (gamma0SmoothSeedMass N φ)).comp (gamma0EnergyInclusion N)
  let a := gamma0CompactForcingMatchedCoefficient N ψ A s
  let b := gamma0CompactForcingMatchedCoefficient N ψ A (1-s)
  let M := gamma0CuspScatteringMatrix N s
  let R := gamma0CompactForcingMatchedEnergy N ψ A
  let E (i : Gamma0EisensteinCuspClasses N) :=
    gamma0CuspEisensteinMatchedTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N i) s
  let u (i : Gamma0EisensteinCuspClasses N) := (2:ℂ)*gamma0EisensteinCutoffCompactTest N
    (gamma0EisensteinCuspClassRepresentative N i) φ s
  let v (i : Gamma0EisensteinCuspClasses N) := (2:ℂ)*gamma0EisensteinCutoffCompactTest N
    (gamma0EisensteinCuspClassRepresentative N i) φ (1-s)
  have hE : R s-R (1-s)= -(∑ i,b i • E i) :=
    gamma0CompactForcingMatchedEnergy_reflected_jump N ψ A s hs hYs hYq
  have hR : L (R s)-L (R (1-s))= -(∑ i,b i • L (E i)) := by
    rw [← map_sub,hE,map_neg,map_sum]
    simp only [map_smul]
  have hv := spectralMatchedJump_sum M a b
    (gamma0CompactForcingMatchedCoefficient_reflection_regular N ψ A s hs hYs hYq) u v
  unfold gamma0CompactForcingMatchedTest gamma0CuspEisensteinMeromorphicTest
  rw [show (1:ℂ)-(1-s)=s from eisensteinParameterReflect_involutive s]
  change (L (R s)+(∑ i,a i • v i))-(L (R (1-s))+(∑ i,b i • u i))=
    -(∑ i,b i • (u i+L (E i)+∑ j,M j i • v j))
  calc
    _ = (L (R s)-L (R (1-s)))+((∑ i,a i • v i)-(∑ i,b i • u i)) := by abel
    _ = _ := by
      rw [hR,hv]
      simp only [smul_add,Finset.sum_add_distrib]
      abel

end ArtinMatthews
