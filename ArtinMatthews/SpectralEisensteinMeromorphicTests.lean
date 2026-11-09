module

public import ArtinMatthews.SpectralEisensteinLocalMeromorphic
public import ArtinMatthews.SpectralEisensteinCutoffCompactTesting


set_option backward.privateInPublic true
@[expose] public section

/-! The meromorphic full Eisenstein family has actual compact smooth
test pairings and satisfies the weak eigen-equation as a meromorphic germ.
The test normalization is twice the literal upper-half-plane pairing. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0CuspEisensteinMeromorphicTest (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ : h2SmoothCompactSeeds) (s : ℂ) : ℂ :=
  (2:ℂ)*gamma0EisensteinCutoffCompactTest N a ψ s+
    inner ℂ (gamma0SmoothSeedMass N ψ)
      (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s))+
    ∑ j, gamma0EisensteinMatchedCoefficient N a s j *
      ((2:ℂ)*gamma0EisensteinCutoffCompactTest N (gamma0EisensteinCuspClassRepresentative N j) ψ (1-s))

theorem gamma0CuspEisensteinMeromorphicTest_meromorphic (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ψ : h2SmoothCompactSeeds) :
    Meromorphic (gamma0CuspEisensteinMeromorphicTest N a ψ) := by
  intro s
  have h0 := (MeromorphicAt.const (2:ℂ) s).fun_mul
    (gamma0EisensteinCutoffCompactTest_analyticAt N a ψ s).meromorphicAt
  have h1 := spectralMeromorphicAt_comp_clm
    ((innerSL ℂ (gamma0SmoothSeedMass N ψ)).comp (gamma0EnergyInclusion N))
    (gamma0CuspEisensteinMatchedTruncatedEnergy_meromorphic N a s)
  have h2 (j : Gamma0EisensteinCuspClasses N) : MeromorphicAt
      (fun w => (2:ℂ)*gamma0EisensteinCutoffCompactTest N
        (gamma0EisensteinCuspClassRepresentative N j) ψ (1-w)) s := by
    have hC : AnalyticAt ℂ (fun w => gamma0EisensteinCutoffCompactTest N
        (gamma0EisensteinCuspClassRepresentative N j) ψ (1-w)) s :=
      (gamma0EisensteinCutoffCompactTest_analyticAt N (gamma0EisensteinCuspClassRepresentative N j) ψ
        (1-s)).comp (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)
    exact (MeromorphicAt.const (2:ℂ) s).fun_mul hC.meromorphicAt
  exact (h0.fun_add h1).fun_add (MeromorphicAt.fun_sum fun j _ =>
    (gamma0EisensteinMatchedCoefficient_meromorphic N a j s).fun_mul (h2 j))

theorem gamma0EisensteinMatchingActualOutgoing_test (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ : h2SmoothCompactSeeds) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    inner ℂ (gamma0SmoothSeedMass N ψ)
      (gamma0EnergyInclusion N (gamma0EisensteinMatchingActualOutgoing N a s hs))=
      ∑ j, gamma0EisensteinMatchingTrueCoefficient N a s j *
        ((2:ℂ)*gamma0EisensteinCutoffCompactTest N (gamma0EisensteinCuspClassRepresentative N j) ψ (1-s)) := by
  let L := (innerSL ℂ (gamma0SmoothSeedMass N ψ)).comp (gamma0EnergyInclusion N)
  change L (gamma0EisensteinMatchingActualOutgoing N a s hs)=_
  rw [gamma0EisensteinMatchingActualOutgoing,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  let b := gamma0EisensteinCuspClassRepresentative N j
  let hq := gamma0Eisenstein_reflect_realPart hs.1
  change gamma0EisensteinMatchingTrueCoefficient N a s j *
    inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0EnergyInclusion N (gamma0CuspOutgoingCutoffEnergy N b (1-s) hq))=_
  rw [gamma0CuspOutgoingCutoffEnergy_mass]
  exact congrArg (fun x : ℂ => gamma0EisensteinMatchingTrueCoefficient N a s j*x)
    (gamma0Mass_inner_unfold_representative N (gamma0CuspOutgoingCutoffMass N b (1-s) hq)
      (gamma0CuspEisensteinCutoff N b (1-s)) (gamma0CuspOutgoingCutoff_continuous N b (1-s))
      (gamma0CuspEisensteinCutoff_automorphy N b (1-s))
      (gamma0CuspOutgoingCutoffMass_ae N b (1-s) hq) ψ)

theorem gamma0CuspEisensteinMeromorphicTest_eq_offcut (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ψ : h2SmoothCompactSeeds) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CuspEisensteinMeromorphicTest N a ψ s=
      (2:ℂ)*gamma0EisensteinCutoffCompactTest N a ψ s+
        inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0CuspEisensteinContinuedRemainder N a s) := by
  rw [gamma0CuspEisensteinMeromorphicTest,← gamma0EisensteinMatchingActualEnergy_mass N a s hs,
    gamma0EisensteinMatching_offcut_energy N a s hs,map_add,
    inner_add_right (𝕜 := ℂ) (E := Gamma0RegionL2 N),
    gamma0CuspEisensteinMatchedTruncatedEnergy_eq_offcut N a s hs,
    gamma0EisensteinMatchingActualOutgoing_test N a ψ s hs]
  simp only [gamma0EisensteinMatchedCoefficient_eq_offcut N a s hs,add_assoc]

theorem gamma0CuspEisensteinMeromorphicTest_initial (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ : h2SmoothCompactSeeds) (s : ℂ) (hs : 1<s.re) :
    gamma0CuspEisensteinMeromorphicTest N a ψ s=
      (2:ℂ)*∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (gamma0CuspEisenstein N a s z) := by
  rw [gamma0CuspEisensteinMeromorphicTest_eq_offcut N a ψ s (gamma0EisensteinContinuationDomain_initial s hs),
    gamma0CuspEisensteinContinuedRemainder_initial N a s hs,
    gamma0Mass_inner_unfold_representative N (gamma0CuspEisensteinRemainderMass N a s hs)
      (gamma0CuspEisensteinRemainder N a s) (gamma0CuspEisensteinRemainder_continuous N a s hs)
      (gamma0CuspEisensteinRemainder_automorphy N a s) (gamma0CuspEisensteinRemainderMass_ae N a s hs) ψ,
    gamma0EisensteinCutoffCompactTest,← mul_add,
    ← integral_add (h2CompactInner_integrable ψ _ (gamma0CuspOutgoingCutoff_continuous N a s))
      (h2CompactInner_integrable ψ _ (gamma0CuspEisensteinRemainder_continuous N a s hs))]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← inner_add_right]
  change inner ℂ (ψ.val z) (gamma0CuspEisensteinCutoff N a s z+
      (gamma0CuspEisenstein N a s z-gamma0CuspEisensteinCutoff N a s z))=_
  congr 1
  ring

theorem gamma0CuspEisensteinMeromorphicTest_eigen_of_matched_pencil (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ψ : h2SmoothCompactSeeds) (s : ℂ)
    (h : gamma0EnergyResolventPencil N (s*(1-s)) (gamma0CuspEisensteinMatchedTruncatedEnergy N a s)=
      gamma0EnergyMassAdjoint N (gamma0EisensteinMatchedForcing N a s)) :
    gamma0CuspEisensteinMeromorphicTest N a (h2SectionLaplacianSeed ψ) s=
      s*(1-s)*gamma0CuspEisensteinMeromorphicTest N a ψ s := by
  let c := gamma0EisensteinMatchedCoefficient N a s
  let b := gamma0EisensteinCuspClassRepresentative N
  let z := s*(1-s)
  let L := innerSL ℂ (gamma0SmoothSeedMass N ψ)
  have h0 := gamma0EisensteinCutoffCompactTest_forcing N a ψ s
  have h1 := gamma0Energy_test_mass_laplacian_of_pencil N ψ z
    (gamma0CuspEisensteinMatchedTruncatedEnergy N a s) (gamma0EisensteinMatchedForcing N a s) h
  have hF : L (gamma0EisensteinMatchedForcing N a s)=
      -L (gamma0CuspEisensteinCompactForcingMass N a s)-
        ∑ j,c j*L (gamma0CuspEisensteinCompactForcingMass N (b j) (1-s)) := by
    simp only [gamma0EisensteinMatchedForcing,map_sub,map_neg,map_sum,map_smul,smul_eq_mul,c,b]
  have hF' : inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0EisensteinMatchedForcing N a s)=
      -inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0CuspEisensteinCompactForcingMass N a s)-
        ∑ j,c j*inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0CuspEisensteinCompactForcingMass N (b j) (1-s)) :=
    hF
  rw [hF'] at h1
  have h2 : (∑ j,c j*((2:ℂ)*gamma0EisensteinCutoffCompactTest N (b j) (h2SectionLaplacianSeed ψ) (1-s)))-
      z*(∑ j,c j*((2:ℂ)*gamma0EisensteinCutoffCompactTest N (b j) ψ (1-s)))=
      ∑ j,c j*inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0CuspEisensteinCompactForcingMass N (b j) (1-s)) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hj := gamma0EisensteinCutoffCompactTest_forcing N (b j) ψ (1-s)
    rw [gamma0Eisenstein_reflect_parameter] at hj
    change _ - (s*(1-s))*_=_
    linear_combination c j*hj
  unfold gamma0CuspEisensteinMeromorphicTest
  dsimp only [z,c,b] at h1 h2
  linear_combination h0+h1+h2

theorem gamma0CuspEisensteinMeromorphicTest_eventually_eigen (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,
      gamma0CuspEisensteinMeromorphicTest N a (h2SectionLaplacianSeed ψ) w=
        w*(1-w)*gamma0CuspEisensteinMeromorphicTest N a ψ w := by
  filter_upwards [gamma0CuspEisensteinMatchedTruncatedEnergy_eventually_pencil N a s] with w hw
  exact gamma0CuspEisensteinMeromorphicTest_eigen_of_matched_pencil N a ψ w hw

end ArtinMatthews
