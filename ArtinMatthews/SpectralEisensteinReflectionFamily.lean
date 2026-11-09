module

public import ArtinMatthews.SpectralEisensteinReflectionEnergy
public import ArtinMatthews.SpectralEisensteinMeromorphicTests


set_option backward.privateInPublic true
@[expose] public section

/-! The functional equation acts on the actual compact chart L²
continuation and its actual compact smooth test pairings. -/
noncomputable section
open Set Filter Topology MeasureTheory Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem spectralReflectedEisensteinValue {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid V] [Module ℂ V] (M P : Matrix ι ι ℂ) (hMP : M*P=1)
    (j : ι) (c d u v : ι → V) (hv : v j=∑ i,P i j • u i) :
    d j+v j+(∑ i,P i j • c i)=
      ∑ i,P i j • (c i+u i+(∑ k,M k i • d k)) := by
  rw [spectralReflectedProfileSum M P hMP j (fun i => c i+u i) d,
    hv]
  simp only [smul_add,Finset.sum_add_distrib]
  ac_rfl

theorem gamma0CuspEisensteinMeromorphicCompactMass_reflection_regular (N : ℕ) [NeZero N]
    (j : Gamma0EisensteinCuspClasses N) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hsub : K⊆ModularGroup.fd)
    (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) (hq : gamma0EisensteinMatchingRegular N (1-s)) :
    gamma0CuspEisensteinMeromorphicCompactMass N (gamma0EisensteinCuspClassRepresentative N j) i K hK hsub (1-s)=
      ∑ k,gamma0CuspScatteringMatrix N (1-s) k j •
        gamma0CuspEisensteinMeromorphicCompactMass N (gamma0EisensteinCuspClassRepresentative N k) i K hK hsub s := by
  let r := gamma0EisensteinCuspClassRepresentative N
  let C (w : ℂ) (k : Gamma0EisensteinCuspClasses N) :=
    gamma0CuspEisensteinCutoffCompactMass N (r k) i.out K hK w
  let L := (gamma0EisensteinCompactChartRestriction N i K hsub).comp (gamma0EnergyInclusion N)
  let U (w : ℂ) (k : Gamma0EisensteinCuspClasses N) := gamma0CuspEisensteinMatchedTruncatedEnergy N (r k) w
  let M := gamma0CuspScatteringMatrix N s
  let P := gamma0CuspScatteringMatrix N (1-s)
  change C (1-s) j+L (U (1-s) j)+(∑ k,P k j • C (1-(1-s)) k)=
    ∑ k,P k j • (C s k+L (U s k)+(∑ l,M l k • C (1-s) l))
  rw [show (1:ℂ)-(1-s)=s from eisensteinParameterReflect_involutive s]
  have hL : L (U (1-s) j)=∑ k,P k j • L (U s k) := by
    have hu : U (1-s) j=∑ k,P k j • U s k :=
      gamma0CuspEisensteinMatchedTruncatedEnergy_reflection_regular N s hs hq j
    rw [hu,map_sum]
    simp only [map_smul]
  exact spectralReflectedEisensteinValue M P (gamma0CuspScatteringMatrix_reflection_regular N s hs hq)
    j (C s) (C (1-s)) (fun k => L (U s k)) (fun k => L (U (1-s) k)) hL

theorem gamma0CuspEisensteinMeromorphicCompactMass_reflection_germ (N : ℕ) [NeZero N]
    (j : Gamma0EisensteinCuspClasses N) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hsub : K⊆ModularGroup.fd) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,
      gamma0CuspEisensteinMeromorphicCompactMass N (gamma0EisensteinCuspClassRepresentative N j) i K hK hsub (1-w)=
        ∑ k,gamma0CuspScatteringCanonical N (1-w) k j •
          gamma0CuspEisensteinMeromorphicCompactMass N (gamma0EisensteinCuspClassRepresentative N k) i K hK hsub w := by
  filter_upwards [gamma0EisensteinMatchingRegular_reflected_eventually N s] with w hw
  rw [gamma0CuspScatteringCanonical_eq_regular N (1-w) hw.2]
  exact gamma0CuspEisensteinMeromorphicCompactMass_reflection_regular N j i K hK hsub w hw.1 hw.2

theorem gamma0CuspEisensteinMeromorphicTest_reflection_regular (N : ℕ) [NeZero N]
    (j : Gamma0EisensteinCuspClasses N) (ψ : h2SmoothCompactSeeds)
    (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) (hq : gamma0EisensteinMatchingRegular N (1-s)) :
    gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ (1-s)=
      ∑ k,gamma0CuspScatteringMatrix N (1-s) k j *
        gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N k) ψ s := by
  let r := gamma0EisensteinCuspClassRepresentative N
  let C (w : ℂ) (k : Gamma0EisensteinCuspClasses N) :=
    (2:ℂ)*gamma0EisensteinCutoffCompactTest N (r k) ψ w
  let L := (innerSL ℂ (gamma0SmoothSeedMass N ψ)).comp (gamma0EnergyInclusion N)
  let U (w : ℂ) (k : Gamma0EisensteinCuspClasses N) := gamma0CuspEisensteinMatchedTruncatedEnergy N (r k) w
  let M := gamma0CuspScatteringMatrix N s
  let P := gamma0CuspScatteringMatrix N (1-s)
  change C (1-s) j+L (U (1-s) j)+(∑ k,P k j • C (1-(1-s)) k)=
    ∑ k,P k j • (C s k+L (U s k)+(∑ l,M l k • C (1-s) l))
  rw [show (1:ℂ)-(1-s)=s from eisensteinParameterReflect_involutive s]
  have hL : L (U (1-s) j)=∑ k,P k j • L (U s k) := by
    have hu : U (1-s) j=∑ k,P k j • U s k :=
      gamma0CuspEisensteinMatchedTruncatedEnergy_reflection_regular N s hs hq j
    rw [hu,map_sum]
    simp only [map_smul]
  exact spectralReflectedEisensteinValue M P (gamma0CuspScatteringMatrix_reflection_regular N s hs hq)
    j (C s) (C (1-s)) (fun k => L (U s k)) (fun k => L (U (1-s) k)) hL

theorem gamma0CuspEisensteinMeromorphicTest_reflection_germ (N : ℕ) [NeZero N]
    (j : Gamma0EisensteinCuspClasses N) (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,
      gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ (1-w)=
        ∑ k,gamma0CuspScatteringCanonical N (1-w) k j *
          gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N k) ψ w := by
  filter_upwards [gamma0EisensteinMatchingRegular_reflected_eventually N s] with w hw
  rw [gamma0CuspScatteringCanonical_eq_regular N (1-w) hw.2]
  exact gamma0CuspEisensteinMeromorphicTest_reflection_regular N j ψ w hw.1 hw.2

end ArtinMatthews
