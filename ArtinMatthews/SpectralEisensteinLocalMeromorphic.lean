module

public import ArtinMatthews.SpectralEisensteinMatchedTruncated
public import ArtinMatthews.SpectralEisensteinCompactRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source Eisenstein family continues meromorphically in L² on
every compact part of every native modular chart. The identification on
Re(s)>1 is with the literal convergent series, almost everywhere. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspEisensteinMeromorphicCompactMass (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (K : Set UpperHalfPlane)
    (hK : IsCompact K) (hsub : K⊆ModularGroup.fd) (s : ℂ) : Lp ℂ 2 (volume.restrict K) :=
  gamma0CuspEisensteinCutoffCompactMass N a i.out K hK s+
    gamma0EisensteinCompactChartRestriction N i K hsub
      (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s))+
    ∑ j, gamma0EisensteinMatchedCoefficient N a s j •
      gamma0CuspEisensteinCutoffCompactMass N (gamma0EisensteinCuspClassRepresentative N j)
        i.out K hK (1-s)

theorem gamma0CuspEisensteinMeromorphicCompactMass_meromorphic (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hsub : K⊆ModularGroup.fd) :
    Meromorphic (gamma0CuspEisensteinMeromorphicCompactMass N a i K hK hsub) := by
  intro s
  have h0 := (gamma0CuspEisensteinCutoffCompactMass_analyticAt N a i.out K hK s).meromorphicAt
  have h1 := spectralMeromorphicAt_comp_clm
    ((gamma0EisensteinCompactChartRestriction N i K hsub).comp (gamma0EnergyInclusion N))
    (gamma0CuspEisensteinMatchedTruncatedEnergy_meromorphic N a s)
  exact (h0.fun_add h1).fun_add (MeromorphicAt.fun_sum fun j _ =>
    (gamma0EisensteinMatchedCoefficient_meromorphic N a j s).fun_smul
      (((gamma0CuspEisensteinCutoffCompactMass_analyticAt N (gamma0EisensteinCuspClassRepresentative N j)
        i.out K hK (1-s)).comp (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)).meromorphicAt))

theorem gamma0EisensteinMatchingActualOutgoing_compact_restriction (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hsub : K⊆ModularGroup.fd)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EisensteinCompactChartRestriction N i K hsub
      (gamma0EnergyInclusion N (gamma0EisensteinMatchingActualOutgoing N a s hs))=
      ∑ j, gamma0EisensteinMatchingTrueCoefficient N a s j •
        gamma0CuspEisensteinCutoffCompactMass N (gamma0EisensteinCuspClassRepresentative N j) i.out K hK (1-s) := by
  simp only [gamma0EisensteinMatchingActualOutgoing,map_sum,map_smul,gamma0CuspOutgoingCutoffEnergy_mass]
  apply Finset.sum_congr rfl
  intro j _
  rw [gamma0CuspOutgoingCutoffMass_compact_restriction N _ _ _ i K hK hsub]

theorem gamma0CuspEisensteinMeromorphicCompactMass_eq_offcut (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hsub : K⊆ModularGroup.fd)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CuspEisensteinMeromorphicCompactMass N a i K hK hsub s=
      gamma0CuspEisensteinCutoffCompactMass N a i.out K hK s+
        gamma0EisensteinCompactChartRestriction N i K hsub (gamma0CuspEisensteinContinuedRemainder N a s) := by
  rw [gamma0CuspEisensteinMeromorphicCompactMass,← gamma0EisensteinMatchingActualEnergy_mass N a s hs,
    gamma0EisensteinMatching_offcut_energy N a s hs,map_add,map_add,
    gamma0CuspEisensteinMatchedTruncatedEnergy_eq_offcut N a s hs,
    gamma0EisensteinMatchingActualOutgoing_compact_restriction N a i K hK hsub s hs]
  simp only [gamma0EisensteinMatchedCoefficient_eq_offcut N a s hs,add_assoc]

theorem gamma0CuspEisensteinMeromorphicCompactMass_initial_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hsub : K⊆ModularGroup.fd)
    (s : ℂ) (hs : 1<s.re) :
    gamma0CuspEisensteinMeromorphicCompactMass N a i K hK hsub s =ᵐ[volume.restrict K]
      fun z => gamma0CuspEisenstein N a s (i.out⁻¹ • z) := by
  rw [gamma0CuspEisensteinMeromorphicCompactMass_eq_offcut N a i K hK hsub s
    (gamma0EisensteinContinuationDomain_initial s hs)]
  have he := (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set _ hsub)).ae_eq
    (gamma0CuspEisensteinContinuedRemainder_series_ae N a s hs i)
  filter_upwards [Lp.coeFn_add (gamma0CuspEisensteinCutoffCompactMass N a i.out K hK s)
    (gamma0EisensteinCompactChartRestriction N i K hsub (gamma0CuspEisensteinContinuedRemainder N a s)),
    gamma0CuspEisensteinCutoffCompactMass_ae N a i.out K hK s,
    gamma0EisensteinCompactChartRestriction_ae N i K hsub (gamma0CuspEisensteinContinuedRemainder N a s),
    he] with z hsum hC hR hz
  rw [hsum,Pi.add_apply,hC,hR,hz]

end ArtinMatthews
