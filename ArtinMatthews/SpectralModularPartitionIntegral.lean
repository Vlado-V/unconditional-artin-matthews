module

public import ArtinMatthews.SpectralModularPartitionGamma0
public import ArtinMatthews.SpectralGamma0CompactMass


set_option backward.privateInPublic true
@[expose] public section

/-! Actual integration over the finite open congruence region is exactly the
sum of the inverse-representative modular chart integrals.  Boundary removal
uses the proved hyperbolic null-set theorem, and each change of variables uses
the actual invariant measure. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

private theorem modular_smul_measurableEmbedding (r : SL(2, ℤ)) :
    MeasurableEmbedding (fun z : UpperHalfPlane => r • z) := by
  change MeasurableEmbedding
    (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z)
  exact measurableEmbedding_const_smul _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem gamma0InteriorChart_integrableOn_iff (N : ℕ)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (f : UpperHalfPlane → E) :
    IntegrableOn f (gamma0InteriorChart N q) ↔
      IntegrableOn (fun z : UpperHalfPlane => f (q.out⁻¹ • z)) ModularGroup.fd := by
  simp only [IntegrableOn]
  rw [modular_restrict_fd_eq_fdo]
  have he := ((h2_integer_measurePreserving q.out).restrict_preimage_emb
    (modular_smul_measurableEmbedding q.out) ModularGroup.fdo).integrable_comp_emb
      (modular_smul_measurableEmbedding q.out)
      (g := fun z : UpperHalfPlane => f (q.out⁻¹ • z))
  simpa only [Function.comp_def, inv_smul_smul, IntegrableOn, gamma0InteriorChart] using he

theorem gamma0InteriorChart_integral_eq (N : ℕ)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (f : UpperHalfPlane → E) :
    (∫ z in gamma0InteriorChart N q, f z) =
      ∫ z in ModularGroup.fd, f (q.out⁻¹ • z) := by
  rw [modular_restrict_fd_eq_fdo]
  simpa only [inv_smul_smul, gamma0InteriorChart] using
    (h2_integer_measurePreserving q.out).setIntegral_preimage_emb
      (modular_smul_measurableEmbedding q.out)
      (fun z : UpperHalfPlane => f (q.out⁻¹ • z)) ModularGroup.fdo

/-- Exact finite-chart integration for the genuine open congruence region. -/
theorem gamma0InteriorRegion_integral_eq_sum (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → E)
    (hf : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      IntegrableOn (fun z : UpperHalfPlane => f (q.out⁻¹ • z)) ModularGroup.fd) :
    (∫ z in gamma0InteriorRegion N, f z) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd, f (q.out⁻¹ • z) := by
  change (∫ z in ⋃ q, gamma0InteriorChart N q, f z) = _
  rw [integral_iUnion_fintype (fun q => (gamma0InteriorChart_isOpen N q).measurableSet)
    (gamma0InteriorChart_pairwiseDisjoint N)
    (fun q => (gamma0InteriorChart_integrableOn_iff N q f).mpr (hf q))]
  exact Finset.sum_congr rfl fun q _ => gamma0InteriorChart_integral_eq N q f

end ArtinMatthews
