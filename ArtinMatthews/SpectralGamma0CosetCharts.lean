module

public import ArtinMatthews.SpectralGamma0EnergyGraph


set_option backward.privateInPublic true
@[expose] public section

/-! Actual coset-chart identification and energy domination for the Γ₀ core. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

/-- Any integral inverse chart has the same invariant values as its chosen
finite coset representative. -/
theorem gamma0_inverse_chart_representative (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z, F ((γ : SL(2, ℤ)) • z) = F z)
    (δ : SL(2, ℤ)) (z : UpperHalfPlane) :
    F (δ⁻¹ • z) = F ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹ • z) := by
  let r : SL(2, ℤ) := (QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out
  have hγ : r⁻¹ * δ ∈ CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.eq.mp (Quotient.out_eq' _)
  have h := hF ⟨r⁻¹ * δ, hγ⟩ (δ⁻¹ • z)
  change F ((r⁻¹ * δ) • (δ⁻¹ • z)) = F (δ⁻¹ • z) at h
  rw [mul_smul, smul_inv_smul] at h
  exact h.symm

/-- The same identification holds for actual derivative energy, because its
invariance was proved from the Möbius derivative. -/
theorem gamma0_inverse_chart_energy_representative (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (δ : SL(2, ℤ)) (z : UpperHalfPlane) :
    h2SectionEnergy (gamma0PoincareSeed N ψ.val) (δ⁻¹ • z) =
      h2SectionEnergy (gamma0PoincareSeed N ψ.val)
        ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹ • z) := by
  let r : SL(2, ℤ) := (QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out
  have hγ : r⁻¹ * δ ∈ CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.eq.mp (Quotient.out_eq' _)
  let γ : CongruenceSubgroup.Gamma0 N := ⟨r⁻¹ * δ, hγ⟩
  have h := h2SectionEnergy_invariant (gamma0PoincareSeed N ψ.val)
    (gamma0SmoothSeed_representative_smooth N ψ)
    (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) (by simp)
    (gamma0PoincareSeed_invariant N ψ.val γ) (δ⁻¹ • z)
  change h2SectionEnergy (gamma0PoincareSeed N ψ.val) ((r⁻¹ * δ) • (δ⁻¹ • z)) = _ at h
  rw [mul_smul, smul_inv_smul] at h
  exact h.symm

/-- Every actual integral cusp chart on the standard region is controlled by
the literal global core energy norm. -/
theorem gamma0Seed_chart_energy_le (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (δ : SL(2, ℤ)) :
    (∫ z in ModularGroup.fd, ‖gamma0PoincareSeed N ψ.val (δ⁻¹ • z)‖ ^ 2 +
      h2SectionEnergy (gamma0PoincareSeed N ψ.val) (δ⁻¹ • z)) ≤
      ‖gamma0EnergyTest N ψ‖ ^ 2 := by
  rw [gamma0EnergyTest_norm_sq]
  have he : (fun z : UpperHalfPlane =>
      ‖gamma0PoincareSeed N ψ.val (δ⁻¹ • z)‖ ^ 2 +
      h2SectionEnergy (gamma0PoincareSeed N ψ.val) (δ⁻¹ • z)) =
    (fun z => ‖gamma0PoincareSeed N ψ.val
      ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹ • z)‖ ^ 2 +
      h2SectionEnergy (gamma0PoincareSeed N ψ.val)
      ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹ • z)) := by
    funext z
    rw [gamma0_inverse_chart_representative N _ (gamma0PoincareSeed_invariant N ψ.val),
      gamma0_inverse_chart_energy_representative]
  rw [he]
  apply Finset.single_le_sum (s := Finset.univ)
    (a := (QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
    (f := fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      ∫ z in ModularGroup.fd, ‖gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖ ^ 2 +
        h2SectionEnergy (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z))
  · intro q _
    exact integral_nonneg (fun z => add_nonneg (sq_nonneg _) (h2SectionEnergy_nonneg _ _))
  · exact Finset.mem_univ _

end ArtinMatthews
