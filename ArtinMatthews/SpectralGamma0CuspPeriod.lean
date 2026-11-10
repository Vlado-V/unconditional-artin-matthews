module

public import ArtinMatthews.SpectralPoincareGamma0
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.Modular


set_option backward.privateInPublic true
@[expose] public section

/-! An actual common horizontal period for every Γ₀(N) cusp chart.
The unnormalized period N is used for qualitative compactness only; it is
not substituted for normalized cusp widths in a Kuznetsov formula. -/

noncomputable section
open scoped MatrixGroups CompactlySupported

namespace ArtinMatthews

/-- Normality of the principal congruence subgroup supplies a common cusp
translation at every integral scaling matrix. -/
theorem gamma0_conjugate_translation_mem (N : ℕ) (r : SL(2, ℤ)) :
    r⁻¹ * ModularGroup.T ^ (N : ℤ) * r ∈ CongruenceSubgroup.Gamma0 N := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa only [Int.natAbs_natCast] using
      CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have hconj : r⁻¹ * ModularGroup.T ^ (N : ℤ) * r ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma_mem'] at hT ⊢
    simp only [map_mul, map_inv, hT, mul_one, inv_mul_cancel]
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hconj).2.2.1

/-- Every actual invariant section has period N in each integral cusp chart. -/
theorem gamma0_cusp_translation_invariant (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z, F ((γ : SL(2, ℤ)) • z) = F z)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) :
    F (r⁻¹ • (ModularGroup.T ^ (N : ℤ) • z)) = F (r⁻¹ • z) := by
  let γ : CongruenceSubgroup.Gamma0 N :=
    ⟨r⁻¹ * ModularGroup.T ^ (N : ℤ) * r, gamma0_conjugate_translation_mem N r⟩
  have h := hF γ (r⁻¹ • z)
  change F ((r⁻¹ * ModularGroup.T ^ (N : ℤ) * r) • (r⁻¹ • z)) = F (r⁻¹ • z) at h
  rw [mul_smul, mul_smul, smul_inv_smul] at h
  exact h

/-- Literal real-coordinate periodicity of the invariant cusp chart. -/
theorem gamma0_cusp_horizontal_periodic (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z, F ((γ : SL(2, ℤ)) • z) = F z)
    (r : SL(2, ℤ)) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ =>
      F (r⁻¹ • UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))) (N : ℝ) := by
  intro x
  let z : UpperHalfPlane := ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩
  have he : UpperHalfPlane.ofComplex (((x + N : ℝ) : ℂ) + y * Complex.I) =
      ModularGroup.T ^ (N : ℤ) • z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq]
    change (((x + N : ℝ) : ℂ) + y * Complex.I) = (x : ℂ) + y * Complex.I + (N : ℤ)
    push_cast
    ring
  change F (r⁻¹ • UpperHalfPlane.ofComplex (((x + N : ℝ) : ℂ) + y * Complex.I)) = _
  rw [he]
  have hz : UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I) = z :=
    UpperHalfPlane.ofComplex_apply z
  change F (r⁻¹ • (ModularGroup.T ^ (N : ℤ) • z)) =
    F (r⁻¹ • UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))
  rw [hz]
  exact gamma0_cusp_translation_invariant N F hF r z

/-- The constructed compact-seed Γ₀ periodizations satisfy the period law. -/
theorem gamma0PoincareSeed_cusp_periodic (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) (r : SL(2, ℤ)) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ =>
      gamma0PoincareSeed N ψ (r⁻¹ • UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I)))
      (N : ℝ) :=
  gamma0_cusp_horizontal_periodic N _ (gamma0PoincareSeed_invariant N ψ) r hy

end ArtinMatthews
