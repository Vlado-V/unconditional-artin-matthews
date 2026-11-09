module

public import ArtinMatthews.SpectralPoincareUnfoldingModular


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reindexing from congruence cosets and subgroup translates to the
integral modular group, for the genuine compact-support unfolding. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups Pointwise

namespace ArtinMatthews

private theorem gamma0_coset_inverse_product_bijective (N : ℕ) :
    Function.Bijective (fun p :
      (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) × CongruenceSubgroup.Gamma0 N =>
        p.1.out * (p.2 : SL(2, ℤ))⁻¹) := by
  have hclass (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
      (γ : CongruenceSubgroup.Gamma0 N) :
      (QuotientGroup.mk (q.out * (γ : SL(2, ℤ))⁻¹) :
        SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = q :=
    (QuotientGroup.mk_mul_of_mem q.out ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property)).trans
      (Quotient.out_eq' q)
  constructor
  · rintro ⟨q, γ⟩ ⟨t, η⟩ h
    have hqt : q = t := (hclass q γ).symm.trans
      ((congrArg (QuotientGroup.mk (s := CongruenceSubgroup.Gamma0 N)) h).trans (hclass t η))
    subst t
    have hγη : γ = η := by
      apply Subtype.ext
      exact inv_injective (mul_left_cancel h)
    exact congrArg (fun a : CongruenceSubgroup.Gamma0 N => (q, a)) hγη
  · intro δ
    let q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N := δ
    have hγ : q.out⁻¹ * δ ∈ CongruenceSubgroup.Gamma0 N :=
      QuotientGroup.eq.mp (Quotient.out_eq' q)
    refine ⟨⟨q, ⟨(q.out⁻¹ * δ)⁻¹, (CongruenceSubgroup.Gamma0 N).inv_mem hγ⟩⟩, ?_⟩
    simp only [inv_inv, mul_inv_cancel_left]

def gamma0CosetInverseEquiv (N : ℕ) :
    ((SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) × CongruenceSubgroup.Gamma0 N) ≃ SL(2, ℤ) :=
  Equiv.ofBijective _ (gamma0_coset_inverse_product_bijective N)

theorem gamma0CosetInverseEquiv_apply (N : ℕ)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (γ : CongruenceSubgroup.Gamma0 N) :
    gamma0CosetInverseEquiv N (q, γ) = q.out * (γ : SL(2, ℤ))⁻¹ := rfl

theorem modular_integral_hasFiniteSupport (F : UpperHalfPlane → ℂ) (hFc : HasCompactSupport F) :
    Function.HasFiniteSupport (fun g : SL(2, ℤ) => ∫ z in ModularGroup.fd, F (g⁻¹ • z)) := by
  apply (compact_modular_translates_meeting_fd_finite hFc).subset
  intro g hg
  by_contra hnot
  apply hg
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  by_contra hn
  exact hnot ⟨z, ⟨g⁻¹ • z, subset_tsupport F hn, smul_inv_smul g z⟩, hz⟩

end ArtinMatthews
