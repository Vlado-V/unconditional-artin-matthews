module

public import ArtinMatthews.SpectralModularPartition
public import ArtinMatthews.SpectralPoincareGamma0


set_option backward.privateInPublic true
@[expose] public section

/-!
Exact single-interior-chart identities for actual arithmetic periodization.
The full group sum contains both central signs; its value on the selected
interior is twice the seed value, and it vanishes on every other coset chart.
-/

noncomputable section
open Set
open scoped CompactlySupported MatrixGroups

namespace ArtinMatthews

/-- Reindex the actual real-matrix periodization by the original integral
congruence subgroup, using the injective arithmetic embedding. -/
theorem gamma0PoincareSeed_eq_finsum (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) (z : UpperHalfPlane) :
    gamma0PoincareSeed N ψ z =
      ∑ᶠ γ : CongruenceSubgroup.Gamma0 N, ψ ((γ : SL(2, ℤ)) • z) := by
  let e := (CongruenceSubgroup.Gamma0 N).equivMapOfInjective
    (Matrix.SpecialLinearGroup.mapGL ℝ) (Matrix.SpecialLinearGroup.mapGL_injective (S := ℝ))
  exact (finsum_comp_equiv
    (f := fun g : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) => ψ (g • z))
    e.toEquiv).symm

/-- A seed supported inside one inverse interior chart has zero periodization
on every distinct actual `Γ₀(N)` chart. -/
theorem gamma0PoincareSeed_eq_zero_of_interior_chart_ne
    (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane, ℂ)) (r s : SL(2, ℤ))
    (hψ : tsupport ψ ⊆ (fun z : UpperHalfPlane => r • z) ⁻¹' ModularGroup.fdo)
    (hrs : (r : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) ≠ s)
    {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fdo) :
    gamma0PoincareSeed N ψ (s⁻¹ • z) = 0 := by
  by_contra hn
  obtain ⟨γ, hγ⟩ := gamma0PoincareSeed_support N ψ hn
  have heq := gamma0_interior_overlap_quotient_eq N γ.property
    (show s • (s⁻¹ • z) ∈ ModularGroup.fdo by simpa only [smul_inv_smul] using hz)
    (hψ hγ)
  exact hrs heq.symm

/-- On the selected interior chart only the two central signs can contribute
to the full arithmetic periodization. -/
theorem gamma0PoincareSeed_eq_two_mul_on_interior_chart
    (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane, ℂ)) (r : SL(2, ℤ))
    (hψ : tsupport ψ ⊆ (fun z : UpperHalfPlane => r • z) ⁻¹' ModularGroup.fdo)
    {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fdo) :
    gamma0PoincareSeed N ψ (r⁻¹ • z) = 2 * ψ (r⁻¹ • z) := by
  classical
  let negOne : CongruenceSubgroup.Gamma0 N := ⟨-1, gamma0_neg_one_mem N⟩
  have hne : (1 : CongruenceSubgroup.Gamma0 N) ≠ negOne := by
    intro he
    have he' := congrArg (fun g : CongruenceSubgroup.Gamma0 N => (g : SL(2, ℤ)) 0 0) he
    norm_num [negOne] at he'
  rw [gamma0PoincareSeed_eq_finsum]
  have hsupp : Function.support
      (fun γ : CongruenceSubgroup.Gamma0 N => ψ ((γ : SL(2, ℤ)) • (r⁻¹ • z))) ⊆
        ({1, negOne} : Finset (CongruenceSubgroup.Gamma0 N)) := by
    intro γ hγ
    have hmem := hψ (subset_tsupport ψ hγ)
    change r • ((γ : SL(2, ℤ)) • (r⁻¹ • z)) ∈ ModularGroup.fdo at hmem
    have hcentral : (r * (γ : SL(2, ℤ))) * r⁻¹ = 1 ∨
        (r * (γ : SL(2, ℤ))) * r⁻¹ = -1 :=
      ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz (by
        simpa only [mul_smul] using hmem)
    have hsign : (γ : SL(2, ℤ)) = 1 ∨ (γ : SL(2, ℤ)) = -1 := by
      rcases hcentral with h | h
      · left
        have he := congrArg (fun u : SL(2, ℤ) => r⁻¹ * u * r) h
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
          inv_mul_cancel, one_mul, mul_one] using he
      · right
        have he := congrArg (fun u : SL(2, ℤ) => r⁻¹ * u * r) h
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
          mul_neg, neg_mul, inv_mul_cancel, one_mul, mul_one] using he
    rcases hsign with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h)))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_pair hne]
  have hact : (negOne : SL(2, ℤ)) • (r⁻¹ • z) = r⁻¹ • z := by
    change (-(1 : SL(2, ℤ))) • (r⁻¹ • z) = r⁻¹ • z
    rw [ModularGroup.SL_neg_smul, one_smul]
  change ψ ((1 : SL(2, ℤ)) • (r⁻¹ • z)) + ψ ((negOne : SL(2, ℤ)) • (r⁻¹ • z)) = _
  rw [one_smul, hact, two_mul]

end ArtinMatthews
