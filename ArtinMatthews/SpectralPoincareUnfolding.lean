module

public import ArtinMatthews.SpectralPoincareUnfoldingCosets


set_option backward.privateInPublic true
@[expose] public section

/-! Exact compact-seed arithmetic unfolding against actual invariant
continuous functions.  The finite chart sum unfolds over the complete
hyperbolic plane with the genuine central multiplicity two. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups CompactlySupported

namespace ArtinMatthews

theorem gamma0_coset_translate_integral_unfold (N : ℕ) [NeZero N]
    (h : UpperHalfPlane → ℂ) (hc : Continuous h) (hcomp : HasCompactSupport h) :
    (∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd, h ((γ : SL(2, ℤ)) • (q.out⁻¹ • z))) =
      2 * ∫ z, h z := by
  let T : SL(2, ℤ) → ℂ := fun g => ∫ z in ModularGroup.fd, h (g⁻¹ • z)
  let e := gamma0CosetInverseEquiv N
  have ht : Function.HasFiniteSupport T := modular_integral_hasFiniteSupport h hcomp
  have hte : Function.HasFiniteSupport (fun p => T (e p)) :=
    Function.HasFiniteSupport.fun_comp_of_injective (f := T) (g := e) e.injective ht
  calc
    _ = ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∑ᶠ γ : CongruenceSubgroup.Gamma0 N, T (e (q, γ)) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      funext γ
      simp only [T, e, gamma0CosetInverseEquiv_apply, mul_inv_rev, inv_inv, mul_smul]
    _ = ∑ᶠ p, T (e p) := by
      rw [finsum_curry _ hte, finsum_eq_sum_of_fintype]
    _ = ∑ᶠ g : SL(2, ℤ), T g := finsum_comp_equiv e
    _ = _ := modular_integral_finsum_eq_two_integral h hc hcomp

theorem gamma0_single_chart_periodization_integral (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hFinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((γ : SL(2, ℤ)) • z) = F z)
    (ψ : C_c(UpperHalfPlane, ℂ)) (r : SL(2, ℤ)) :
    (∫ z in ModularGroup.fd,
      F (r⁻¹ • z) * gamma0PoincareSeed N ψ (r⁻¹ • z)) =
      ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd,
          F ((γ : SL(2, ℤ)) • (r⁻¹ • z)) * ψ ((γ : SL(2, ℤ)) • (r⁻¹ • z)) := by
  classical
  let h : UpperHalfPlane → ℂ := fun z => F z * ψ z
  have hc : Continuous h := hF.mul ψ.continuous
  have hcomp : HasCompactSupport h := by
    apply ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport h)
    exact tsupport_mul_subset_right
  let hf := gamma0_compact_seed_fd_translates_finite N r ψ.hasCompactSupport
  let s := hf.toFinset
  have hperiod (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
      gamma0PoincareSeed N ψ (r⁻¹ • z) =
        ∑ γ ∈ s, ψ ((γ : SL(2, ℤ)) • (r⁻¹ • z)) := by
    rw [gamma0PoincareSeed_eq_finsum]
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    exact hf.mem_toFinset.mpr ⟨z, hz, subset_tsupport ψ hγ⟩
  have hint (γ : CongruenceSubgroup.Gamma0 N) :
      IntegrableOn (fun z : UpperHalfPlane => h ((γ : SL(2, ℤ)) • (r⁻¹ • z))) ModularGroup.fd := by
    let g := Matrix.SpecialLinearGroup.mapGL ℝ ((γ : SL(2, ℤ)) * r⁻¹)
    have hh : HasCompactSupport (h ∘ Homeomorph.smul g) := hcomp.comp_homeomorph _
    have hi : Integrable (h ∘ Homeomorph.smul g) (volume : Measure UpperHalfPlane) :=
      (hc.comp (continuous_const_smul g)).integrable_of_hasCompactSupport hh
    have hir : Integrable (h ∘ Homeomorph.smul g)
        (volume.restrict ModularGroup.fd) := hi.restrict
    change Integrable (fun z : UpperHalfPlane =>
      h (Matrix.SpecialLinearGroup.mapGL ℝ ((γ : SL(2, ℤ)) * r⁻¹) • z))
        (volume.restrict ModularGroup.fd) at hir
    change Integrable (fun z : UpperHalfPlane => h (((γ : SL(2, ℤ)) * r⁻¹) • z))
      (volume.restrict ModularGroup.fd) at hir
    simpa only [mul_smul, IntegrableOn] using hir
  have hsupp : Function.support (fun γ : CongruenceSubgroup.Gamma0 N =>
      ∫ z in ModularGroup.fd, h ((γ : SL(2, ℤ)) • (r⁻¹ • z))) ⊆ s := by
    intro γ hγ
    by_contra hn
    apply hγ
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    have hp : ψ ((γ : SL(2, ℤ)) • (r⁻¹ • z)) = 0 := by
      by_contra hp
      exact hn (hf.mem_toFinset.mpr ⟨z, hz, subset_tsupport ψ hp⟩)
    exact mul_eq_zero_of_right _ hp
  calc
    _ = ∫ z in ModularGroup.fd,
        ∑ γ ∈ s, h ((γ : SL(2, ℤ)) • (r⁻¹ • z)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
      rw [hperiod z hz, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      change F (r⁻¹ • z) * ψ ((γ : SL(2, ℤ)) • (r⁻¹ • z)) =
        F ((γ : SL(2, ℤ)) • (r⁻¹ • z)) * ψ ((γ : SL(2, ℤ)) • (r⁻¹ • z))
      rw [hFinv γ]
    _ = ∑ γ ∈ s, ∫ z in ModularGroup.fd, h ((γ : SL(2, ℤ)) • (r⁻¹ • z)) :=
      integral_finsetSum s fun γ _ => hint γ
    _ = _ := (finsum_eq_sum_of_support_subset _ hsupp).symm

/-- The exact full-group compact-seed unfolding used for whole-strip tests.
Its multiplicity two is derived from the actual `SL₂` action. -/
theorem gamma0_periodization_unfold_integral (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hFinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((γ : SL(2, ℤ)) • z) = F z)
    (ψ : C_c(UpperHalfPlane, ℂ)) :
    (∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ∫ z in ModularGroup.fd,
        F (q.out⁻¹ • z) * gamma0PoincareSeed N ψ (q.out⁻¹ • z)) =
      2 * ∫ z : UpperHalfPlane, F z * ψ z := by
  let h : UpperHalfPlane → ℂ := fun z => F z * ψ z
  have hc : Continuous h := hF.mul ψ.continuous
  have hcomp : HasCompactSupport h := by
    apply ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport h)
    exact tsupport_mul_subset_right
  calc
    _ = ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
          ∫ z in ModularGroup.fd, h ((γ : SL(2, ℤ)) • (q.out⁻¹ • z)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact gamma0_single_chart_periodization_integral N F hF hFinv ψ q.out
    _ = _ := gamma0_coset_translate_integral_unfold N h hc hcomp

end ArtinMatthews
