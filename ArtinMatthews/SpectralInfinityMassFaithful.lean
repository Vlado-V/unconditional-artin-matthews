module

public import ArtinMatthews.SpectralInfinityMassPatch
public import Mathlib.Algebra.Order.Archimedean.Real.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! All positive heights in the actual infinity strip detect the full
modular-chart mass. Integer-period translates provide the countable cover. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0Mass_eq_zero_of_infinity_restrictions_eq_zero (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N)
    (h : ∀ (Y : ℝ) (hY : 0 < Y), gamma0CuspMassRestriction N 1 Y hY f = 0) : f = 0 := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma0 N := by
    simpa only [inv_one, one_mul, mul_one] using gamma0_conjugate_translation_mem N 1
  let γ (k : ℤ) : CongruenceSubgroup.Gamma0 N :=
    ⟨ModularGroup.T ^ ((N : ℤ) * k), by
      rw [zpow_mul]
      exact (CongruenceSubgroup.Gamma0 N).zpow_mem hT k⟩
  let Y (n : {n : ℕ // 0 < n}) : ℝ := (n.val : ℝ)⁻¹
  have hY (n : {n : ℕ // 0 < n}) : 0 < Y n := inv_pos.mpr (Nat.cast_pos.mpr n.property)
  apply PiLp.ext
  intro q
  change f q = 0
  apply Lp.ext
  have hpatch (k : ℤ) (n : {n : ℕ // 0 < n}) :
      ∀ᵐ z ∂volume.restrict ModularGroup.fd,
        (((γ k : SL(2, ℤ)) * q.out⁻¹) • z) ∈ hyperbolicCuspStrip (N : ℝ) (Y n) → f q z = 0 :=
    ae_imp_of_ae_restrict (gamma0InfinityChartPatch_ae_zero N q (γ k) (Y n) (hY n) f (h _ _))
  have hall : ∀ᵐ z ∂volume.restrict ModularGroup.fd, ∀ (k : ℤ) (n : {n : ℕ // 0 < n}),
      (((γ k : SL(2, ℤ)) * q.out⁻¹) • z) ∈ hyperbolicCuspStrip (N : ℝ) (Y n) → f q z = 0 :=
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (hpatch k))
  filter_upwards [hall, Lp.coeFn_zero ℂ 2 (volume.restrict ModularGroup.fd)] with z hz hzero
  let z₀ : UpperHalfPlane := q.out⁻¹ • z
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ioc hN z₀.re 0
  obtain ⟨n, hn, hlt⟩ := Real.exists_nat_pos_inv_lt z₀.im_pos
  have hmem : (((γ k : SL(2, ℤ)) * q.out⁻¹) • z) ∈
      hyperbolicCuspStrip (N : ℝ) (Y ⟨n, hn⟩) := by
    change (ModularGroup.T ^ ((N : ℤ) * k) * q.out⁻¹) • z ∈ _
    rw [mul_smul]
    change (ModularGroup.T ^ ((N : ℤ) * k) • z₀).re ∈ Ioc 0 (N : ℝ) ∧
      Y ⟨n, hn⟩ < (ModularGroup.T ^ ((N : ℤ) * k) • z₀).im
    rw [ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul]
    exact ⟨by simpa only [Int.cast_mul, Int.cast_natCast, zsmul_eq_mul, zero_add, mul_comm] using hk, hlt⟩
  exact (hz k ⟨n, hn⟩ hmem).trans hzero.symm

end ArtinMatthews
