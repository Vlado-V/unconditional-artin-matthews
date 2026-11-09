module

public import ArtinMatthews.SpectralCuspEisensteinRowKernel
public import ArtinMatthews.SpectralCuspScatteringSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite residue counts emerge from the absolutely convergent
positive-row integral; no constant-term formula is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinPositiveIntegral_summable (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : CuspEisensteinPositiveRows N r a =>
      cuspEisensteinRowIntegral N r a s y hy v.val) :=
  (cuspEisensteinRowIntegral_summable N r a s hs y hy).comp_injective
    (i := fun v : CuspEisensteinPositiveRows N r a => v.val) Subtype.coe_injective

theorem cuspEisensteinCoordinateIntegral_summable (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : CuspEisensteinPositiveCoordinates N r a =>
      cuspEisensteinCoordinateIntegral N r a s y hy v.1 v.2) :=
  (cuspEisensteinPositiveCoordinateEquiv N r a).summable_iff.mpr
    (cuspEisensteinPositiveIntegral_summable N r a s hs y hy)

theorem cuspEisensteinCoordinateIntegral_fibre (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (c : {c : ℕ // 0 < c})
    (hD : Summable (cuspEisensteinCoordinateIntegral N r a s y hy c)) :
    (∑' d, cuspEisensteinCoordinateIntegral N r a s y hy c d)=
      (gamma0CuspScatteringCount N r a c.val:ℂ)*(gamma0CuspTrueWidth N r:ℂ)^(-s)*
        (c.val:ℂ)^(-2*s)*(y:ℂ)^(1-s)*
          ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by
  let e := cuspEisensteinResidueTranslateEquiv N r a c.val c.property
  have hR : Summable (fun v : CuspEisensteinRowResidues N r a c.val × ℤ =>
      cuspEisensteinCoordinateIntegral N r a s y hy c (e v)) := e.summable_iff.mpr hD
  have hprod := Summable.tsum_prod
    (f := fun v : CuspEisensteinRowResidues N r a c.val × ℤ =>
      cuspEisensteinCoordinateIntegral N r a s y hy c (e v)) hR
  rw [← e.tsum_eq (cuspEisensteinCoordinateIntegral N r a s y hy c),hprod]
  simp_rw [show ∀ b : CuspEisensteinRowResidues N r a c.val,
      (∑' k : ℤ, cuspEisensteinCoordinateIntegral N r a s y hy c (e (b,k)))=
        (gamma0CuspTrueWidth N r:ℂ)^(-s)*(c.val:ℂ)^(-2*s)*(y:ℂ)^(1-s)*
          ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) from
    fun b => cuspEisensteinCoordinateIntegral_orbit N r a s hs y hy c b]
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (gamma0CuspScatteringCount N r a c.val:ℂ)*_= _
  ring

theorem cuspEisensteinPositiveIntegral_dirichlet (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∑' v : CuspEisensteinPositiveRows N r a, cuspEisensteinRowIntegral N r a s y hy v.val)=
      (gamma0CuspTrueWidth N r:ℂ)^(-s)*(y:ℂ)^(1-s)*
        ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
          gamma0CuspScatteringDirichlet N r a s := by
  let f : CuspEisensteinPositiveRows N r a → ℂ := fun v =>
    cuspEisensteinRowIntegral N r a s y hy v.val
  let e := cuspEisensteinPositiveCoordinateEquiv N r a
  have hsum := cuspEisensteinCoordinateIntegral_summable N r a s hs y hy
  have hsigma := Summable.tsum_sigma
    (f := fun v : CuspEisensteinPositiveCoordinates N r a =>
      cuspEisensteinCoordinateIntegral N r a s y hy v.1 v.2) hsum
  change (∑' v, f v)=_
  rw [← e.tsum_eq f]
  change (∑' v : CuspEisensteinPositiveCoordinates N r a,
    cuspEisensteinCoordinateIntegral N r a s y hy v.1 v.2)=_
  rw [hsigma]
  have hinner (c : {c : ℕ // 0 < c}) :
      (∑' d, cuspEisensteinCoordinateIntegral N r a s y hy c d)=
        ((gamma0CuspScatteringCount N r a c.val:ℂ)*(c.val:ℂ)^(-2*s))*
          ((gamma0CuspTrueWidth N r:ℂ)^(-s)*(y:ℂ)^(1-s)*
            ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)) := by
    rw [cuspEisensteinCoordinateIntegral_fibre N r a s hs y hy c (hsum.sigma_factor c)]
    ring
  simp_rw [hinner]
  rw [tsum_mul_right]
  change gamma0CuspScatteringDirichlet N r a s*_= _
  ring

end ArtinMatthews
