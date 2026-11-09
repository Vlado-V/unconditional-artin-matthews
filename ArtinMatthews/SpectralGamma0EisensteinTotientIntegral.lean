module

public import ArtinMatthews.SpectralGamma0EisensteinPositiveIntegral
public import ArtinMatthews.SpectralGamma0EisensteinPositiveCoordinates
public import ArtinMatthews.SpectralEisensteinRowKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Each actual positive first-coordinate fibre contributes precisely its totient factor. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

def gamma0EisensteinCoordinateIntegral (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0<y)
    (c : Gamma0EisensteinPositiveFirst N) (d : {d : ℤ // IsCoprime (c.val:ℤ) d}) : ℂ :=
  ∫ x in Ioc (0:ℝ) 1, gamma0EisensteinPrimitiveTerm N s
    (gamma0EisensteinPositiveCoordinateRow N ⟨c,d⟩).val (gamma0EisensteinHorizontalPoint y hy x)

theorem gamma0EisensteinCoordinateTerm_eq (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0<y)
    (c : Gamma0EisensteinPositiveFirst N) (d : {d : ℤ // IsCoprime (c.val:ℤ) d}) (x : ℝ) :
    gamma0EisensteinPrimitiveTerm N s (gamma0EisensteinPositiveCoordinateRow N ⟨c,d⟩).val
      (gamma0EisensteinHorizontalPoint y hy x) = eisensteinRealRowTerm s (c.val:ℝ) (d.val:ℝ) x y := by
  have hn : ‖(c.val:ℂ)*Complex.mk x y+(d.val:ℂ)‖^2 =
      ((c.val:ℝ)*x+(d.val:ℝ))^2+((c.val:ℝ)*y)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,pow_two]
  change ((y/‖(c.val:ℂ)*Complex.mk x y+(d.val:ℂ)‖^2:ℝ):ℂ)^s=_
  rw [hn]
  rfl

theorem gamma0EisensteinCoordinateIntegral_eq (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0<y)
    (c : Gamma0EisensteinPositiveFirst N) (d : {d : ℤ // IsCoprime (c.val:ℤ) d}) :
    gamma0EisensteinCoordinateIntegral N s y hy c d =
      ∫ x in (0:ℝ)..1, eisensteinRealRowTerm s (c.val:ℝ) (d.val:ℝ) x y := by
  unfold gamma0EisensteinCoordinateIntegral
  simp_rw [gamma0EisensteinCoordinateTerm_eq]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

theorem gamma0EisensteinCoordinateIntegral_tsum (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) (c : Gamma0EisensteinPositiveFirst N)
    (hD : Summable (gamma0EisensteinCoordinateIntegral N s y hy c)) :
    (∑' d, gamma0EisensteinCoordinateIntegral N s y hy c d) =
      (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)*(y:ℂ)^(1-s)*
        ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by
  let e := eisensteinResidueTranslateEquiv c.val c.property.1
  have hR : Summable (fun v : EisensteinCoprimeResidues c.val × ℤ =>
      gamma0EisensteinCoordinateIntegral N s y hy c (e v)) := e.summable_iff.mpr hD
  have hprod := Summable.tsum_prod
    (f := fun v : EisensteinCoprimeResidues c.val × ℤ =>
      gamma0EisensteinCoordinateIntegral N s y hy c (e v)) hR
  rw [← e.tsum_eq (gamma0EisensteinCoordinateIntegral N s y hy c),hprod]
  have hinner (a : EisensteinCoprimeResidues c.val) :
      (∑' k : ℤ, gamma0EisensteinCoordinateIntegral N s y hy c (e (a,k))) =
        (c.val:ℂ)^(-2*s)*(y:ℂ)^(1-s)*
          ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by
    simp only [gamma0EisensteinCoordinateIntegral_eq,e,eisensteinResidueTranslateEquiv_apply,
      Int.cast_add,Int.cast_mul,Int.cast_natCast]
    exact eisensteinRealRowTerm_translate_integral s (by linarith)
      (c.val:ℝ) (by exact_mod_cast c.property.1) (a.val.val:ℝ) y hy
  simp_rw [hinner]
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,eisensteinCoprimeResidues_card,nsmul_eq_mul]
  ring

end ArtinMatthews
