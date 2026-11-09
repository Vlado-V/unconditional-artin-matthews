module

public import ArtinMatthews.SpectralPeterssonHeckeMajorant
public import ArtinMatthews.SpectralPeterssonHolomorphic


set_option backward.privateInPublic true
@[expose] public section

/-! The zero-regulator sum is holomorphic. Both the fixed-modulus
translation sums and the outer modulus sum converge locally uniformly. -/

noncomputable section
open Set Filter UpperHalfPlane Matrix
open scoped MatrixGroups UpperHalfPlane Manifold

namespace ArtinMatthews

private theorem petersson_mdiff_tsum_of_compact_majorant {ι : Type*} (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i, MDiff (F i))
    (hbd : ∀ K : Set UpperHalfPlane, IsCompact K →
      ∃ U : ι → ℝ, Summable U ∧ ∀ i z, z ∈ K → ‖F i z‖ ≤ U i) :
    MDiff (fun z => ∑' i, F i z) := by
  let P (z : UpperHalfPlane) := ∑' i, F i z
  let Q (s : Finset ι) (z : UpperHalfPlane) := ∑ i ∈ s, F i z
  have hL : TendstoLocallyUniformly Q P atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨U,hU,h⟩ := hbd K hK
    exact tendstoUniformlyOn_tsum (hu := hU) h
  have hL' : TendstoLocallyUniformlyOn (fun s => ↑ₕ(Q s)) (↑ₕP) atTop upperHalfPlaneSet := by
    rw [← range_coe,← image_univ]
    apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
    · simpa only [Set.top_eq_univ,tendstoLocallyUniformlyOn_univ] using hL
    · intro z _
      exact Set.mem_univ _
  have hD : ∀ᶠ s in atTop, DifferentiableOn ℂ (↑ₕ(Q s)) upperHalfPlaneSet := by
    apply Eventually.of_forall
    intro s
    change DifferentiableOn ℂ (fun z => ∑ i ∈ s, F i (ofComplex z)) upperHalfPlaneSet
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (differentiableOn_const (0 : ℂ))
    | @insert i s hi hs =>
      simp only [Finset.sum_insert hi]
      exact (UpperHalfPlane.mdifferentiable_iff.mp (hF i)).add hs
  exact UpperHalfPlane.mdifferentiable_iff.mpr (hL'.differentiableOn hD isOpen_upperHalfPlaneSet)

theorem spectralPeterssonHeckeOrbital_zero_summand_bound (m : ℕ+) (G : SL(2, ℝ))
    (hC : 0 < G 1 0) (l : ℤ) (z : UpperHalfPlane) :
    ‖spectralHolomorphicSlash 2 (G*realTranslation (l : ℝ)) (spectralPeterssonHeckeSeed 0 m) z‖ ≤
      (G 1 0)^(- (2 : ℝ))/(z.im^2+(z.re+G 1 1/(G 1 0)+(l : ℝ))^2) := by
  let q := G 1 0
  let y := z.im
  let x := z.re+G 1 1/q+(l : ℝ)
  let A := G 0 0
  let lam := spectralPeterssonHeckeLambda m q y
  have hC' : 0 < q := hC
  have hy : 0 < y := z.im_pos
  have hl : 0 ≤ lam := by dsimp only [lam,spectralPeterssonHeckeLambda]; positivity
  rw [spectralHolomorphicSlash_mul,spectralHolomorphicSlash_realTranslation,
    spectralPeterssonHeckeSlash_rescale 0 m G hC,realTranslation_im_smul,realTranslation_re_smul]
  have hx : z.re+(l : ℝ)+G 1 1/(G 1 0)=x := by dsimp only [x,q]; ring
  rw [hx]
  change ‖(atkinPhase ((m : ℝ)*A/q)*((q^(-(2+2*(0 : ℝ)))*y^(-2-0) : ℝ) : ℂ))*
    spectralPeterssonHeckeProfile 0 lam (x/y)‖ ≤ q^(-(2 : ℝ))/(y^2+x^2)
  simp only [norm_mul,atkinPhase_norm,one_mul,Complex.norm_real,mul_zero,add_zero,sub_zero,
    Real.norm_of_nonneg (Real.rpow_nonneg hC'.le _),Real.norm_of_nonneg (Real.rpow_nonneg hy.le _)]
  refine (mul_le_mul_of_nonneg_left (spectralPeterssonHeckeProfile_norm_le 0 lam (x/y) le_rfl hl)
    (mul_nonneg (Real.rpow_nonneg hC'.le _) (Real.rpow_nonneg hy.le _))).trans_eq ?_
  rw [Real.rpow_neg hy.le,Real.rpow_two]
  field_simp [hy.ne',show y^2+x^2 ≠ 0 by positivity]
  <;> ring

theorem spectralPeterssonHeckeOrbital_zero_mdifferentiable (m : ℕ+) (G : SL(2, ℝ))
    (hC : 0 < G 1 0) : MDiff (spectralPeterssonHeckeOrbital 0 m G) := by
  let F (l : ℤ) := spectralHolomorphicSlash 2 (G*realTranslation (l : ℝ)) (spectralPeterssonHeckeSeed 0 m)
  have hF (l : ℤ) : MDiff (F l) := by
    apply UpperHalfPlane.mdifferentiable_iff.mpr
    simp only [F,spectralPeterssonHeckeSeed_zero]
    exact spectralHolomorphicSeedSlash_differentiableOn 2 (m : ℕ) _
  unfold spectralPeterssonHeckeOrbital
  refine petersson_mdiff_tsum_of_compact_majorant F hF ?_
  intro K hK
  obtain ⟨A,B,hB,hKB⟩ := subset_verticalStrip_of_isCompact hK
  let d := G 1 1/(G 1 0)
  let R := max A 0+|d|
  let E := (1+2*R^2)/B^2
  let M := 2+E
  let q := G 1 0
  let U (l : ℤ) : ℝ := (q^(-(2 : ℝ))*M)*(1+(l : ℝ)^2)⁻¹
  have hC' : 0 < q := hC
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨U,spectralPetersson_inverseSquare_samples_summable.mul_left _,?_⟩
  intro l z hz
  let x := z.re+d+(l : ℝ)
  have h := hKB hz
  change |z.re| ≤ A ∧ B ≤ z.im at h
  have hR : |z.re+d| ≤ R := (abs_add_le _ _).trans (add_le_add (h.1.trans (le_max_left _ _)) le_rfl)
  have hR_sq : (z.re+d)^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hR 2
  have hX : (l : ℝ)^2 ≤ 2*x^2+2*R^2 := by
    dsimp only [x]
    nlinarith only [hR_sq,sq_nonneg (z.re+d+(z.re+d+(l : ℝ)))]
  have hB_sq : B^2 ≤ z.im^2 := pow_le_pow_left₀ hB.le h.2 2
  have hE' : E*B^2 = 1+2*R^2 := by dsimp only [E]; field_simp
  have hdom : 1+(l : ℝ)^2 ≤ M*(z.im^2+x^2) := by
    dsimp only [M]
    nlinarith only [hX,hE',mul_le_mul_of_nonneg_left hB_sq hE,sq_nonneg z.im,
      mul_nonneg hE (sq_nonneg x)]
  have hpos : 0 < z.im^2+x^2 := by positivity
  refine (spectralPeterssonHeckeOrbital_zero_summand_bound m G hC l z).trans ?_
  change q^(-(2 : ℝ))/(z.im^2+x^2) ≤ _
  dsimp only [U]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ hpos (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hdom (Real.rpow_nonneg hC'.le (-(2 : ℝ)))]

theorem gamma0PeterssonHeckeModulus_zero_mdifferentiable (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (m : ℕ+) (c : Ioi (0 : ℕ)) : MDiff (gamma0PeterssonHeckeModulus N b a 0 m c) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let F (R : gamma0TrueWidthReducedMatrix N b a c.val) :=
    spectralPeterssonHeckeOrbital 0 m (gamma0TrueWidthMatrix N b a R.val)
  have hD (R : gamma0TrueWidthReducedMatrix N b a c.val) : MDiff (F R) := by
    apply spectralPeterssonHeckeOrbital_zero_mdifferentiable
    rw [gamma0TrueWidthMatrix_lower N b a R.val c.val R.property.2.1]
    exact gamma0TrueWidthModulus_pos N b a (Nat.cast_pos.mpr c.property)
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  change DifferentiableOn ℂ (fun z => ∑ R, F R (ofComplex z)) upperHalfPlaneSet
  suffices h : ∀ s : Finset (gamma0TrueWidthReducedMatrix N b a c.val),
      DifferentiableOn ℂ (fun z => ∑ R ∈ s, F R (ofComplex z)) upperHalfPlaneSet from h Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (differentiableOn_const (0 : ℂ))
  | @insert p s hp hs =>
    simp only [Finset.sum_insert hp]
    exact (UpperHalfPlane.mdifferentiable_iff.mp (hD p)).add hs

theorem gamma0PeterssonHeckeZeroSector_zero_mdifferentiable (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (m : ℕ+) : MDiff (gamma0PeterssonHeckeZeroSector N b a 0 m) := by
  classical
  rcases isEmpty_or_nonempty (Gamma0PeterssonZeroRow N b a) with h | h
  · let _ := h
    have he : gamma0PeterssonHeckeZeroSector N b a 0 m = fun _ => (0 : ℂ) := by
      funext z
      exact tsum_empty
    rw [he]
    exact mdifferentiable_const
  · let p := h.some
    have hfun : gamma0PeterssonHeckeZeroSector N b a 0 m = gamma0PeterssonHeckeSignedSummand N b a 0 m p.val.val := by
      funext z
      unfold gamma0PeterssonHeckeZeroSector
      exact tsum_eq_single p (fun q hq => (hq (Subsingleton.elim q p)).elim)
    rw [hfun]
    apply UpperHalfPlane.mdifferentiable_iff.mpr
    simp only [gamma0PeterssonHeckeSignedSummand,gamma0PeterssonHeckeMatrixSeed,spectralPeterssonHeckeSeed_zero]
    exact spectralHolomorphicSeedSlash_differentiableOn 2 (m : ℕ) _

theorem gamma0PeterssonHeckeGrouped_zero_mdifferentiable (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (m : ℕ+) : MDiff (gamma0PeterssonHeckeGrouped N b 1 0 m) := by
  let F (c : Ioi (0 : ℕ)) := gamma0PeterssonHeckeModulus N b 1 0 m c
  have h : MDiff (fun z => ∑' c, F c z) := by
    refine petersson_mdiff_tsum_of_compact_majorant F (gamma0PeterssonHeckeModulus_zero_mdifferentiable N b 1 m) ?_
    intro K hK
    obtain ⟨A,B,hB,hKB⟩ := subset_verticalStrip_of_isCompact hK
    obtain ⟨D,hD,hbd⟩ := gamma0PeterssonHeckeModulus_majorant N b m B hB
    let U (c : Ioi (0 : ℕ)) := (D/B)*(c.val : ℝ)^(-(5/4 : ℝ))
    refine ⟨U,gamma0PeterssonHecke_rawModulusMajorant_summable.mul_left _,?_⟩
    intro c z hz
    have hz' : B ≤ z.im := (hKB hz).2
    have hh := hbd 0 c z ⟨le_rfl,zero_le_one⟩ hz'
    have hnorm : ‖F c z‖*B ≤ D*(c.val : ℝ)^(-(5/4 : ℝ)) :=
      (mul_le_mul_of_nonneg_left hz' (norm_nonneg _)).trans hh
    dsimp only [U]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hB).mpr hnorm
  exact (gamma0PeterssonHeckeZeroSector_zero_mdifferentiable N b 1 m).add h

end ArtinMatthews
