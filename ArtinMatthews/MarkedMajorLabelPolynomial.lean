module

public import ArtinMatthews.MarkedMinorArcPrimeProducts
public import ArtinMatthews.MarkedSparsePrimeMoments


set_option backward.privateInPublic true
@[expose] public section

/-! The actual prime-label endpoint polynomial, with the product of the
band normalizers and the dyadic label normalization retained. -/
namespace ArtinMatthews
open Finset

noncomputable def markedMajorLabelSet {J : Type*} [Fintype J] (P : J → Finset ℕ) : Finset ℕ := by
  classical
  exact univ.image (markedPrimeBandProduct P)

noncomputable def markedMajorLabelMass {J : Type*} [Fintype J] (P : J → Finset ℕ) : ℝ :=
  ∏ j, (bandReciprocalMass (P j))⁻¹

lemma markedMajorLabelMass_pos {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) : 0 < markedMajorLabelMass P := by
  exact prod_pos (fun j _ => inv_pos.mpr (hV j))

lemma markedMajorLabelSet_pos {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime) {b : ℕ} (hb : b ∈ markedMajorLabelSet P) : 0 < b := by
  classical
  obtain ⟨t,_,rfl⟩ := mem_image.mp hb
  exact prod_pos (fun j _ => (hP j _ (t j).property).pos)

 theorem markedMajorLabelSet_reciprocal_mass {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (∑ b ∈ markedMajorLabelSet P, markedMajorLabelMass P/(b:ℝ)) = 1 := by
  classical
  rw [markedMajorLabelSet,sum_image (fun _ _ _ _ h => markedPrimeBandProduct_injective P hP hdis h)]
  have hsum : (∑ t : (j : J) → ↥(P j), 1/(markedPrimeBandProduct P t:ℝ)) =
      ∏ j, bandReciprocalMass (P j) := by
    simp only [markedPrimeBandProduct,Nat.cast_prod,one_div,← prod_inv_distrib]
    rw [← Fintype.prod_sum (fun j (p : ↥(P j)) => (p.val:ℝ)⁻¹)]
    apply prod_congr rfl
    intro j _
    simpa only [bandReciprocalMass,one_div] using sum_coe_sort (P j) (fun p : ℕ => (p:ℝ)⁻¹)
  calc
    _ = markedMajorLabelMass P*∑ t : (j : J) → ↥(P j), 1/(markedPrimeBandProduct P t:ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t _
      ring
    _ = markedMajorLabelMass P*∏ j,bandReciprocalMass (P j) := by rw [hsum]
    _ = 1 := by
      unfold markedMajorLabelMass
      rw [← prod_mul_distrib]
      simp only [inv_mul_cancel₀ (hV _).ne',prod_const_one]

noncomputable def markedMajorLabelPolynomial {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (η : ℝ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (θ Y t : ℝ) : ℂ :=
  (Y:ℂ)⁻¹*∑ b ∈ markedMajorLabelSet P,
    η ((b:ℝ)/Y)*Complex.exp (((-2*Real.pi*θ*(b:ℝ)/Y:ℝ):ℂ)*Complex.I)*
      (markedMajorLabelMass P:ℂ)*χ (b:ZMod q)*markedPrimePhase b t

 theorem markedMajorLabelPolynomial_norm_le {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (η : ℝ → ℂ) {R : ℝ} (hR : 0 ≤ R) (hη : ∀ y, ‖η y‖ ≤ 1)
    (hsupport : Function.support η ⊆ Set.Iic R) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (θ Y t : ℝ) (hY : 0 < Y) :
    ‖markedMajorLabelPolynomial P η χ θ Y t‖ ≤ R := by
  classical
  have hMass := markedMajorLabelMass_pos P hV
  unfold markedMajorLabelPolynomial
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY]
  have hterms : ∀ b ∈ markedMajorLabelSet P,
      ‖η ((b:ℝ)/Y)*Complex.exp (((-2*Real.pi*θ*(b:ℝ)/Y:ℝ):ℂ)*Complex.I)*
        (markedMajorLabelMass P:ℂ)*χ (b:ZMod q)*markedPrimePhase b t‖ ≤
          Y*R*(markedMajorLabelMass P/(b:ℝ)) := by
    intro b hb
    have hbpos : (0:ℝ) < b := by exact_mod_cast markedMajorLabelSet_pos P hP hb
    by_cases hz : η ((b:ℝ)/Y)=0
    · simp only [hz,zero_mul,norm_zero]
      positivity
    have hbR : (b:ℝ) ≤ Y*R := by
      have hh := hsupport hz
      exact (div_le_iff₀ hY).mp hh |>.trans_eq (mul_comm R Y)
    have hphase : ‖Complex.exp (((-2*Real.pi*θ*(b:ℝ)/Y:ℝ):ℂ)*Complex.I)‖=1 := by
      rw [Complex.norm_exp]
      simp
    simp only [norm_mul,hphase,markedPrimePhase_norm,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hMass]
    calc
      _ ≤ markedMajorLabelMass P := by
        have hχ := χ.norm_le_one (b:ZMod q)
        nlinarith [mul_nonneg (norm_nonneg (η ((b:ℝ)/Y))) (norm_nonneg (χ (b:ZMod q))),
          mul_le_mul (hη ((b:ℝ)/Y)) hχ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)]
      _ ≤ _ := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hbpos).mpr
        nlinarith [mul_le_mul_of_nonneg_right hbR hMass.le]
  calc
    _ ≤ Y⁻¹*∑ b ∈ markedMajorLabelSet P, Y*R*(markedMajorLabelMass P/(b:ℝ)) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum hterms)) (inv_nonneg.mpr hY.le)
    _ = R := by
      rw [← mul_sum,markedMajorLabelSet_reciprocal_mass P hP hdis hV]
      field_simp

end ArtinMatthews
