module

public import ArtinMatthews.MarkedMajorComparableNormalization


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Finset
noncomputable section

/-- Literal supported triple source for independently normalized endpoints at
comparable product scales. Every finite summand and phase is retained. -/
theorem markedMajorLabel_comparable_finite_source_energy {J J' : Type*} [Fintype J] [Fintype J']
    (bands : J → Finset ℕ) (bands' : J' → Finset ℕ)
    (hbands : ∀ j p,p ∈ bands j → p.Prime) (hbands' : ∀ j p,p ∈ bands' j → p.Prime)
    (cutoff : ℝ → ℂ) {lo hi : ℝ} (hlo : 0 < lo) (hinterval : lo/2 < 8*hi)
    (hsupp : Function.support cutoff ⊆ Icc lo hi)
    {k q k' q' : ℕ} (χb : DirichletCharacter ℂ k) (χb' : DirichletCharacter ℂ k')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (θ θ' theta Y W X X' H u v U H' u' v' U' modulation modulation' : ℝ)
    (l r l' r' : ℕ) (β β' : ℕ → ℂ)
    (hY : 0 < Y) (hX : 0 < X) (hX' : 0 < X') (hH : 0 < H) (hU : 0 < U) (hH' : 0 < H') (hU' : 0 < U')
    (hscale : H*U=X) (hscale' : H'*U'=X') (hlow : X ≤ 2*X') (hupp : X' ≤ 2*X)
    (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (hHu' : H' ≤ u') (huv' : u' ≤ v') (hvH' : v' ≤ 2*H') (hl' : U' ≤ (l':ℝ)) (hr' : (r':ℝ) ≤ 2*U')
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Icc (-R) R) :
    ‖(Y:ℂ)⁻¹ * ∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      ∑ z' ∈ markedMajorSupportedTripleSet bands' cutoff Y u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*
      (ψ (X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))*
       OAI.Problem337.RealPhase.phase (theta*(X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))))‖ ≤
      (4*Y*X)*(∫ p : ℝ × ℝ,
        ‖markedMajorConstructedCoefficient ψ (half_pos hlo) hinterval hψ hX theta (p.1/X,p.2)*
          (markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β p.1*
           markedMajorLabelConjugateEndpoint bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β' (p.2-p.1))‖) := by
  classical
  have hlpos : 0 < l := by exact_mod_cast (hU.trans_le hl)
  have hlpos' : 0 < l' := by exact_mod_cast (hU'.trans_le hl')
  apply markedMajorComparable_normalized_bound hX hY
  apply markedMajor_finite_endpoint_L1_bound _ _ _ _ _ _ ψ (half_pos hlo) hinterval hψ hX
    (show 0 ≤ 2*Y*X by positivity) theta
  · intro z hz
    have hzcompact : markedMajorLabelTripleValue z/(Y*X) ∈ Icc lo (4*hi) := by
      simpa only [mul_assoc,hscale] using
        markedMajorSupportedTriple_compact bands cutoff hlo hsupp hY hH hU hHu huv hvH l r hl hr z hz
    exact markedMajorComparable_compact hlo hY hX hX (by linarith) (by linarith) hzcompact
  · intro z hz
    have hzcompact : markedMajorLabelTripleValue z/(Y*X') ∈ Icc lo (4*hi) := by
      simpa only [mul_assoc,hscale'] using
        markedMajorSupportedTriple_compact bands' cutoff hlo hsupp hY hH' hU' hHu' huv' hvH' l' r' hl' hr' z hz
    exact markedMajorComparable_compact hlo hY hX hX' hlow hupp hzcompact
  · exact markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W modulation H u v U l r β
  · exact markedMajorLabelConjugateEndpoint_continuous bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β'
  · exact markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W modulation H u v U l r β
  · exact markedMajorLabelConjugateEndpoint_bounded bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β'
  · intro t
    have he : ‖markedMajorEndpointPolynomial (markedMajorSupportedTripleSet bands cutoff Y u v l r)
        (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β)
        (fun z => markedMajorLabelTripleValue z/(Y*X)) t‖ =
        (Y*X)*‖markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t‖ := by
      simpa only [mul_assoc,hscale] using
        markedMajorSupportedEndpoint_norm bands hbands cutoff χb θ Y χ W modulation H u v U l r β hY hH hU hlpos t
    rw [he]
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hY hX]) (norm_nonneg _)
  · intro t
    have he := markedMajorEndpointPolynomial_norm_change_scale
      (markedMajorSupportedTripleSet bands' cutoff Y u' v' l' r')
      (markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β')
      markedMajorLabelTripleValue
      (fun z hz => markedMajorLabelTripleValue_pos bands' hbands' u' v' l' r' hlpos' z (mem_filter.mp hz).1)
      (mul_pos hY hX) (mul_pos (mul_pos hY hH') hU') t
    rw [he,markedMajorSupportedConjugateEndpoint_norm bands' hbands' cutoff χb' θ' Y χ' W modulation'
      H' u' v' U' l' r' β' hY hH' hU' hlpos']
    rw [show Y*H'*U' = Y*X' by rw [mul_assoc,hscale']]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hupp hY.le]

end
end ArtinMatthews
