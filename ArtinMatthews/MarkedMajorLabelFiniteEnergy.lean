module

public import ArtinMatthews.MarkedMajorMellinFiniteEnergy
public import ArtinMatthews.MarkedMajorLabelSupportedEndpoint
public import ArtinMatthews.MarkedMajorLabelBounded


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Finset
noncomputable section

theorem markedMajorSupportedEndpoint_norm {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) {k q : ℕ} (χb : DirichletCharacter ℂ k) (θ Y : ℝ)
    (χ : DirichletCharacter ℂ q) (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U) (hl : 0 < l) (t : ℝ) :
    ‖markedMajorEndpointPolynomial (markedMajorSupportedTripleSet bands cutoff Y u v l r)
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β)
      (fun z => markedMajorLabelTripleValue z/(Y*H*U)) t‖ =
      (Y*H*U)*‖markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t‖ := by
  rw [markedMajorSupportedEndpoint_eq,markedMajorLabel_scaled_endpoint_identity
    bands hbands cutoff χb θ Y χ W modulation H u v U l r β hY hH hU hl,
    norm_mul,markedMajor_scale_phase_norm,one_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (mul_pos (mul_pos hY hH) hU)]

theorem markedMajorSupportedConjugateEndpoint_norm {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) {k q : ℕ} (χb : DirichletCharacter ℂ k) (θ Y : ℝ)
    (χ : DirichletCharacter ℂ q) (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U) (hl : 0 < l) (t : ℝ) :
    ‖markedMajorEndpointPolynomial (markedMajorSupportedTripleSet bands cutoff Y u v l r)
      (markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β)
      (fun z => markedMajorLabelTripleValue z/(Y*H*U)) t‖ =
      (Y*H*U)*‖markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t‖ := by
  simp only [markedMajorLabelConjugateTripleCoefficient_eq,markedMajorLabelConjugateEndpoint_eq]
  exact markedMajorSupportedEndpoint_norm bands hbands cutoff χb θ Y χ W (-modulation) H u v U l r β hY hH hU hl t

/-- Literal two supported triple sums, with independent endpoint arithmetic and
common scale X=HU=H'U', satisfy the exact normalized energy inequality. -/
theorem markedMajorLabel_finite_source_energy {J J' : Type*} [Fintype J] [Fintype J']
    (bands : J → Finset ℕ) (bands' : J' → Finset ℕ)
    (hbands : ∀ j p,p ∈ bands j → p.Prime) (hbands' : ∀ j p,p ∈ bands' j → p.Prime)
    (cutoff : ℝ → ℂ) {lo hi : ℝ} (hlo : 0 < lo) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Icc lo hi)
    {k q k' q' : ℕ} (χb : DirichletCharacter ℂ k) (χb' : DirichletCharacter ℂ k')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (θ θ' theta Y W X H u v U H' u' v' U' modulation modulation' : ℝ)
    (l r l' r' : ℕ) (β β' : ℕ → ℂ)
    (hY : 0 < Y) (hX : 0 < X) (hH : 0 < H) (hU : 0 < U) (hH' : 0 < H') (hU' : 0 < U')
    (hscale : H*U=X) (hscale' : H'*U'=X)
    (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (hHu' : H' ≤ u') (huv' : u' ≤ v') (hvH' : v' ≤ 2*H') (hl' : U' ≤ (l':ℝ)) (hr' : (r':ℝ) ≤ 2*U')
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Icc (-R) R) :
    ‖(Y:ℂ)⁻¹ * ∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      ∑ z' ∈ markedMajorSupportedTripleSet bands' cutoff Y u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*
      (ψ (X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))*
       OAI.Problem337.RealPhase.phase (theta*(X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))))‖ ≤
      (Y*X)*(∫ p : ℝ × ℝ,
        ‖markedMajorConstructedCoefficient ψ hlo hinterval hψ hX theta (p.1/X,p.2)*
          (markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β p.1*
           markedMajorLabelConjugateEndpoint bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β' (p.2-p.1))‖) := by
  have hlpos : 0 < l := by exact_mod_cast (hU.trans_le hl)
  have hlpos' : 0 < l' := by exact_mod_cast (hU'.trans_le hl')
  apply markedMajor_normalized_endpoint_bound hX hY
  apply markedMajor_finite_endpoint_L1_bound _ _ _ _ _ _ ψ hlo hinterval hψ hX (mul_pos hY hX).le theta
  · intro z hz
    simpa only [mul_assoc,hscale] using
      markedMajorSupportedTriple_compact bands cutoff hlo hsupp hY hH hU hHu huv hvH l r hl hr z hz
  · intro z hz
    simpa only [mul_assoc,hscale'] using
      markedMajorSupportedTriple_compact bands' cutoff hlo hsupp hY hH' hU' hHu' huv' hvH' l' r' hl' hr' z hz
  · exact markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W modulation H u v U l r β
  · exact markedMajorLabelConjugateEndpoint_continuous bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β'
  · exact markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W modulation H u v U l r β
  · exact markedMajorLabelConjugateEndpoint_bounded bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β'
  · intro t
    apply le_of_eq
    simpa only [mul_assoc,hscale] using
      markedMajorSupportedEndpoint_norm bands hbands cutoff χb θ Y χ W modulation H u v U l r β hY hH hU hlpos t
  · intro t
    apply le_of_eq
    simpa only [mul_assoc,hscale'] using
      markedMajorSupportedConjugateEndpoint_norm bands' hbands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β' hY hH' hU' hlpos' t

end
end ArtinMatthews
