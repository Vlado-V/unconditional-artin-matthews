module

public import ArtinMatthews.MarkedMajorComparableFiniteEnergy
public import ArtinMatthews.MarkedMajorLabelFiniteSupport


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Finset
noncomputable section

/-- Exact original triple source, with no truncation or cutoff error. -/
theorem markedMajorLabel_comparable_full_source_energy {J J' : Type*} [Fintype J] [Fintype J']
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
    ‖(Y:ℂ)⁻¹ * ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      ∑ z' ∈ markedMajorLabelTripleSet bands' u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*
      (ψ (X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))*
       OAI.Problem337.RealPhase.phase (theta*(X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))))‖ ≤
      (4*Y*X)*(∫ p : ℝ × ℝ,
        ‖markedMajorConstructedCoefficient ψ (half_pos hlo) hinterval hψ hX theta (p.1/X,p.2)*
          (markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β p.1*
           markedMajorLabelConjugateEndpoint bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β' (p.2-p.1))‖) := by
  have H := markedMajorLabel_comparable_finite_source_energy bands bands' hbands hbands' cutoff hlo hinterval hsupp
    χb χb' χ χ' θ θ' theta Y W X X' H u v U H' u' v' U' modulation modulation'
    l r l' r' β β' hY hX hX' hH hU hH' hU' hscale hscale' hlow hupp hHu huv hvH hl hr hHu' huv' hvH' hl' hr' ψ hψ
  have he := markedMajorSupported_bilateral_sum bands bands' cutoff χb χb' χ χ'
    θ θ' Y W modulation modulation' u v u' v' l r l' r' β β'
    (fun z z' => ψ (X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))*
      OAI.Problem337.RealPhase.phase (theta*(X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))))
  rw [he] at H
  exact H

end
end ArtinMatthews
