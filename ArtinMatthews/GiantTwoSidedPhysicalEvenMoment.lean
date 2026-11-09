module

public import ArtinMatthews.GiantTwoSidedPhysicalMatrixPaths
public import ArtinMatthews.MarkedFiniteEvenMomentPaths
public import ArtinMatthews.MarkedPhysicalMomentTrace


set_option backward.privateInPublic true
@[expose] public section

/-! The source even moment is the position-diagonal trace of the true
physical operator. The two endpoint lists remain independently summed. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantTwoSidedPhysicalPositionTrace_eq_expanded {I J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime) {k ell : ℕ}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (roots Z : Finset ℕ) (R : ℕ) :
    let A := giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns C step q ζ K
    let pos (s : GiantTwoSidedEndpointState P (k+ell) Z) := s.val.1.val
    let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
    (∑ r ∈ roots, markedQuadraticForm ((A*Aᴴ)^R) (markedPositionVector pos σ r)) =
      (giantTwoSidedExpandedPhysicalMoment (fun _ : Fin (2*R) => patterns) (fun _ => C)
        (fun i => if i.val%2 = 0 then step else -step) q
        (fun i => if i.val%2 = 0 then ζ else -ζ)
        (fun i p a b aux => if i.val%2 = 0 then K p a b aux else star (K p b a aux)) roots Z).re := by
  intro A pos σ
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let W (s : Fin (2*R+1) → State) := markedMatrixPathWeight (markedAlternatingMatrix A) (2*R) 0 s
  let End (s : Fin (2*R+1) → State) : Prop := pos (s 0) ∈ roots ∧ pos (s (Fin.last (2*R))) = pos (s 0)
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _ (fun j =>
    Finset.sum_nonneg (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)))
  have hA (i : Fin (2*R)) : markedAlternatingMatrix A i.val =
      giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns C
        (if i.val%2 = 0 then step else -step) q (if i.val%2 = 0 then ζ else -ζ)
        (fun p a b aux => if i.val%2 = 0 then K p a b aux else star (K p b a aux)) := by
    by_cases hi : i.val%2 = 0
    · simp only [markedAlternatingMatrix, hi, ite_true, A]
    · simpa only [markedAlternatingMatrix, hi, ite_false, A, Complex.star_def] using
        giantTwoSidedPhysicalFamilyMatrix_adjoint (Z := Z) hP patterns C step q ζ K
  have hquad (r : ℕ) : markedQuadraticForm ((A*Aᴴ)^R) (markedPositionVector pos σ r) =
      σ * (∑ s : Fin (2*R+1) → State, if pos (s 0) = r ∧ pos (s (Fin.last (2*R))) = r then W s else 0).re := by
    have hs : markedPositionVector pos σ r = (Real.sqrt σ : ℂ) • (fun s => if pos s = r then 1 else 0) := by
      funext s
      by_cases h : pos s = r <;> simp [markedPositionVector, h]
    rw [hs, markedPSD_quadratic_real_scale _ ((Matrix.posSemidef_self_mul_conjTranspose A).pow R),
      Real.sq_sqrt hσ, markedEvenMoment_indicator_paths]
  have hroot (s : Fin (2*R+1) → State) :
      (∑ r ∈ roots, if pos (s 0) = r ∧ pos (s (Fin.last (2*R))) = r then W s else 0) =
        if End s then W s else 0 := by
    by_cases hs : pos (s 0) ∈ roots
    · rw [Finset.sum_eq_single_of_mem (pos (s 0)) hs]
      · simp only [End, hs, true_and]
      · intro r _ hr
        simp only [Ne.symm hr, false_and, ite_false]
    · rw [Finset.sum_eq_zero (fun r hr => by
        have he : pos (s 0) ≠ r := fun h => hs (h ▸ hr)
        simp only [he, false_and, ite_false])]
      simp only [End, hs, false_and, ite_false]
  calc
    _ = σ * (∑ s : Fin (2*R+1) → State, if End s then W s else 0).re := by
      simp_rw [hquad]
      rw [← Finset.mul_sum, ← markedComplex_re_sum, Finset.sum_comm]
      simp_rw [hroot]
    _ = _ := by
      rw [giantTwoSidedExpandedPhysicalMoment_matrix_paths]
      have hw (s : Fin (2*R+1) → State) := markedMatrixPathWeight_product (markedAlternatingMatrix A) (2*R) 0 s
      simp only [zero_add, hA] at hw
      simp_rw [← hw]
      have hm : σ * (∑ s : Fin (2*R+1) → State, if End s then W s else 0).re =
          ((σ : ℂ) * (∑ s : Fin (2*R+1) → State, if End s then W s else 0)).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hm, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      change (σ : ℂ) * (if End s then W s else 0) = (if End s then (σ : ℂ) else 0) * W s
      by_cases hs : End s <;> simp [hs]

end
end ArtinMatthews
