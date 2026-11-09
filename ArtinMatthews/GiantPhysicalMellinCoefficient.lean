module

public import ArtinMatthews.GiantPhysicalMellin
public import ArtinMatthews.GiantTwoSidedPatternKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The Fourier variable shifts the actual dilation frequency in each
physical coefficient, including its auxiliary-prime product. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantPhysicalMellin_cpow_shift (ζ v : ℝ) {D : ℕ} (hD : 0 < D) :
    (D : ℂ) ^ (((ζ - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I) =
      (D : ℂ) ^ ((ζ : ℂ) * Complex.I) * primeExtractionMellinPhase (-v) D := by
  rw [giantPhysicalMellinPhase_nat_cpow (-v) hD]
  have he : (((ζ - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I) =
      (ζ : ℂ) * Complex.I + (((2 * Real.pi * (-v) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.cpow_add _ _ (by exact_mod_cast hD.ne')]

theorem giantTwoSidedPatternPhysicalCoefficient_mellin {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ v : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k + ell) Z)
    (t : GiantTwoSidedEndpointState P (k + ell) Z')
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    giantTwoSidedPatternPhysicalCoefficient step q (ζ - 2 * Real.pi * v) K s t aux =
      giantTwoSidedPatternPhysicalCoefficient step q ζ K s t aux *
        primeExtractionMellinPhase (-v)
          (giantTwoSidedPatternCopiedProduct C s.val.2 * giantTwoSidedPatternAuxiliaryProduct aux) := by
  have hD : 0 < giantTwoSidedPatternCopiedProduct C s.val.2 *
      giantTwoSidedPatternAuxiliaryProduct aux := Nat.mul_pos
    (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (s.val.2 j (Fin.castAdd ell i)).property).pos)
    (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (aux j i).property).pos)
  unfold giantTwoSidedPatternPhysicalCoefficient
  split_ifs
  · rw [giantPhysicalMellin_cpow_shift ζ v hD]
    simp only [Nat.cast_mul]
    ring
  · exact (zero_mul _).symm

end
end ArtinMatthews
