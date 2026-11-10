module

public import ArtinMatthews.MarkedFiniteSpectralMoments
public import ArtinMatthews.MarkedFinitePowerMean
public import Mathlib.Analysis.Matrix.PosDef


set_option backward.privateInPublic true
@[expose] public section

/-! Spectral Hölder and Cauchy summed over localizations. Both estimates
use the total vector energy; the number of cells does not occur. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

theorem markedPSD_sum_spectralHolder {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (f : κ → ι → ℂ) (k : ℕ) :
    (∑ j, markedQuadraticForm B (f j))^(k+1) ≤
      (∑ j, ∑ i, ‖f j i‖^2)^k * ∑ j, markedQuadraticForm (B^(k+1)) (f j) := by
  let c := fun j => (hB.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ f j
  have h := markedWeightedPowerMean
    (fun z : κ × ι => ‖c z.1 z.2‖^2)
    (fun z : κ × ι => hB.isHermitian.eigenvalues z.2)
    (fun _ => sq_nonneg _) (fun z => hB.eigenvalues_nonneg z.2) k
  simp only [Fintype.sum_prod_type] at h
  have he : (∑ j, ∑ i, ‖c j i‖^2) = ∑ j, ∑ i, ‖f j i‖^2 := by
    apply Finset.sum_congr rfl
    intro j _
    exact markedUnitary_energy hB.isHermitian.eigenvectorUnitary (f j)
  rw [he] at h
  simpa only [markedQuadraticForm_spectral B hB.isHermitian,
    markedQuadraticForm_spectral_pow B hB.isHermitian,c,mul_comm] using h

theorem markedMatrixPairing_sum_cauchy {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (f g : κ → ι → ℂ) :
    ‖∑ j, markedMatrixPairing A (f j) (g j)‖^2 ≤
      (∑ j, markedQuadraticForm (A*Aᴴ) (f j)) * ∑ j, ∑ i, ‖g j i‖^2 := by
  have hq (j : κ) := markedQuadraticForm_congruence (1 : Matrix ι ι ℂ) Aᴴ (f j)
  simp only [Matrix.conjTranspose_conjTranspose,mul_one,markedQuadraticForm_one] at hq
  simp_rw [hq,markedMatrixPairing_adjoint,dotProduct]
  have hn : ‖∑ j, ∑ i, star ((Aᴴ *ᵥ f j) i)*g j i‖ ≤
      ∑ j, ∑ i, ‖(Aᴴ *ᵥ f j) i‖*‖g j i‖ := by
    simpa only [Fintype.sum_prod_type,norm_mul,norm_star] using
      norm_sum_le Finset.univ
        (fun z : κ × ι => star ((Aᴴ *ᵥ f z.1) z.2)*g z.1 z.2)
  apply (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
  have hs : (∑ z : κ × ι, ‖(Aᴴ *ᵥ f z.1) z.2‖*‖g z.1 z.2‖)^2 ≤
      (∑ z : κ × ι, ‖(Aᴴ *ᵥ f z.1) z.2‖^2) * ∑ z : κ × ι, ‖g z.1 z.2‖^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro z _; exact sq_nonneg _
    · intro z _; exact sq_nonneg _
    · intro z _; exact le_of_eq (by ring)
  simpa only [Fintype.sum_prod_type] using hs

theorem markedMatrixPairing_sum_moment {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (f g : κ → ι → ℂ) (k : ℕ) :
    ‖∑ j, markedMatrixPairing A (f j) (g j)‖^(2*(k+1)) ≤
      (∑ j, ∑ i, ‖g j i‖^2)^(k+1) * (∑ j, ∑ i, ‖f j i‖^2)^k *
        ∑ j, markedQuadraticForm ((A*Aᴴ)^(k+1)) (f j) := by
  have hc := markedMatrixPairing_sum_cauchy A f g
  have hp := pow_le_pow_left₀ (sq_nonneg ‖∑ j, markedMatrixPairing A (f j) (g j)‖) hc (k+1)
  have hm := markedPSD_sum_spectralHolder (A*Aᴴ)
    (Matrix.posSemidef_self_mul_conjTranspose A) f k
  have hg : 0 ≤ ∑ j, ∑ i, ‖g j i‖^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [mul_pow,← pow_mul] at hp
  calc
    _ ≤ (∑ j, markedQuadraticForm (A*Aᴴ) (f j))^(k+1) *
        (∑ j, ∑ i, ‖g j i‖^2)^(k+1) := hp
    _ ≤ ((∑ j, ∑ i, ‖f j i‖^2)^k *
          ∑ j, markedQuadraticForm ((A*Aᴴ)^(k+1)) (f j)) *
        (∑ j, ∑ i, ‖g j i‖^2)^(k+1) :=
      mul_le_mul_of_nonneg_right hm (pow_nonneg hg _)
    _ = _ := by ring

end
end ArtinMatthews
