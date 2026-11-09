module

public import ArtinMatthews.MarkedFinitePSDCompression
public import ArtinMatthews.MarkedFinitePowerMean


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine finite spectral-Hölder interpolation. The moment uses the
actual positive matrix power, and no dimension factor is introduced. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

theorem markedQuadraticForm_spectral_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (r : ℕ) (f : ι → ℂ) :
    markedQuadraticForm (B^r) f =
      ∑ i, (hB.eigenvalues i)^r * ‖((hB.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ f) i‖^2 := by
  let D := Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ))
  have hp : B^r = Unitary.conjStarAlgAut ℂ _ hB.eigenvectorUnitary
      (Matrix.diagonal (fun i => (((hB.eigenvalues i)^r : ℝ) : ℂ))) := by
    calc
      _ = (Unitary.conjStarAlgAut ℂ _ hB.eigenvectorUnitary D)^r :=
        congrArg (fun M : Matrix ι ι ℂ => M^r) hB.spectral_theorem
      _ = Unitary.conjStarAlgAut ℂ _ hB.eigenvectorUnitary (D^r) := (map_pow _ D r).symm
      _ = _ := by
        congr 1
        rw [Matrix.diagonal_pow]
        congr 1
        funext i
        simp only [Pi.pow_apply,Complex.ofReal_pow]
  calc
    _ = markedQuadraticForm
        (Unitary.conjStarAlgAut ℂ _ hB.eigenvectorUnitary
          (Matrix.diagonal (fun i => (((hB.eigenvalues i)^r : ℝ) : ℂ)))) f :=
      congrArg (fun M => markedQuadraticForm M f) hp
    _ = _ := by
      rw [Unitary.conjStarAlgAut_apply]
      have h := markedQuadraticForm_congruence
        (Matrix.diagonal (fun i => (((hB.eigenvalues i)^r : ℝ) : ℂ)))
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ f
      rw [Matrix.conjTranspose_conjTranspose,← Matrix.star_eq_conjTranspose] at h
      exact h.trans (markedQuadraticForm_diagonal _ _)

theorem markedPSD_spectralHolder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (f : ι → ℂ) (k : ℕ) :
    (markedQuadraticForm B f)^(k+1) ≤
      (∑ i, ‖f i‖^2)^k * markedQuadraticForm (B^(k+1)) f := by
  let c := (hB.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ f
  have h := markedWeightedPowerMean (fun i => ‖c i‖^2) hB.isHermitian.eigenvalues
    (fun _ => sq_nonneg _) hB.eigenvalues_nonneg k
  rw [markedQuadraticForm_spectral B hB.isHermitian,
    markedQuadraticForm_spectral_pow B hB.isHermitian]
  rw [← markedUnitary_energy hB.isHermitian.eigenvectorUnitary f]
  simpa only [c,mul_comm] using h

def markedMatrixPairing {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (f g : ι → ℂ) : ℂ :=
  star f ⬝ᵥ (A *ᵥ g)

theorem markedMatrixPairing_adjoint {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (f g : ι → ℂ) :
    markedMatrixPairing A f g = star (Aᴴ *ᵥ f) ⬝ᵥ g := by
  simp only [markedMatrixPairing,Matrix.star_mulVec,Matrix.conjTranspose_conjTranspose,
    Matrix.dotProduct_mulVec]

theorem markedMatrixPairing_cauchy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (f g : ι → ℂ) :
    ‖markedMatrixPairing A f g‖^2 ≤ markedQuadraticForm (A*Aᴴ) f * ∑ i, ‖g i‖^2 := by
  have hq := markedQuadraticForm_congruence (1 : Matrix ι ι ℂ) Aᴴ f
  rw [Matrix.conjTranspose_conjTranspose,mul_one,markedQuadraticForm_one] at hq
  rw [hq,markedMatrixPairing_adjoint]
  have hn : ‖star (Aᴴ *ᵥ f) ⬝ᵥ g‖ ≤ ∑ i, ‖(Aᴴ *ᵥ f) i‖*‖g i‖ := by
    simpa only [dotProduct,norm_mul,Pi.star_apply,norm_star] using
      norm_sum_le Finset.univ (fun i => star ((Aᴴ *ᵥ f) i)*g i)
  apply (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact sq_nonneg _
  · intro i _; exact sq_nonneg _
  · intro i _; exact le_of_eq (by ring)

theorem markedMatrixPairing_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (f g : ι → ℂ) (k : ℕ) :
    ‖markedMatrixPairing A f g‖^(2*(k+1)) ≤
      (∑ i, ‖g i‖^2)^(k+1) * (∑ i, ‖f i‖^2)^k *
        markedQuadraticForm ((A*Aᴴ)^(k+1)) f := by
  have hc := markedMatrixPairing_cauchy A f g
  have hp := pow_le_pow_left₀ (sq_nonneg ‖markedMatrixPairing A f g‖) hc (k+1)
  have hm := markedPSD_spectralHolder (A*Aᴴ) (Matrix.posSemidef_self_mul_conjTranspose A) f k
  have hg : 0 ≤ ∑ i, ‖g i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [mul_pow,← pow_mul] at hp
  calc
    _ ≤ (markedQuadraticForm (A*Aᴴ) f)^(k+1) * (∑ i, ‖g i‖^2)^(k+1) := hp
    _ ≤ ((∑ i, ‖f i‖^2)^k * markedQuadraticForm ((A*Aᴴ)^(k+1)) f) *
        (∑ i, ‖g i‖^2)^(k+1) := mul_le_mul_of_nonneg_right hm (pow_nonneg hg _)
    _ = _ := by ring

end
end ArtinMatthews
