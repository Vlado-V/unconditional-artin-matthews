module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef


set_option backward.privateInPublic true
@[expose] public section

/-! A positive-semidefinite compression on an arbitrary finite family of
testing vectors. The vectors need not be normalized or orthogonal. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

def markedQuadraticForm {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (f : ι → ℂ) : ℝ :=
  (star f ⬝ᵥ (B *ᵥ f)).re

theorem markedComplex_re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reCLM f s

theorem markedQuadraticForm_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (i : ι) :
    markedQuadraticForm B (Pi.single i 1) = (B i i).re := by
  simp only [markedQuadraticForm,← Pi.single_star,star_one,single_dotProduct,
    Matrix.mulVec_single_one,Matrix.col_apply,one_mul]

theorem markedQuadraticForm_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℂ) (U : Matrix ι κ ℂ) (a : κ → ℂ) :
    markedQuadraticForm (Uᴴ * B * U) a = markedQuadraticForm B (U *ᵥ a) := by
  simp only [markedQuadraticForm,Matrix.mulVec_mulVec,Matrix.star_mulVec,
    Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,Matrix.mul_assoc]

theorem markedQuadraticForm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (f : ι → ℂ) :
    markedQuadraticForm (Matrix.diagonal (fun i => (d i : ℂ))) f =
      ∑ i, d i * ‖f i‖^2 := by
  simp only [markedQuadraticForm,dotProduct,Pi.star_apply,Matrix.mulVec_diagonal,markedComplex_re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hn : star (f i) * f i = (‖f i‖ : ℂ)^2 := by
    simpa only [Complex.star_def] using Complex.conj_mul' (f i)
  have he : star (f i) * ((d i : ℂ)*f i) = ((d i*‖f i‖^2 : ℝ) : ℂ) := by
    calc
      _ = (d i : ℂ)*(star (f i)*f i) := by ring
      _ = _ := by rw [hn,Complex.ofReal_mul,Complex.ofReal_pow]
  simpa only [Complex.ofReal_re] using congrArg Complex.re he

theorem markedQuadraticForm_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) :
    markedQuadraticForm (1 : Matrix ι ι ℂ) f = ∑ i, ‖f i‖^2 := by
  simpa only [Complex.ofReal_one,Matrix.diagonal_one,one_mul] using
    markedQuadraticForm_diagonal (fun _ : ι => (1 : ℝ)) f

theorem markedUnitary_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (f : ι → ℂ) :
    (∑ i, ‖((U : Matrix ι ι ℂ)ᴴ *ᵥ f) i‖^2) = ∑ i, ‖f i‖^2 := by
  have hu : (U : Matrix ι ι ℂ)*star (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.property
  have h := markedQuadraticForm_congruence (1 : Matrix ι ι ℂ) (U : Matrix ι ι ℂ)ᴴ f
  rw [Matrix.conjTranspose_conjTranspose,mul_one,← Matrix.star_eq_conjTranspose,
    hu,markedQuadraticForm_one,markedQuadraticForm_one] at h
  exact h.symm

theorem markedQuadraticForm_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (f : ι → ℂ) :
    markedQuadraticForm B f =
      ∑ i, hB.eigenvalues i * ‖((hB.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ f) i‖^2 := by
  calc
    _ = markedQuadraticForm
        (Unitary.conjStarAlgAut ℂ _ hB.eigenvectorUnitary
          (Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)))) f :=
      congrArg (fun M => markedQuadraticForm M f) hB.spectral_theorem
    _ = _ := by
      rw [Unitary.conjStarAlgAut_apply]
      have h := markedQuadraticForm_congruence
        (Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)))
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ f
      rw [Matrix.conjTranspose_conjTranspose] at h
      rw [← Matrix.star_eq_conjTranspose] at h
      exact h.trans (markedQuadraticForm_diagonal _ _)

theorem markedPSD_quadratic_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (f : ι → ℂ) :
    markedQuadraticForm B f ≤ (∑ i, (B i i).re) * ∑ i, ‖f i‖^2 := by
  have ht : (∑ i, (B i i).re) = ∑ i, hB.isHermitian.eigenvalues i := by
    calc
      _ = (B.trace).re := by rw [Matrix.trace,markedComplex_re_sum]; rfl
      _ = (∑ i, (hB.isHermitian.eigenvalues i : ℂ)).re :=
        congrArg Complex.re hB.isHermitian.trace_eq_sum_eigenvalues
      _ = _ := by
        rw [markedComplex_re_sum]
        apply Finset.sum_congr rfl
        intro i _
        rfl
  rw [markedQuadraticForm_spectral B hB.isHermitian,ht,
    ← markedUnitary_energy hB.isHermitian.eigenvectorUnitary f,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)) (sq_nonneg _)

theorem markedPSD_compression {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (U : Matrix ι κ ℂ) (a : κ → ℂ) :
    markedQuadraticForm B (U *ᵥ a) ≤
      (∑ j, markedQuadraticForm B (fun i => U i j)) * ∑ j, ‖a j‖^2 := by
  have hC := hB.conjTranspose_mul_mul_same U
  have h := markedPSD_quadratic_le_trace (Uᴴ * B * U) hC a
  rw [markedQuadraticForm_congruence] at h
  have hd (j : κ) : ((Uᴴ * B * U) j j).re =
      markedQuadraticForm B (fun i => U i j) := by
    rw [← markedQuadraticForm_single]
    rw [markedQuadraticForm_congruence]
    simp only [Matrix.mulVec_single_one,Matrix.col_apply']
  simpa only [hd] using h

end
end ArtinMatthews
