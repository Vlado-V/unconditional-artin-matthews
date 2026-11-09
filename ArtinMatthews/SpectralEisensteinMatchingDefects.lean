module

public import ArtinMatthews.SpectralEisensteinMatchingModes
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


set_option backward.privateInPublic true
@[expose] public section

/-! The weak defects of the actual outgoing truncated responses are
independent at every off-cut parameter. A vanishing combination would
solve the full ambient equation and hence coincide with the corresponding
outgoing cutoffs, whose actual cusp tails force the coefficients to vanish. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinOutgoingDefect (N : ℕ) [NeZero N] (s : ℂ)
    (i : Gamma0EisensteinCuspClasses N) : gamma0EnergySpace N :=
  gamma0EisensteinMatchingDefect N (gamma0EisensteinCuspClassRepresentative N i) (1-s)

theorem gamma0Eisenstein_reflect_parameter (s : ℂ) : (1-s)*(1-(1-s))=s*(1-s) := by ring

theorem gamma0Eisenstein_reflect_realPart {s : ℂ} (hs : (1/2:ℝ)<s.re) :
    (1-s).re<1/2 := by
  rw [Complex.sub_re,Complex.one_re]
  linarith

theorem gamma0EisensteinOutgoingDefect_sum_eq_zero_imp (N : ℕ) [NeZero N] (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain) (c : Gamma0EisensteinCuspClasses N → ℂ)
    (hc : (∑ i, c i • gamma0EisensteinOutgoingDefect N s i)=0) : c=0 := by
  let a := gamma0EisensteinCuspClassRepresentative N
  let hq := gamma0Eisenstein_reflect_realPart hs.1
  let U := ∑ i, c i • gamma0EisensteinMatchingResponse N (a i) (1-s)
  let W := ∑ i, c i • gamma0CuspOutgoingCutoffEnergy N (a i) (1-s) hq
  let F := ∑ i, c i • gamma0CuspEisensteinCompactForcingMass N (a i) (1-s)
  let P := gamma0EnergyResolventPencil N (s*(1-s))
  let J := gamma0EnergyMassAdjoint N
  have hU : U∈(gamma0EisensteinMatchingForm N).subspace :=
    (gamma0EisensteinMatchingForm N).subspace.sum_mem fun i _ =>
      (gamma0EisensteinMatchingForm N).subspace.smul_mem _ (gamma0EisensteinMatchingResponse_mem N _ _)
  have hPU : P U=J F := by
    simp only [gamma0EisensteinOutgoingDefect,gamma0EisensteinMatchingDefect,
      gamma0Eisenstein_reflect_parameter,smul_sub,Finset.sum_sub_distrib,sub_eq_zero] at hc
    simpa only [P,J,U,F,a,map_sum,map_smul] using hc
  have hPW : P W=J F := by
    simp only [P,J,W,F,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← gamma0Eisenstein_reflect_parameter s,gamma0CuspOutgoingCutoffEnergy_pencil]
  have he : U=W := gamma0EisensteinMatchingPencil_injective N _ hs.2 (hPU.trans hPW.symm)
  rw [he] at hU
  exact gamma0CuspOutgoingCutoffEnergy_sum_mem_imp_zero N (1-s) hq c hU

section Gram
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem spectralGram_det_ne_zero_of_sum (d : ι → E)
    (hd : ∀ c : ι → ℂ, (∑ i, c i • d i)=0 → c=0) :
    Matrix.det (fun i j => inner ℂ (d i) (d j))≠0 := by
  let A : Matrix ι ι ℂ := fun i j => inner ℂ (d i) (d j)
  apply isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp ?_)
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hker (c : ι → ℂ) (hc : A.mulVec c=0) : c=0 := by
    let u := ∑ j, c j • d j
    have h (i : ι) : inner ℂ (d i) u=0 := by
      have he := congrFun hc i
      simpa only [A,u,Matrix.mulVec,dotProduct,inner_sum,inner_smul_right,mul_comm,Pi.zero_apply] using he
    apply hd
    have hu : inner ℂ u u=0 := by
      calc
        inner ℂ u u=∑ j, inner ℂ (c j • d j) u := sum_inner _ _ _
        _=0 := by simp only [inner_smul_left,h,mul_zero,Finset.sum_const_zero]
    exact inner_self_eq_zero.mp hu
  intro c b h
  have h0 : A.mulVec (c-b)=0 := by rw [Matrix.mulVec_sub,h,sub_self]
  exact sub_eq_zero.mp (hker (c-b) h0)

end Gram
end ArtinMatthews
