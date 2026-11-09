module

public import ArtinMatthews.SpectralEisensteinReflectionScattering


set_option backward.privateInPublic true
@[expose] public section

/-! The reflected matching identity acts on the actual truncated
Eisenstein energy vector and on its finite cutoff profiles. -/
noncomputable section
open Matrix
namespace ArtinMatthews

theorem spectralReflectedProfileSum {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid V] [Module ℂ V] (M P : Matrix ι ι ℂ) (hMP : M*P=1)
    (j : ι) (u v : ι → V) :
    (∑ i,P i j • (u i+∑ k,M k i • v k))=(∑ i,P i j • u i)+v j := by
  have hc : M.mulVec (P.col j)=Pi.single j (1:ℂ) := by
    rw [← Matrix.col_mul_eq_mulVec_col,hMP]
    ext k
    by_cases hk : k=j
    · subst k
      simp [Matrix.col]
    · simp [Matrix.col,hk]
  simp only [smul_add,Finset.sum_add_distrib]
  congr 1
  change (∑ i,P.col j i • (∑ k,M k i • v k))=v j
  rw [spectralSum_smul_matrix_mulVec M (P.col j) v,hc,Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_reflection_regular (N : ℕ) [NeZero N]
    (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) (hq : gamma0EisensteinMatchingRegular N (1-s))
    (j : Gamma0EisensteinCuspClasses N) :
    gamma0CuspEisensteinMatchedTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N j) (1-s)=
      ∑ i,gamma0CuspScatteringMatrix N (1-s) i j •
        gamma0CuspEisensteinMatchedTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N i) s := by
  let M := gamma0CuspScatteringMatrix N s
  let P := gamma0CuspScatteringMatrix N (1-s)
  let R (w : ℂ) (i : Gamma0EisensteinCuspClasses N) :=
    gamma0EisensteinMatchingResponse N (gamma0EisensteinCuspClassRepresentative N i) w
  change -R (1-s) j-(∑ i,P i j • R (1-(1-s)) i)=
    ∑ i,P i j • (-R s i-(∑ k,M k i • R (1-s) k))
  rw [show (1:ℂ)-(1-s)=s from eisensteinParameterReflect_involutive s]
  have hMP : M*P=1 := gamma0CuspScatteringMatrix_reflection_regular N s hs hq
  have he := spectralReflectedProfileSum M P hMP j (fun i => -R s i) (fun i => -R (1-s) i)
  simp only [smul_neg,Finset.sum_neg_distrib,← sub_eq_add_neg] at he
  rw [he]
  abel

end ArtinMatthews
