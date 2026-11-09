module

public import ArtinMatthews.SpectralEisensteinMatchingMatrix


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine meromorphic scattering obtained by finite matching of the
actual ambient weak equations. Agreement with the original normalized
constant term is exact, including removable zeros of the chosen matrix
determinant on the original domain. -/
noncomputable section
open Set Filter Topology Matrix MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinMatchingCandidate (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    Gamma0EisensteinCuspClasses N → ℂ :=
  (gamma0EisensteinMatchingMatrix N s).det⁻¹ •
    (gamma0EisensteinMatchingMatrix N s).cramer (gamma0EisensteinMatchingRhs N a s)

theorem gamma0EisensteinMatchingCandidate_meromorphic (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (i : Gamma0EisensteinCuspClasses N) :
    Meromorphic (fun s => gamma0EisensteinMatchingCandidate N a s i) := by
  intro s
  have hcol : MeromorphicAt (fun w => ((gamma0EisensteinMatchingMatrix N w).updateCol i
      (gamma0EisensteinMatchingRhs N a w)).det) s := by
    apply spectralMatrixDet_meromorphicAt
    intro j k
    by_cases h : k=i
    · simpa only [Matrix.updateCol_apply,ite_eq_left h] using gamma0EisensteinMatchingRhs_meromorphic N a j s
    · simpa only [Matrix.updateCol_apply,ite_eq_right h] using
        gamma0EisensteinMatchingMatrix_entry_meromorphic N j k s
  simpa only [gamma0EisensteinMatchingCandidate,Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,Pi.inv_apply] using
    (gamma0EisensteinMatchingMatrix_det_meromorphic N s).inv.fun_mul hcol

theorem gamma0EisensteinMatchingCandidate_eq_true (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain)
    (hd : (gamma0EisensteinMatchingMatrix N s).det≠0) :
    gamma0EisensteinMatchingCandidate N a s=gamma0EisensteinMatchingTrueCoefficient N a s := by
  let M := gamma0EisensteinMatchingMatrix N s
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  change M.mulVec (M.det⁻¹ • M.cramer (gamma0EisensteinMatchingRhs N a s))=
    M.mulVec (gamma0EisensteinMatchingTrueCoefficient N a s)
  rw [Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hd,one_smul]
  exact (gamma0EisensteinMatchingMatrix_equation N a s hs).symm

theorem gamma0EisensteinContinuationDomain_open : IsOpen gamma0EisensteinContinuationDomain := by
  change IsOpen ({s : ℂ | (1/2:ℝ)<s.re}∩{s : ℂ | (s*(1-s)).re<‖s*(1-s)‖})
  exact (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt (by fun_prop) (by fun_prop))

def gamma0CuspScatteringMeromorphic (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) : ℂ := by
  classical
  exact if s∈gamma0EisensteinContinuationDomain then gamma0CuspScatteringContinued N r a s
    else gamma0EisensteinMatchingCandidate N a s (gamma0EisensteinCuspClass N r)

theorem gamma0CuspScatteringMeromorphic_eq_offcut (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CuspScatteringMeromorphic N r a s=gamma0CuspScatteringContinued N r a s := by
  simp only [gamma0CuspScatteringMeromorphic,ite_eq_left hs]

theorem gamma0CuspScatteringMeromorphic_meromorphic (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) :
    Meromorphic (gamma0CuspScatteringMeromorphic N r a) := by
  intro s
  apply (gamma0EisensteinMatchingCandidate_meromorphic N a (gamma0EisensteinCuspClass N r) s).congr
  filter_upwards [gamma0EisensteinMatchingMatrix_det_eventually_ne_zero N s] with w hw
  by_cases h : w∈gamma0EisensteinContinuationDomain
  · rw [gamma0CuspScatteringMeromorphic_eq_offcut N r a w h,gamma0EisensteinMatchingCandidate_eq_true N a w h hw]
    exact (gamma0CuspScatteringContinued_equivalent_target N r _ a
      (gamma0EisensteinCuspClassRepresentative_equivalent N r) w h).symm
  · simp only [gamma0CuspScatteringMeromorphic,ite_eq_right h]

theorem gamma0CuspScatteringMeromorphic_analyticAt_offcut (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    AnalyticAt ℂ (gamma0CuspScatteringMeromorphic N r a) s := by
  apply (gamma0CuspScatteringContinued_analyticAt N r a s hs).congr
  filter_upwards [gamma0EisensteinContinuationDomain_open.mem_nhds hs] with w hw
  exact (gamma0CuspScatteringMeromorphic_eq_offcut N r a w hw).symm

theorem gamma0CuspScatteringMeromorphic_initial (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1<s.re) :
    gamma0CuspScatteringMeromorphic N r a s=gamma0CuspScattering N r a s := by
  rw [gamma0CuspScatteringMeromorphic_eq_offcut N r a s (gamma0EisensteinContinuationDomain_initial s hs),
    gamma0CuspScatteringContinued_initial N r a s hs]

theorem gamma0CuspEisenstein_initial_constant_matrix_meromorphic
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x))=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s+
        (y:ℂ)^(1-s)*gamma0CuspScatteringMeromorphic N r a s := by
  rw [gamma0CuspScatteringMeromorphic_initial N r a s hs]
  exact gamma0CuspEisenstein_all_cusp_constant_term N r a s hs y hy

end ArtinMatthews
