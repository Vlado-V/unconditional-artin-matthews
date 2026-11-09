module

public import ArtinMatthews.SourceKPAdelicDefectTermContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual parameter derivative of each radial defect term, with
joint archimedean continuity. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups ContDiff
noncomputable section

def sourceKPAdelicDefectCoefficientPrime (T H : ℝ) : ℂ :=
  -(8*H*deriv (sourceKPAdelicHeightCutoff T) H : ℝ)

theorem sourceKPAdelicDefectCoefficient_hasDerivAt (T : ℝ) (s : ℂ) (H : ℝ) :
    HasDerivAt (fun z => sourceKPAdelicDefectCoefficient T z H)
      (sourceKPAdelicDefectCoefficientPrime T H) s := by
  let A : ℂ := -(4*H^2*deriv (deriv (sourceKPAdelicHeightCutoff T)) H : ℝ)
  let B : ℂ := (H : ℂ)*((deriv (sourceKPAdelicHeightCutoff T) H : ℝ) : ℂ)
  have h := ((((hasDerivAt_id s).const_mul 8).add_const 4).mul_const B).const_sub A
  convert h using 1
  · funext z
    dsimp only [sourceKPAdelicDefectCoefficient,A,B,id_eq]
    ring
  · dsimp only [sourceKPAdelicDefectCoefficientPrime,B]
    push_cast
    ring

theorem sourceKPAdelicDefectCoefficientPrime_continuous (T : ℝ) :
    Continuous (sourceKPAdelicDefectCoefficientPrime T) := by
  have hφ : ContDiff (ℝ) (2 : ℕ∞ω) (sourceKPAdelicHeightCutoff T) :=
    (sourceKPAdelicHeightCutoff_contDiff T).of_le (by simp)
  have hφ₁ : ContDiff (ℝ) (1 : ℕ∞ω) (deriv (sourceKPAdelicHeightCutoff T)) := hφ.deriv'
  have h := hφ₁.continuous
  unfold sourceKPAdelicDefectCoefficientPrime
  fun_prop

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicDefectTermDerivative (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (c : SourceKPRationalBorelCoset K) : ℂ :=
  (sourceKPAdelicDefectCoefficientPrime T (sourceKPAdelicRationalHeight K hζ q c) +
    sourceKPAdelicDefectCoefficient T s (sourceKPAdelicRationalHeight K hζ q c) *
      (Real.log (sourceKPAdelicRationalHeight K hζ q c) : ℂ)) *
    sourceKPAdelicRationalSummand K hζ
      (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)) q c

theorem sourceKPAdelicDefectTerm_hasDerivAt (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (c : SourceKPRationalBorelCoset K) :
    HasDerivAt (fun z => sourceKPAdelicDefectTerm K hζ T z q c)
      (sourceKPAdelicDefectTermDerivative K hζ T s q c) s := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    let a := sourceKPAdelicProjectiveRationalLift K hζ γ*q
    let H := sourceKPAdelicCoverHeight K hζ a
    change HasDerivAt (fun z => sourceKPAdelicDefectCoefficient T z H * sourceKPAdelicCompactScalar K hζ z a)
      ((sourceKPAdelicDefectCoefficientPrime T H + sourceKPAdelicDefectCoefficient T s H * (Real.log H : ℂ)) *
        sourceKPAdelicCompactScalar K hζ s a) s
    have h := (sourceKPAdelicDefectCoefficient_hasDerivAt T s H).mul
      (sourceKPAdelicCompactScalarParameterDerivative_hasDerivAt K hζ s a)
    convert h using 1
    unfold sourceKPAdelicCompactScalarParameterDerivative
    dsimp only [H]
    ring

theorem sourceKPAdelicDefectTermDerivative_joint_arch_continuous (T : ℝ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicDefectTermDerivative K hζ T p.1 (p.2,qf) c) := by
  have hH := sourceKPAdelicRationalHeight_arch_continuous K hζ qf c
  have hlog := hH.log (fun a => (sourceKPAdelicRationalHeight_pos K hζ (a,qf) c).ne')
  exact (((sourceKPAdelicDefectCoefficientPrime_continuous T).comp (hH.comp continuous_snd)).add
    (((sourceKPAdelicDefectCoefficient_continuous T).comp
      (continuous_fst.prodMk (hH.comp continuous_snd))).mul
        (Complex.continuous_ofReal.comp (hlog.comp continuous_snd)))).mul
          (sourceKPAdelicRationalScalar_joint_arch_continuous K hζ qf c)

end
end ArtinMatthews
