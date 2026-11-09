module

public import ArtinMatthews.SourceEisensteinNativeEnergy
public import ArtinMatthews.SourceEisensteinHighRemainderContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! The literal native gradient energy descends continuously to the genuine
high cusp, independently of the finite-level and compact-frame representatives. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter OAI.CubicEisenstein SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)

theorem sourceKPAdelicNonconstantEnergy_finite_right (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicNonconstantEnergy K hζ s (q*sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicNonconstantEnergy K hζ s q := by
  let d := sourceKPFiniteDeepCoverLift K hζ k
  let p := sourceKPArchNativeCoordinates K hζ q.1
  have hd : d.1 = 1 := sourceKPFiniteDeepCoverLift_fst K hζ k
  have hA : (q*d).1 = q.1 := by change q.1*d.1 = q.1; rw [hd,mul_one]
  have he : sourceKPAdelicNonconstantProductChart K hζ s (1,q.2*d.2) =ᶠ[𝓝 p]
      sourceKPAdelicNonconstantProductChart K hζ s (1,q.2) := by
    filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds
      (sourceKPArchNativeCoordinates_positive K hζ q.1)] with x hx
    let a := ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ x (fun v => productUpper_pos hx v))
    rw [sourceKPAdelicNonconstantProductChart_apply_of_positive K hζ s (1,q.2*d.2) x
      (fun v => productUpper_pos hx v),
      sourceKPAdelicNonconstantProductChart_apply_of_positive K hζ s (1,q.2) x
      (fun v => productUpper_pos hx v)]
    change sourceKPAdelicNonconstantEisenstein K hζ s ((1,q.2*d.2)*(a,1)) =
      sourceKPAdelicNonconstantEisenstein K hζ s ((1,q.2)*(a,1))
    have hmul : ((1,q.2*d.2) : SourceKPAdelicProjective K hζ)*(a,1) =
        ((1,q.2)*(a,1))*d := by
      apply Prod.ext
      · change 1*a = (1*a)*d.1
        rw [hd,mul_one]
      · change (q.2*d.2)*1 = (q.2*1)*d.2
        simp only [mul_one]
    rw [hmul]
    exact sourceKPAdelicNonconstantEisenstein_finite_right K hζ s ((1,q.2)*(a,1)) k
  unfold sourceKPAdelicNonconstantEnergy
  change productGradientEnergy (sourceKPAdelicNonconstantProductChart K hζ s (1,q.2*d.2))
    (sourceKPArchNativeCoordinates K hζ (q*d).1) = _
  rw [hA]
  change productGradientEnergy _ p = productGradientEnergy _ p
  simp only [productGradientEnergy,productPartial,he.fderiv_eq (𝕜 := ℝ)]

theorem sourceKPAdelicNonconstantEnergy_arch_right (s : ℂ)
    (a k : PGL(2,InfiniteAdeleRing K)) (hk : k ∈ sourceKPArchBaseCompactSubgroup K hζ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicNonconstantEnergy K hζ s (a*k,qf) =
      sourceKPAdelicNonconstantEnergy K hζ s (a,qf) := by
  simp only [sourceKPAdelicNonconstantEnergy,sourceKPArchNativeCoordinates,
    sourceKPArchGramCoordinates_compact K hζ a k hk]

theorem sourceKPAdelicNonconstantEnergy_arch_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2,InfiniteAdeleRing K) => sourceKPAdelicNonconstantEnergy K hζ s (a,qf)) := by
  let R := sourceKPAdelicNonconstantProductChart K hζ s (1,qf)
  have hE : ContinuousOn (productGradientEnergy R) U := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hD := (sourceKPAdelicNonconstantProductChart_contDiffAt K hζ hs (1,qf) p hp).continuousAt_fderiv
      (by norm_num)
    unfold productGradientEnergy
    apply tendsto_finsetSum
    intro v _
    have hy : Continuous (fun x : P => x v 2) := (EuclideanSpace.proj 2).continuous.comp (continuous_apply v)
    apply (hy.continuousAt.pow 2).mul
    apply tendsto_finsetSum
    intro j _
    change ContinuousAt (fun x : P => ‖fderiv ℝ R x (productDirection v j)‖ ^ 2) p
    exact (hD.clm_apply continuousAt_const).norm.pow 2
  exact hE.comp_continuous (sourceKPArchNativeCoordinates_continuous K hζ)
    (sourceKPArchNativeCoordinates_positive K hζ)

def sourceKPFiniteLevelNonconstantEnergy (s : ℂ) : SourceKPFiniteLevelSpace K hζ → ℝ :=
  sourceKPFiniteLevelDescend K hζ (sourceKPAdelicNonconstantEnergy K hζ s)
    (sourceKPAdelicNonconstantEnergy_finite_right K hζ s)

theorem sourceKPFiniteLevelNonconstantEnergy_mk (s : ℂ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelNonconstantEnergy K hζ s (sourceKPFiniteLevelMk K hζ q) =
      sourceKPAdelicNonconstantEnergy K hζ s q := rfl

theorem sourceKPFiniteLevelNonconstantEnergy_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    Continuous (sourceKPFiniteLevelNonconstantEnergy K hζ s) :=
  sourceKPFiniteLevelDescend_continuous K hζ _ _
    (sourceKPAdelicNonconstantEnergy_arch_continuous K hζ hs)

theorem sourceKPFiniteLevelNonconstantEnergy_rationalBorel {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (b : PGL(2,K)) (hb : b ∈ sourceKPRationalBorel K)
    (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelNonconstantEnergy K hζ s (b • x) =
      sourceKPFiniteLevelNonconstantEnergy K hζ s x := by
  obtain ⟨q,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  rw [← sourceKPFiniteLevelMk_rational,sourceKPFiniteLevelNonconstantEnergy_mk,
    sourceKPFiniteLevelNonconstantEnergy_mk,sourceKPAdelicNonconstantEnergy_rationalBorel K hζ hs b hb]

def sourceKPHighCuspNonconstantEnergy {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) : SourceKPHighCuspAutomorphic K hζ T → ℝ :=
  let E : SourceKPHighCuspBorelQuotient K hζ T → ℝ :=
    Quotient.lift (fun x : SourceKPHighCuspFinite K hζ T => sourceKPFiniteLevelNonconstantEnergy K hζ s x.val)
      (by
        intro x y hxy
        obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hxy
        rw [← hb]
        exact sourceKPFiniteLevelNonconstantEnergy_rationalBorel K hζ hs b.val b.property y.val)
  E ∘ (sourceKPHighCuspHomeomorph K hζ T hT).symm

theorem sourceKPHighCuspNonconstantEnergy_rep {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspNonconstantEnergy K hζ hs T hT (sourceKPHighCuspProjection K hζ T x) =
      sourceKPFiniteLevelNonconstantEnergy K hζ s x.val := by
  simp only [sourceKPHighCuspNonconstantEnergy,Function.comp_apply,
    ← sourceKPHighCuspHomeomorph_mk K hζ T hT x,Homeomorph.symm_apply_apply]
  rfl

theorem sourceKPHighCuspNonconstantEnergy_adelic {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (x : SourceKPHighCuspFinite K hζ T)
    (q : SourceKPAdelicProjective K hζ) (hq : sourceKPFiniteLevelMk K hζ q = x.val) :
    sourceKPHighCuspNonconstantEnergy K hζ hs T hT (sourceKPHighCuspProjection K hζ T x) =
      sourceKPAdelicNonconstantEnergy K hζ s q := by
  rw [sourceKPHighCuspNonconstantEnergy_rep,← hq,sourceKPFiniteLevelNonconstantEnergy_mk]

theorem sourceKPHighCuspNonconstantEnergy_nonneg {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (x : SourceKPHighCuspAutomorphic K hζ T) :
    0 ≤ sourceKPHighCuspNonconstantEnergy K hζ hs T hT x := by
  obtain ⟨a,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T x
  induction a using Quotient.inductionOn with
  | _ y =>
    rw [sourceKPHighCuspQuotientMap_mk]
    obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ y.val
    rw [sourceKPHighCuspNonconstantEnergy_adelic K hζ hs T hT y q hq]
    exact sourceKPAdelicNonconstantEnergy_nonneg K hζ s q

theorem sourceKPHighCuspNonconstantEnergy_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) :
    Continuous (sourceKPHighCuspNonconstantEnergy K hζ hs T hT) :=
  (((sourceKPFiniteLevelNonconstantEnergy_continuous K hζ hs).comp
    continuous_subtype_val).quotient_lift _).comp
      (sourceKPHighCuspHomeomorph K hζ T hT).symm.continuous

end
end ArtinMatthews
