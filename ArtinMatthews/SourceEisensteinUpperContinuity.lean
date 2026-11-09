module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAdelicKernelCompactBound
public import Mathlib.Analysis.Normed.Group.FunctionSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine full adelic unipotent orbit is continuous, by locally uniform
convergence of the checked rational periodization. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactEisenstein_upper_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) :
    Continuous (fun y : 𝔸[K] => sourceKPAdelicCompactEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ y * g)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨C,hC,hCy⟩ := exists_compact_mem_nhds y
  obtain ⟨B,_hB,hbound⟩ := sourceKPAdelicIntertwiningKernel_compact_bound K hζ hs g C hC
  have hterms (x : K) : Continuous (fun a : 𝔸[K] =>
      sourceKPAdelicIntertwiningKernel K hζ s g (algebraMap K 𝔸[K] x + a)) :=
    (sourceKPAdelicIntertwiningKernel_continuous K hζ s g).comp (continuous_const.add continuous_id)
  have hsum := continuousOn_tsum (fun x => (hterms x).continuousOn)
    ((sourceKPRationalHeight_rpow_summable K hs).mul_left B)
    (fun x a ha => hbound a ha x)
  have hc : ContinuousAt (fun a : 𝔸[K] => sourceKPAdelicCompactScalar K hζ s g +
      ∑' x : K, sourceKPAdelicIntertwiningKernel K hζ s g (algebraMap K 𝔸[K] x + a)) y :=
    continuousAt_const.add (hsum.continuousAt hCy)
  exact hc.congr (Filter.Eventually.of_forall
    (fun a => (sourceKPAdelicCompactEisenstein_upper_periodization K hζ hs g a).symm))

theorem sourceKPAdelicNonconstantEisenstein_upper_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) :
    Continuous (fun y : 𝔸[K] => sourceKPAdelicNonconstantEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ y * g)) := by
  have hc := (sourceKPAdelicCompactEisenstein_upper_continuous K hζ hs g).sub
    (continuous_const : Continuous (fun _ : 𝔸[K] =>
      sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g))
  exact hc.congr (fun y => (sourceKPAdelicNonconstantEisenstein_upper K hζ s g y).symm)

end
end ArtinMatthews
