module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuationBase
public import Mathlib.Analysis.Meromorphic.Order


set_option backward.privateInPublic true
@[expose] public section

/-! Actual meromorphic continuation of the mixed-signature Dedekind series,
with exact pole order and class-number residue at one. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open scoped Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

private theorem discriminantInverse_entire :
    Differentiable ℂ (fun z : ℂ => ((mixedDiscriminantScale K : ℂ)^z)⁻¹) := by
  apply Differentiable.inv
  · exact differentiable_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
  · intro z
    exact cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))

theorem mixedRegularizedDedekindZeta_analyticAt {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (mixedRegularizedDedekindZeta K) s := by
  exact (((mixedCompletedDedekindXi_entire K).analyticAt s).mul
    ((discriminantInverse_entire K).analyticAt s)).mul
      ((mixedInverseGammaFactor_entire K).analyticAt s) |>.div analyticAt_id hs

theorem mixedRegularizedDedekindZeta_meromorphic :
    Meromorphic (mixedRegularizedDedekindZeta K) := by
  intro s
  exact ((((mixedCompletedDedekindXi_entire K).analyticAt s).meromorphicAt.mul
    ((discriminantInverse_entire K).analyticAt s).meromorphicAt).mul
    ((mixedInverseGammaFactor_entire K).analyticAt s).meromorphicAt).div
      (MeromorphicAt.id s)

/-- The zeta continuation given by the actual entire completion. Values at
poles use Lean's totalized division; its meromorphic germ is the stated object. -/
def mixedDedekindZetaContinuation (s : ℂ) : ℂ :=
  mixedRegularizedDedekindZeta K s / (s-1)

theorem mixedDedekindZetaContinuation_meromorphic :
    Meromorphic (mixedDedekindZetaContinuation K) := by
  intro s
  exact (mixedRegularizedDedekindZeta_meromorphic K s).div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt)

theorem mixedDedekindZetaContinuation_analyticAt {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (mixedDedekindZetaContinuation K) s :=
  (mixedRegularizedDedekindZeta_analyticAt K hs0).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1)

theorem mixedDedekindZetaContinuation_eq {s : ℂ} (hs : 1 < s.re) :
    mixedDedekindZetaContinuation K s = dedekindZeta K s := by
  unfold mixedDedekindZetaContinuation
  rw [mixedRegularizedDedekindZeta_eq K hs]
  have hs1 : s-1 ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he] at hs
    norm_num at hs
  exact mul_div_cancel_left₀ _ hs1

/-- The continued zeta has a genuine simple pole at one. -/
theorem mixedDedekindZetaContinuation_order_one :
    meromorphicOrderAt (mixedDedekindZetaContinuation K) 1 = -1 := by
  have ha := mixedRegularizedDedekindZeta_analyticAt K (s := 1) one_ne_zero
  have ho : meromorphicOrderAt (mixedRegularizedDedekindZeta K) 1 = 0 := by
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr
      (mixedRegularizedDedekindZeta_one_ne_zero K)]
    rfl
  change meromorphicOrderAt
    (mixedRegularizedDedekindZeta K / (fun s : ℂ => s-1)) 1 = -1
  have hd : MeromorphicAt (fun s : ℂ => s-1) 1 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  rw [meromorphicOrderAt_div ha.meromorphicAt hd, ho,
    meromorphicOrderAt_id_sub_const]
  norm_num

/-- The Laurent residue at the pole is the actual class-number residue. -/
theorem mixedDedekindZetaContinuation_residue :
    Tendsto (fun s : ℂ => (s-1)*mixedDedekindZetaContinuation K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  have H : Tendsto (mixedRegularizedDedekindZeta K) (𝓝[≠] 1)
      (𝓝 (mixedRegularizedDedekindZeta K 1)) :=
    (mixedRegularizedDedekindZeta_differentiableAt K
      (s := 1) one_ne_zero).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [mixedRegularizedDedekindZeta_one] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s-1 ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
  simp only [mixedDedekindZetaContinuation]
  exact (mul_div_cancel₀ _ hs1).symm

end
end ArtinMatthews.VaryingKummerAnalytic
