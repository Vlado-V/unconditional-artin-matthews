module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded band pairing identifies the vector residue through meromorphic uniqueness. -/

namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem sourceKPMeromorphicOn_eventuallyEq_of_germ {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) (he : f =ᶠ[𝓝 x] g) :
    f =ᶠ[𝓝[≠] y] g := by
  have hz : (f-g) =ᶠ[𝓝[≠] x] 0 := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  have htop := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hU hx hy
    (meromorphicOrderAt_eq_top_iff.mpr hz)
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with z hz
  exact sub_eq_zero.mp hz

theorem sourceKPBandResidue_pairing {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : H →L[ℂ] ℂ) {u : ℂ → H} {m j : ℂ → ℂ} {U : Set ℂ}
    (hU : IsPreconnected U) (hu : MeromorphicOn u U)
    (hm : MeromorphicOn m U) (hj : ∀ s, AnalyticAt ℂ j s)
    {a c : ℂ} (ha : a ∈ U) (hc : c ∈ U)
    (he : (fun s => L (u s)) =ᶠ[𝓝 a] fun s => m s*j s)
    {res : H} {resM : ℂ}
    (hres : Tendsto (fun s => (s-c) • u s) (𝓝[≠] c) (𝓝 res))
    (hresM : Tendsto (fun s => (s-c)*m s) (𝓝[≠] c) (𝓝 resM)) :
    L res = resM*j c := by
  have hLu : MeromorphicOn (fun s => L (u s)) U :=
    fun s hs => OAI.CubicEisenstein.meromorphicAt_clm L (hu s hs)
  have hmj : MeromorphicOn (fun s => m s*j s) U :=
    fun s hs => (hm s hs).mul (hj s).meromorphicAt
  have hec := sourceKPMeromorphicOn_eventuallyEq_of_germ hLu hmj hU ha hc he
  have hLres : Tendsto (fun s => (s-c)*L (u s)) (𝓝[≠] c) (𝓝 (L res)) := by
    simpa only [Function.comp_def,map_smul,smul_eq_mul] using (L.continuous.tendsto res).comp hres
  have hJ : Tendsto j (𝓝[≠] c) (𝓝 (j c)) :=
    (hj c).continuousAt.mono_left nhdsWithin_le_nhds
  have hM : Tendsto (fun s => (s-c)*L (u s)) (𝓝[≠] c) (𝓝 (resM*j c)) := by
    apply (hresM.mul hJ).congr'
    filter_upwards [hec] with s hs
    rw [hs,mul_assoc]
  exact tendsto_nhds_unique hLres hM

end
end ArtinMatthews
