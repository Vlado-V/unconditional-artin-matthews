module

public import ArtinMatthews.SourceArchWeightedDiagonal


set_option backward.privateInPublic true
@[expose] public section

/-! The finite product of the normalized local Fourier factors and
its exact parameter derivative. -/
namespace ArtinMatthews.SourceArchJacquet
open Filter
open scoped Topology BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceArchWeightedProduct (ψ : ι → ℂ → ℂ) (a : ι → ℂ) (s : ℂ) (y : ι → ℝ) : ℂ :=
  ∏ i, sourceArchWeightedDiagonalProfile (ψ i) s (a i) (y i)

def sourceArchWeightedProductDerivative (ψ : ι → ℂ → ℂ) (a : ι → ℂ) (s : ℂ) (y : ι → ℝ) : ℂ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i, sourceArchWeightedDiagonalProfile (ψ j) s (a j) (y j)) *
    sourceArchWeightedDiagonalProfileDerivative (ψ i) s (a i) (y i)

theorem sourceArchWeightedProduct_hasDerivAt (ψ : ι → ℂ → ℂ)
    (hψ : ∀ i, Continuous (ψ i)) (hψ₁ : ∀ i x, ‖ψ i x‖ ≤ 1)
    (a : ι → ℂ) {s : ℂ} (hs : 0 < s.re) (y : ι → ℝ) (hy : ∀ i, 0 < y i) :
    HasDerivAt (fun z => sourceArchWeightedProduct ψ a z y)
      (sourceArchWeightedProductDerivative ψ a s y) s := by
  have h (i : ι) (_ : i ∈ (Finset.univ : Finset ι)) :=
    sourceArchWeightedDiagonalProfile_hasDerivAt (ψ i) (hψ i) (hψ₁ i) hs (a i) (hy i)
  exact HasDerivAt.fun_finsetProd h

theorem sourceArchWeightedProduct_continuousAt (ψ : ι → ℂ → ℂ)
    (hψ : ∀ i, Continuous (ψ i)) (hψ₁ : ∀ i x, ‖ψ i x‖ ≤ 1)
    (a : ι → ℂ) (p : ℂ × (ι → ℝ)) (hs : 0 < p.1.re) (hy : ∀ i, 0 < p.2 i) :
    ContinuousAt (fun p : ℂ × (ι → ℝ) => sourceArchWeightedProduct ψ a p.1 p.2) p := by
  apply tendsto_finsetProd
  intro i _
  have hc : Continuous (fun p : ℂ × (ι → ℝ) => (p.1,a i,p.2 i)) :=
    continuous_fst.prodMk (continuous_const.prodMk ((continuous_apply i).comp continuous_snd))
  have h := sourceArchWeightedDiagonalProfile_continuousAt (ψ i) (hψ i) (hψ₁ i)
    (p.1,a i,p.2 i) hs (hy i)
  exact h.comp (f := fun q : ℂ × (ι → ℝ) => (q.1,a i,q.2 i)) (hc.continuousAt (x := p))

theorem sourceArchWeightedProductDerivative_continuousAt (ψ : ι → ℂ → ℂ)
    (hψ : ∀ i, Continuous (ψ i)) (hψ₁ : ∀ i x, ‖ψ i x‖ ≤ 1)
    (a : ι → ℂ) (p : ℂ × (ι → ℝ)) (hs : 0 < p.1.re) (hy : ∀ i, 0 < p.2 i) :
    ContinuousAt (fun p : ℂ × (ι → ℝ) => sourceArchWeightedProductDerivative ψ a p.1 p.2) p := by
  apply tendsto_finsetSum
  intro i _
  apply ContinuousAt.mul
  · apply tendsto_finsetProd
    intro j _
    have hc : Continuous (fun p : ℂ × (ι → ℝ) => (p.1,a j,p.2 j)) :=
      continuous_fst.prodMk (continuous_const.prodMk ((continuous_apply j).comp continuous_snd))
    exact (sourceArchWeightedDiagonalProfile_continuousAt (ψ j) (hψ j) (hψ₁ j)
      (p.1,a j,p.2 j) hs (hy j)).comp
      (f := fun q : ℂ × (ι → ℝ) => (q.1,a j,q.2 j)) (hc.continuousAt (x := p))
  · have hc : Continuous (fun p : ℂ × (ι → ℝ) => (p.1,a i,p.2 i)) :=
      continuous_fst.prodMk (continuous_const.prodMk ((continuous_apply i).comp continuous_snd))
    exact (sourceArchWeightedDiagonalProfileDerivative_continuousAt (ψ i) (hψ i) (hψ₁ i)
      (p.1,a i,p.2 i) hs (hy i)).comp
      (f := fun q : ℂ × (ι → ℝ) => (q.1,a i,q.2 i)) (hc.continuousAt (x := p))

theorem sourceArchWeightedProduct_analyticOnNhd (ψ : ι → ℂ → ℂ)
    (hψ : ∀ i, Continuous (ψ i)) (hψ₁ : ∀ i x, ‖ψ i x‖ ≤ 1)
    (a : ι → ℂ) (y : ι → ℝ) (hy : ∀ i, 0 < y i) :
    AnalyticOnNhd ℂ (fun z => sourceArchWeightedProduct ψ a z y) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (sourceArchWeightedProduct_hasDerivAt ψ hψ hψ₁ a hs y hy).differentiableAt.differentiableWithinAt

end
end ArtinMatthews.SourceArchJacquet
