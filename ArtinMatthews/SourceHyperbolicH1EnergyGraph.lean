module

public import ArtinMatthews.SourceHyperbolicH1ClosedGraph
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

abbrev H1Ambient (ι : Type*) [Fintype ι] := WithLp 2 (H1Mass ι × H1Gradient ι)

def h1EnergySubmodule (ι : Type*) [Fintype ι] : Submodule ℂ (H1Ambient ι) :=
  (h1InitialGraph ι).topologicalClosure.comap
    (WithLp.linearEquiv 2 ℂ (H1Mass ι × H1Gradient ι)).toLinearMap

theorem h1EnergySubmodule_isClosed : IsClosed (h1EnergySubmodule ι : Set (H1Ambient ι)) :=
  (h1InitialGraph ι).isClosed_topologicalClosure.preimage
    (WithLp.prodContinuousLinearEquiv 2 ℂ (H1Mass ι) (H1Gradient ι)).continuous

abbrev H1EnergySpace (ι : Type*) [Fintype ι] := h1EnergySubmodule ι

instance h1EnergySpace_complete : CompleteSpace (H1EnergySpace ι) :=
  h1EnergySubmodule_isClosed.completeSpace_coe

def h1EnergyMass (ι : Type*) [Fintype ι] : H1EnergySpace ι →L[ℂ] H1Mass ι :=
  (ContinuousLinearMap.fst ℂ (H1Mass ι) (H1Gradient ι)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ (H1Mass ι) (H1Gradient ι)).toContinuousLinearMap.comp
      (h1EnergySubmodule ι).subtypeL)

def h1EnergyGradient (ι : Type*) [Fintype ι] : H1EnergySpace ι →L[ℂ] H1Gradient ι :=
  (ContinuousLinearMap.snd ℂ (H1Mass ι) (H1Gradient ι)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ (H1Mass ι) (H1Gradient ι)).toContinuousLinearMap.comp
      (h1EnergySubmodule ι).subtypeL)

theorem h1Energy_norm_sq (u : H1EnergySpace ι) :
    ‖u‖^2 = ‖h1EnergyMass ι u‖^2 + ‖h1EnergyGradient ι u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.val

theorem h1EnergyMass_injective : Function.Injective (h1EnergyMass ι) := by
  suffices hzero : ∀ u : H1EnergySpace ι, h1EnergyMass ι u=0 → u=0 by
    intro u v huv
    apply sub_eq_zero.mp
    apply hzero (u-v)
    rw [map_sub,huv,sub_self]
  intro u hu
  have hg : h1EnergyGradient ι u=0 := h1InitialGraph_closure_unique u.val.ofLp u.prop hu
  apply norm_eq_zero.mp
  have hn := h1Energy_norm_sq u
  simp only [hu,hg,norm_zero,zero_pow (by decide : 2≠0),add_zero] at hn
  exact (sq_eq_zero_iff.mp hn)

def h1EnergyCore (f : h1Tests ι 2) : H1EnergySpace ι :=
  ⟨WithLp.toLp 2 (h1TestMass f,h1TestGradient f),
    (h1InitialGraph ι).le_topologicalClosure ⟨f,rfl⟩⟩

theorem h1EnergyMass_core (f : h1Tests ι 2) : h1EnergyMass ι (h1EnergyCore f) = h1TestMass f := rfl

theorem h1EnergyGradient_core (f : h1Tests ι 2) : h1EnergyGradient ι (h1EnergyCore f) = h1TestGradient f := rfl

theorem h1EnergyMass_denseRange : DenseRange (h1EnergyMass ι) := by
  apply (h1TestMass_denseRange (ι := ι) 2 (by simp)).mono
  rintro _ ⟨f,rfl⟩
  exact ⟨h1EnergyCore f,rfl⟩

def h1DirichletEnergy (u : H1EnergySpace ι) : ℝ := ‖h1EnergyGradient ι u‖^2

theorem h1DirichletEnergy_nonneg (u : H1EnergySpace ι) : 0 ≤ h1DirichletEnergy u := sq_nonneg _

theorem h1EnergyGraph_inner (u v : H1EnergySpace ι) :
    inner ℂ u v = inner ℂ (h1EnergyMass ι u) (h1EnergyMass ι v) +
      inner ℂ (h1EnergyGradient ι u) (h1EnergyGradient ι v) := rfl

end
end ArtinMatthews.SourceHyperbolicGreen
