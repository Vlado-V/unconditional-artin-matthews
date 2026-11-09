module

public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A convergent product of eighth roots of unity has finite support.
This turns the genuine analytic Weil product into literal finite products,
without assuming a support set. -/

namespace ArtinMatthews.QuadraticWeil

open scoped Classical
noncomputable section

variable {ι : Type*}

def eighthRootOf (f : ι → ℂ) (h8 : ∀ i, f i ^ 8 = 1) (i : ι) : rootsOfUnity 8 ℂ :=
  ⟨Units.mk0 (f i) (by
    intro hz
    have h := h8 i
    rw [hz, zero_pow (by decide)] at h
    exact zero_ne_one h), by
    apply Units.ext
    exact h8 i⟩

def eighthRootVal : rootsOfUnity 8 ℂ →* ℂ :=
  (Units.coeHom ℂ).comp (rootsOfUnity 8 ℂ).subtype

theorem eighthRootVal_inducing : Topology.IsInducing eighthRootVal :=
  Units.isEmbedding_val₀.isInducing.comp Topology.IsEmbedding.subtypeVal.isInducing

theorem hasFiniteMulSupport_of_eighth (f : ι → ℂ) (hprod : HasProd f 1)
    (h8 : ∀ i, f i ^ 8 = 1) : Function.HasFiniteMulSupport f := by
  have hroot : HasProd (eighthRootOf f h8) 1 := by
    apply (eighthRootVal_inducing.hasProd_iff (eighthRootOf f h8) 1).mp
    exact hprod
  have hs := hroot.multipliable.hasFiniteMulSupport_of_discreteTopology
  apply hs.subset
  intro i hi
  change f i ≠ 1 at hi
  change eighthRootOf f h8 i ≠ 1
  intro he
  apply hi
  exact congrArg eighthRootVal he

end

end ArtinMatthews.QuadraticWeil
