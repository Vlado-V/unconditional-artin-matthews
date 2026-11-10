module

public import ArtinMatthews.SpectralPoincareSeed
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import ArtinMatthews.SpectralPoincareSmooth
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


set_option backward.privateInPublic true
@[expose] public section

/-!
The actual Γ₀(N) compact-seed construction, with arithmeticity and determinant
one discharged by Mathlib.  The sum is over the full group, including both
central signs; no normalized Kuznetsov Poincaré-series identity is asserted.
-/

noncomputable section
open Set
open scoped CompactlySupported MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0PoincareSeed (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane, ℂ)) :
    C(UpperHalfPlane, ℂ) :=
  arithmeticPoincareSeed (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ

theorem gamma0PoincareSeed_invariant (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) (γ : CongruenceSubgroup.Gamma0 N)
    (z : UpperHalfPlane) :
    gamma0PoincareSeed N ψ ((γ : SL(2, ℤ)) • z) = gamma0PoincareSeed N ψ z := by
  let g : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
    ⟨Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)),
      Subgroup.mem_map.mpr ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩
  exact arithmeticPoincareSeed_invariant _ ψ g z

theorem gamma0PoincareSeed_support (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) {z : UpperHalfPlane}
    (hz : gamma0PoincareSeed N ψ z ≠ 0) :
    ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • z ∈ tsupport ψ := by
  obtain ⟨g, hg⟩ := arithmeticPoincareSeed_support
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ hz
  obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp g.property
  refine ⟨⟨γ, hγ⟩, ?_⟩
  change Matrix.SpecialLinearGroup.mapGL ℝ γ • z ∈ tsupport ψ
  rw [he]
  exact hg

theorem gamma0PoincareSeed_smooth (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ))
    (hψ : ContDiffOn ℝ ∞ (fun z : ℂ => ψ (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) :
    ContDiffOn ℝ ∞
      (fun z : ℂ => gamma0PoincareSeed N ψ (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} :=
  arithmeticPoincareSeed_smooth _ ψ hψ

end ArtinMatthews
