module

public import ArtinMatthews.SpectralGamma0GlobalWeakLaplacian
public import ArtinMatthews.SpectralGamma0FormOperator


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine represented self-adjoint operator agrees with the literal
mass-plus-hyperbolic-Laplacian on every actual compact smooth Poincare seed. -/

noncomputable section
namespace ArtinMatthews

theorem gamma0MassEnergyOperator_compact_seed_graph (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) :
    (gamma0SmoothSeedMass N ψ,
      gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ)) ∈
      (gamma0MassEnergyOperator N).graph :=
  (gamma0MassEnergyOperator_graph N _ _).mpr (gamma0Green_compact_seed_inverse N ψ)

end ArtinMatthews
