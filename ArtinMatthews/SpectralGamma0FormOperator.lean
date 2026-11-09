module

public import ArtinMatthews.SpectralGamma0WeakInverse
public import ArtinMatthews.SpectralModularDensity
public import OAI.Analysis.CoulombIonization.FormDomain.CoerciveOperator


set_option backward.privateInPublic true
@[expose] public section

/-! The self-adjoint operator represented by the actual completed Γ₀
mass-plus-gradient form. Its inverse is the previously constructed Green
operator. All density hypotheses are discharged by the genuine modular
smooth-core theorem. No coordinate Laplacian or cuspidal spectral
identification is asserted here. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0Green_selfAdjoint (N : ℕ) [NeZero N] : IsSelfAdjoint (gamma0Green N) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (gamma0Green_symmetric N)

theorem gamma0Green_eq_zero_iff (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N) :
    gamma0Green N F = 0 ↔ F = 0 := by
  constructor
  · intro h
    have he := gamma0Green_energy N F
    rw [h, inner_zero_right, Complex.zero_re] at he
    have hw : gamma0WeakSolution N F = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
    apply (gamma0EnergyInclusion_denseRange N).eq_of_inner_left ℂ
    intro v
    rw [← gamma0WeakSolution_equation, hw]
    simp
  · rintro rfl
    exact map_zero _

theorem gamma0Green_injective (N : ℕ) [NeZero N] : Function.Injective (gamma0Green N) := by
  intro F G h
  apply sub_eq_zero.mp
  apply (gamma0Green_eq_zero_iff N (F-G)).mp
  rw [map_sub, h, sub_self]

theorem gamma0Green_denseRange (N : ℕ) [NeZero N] : DenseRange (gamma0Green N) :=
  OAI.CoulombAtom.selfAdjoint_denseRange (gamma0Green_selfAdjoint N) (gamma0Green_injective N)

/-- The operator represented by the actual mass-plus-gradient energy form. -/
def gamma0MassEnergyOperator (N : ℕ) [NeZero N] : Gamma0RegionL2 N →ₗ.[ℂ] Gamma0RegionL2 N :=
  OAI.CoulombAtom.inverseOperator (gamma0Green N)

theorem gamma0MassEnergyOperator_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (gamma0MassEnergyOperator N) :=
  OAI.CoulombAtom.inverseOperator_selfAdjoint (gamma0Green_selfAdjoint N) (gamma0Green_injective N)

theorem gamma0MassEnergyOperator_domain (N : ℕ) [NeZero N] :
    (gamma0MassEnergyOperator N).domain = (gamma0Green N).range :=
  OAI.CoulombAtom.inverseOperator_domain _

theorem gamma0MassEnergyOperator_dense_domain (N : ℕ) [NeZero N] :
    Dense ((gamma0MassEnergyOperator N).domain : Set (Gamma0RegionL2 N)) :=
  (gamma0MassEnergyOperator_selfAdjoint N).dense_domain

theorem gamma0MassEnergyOperator_closed (N : ℕ) [NeZero N] :
    (gamma0MassEnergyOperator N).IsClosed :=
  (gamma0MassEnergyOperator_selfAdjoint N).isClosed

theorem gamma0MassEnergyOperator_graph (N : ℕ) [NeZero N] (x y : Gamma0RegionL2 N) :
    (x,y) ∈ (gamma0MassEnergyOperator N).graph ↔ gamma0Green N y = x :=
  OAI.CoulombAtom.inverseOperator_graph (gamma0Green_injective N) x y

theorem gamma0FormEnergy_inner (N : ℕ) [NeZero N] (u v : gamma0EnergySpace N) :
    inner ℂ u v = inner ℂ (gamma0EnergyInclusion N u) (gamma0EnergyInclusion N v) +
      inner ℂ (gamma0EnergyGradient N u) (gamma0EnergyGradient N v) := rfl

/-- Exact variational characterization on the actual completed energy domain. -/
theorem gamma0MassEnergyOperator_weak_graph (N : ℕ) [NeZero N] (x y : Gamma0RegionL2 N) :
    (x,y) ∈ (gamma0MassEnergyOperator N).graph ↔ ∃ u : gamma0EnergySpace N,
      gamma0EnergyInclusion N u = x ∧ ∀ v : gamma0EnergySpace N,
        inner ℂ u v = inner ℂ y (gamma0EnergyInclusion N v) := by
  rw [gamma0MassEnergyOperator_graph]
  constructor
  · intro h
    exact ⟨gamma0WeakSolution N y, (gamma0Green_apply N y).symm.trans h,
      gamma0WeakSolution_equation N y⟩
  · rintro ⟨u, hu, he⟩
    rw [gamma0Green_apply, ← gamma0WeakSolution_unique N y he, hu]

theorem gamma0MassEnergyOperator_mass_gradient_graph (N : ℕ) [NeZero N]
    (x y : Gamma0RegionL2 N) :
    (x,y) ∈ (gamma0MassEnergyOperator N).graph ↔ ∃ u : gamma0EnergySpace N,
      gamma0EnergyInclusion N u = x ∧ ∀ v : gamma0EnergySpace N,
        inner ℂ x (gamma0EnergyInclusion N v) +
          inner ℂ (gamma0EnergyGradient N u) (gamma0EnergyGradient N v) =
            inner ℂ y (gamma0EnergyInclusion N v) := by
  rw [gamma0MassEnergyOperator_weak_graph]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, fun v => ?_⟩
    rw [← hu, ← gamma0FormEnergy_inner]
    exact he v
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, fun v => ?_⟩
    rw [gamma0FormEnergy_inner, hu]
    exact he v

/-- The represented shifted operator is bounded below by the actual mass. -/
theorem gamma0MassEnergyOperator_lower_bound (N : ℕ) [NeZero N]
    (x y : Gamma0RegionL2 N) (h : (x,y) ∈ (gamma0MassEnergyOperator N).graph) :
    ‖x‖^2 ≤ (inner ℂ x y).re := by
  obtain ⟨u, hu, he⟩ := (gamma0MassEnergyOperator_weak_graph N x y).mp h
  have hn := sq_le_sq₀ (norm_nonneg x) (norm_nonneg u)
  have hb : ‖x‖ ≤ ‖u‖ := hu ▸ gamma0EnergyInclusion_bound N u
  have hnorm : ‖u‖^2 = (inner ℂ x y).re := calc
    _ = (inner ℂ u u).re := (inner_self_eq_norm_sq (𝕜:=ℂ) u).symm
    _ = (inner ℂ y x).re := by rw [he u, hu]
    _ = _ := inner_re_symm (𝕜:=ℂ) y x
  exact (hn.mpr hb).trans_eq hnorm

end ArtinMatthews
