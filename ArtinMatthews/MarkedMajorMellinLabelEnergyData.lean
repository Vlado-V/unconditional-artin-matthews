module

public import ArtinMatthews.MarkedMajorMellinLocalMeanScaledConjugate
public import ArtinMatthews.MarkedMajorLabelConjugate


set_option backward.privateInPublic true
@[expose] public section

/-! Literal arithmetic data for one endpoint of the major-arc energy.
There are no analytic energy or cancellation fields. -/
namespace ArtinMatthews
open Finset MeasureTheory

structure MarkedMajorLabelEnergyConfig where
  c : ℝ
  C₁ : ℝ
  d : ℝ
  a : ℝ
  η : ℝ
  τ : ℝ
  C : ℝ
  D : ℝ
  A₀ : ℝ
  Kθ : ℝ
  v₀ : ℝ
  hc : 0 < c
  hC₁ : 0 < C₁
  hd : 0 < d
  ha : 0 ≤ a
  hη : 0 < η
  hτ : 0 < τ
  hC : 0 ≤ C
  hD : 0 ≤ D
  hA₀ : 0 ≤ A₀
  hKθ : 0 ≤ Kθ
  hv₀ : 0 < v₀

structure MarkedMajorLabelEnergyData (J : Type) (cfg : MarkedMajorLabelEnergyConfig) (L X : ℝ) where
  P₀ : Finset ℕ
  bands : J → Finset ℕ
  first_prime : ∀ p ∈ P₀, p.Prime
  bands_prime : ∀ j p, p ∈ bands j → p.Prime
  first_disjoint : ∀ j, Disjoint P₀ (bands j)
  bands_disjoint : Pairwise (fun i j => Disjoint (bands i) (bands j))
  first_mass : cfg.v₀ ≤ bandReciprocalMass P₀
  bands_mass : ∀ j, 0 < bandReciprocalMass (bands j)
  first_lower : ∀ p ∈ P₀, cfg.c*L^(1/(10:ℝ)) ≤ Real.log p
  first_upper : ∀ p ∈ P₀, Real.log p ≤ cfg.C₁*L^(1/(5:ℝ))
  Y : ℝ
  θ : ℝ
  H : ℝ
  u : ℝ
  v : ℝ
  U : ℝ
  l : ℕ
  r : ℕ
  β : ℕ → ℂ
  Y_pos : 0 < Y
  theta_bound : |θ| ≤ cfg.Kθ*L^cfg.A₀
  H_lower : Real.exp (cfg.τ*L) ≤ H
  H_le_u : H ≤ u
  u_le_v : u ≤ v
  v_le_two_H : v ≤ 2*H
  v_upper : v ≤ Real.exp (cfg.η*L)
  U_lower : Real.exp (cfg.d*L) ≤ U
  U_le_l : U ≤ (l:ℝ)
  r_le_two_U : (r:ℝ) ≤ 2*U
  product_eq : H*U = X
  coefficient_bound : ∀ n ∈ Icc l r, ‖β n‖ ≤ L^cfg.D
  q : ℕ
  k : ℕ
  q_ne_zero : q ≠ 0
  χ : DirichletCharacter ℂ q
  χb : DirichletCharacter ℂ k
  modulation : ℝ
  modulus_bound : (q:ℝ) ≤ L^cfg.a
  modulation_bound : |modulation| ≤ L^cfg.C

namespace MarkedMajorLabelEnergyData
variable {J : Type} {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}

def allBands (z : MarkedMajorLabelEnergyData J cfg L X) : Option J → Finset ℕ :=
  fun j => j.elim z.P₀ z.bands

theorem allBands_prime (z : MarkedMajorLabelEnergyData J cfg L X) :
    ∀ j p, p ∈ z.allBands j → p.Prime := by
  intro j p hp
  cases j with
  | none => exact z.first_prime p hp
  | some j => exact z.bands_prime j p hp

theorem allBands_disjoint (z : MarkedMajorLabelEnergyData J cfg L X) :
    Pairwise (fun i j => Disjoint (z.allBands i) (z.allBands j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j => exact z.first_disjoint j
  | some i =>
    cases j with
    | none => exact (z.first_disjoint i).symm
    | some j => exact z.bands_disjoint (fun he => hij (congrArg Option.some he))

theorem allBands_mass (z : MarkedMajorLabelEnergyData J cfg L X) :
    ∀ j, 0 < bandReciprocalMass (z.allBands j) := by
  intro j
  cases j with
  | none => exact cfg.hv₀.trans_le z.first_mass
  | some j => exact z.bands_mass j

theorem H_pos (z : MarkedMajorLabelEnergyData J cfg L X) : 0 < z.H :=
  (Real.exp_pos _).trans_le z.H_lower

theorem U_pos (z : MarkedMajorLabelEnergyData J cfg L X) : 0 < z.U :=
  (Real.exp_pos _).trans_le z.U_lower

noncomputable def endpoint [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) : ℝ → ℂ :=
  markedMajorLabelEndpoint z.allBands cutoff z.χb z.θ z.Y z.χ (Real.exp (L^(6/25:ℝ)))
    z.modulation z.H z.u z.v z.U z.l z.r z.β

noncomputable def conjugateEndpoint [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) : ℝ → ℂ :=
  markedMajorLabelConjugateEndpoint z.allBands cutoff z.χb z.θ z.Y z.χ (Real.exp (L^(6/25:ℝ)))
    z.modulation z.H z.u z.v z.U z.l z.r z.β

theorem endpoint_continuous [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) : Continuous (z.endpoint cutoff) :=
  markedMajorLabelEndpoint_continuous ..

theorem conjugateEndpoint_continuous [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) : Continuous (z.conjugateEndpoint cutoff) :=
  markedMajorLabelConjugateEndpoint_continuous ..

theorem endpoint_bounded [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) : ∃ B, ∀ t, ‖z.endpoint cutoff t‖ ≤ B :=
  markedMajorLabelEndpoint_bounded ..

theorem conjugateEndpoint_bounded [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) : ∃ B, ∀ t, ‖z.conjugateEndpoint cutoff t‖ ≤ B :=
  markedMajorLabelConjugateEndpoint_bounded ..

end MarkedMajorLabelEnergyData
end ArtinMatthews
