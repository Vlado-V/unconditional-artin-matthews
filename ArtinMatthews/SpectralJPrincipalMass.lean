module

public import ArtinMatthews.SpectralDiscretePolynomialMass
public import ArtinMatthews.SpectralJNativeAmplitudes


set_option backward.privateInPublic true
@[expose] public section

/-! The actual principal cusp density has a summable reciprocal-quartic weight. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups BigOperators
noncomputable section

def gamma0NativePrincipalDensity (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (i : Gamma0HeatPrincipalCuspidalIndex N) : ℝ :=
  ‖gamma0CuspUnitAmplitude N i.val b Y hY n hn‖ ^ 2 /
    Real.cosh (Real.pi * gamma0CuspPrincipalParameter N i.val)

theorem gamma0NativePrincipalDensity_summable_of_moment
    (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hMom : ∀ (u : Finset (Gamma0AllHeightSpectralIndex N)) (R : ℝ), 1 ≤ R →
      (∀ i ∈ u, 1 / 4 ≤ gamma0AllHeightGradientSpectralValue N i) →
      (∀ i ∈ u, 1 + |gamma0CuspPrincipalParameter N i| ≤ R) →
      gamma0CuspPrincipalMoment N u b Y hY n hn ≤ C * R ^ 2) :
    Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      gamma0NativePrincipalDensity N b Y hY n hn i /
        (1 + |gamma0CuspPrincipalParameter N i.val|) ^ 4) := by
  classical
  apply spectralQuadraticMass_quartic_summable
    (fun i : Gamma0HeatPrincipalCuspidalIndex N => 1 + |gamma0CuspPrincipalParameter N i.val|)
    (gamma0NativePrincipalDensity N b Y hY n hn)
    (fun i => by linarith only [abs_nonneg (gamma0CuspPrincipalParameter N i.val)])
    (fun i => div_nonneg (sq_nonneg _) (Real.cosh_pos _).le) C hC
  intro R hR u hcut
  let v := u.image (fun i : Gamma0HeatPrincipalCuspidalIndex N => i.val)
  have hprincipal : ∀ i ∈ v, 1 / 4 ≤ gamma0AllHeightGradientSpectralValue N i := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  have hcap : ∀ i ∈ v, 1 + |gamma0CuspPrincipalParameter N i| ≤ R := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hcut j hj
  have he : gamma0CuspPrincipalMoment N v b Y hY n hn =
      ∑ i ∈ u, gamma0NativePrincipalDensity N b Y hY n hn i := by
    unfold gamma0CuspPrincipalMoment
    dsimp only [v]
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    rfl
  rw [← he]
  exact hMom v R hR hprincipal hcap

end
end ArtinMatthews
