module

public import ArtinMatthews.MarkedMajorCharacterSource
public import ArtinMatthews.MarkedMajorMellinLabelEnergyData


set_option backward.privateInPublic true
@[expose] public section

/-! The six character twists preserve every actual arithmetic requirement of
the endpoint-energy theorem. No energy or cancellation assumption is added. -/
namespace ArtinMatthews
noncomputable section
namespace MarkedMajorLabelEnergyData
variable {J : Type} {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}

def characterLeft (z : MarkedMajorLabelEnergyData J cfg L X)
    (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    MarkedMajorLabelEnergyData J cfg L X :=
  { z with
    θ := θ
    theta_bound := hθ
    β := fun n => z.β n*markedCoordinateDirichlet q χ 3 n
    coefficient_bound := fun n hn => markedMajor_character_twisted_coefficient_bound _ _ n (z.coefficient_bound n hn)
    q := q
    k := q
    q_ne_zero := NeZero.ne q
    χ := markedCoordinateDirichlet q χ 2
    χb := markedCoordinateDirichlet q χ 1
    modulus_bound := hq }

def characterRight (z : MarkedMajorLabelEnergyData J cfg L X)
    (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    MarkedMajorLabelEnergyData J cfg L X :=
  { z with
    θ := -θ
    theta_bound := by simpa only [abs_neg] using hθ
    β := fun n => z.β n*markedCoordinateDirichlet q χ 5 n
    coefficient_bound := fun n hn => markedMajor_character_twisted_coefficient_bound _ _ n (z.coefficient_bound n hn)
    q := q
    k := q
    q_ne_zero := NeZero.ne q
    χ := markedCoordinateDirichlet q χ 4
    χb := markedCoordinateDirichlet q χ 0
    modulus_bound := hq }

theorem characterLeft_endpoint [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    (z.characterLeft q χ θ hq hθ).endpoint cutoff =
      markedMajorLabelEndpoint z.allBands cutoff (markedCoordinateDirichlet q χ 1) θ z.Y
        (markedCoordinateDirichlet q χ 2) (Real.exp (L^(6/25:ℝ))) z.modulation
        z.H z.u z.v z.U z.l z.r (fun n => z.β n*markedCoordinateDirichlet q χ 3 n) := rfl

theorem characterRight_conjugateEndpoint [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
    (cutoff : ℝ → ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    (z.characterRight q χ θ hq hθ).conjugateEndpoint cutoff =
      markedMajorLabelConjugateEndpoint z.allBands cutoff (markedCoordinateDirichlet q χ 0) (-θ) z.Y
        (markedCoordinateDirichlet q χ 4) (Real.exp (L^(6/25:ℝ))) z.modulation
        z.H z.u z.v z.U z.l z.r (fun n => z.β n*markedCoordinateDirichlet q χ 5 n) := rfl

end MarkedMajorLabelEnergyData
end
end ArtinMatthews
