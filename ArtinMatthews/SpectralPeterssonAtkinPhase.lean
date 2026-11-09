module

public import ArtinMatthews.SpectralPeterssonFourierTranslation
public import ArtinMatthews.SpectralPeterssonAtkinHecke


set_option backward.privateInPublic true
@[expose] public section

/-! The same-cusp chart and its horizontal Fourier phase under Atkin–Lehner transport. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0AtkinSameCusp_inv_mul_scaling (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    (atkinScaling (NeZero.pos r) hab)⁻¹ * gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s) =
      realTranslation (-((b : ℝ)/(r : ℝ))) := by
  let t : ℝ := (b : ℝ)/(r : ℝ)
  calc
    _ = (realTranslation t)⁻¹ := by
      rw [gamma0AtkinSameCusp_scaling r s hcop hab]
      dsimp only [t]
      group
    _ = _ := by
      apply inv_eq_of_mul_eq_one_right
      rw [realTranslation_mul, show t + (-((b : ℝ)/(r : ℝ))) = 0 by exact add_neg_cancel t,
        realTranslation_zero]

theorem spectralPeterssonAtkin_sameCusp_slash (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (k : ℕ) (v : ℂ) (F : UpperHalfPlane → ℂ) :
    spectralHolomorphicSlash k (gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s))
      (fun z => v*spectralHolomorphicSlash k (atkinScaling (NeZero.pos r) hab)⁻¹ F z) =
        fun z => v*spectralHolomorphicSlash k (realTranslation (-((b : ℝ)/(r : ℝ)))) F z := by
  let σ := gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s)
  let W := atkinScaling (NeZero.pos r) hab
  have hscalar :
      spectralHolomorphicSlash k σ (fun z => v*spectralHolomorphicSlash k W⁻¹ F z) =
        fun z => v*spectralHolomorphicSlash k σ (spectralHolomorphicSlash k W⁻¹ F) z := by
    funext z
    simp only [spectralHolomorphicSlash_apply, mul_div_assoc]
  change spectralHolomorphicSlash k σ (fun z => v*spectralHolomorphicSlash k W⁻¹ F z) = _
  rw [hscalar, ← spectralHolomorphicSlash_mul, gamma0AtkinSameCusp_inv_mul_scaling r s hcop hab]

theorem spectralPeterssonAtkin_sameCusp_FourierAtHeight (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (k : ℕ) (F : UpperHalfPlane → ℂ) (m n : ℕ+) (y : ℝ) (hy : 0 < y)
    (hF : Function.Periodic (fun x => F (spectralPeterssonHeightPoint x y hy)) 1) :
    spectralPeterssonFourierAtHeight
      (spectralHolomorphicSlash k (gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s))
        (fun z => atkinPhase ((m : ℝ)*((b : ℝ)/(r : ℝ)))*
          spectralHolomorphicSlash k (atkinScaling (NeZero.pos r) hab)⁻¹ F z)) n y hy =
      atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ)))*
        spectralPeterssonFourierAtHeight F n y hy := by
  rw [spectralPeterssonAtkin_sameCusp_slash r s hcop hab,
    spectralPeterssonFourierAtHeight_const_mul, spectralPeterssonFourierAtHeight_translate k F n y hy _ hF,
    ← mul_assoc, ← atkinPhase_add]
  congr 2
  ring

theorem gamma0PeterssonHeckeChart_atkinLehner_sameCusp (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (u : ℝ) (m : ℕ+) :
    gamma0PeterssonHeckeChart (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) u m =
      fun z => atkinPhase ((m : ℝ)*((b : ℝ)/(r : ℝ)))*
        spectralHolomorphicSlash 2 (realTranslation (-((b : ℝ)/(r : ℝ))))
          (gamma0PeterssonHecke (r*s) 1 u m) z := by
  rw [← gamma0PeterssonHecke_slash_cusp,
    gamma0PeterssonHecke_atkinLehner_transport r s hcop hab u m,
    spectralPeterssonAtkin_sameCusp_slash r s hcop hab]

theorem gamma0PeterssonHeckeChart_atkinLehner_sameCusp_FourierAtHeight (r s : ℕ)
    [NeZero r] [NeZero s] (hcop : r.Coprime s) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (u : ℝ) (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight
      (gamma0PeterssonHeckeChart (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) u m) n y hy =
      atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ)))*
        spectralPeterssonFourierAtHeight (gamma0PeterssonHecke (r*s) 1 u m) n y hy := by
  rw [← gamma0PeterssonHecke_slash_cusp,
    gamma0PeterssonHecke_atkinLehner_transport r s hcop hab u m]
  apply spectralPeterssonAtkin_sameCusp_FourierAtHeight r s hcop hab
  exact spectralPeterssonFourierAtHeight_periodic_of_gamma0 (r*s) 2 _ (fun γ =>
    gamma0PeterssonHecke_slash_gamma0 (r*s) 1 γ u m) y hy

end ArtinMatthews
