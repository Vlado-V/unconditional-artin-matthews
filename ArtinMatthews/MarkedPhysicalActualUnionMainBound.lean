module

public import ArtinMatthews.MarkedPhysicalActualLineMain
public import ArtinMatthews.MarkedPhysicalBadRootLogBound


set_option backward.privateInPublic true
@[expose] public section

/-! The actual residue-and-union-label Haar main term after UV
normalization. No growing residue or label cardinality remains. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedPhysicalActualUnionLineMain_normalized_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y : ℝ), Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ U V A B C D : ℝ, 0 < U → 0 < V →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
      ∀ (R Q W : ℝ) (ψ : ℝ → ℂ),
        1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
        (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
        markedPhysicalActualUnionLineMain e x hdis d₀ Y A B C D R Q ψ / (U*V) ≤
          (16/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  filter_upwards [markedPhysicalActualUnionLineMain_log_saving e he hinj T,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro hdis d₀ Y hY U V A B C D hU hV hUA hAB hB hVC hCD hD
    R Q W ψ hQ hYone hR hW hψ hsupp
  have hh := hx hdis d₀ Y hY A B C D hAB hCD R Q W ψ hQ hYone hR hW hψ hsupp
  have harea := markedPhysicalRoot_normalized_area_le hU hV hUA hAB hB hVC hCD hD
  have hscale : 0 ≤ (1/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
    have hz := markedPhysicalRoot_zeta_two_pos
    have hlog := (Real.log_pos hx1).le
    positivity
  calc
    _ ≤ (((B-A)*(D-C)/(riemannZeta 2).re) *
        ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T))/(U*V) :=
      div_le_div_of_nonneg_right hh (mul_pos hU hV).le
    _ = ((B-A)*(D-C)/(U*V)) *
        ((1/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T)) := by ring
    _ ≤ 16 * ((1/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T)) :=
      mul_le_mul_of_nonneg_right harea hscale
    _ = _ := by ring

theorem markedPhysicalActualUnionLineMain_normalized_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (A₀ G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y : ℝ), Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ U V A B C D : ℝ, 0 < U → 0 < V →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
      ∀ (R Q W : ℝ) (ψ : ℝ → ℂ),
        1 ≤ Q → Q ≤ (Real.log x)^A₀ → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
        (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
        markedPhysicalActualUnionLineMain e x hdis d₀ Y A B C D R Q ψ / (U*V) ≤
          (16/(riemannZeta 2).re) * (33*W*(8*R+5)) * (Real.log x)^(-G) := by
  filter_upwards [markedPhysicalActualUnionLineMain_normalized_bound e he hinj (G+3*A₀),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro hdis d₀ Y hY U V A B C D hU hV hUA hAB hB hVC hCD hD
    R Q W ψ hQ hQlog hYone hR hW hψ hsupp
  have hh := hx hdis d₀ Y hY U V A B C D hU hV hUA hAB hB hVC hCD hD
    R Q W ψ hQ hYone hR hW hψ hsupp
  have hpow := markedPhysicalRoot_log_cube_cancel (G := G) (Real.log_pos hx1)
    (zero_le_one.trans hQ) hQlog
  have hfac : 0 ≤ (16/(riemannZeta 2).re) * (33*W*(8*R+5)) := by
    have hz := markedPhysicalRoot_zeta_two_pos
    positivity
  apply hh.trans
  calc
    _ = ((16/(riemannZeta 2).re) * (33*W*(8*R+5))) *
        (Q^3 * (Real.log x)^(-(G+3*A₀))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hfac

end ArtinMatthews
