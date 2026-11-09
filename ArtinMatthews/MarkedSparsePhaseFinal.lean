module

public import ArtinMatthews.MarkedSparsePhaseUniform
public import ArtinMatthews.MarkedSparsePhaseEnergy
public import ArtinMatthews.MarkedSparseAbsorption


set_option backward.privateInPublic true
@[expose] public section

/-! The actual sparse Dirichlet-polynomial energy estimate. Sparse counts
are absorbed using the fixed power saving furnished by the proved
logarithmic-phase estimate, uniformly over the full exponential height. -/

namespace ArtinMatthews

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Uniform sparse energy in logarithmic scale `X`. No kernel or analytic
estimate remains a hypothesis. `Q` allows the three-class interval count. -/
theorem markedDyadicPolynomial_sparse_energy_exp_range (d b C Q : ℝ)
    (hd : 0 < d) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (U T M : ℝ) (L R : ℕ) (S : Finset ℝ) (a : ℕ → ℂ),
        Real.exp (d*X) ≤ U → 0 ≤ T → T ≤ Real.exp (b*X) →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        (∀ n ∈ Finset.Icc L R, ‖a n‖ ≤ M) →
        (S.card:ℝ) ≤ Q*Real.exp (C*X^(91/(100:ℝ))) →
        (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t-u|) →
        (∀ t ∈ S, ∀ u ∈ S, |t-u| ≤ T) →
        (∑ t ∈ S, ‖markedDyadicPolynomial L R U a t‖^2) ≤ K*X*M^2 := by
  let B : ℝ := 1+b/d
  have hB1 : 1 ≤ B := by
    have hh := div_nonneg hb hd.le
    dsimp [B]
    linarith
  have hBhalf : 1/2 ≤ B := by linarith
  obtain ⟨A,η,hA,hη,hηhalf,hrows⟩ := markedLogKernel_rows B hBhalf
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hrows
  have hscale : Tendsto (fun X : ℝ => Real.exp (d*X)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hd)
  let K : ℝ := 3*A*(3+2*Real.log 2+2*b)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hscale.eventually (eventually_ge_atTop U₀),
    marked_sparse_power_error_absorption_mul Q C d η hd hη,
    eventually_ge_atTop (1:ℝ)] with X hXU₀ habsorb hX
  intro U T M L R S a hU hT hTU hL hR ha hcard hsep hdiam
  have hX0 : 0 ≤ X := by linarith
  have hexp1 : 1 ≤ Real.exp (d*X) := Real.one_le_exp_iff.mpr (mul_nonneg hd.le hX0)
  have hU1 : 1 ≤ U := hexp1.trans hU
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hbX : 0 ≤ b*X := mul_nonneg hb hX0
  have hTpower : T ≤ U^B := by
    calc
      T ≤ Real.exp (b*X) := hTU
      _ ≤ Real.exp (d*X*B) := by
        apply Real.exp_le_exp.mpr
        have hdb : d*B = d+b := by dsimp [B]; field_simp
        rw [mul_assoc, mul_comm X B, ← mul_assoc, hdb]
        nlinarith
      _ = (Real.exp (d*X))^B := Real.exp_mul _ _
      _ ≤ U^B := Real.rpow_le_rpow (Real.exp_pos _).le hU (by linarith)
  have hsmall : (S.card:ℝ)*U^(1-η) ≤ U := habsorb U S.card hU hcard
  have hrow : ∀ t ∈ S, ∑ u ∈ S, ‖markedLogKernel L R (t-u)‖ ≤
      A*U*(3+2*Real.log (T+1)) := by
    intro t ht
    apply (hU₀ U (hXU₀.trans hU) L R S T hL hR hT hTpower hsep hdiam t ht).trans
    calc
      _ ≤ A*(2*U*(1+Real.log (T+1))+U) :=
        mul_le_mul_of_nonneg_left (by linarith) hA.le
      _ = _ := by ring
  have hlogT : Real.log (T+1) ≤ Real.log 2+b*X := by
    have hexp : 1 ≤ Real.exp (b*X) := Real.one_le_exp_iff.mpr hbX
    calc
      Real.log (T+1) ≤ Real.log (2*Real.exp (b*X)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
  have hlogscale : 3+2*Real.log (T+1) ≤ (3+2*Real.log 2+2*b)*X := by
    have hc := mul_le_mul_of_nonneg_left hX (show 0 ≤ 3+2*Real.log 2 by positivity)
    nlinarith
  calc
    _ ≤ 3*A*(3+2*Real.log (T+1))*M^2 :=
      markedDyadicPolynomial_energy_from_rows L R U A M T hU1 hR hA.le hT a S ha hrow
    _ ≤ 3*A*((3+2*Real.log 2+2*b)*X)*M^2 := by gcongr
    _ = K*X*M^2 := by dsimp [K]; ring

end
end ArtinMatthews
